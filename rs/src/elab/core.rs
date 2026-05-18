// core — expression elaboration: surface Expr → (kernel Term, its type)
// spec: specs/surface.md § elaboration algorithm

use std::collections::HashMap;

use crate::{
    ctx::{ctx_lookup, CtxEntry},
    env::Env,
    reduce::{instantiate, whnf},
    subst::{shift, subst},
    term::Term,
};
use super::{
    ast::{Arm, Binder, Expr, Pattern},
    meta::{ElabError, MetaCtx},
};

// ── ElabState ────────────────────────────────────────────────────────────────

/// Mutable elaboration state: metavars + name environment.
#[derive(Debug)]
pub struct ElabState {
    pub mctx: MetaCtx,
    /// Global definitions: name → (elaborated term, type)
    pub globals: HashMap<String, (Term, Term)>,
    /// Local binders, innermost first: (name, raw_type_at_binding_site).
    /// locals[0] = VAR(0), locals[i] = VAR(i).
    pub locals: Vec<(String, Term)>,
}

impl ElabState {
    pub fn new() -> Self {
        ElabState { mctx: MetaCtx::new(), globals: HashMap::new(), locals: Vec::new() }
    }

    /// Populate globals with stdlib constructors and type names.
    pub fn add_stdlib(&mut self) {
        use crate::stdlib::*;
        let nat_arr = Term::Pi(Box::new(nat()), Box::new(nat()));
        let type1 = Term::Sort(1);
        let list_fn = Term::Lam(Box::new(type1.clone()),
            Box::new(Term::Ind(LIST_ID, vec![Term::Var(0)])));
        let list_ty = Term::Pi(Box::new(type1.clone()), Box::new(type1.clone()));
        let nil_fn = Term::Lam(Box::new(type1.clone()),
            Box::new(Term::Ctor(LIST_ID, LIST_NIL_IDX, vec![Term::Var(0)])));
        let nil_ty = Term::Pi(Box::new(type1.clone()),
            Box::new(Term::Ind(LIST_ID, vec![Term::Var(0)])));
        let next_fn = Term::Lam(Box::new(nat()),
            Box::new(Term::Ctor(NAT_ID, NAT_NEXT, vec![Term::Var(0)])));
        let eq_fn = Term::Lam(Box::new(type1.clone()), Box::new(
            Term::Lam(Box::new(Term::Var(0)), Box::new(
                Term::Lam(Box::new(Term::Var(1)), Box::new(
                    Term::Ind(EQ_ID, vec![Term::Var(2), Term::Var(1), Term::Var(0)])))))));
        let eq_ty = Term::Pi(Box::new(type1.clone()), Box::new(
            Term::Pi(Box::new(Term::Var(0)), Box::new(
                Term::Pi(Box::new(Term::Var(1)), Box::new(Term::Sort(0)))))));
        self.globals.insert("Nat".into(),       (nat(),        type1.clone()));
        self.globals.insert("Nat.zero".into(),  (nat_zero(),   nat()));
        self.globals.insert("Nat.next".into(),  (next_fn.clone(), nat_arr.clone()));
        self.globals.insert("Bool".into(),      (bool_ty(),    type1.clone()));
        self.globals.insert("Bool.false".into(),(bool_false(), bool_ty()));
        self.globals.insert("Bool.true".into(), (bool_true(),  bool_ty()));
        self.globals.insert("True".into(),  (Term::Ind(TRUE_ID,  vec![]), Term::Sort(0)));
        self.globals.insert("False".into(), (Term::Ind(FALSE_ID, vec![]), Term::Sort(0)));
        self.globals.insert("List".into(),      (list_fn,  list_ty));
        self.globals.insert("List.nil".into(),  (nil_fn,   nil_ty));
        self.globals.insert("Eq".into(), (eq_fn, eq_ty));

        // Arithmetic
        let nat_nat_nat = Term::Pi(Box::new(nat()), Box::new(Term::Pi(Box::new(nat()), Box::new(nat()))));
        let add_fn = Term::Lam(Box::new(nat()), Box::new(Term::Lam(
            Box::new(nat()),
            Box::new(nat_add(Term::Var(1), Term::Var(0))),
        )));
        let mul_fn = Term::Lam(Box::new(nat()), Box::new(Term::Lam(
            Box::new(nat()),
            Box::new(nat_mul(Term::Var(1), Term::Var(0))),
        )));
        self.globals.insert("Nat.add".into(),  (add_fn,       nat_nat_nat.clone()));
        self.globals.insert("Nat.mul".into(),  (mul_fn,       nat_nat_nat.clone()));
        self.globals.insert("Nat.succ".into(), (next_fn.clone(), nat_arr.clone()));

        // Eq.refl : ∀ (A : Type) (a : A), Eq A a a
        let eq_refl_fn = Term::Lam(Box::new(type1.clone()), Box::new(Term::Lam(
            Box::new(Term::Var(0)),
            Box::new(eq_refl(Term::Var(1), Term::Var(0))),
        )));
        let eq_refl_ty = Term::Pi(Box::new(type1.clone()), Box::new(
            Term::Pi(Box::new(Term::Var(0)),
                Box::new(Term::Ind(EQ_ID, vec![Term::Var(1), Term::Var(0), Term::Var(0)])))));
        self.globals.insert("Eq.refl".into(), (eq_refl_fn, eq_refl_ty));

        // And : Prop → Prop → Prop
        let and_fn = Term::Lam(Box::new(Term::Sort(0)), Box::new(Term::Lam(
            Box::new(Term::Sort(0)),
            Box::new(Term::Ind(AND_ID, vec![Term::Var(1), Term::Var(0)])),
        )));
        let and_ty = Term::Pi(Box::new(Term::Sort(0)), Box::new(
            Term::Pi(Box::new(Term::Sort(0)), Box::new(Term::Sort(0)))));
        self.globals.insert("And".into(), (and_fn, and_ty));

        // And.intro : ∀ P Q : Prop, P → Q → And P Q
        let and_intro_fn = Term::Lam(Box::new(Term::Sort(0)), Box::new(  // P
            Term::Lam(Box::new(Term::Sort(0)), Box::new(  // Q
                Term::Lam(Box::new(Term::Var(1)), Box::new(  // p : P
                    Term::Lam(Box::new(Term::Var(1)), Box::new(  // q : Q (P shifted)
                        Term::Ctor(AND_ID, 0, vec![
                            Term::Var(3), Term::Var(2), Term::Var(1), Term::Var(0)
                        ])
                    ))
                ))
            ))
        ));
        let and_intro_ty = Term::Pi(Box::new(Term::Sort(0)), Box::new(  // P
            Term::Pi(Box::new(Term::Sort(0)), Box::new(  // Q
                Term::Pi(Box::new(Term::Var(1)), Box::new(  // p : P
                    Term::Pi(Box::new(Term::Var(1)), Box::new(  // q : Q
                        Term::Ind(AND_ID, vec![Term::Var(3), Term::Var(2)])
                    ))
                ))
            ))
        ));
        self.globals.insert("And.intro".into(), (and_intro_fn, and_intro_ty));

        // Le : Nat → Nat → Prop
        self.globals.insert("Le".into(),      (le_type_lam(), le_type_pi()));
        self.globals.insert("Nat.Le".into(),  (le_type_lam(), le_type_pi()));

        // Le.refl : Π(n:Nat). Le n n
        let le_refl_ty = Term::Pi(
            Box::new(nat()),
            Box::new(Term::Ind(LE_ID, vec![Term::Var(0), Term::Var(0)])),
        );
        let le_refl_term = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Ctor(LE_ID, LE_REFL_IDX, vec![Term::Var(0), Term::Var(0)])),
        );
        self.globals.insert("Le.refl".into(),      (le_refl_term.clone(), le_refl_ty.clone()));
        self.globals.insert("Nat.Le.refl".into(),  (le_refl_term, le_refl_ty));

        // Le.step : Π(n m : Nat). Le n m → Le n (Nat.succ m)
        let le_step_ty = Term::Pi(
            Box::new(nat()),
            Box::new(Term::Pi(
                Box::new(nat()),
                Box::new(Term::Pi(
                    Box::new(Term::Ind(LE_ID, vec![Term::Var(1), Term::Var(0)])),
                    Box::new(Term::Ind(LE_ID, vec![Term::Var(2), nat_next(Term::Var(1))])),
                )),
            )),
        );
        let le_step_fn = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(Term::Lam(
                    Box::new(Term::Ind(LE_ID, vec![Term::Var(1), Term::Var(0)])),
                    Box::new(Term::Ctor(LE_ID, LE_STEP_IDX, vec![Term::Var(2), Term::Var(1), Term::Var(0)])),
                )),
            )),
        );
        self.globals.insert("Le.step".into(),     (le_step_fn.clone(), le_step_ty.clone()));
        self.globals.insert("Nat.Le.step".into(), (le_step_fn, le_step_ty));

        // Nat.min, Nat.max : Nat → Nat → Nat
        self.globals.insert("Nat.min".into(), (nat_min_term(), nat_nat_nat.clone()));
        self.globals.insert("Nat.max".into(), (nat_max_term(), nat_nat_nat.clone()));

        // Nat.sub : Nat → Nat → Nat (saturating)
        let sub_fn = Term::Lam(Box::new(nat()), Box::new(Term::Lam(
            Box::new(nat()),
            Box::new(crate::stdlib::nat_sub(Term::Var(1), Term::Var(0))),
        )));
        self.globals.insert("Nat.sub".into(), (sub_fn, nat_nat_nat.clone()));

        // Nat.div : Nat → Nat → Nat (axiomatic)
        self.globals.insert("Nat.div".into(), (nat_nat_nat.clone(), nat_nat_nat.clone()));

        // Nat axiom lemmas (bootstrap — proved in Lean, trusted here)
        let opaque = Term::Sort(0);
        self.globals.insert("Nat.min_le_right".into(),     (opaque.clone(), opaque.clone()));
        self.globals.insert("Nat.div_le_self".into(),      (opaque.clone(), opaque.clone()));
        self.globals.insert("Nat.div_le_div_right".into(), (opaque.clone(), opaque.clone()));
        self.globals.insert("Nat.mul_le_mul_right".into(), (opaque.clone(), opaque.clone()));
        self.globals.insert("Nat.mul_div_cancel_left".into(), (opaque.clone(), opaque));
    }

    pub fn depth(&self) -> usize { self.locals.len() }

    /// Build a kernel Ctx from current locals (innermost first = VAR(0) first).
    pub fn ctx(&self) -> crate::ctx::Ctx {
        self.locals.iter().map(|(_, t)| CtxEntry::Var(t.clone())).collect()
    }

    /// Push a new innermost local binder.
    pub fn push(&mut self, name: String, ty: Term) {
        self.locals.insert(0, (name, ty));
    }

    /// Pop the innermost local binder.
    pub fn pop(&mut self) {
        if !self.locals.is_empty() { self.locals.remove(0); }
    }

    /// Resolve a local name: returns (de_bruijn_index, shifted_type).
    pub fn lookup_local(&self, name: &str) -> Option<(u64, Term)> {
        let ctx = self.ctx();
        for (i, (n, _)) in self.locals.iter().enumerate() {
            if n == name {
                let ty = match ctx_lookup(&ctx, i)? {
                    CtxEntry::Var(t) | CtxEntry::Let(t, _) => t,
                };
                return Some((i as u64, ty));
            }
        }
        None
    }
}

// ── elab_expr ────────────────────────────────────────────────────────────────

/// Elaborate a surface expression: returns (kernel term, its type).
pub fn elab_expr(st: &mut ElabState, env: &Env, expr: &Expr) -> Result<(Term, Term), ElabError> {
    match expr {
        Expr::Name(n) => {
            if let Some((idx, ty)) = st.lookup_local(n) {
                return Ok((Term::Var(idx), ty));
            }
            if let Some((t, ty)) = st.globals.get(n).cloned() {
                return Ok((t, ty));
            }
            Err(ElabError::UnknownName(n.clone()))
        }

        Expr::Sort(level) => {
            let u: u64 = match level {
                None    => 0,          // Prop
                Some(0) => 1,          // Type = Type₀ = Sort(1)
                Some(n) => 1 + n,      // Type n = Sort(1+n)
            };
            Ok((Term::Sort(u), Term::Sort(u + 1)))
        }

        Expr::Arrow(a, b) => {
            // A -> B: non-dependent; B elaborated in outer scope then shifted
            let (a_term, a_ty) = elab_expr(st, env, a)?;
            let sort_a = require_sort(a_ty)?;
            let (b_term, b_ty) = elab_expr(st, env, b)?;
            let sort_b = require_sort(b_ty)?;
            Ok((
                Term::Pi(Box::new(a_term), Box::new(shift(&b_term, 1))),
                Term::Sort(Term::prop_max(sort_a, sort_b)),
            ))
        }

        Expr::Pi(binder, body) => {
            let (a_term, a_ty) = elab_expr(st, env, binder.ty())?;
            let sort_a = require_sort(a_ty)?;
            st.push(binder.name().to_string(), a_term.clone());
            let res = elab_expr(st, env, body);
            st.pop();
            let (b_term, b_ty) = res?;
            let sort_b = require_sort(b_ty)?;
            Ok((
                Term::Pi(Box::new(a_term), Box::new(b_term)),
                Term::Sort(Term::prop_max(sort_a, sort_b)),
            ))
        }

        Expr::Fun(binder, body) => {
            let (a_term, _) = elab_expr(st, env, binder.ty())?;
            st.push(binder.name().to_string(), a_term.clone());
            let res = elab_expr(st, env, body);
            st.pop();
            let (body_term, body_ty) = res?;
            Ok((
                Term::Lam(Box::new(a_term.clone()), Box::new(body_term)),
                Term::Pi(Box::new(a_term), Box::new(body_ty)),
            ))
        }

        Expr::App(f_expr, a_expr) => {
            let (f_term, f_ty) = elab_expr(st, env, f_expr)?;
            let ctx = st.ctx();
            let f_ty_w = whnf(env, &ctx, st.mctx.zonk(&f_ty));
            match f_ty_w {
                Term::Pi(a_ty, b_ty) => {
                    let (a_term, a_actual) = elab_expr(st, env, a_expr)?;
                    let ctx2 = st.ctx();
                    st.mctx.unify(env, &ctx2, &a_ty, &a_actual)?;
                    let res_ty = subst(&b_ty, &a_term);
                    Ok((Term::App(Box::new(f_term), Box::new(a_term)), res_ty))
                }
                other => Err(ElabError::ExpectedPi(other)),
            }
        }

        Expr::Let(x, ty_expr, val_expr, body_expr) => {
            let (ty_term, _) = elab_expr(st, env, ty_expr)?;
            let (val_term, val_ty) = elab_expr(st, env, val_expr)?;
            let ctx = st.ctx();
            st.mctx.unify(env, &ctx, &ty_term, &val_ty)?;
            st.push(x.clone(), ty_term.clone());
            let res = elab_expr(st, env, body_expr);
            st.pop();
            let (body_term, body_ty) = res?;
            let res_ty = subst(&body_ty, &val_term);
            Ok((
                Term::Let(Box::new(ty_term), Box::new(val_term), Box::new(body_term)),
                res_ty,
            ))
        }

        Expr::Hole => {
            let ty  = st.mctx.fresh();
            let tm  = st.mctx.fresh();
            Ok((tm, ty))
        }

        Expr::NatLit(n) => Ok((crate::stdlib::nat_lit(*n), crate::stdlib::nat())),

        Expr::Match(target, motive, arms) =>
            elab_match(st, env, target, motive.as_deref(), arms),

        Expr::Explicit(name, args) => {
            let (mut t, mut ty) = elab_expr(st, env, &Expr::Name(name.clone()))?;
            for arg in args {
                let (a, a_ty) = elab_expr(st, env, arg)?;
                let ctx = st.ctx();
                match whnf(env, &ctx, st.mctx.zonk(&ty)) {
                    Term::Pi(dom, cod) => {
                        st.mctx.unify(env, &ctx, &dom, &a_ty)?;
                        ty = subst(&cod, &a);
                        t = Term::App(Box::new(t), Box::new(a));
                    }
                    other => return Err(ElabError::ExpectedPi(other)),
                }
            }
            Ok((t, ty))
        }
    }
}

// ── match elaboration ────────────────────────────────────────────────────────

fn elab_match(
    st: &mut ElabState,
    env: &Env,
    target: &Expr,
    motive: Option<&Expr>,
    arms: &[Arm],
) -> Result<(Term, Term), ElabError> {
    let (tg_term, tg_ty) = elab_expr(st, env, target)?;
    let ctx = st.ctx();
    let tg_ty_w = whnf(env, &ctx, st.mctx.zonk(&tg_ty));
    let (ind_id, params) = match tg_ty_w {
        Term::Ind(id, ps) => (id, ps),
        other => return Err(ElabError::ExpectedInd(other)),
    };
    let desc = env.lookup(ind_id)
        .ok_or_else(|| ElabError::UnknownName(format!("{ind_id:#x}")))?;

    if arms.len() != desc.constructors.len() {
        return Err(ElabError::CaseMismatch {
            expected: desc.constructors.len(),
            got: arms.len(),
        });
    }

    let motive_term = match motive {
        Some(m) => elab_expr(st, env, m)?.0,
        None    => st.mctx.fresh(),
    };

    let ctors = desc.constructors.clone();
    let mut cases = Vec::with_capacity(arms.len());
    for (arm, ctor_tel) in arms.iter().zip(ctors.iter()) {
        cases.push(elab_arm(st, env, arm, ctor_tel, &params, ind_id)?);
    }

    let res_ty = Term::App(Box::new(motive_term.clone()), Box::new(tg_term.clone()));
    Ok((Term::Elim(ind_id, Box::new(motive_term), cases, Box::new(tg_term)), res_ty))
}

/// Elaborate a match arm as a case function (lambda over fields + IH).
fn elab_arm(
    st: &mut ElabState,
    env: &Env,
    arm: &Arm,
    ctor_tel: &Term,
    params: &[Term],
    ind_id: u64,
) -> Result<Term, ElabError> {
    let inst_tel = instantiate(ctor_tel, params);
    let field_names: Vec<&str> = match &arm.pattern {
        Pattern::Wildcard | Pattern::Name(_) => vec![],
        Pattern::App(_, vars) => vars.iter().map(|s| s.as_str()).collect(),
    };
    let (pushed, lam_types) = push_arm_locals(st, env, inst_tel, &field_names, ind_id)?;
    let res = elab_expr(st, env, &arm.body);
    for _ in 0..pushed { st.pop(); }
    let (body_term, _) = res?;
    let mut result = body_term;
    for ty in lam_types.into_iter().rev() {
        result = Term::Lam(Box::new(ty), Box::new(result));
    }
    Ok(result)
}

/// Walk the constructor telescope, pushing field locals + IH locals for recursive fields.
/// Returns (number_pushed, lam_types_in_push_order).
fn push_arm_locals(
    st: &mut ElabState,
    env: &Env,
    mut tel: Term,
    names: &[&str],
    ind_id: u64,
) -> Result<(usize, Vec<Term>), ElabError> {
    let mut pushed = 0;
    let mut lam_types: Vec<Term> = Vec::new();
    let mut name_idx = 0;
    loop {
        let ctx = st.ctx();
        match whnf(env, &ctx, tel) {
            Term::Pi(a, rest) => {
                let fname = if name_idx < names.len() {
                    names[name_idx].to_string()
                } else {
                    format!("_f{name_idx}")
                };
                name_idx += 1;
                let a_w = whnf(env, &ctx, *a.clone());
                let is_rec = matches!(&a_w, Term::Ind(fid, _) if *fid == ind_id);
                st.push(fname, *a.clone());
                pushed += 1;
                lam_types.push(*a.clone());
                if is_rec {
                    let ih_ty = st.mctx.fresh();
                    st.push("_ih".to_string(), ih_ty.clone());
                    pushed += 1;
                    lam_types.push(ih_ty);
                }
                tel = subst(&rest, &Term::Var(0));
            }
            _ => break,
        }
    }
    Ok((pushed, lam_types))
}

// ── helpers ──────────────────────────────────────────────────────────────────

fn require_sort(ty: Term) -> Result<u64, ElabError> {
    match ty {
        Term::Sort(u) => Ok(u),
        other => Err(ElabError::ExpectedSort(other)),
    }
}

/// Build a telescope of binders (params) into `ElabState.locals`.
/// Returns the list of elaborated parameter types (for later folding into PI/LAM).
pub fn push_params(
    st: &mut ElabState,
    env: &Env,
    params: &[Binder],
) -> Result<Vec<Term>, ElabError> {
    let mut types = Vec::with_capacity(params.len());
    for b in params {
        let (ty_term, _) = elab_expr(st, env, b.ty())?;
        st.push(b.name().to_string(), ty_term.clone());
        types.push(ty_term);
    }
    Ok(types)
}

/// Fold a list of parameter types into a PI telescope around `body`.
/// param_types[0] = first (outermost) param type; iterate in reverse so it
/// ends up as the outermost Pi binder.
pub fn fold_pi(param_types: &[Term], body: Term) -> Term {
    let mut result = body;
    for ty in param_types.iter().rev() {
        result = Term::Pi(Box::new(ty.clone()), Box::new(result));
    }
    result
}

/// Fold a list of parameter types into a LAM telescope around `body`.
/// param_types[0] = first (outermost) param type; iterate in reverse so it
/// ends up as the outermost Lam binder.
pub fn fold_lam(param_types: &[Term], body: Term) -> Term {
    let mut result = body;
    for ty in param_types.iter().rev() {
        result = Term::Lam(Box::new(ty.clone()), Box::new(result));
    }
    result
}
