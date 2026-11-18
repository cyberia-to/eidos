// core — expression elaboration: surface Expr → (kernel Term, its type)
// spec: specs/surface.md § elaboration algorithm

use std::collections::HashMap;

use super::{
    ast::{Arm, Binder, Expr, Pattern},
    meta::{ElabError, MetaCtx},
};
use crate::{
    ctx::{ctx_lookup, CtxEntry},
    env::Env,
    reduce::{instantiate, whnf},
    subst::{shift, subst},
    term::Term,
};

// ── ElabState ────────────────────────────────────────────────────────────────

/// Mutable elaboration state: metavars + name environment.
#[derive(Debug)]
pub struct ElabState {
    pub mctx: MetaCtx,
    /// Global definitions: name → (elaborated term, type)
    pub globals: HashMap<String, (Term, Term)>,
    /// Local binders, innermost first: (name, raw_type_at_binding_site).
    /// `locals[0] = VAR(0)`, `locals[i] = VAR(i)`.
    pub locals: Vec<(String, Term)>,
}

impl Default for ElabState {
    fn default() -> Self {
        Self::new()
    }
}

impl ElabState {
    pub fn new() -> Self {
        ElabState {
            mctx: MetaCtx::new(),
            globals: HashMap::new(),
            locals: Vec::new(),
        }
    }

    pub fn depth(&self) -> usize {
        self.locals.len()
    }

    /// Build a kernel Ctx from current locals (innermost first = VAR(0) first).
    pub fn ctx(&self) -> crate::ctx::Ctx {
        self.locals
            .iter()
            .map(|(_, t)| CtxEntry::Var(t.clone()))
            .collect()
    }

    /// Push a new innermost local binder.
    pub fn push(&mut self, name: String, ty: Term) {
        self.locals.insert(0, (name, ty));
    }

    /// Pop the innermost local binder.
    pub fn pop(&mut self) {
        if !self.locals.is_empty() {
            self.locals.remove(0);
        }
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
                None => 0,        // Prop
                Some(0) => 1,     // Type = Type₀ = Sort(1)
                Some(n) => 1 + n, // Type n = Sort(1+n)
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
            let ty = st.mctx.fresh();
            let tm = st.mctx.fresh();
            Ok((tm, ty))
        }

        Expr::NatLit(n) => Ok((crate::stdlib::nat_lit(*n), crate::stdlib::nat())),

        Expr::Match(target, motive, arms) => elab_match(st, env, target, motive.as_deref(), arms),

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
    let desc = env
        .lookup(ind_id)
        .ok_or_else(|| ElabError::UnknownName(format!("{ind_id:#x}")))?;

    if arms.len() != desc.constructors.len() {
        return Err(ElabError::CaseMismatch {
            expected: desc.constructors.len(),
            got: arms.len(),
        });
    }

    let motive_term = match motive {
        Some(m) => elab_expr(st, env, m)?.0,
        None => st.mctx.fresh(),
    };

    let ctors = desc.constructors.clone();
    let mut cases = Vec::with_capacity(arms.len());
    for (arm, ctor_tel) in arms.iter().zip(ctors.iter()) {
        cases.push(elab_arm(st, env, arm, ctor_tel, &params, ind_id)?);
    }

    let res_ty = Term::App(Box::new(motive_term.clone()), Box::new(tg_term.clone()));
    Ok((
        Term::Elim(ind_id, Box::new(motive_term), cases, Box::new(tg_term)),
        res_ty,
    ))
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
    for _ in 0..pushed {
        st.pop();
    }
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
/// `param_types[0]` = first (outermost) param type; iterate in reverse so it
/// ends up as the outermost Pi binder.
pub fn fold_pi(param_types: &[Term], body: Term) -> Term {
    let mut result = body;
    for ty in param_types.iter().rev() {
        result = Term::Pi(Box::new(ty.clone()), Box::new(result));
    }
    result
}

/// Fold a list of parameter types into a LAM telescope around `body`.
/// `param_types[0]` = first (outermost) param type; iterate in reverse so it
/// ends up as the outermost Lam binder.
pub fn fold_lam(param_types: &[Term], body: Term) -> Term {
    let mut result = body;
    for ty in param_types.iter().rev() {
        result = Term::Lam(Box::new(ty.clone()), Box::new(result));
    }
    result
}
