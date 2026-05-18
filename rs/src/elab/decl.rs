// decl — declaration elaboration: def/theorem/axiom/inductive
// spec: specs/surface.md § declaration elaboration

use crate::{env::{ConstDecl, Env, IndDesc}, kernel, term::Term};
use super::{
    ast::Decl,
    core::{elab_expr, fold_lam, fold_pi, push_params, ElabState},
    meta::ElabError,
};

/// Elaborate a top-level declaration, extending `st.globals` and/or `env`.
pub fn elab_decl(st: &mut ElabState, env: &mut Env, decl: &Decl) -> Result<(), ElabError> {
    match decl {
        Decl::Def { name, params, ty, body }
        | Decl::Theorem { name, params, ty, body } => {
            elab_def(st, env, name, params, ty, body)
        }

        Decl::Axiom { name, ty } => {
            let (ty_term, _) = elab_expr(st, env, ty)?;
            let ty_closed = st.mctx.zonk(&ty_term);
            if !ty_closed.is_kernel_term() {
                return Err(ElabError::UnsolvedMeta(0));
            }
            let id = fnv_hash(name.as_bytes());
            env.insert_const(id, ConstDecl { ty: ty_closed.clone(), body: None });
            st.globals.insert(name.clone(), (Term::Const(id), ty_closed));
            Ok(())
        }

        Decl::Inductive { name, params, sort, ctors } => {
            elab_inductive(st, env, name, params, sort, ctors)
        }
    }
}

fn elab_def(
    st: &mut ElabState,
    env: &Env,
    name: &str,
    params: &[super::ast::Binder],
    ty_expr: &super::ast::Expr,
    body_expr: &super::ast::Expr,
) -> Result<(), ElabError> {
    let n_before = st.locals.len();
    let param_types = push_params(st, env, params)?;
    let n_params = st.locals.len() - n_before;

    let (ty_term, _)   = elab_expr(st, env, ty_expr)?;
    let (body_term, _) = elab_expr(st, env, body_expr)?;

    // Kernel check
    let ctx = st.ctx();
    let ty_z   = st.mctx.zonk(&ty_term);
    let body_z = st.mctx.zonk(&body_term);
    if !ty_z.is_kernel_term()   { return Err(ElabError::UnsolvedMeta(0)); }
    if !body_z.is_kernel_term() { return Err(ElabError::UnsolvedMeta(0)); }
    kernel::check(env, &ctx, &body_z, &ty_z)?;

    // Pop param locals and fold into LAM / PI
    for _ in 0..n_params { st.pop(); }
    let closed_body = fold_lam(&param_types, body_z);
    let closed_ty   = fold_pi (&param_types, ty_z);

    st.globals.insert(name.to_string(), (closed_body, closed_ty));
    Ok(())
}

fn elab_inductive(
    st: &mut ElabState,
    env: &mut Env,
    name: &str,
    params: &[super::ast::Binder],
    sort_expr: &super::ast::Expr,
    ctors: &[(String, Box<super::ast::Expr>)],
) -> Result<(), ElabError> {
    let n_before = st.locals.len();
    let param_types = push_params(st, env, params)?;
    let n_params = st.locals.len() - n_before;

    // Elaborate the sort
    let (sort_term, _) = elab_expr(st, env, sort_expr)?;
    let u = match st.mctx.zonk(&sort_term) {
        Term::Sort(u) => u,
        other => return Err(ElabError::ExpectedSort(other)),
    };

    // Assign a deterministic ID from the name
    let ind_id = fnv_hash(name.as_bytes());

    // Build param_tel: PI(P0, PI(P1, ...)) from param_types (innermost first)
    // param_types[0] = innermost, param_types[n-1] = outermost
    let param_tel = if param_types.is_empty() {
        Term::Sort(0) // dummy when arity=0
    } else {
        fold_pi(&param_types, Term::Sort(u))
    };

    // Register the inductive type in a temporary env so ctors can reference it
    let placeholder = IndDesc {
        arity: n_params as u64,
        sort: u,
        param_tel: param_tel.clone(),
        constructors: vec![],
    };
    let mut env2 = env.clone();
    env2.insert(ind_id, placeholder);
    // Add IND(ind_id, []) to globals so the name resolves
    let ind_term = Term::Ind(ind_id, (0..n_params as u64).map(Term::Var).collect());
    let ind_ty = Term::Sort(u);
    st.globals.insert(name.to_string(), (ind_term, ind_ty));

    // Elaborate constructors (in scope of the inductive name + params)
    let mut ctor_tels: Vec<Term> = Vec::with_capacity(ctors.len());
    for (ctor_name, ctor_ty_expr) in ctors {
        let (ctor_term, _) = elab_expr(st, &env2, ctor_ty_expr)?;
        let ctor_z = st.mctx.zonk(&ctor_term);
        if !ctor_z.is_kernel_term() { return Err(ElabError::UnsolvedMeta(0)); }
        // Positivity: ind_id must not appear in negative position
        check_positivity(ind_id, &ctor_z, ctor_name)?;
        ctor_tels.push(ctor_z.clone());
        // Add constructor to globals with correct type (for arity=0 inductives).
        // For parameterized inductives (arity>0) the free-variable encoding is
        // complex; leave them as placeholders since stdlib handles those manually.
        let ctor_idx = (ctor_tels.len() - 1) as u64;
        let (ctor_val, ctor_ty) = if n_params == 0 {
            build_ctor_fn(ind_id, ctor_idx, &ctor_z)
        } else {
            (Term::Ctor(ind_id, ctor_idx, vec![]), Term::Sort(0))
        };
        st.globals.insert(format!("{}.{}", name, ctor_name), (ctor_val, ctor_ty));
    }

    // Pop param locals
    for _ in 0..n_params { st.pop(); }

    let desc = IndDesc {
        arity: n_params as u64,
        sort: u,
        param_tel,
        constructors: ctor_tels,
    };
    env.insert(ind_id, desc);
    Ok(())
}

/// Build a lambda-wrapped constructor function and its type from the constructor telescope.
/// For nullary ctors (no Pi layers): returns (Ctor(id,k,[]), return_type).
/// For k-ary ctors: returns (λx1...xk. Ctor(id,k,[xk-1,...,x0]), Pi(T1,...,Pi(Tk,ret))).
fn build_ctor_fn(id: u64, k: u64, ctor_tel: &Term) -> (Term, Term) {
    let mut field_tys: Vec<Term> = Vec::new();
    let mut t = ctor_tel;
    loop {
        match t {
            Term::Pi(a, b) => { field_tys.push(*a.clone()); t = b; }
            _ => break,
        }
    }
    let n = field_tys.len();
    // Ctor args are innermost-first de Bruijn: field 0 = Var(n-1), ..., field n-1 = Var(0)
    let args: Vec<Term> = (0..n).map(|i| Term::Var((n - 1 - i) as u64)).collect();
    let mut val = Term::Ctor(id, k, args);
    for field_ty in field_tys.iter().rev() {
        val = Term::Lam(Box::new(field_ty.clone()), Box::new(val));
    }
    (val, ctor_tel.clone())
}

/// Strict positivity check: ind_id must not appear in a NEGATIVE position.
/// Negative = inside the domain of a Pi within a constructor argument type.
/// Direct occurrence as `Ind(id, _)` is positive (valid recursive argument).
fn check_positivity(ind_id: u64, t: &Term, ctor_name: &str) -> Result<(), ElabError> {
    match t {
        Term::Pi(a, b) => {
            if contains_ind_negative(ind_id, a) {
                return Err(ElabError::PositivityViolation(ctor_name.to_string()));
            }
            check_positivity(ind_id, b, ctor_name)
        }
        _ => Ok(()),
    }
}

/// Returns true if `ind_id` appears in a negative (contravariant) position in `t`.
/// Direct `Ind(id, _)` is positive (fine for recursive args).
/// Occurrence inside a Pi domain is negative.
fn contains_ind_negative(ind_id: u64, t: &Term) -> bool {
    match t {
        Term::Ind(id, _) if *id == ind_id => false,
        Term::Pi(a, b) => contains_ind(ind_id, a) || contains_ind_negative(ind_id, b),
        _ => false,
    }
}

fn contains_ind(id: u64, t: &Term) -> bool {
    match t {
        Term::Ind(i, ps) => *i == id || ps.iter().any(|p| contains_ind(id, p)),
        Term::Var(_) | Term::Sort(_) | Term::Meta(_) => false,
        Term::Pi(a, b) | Term::Lam(a, b) | Term::App(a, b) =>
            contains_ind(id, a) || contains_ind(id, b),
        Term::Let(a, v, b) =>
            contains_ind(id, a) || contains_ind(id, v) || contains_ind(id, b),
        Term::Ctor(_, _, args) => args.iter().any(|a| contains_ind(id, a)),
        Term::Elim(_, m, cs, tg) =>
            contains_ind(id, m) || cs.iter().any(|c| contains_ind(id, c)) || contains_ind(id, tg),
        Term::EqSubst(p, h, pf) =>
            contains_ind(id, p) || contains_ind(id, h) || contains_ind(id, pf),
        Term::Const(_) => false,
    }
}

pub fn fnv_hash(data: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in data {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}
