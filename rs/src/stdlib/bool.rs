// stdlib/bool.rs — Bool inductive type and helpers
use crate::{env::{Env, IndDesc}, term::Term};
use super::ids::*;

pub fn bool_ty()    -> Term { Term::Ind(BOOL_ID, vec![]) }
pub fn bool_false() -> Term { Term::Ctor(BOOL_ID, BOOL_FALSE_IDX, vec![]) }
pub fn bool_true()  -> Term { Term::Ctor(BOOL_ID, BOOL_TRUE_IDX,  vec![]) }

pub fn declare_bool(env: &mut Env) {
    let b = bool_ty();
    env.insert(BOOL_ID, IndDesc {
        arity: 0,
        sort: 1,
        param_tel: Term::Sort(0),
        constructors: vec![b.clone(), b.clone()],
    });
}

/// bool_not b — boolean negation.
pub fn bool_not(b: Term) -> Term {
    Term::Elim(
        BOOL_ID,
        Box::new(Term::Lam(Box::new(bool_ty()), Box::new(bool_ty()))),
        vec![bool_true(), bool_false()],
        Box::new(b),
    )
}

/// Proof that bool_not false = true.
pub fn bool_not_false_eq() -> Term {
    super::prop::eq_refl(bool_ty(), bool_true())
}

/// Proof that bool_not true = false.
pub fn bool_not_true_eq() -> Term {
    super::prop::eq_refl(bool_ty(), bool_false())
}
