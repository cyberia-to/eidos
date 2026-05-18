// stdlib/list.rs — List inductive type
use crate::{env::{Env, IndDesc}, term::Term};
use super::ids::*;

pub fn list(a: Term) -> Term { Term::Ind(LIST_ID, vec![a]) }

pub fn list_nil(a: Term) -> Term {
    Term::Ctor(LIST_ID, LIST_NIL_IDX, vec![a])
}
pub fn list_link(a: Term, head: Term, tail: Term) -> Term {
    Term::Ctor(LIST_ID, LIST_LINK_IDX, vec![a, head, tail])
}

/// declare_list — List (A : Type₀) : Type₀ with nil and link constructors.
/// arity=1; VAR(0) = A in constructor bodies.
pub fn declare_list(env: &mut Env) {
    let id = LIST_ID;
    let a = Term::Var(0);

    let nil_tel  = Term::Ind(id, vec![a.clone()]);
    let link_tel = Term::Pi(
        Box::new(a.clone()),
        Box::new(Term::Pi(
            Box::new(Term::Ind(id, vec![Term::Var(1)])),
            Box::new(Term::Ind(id, vec![Term::Var(2)])),
        )),
    );
    let param_tel = Term::Pi(Box::new(Term::Sort(1)), Box::new(Term::Sort(0)));

    env.insert(id, IndDesc {
        arity: 1,
        sort: 1,
        param_tel,
        constructors: vec![nil_tel, link_tel],
    });
}
