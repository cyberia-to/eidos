// stdlib/prop.rs — False, True, And, Or, Eq, Fin inductives and proof helpers
use crate::{env::{Env, IndDesc}, term::Term};
use super::ids::*;
use super::nat::{nat, nat_zero, nat_next};

// ── False ────────────────────────────────────────────────────────────────────

pub fn declare_false(env: &mut Env) {
    env.insert(FALSE_ID, IndDesc {
        arity: 0,
        sort: 0,
        param_tel: Term::Sort(0),
        constructors: vec![],
    });
}

/// false_elim P h — given h : False, produce element of P.
pub fn false_elim(p: Term, h: Term) -> Term {
    let motive = Term::Lam(
        Box::new(Term::Ind(FALSE_ID, vec![])),
        Box::new(crate::subst::shift(&p, 1)),
    );
    Term::Elim(FALSE_ID, Box::new(motive), vec![], Box::new(h))
}

// ── True ─────────────────────────────────────────────────────────────────────

pub fn declare_true(env: &mut Env) {
    let t = Term::Ind(TRUE_ID, vec![]);
    env.insert(TRUE_ID, IndDesc {
        arity: 0,
        sort: 0,
        param_tel: Term::Sort(0),
        constructors: vec![t],
    });
}

// ── And ──────────────────────────────────────────────────────────────────────

pub fn declare_and(env: &mut Env) {
    let id = AND_ID;
    let p = Term::Var(1);

    let intro_tel = Term::Pi(
        Box::new(p.clone()),
        Box::new(Term::Pi(
            Box::new(Term::Var(1)),
            Box::new(Term::Ind(id, vec![Term::Var(3), Term::Var(2)])),
        )),
    );
    let param_tel = Term::Pi(
        Box::new(Term::Sort(0)),
        Box::new(Term::Pi(Box::new(Term::Sort(0)), Box::new(Term::Sort(0)))),
    );
    env.insert(id, IndDesc { arity: 2, sort: 0, param_tel, constructors: vec![intro_tel] });
}

pub fn and_intro(p_ty: Term, q_ty: Term, p: Term, q: Term) -> Term {
    Term::Ctor(AND_ID, 0, vec![p_ty, q_ty, p, q])
}

pub fn and_right(p_ty: Term, q_ty: Term, h: Term) -> Term {
    let motive = Term::Lam(
        Box::new(Term::Ind(AND_ID, vec![p_ty.clone(), q_ty.clone()])),
        Box::new(crate::subst::shift(&q_ty, 1)),
    );
    let case = Term::Lam(
        Box::new(crate::subst::shift(&p_ty, 0)),
        Box::new(Term::Lam(
            Box::new(crate::subst::shift(&q_ty, 1)),
            Box::new(Term::Var(0)),
        )),
    );
    Term::Elim(AND_ID, Box::new(motive), vec![case], Box::new(h))
}

pub fn and_left(p_ty: Term, q_ty: Term, h: Term) -> Term {
    let motive = Term::Lam(
        Box::new(Term::Ind(AND_ID, vec![p_ty.clone(), q_ty.clone()])),
        Box::new(crate::subst::shift(&p_ty, 1)),
    );
    let case = Term::Lam(
        Box::new(crate::subst::shift(&p_ty, 0)),
        Box::new(Term::Lam(
            Box::new(crate::subst::shift(&q_ty, 1)),
            Box::new(Term::Var(1)),
        )),
    );
    Term::Elim(AND_ID, Box::new(motive), vec![case], Box::new(h))
}

// ── Or ───────────────────────────────────────────────────────────────────────

pub fn declare_or(env: &mut Env) {
    let id = OR_ID;
    let p = Term::Var(1);
    let q = Term::Var(0);
    let left_tel = Term::Pi(
        Box::new(p.clone()),
        Box::new(Term::Ind(id, vec![Term::Var(2), Term::Var(1)])),
    );
    let right_tel = Term::Pi(
        Box::new(q.clone()),
        Box::new(Term::Ind(id, vec![Term::Var(2), Term::Var(1)])),
    );
    let param_tel = Term::Pi(
        Box::new(Term::Sort(0)),
        Box::new(Term::Pi(Box::new(Term::Sort(0)), Box::new(Term::Sort(0)))),
    );
    env.insert(id, IndDesc { arity: 2, sort: 0, param_tel, constructors: vec![left_tel, right_tel] });
}

// ── Eq ───────────────────────────────────────────────────────────────────────
// arity=3 (A, a, b all params); refl : Eq A a a.

pub fn declare_eq(env: &mut Env) {
    let id = EQ_ID;
    let refl_tel = Term::Ind(id, vec![Term::Var(2), Term::Var(1), Term::Var(1)]);
    let param_tel = Term::Pi(
        Box::new(Term::Sort(1)),
        Box::new(Term::Pi(
            Box::new(Term::Var(0)),
            Box::new(Term::Pi(Box::new(Term::Var(1)), Box::new(Term::Sort(0)))),
        )),
    );
    env.insert(id, IndDesc { arity: 3, sort: 0, param_tel, constructors: vec![refl_tel] });
}

/// eq_refl A a — proof of Eq A a a.
pub fn eq_refl(a_ty: Term, a: Term) -> Term {
    Term::Ctor(EQ_ID, 0, vec![a_ty, a.clone(), a])
}

// ── Fin ──────────────────────────────────────────────────────────────────────

pub fn fin(n: Term)                -> Term { Term::Ind(FIN_ID, vec![n]) }
pub fn fin_zero(n: Term)           -> Term { Term::Ctor(FIN_ID, FIN_ZERO_IDX, vec![n]) }
pub fn fin_next(n: Term, i: Term)  -> Term { Term::Ctor(FIN_ID, FIN_NEXT_IDX, vec![n, i]) }

pub fn declare_fin(env: &mut Env) {
    let id = FIN_ID;
    let zero_tel = Term::Pi(
        Box::new(nat()),
        Box::new(Term::Ind(id, vec![nat_next(Term::Var(0))])),
    );
    let next_tel = Term::Pi(
        Box::new(nat()),
        Box::new(Term::Pi(
            Box::new(Term::Ind(id, vec![Term::Var(1)])),
            Box::new(Term::Ind(id, vec![nat_next(Term::Var(2))])),
        )),
    );
    let param_tel = Term::Pi(Box::new(Term::Sort(1)), Box::new(Term::Sort(0)));
    env.insert(id, IndDesc {
        arity: 1,
        sort: 1,
        param_tel,
        constructors: vec![zero_tel, next_tel],
    });
}
