//! Canonical nonnegative binary integers. All operations are CIC terms.
use super::{
    binary as p,
    bool::{bool_false, bool_true, bool_ty},
};
use crate::{
    env::{Env, IndDesc},
    term::Term,
};
use std::collections::HashMap;

pub const BNAT_ID: u64 = 0x424e_4154;
fn lam(a: Term, b: Term) -> Term {
    Term::Lam(Box::new(a), Box::new(b))
}
fn pi(a: Term, b: Term) -> Term {
    Term::Pi(Box::new(a), Box::new(b))
}
fn app(a: Term, b: Term) -> Term {
    Term::App(Box::new(a), Box::new(b))
}
fn v(i: u64) -> Term {
    Term::Var(i)
}
pub fn bnat() -> Term {
    Term::Ind(BNAT_ID, vec![])
}
pub fn zero() -> Term {
    Term::Ctor(BNAT_ID, 0, vec![])
}
pub fn positive(n: Term) -> Term {
    Term::Ctor(BNAT_ID, 1, vec![n])
}
pub fn literal(n: u128) -> Term {
    p::literal(n).map_or_else(zero, positive)
}

pub fn declare(env: &mut Env) {
    env.insert(
        BNAT_ID,
        IndDesc {
            arity: 0,
            sort: 1,
            param_tel: Term::Sort(0),
            constructors: vec![bnat(), pi(p::pos(), bnat())],
        },
    );
}

fn elim(n: Term, output: Term, z: Term, pos_case: Term) -> Term {
    Term::Elim(
        BNAT_ID,
        Box::new(lam(bnat(), output)),
        vec![z, pos_case],
        Box::new(n),
    )
}

pub fn successor(n: Term) -> Term {
    elim(
        n,
        bnat(),
        positive(p::one()),
        lam(p::pos(), positive(p::successor(v(0)))),
    )
}

pub fn add(a: Term, b: Term) -> Term {
    app(
        elim(
            a,
            pi(bnat(), bnat()),
            lam(bnat(), v(0)),
            lam(
                p::pos(),
                lam(
                    bnat(),
                    elim(
                        v(0),
                        bnat(),
                        positive(v(1)),
                        lam(p::pos(), positive(p::add(v(2), v(0)))),
                    ),
                ),
            ),
        ),
        b,
    )
}

/// Positive product, recursively doubling and adding; no host multiplication.
fn pos_mul(a: Term, b: Term) -> Term {
    let result = pi(p::pos(), p::pos());
    let call = app(v(1), v(0)); // a', ih, b
    let even = lam(
        p::pos(),
        lam(result.clone(), lam(p::pos(), p::bit0(call.clone()))),
    );
    let odd = lam(
        p::pos(),
        lam(result.clone(), lam(p::pos(), p::add(p::bit0(call), v(0)))),
    );
    app(
        Term::Elim(
            p::POS_ID,
            Box::new(lam(p::pos(), result)),
            vec![lam(p::pos(), v(0)), even, odd],
            Box::new(a),
        ),
        b,
    )
}

pub fn mul(a: Term, b: Term) -> Term {
    app(
        elim(
            a,
            pi(bnat(), bnat()),
            lam(bnat(), zero()),
            lam(
                p::pos(),
                lam(
                    bnat(),
                    elim(
                        v(0),
                        bnat(),
                        zero(),
                        lam(p::pos(), positive(pos_mul(v(2), v(0)))),
                    ),
                ),
            ),
        ),
        b,
    )
}

/// Compare positives, using `tie` when equal. More significant bits override it.
fn pos_compare(a: Term, b: Term, tie: Term) -> Term {
    let result = pi(p::pos(), pi(bool_ty(), bool_ty()));
    let base = lam(
        p::pos(),
        lam(
            bool_ty(),
            Term::Elim(
                p::POS_ID,
                Box::new(lam(p::pos(), bool_ty())),
                vec![
                    v(0),
                    lam(p::pos(), lam(bool_ty(), bool_true())),
                    lam(p::pos(), lam(bool_ty(), bool_true())),
                ],
                Box::new(v(1)),
            ),
        ),
    );
    fn case(odd: bool, result: Term) -> Term {
        // a', ih, b, tie; inside b branches: b', unused recurrence.
        let branch = |b_odd: bool| {
            let tie = if odd == b_odd {
                v(2)
            } else if b_odd {
                bool_true()
            } else {
                bool_false()
            };
            lam(p::pos(), lam(bool_ty(), app(app(v(4), v(1)), tie)))
        };
        lam(
            p::pos(),
            lam(
                result,
                lam(
                    p::pos(),
                    lam(
                        bool_ty(),
                        Term::Elim(
                            p::POS_ID,
                            Box::new(lam(p::pos(), bool_ty())),
                            vec![bool_false(), branch(false), branch(true)],
                            Box::new(v(1)),
                        ),
                    ),
                ),
            ),
        )
    }
    app(
        app(
            Term::Elim(
                p::POS_ID,
                Box::new(lam(p::pos(), result.clone())),
                vec![base, case(false, result.clone()), case(true, result)],
                Box::new(a),
            ),
            b,
        ),
        tie,
    )
}

pub fn less(a: Term, b: Term) -> Term {
    app(
        elim(
            a,
            pi(bnat(), bool_ty()),
            lam(
                bnat(),
                elim(v(0), bool_ty(), bool_false(), lam(p::pos(), bool_true())),
            ),
            lam(
                p::pos(),
                lam(
                    bnat(),
                    elim(
                        v(0),
                        bool_ty(),
                        bool_false(),
                        lam(p::pos(), pos_compare(v(2), v(0), bool_false())),
                    ),
                ),
            ),
        ),
        b,
    )
}

pub fn add_globals(globals: &mut HashMap<String, (Term, Term)>) {
    globals.insert("BNat".into(), (bnat(), Term::Sort(1)));
    globals.insert("BNat.zero".into(), (zero(), bnat()));
    globals.insert(
        "BNat.positive".into(),
        (lam(p::pos(), positive(v(0))), pi(p::pos(), bnat())),
    );
    globals.insert(
        "BNat.succ".into(),
        (lam(bnat(), successor(v(0))), pi(bnat(), bnat())),
    );
    for (name, body, output) in [
        ("BNat.add", add(v(1), v(0)), bnat()),
        ("BNat.mul", mul(v(1), v(0)), bnat()),
        ("BNat.lt", less(v(1), v(0)), bool_ty()),
    ] {
        globals.insert(
            name.into(),
            (
                lam(bnat(), lam(bnat(), body)),
                pi(bnat(), pi(bnat(), output)),
            ),
        );
    }
}
