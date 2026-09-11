//! Canonical binary positives and CIC successor/addition terms.
//! No host arithmetic result is accepted without kernel reduction/checking.
use crate::{
    env::{Env, IndDesc},
    term::Term,
};
use std::collections::HashMap;

pub const POS_ID: u64 = 0x504f_5300;
fn lam(ty: Term, body: Term) -> Term {
    Term::Lam(Box::new(ty), Box::new(body))
}
fn pi(ty: Term, body: Term) -> Term {
    Term::Pi(Box::new(ty), Box::new(body))
}
fn app(f: Term, x: Term) -> Term {
    Term::App(Box::new(f), Box::new(x))
}
pub fn pos() -> Term {
    Term::Ind(POS_ID, vec![])
}
pub fn one() -> Term {
    Term::Ctor(POS_ID, 0, vec![])
}
pub fn bit0(n: Term) -> Term {
    Term::Ctor(POS_ID, 1, vec![n])
}
pub fn bit1(n: Term) -> Term {
    Term::Ctor(POS_ID, 2, vec![n])
}

pub fn declare(env: &mut Env) {
    env.insert(
        POS_ID,
        IndDesc {
            arity: 0,
            sort: 1,
            param_tel: Term::Sort(0),
            constructors: vec![pos(), pi(pos(), pos()), pi(pos(), pos())],
        },
    );
}

pub fn literal(n: u128) -> Option<Term> {
    if n == 0 {
        return None;
    }
    let mut term = one();
    for bit in (0..127 - n.leading_zeros()).rev() {
        term = if n & (1u128 << bit) == 0 {
            bit0(term)
        } else {
            bit1(term)
        };
    }
    Some(term)
}

pub fn successor(n: Term) -> Term {
    Term::Elim(
        POS_ID,
        Box::new(lam(pos(), pos())),
        vec![
            bit0(one()),
            lam(pos(), lam(pos(), bit1(Term::Var(1)))),
            lam(pos(), lam(pos(), bit0(Term::Var(0)))),
        ],
        Box::new(n),
    )
}

pub fn add(a: Term, b: Term) -> Term {
    fn case(odd: bool) -> Term {
        // Context before inner elimination: b=0, ih=1, a'=2.
        let first = if odd {
            bit0(successor(Term::Var(2)))
        } else {
            bit1(Term::Var(2))
        };
        // Inner constructor cases bind b' and its (unused) recursion result:
        // rec=0, b'=1, b=2, ih=3, a'=4.
        let sum = app(Term::Var(3), Term::Var(1));
        let even = if odd {
            bit1(sum.clone())
        } else {
            bit0(sum.clone())
        };
        let odd_result = if odd { bit0(successor(sum)) } else { bit1(sum) };
        lam(
            pos(),
            lam(
                pi(pos(), pos()),
                lam(
                    pos(),
                    Term::Elim(
                        POS_ID,
                        Box::new(lam(pos(), pos())),
                        vec![
                            first,
                            lam(pos(), lam(pos(), even)),
                            lam(pos(), lam(pos(), odd_result)),
                        ],
                        Box::new(Term::Var(0)),
                    ),
                ),
            ),
        )
    }
    app(
        Term::Elim(
            POS_ID,
            Box::new(lam(pos(), pi(pos(), pos()))),
            vec![lam(pos(), successor(Term::Var(0))), case(false), case(true)],
            Box::new(a),
        ),
        b,
    )
}

pub fn add_globals(globals: &mut HashMap<String, (Term, Term)>) {
    globals.insert("Pos".into(), (pos(), Term::Sort(1)));
    globals.insert("Pos.one".into(), (one(), pos()));
    for (name, body) in [
        ("Pos.bit0", bit0(Term::Var(0))),
        ("Pos.bit1", bit1(Term::Var(0))),
        ("Pos.succ", successor(Term::Var(0))),
    ] {
        globals.insert(name.into(), (lam(pos(), body), pi(pos(), pos())));
    }
    globals.insert(
        "Pos.add".into(),
        (
            lam(pos(), lam(pos(), add(Term::Var(1), Term::Var(0)))),
            pi(pos(), pi(pos(), pos())),
        ),
    );
}
