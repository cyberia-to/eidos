// stdlib/nat.rs — Nat inductive type, constructors, arithmetic functions
use crate::{env::{Env, IndDesc}, term::Term};
use super::ids::*;

// ── Constructors ──────────────────────────────────────────────────────────────

pub fn nat() -> Term { Term::Ind(NAT_ID, vec![]) }

pub fn nat_zero()        -> Term { Term::Ctor(NAT_ID, NAT_ZERO, vec![]) }
pub fn nat_next(n: Term) -> Term { Term::Ctor(NAT_ID, NAT_NEXT, vec![n]) }

pub fn nat_lit(n: u64) -> Term {
    let mut t = nat_zero();
    for _ in 0..n { t = nat_next(t); }
    t
}

// ── Declaration ───────────────────────────────────────────────────────────────

pub fn declare_nat(env: &mut Env) {
    let n = nat();
    env.insert(NAT_ID, IndDesc {
        arity: 0,
        sort: 1,
        param_tel: Term::Sort(0),
        constructors: vec![
            n.clone(),
            Term::Pi(Box::new(n.clone()), Box::new(n.clone())),
        ],
    });
}

// ── Arithmetic ────────────────────────────────────────────────────────────────

/// nat_add n m — n + m by elimination on n.
pub fn nat_add(n: Term, m: Term) -> Term {
    Term::Elim(
        NAT_ID,
        Box::new(Term::Lam(Box::new(nat()), Box::new(nat()))),
        vec![
            m,
            Term::Lam(Box::new(nat()), Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(nat_next(Term::Var(0))),
            ))),
        ],
        Box::new(n),
    )
}

/// nat_mul n m — n * m by elimination on n.
pub fn nat_mul(n: Term, m: Term) -> Term {
    let m_shifted = crate::subst::shift(&m, 2);
    Term::Elim(
        NAT_ID,
        Box::new(Term::Lam(Box::new(nat()), Box::new(nat()))),
        vec![
            nat_zero(),
            Term::Lam(Box::new(nat()), Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(nat_add(m_shifted, Term::Var(0))),
            ))),
        ],
        Box::new(n),
    )
}

/// nat_le n m — n ≤ m as a Bool.
pub fn nat_le(n: Term, m: Term) -> Term {
    use super::bool::{bool_ty, bool_false, bool_true};
    Term::Elim(
        NAT_ID,
        Box::new(Term::Lam(Box::new(nat()), Box::new(bool_ty()))),
        vec![
            Term::Lam(Box::new(nat()), Box::new(bool_true())),
            Term::Lam(Box::new(nat()), Box::new(Term::Lam(
                Box::new(Term::Pi(Box::new(nat()), Box::new(bool_ty()))),
                Box::new(Term::Elim(
                    NAT_ID,
                    Box::new(Term::Lam(Box::new(nat()), Box::new(bool_ty()))),
                    vec![
                        bool_false(),
                        Term::Lam(Box::new(nat()), Box::new(Term::Lam(
                            Box::new(bool_ty()),
                            Box::new(Term::App(Box::new(Term::Var(3)), Box::new(Term::Var(1)))),
                        ))),
                    ],
                    Box::new(m.clone()),
                )),
            ))),
        ],
        Box::new(n),
    )
}

/// nat_sub n m — saturating subtraction n - m (returns 0 when m > n).
pub fn nat_sub(n: Term, m: Term) -> Term {
    // nat_sub n m = ELIM(Nat, λ_.Nat, [n, λm'. λih. pred(ih)], m)
    // where pred k = ELIM(Nat, λ_.Nat, [0, λk'. λ_. k'], k)
    let pred_of_ih = Term::Elim(
        NAT_ID,
        Box::new(Term::Lam(Box::new(nat()), Box::new(nat()))),
        vec![
            nat_zero(),
            Term::Lam(Box::new(nat()), Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(Term::Var(1)), // k'
            ))),
        ],
        Box::new(Term::Var(0)), // ih (accumulated result)
    );
    Term::Elim(
        NAT_ID,
        Box::new(Term::Lam(Box::new(nat()), Box::new(nat()))),
        vec![
            n,
            Term::Lam(Box::new(nat()), Box::new(Term::Lam(
                Box::new(nat()), // ih = n - m'
                Box::new(pred_of_ih),
            ))),
        ],
        Box::new(m),
    )
}

/// nat_min_term — λn:Nat. λm:Nat. min n m, as a closed Term.
/// min 0 m = m; min (S n') 0 = 0; min (S n') (S m') = S(min n' m').
pub fn nat_min_term() -> Term {
    // outer motive: λ_:Nat. Nat → Nat
    let outer_motive = Term::Lam(
        Box::new(nat()),
        Box::new(Term::Pi(Box::new(nat()), Box::new(nat()))),
    );
    // case_zero: λm:Nat. 0  (min 0 m = 0, not m)
    let case_zero = Term::Lam(Box::new(nat()), Box::new(nat_zero()));
    // case_succ: λn':Nat. λih:(Nat→Nat). λm:Nat.
    //   ELIM(Nat, λ_.Nat, [0, λm'.λ_. S(ih m')], m)
    // Inside body: n'=Var(2), ih=Var(1), m=Var(0)
    // Inside λm'.λ_: ih=Var(3), m'=Var(1)
    let inner_case_succ = Term::Lam(
        Box::new(nat()), // m'
        Box::new(Term::Lam(
            Box::new(nat()), // _ (IH of inner elim)
            Box::new(nat_next(Term::App(
                Box::new(Term::Var(3)), // ih
                Box::new(Term::Var(1)), // m'
            ))),
        )),
    );
    let case_succ_body = Term::Elim(
        NAT_ID,
        Box::new(Term::Lam(Box::new(nat()), Box::new(nat()))),
        vec![nat_zero(), inner_case_succ],
        Box::new(Term::Var(0)), // m
    );
    let case_succ = Term::Lam(
        Box::new(nat()), // n'
        Box::new(Term::Lam(
            Box::new(Term::Pi(Box::new(nat()), Box::new(nat()))), // ih: Nat→Nat
            Box::new(Term::Lam(
                Box::new(nat()), // m
                Box::new(case_succ_body),
            )),
        )),
    );
    Term::Lam(
        Box::new(nat()), // n
        Box::new(Term::Elim(
            NAT_ID,
            Box::new(outer_motive),
            vec![case_zero, case_succ],
            Box::new(Term::Var(0)), // n
        )),
    )
}

/// nat_max_term — λn:Nat. λm:Nat. max n m, as a closed Term.
/// max 0 m = m; max (S n') 0 = S n'; max (S n') (S m') = S(max n' m').
pub fn nat_max_term() -> Term {
    // outer motive: λ_:Nat. Nat → Nat
    let outer_motive = Term::Lam(
        Box::new(nat()),
        Box::new(Term::Pi(Box::new(nat()), Box::new(nat()))),
    );
    // case_zero: λm:Nat. m  (max 0 m = m)
    let case_zero = Term::Lam(Box::new(nat()), Box::new(Term::Var(0)));
    // case_succ: λn':Nat. λih:(Nat→Nat). λm:Nat.
    //   ELIM(Nat, λ_.Nat, [S n', λm'.λ_. S(ih m')], m)
    // Inside body: n'=Var(2), ih=Var(1), m=Var(0)
    // Inside λm'.λ_: n'=Var(4), ih=Var(3), m_outer=Var(2), m'=Var(1)
    let inner_case_zero_max = nat_next(Term::Var(2)); // S n' (n'=Var(2) inside case_succ body)
    let inner_case_succ_max = Term::Lam(
        Box::new(nat()), // m'
        Box::new(Term::Lam(
            Box::new(nat()), // _
            Box::new(nat_next(Term::App(
                Box::new(Term::Var(3)), // ih
                Box::new(Term::Var(1)), // m'
            ))),
        )),
    );
    let case_succ_body = Term::Elim(
        NAT_ID,
        Box::new(Term::Lam(Box::new(nat()), Box::new(nat()))),
        vec![inner_case_zero_max, inner_case_succ_max],
        Box::new(Term::Var(0)), // m
    );
    let case_succ = Term::Lam(
        Box::new(nat()), // n'
        Box::new(Term::Lam(
            Box::new(Term::Pi(Box::new(nat()), Box::new(nat()))), // ih: Nat→Nat
            Box::new(Term::Lam(
                Box::new(nat()), // m
                Box::new(case_succ_body),
            )),
        )),
    );
    Term::Lam(
        Box::new(nat()), // n
        Box::new(Term::Elim(
            NAT_ID,
            Box::new(outer_motive),
            vec![case_zero, case_succ],
            Box::new(Term::Var(0)), // n
        )),
    )
}
