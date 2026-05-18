// stdlib/le.rs — Nat.Le (≤) inductive, helpers, and Nat arithmetic axioms
//
// Le : Nat → Nat → Prop (arity=0, both Nats are explicit constructor params)
//   refl : Π(n : Nat). Le n n
//   step : Π(n m : Nat). Le n m → Le n (S m)
//
// Arithmetic axioms (standard Lean lemmas, trusted bootstrap):
//   Nat.min_le_right, Nat.div_le_self, Nat.div_le_div_right,
//   Nat.mul_le_mul_right, Nat.mul_div_cancel_left

use crate::{env::{Env, IndDesc}, term::Term};
use super::ids::*;
use super::nat::{nat, nat_lit, nat_next};
use super::prop::eq_refl;

// ── Le constructors ───────────────────────────────────────────────────────────

pub fn le(n: Term, m: Term) -> Term { Term::Ind(LE_ID, vec![n, m]) }

pub fn le_refl(n: Term) -> Term {
    Term::Ctor(LE_ID, LE_REFL_IDX, vec![n.clone(), n])
}

pub fn le_step(n: Term, m: Term, h: Term) -> Term {
    Term::Ctor(LE_ID, LE_STEP_IDX, vec![n, m, h])
}

// ── Declaration ───────────────────────────────────────────────────────────────
//
// refl_tel : Π(n:Nat). Le n n
//   Under n binder: Var(0)=n; return Le n n = Ind(LE_ID,[Var(0),Var(0)])
//
// step_tel : Π(n:Nat). Π(m:Nat). Π(h: Le n m). Le n (S m)
//   Under n,m,h binders (innermost first): h=Var(0), m=Var(1), n=Var(2)
//   premise: Ind(LE_ID,[Var(1),Var(0)]) = Le n m  (Wait: n=Var(2) under 2 binders...)
//   Let's track carefully:
//   — Under n: n=Var(0)
//   — Under n,m: m=Var(0), n=Var(1)
//   — Under n,m,h: h=Var(0), m=Var(1), n=Var(2)
//   premise: Le(Var(2), Var(1)) = Le n m        (h : Le n m)
//   return:  Le(Var(2), S(Var(1))) = Le n (S m)

pub fn declare_le(env: &mut Env) {
    let id = LE_ID;
    // arity=2: Le takes (n m : Nat) as params. Constructor telescopes reference
    // Var(1)=n (outermost param) and Var(0)=m (innermost param) at depth=0.
    //
    // refl: return type Le n n  (both params equal n)
    let refl_tel = Term::Ind(id, vec![Term::Var(1), Term::Var(1)]);
    // step: Π(h: Le n m). Le n (S m)
    // At depth=0: Var(1)=n, Var(0)=m
    // Under Pi binder (depth=1): Var(0)=h, Var(1)=m, Var(2)=n
    let step_tel = Term::Pi(
        Box::new(Term::Ind(id, vec![Term::Var(1), Term::Var(0)])), // h : Le n m
        Box::new(Term::Ind(id, vec![Term::Var(2), nat_next(Term::Var(1))])), // Le n (S m)
    );
    env.insert(id, IndDesc {
        arity: 2,
        sort: 0,
        param_tel: Term::Pi(
            Box::new(nat()),
            Box::new(Term::Pi(Box::new(nat()), Box::new(Term::Sort(0)))),
        ),
        constructors: vec![refl_tel, step_tel],
    });
}

// ── Proof builder for concrete Le ────────────────────────────────────────────

/// Build a proof of Le (nat_lit n) (nat_lit m) for n ≤ m.
pub fn le_of_lits(n: u64, m: u64) -> Term {
    assert!(n <= m, "le_of_lits: {n} > {m}");
    if n == m {
        le_refl(nat_lit(n))
    } else {
        le_step(nat_lit(n), nat_lit(m - 1), le_of_lits(n, m - 1))
    }
}

// ── Nat.div (axiomatic — non-structurally recursive) ─────────────────────────

/// The type of Nat.div: Nat → Nat → Nat
pub fn nat_div_ty() -> Term {
    Term::Pi(Box::new(nat()), Box::new(Term::Pi(Box::new(nat()), Box::new(nat()))))
}

/// Nat.div as an axiom term (self-typed, opaque). Reduces only via globals.
pub fn nat_div_axiom() -> Term {
    // Stored as axiom: term = type (opaque)
    nat_div_ty()
}

// ── Axiom terms for standard Nat lemmas ──────────────────────────────────────
// These are bootstrap axioms: standard Lean theorems we trust but don't yet
// prove within eidos. Each is self-typed (term = type).

/// Nat.min_le_right : Π(a b : Nat). Le (Nat.min a b) b
pub fn nat_min_le_right_ty() -> Term {
    Term::Pi(
        Box::new(nat()),
        Box::new(Term::Pi(
            Box::new(nat()),
            Box::new(Term::Ind(LE_ID, vec![
                // min a b — App(App(Nat.min, Var(1)), Var(0))
                // expressed as a meta-level call; use opaque application
                Term::App(
                    Box::new(Term::App(
                        Box::new(Term::Var(2)), // Nat.min (a global ref — placeholder)
                        Box::new(Term::Var(1)), // a
                    )),
                    Box::new(Term::Var(0)), // b
                ),
                Term::Var(0), // b
            ])),
        )),
    )
}

/// Nat.div_le_self : Π(n k : Nat). Le (Nat.div n k) n
pub fn nat_div_le_self_ty() -> Term {
    Term::Pi(
        Box::new(nat()),
        Box::new(Term::Pi(
            Box::new(nat()),
            Box::new(Term::Ind(LE_ID, vec![
                Term::App(
                    Box::new(Term::App(
                        Box::new(Term::Var(2)), // Nat.div placeholder
                        Box::new(Term::Var(1)), // n
                    )),
                    Box::new(Term::Var(0)), // k
                ),
                Term::Var(1), // n
            ])),
        )),
    )
}

// For the remaining 3 lemmas, the types reference Le hypotheses and are complex.
// We store them as opaque axiom shells with their names registered in globals.
// The surface elaborator resolves Nat.div_le_div_right etc. by name lookup.

/// Proof term for an axiom: term = type (opaque / sorry).
pub fn axiom_term(ty: Term) -> Term { ty.clone() }

// ── Nat.Le as a proposition constructor ──────────────────────────────────────

/// Convenience: Le wrapped so surface elaborator can refer to it by name.
/// "Le" in surface = Term::Ind(LE_ID, [a, b]) after applying two Nat args.
/// We expose it as a pi-type: Π(a b : Nat). Prop
pub fn le_type_pi() -> Term {
    Term::Pi(
        Box::new(nat()),
        Box::new(Term::Pi(Box::new(nat()), Box::new(Term::Sort(0)))),
    )
}

/// The Le type constructor as a lambda: λa:Nat. λb:Nat. Le a b
pub fn le_type_lam() -> Term {
    Term::Lam(
        Box::new(nat()),
        Box::new(Term::Lam(
            Box::new(nat()),
            Box::new(Term::Ind(LE_ID, vec![Term::Var(1), Term::Var(0)])),
        )),
    )
}

// ── tests ─────────────────────────────────────────────────────────────────────
#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::check;

    fn ctx() -> crate::ctx::Ctx { vec![] }

    #[test]
    fn le_refl_type_checks() {
        let env = crate::stdlib::std_env();
        let proof = le_refl(nat_lit(3));
        let ty    = le(nat_lit(3), nat_lit(3));
        assert_eq!(check(&env, &ctx(), &proof, &ty), Ok(()));
    }

    #[test]
    fn le_step_type_checks() {
        let env = crate::stdlib::std_env();
        // 2 ≤ 3: le_step 2 2 (le_refl 2)
        let h   = le_refl(nat_lit(2));
        let proof = le_step(nat_lit(2), nat_lit(2), h);
        let ty    = le(nat_lit(2), nat_lit(3));
        assert_eq!(check(&env, &ctx(), &proof, &ty), Ok(()));
    }

    #[test]
    fn le_of_lits_correct() {
        let env = crate::stdlib::std_env();
        let proof = le_of_lits(0, 5);
        let ty    = le(nat_lit(0), nat_lit(5));
        assert_eq!(check(&env, &ctx(), &proof, &ty), Ok(()));
    }

    #[test]
    fn le_of_lits_refl() {
        let env = crate::stdlib::std_env();
        let proof = le_of_lits(3, 3);
        let ty    = le(nat_lit(3), nat_lit(3));
        assert_eq!(check(&env, &ctx(), &proof, &ty), Ok(()));
    }
}
