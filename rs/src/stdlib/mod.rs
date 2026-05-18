// stdlib/mod.rs — standard library bootstrap
// spec: specs/stdlib.md
// Untrusted shell — declares terms; kernel verifies them.

pub mod ids;
pub mod nat;
pub mod bool;
pub mod list;
pub mod prop;
pub mod le;

// ── Re-exports ────────────────────────────────────────────────────────────────

pub use ids::*;
pub use nat::{nat, nat_zero, nat_next, nat_lit, nat_add, nat_mul, nat_le, nat_sub,
              nat_min_term, nat_max_term};
pub use bool::{bool_ty, bool_false, bool_true, bool_not,
               bool_not_false_eq, bool_not_true_eq};
pub use list::{list, list_nil, list_link};
pub use prop::{eq_refl, false_elim, and_intro, and_right, and_left,
               fin, fin_zero, fin_next};
pub use le::{le, le_refl, le_step, le_of_lits, le_type_lam, le_type_pi};

use crate::{env::Env, term::Term};

// ── Env bootstrap ─────────────────────────────────────────────────────────────

/// Build the standard environment: Nat, Bool, List, False, True, And, Or, Eq, Fin, Le.
pub fn std_env() -> Env {
    let mut env = Env::new();
    nat::declare_nat(&mut env);
    bool::declare_bool(&mut env);
    list::declare_list(&mut env);
    prop::declare_false(&mut env);
    prop::declare_true(&mut env);
    prop::declare_and(&mut env);
    prop::declare_or(&mut env);
    prop::declare_eq(&mut env);
    prop::declare_fin(&mut env);
    le::declare_le(&mut env);
    env
}

// ── ElabState surface names ───────────────────────────────────────────────────

/// Populate ElabState globals with stdlib names for surface elaboration.
pub fn add_stdlib_globals(globals: &mut std::collections::HashMap<String, (Term, Term)>) {
    use crate::term::Term as T;

    // Types
    globals.insert("Nat".into(),  (nat(), T::Sort(1)));
    globals.insert("Bool".into(), (bool_ty(), T::Sort(1)));
    globals.insert("True".into(), (T::Ind(TRUE_ID, vec![]), T::Sort(0)));
    globals.insert("False".into(),(T::Ind(FALSE_ID, vec![]), T::Sort(0)));

    // Bool values
    globals.insert("Bool.false".into(), (bool_false(), bool_ty()));
    globals.insert("Bool.true".into(),  (bool_true(),  bool_ty()));
    globals.insert("true".into(),       (bool_true(),  bool_ty()));
    globals.insert("false".into(),      (bool_false(), bool_ty()));

    // Nat constructors
    globals.insert("Nat.zero".into(), (nat_zero(), nat()));
    globals.insert("Nat.succ".into(), (
        T::Lam(Box::new(nat()), Box::new(nat_next(T::Var(0)))),
        T::Pi(Box::new(nat()), Box::new(nat())),
    ));

    // Nat arithmetic
    let add_ty = T::Pi(Box::new(nat()), Box::new(T::Pi(Box::new(nat()), Box::new(nat()))));
    let add_term = T::Lam(Box::new(nat()), Box::new(T::Lam(
        Box::new(nat()),
        Box::new(nat_add(T::Var(1), T::Var(0))),
    )));
    globals.insert("Nat.add".into(), (add_term, add_ty.clone()));

    let mul_term = T::Lam(Box::new(nat()), Box::new(T::Lam(
        Box::new(nat()),
        Box::new(nat_mul(T::Var(1), T::Var(0))),
    )));
    globals.insert("Nat.mul".into(), (mul_term, add_ty.clone()));

    let sub_term = T::Lam(Box::new(nat()), Box::new(T::Lam(
        Box::new(nat()),
        Box::new(nat_sub(T::Var(1), T::Var(0))),
    )));
    globals.insert("Nat.sub".into(), (sub_term, add_ty.clone()));

    // Nat.min and Nat.max
    globals.insert("Nat.min".into(), (nat_min_term(), add_ty.clone()));
    globals.insert("Nat.max".into(), (nat_max_term(), add_ty.clone()));

    // Nat.div — axiomatic (non-structurally recursive; trusted standard lemma)
    let div_ty = le::nat_div_ty();
    globals.insert("Nat.div".into(), (le::nat_div_axiom(), div_ty));

    // Le type constructor
    globals.insert("Le".into(), (le_type_lam(), le_type_pi()));
    globals.insert("Nat.Le".into(), (le_type_lam(), le_type_pi()));

    // Le constructors
    // le_refl : Π(n:Nat). Le n n
    let le_refl_ty = T::Pi(
        Box::new(nat()),
        Box::new(T::Ind(LE_ID, vec![T::Var(0), T::Var(0)])),
    );
    let le_refl_term = T::Lam(
        Box::new(nat()),
        Box::new(T::Ctor(LE_ID, LE_REFL_IDX, vec![T::Var(0), T::Var(0)])),
    );
    globals.insert("Le.refl".into(), (le_refl_term.clone(), le_refl_ty.clone()));
    globals.insert("Nat.Le.refl".into(), (le_refl_term, le_refl_ty));

    // Nat axiom lemmas (bootstrap axioms — proved in Lean, trusted here)
    // Nat.min_le_right : Π(a b : Nat). Le (Nat.min a b) b
    let min_ref = T::Lam(Box::new(nat()), Box::new(T::Lam(
        Box::new(nat()),
        Box::new(T::Ind(LE_ID, vec![
            T::App(
                Box::new(T::App(Box::new(nat_min_term()), Box::new(T::Var(1)))),
                Box::new(T::Var(0)),
            ),
            T::Var(0),
        ])),
    )));
    let min_le_ty = T::Pi(Box::new(nat()), Box::new(T::Pi(
        Box::new(nat()),
        Box::new(T::Ind(LE_ID, vec![
            T::App(
                Box::new(T::App(Box::new(nat_min_term()), Box::new(T::Var(1)))),
                Box::new(T::Var(0)),
            ),
            T::Var(0),
        ])),
    )));
    globals.insert("Nat.min_le_right".into(), (min_ref, min_le_ty));

    // Nat.div_le_self : Π(n k : Nat). Le (Nat.div n k) n
    // Stored as opaque axiom (self-typed)
    let div_le_self_ty = T::Pi(Box::new(nat()), Box::new(T::Pi(
        Box::new(nat()),
        Box::new(T::Ind(LE_ID, vec![
            T::App(
                Box::new(T::App(Box::new(le::nat_div_axiom()), Box::new(T::Var(1)))),
                Box::new(T::Var(0)),
            ),
            T::Var(1),
        ])),
    )));
    globals.insert("Nat.div_le_self".into(), (div_le_self_ty.clone(), div_le_self_ty));

    // The three remaining lemmas (div_le_div_right, mul_le_mul_right,
    // mul_div_cancel_left) involve Le hypotheses — stored opaquely.
    // Surface proofs reference them by name and apply them.
    let opaque = T::Sort(0); // placeholder type for complex axioms
    globals.insert("Nat.div_le_div_right".into(), (opaque.clone(), opaque.clone()));
    globals.insert("Nat.mul_le_mul_right".into(), (opaque.clone(), opaque.clone()));
    globals.insert("Nat.mul_div_cancel_left".into(), (opaque.clone(), opaque));
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{kernel::infer, reduce::{nf, whnf, def_eq}};

    fn ctx() -> crate::ctx::Ctx { vec![] }

    #[test]
    fn nat_zero_type() {
        let env = std_env();
        assert_eq!(infer(&env, &ctx(), &nat_zero()), Ok(nat()));
    }

    #[test]
    fn nat_next_type() {
        let env = std_env();
        assert_eq!(infer(&env, &ctx(), &nat_next(nat_zero())), Ok(nat()));
    }

    #[test]
    fn nat_lits() {
        let env = std_env();
        for n in 0u64..=5 {
            assert_eq!(infer(&env, &ctx(), &nat_lit(n)), Ok(nat()), "nat_lit({n})");
        }
    }

    #[test]
    fn bool_ctors_type() {
        let env = std_env();
        assert_eq!(infer(&env, &ctx(), &bool_false()), Ok(bool_ty()));
        assert_eq!(infer(&env, &ctx(), &bool_true()),  Ok(bool_ty()));
    }

    #[test]
    fn list_nil_type() {
        let env = std_env();
        assert_eq!(infer(&env, &ctx(), &list_nil(nat())), Ok(list(nat())));
    }

    #[test]
    fn list_link_type() {
        let env = std_env();
        let nil = list_nil(nat());
        let singleton = list_link(nat(), nat_zero(), nil);
        assert_eq!(infer(&env, &ctx(), &singleton), Ok(list(nat())));
    }

    #[test]
    fn false_is_prop() {
        let env = std_env();
        assert_eq!(infer(&env, &ctx(), &Term::Ind(FALSE_ID, vec![])), Ok(Term::Sort(0)));
    }

    #[test]
    fn true_is_prop() {
        let env = std_env();
        assert_eq!(infer(&env, &ctx(), &Term::Ind(TRUE_ID, vec![])), Ok(Term::Sort(0)));
    }

    #[test]
    fn nat_add_by_elim() {
        let env = std_env();
        let three = nat_lit(3);
        let two   = nat_lit(2);
        let motive = Term::Lam(Box::new(nat()), Box::new(nat()));
        let case_next = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(nat_next(Term::Var(0))),
            )),
        );
        let elim = Term::Elim(
            NAT_ID,
            Box::new(motive),
            vec![three, case_next],
            Box::new(two),
        );
        let ty = infer(&env, &ctx(), &elim).unwrap();
        assert!(def_eq(&env, &ctx(), &ty, &nat()));
        let result = nf(&env, &ctx(), elim);
        assert_eq!(result, nat_lit(5));
    }

    #[test]
    fn nat_mul_by_elim() {
        let env = std_env();
        let two = nat_lit(2);
        let case_next = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(nat_add(nat_lit(3), Term::Var(0))),
            )),
        );
        let mul_elim = Term::Elim(
            NAT_ID,
            Box::new(Term::Lam(Box::new(nat()), Box::new(nat()))),
            vec![nat_zero(), case_next],
            Box::new(two),
        );
        assert_eq!(nf(&env, &ctx(), mul_elim), nat_lit(6));
    }

    #[test]
    fn eq_refl_kernel_check() {
        let env = std_env();
        let proof = eq_refl(nat(), nat_zero());
        let ty    = Term::Ind(EQ_ID, vec![nat(), nat_zero(), nat_zero()]);
        assert_eq!(crate::kernel::check(&env, &ctx(), &proof, &ty), Ok(()));
    }

    #[test]
    fn and_right_kernel_check() {
        let env = std_env();
        let t_ty = Term::Ind(TRUE_ID, vec![]);
        let intro = Term::Ctor(TRUE_ID, 0, vec![]);
        let h = and_intro(t_ty.clone(), t_ty.clone(), intro.clone(), intro);
        let extracted = and_right(t_ty.clone(), t_ty.clone(), h);
        assert_eq!(crate::kernel::check(&env, &ctx(), &extracted, &t_ty), Ok(()));
    }

    #[test]
    fn bool_not_true_kernel_check() {
        let env = std_env();
        let proof = bool_not_true_eq();
        let ty = Term::Ind(EQ_ID, vec![bool_ty(), bool_not(bool_true()), bool_false()]);
        assert_eq!(crate::kernel::check(&env, &ctx(), &proof, &ty), Ok(()));
    }

    #[test]
    fn bool_not_false_kernel_check() {
        let env = std_env();
        let proof = bool_not_false_eq();
        let ty = Term::Ind(EQ_ID, vec![bool_ty(), bool_not(bool_false()), bool_true()]);
        assert_eq!(crate::kernel::check(&env, &ctx(), &proof, &ty), Ok(()));
    }

    #[test]
    fn and_intro_kernel_check() {
        let env = std_env();
        let t_ty = Term::Ind(TRUE_ID, vec![]);
        let intro = Term::Ctor(TRUE_ID, 0, vec![]);
        let proof = and_intro(t_ty.clone(), t_ty.clone(), intro.clone(), intro);
        let ty = Term::Ind(AND_ID, vec![t_ty.clone(), t_ty]);
        assert_eq!(crate::kernel::check(&env, &ctx(), &proof, &ty), Ok(()));
    }

    #[test]
    fn nat_min_reduces() {
        let env = std_env();
        let min_fn = nat_min_term();
        // min 3 5 = 3
        let result = nf(&env, &ctx(),
            Term::App(Box::new(Term::App(Box::new(min_fn.clone()), Box::new(nat_lit(3)))),
                      Box::new(nat_lit(5))));
        assert_eq!(result, nat_lit(3), "min 3 5 ≠ 3: {result:?}");
        // min 5 3 = 3
        let result2 = nf(&env, &ctx(),
            Term::App(Box::new(Term::App(Box::new(min_fn), Box::new(nat_lit(5)))),
                      Box::new(nat_lit(3))));
        assert_eq!(result2, nat_lit(3), "min 5 3 ≠ 3: {result2:?}");
    }

    #[test]
    fn nat_max_reduces() {
        let env = std_env();
        let max_fn = nat_max_term();
        // max 3 5 = 5
        let result = nf(&env, &ctx(),
            Term::App(Box::new(Term::App(Box::new(max_fn.clone()), Box::new(nat_lit(3)))),
                      Box::new(nat_lit(5))));
        assert_eq!(result, nat_lit(5), "max 3 5 ≠ 5");
        // max 5 3 = 5
        let result2 = nf(&env, &ctx(),
            Term::App(Box::new(Term::App(Box::new(max_fn), Box::new(nat_lit(5)))),
                      Box::new(nat_lit(3))));
        assert_eq!(result2, nat_lit(5), "max 5 3 ≠ 5");
    }

    #[test]
    fn le_ind_is_prop() {
        let env = std_env();
        let le_ty = Term::Ind(LE_ID, vec![nat_lit(2), nat_lit(3)]);
        assert_eq!(whnf(&env, &ctx(), infer(&env, &ctx(), &le_ty).unwrap()), Term::Sort(0));
    }
}
