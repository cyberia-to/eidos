// globals — stdlib name registration for the elaborator
// spec: specs/surface.md § elaboration algorithm
// Split out of core.rs so that neither file exceeds the 500-line cap.

use super::core::ElabState;
use crate::term::Term;

impl ElabState {
    /// Populate globals with stdlib constructors and type names.
    pub fn add_stdlib(&mut self) {
        crate::stdlib::binary::add_globals(&mut self.globals);
        crate::stdlib::binary_nat::add_globals(&mut self.globals);
        use crate::stdlib::*;
        let nat_arr = Term::Pi(Box::new(nat()), Box::new(nat()));
        let type1 = Term::Sort(1);
        let list_fn = Term::Lam(
            Box::new(type1.clone()),
            Box::new(Term::Ind(LIST_ID, vec![Term::Var(0)])),
        );
        let list_ty = Term::Pi(Box::new(type1.clone()), Box::new(type1.clone()));
        let nil_fn = Term::Lam(
            Box::new(type1.clone()),
            Box::new(Term::Ctor(LIST_ID, LIST_NIL_IDX, vec![Term::Var(0)])),
        );
        let nil_ty = Term::Pi(
            Box::new(type1.clone()),
            Box::new(Term::Ind(LIST_ID, vec![Term::Var(0)])),
        );
        let next_fn = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Ctor(NAT_ID, NAT_NEXT, vec![Term::Var(0)])),
        );
        let eq_fn = Term::Lam(
            Box::new(type1.clone()),
            Box::new(Term::Lam(
                Box::new(Term::Var(0)),
                Box::new(Term::Lam(
                    Box::new(Term::Var(1)),
                    Box::new(Term::Ind(
                        EQ_ID,
                        vec![Term::Var(2), Term::Var(1), Term::Var(0)],
                    )),
                )),
            )),
        );
        let eq_ty = Term::Pi(
            Box::new(type1.clone()),
            Box::new(Term::Pi(
                Box::new(Term::Var(0)),
                Box::new(Term::Pi(Box::new(Term::Var(1)), Box::new(Term::Sort(0)))),
            )),
        );
        self.globals.insert("Nat".into(), (nat(), type1.clone()));
        self.globals.insert("Nat.zero".into(), (nat_zero(), nat()));
        self.globals
            .insert("Nat.next".into(), (next_fn.clone(), nat_arr.clone()));
        self.globals
            .insert("Bool".into(), (bool_ty(), type1.clone()));
        self.globals
            .insert("Bool.false".into(), (bool_false(), bool_ty()));
        self.globals
            .insert("Bool.true".into(), (bool_true(), bool_ty()));
        self.globals
            .insert("True".into(), (Term::Ind(TRUE_ID, vec![]), Term::Sort(0)));
        self.globals
            .insert("False".into(), (Term::Ind(FALSE_ID, vec![]), Term::Sort(0)));
        self.globals.insert("List".into(), (list_fn, list_ty));
        self.globals.insert("List.nil".into(), (nil_fn, nil_ty));
        self.globals.insert("Eq".into(), (eq_fn, eq_ty));

        // Arithmetic
        let nat_nat_nat = Term::Pi(
            Box::new(nat()),
            Box::new(Term::Pi(Box::new(nat()), Box::new(nat()))),
        );
        let add_fn = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(nat_add(Term::Var(1), Term::Var(0))),
            )),
        );
        let mul_fn = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(nat_mul(Term::Var(1), Term::Var(0))),
            )),
        );
        self.globals
            .insert("Nat.add".into(), (add_fn, nat_nat_nat.clone()));
        self.globals
            .insert("Nat.mul".into(), (mul_fn, nat_nat_nat.clone()));
        self.globals
            .insert("Nat.succ".into(), (next_fn.clone(), nat_arr.clone()));

        // Eq.refl : ∀ (A : Type) (a : A), Eq A a a
        let eq_refl_fn = Term::Lam(
            Box::new(type1.clone()),
            Box::new(Term::Lam(
                Box::new(Term::Var(0)),
                Box::new(eq_refl(Term::Var(1), Term::Var(0))),
            )),
        );
        let eq_refl_ty = Term::Pi(
            Box::new(type1.clone()),
            Box::new(Term::Pi(
                Box::new(Term::Var(0)),
                Box::new(Term::Ind(
                    EQ_ID,
                    vec![Term::Var(1), Term::Var(0), Term::Var(0)],
                )),
            )),
        );
        self.globals
            .insert("Eq.refl".into(), (eq_refl_fn, eq_refl_ty));

        // And : Prop → Prop → Prop
        let and_fn = Term::Lam(
            Box::new(Term::Sort(0)),
            Box::new(Term::Lam(
                Box::new(Term::Sort(0)),
                Box::new(Term::Ind(AND_ID, vec![Term::Var(1), Term::Var(0)])),
            )),
        );
        let and_ty = Term::Pi(
            Box::new(Term::Sort(0)),
            Box::new(Term::Pi(Box::new(Term::Sort(0)), Box::new(Term::Sort(0)))),
        );
        self.globals.insert("And".into(), (and_fn, and_ty));

        // And.intro : ∀ P Q : Prop, P → Q → And P Q
        let and_intro_fn = Term::Lam(
            Box::new(Term::Sort(0)),
            Box::new(
                // P
                Term::Lam(
                    Box::new(Term::Sort(0)),
                    Box::new(
                        // Q
                        Term::Lam(
                            Box::new(Term::Var(1)),
                            Box::new(
                                // p : P
                                Term::Lam(
                                    Box::new(Term::Var(1)),
                                    Box::new(
                                        // q : Q (P shifted)
                                        Term::Ctor(
                                            AND_ID,
                                            0,
                                            vec![
                                                Term::Var(3),
                                                Term::Var(2),
                                                Term::Var(1),
                                                Term::Var(0),
                                            ],
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        );
        let and_intro_ty = Term::Pi(
            Box::new(Term::Sort(0)),
            Box::new(
                // P
                Term::Pi(
                    Box::new(Term::Sort(0)),
                    Box::new(
                        // Q
                        Term::Pi(
                            Box::new(Term::Var(1)),
                            Box::new(
                                // p : P
                                Term::Pi(
                                    Box::new(Term::Var(1)),
                                    Box::new(
                                        // q : Q
                                        Term::Ind(AND_ID, vec![Term::Var(3), Term::Var(2)]),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        );
        self.globals
            .insert("And.intro".into(), (and_intro_fn, and_intro_ty));

        // Le : Nat → Nat → Prop
        self.globals
            .insert("Le".into(), (le_type_lam(), le_type_pi()));
        self.globals
            .insert("Nat.Le".into(), (le_type_lam(), le_type_pi()));

        // Le.refl : Π(n:Nat). Le n n
        let le_refl_ty = Term::Pi(
            Box::new(nat()),
            Box::new(Term::Ind(LE_ID, vec![Term::Var(0), Term::Var(0)])),
        );
        let le_refl_term = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Ctor(
                LE_ID,
                LE_REFL_IDX,
                vec![Term::Var(0), Term::Var(0)],
            )),
        );
        self.globals
            .insert("Le.refl".into(), (le_refl_term.clone(), le_refl_ty.clone()));
        self.globals
            .insert("Nat.Le.refl".into(), (le_refl_term, le_refl_ty));

        // Le.step : Π(n m : Nat). Le n m → Le n (Nat.succ m)
        let le_step_ty = Term::Pi(
            Box::new(nat()),
            Box::new(Term::Pi(
                Box::new(nat()),
                Box::new(Term::Pi(
                    Box::new(Term::Ind(LE_ID, vec![Term::Var(1), Term::Var(0)])),
                    Box::new(Term::Ind(LE_ID, vec![Term::Var(2), nat_next(Term::Var(1))])),
                )),
            )),
        );
        let le_step_fn = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(Term::Lam(
                    Box::new(Term::Ind(LE_ID, vec![Term::Var(1), Term::Var(0)])),
                    Box::new(Term::Ctor(
                        LE_ID,
                        LE_STEP_IDX,
                        vec![Term::Var(2), Term::Var(1), Term::Var(0)],
                    )),
                )),
            )),
        );
        self.globals
            .insert("Le.step".into(), (le_step_fn.clone(), le_step_ty.clone()));
        self.globals
            .insert("Nat.Le.step".into(), (le_step_fn, le_step_ty));

        // Nat.min, Nat.max : Nat → Nat → Nat
        self.globals
            .insert("Nat.min".into(), (nat_min_term(), nat_nat_nat.clone()));
        self.globals
            .insert("Nat.max".into(), (nat_max_term(), nat_nat_nat.clone()));

        // Nat.sub : Nat → Nat → Nat (saturating)
        let sub_fn = Term::Lam(
            Box::new(nat()),
            Box::new(Term::Lam(
                Box::new(nat()),
                Box::new(crate::stdlib::nat_sub(Term::Var(1), Term::Var(0))),
            )),
        );
        self.globals
            .insert("Nat.sub".into(), (sub_fn, nat_nat_nat.clone()));

        // Nat.div : Nat → Nat → Nat (axiomatic)
        self.globals
            .insert("Nat.div".into(), (nat_nat_nat.clone(), nat_nat_nat.clone()));

        // Nat axiom lemmas (bootstrap — proved in Lean, trusted here)
        let opaque = Term::Sort(0);
        self.globals
            .insert("Nat.min_le_right".into(), (opaque.clone(), opaque.clone()));
        self.globals
            .insert("Nat.div_le_self".into(), (opaque.clone(), opaque.clone()));
        self.globals.insert(
            "Nat.div_le_div_right".into(),
            (opaque.clone(), opaque.clone()),
        );
        self.globals.insert(
            "Nat.mul_le_mul_right".into(),
            (opaque.clone(), opaque.clone()),
        );
        self.globals
            .insert("Nat.mul_div_cancel_left".into(), (opaque.clone(), opaque));
    }
}
