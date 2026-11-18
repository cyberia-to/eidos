// tests for tactic — split out so that tactic.rs stays under the 500-line cap.

use super::*;
use crate::stdlib::{nat, nat_zero, std_env};

#[test]
fn exact_closes_goal() {
    let env = std_env();
    // Goal: Nat. Provide: nat_zero().
    let mut ps = ProofState::new(env.clone(), nat());
    assert_eq!(ps.goals.len(), 1);
    tac_exact(&mut ps, nat_zero()).unwrap();
    assert!(ps.is_complete());
}

#[test]
fn exact_wrong_type_fails() {
    let env = std_env();
    let mut ps = ProofState::new(env.clone(), nat());
    // Provide Sort(0) (Prop), not Nat
    let result = tac_exact(&mut ps, Term::Sort(0));
    assert!(result.is_err());
    assert_eq!(ps.goals.len(), 1); // goal not removed
}

#[test]
fn intro_peels_pi() {
    let env = std_env();
    // Goal: Nat → Nat
    let goal_ty = Term::Pi(Box::new(nat()), Box::new(nat()));
    let mut ps = ProofState::new(env, goal_ty);
    tac_intro(&mut ps, "n").unwrap();
    // After intro, goal is Nat (the body) with n:Nat in ctx
    assert_eq!(ps.goals[0].expected, nat());
    assert_eq!(ps.goals[0].local_ctx.len(), 1);
}

#[test]
fn intro_fails_on_non_pi() {
    let env = std_env();
    let mut ps = ProofState::new(env, nat());
    assert!(tac_intro(&mut ps, "n").is_err());
}

#[test]
fn assumption_finds_hyp() {
    let env = std_env();
    // Goal: Nat, with hypothesis n:Nat in context.
    let goal_ty = nat();
    let mut ps = ProofState::new(env, goal_ty);
    push_var(&mut ps.goals[0].local_ctx, nat()); // n : Nat
    tac_assumption(&mut ps).unwrap();
    assert!(ps.is_complete());
}

#[test]
fn rfl_closes_eq() {
    use crate::stdlib::{nat_zero, EQ_ID};
    let env = std_env();
    // Goal: Eq Nat zero zero
    let goal_ty = Term::Ind(EQ_ID, vec![nat(), nat_zero(), nat_zero()]);
    let mut ps = ProofState::new(env, goal_ty);
    tac_rfl(&mut ps).unwrap();
    assert!(ps.is_complete());
}

#[test]
fn skip_leaves_goals() {
    let env = std_env();
    let mut ps = ProofState::new(env, nat());
    tac_skip(&mut ps).unwrap();
    assert_eq!(ps.goals.len(), 1);
}

#[test]
fn try_ignores_failure() {
    let env = std_env();
    let mut ps = ProofState::new(env, nat());
    // tac_intro will fail (Nat is not Pi), but try should swallow it
    tac_try(&mut ps, |s| tac_intro(s, "n")).unwrap();
    assert_eq!(ps.goals.len(), 1); // goal unchanged
}

#[test]
fn first_picks_first_success() {
    let env = std_env();
    let mut ps = ProofState::new(env, nat());
    tac_first(
        &mut ps,
        vec![
            |s: &mut ProofState| tac_intro(s, "n"),        // fails
            |s: &mut ProofState| tac_exact(s, nat_zero()), // succeeds
        ],
    )
    .unwrap();
    assert!(ps.is_complete());
}

#[test]
fn revert_wraps_goal_in_pi() {
    let env = std_env();
    let goal_ty = nat();
    let mut ps = ProofState::new(env, goal_ty);
    push_var(&mut ps.goals[0].local_ctx, nat()); // n : Nat
    tac_revert(&mut ps, 0).unwrap();
    // Goal becomes Nat → Nat
    let expected = Term::Pi(Box::new(nat()), Box::new(nat()));
    assert_eq!(ps.goals[0].expected, expected);
    assert_eq!(ps.goals[0].local_ctx.len(), 0);
}

#[test]
fn show_replaces_goal_def_eq() {
    let env = std_env();
    // Goal: APP(λ_.Nat, zero) (reduces to Nat)
    let goal_ty = Term::App(
        Box::new(Term::Lam(Box::new(nat()), Box::new(nat()))),
        Box::new(nat_zero()),
    );
    let mut ps = ProofState::new(env, goal_ty);
    tac_show(&mut ps, nat()).unwrap(); // display as Nat
    assert_eq!(ps.goals[0].expected, nat());
}

#[test]
fn intro_then_exact_verify() {
    // Proof of Nat → Nat: intro n, exact n.
    // verify() must succeed — this tests the LAM assembly fix.
    let env = std_env();
    let goal_ty = Term::Pi(Box::new(nat()), Box::new(nat()));
    let mut ps = ProofState::new(env.clone(), goal_ty.clone());
    tac_intro(&mut ps, "n").unwrap();
    // Goal is now Nat with n:Nat in context
    assert_eq!(ps.goals[0].expected, nat());
    tac_exact(&mut ps, Term::Var(0)).unwrap();
    assert!(ps.is_complete());
    assert!(ps.verify(&goal_ty).is_ok(), "intro+exact verify failed");
}

#[test]
fn intro_twice_verify() {
    // Proof of Nat → Nat → Nat: intro n m, exact n.
    let env = std_env();
    let goal_ty = Term::Pi(
        Box::new(nat()),
        Box::new(Term::Pi(Box::new(nat()), Box::new(nat()))),
    );
    let mut ps = ProofState::new(env.clone(), goal_ty.clone());
    tac_intro(&mut ps, "n").unwrap();
    tac_intro(&mut ps, "m").unwrap();
    assert_eq!(ps.goals[0].local_ctx.len(), 2);
    tac_exact(&mut ps, Term::Var(1)).unwrap(); // VAR(1) = n (outer)
    assert!(ps.is_complete());
    assert!(
        ps.verify(&goal_ty).is_ok(),
        "double intro+exact verify failed"
    );
}

#[test]
fn clear_decrements_indices() {
    let env = std_env();
    // Goal: Nat. Context: [Bool, Nat] (innermost Bool at 0, Nat at 1)
    // expected references VAR(1) = Nat
    let goal_ty = Term::Var(1); // refers to the outer Nat hypothesis
    let mut ps = ProofState::new(env, goal_ty);
    push_var(&mut ps.goals[0].local_ctx, nat()); // VAR(0) = Nat
    push_var(&mut ps.goals[0].local_ctx, crate::stdlib::bool_ty()); // VAR(0)=Bool, VAR(1)=Nat
                                                                    // Reverse: after 2 push_vars, ctx = [Bool, Nat], expected still VAR(1)
                                                                    // Clear VAR(0) = Bool (must not appear free in goal which has VAR(1))
    tac_clear(&mut ps, 0).unwrap();
    // After clear, ctx = [Nat], and old VAR(1) should become VAR(0)
    assert_eq!(ps.goals[0].local_ctx.len(), 1);
    assert_eq!(ps.goals[0].expected, Term::Var(0));
}

#[test]
fn var_free_in_checks() {
    // VAR(0) is free in Var(0)
    assert!(var_free_in(0, &Term::Var(0)));
    // VAR(0) is not free in Var(1)
    assert!(!var_free_in(0, &Term::Var(1)));
    // VAR(0) is not free in LAM(Sort(0), Var(0)) — it's bound
    let lam = Term::Lam(Box::new(Term::Sort(0)), Box::new(Term::Var(0)));
    assert!(!var_free_in(0, &lam));
    // VAR(1) IS free in LAM(Sort(0), Var(1)) — it refers to outer context
    let lam2 = Term::Lam(Box::new(Term::Sort(0)), Box::new(Term::Var(1)));
    assert!(var_free_in(0, &lam2)); // idx=0, under lam depth=1 → checks Var(1) == 0+1 = 1 ✓
}
