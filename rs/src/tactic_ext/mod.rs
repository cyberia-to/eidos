// tactic_ext/mod.rs — extended tactics: re-exports and tests
// spec: specs/tactics.md § core tactics + tactic library

pub mod apply;
pub mod elim;
pub mod have;
pub mod rewrite;
pub mod arith;
pub mod derived;

pub use apply::tac_apply;
pub use elim::{tac_induction, tac_cases};
pub use have::{tac_have_exact, tac_have_goal};
pub use rewrite::tac_rewrite;
pub use arith::{tac_omega, tac_simp, tac_decide};
pub use derived::{
    tac_contradiction, tac_constructor, tac_left, tac_right, tac_trivial,
    tac_repeat, tac_seq,
};

// ── tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use crate::ctx::CtxEntry;
    use crate::stdlib::{nat, nat_zero, std_env};
    use crate::tactic::ProofState;
    use crate::term::Term;
    use super::*;

    #[test]
    fn apply_ctor_closes_nat_goal() {
        let env = std_env();
        let mut ps = ProofState::new(env, nat());
        tac_apply(&mut ps, nat_zero()).unwrap();
        assert!(ps.is_complete());
    }

    #[test]
    fn repeat_intro() {
        let env = std_env();
        let pi_ty = Term::Pi(Box::new(nat()), Box::new(nat()));
        let mut ps = ProofState::new(env, pi_ty);
        tac_repeat(&mut ps, |s| crate::tactic::tac_intro(s, "_")).unwrap();
        assert_eq!(ps.goals[0].expected, nat());
    }

    #[test]
    fn contradiction_with_false_hyp() {
        let env = std_env();
        let mut ps = ProofState::new(env, nat());
        let false_ty = Term::Ind(crate::stdlib::FALSE_ID, vec![]);
        ps.goals[0].local_ctx.push(CtxEntry::Var(false_ty));
        tac_contradiction(&mut ps).unwrap();
        assert!(ps.is_complete());
    }

    #[test]
    fn cases_strips_ih_binders() {
        let env = std_env();
        let p_of_n = Term::App(Box::new(Term::Var(1)), Box::new(Term::Var(0)));
        let mut ps = ProofState::new(env, p_of_n);
        ps.goals[0].local_ctx.push(CtxEntry::Var(nat()));
        tac_cases(&mut ps, 0).unwrap();
        assert_eq!(ps.goals.len(), 2);
        let next_case_ty = &ps.goals[1].expected;
        if let Term::Pi(_, body) = next_case_ty {
            assert!(!matches!(body.as_ref(), Term::Pi(_, _)), "IH binder not stripped");
        }
    }

    #[test]
    fn have_goal_wires_continuation() {
        let env = std_env();
        let mut ps = ProofState::new(env.clone(), nat());
        tac_have_goal(&mut ps, "_", nat()).unwrap();
        assert_eq!(ps.goals.len(), 2);
        assert_eq!(ps.goals[0].expected, nat());
        assert_eq!(ps.goals[1].local_ctx.len(), 1);
        crate::tactic::tac_exact(&mut ps, nat_zero()).unwrap();
        crate::tactic::tac_exact(&mut ps, Term::Var(0)).unwrap();
        assert!(ps.verify(&nat()).is_ok(), "have_goal proof failed to verify");
    }

    #[test]
    fn simp_normalizes_goal() {
        let env = std_env();
        let redex = Term::App(
            Box::new(Term::Lam(Box::new(nat()), Box::new(nat()))),
            Box::new(nat_zero()),
        );
        let mut ps = ProofState::new(env, redex);
        tac_simp(&mut ps).unwrap();
        assert_eq!(ps.goals[0].expected, nat());
    }

    #[test]
    fn omega_solves_concrete_eq() {
        let env = std_env();
        use crate::stdlib::{nat_lit, EQ_ID};
        let goal_ty = Term::Ind(EQ_ID, vec![nat(), nat_lit(2), nat_lit(2)]);
        let mut ps = ProofState::new(env, goal_ty);
        tac_omega(&mut ps).unwrap();
        assert!(ps.is_complete());
    }

    #[test]
    fn omega_solves_concrete_le() {
        let env = std_env();
        use crate::stdlib::{nat_lit, LE_ID};
        let goal_ty = Term::Ind(LE_ID, vec![nat_lit(2), nat_lit(5)]);
        let mut ps = ProofState::new(env, goal_ty);
        tac_omega(&mut ps).unwrap();
        assert!(ps.is_complete());
    }

    #[test]
    fn decide_closes_le_goal() {
        let env = std_env();
        use crate::stdlib::{nat_lit, LE_ID};
        let goal_ty = Term::Ind(LE_ID, vec![nat_lit(0), nat_lit(3)]);
        let mut ps = ProofState::new(env, goal_ty);
        tac_decide(&mut ps).unwrap();
        assert!(ps.is_complete());
    }

    #[test]
    fn induction_generates_cases() {
        let env = std_env();
        let p_of_n = Term::App(Box::new(Term::Var(1)), Box::new(Term::Var(0)));
        let mut ps = ProofState::new(env, p_of_n);
        ps.goals[0].local_ctx.push(CtxEntry::Var(nat()));
        let result = tac_induction(&mut ps, 0);
        assert!(result.is_ok(), "induction failed: {:?}", result);
        assert_eq!(ps.goals.len(), 2);
    }
}
