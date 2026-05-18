// tactic_ext/have.rs — tac_have_exact, tac_have_goal
use crate::{ctx::CtxEntry, term::Term};
use crate::tactic::{ProofState, TacticError};
use crate::subst::shift;

/// have h : T := e — introduce a local fact proved by term e.
pub fn tac_have_exact(
    state: &mut ProofState,
    hyp_name: &str,
    ty: Term,
    proof: Term,
) -> Result<(), TacticError> {
    let goal = state.goals.first_mut().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = &goal.local_ctx.clone();
    crate::kernel::check(env, ctx, &proof, &ty).map_err(TacticError::Kernel)?;
    goal.local_ctx.insert(0, CtxEntry::Let(ty, proof));
    goal.names.insert(0, hyp_name.to_string());
    Ok(())
}

/// have h : T — create a subgoal for T, add h to the continuation goal context.
pub fn tac_have_goal(
    state: &mut ProofState,
    name: &str,
    ty: Term,
) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let ctx = goal.local_ctx.clone();
    let ctx_names = goal.names.clone();
    let original_expected = goal.expected.clone();
    let original_meta = goal.meta;

    let m_h    = state.metas.next;
    let m_body = state.metas.next + 1;
    state.metas.next += 2;

    state.metas.assign(original_meta, Term::Let(
        Box::new(ty.clone()),
        Box::new(Term::Meta(m_h)),
        Box::new(Term::Meta(m_body)),
    ));
    state.goals.remove(0);

    let have_goal = crate::tactic::Goal {
        local_ctx: ctx.clone(),
        names: ctx_names.clone(),
        meta: m_h,
        expected: ty.clone(),
        label: Some("have".into()),
    };

    let mut cont_ctx = ctx;
    cont_ctx.insert(0, CtxEntry::Var(ty));
    let mut cont_names = ctx_names;
    cont_names.insert(0, name.to_string());
    let cont_goal = crate::tactic::Goal {
        local_ctx: cont_ctx,
        names: cont_names,
        meta: m_body,
        expected: shift(&original_expected, 1),
        label: Some("cont".into()),
    };

    state.goals.insert(0, cont_goal);
    state.goals.insert(0, have_goal);
    Ok(())
}
