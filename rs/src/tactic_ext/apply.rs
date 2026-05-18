// tactic_ext/apply.rs — tac_apply
use crate::{
    env::Env,
    kernel::infer,
    reduce::{def_eq, whnf},
    term::Term,
};
use crate::tactic::{MetaEnv, ProofState, TacticError};

/// apply e: unify the conclusion of e's type with the goal; generate premise subgoals.
pub fn tac_apply(state: &mut ProofState, term: Term) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    let goal_names = goal.names.clone();
    let expected = goal.expected.clone();
    let meta = goal.meta;

    let f_ty = infer(env, &ctx, &term).map_err(TacticError::Kernel)?;
    let (arg_metas, arg_tys, concl) = peel_pi_metas(&state.metas, env, &ctx, f_ty);
    state.metas.next += arg_metas.len() as u64;

    if !def_eq(env, &ctx, &concl, &expected) {
        return Err(TacticError::TacticFailed("apply: conclusion does not match goal".into()));
    }

    let mut result = term;
    for mid in &arg_metas {
        result = Term::App(Box::new(result), Box::new(Term::Meta(*mid)));
    }
    state.metas.assign(meta, result);
    state.goals.remove(0);

    let mut new_goals = Vec::new();
    for (mid, arg_ty) in arg_metas.into_iter().zip(arg_tys.into_iter()) {
        if state.metas.lookup(mid).is_none() {
            new_goals.push(crate::tactic::Goal {
                local_ctx: ctx.clone(),
                names: goal_names.clone(),
                meta: mid,
                expected: arg_ty,
                label: None,
            });
        }
    }
    let mut goals = std::mem::take(&mut state.goals);
    goals.splice(0..0, new_goals);
    state.goals = goals;
    Ok(())
}

pub(super) fn peel_pi_metas(menv: &MetaEnv, env: &Env, ctx: &crate::ctx::Ctx, mut ty: Term)
    -> (Vec<u64>, Vec<Term>, Term)
{
    let mut meta_ids  = Vec::new();
    let mut meta_tys  = Vec::new();
    let mut next_id = menv.next;
    loop {
        match whnf(env, ctx, ty) {
            Term::Pi(a, b) => {
                meta_ids.push(next_id);
                meta_tys.push(*a.clone());
                ty = crate::subst::subst(&b, &Term::Meta(next_id));
                next_id += 1;
            }
            other => return (meta_ids, meta_tys, other),
        }
    }
}
