// tactic_ext/derived.rs — contradiction, constructor, left, right, trivial, repeat, seq
use crate::{
    reduce::whnf,
    stdlib::{FALSE_ID, TRUE_ID},
    subst::shift,
    term::Term,
};
use crate::tactic::{ProofState, TacticError};
use super::apply::tac_apply;

/// contradiction — find h : False in local ctx and close via False.elim.
pub fn tac_contradiction(state: &mut ProofState) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    let meta = goal.meta;

    for (i, entry) in ctx.iter().enumerate() {
        let ty = entry.ty().clone();
        if let Term::Ind(id, _) = whnf(env, &ctx, ty) {
            if id == FALSE_ID {
                let false_elim = Term::Elim(
                    FALSE_ID,
                    Box::new(Term::Lam(
                        Box::new(Term::Ind(FALSE_ID, vec![])),
                        Box::new(shift(&goal.expected, 1)),
                    )),
                    vec![],
                    Box::new(Term::Var(i as u64)),
                );
                state.metas.assign(meta, false_elim);
                state.goals.remove(0);
                return Ok(());
            }
        }
    }
    Err(TacticError::NoContradiction)
}

/// constructor — apply the first constructor of the goal's inductive type.
pub fn tac_constructor(state: &mut ProofState) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    let expected = whnf(env, &ctx, goal.expected.clone());
    match expected {
        Term::Ind(id, params) => {
            let desc = env.lookup(id)
                .ok_or_else(|| TacticError::TacticFailed("constructor: unknown inductive".into()))?
                .clone();
            if desc.constructors.is_empty() {
                return Err(TacticError::TacticFailed("constructor: no constructors".into()));
            }
            let ctor = Term::Ctor(id, 0, params.clone());
            crate::tactic::tac_exact(state, ctor)
        }
        other => Err(TacticError::TacticFailed(
            format!("constructor: goal is not an inductive: {other:?}")
        )),
    }
}

/// left — Or introduction (constructor 0).
pub fn tac_left(state: &mut ProofState) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    match whnf(env, &ctx, goal.expected.clone()) {
        Term::Ind(id, params) => tac_apply(state, Term::Ctor(id, 0, params)),
        _ => Err(TacticError::TacticFailed("left: goal is not Or".into())),
    }
}

/// right — Or introduction (constructor 1).
pub fn tac_right(state: &mut ProofState) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    match whnf(env, &ctx, goal.expected.clone()) {
        Term::Ind(id, params) => tac_apply(state, Term::Ctor(id, 1, params)),
        _ => Err(TacticError::TacticFailed("right: goal is not Or".into())),
    }
}

/// trivial — try rfl, then assumption, then True.intro.
pub fn tac_trivial(state: &mut ProofState) -> Result<(), TacticError> {
    use crate::tactic::{tac_rfl, tac_assumption, tac_exact};
    let saved = state.clone();
    if tac_rfl(state).is_ok()        { return Ok(()); }
    *state = saved.clone();
    if tac_assumption(state).is_ok() { return Ok(()); }
    *state = saved;
    tac_exact(state, Term::Ctor(TRUE_ID, 0, vec![]))
}

/// repeat t — apply t until it fails, then succeed.
pub fn tac_repeat<F>(state: &mut ProofState, mut tac: F) -> Result<(), TacticError>
where
    F: FnMut(&mut ProofState) -> Result<(), TacticError>,
{
    loop {
        let saved = state.clone();
        match tac(state) {
            Ok(()) => {}
            Err(_) => { *state = saved; return Ok(()); }
        }
    }
}

/// broadcast: apply t1 then apply t2 to every new goal t1 produces.
pub fn tac_seq<F, G>(state: &mut ProofState, t1: F, t2: G) -> Result<(), TacticError>
where
    F: FnOnce(&mut ProofState) -> Result<(), TacticError>,
    G: Fn(&mut ProofState) -> Result<(), TacticError>,
{
    let n_before = state.goals.len();
    t1(state)?;
    let n_new = state.goals.len().saturating_sub(n_before.saturating_sub(1));
    let saved = state.clone();
    for _ in 0..n_new {
        match t2(state) {
            Ok(()) => {}
            Err(e) => { *state = saved; return Err(e); }
        }
    }
    Ok(())
}
