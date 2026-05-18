// tactic_ext/arith.rs — tac_omega, tac_simp, tac_decide
use crate::{
    stdlib::{eq_refl, le_of_lits, EQ_ID, LE_ID, NAT_ID},
    term::Term,
};
use crate::tactic::{ProofState, TacticError};

/// omega — solve decidable Nat arithmetic goals.
/// Normalizes the goal, then closes if it reduces to Eq _ a b where a ≡ b,
/// or Le a b where both are Nat literals with a ≤ b.
pub fn tac_omega(state: &mut ProofState) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    let meta = goal.meta;

    let reduced = crate::reduce::nf(env, &ctx, goal.expected.clone());

    // Case 1: Eq _ a b with def_eq(a, b)
    if let Term::Ind(id, ref params) = reduced {
        if id == EQ_ID && params.len() == 3
            && crate::reduce::def_eq(env, &ctx, &params[1], &params[2])
        {
            let proof = eq_refl(params[0].clone(), params[1].clone());
            state.metas.assign(meta, proof);
            state.goals.remove(0);
            return Ok(());
        }
        // Case 2: Le a b where both reduce to Nat literals
        if id == LE_ID && params.len() == 2 {
            if let (Some(n), Some(m)) = (nat_lit_val(&params[0], env, &ctx), nat_lit_val(&params[1], env, &ctx)) {
                if n <= m {
                    let proof = le_of_lits(n, m);
                    state.metas.assign(meta, proof);
                    state.goals.remove(0);
                    return Ok(());
                }
            }
        }
    }
    Err(TacticError::TacticFailed("omega: cannot solve this goal".into()))
}

/// simp — normalize the goal type via full β/δ/ι reduction.
pub fn tac_simp(state: &mut ProofState) -> Result<(), TacticError> {
    let goal = state.goals.first_mut().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    goal.expected = crate::reduce::nf(env, &ctx, goal.expected.clone());
    Ok(())
}

/// decide — close decidable ground propositions: tries rfl, then omega.
/// For Le/Lt goals with concrete Nat values, builds the proof term.
pub fn tac_decide(state: &mut ProofState) -> Result<(), TacticError> {
    let saved = state.clone();
    if crate::tactic::tac_rfl(state).is_ok() { return Ok(()); }
    *state = saved;
    tac_omega(state)
}

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Extract the numeric value from a Nat literal term (after normalization).
fn nat_lit_val(t: &Term, env: &crate::env::Env, ctx: &crate::ctx::Ctx) -> Option<u64> {
    let nf = crate::reduce::nf(env, ctx, t.clone());
    count_succ(&nf)
}

fn count_succ(t: &Term) -> Option<u64> {
    match t {
        Term::Ctor(id, 0, args) if *id == NAT_ID && args.is_empty() => Some(0),
        Term::Ctor(id, 1, args) if *id == NAT_ID && args.len() == 1 => {
            Some(1 + count_succ(&args[0])?)
        }
        _ => None,
    }
}
