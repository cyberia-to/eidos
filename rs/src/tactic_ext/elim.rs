// tactic_ext/elim.rs — tac_induction, tac_cases
use crate::{
    kernel::{case_type, infer},
    reduce::whnf,
    term::Term,
};
use crate::tactic::{ProofState, TacticError};

/// induction x — apply the eliminator for x's inductive type (with IH).
pub fn tac_induction(state: &mut ProofState, hyp_idx: usize) -> Result<(), TacticError> {
    elim_tactic(state, hyp_idx, true)
}

/// cases x — case split without IH subgoals.
pub fn tac_cases(state: &mut ProofState, hyp_idx: usize) -> Result<(), TacticError> {
    elim_tactic(state, hyp_idx, false)
}

fn elim_tactic(state: &mut ProofState, hyp_idx: usize, with_ih: bool) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    let ctx_names = goal.names.clone();
    let expected = goal.expected.clone();
    let meta = goal.meta;

    let tgt = Term::Var(hyp_idx as u64);
    let tgt_ty = infer(env, &ctx, &tgt).map_err(TacticError::Kernel)?;
    let (ind_id, params) = match whnf(env, &ctx, tgt_ty) {
        Term::Ind(id, ps) => (id, ps),
        other => return Err(TacticError::TacticFailed(
            format!("induction/cases: expected inductive type, got {:?}", other)
        )),
    };
    let desc = env.lookup(ind_id)
        .ok_or_else(|| TacticError::TacticFailed("unknown inductive".into()))?
        .clone();

    let motive = Term::Lam(
        Box::new(Term::Ind(ind_id, params.clone())),
        Box::new(expected.clone()),
    );

    let n_ctors = desc.constructors.len();
    let mut case_metas: Vec<u64> = Vec::with_capacity(n_ctors);
    let base_next = state.metas.next;
    for i in 0..n_ctors { case_metas.push(base_next + i as u64); }
    state.metas.next += n_ctors as u64;

    let cases_terms: Vec<Term> = case_metas.iter().map(|&m| Term::Meta(m)).collect();
    let elim = Term::Elim(ind_id, Box::new(motive.clone()), cases_terms, Box::new(tgt));
    state.metas.assign(meta, elim);
    state.goals.remove(0);

    let mut new_goals = Vec::new();
    for (k, ctor_tel) in desc.constructors.iter().enumerate() {
        let expected_case = case_type(env, &ctx, ctor_tel, k, ind_id, &motive, &params);
        let case_ty = if with_ih { expected_case } else { strip_ih_binders(expected_case, ind_id) };
        new_goals.push(crate::tactic::Goal {
            local_ctx: ctx.clone(),
            names: ctx_names.clone(),
            meta: case_metas[k],
            expected: case_ty,
            label: Some(format!("case_{k}")),
        });
    }
    let mut goals = std::mem::take(&mut state.goals);
    goals.splice(0..0, new_goals);
    state.goals = goals;
    Ok(())
}

fn strip_ih_binders(ty: Term, ind_id: u64) -> Term {
    match ty {
        Term::Pi(a, b) => {
            let is_rec = matches!(a.as_ref(), Term::Ind(fid, _) if *fid == ind_id);
            let b_stripped = if is_rec {
                match *b {
                    Term::Pi(ih_ty, inner) if is_ih_type(&ih_ty) => {
                        crate::subst::subst(&inner, &Term::Sort(0))
                    }
                    other => other,
                }
            } else {
                *b
            };
            Term::Pi(a, Box::new(strip_ih_binders(b_stripped, ind_id)))
        }
        other => other,
    }
}

fn is_ih_type(ty: &Term) -> bool {
    matches!(ty, Term::App(_, arg) if matches!(arg.as_ref(), Term::Var(0)))
}
