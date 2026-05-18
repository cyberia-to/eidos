// tactic_ext/rewrite.rs — tac_rewrite and term rewriting helpers
use crate::{
    env::Env,
    kernel::infer,
    reduce::whnf,
    stdlib::{eq_refl, EQ_ID},
    subst::shift,
    term::Term,
};
use crate::tactic::{ProofState, TacticError};

/// rewrite [h] — replace lhs with rhs in the goal using h : Eq A lhs rhs.
pub fn tac_rewrite(state: &mut ProofState, eq_proof: Term) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();

    let eq_ty = infer(env, &ctx, &eq_proof).map_err(TacticError::Kernel)?;
    let (a_ty, lhs, rhs) = parse_eq(env, &ctx, eq_ty)?;

    let lhs_nf  = crate::reduce::nf(env, &ctx, lhs);
    let goal_nf = crate::reduce::nf(env, &ctx, goal.expected.clone());
    let new_expected = rewrite_term(&goal_nf, &lhs_nf, &rhs);
    if new_expected == goal_nf {
        return Err(TacticError::TacticFailed("rewrite: lhs not found in goal".into()));
    }

    // h_sym : Eq A rhs lhs  via  EqSubst(p_sym, eq_proof, refl_lhs)
    let p_sym = Term::Lam(
        Box::new(a_ty.clone()),
        Box::new(Term::Ind(EQ_ID, vec![
            shift(&a_ty, 1),
            Term::Var(0),
            shift(&lhs_nf, 1),
        ])),
    );
    let h_sym = Term::EqSubst(
        Box::new(p_sym),
        Box::new(eq_proof),
        Box::new(eq_refl(a_ty.clone(), lhs_nf.clone())),
    );

    // p_lam = λ(x:A). goal_nf[lhs_nf ↦ x]
    let p_lam = Term::Lam(
        Box::new(a_ty.clone()),
        Box::new(rewrite_term(
            &shift(&goal_nf, 1),
            &shift(&lhs_nf, 1),
            &Term::Var(0),
        )),
    );

    let old_meta_id = goal.meta;
    let old_ctx     = goal.local_ctx.clone();
    let old_names   = goal.names.clone();
    let old_label   = goal.label.clone();
    let new_meta_id = state.metas.fresh();

    let coerce = Term::EqSubst(
        Box::new(p_lam),
        Box::new(h_sym),
        Box::new(Term::Meta(new_meta_id)),
    );
    state.metas.assign(old_meta_id, coerce);

    state.goals[0] = crate::tactic::Goal {
        local_ctx: old_ctx,
        names: old_names,
        meta: new_meta_id,
        expected: new_expected,
        label: old_label,
    };
    Ok(())
}

pub(super) fn parse_eq(env: &Env, ctx: &crate::ctx::Ctx, ty: Term)
    -> Result<(Term, Term, Term), TacticError>
{
    match whnf(env, ctx, ty) {
        Term::Ind(id, params) if id == EQ_ID && params.len() == 3 => {
            Ok((params[0].clone(), params[1].clone(), params[2].clone()))
        }
        other => Err(TacticError::TacticFailed(format!("rewrite: not an Eq type: {other:?}"))),
    }
}

/// Syntactic substitution: replace all occurrences of `lhs` with `rhs` in `t`.
pub fn rewrite_term(t: &Term, lhs: &Term, rhs: &Term) -> Term {
    if t == lhs { return rhs.clone(); }
    match t {
        Term::Var(_) | Term::Sort(_) | Term::Const(_) | Term::Meta(_) => t.clone(),
        Term::Pi(a, b)     => Term::Pi(Box::new(rewrite_term(a,lhs,rhs)), Box::new(rewrite_term(b,lhs,rhs))),
        Term::Lam(a, b)    => Term::Lam(Box::new(rewrite_term(a,lhs,rhs)), Box::new(rewrite_term(b,lhs,rhs))),
        Term::App(f, a)    => Term::App(Box::new(rewrite_term(f,lhs,rhs)), Box::new(rewrite_term(a,lhs,rhs))),
        Term::Let(a, v, b) => Term::Let(
            Box::new(rewrite_term(a,lhs,rhs)),
            Box::new(rewrite_term(v,lhs,rhs)),
            Box::new(rewrite_term(b,lhs,rhs)),
        ),
        Term::Ind(id, ps)     => Term::Ind(*id, ps.iter().map(|p| rewrite_term(p,lhs,rhs)).collect()),
        Term::Ctor(id,k,args) => Term::Ctor(*id,*k, args.iter().map(|a| rewrite_term(a,lhs,rhs)).collect()),
        Term::Elim(id,m,cs,tg) => Term::Elim(
            *id,
            Box::new(rewrite_term(m,lhs,rhs)),
            cs.iter().map(|c| rewrite_term(c,lhs,rhs)).collect(),
            Box::new(rewrite_term(tg,lhs,rhs)),
        ),
        Term::EqSubst(p,h,pf) => Term::EqSubst(
            Box::new(rewrite_term(p,lhs,rhs)),
            Box::new(rewrite_term(h,lhs,rhs)),
            Box::new(rewrite_term(pf,lhs,rhs)),
        ),
    }
}
