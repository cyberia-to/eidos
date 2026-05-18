// tactic_runner — execute surface Tactic lists against a ProofState
// spec: specs/tactics.md

use crate::{
    ctx::CtxEntry,
    env::Env,
    elab::{ast::Expr, core::{elab_expr, ElabState}, ElabError},
    tactic::{tac_assumption, tac_exact, tac_intro, tac_rfl, tac_revert,
              tac_show, tac_clear, ProofState, TacticError},
    tactic_ext::{
        tac_apply, tac_cases, tac_contradiction, tac_decide, tac_have_exact, tac_have_goal,
        tac_induction, tac_omega, tac_rewrite, tac_simp, tac_trivial,
    },
    term::Term,
};
use super::parser::{Proof, Tactic};

// ── Error ─────────────────────────────────────────────────────────────────────

#[derive(Debug)]
pub enum RunError {
    Tactic(TacticError),
    Elab(ElabError),
    Sorry(String),  // sorry was used — proof incomplete
    NoGoals,
    GoalMismatch(String),
}

impl From<TacticError> for RunError {
    fn from(e: TacticError) -> Self { RunError::Tactic(e) }
}
impl From<ElabError> for RunError {
    fn from(e: ElabError) -> Self { RunError::Elab(e) }
}

// ── Public entry point ────────────────────────────────────────────────────────

/// Execute a proof (term or tactic block) and return the proof term.
pub fn run_proof(
    st: &mut ElabState,
    env: &Env,
    proof: &Proof,
    expected_ty: &Term,
) -> Result<Term, RunError> {
    match proof {
        Proof::Term(expr) => {
            let (term, _) = elab_expr(st, env, expr)?;
            let term_z = st.mctx.zonk(&term);
            Ok(term_z)
        }
        Proof::Tactics(tactics) => {
            let mut ps = ProofState::new(env.clone(), expected_ty.clone());
            // Populate local context from st.locals (innermost first = index 0 = Var(0))
            for (name, ty) in &st.locals {
                ps.goals[0].local_ctx.push(CtxEntry::Var(ty.clone()));
                ps.goals[0].names.push(name.clone());
            }
            run_tactics(st, env, &mut ps, tactics)?;
            if !ps.is_complete() {
                let n = ps.goals.len();
                return Err(RunError::GoalMismatch(format!("{n} goals remaining")));
            }
            // Extract root proof term; caller (check_theorem) does the real kernel check
            // with the correct local context. ps.verify uses empty_ctx which fails for
            // parameterized theorems (free variables from params).
            let root = ps.metas.lookup(0)
                .ok_or_else(|| RunError::GoalMismatch("root meta unassigned".into()))?;
            Ok(ps.metas.apply(root))
        }
    }
}

/// Execute a sequence of tactics against a ProofState.
pub fn run_tactics(
    st: &mut ElabState,
    env: &Env,
    ps: &mut ProofState,
    tactics: &[Tactic],
) -> Result<(), RunError> {
    for tac in tactics {
        run_one(st, env, ps, tac)?;
    }
    Ok(())
}

fn run_one(
    st: &mut ElabState,
    env: &Env,
    ps: &mut ProofState,
    tac: &Tactic,
) -> Result<(), RunError> {
    match tac {
        Tactic::Intro(names) => {
            for name in names {
                tac_intro(ps, name)?;
            }
        }

        Tactic::Exact(expr) => {
            let (term, _) = elab_in_goal(st, env, ps, expr)?;
            tac_exact(ps, term)?;
        }

        Tactic::Apply(expr) => {
            let (term, _) = elab_in_goal(st, env, ps, expr)?;
            tac_apply(ps, term)?;
        }

        Tactic::Rfl => { tac_rfl(ps)?; }

        Tactic::Assumption => { tac_assumption(ps)?; }

        Tactic::Omega => { tac_omega(ps)?; }

        Tactic::Decide => { tac_decide(ps)?; }

        Tactic::Simp(lemmas) => {
            tac_simp(ps)?;
            // After simp, try rfl if no lemmas specified
            if lemmas.is_empty() {
                let _ = tac_rfl(ps); // ignore failure
            }
            // TODO: apply provided lemmas via rewrite
        }

        Tactic::Contradiction => { tac_contradiction(ps)?; }

        Tactic::Trivial => { tac_trivial(ps)?; }

        Tactic::Show(expr) => {
            let goal = ps.goals.first().ok_or(TacticError::NoGoals)?;
            let ctx = goal.local_ctx.clone();
            let names = goal.names.clone();
            let saved = st.locals.clone();
            st.locals = goal_locals(&ctx, &names);
            let (new_ty, _) = elab_expr(st, env, expr).map_err(RunError::Elab)?;
            st.locals = saved;
            let new_ty_z = st.mctx.zonk(&new_ty);
            tac_show(ps, new_ty_z)?;
        }

        Tactic::Clear(name) => {
            let goal = ps.goals.first().ok_or(TacticError::NoGoals)?;
            let idx = find_local(&goal.names, name)
                .ok_or_else(|| TacticError::TacticFailed(format!("clear: unknown {name}")))?;
            tac_clear(ps, idx)?;
        }

        Tactic::Revert(name) => {
            let goal = ps.goals.first().ok_or(TacticError::NoGoals)?;
            let idx = find_local(&goal.names, name)
                .ok_or_else(|| TacticError::TacticFailed(format!("revert: unknown {name}")))?;
            tac_revert(ps, idx)?;
        }

        Tactic::Induction(target) => {
            let goal = ps.goals.first().ok_or(TacticError::NoGoals)?;
            let idx = find_local(&goal.names, target)
                .ok_or_else(|| TacticError::TacticFailed(
                    format!("induction: unknown variable {target}")
                ))?;
            tac_induction(ps, idx)?;
        }

        Tactic::Cases(target) => {
            let goal = ps.goals.first().ok_or(TacticError::NoGoals)?;
            let idx = find_local(&goal.names, target)
                .ok_or_else(|| TacticError::TacticFailed(
                    format!("cases: unknown variable {target}")
                ))?;
            tac_cases(ps, idx)?;
        }

        Tactic::Have { name, ty, proof } => {
            let (ty_term, _) = elab_in_goal(st, env, ps, ty)?;
            let ty_z = st.mctx.zonk(&ty_term);
            match proof.as_ref() {
                Proof::Term(val_expr) => {
                    let (val, _) = elab_in_goal(st, env, ps, val_expr)?;
                    let val_z = st.mctx.zonk(&val);
                    tac_have_exact(ps, name, ty_z, val_z)?;
                }
                Proof::Tactics(sub_tactics) => {
                    tac_have_goal(ps, name, ty_z)?;
                    // Solve the have-subgoal (first goal after tac_have_goal)
                    run_tactics(st, env, ps, sub_tactics)?;
                }
            }
        }

        Tactic::Rewrite { expr, reverse } => {
            let (term, _) = elab_in_goal(st, env, ps, expr)?;
            let term_z = st.mctx.zonk(&term);
            if *reverse {
                // rewrite ← h: swap lhs/rhs in the eq proof
                let rev = build_symm_proof(ps, env, term_z)?;
                tac_rewrite(ps, rev)?;
            } else {
                tac_rewrite(ps, term_z)?;
            }
        }

        Tactic::Sorry => {
            // sorry — accept the goal without proof (unsound, for development only)
            // Return an error that check_theorem can catch and treat as an axiom
            return Err(RunError::Sorry("theorem declared with sorry".into()));
        }

        Tactic::Case { ctor: _, vars: _, body } => {
            // Execute the body tactics on the current goal (first remaining)
            // Name binding for case vars is handled by intro
            run_tactics(st, env, ps, body)?;
        }

        Tactic::Focus(body) => {
            // · tactic — focus on first goal
            if ps.goals.is_empty() {
                return Err(TacticError::NoGoals.into());
            }
            run_tactics(st, env, ps, body)?;
        }

        Tactic::Seq(ts) => {
            run_tactics(st, env, ps, ts)?;
        }
    }
    Ok(())
}

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Elaborate an expression in the context of the current proof goal.
/// Replaces st.locals with the goal's context (innermost first = Var(0) first),
/// then restores after elaboration. This mirrors the exact proof-state variable layout.
fn elab_in_goal(
    st: &mut ElabState,
    env: &Env,
    ps: &ProofState,
    expr: &Expr,
) -> Result<(Term, Term), RunError> {
    let (ctx, names) = ps.goals.first()
        .map(|g| (g.local_ctx.clone(), g.names.clone()))
        .unwrap_or_default();
    let saved = st.locals.clone();
    st.locals = goal_locals(&ctx, &names);
    let result = elab_expr(st, env, expr).map_err(RunError::Elab);
    st.locals = saved;
    result
}

/// Build a (name, type) locals list from a goal context, innermost first.
fn goal_locals(ctx: &crate::ctx::Ctx, names: &[String]) -> Vec<(String, crate::term::Term)> {
    ctx.iter().enumerate()
        .map(|(i, e)| (names.get(i).cloned().unwrap_or_else(|| "_".into()), e.ty().clone()))
        .collect()
}

/// Find the de Bruijn index of a named local hypothesis (innermost = index 0).
fn find_local(names: &[String], name: &str) -> Option<usize> {
    names.iter().position(|n| n == name)
}

/// Build a symmetry proof: given `h : Eq A a b`, produce a proof of `Eq A b a`.
/// Uses EqSubst with motive λ(x: A). Eq A x a.
fn build_symm_proof(
    ps: &ProofState,
    env: &Env,
    h: Term,
) -> Result<Term, RunError> {
    use crate::kernel::infer;
    use crate::stdlib::{EQ_ID, eq_refl};
    use crate::subst::shift;
    let goal = ps.goals.first().ok_or(TacticError::NoGoals)?;
    let ctx = &goal.local_ctx;
    let h_ty = infer(env, ctx, &h).map_err(TacticError::Kernel)?;
    if let Term::Ind(id, params) = crate::reduce::whnf(env, ctx, h_ty) {
        if id == EQ_ID && params.len() == 3 {
            let (a_ty, a, _b) = (params[0].clone(), params[1].clone(), params[2].clone());
            // p_sym = λ(x: A). Eq A x a  (motive: x → Eq A x a)
            let p_sym = Term::Lam(
                Box::new(a_ty.clone()),
                Box::new(Term::Ind(EQ_ID, vec![
                    shift(&a_ty, 1),
                    Term::Var(0),   // x
                    shift(&a, 1),   // a shifted past binder
                ])),
            );
            // EqSubst(p_sym, h, refl_a) : p_sym(b) = Eq A b a
            let refl_a = eq_refl(a_ty, a);
            return Ok(Term::EqSubst(Box::new(p_sym), Box::new(h), Box::new(refl_a)));
        }
    }
    Err(TacticError::TacticFailed("rewrite ←: argument is not an Eq proof".into()).into())
}
