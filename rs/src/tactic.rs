// tactic — tactic engine (untrusted shell)
// spec: specs/tactics.md
// Produces candidate proof terms; the kernel verifies them at completion.

use std::collections::HashMap;

use crate::{
    ctx::{push_var, Ctx, CtxEntry},
    env::Env,
    kernel::{check, infer, Error as KError},
    reduce::{def_eq, whnf},
    term::Term,
};

// ── Metavariables ─────────────────────────────────────────────────────────────

pub type MetaId = u64;

#[derive(Debug, Clone, Default)]
pub struct MetaEnv {
    pub next: MetaId,
    assignments: HashMap<MetaId, Term>,
}

impl MetaEnv {
    pub fn fresh(&mut self) -> MetaId {
        let id = self.next;
        self.next += 1;
        id
    }

    pub fn assign(&mut self, id: MetaId, t: Term) {
        self.assignments.insert(id, t);
    }

    pub fn lookup(&self, id: MetaId) -> Option<&Term> {
        self.assignments.get(&id)
    }

    /// Substitute all solved metavars in t.
    pub fn apply(&self, t: &Term) -> Term {
        match t {
            Term::Var(_) | Term::Sort(_) | Term::Const(_) => t.clone(),
            Term::Pi(a, b) => Term::Pi(Box::new(self.apply(a)), Box::new(self.apply(b))),
            Term::Lam(a, b) => Term::Lam(Box::new(self.apply(a)), Box::new(self.apply(b))),
            Term::App(f, a) => Term::App(Box::new(self.apply(f)), Box::new(self.apply(a))),
            Term::Let(a, v, b) => Term::Let(
                Box::new(self.apply(a)),
                Box::new(self.apply(v)),
                Box::new(self.apply(b)),
            ),
            Term::Ind(id, ps) => Term::Ind(*id, ps.iter().map(|p| self.apply(p)).collect()),
            Term::Ctor(id, k, args) => {
                Term::Ctor(*id, *k, args.iter().map(|a| self.apply(a)).collect())
            }
            Term::Elim(id, m, cs, tg) => Term::Elim(
                *id,
                Box::new(self.apply(m)),
                cs.iter().map(|c| self.apply(c)).collect(),
                Box::new(self.apply(tg)),
            ),
            Term::EqSubst(p, h, pf) => Term::EqSubst(
                Box::new(self.apply(p)),
                Box::new(self.apply(h)),
                Box::new(self.apply(pf)),
            ),
            Term::Meta(id) => match self.lookup(*id) {
                Some(v) => self.apply(v),
                None => t.clone(),
            },
        }
    }
}

// ── Proof state ───────────────────────────────────────────────────────────────

/// One proof obligation.
#[derive(Debug, Clone)]
pub struct Goal {
    /// Hypotheses in scope (innermost first).
    pub local_ctx: Ctx,
    /// Names of local hypotheses, parallel to local_ctx (innermost first).
    pub names: Vec<String>,
    /// The metavariable hole this goal must fill.
    pub meta: MetaId,
    /// The type this goal must produce.
    pub expected: Term,
    /// Optional case label (from induction/cases).
    pub label: Option<String>,
}

/// Proof state: list of open goals.
#[derive(Debug, Clone)]
pub struct ProofState {
    pub goals: Vec<Goal>,
    pub metas: MetaEnv,
    pub env: Env,
}

impl ProofState {
    pub fn new(env: Env, goal_ty: Term) -> Self {
        let mut metas = MetaEnv::default();
        let root = metas.fresh();
        ProofState {
            goals: vec![Goal {
                local_ctx: vec![],
                names: vec![],
                meta: root,
                expected: goal_ty,
                label: None,
            }],
            metas,
            env,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.goals.is_empty()
    }

    /// Assemble the proof term and kernel-verify it.
    pub fn verify(&self, theorem_ty: &Term) -> Result<(), TacticError> {
        if !self.is_complete() {
            return Err(TacticError::Incomplete(self.goals.len()));
        }
        // Root meta must be assigned
        let root_term = self.metas.lookup(0).ok_or(TacticError::Incomplete(1))?;
        let root_applied = self.metas.apply(root_term);
        let empty_ctx: Ctx = vec![];
        check(&self.env, &empty_ctx, &root_applied, theorem_ty).map_err(TacticError::Kernel)
    }
}

// ── Errors ────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub enum TacticError {
    NoGoals,
    NotPi,
    NotInd,
    NoMatchingHypothesis,
    NoContradiction,
    CaseLabelNotFound(String),
    HypothesisInUse(String),
    TacticFailed(String),
    Kernel(KError),
    Incomplete(usize),
}

// ── Core tactics ──────────────────────────────────────────────────────────────

/// exact e: close the focused goal with a fully elaborated term.
pub fn tac_exact(state: &mut ProofState, term: Term) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = &goal.local_ctx.clone();
    let expected = goal.expected.clone();
    let meta = goal.meta;

    let actual = infer(env, ctx, &term).map_err(TacticError::Kernel)?;
    if !def_eq(env, ctx, &actual, &expected) {
        return Err(TacticError::Kernel(KError::TypeMismatch(
            Box::new(actual),
            Box::new(expected),
        )));
    }
    state.metas.assign(meta, term);
    state.goals.remove(0);
    Ok(())
}

/// intro x: peel one PI binder from the focused goal.
pub fn tac_intro(state: &mut ProofState, _name: &str) -> Result<(), TacticError> {
    let goal = state.goals.first_mut().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let expected_whnf = whnf(env, &goal.local_ctx, goal.expected.clone());

    match expected_whnf {
        Term::Pi(a, b) => {
            let new_expected = *b;
            let old_meta = goal.meta;
            let new_meta = state.metas.fresh();
            // Assign the root meta now: λx:A. <new_meta>
            // When new_meta is later filled by another tactic, metas.apply will substitute.
            state.metas.assign(
                old_meta,
                Term::Lam(a.clone(), Box::new(Term::Meta(new_meta))),
            );
            push_var(&mut goal.local_ctx, *a);
            goal.names.insert(0, _name.to_string());
            goal.expected = new_expected;
            goal.meta = new_meta;
            Ok(())
        }
        _ => Err(TacticError::NotPi),
    }
}

/// intro multiple names in sequence.
pub fn tac_intros(state: &mut ProofState, names: &[&str]) -> Result<(), TacticError> {
    for name in names {
        tac_intro(state, name)?;
    }
    Ok(())
}

/// assumption: find a hypothesis whose type matches the goal.
pub fn tac_assumption(state: &mut ProofState) -> Result<(), TacticError> {
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    let expected = goal.expected.clone();

    for (i, entry) in ctx.iter().enumerate() {
        let hyp_ty_shifted = crate::subst::shift(entry.ty(), (i + 1) as u64);
        if def_eq(env, &ctx, &hyp_ty_shifted, &expected) {
            let term = Term::Var(i as u64);
            let meta = goal.meta;
            state.metas.assign(meta, term);
            state.goals.remove(0);
            return Ok(());
        }
    }
    Err(TacticError::NoMatchingHypothesis)
}

/// rfl: close a reflexivity goal (Eq A t t).
pub fn tac_rfl(state: &mut ProofState) -> Result<(), TacticError> {
    use crate::stdlib::EQ_ID;
    let goal = state.goals.first().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    let ctx = goal.local_ctx.clone();
    let expected_whnf = whnf(env, &ctx, goal.expected.clone());

    match &expected_whnf {
        Term::Ind(id, params) if *id == EQ_ID && params.len() == 3 => {
            let a_ty = &params[0];
            let lhs = &params[1];
            let rhs = &params[2];
            if def_eq(env, &ctx, lhs, rhs) {
                // refl : Eq A a a  = CTOR(EQ_ID, 0, [A, a, a]) — arity=3
                let refl = Term::Ctor(EQ_ID, 0, vec![a_ty.clone(), lhs.clone(), lhs.clone()]);
                let meta = goal.meta;
                state.metas.assign(meta, refl);
                state.goals.remove(0);
                Ok(())
            } else {
                Err(TacticError::TacticFailed(
                    "rfl: sides not definitionally equal".into(),
                ))
            }
        }
        _ => Err(TacticError::TacticFailed("rfl: goal is not an Eq".into())),
    }
}

/// show T: assert that T is definitionally equal to the goal type, then display T.
pub fn tac_show(state: &mut ProofState, new_ty: Term) -> Result<(), TacticError> {
    let goal = state.goals.first_mut().ok_or(TacticError::NoGoals)?;
    let env = &state.env;
    if def_eq(env, &goal.local_ctx, &new_ty, &goal.expected) {
        goal.expected = new_ty;
        Ok(())
    } else {
        Err(TacticError::TacticFailed(
            "show: type not definitionally equal to goal".into(),
        ))
    }
}

/// revert h: move hypothesis h back into the goal as a PI prefix.
pub fn tac_revert(state: &mut ProofState, hyp_idx: usize) -> Result<(), TacticError> {
    let goal = state.goals.first_mut().ok_or(TacticError::NoGoals)?;
    if hyp_idx >= goal.local_ctx.len() {
        return Err(TacticError::TacticFailed(
            "revert: hypothesis not in context".into(),
        ));
    }
    let entry = goal.local_ctx.remove(hyp_idx);
    if hyp_idx < goal.names.len() {
        goal.names.remove(hyp_idx);
    }
    let a = entry.ty().clone();
    // shift expected_type down by 1 for the removed binder ... actually when we remove
    // entry at index 0 (innermost), the goal gets wrapped in PI(A, old_goal).
    // Since ctx is innermost-first and hyp_idx=0 is the innermost, this is straightforward.
    let old_expected = goal.expected.clone();
    goal.expected = Term::Pi(Box::new(a), Box::new(old_expected));
    Ok(())
}

/// clear h: remove hypothesis at hyp_idx (must not appear free in goal or other hyps).
/// All de Bruijn indices above hyp_idx are decremented by 1 after removal.
pub fn tac_clear(state: &mut ProofState, hyp_idx: usize) -> Result<(), TacticError> {
    let goal = state.goals.first_mut().ok_or(TacticError::NoGoals)?;
    if hyp_idx >= goal.local_ctx.len() {
        return Err(TacticError::TacticFailed(
            "clear: hypothesis not in context".into(),
        ));
    }
    // Check h not free in goal type
    if var_free_in(hyp_idx, &goal.expected) {
        return Err(TacticError::HypothesisInUse("in goal type".into()));
    }
    // Check not free in any other hypothesis
    for (i, entry) in goal.local_ctx.iter().enumerate() {
        if i == hyp_idx {
            continue;
        }
        if var_free_in(hyp_idx, entry.ty()) {
            return Err(TacticError::HypothesisInUse(format!("in hypothesis {i}")));
        }
        if let CtxEntry::Let(_, v) = entry {
            if var_free_in(hyp_idx, v) {
                return Err(TacticError::HypothesisInUse(format!("in let-value at {i}")));
            }
        }
    }
    goal.local_ctx.remove(hyp_idx);
    if hyp_idx < goal.names.len() {
        goal.names.remove(hyp_idx);
    }
    // Decrement all free variable indices > hyp_idx in the goal and remaining hypotheses.
    // Since we removed VAR(hyp_idx), any VAR(j) with j > hyp_idx must become VAR(j-1).
    goal.expected = decrement_above(&goal.expected, hyp_idx as u64);
    for entry in goal.local_ctx.iter_mut() {
        match entry {
            CtxEntry::Var(a) => *a = decrement_above(a, hyp_idx as u64),
            CtxEntry::Let(a, v) => {
                *a = decrement_above(a, hyp_idx as u64);
                *v = decrement_above(v, hyp_idx as u64);
            }
        }
    }
    Ok(())
}

/// Decrement all free variable indices strictly above `threshold` by 1.
/// Used after removing a binder at de Bruijn depth `threshold`.
fn decrement_above(t: &Term, threshold: u64) -> Term {
    decrement_above_at(t, threshold, 0)
}

fn decrement_above_at(t: &Term, threshold: u64, depth: u64) -> Term {
    match t {
        Term::Var(i) => {
            let adjusted = threshold + depth; // the threshold in the current de Bruijn scope
            if *i > adjusted {
                Term::Var(i - 1)
            } else {
                Term::Var(*i)
            }
        }
        Term::Sort(u) => Term::Sort(*u),
        Term::Const(id) => Term::Const(*id),
        Term::Meta(id) => Term::Meta(*id),
        Term::Pi(a, b) => Term::Pi(
            Box::new(decrement_above_at(a, threshold, depth)),
            Box::new(decrement_above_at(b, threshold, depth + 1)),
        ),
        Term::Lam(a, b) => Term::Lam(
            Box::new(decrement_above_at(a, threshold, depth)),
            Box::new(decrement_above_at(b, threshold, depth + 1)),
        ),
        Term::App(f, x) => Term::App(
            Box::new(decrement_above_at(f, threshold, depth)),
            Box::new(decrement_above_at(x, threshold, depth)),
        ),
        Term::Let(a, v, b) => Term::Let(
            Box::new(decrement_above_at(a, threshold, depth)),
            Box::new(decrement_above_at(v, threshold, depth)),
            Box::new(decrement_above_at(b, threshold, depth + 1)),
        ),
        Term::Ind(id, ps) => Term::Ind(
            *id,
            ps.iter()
                .map(|p| decrement_above_at(p, threshold, depth))
                .collect(),
        ),
        Term::Ctor(id, k, args) => Term::Ctor(
            *id,
            *k,
            args.iter()
                .map(|a| decrement_above_at(a, threshold, depth))
                .collect(),
        ),
        Term::Elim(id, m, cs, tg) => Term::Elim(
            *id,
            Box::new(decrement_above_at(m, threshold, depth)),
            cs.iter()
                .map(|c| decrement_above_at(c, threshold, depth))
                .collect(),
            Box::new(decrement_above_at(tg, threshold, depth)),
        ),
        Term::EqSubst(p, h, pf) => Term::EqSubst(
            Box::new(decrement_above_at(p, threshold, depth)),
            Box::new(decrement_above_at(h, threshold, depth)),
            Box::new(decrement_above_at(pf, threshold, depth)),
        ),
    }
}

/// skip: identity tactic — always succeeds.
pub fn tac_skip(_state: &mut ProofState) -> Result<(), TacticError> {
    Ok(())
}

/// fail: always fails.
pub fn tac_fail(msg: impl Into<String>) -> Result<(), TacticError> {
    Err(TacticError::TacticFailed(msg.into()))
}

/// try t: attempt t; ignore failure.
pub fn tac_try<F>(state: &mut ProofState, tac: F) -> Result<(), TacticError>
where
    F: FnOnce(&mut ProofState) -> Result<(), TacticError>,
{
    let saved = state.clone();
    match tac(state) {
        Ok(()) => Ok(()),
        Err(_) => {
            *state = saved;
            Ok(())
        }
    }
}

/// first: try each branch in order, commit to the first that succeeds.
pub fn tac_first<F>(state: &mut ProofState, branches: Vec<F>) -> Result<(), TacticError>
where
    F: FnOnce(&mut ProofState) -> Result<(), TacticError>,
{
    let mut last_err = TacticError::TacticFailed("first: no branches".into());
    for branch in branches {
        let saved = state.clone();
        match branch(state) {
            Ok(()) => return Ok(()),
            Err(e) => {
                *state = saved;
                last_err = e;
            }
        }
    }
    Err(last_err)
}

// ── Helper: free variable check ───────────────────────────────────────────────

fn var_free_in(idx: usize, t: &Term) -> bool {
    var_free_at(idx as u64, t, 0)
}

fn var_free_at(idx: u64, t: &Term, depth: u64) -> bool {
    match t {
        Term::Var(i) => *i == idx + depth,
        Term::Sort(_) | Term::Const(_) => false,
        Term::Pi(a, b) | Term::Lam(a, b) => {
            var_free_at(idx, a, depth) || var_free_at(idx, b, depth + 1)
        }
        Term::App(f, a) => var_free_at(idx, f, depth) || var_free_at(idx, a, depth),
        Term::Let(a, v, b) => {
            var_free_at(idx, a, depth)
                || var_free_at(idx, v, depth)
                || var_free_at(idx, b, depth + 1)
        }
        Term::Ind(_, ps) => ps.iter().any(|p| var_free_at(idx, p, depth)),
        Term::Ctor(_, _, args) => args.iter().any(|a| var_free_at(idx, a, depth)),
        Term::Elim(_, m, cs, tg) => {
            var_free_at(idx, m, depth)
                || cs.iter().any(|c| var_free_at(idx, c, depth))
                || var_free_at(idx, tg, depth)
        }
        Term::EqSubst(p, h, pf) => {
            var_free_at(idx, p, depth) || var_free_at(idx, h, depth) || var_free_at(idx, pf, depth)
        }
        Term::Meta(_) => false,
    }
}

#[cfg(test)]
mod tests;
