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
            Term::Pi(a, b)   => Term::Pi(Box::new(self.apply(a)), Box::new(self.apply(b))),
            Term::Lam(a, b)  => Term::Lam(Box::new(self.apply(a)), Box::new(self.apply(b))),
            Term::App(f, a)  => Term::App(Box::new(self.apply(f)), Box::new(self.apply(a))),
            Term::Let(a,v,b) => Term::Let(
                Box::new(self.apply(a)),
                Box::new(self.apply(v)),
                Box::new(self.apply(b)),
            ),
            Term::Ind(id, ps) => Term::Ind(*id, ps.iter().map(|p| self.apply(p)).collect()),
            Term::Ctor(id,k,args) => Term::Ctor(*id, *k, args.iter().map(|a| self.apply(a)).collect()),
            Term::Elim(id,m,cs,tg) => Term::Elim(
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
                None    => t.clone(),
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

    pub fn is_complete(&self) -> bool { self.goals.is_empty() }

    /// Assemble the proof term and kernel-verify it.
    pub fn verify(&self, theorem_ty: &Term) -> Result<(), TacticError> {
        if !self.is_complete() {
            return Err(TacticError::Incomplete(self.goals.len()));
        }
        // Root meta must be assigned
        let root_term = self.metas.lookup(0)
            .ok_or(TacticError::Incomplete(1))?;
        let root_applied = self.metas.apply(root_term);
        let empty_ctx: Ctx = vec![];
        check(&self.env, &empty_ctx, &root_applied, theorem_ty)
            .map_err(TacticError::Kernel)
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
            state.metas.assign(old_meta, Term::Lam(a.clone(), Box::new(Term::Meta(new_meta))));
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
            let lhs  = &params[1];
            let rhs  = &params[2];
            if def_eq(env, &ctx, lhs, rhs) {
                // refl : Eq A a a  = CTOR(EQ_ID, 0, [A, a, a]) — arity=3
                let refl = Term::Ctor(EQ_ID, 0, vec![a_ty.clone(), lhs.clone(), lhs.clone()]);
                let meta = goal.meta;
                state.metas.assign(meta, refl);
                state.goals.remove(0);
                Ok(())
            } else {
                Err(TacticError::TacticFailed("rfl: sides not definitionally equal".into()))
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
        Err(TacticError::TacticFailed("show: type not definitionally equal to goal".into()))
    }
}

/// revert h: move hypothesis h back into the goal as a PI prefix.
pub fn tac_revert(state: &mut ProofState, hyp_idx: usize) -> Result<(), TacticError> {
    let goal = state.goals.first_mut().ok_or(TacticError::NoGoals)?;
    if hyp_idx >= goal.local_ctx.len() {
        return Err(TacticError::TacticFailed("revert: hypothesis not in context".into()));
    }
    let entry = goal.local_ctx.remove(hyp_idx);
    if hyp_idx < goal.names.len() { goal.names.remove(hyp_idx); }
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
        return Err(TacticError::TacticFailed("clear: hypothesis not in context".into()));
    }
    // Check h not free in goal type
    if var_free_in(hyp_idx, &goal.expected) {
        return Err(TacticError::HypothesisInUse("in goal type".into()));
    }
    // Check not free in any other hypothesis
    for (i, entry) in goal.local_ctx.iter().enumerate() {
        if i == hyp_idx { continue; }
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
    if hyp_idx < goal.names.len() { goal.names.remove(hyp_idx); }
    // Decrement all free variable indices > hyp_idx in the goal and remaining hypotheses.
    // Since we removed VAR(hyp_idx), any VAR(j) with j > hyp_idx must become VAR(j-1).
    goal.expected = decrement_above(&goal.expected, hyp_idx as u64);
    for entry in goal.local_ctx.iter_mut() {
        match entry {
            CtxEntry::Var(a)    => *a = decrement_above(a, hyp_idx as u64),
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
            if *i > adjusted { Term::Var(i - 1) } else { Term::Var(*i) }
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
        Term::Ind(id, ps) =>
            Term::Ind(*id, ps.iter().map(|p| decrement_above_at(p, threshold, depth)).collect()),
        Term::Ctor(id, k, args) =>
            Term::Ctor(*id, *k, args.iter().map(|a| decrement_above_at(a, threshold, depth)).collect()),
        Term::Elim(id, m, cs, tg) => Term::Elim(
            *id,
            Box::new(decrement_above_at(m, threshold, depth)),
            cs.iter().map(|c| decrement_above_at(c, threshold, depth)).collect(),
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
        Err(_) => { *state = saved; Ok(()) }
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
            Err(e) => { *state = saved; last_err = e; }
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
        Term::Pi(a, b) | Term::Lam(a, b) =>
            var_free_at(idx, a, depth) || var_free_at(idx, b, depth + 1),
        Term::App(f, a) => var_free_at(idx, f, depth) || var_free_at(idx, a, depth),
        Term::Let(a, v, b) =>
            var_free_at(idx, a, depth) || var_free_at(idx, v, depth) || var_free_at(idx, b, depth + 1),
        Term::Ind(_, ps) => ps.iter().any(|p| var_free_at(idx, p, depth)),
        Term::Ctor(_, _, args) => args.iter().any(|a| var_free_at(idx, a, depth)),
        Term::Elim(_, m, cs, tg) =>
            var_free_at(idx, m, depth)
            || cs.iter().any(|c| var_free_at(idx, c, depth))
            || var_free_at(idx, tg, depth),
        Term::EqSubst(p, h, pf) =>
            var_free_at(idx, p, depth) || var_free_at(idx, h, depth) || var_free_at(idx, pf, depth),
        Term::Meta(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stdlib::{std_env, nat, nat_zero};

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
        use crate::stdlib::{EQ_ID, nat_zero};
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
        tac_first(&mut ps, vec![
            |s: &mut ProofState| tac_intro(s, "n"),  // fails
            |s: &mut ProofState| tac_exact(s, nat_zero()), // succeeds
        ]).unwrap();
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
        assert!(ps.verify(&goal_ty).is_ok(), "double intro+exact verify failed");
    }

    #[test]
    fn clear_decrements_indices() {
        let env = std_env();
        // Goal: Nat. Context: [Bool, Nat] (innermost Bool at 0, Nat at 1)
        // expected references VAR(1) = Nat
        let goal_ty = Term::Var(1); // refers to the outer Nat hypothesis
        let mut ps = ProofState::new(env, goal_ty);
        push_var(&mut ps.goals[0].local_ctx, nat());  // VAR(0) = Nat
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
}
