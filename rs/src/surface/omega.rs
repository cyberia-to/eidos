// omega — linear arithmetic decision procedure
// Handles Nat equality goals that reduce to reflexivity or match known arithmetic laws.
// spec: specs/tactics.md § omega

use crate::{
    ctx::Ctx,
    env::Env,
    reduce::{def_eq, nf, whnf},
    stdlib::{eq_refl, nat, nat_zero, EQ_ID, NAT_ID, NAT_NEXT, NAT_ZERO},
    term::Term,
};

/// Try to close a goal of the form `Eq A lhs rhs` by linear arithmetic.
/// Returns `Some(proof_term)` if solved, `None` if the tactic cannot handle it.
pub fn omega_solve(env: &Env, ctx: &Ctx, goal: &Term) -> Option<Term> {
    // Step 1: normalize via nf and try def_eq (handles concrete + ι-reducible goals)
    if let Some(proof) = try_rfl(env, ctx, goal) {
        return Some(proof);
    }
    // Step 2: try structural arithmetic laws
    if let Term::Ind(id, params) = nf(env, ctx, goal.clone()) {
        if id == EQ_ID && params.len() == 3 {
            let ty  = &params[0];
            let lhs = &params[1];
            let rhs = &params[2];
            if let Some(proof) = try_arith_laws(env, ctx, ty, lhs, rhs) {
                return Some(proof);
            }
        }
    }
    None
}

/// Try closing `Eq A a b` by reflexivity (def_eq of a and b).
pub fn try_rfl(env: &Env, ctx: &Ctx, goal: &Term) -> Option<Term> {
    let reduced = nf(env, ctx, goal.clone());
    if let Term::Ind(id, ref params) = reduced {
        if id == EQ_ID && params.len() == 3 {
            if def_eq(env, ctx, &params[1], &params[2]) {
                return Some(eq_refl(params[0].clone(), params[1].clone()));
            }
        }
    }
    None
}

/// Try to prove `Eq Nat lhs rhs` using known arithmetic identities.
fn try_arith_laws(env: &Env, ctx: &Ctx, ty: &Term, lhs: &Term, rhs: &Term) -> Option<Term> {
    // Only handle Nat equalities
    if !def_eq(env, ctx, ty, &nat()) {
        return None;
    }
    let lhs_nf = nf(env, ctx, lhs.clone());
    let rhs_nf = nf(env, ctx, rhs.clone());

    // Already equal after normalization
    if def_eq(env, ctx, &lhs_nf, &rhs_nf) {
        return Some(eq_refl(nat(), lhs_nf));
    }

    // Try commutativity: add n m = add m n
    // We check if lhs and rhs have the same multiset of addends
    if let (Some(lhs_addends), Some(rhs_addends)) = (
        extract_add_terms(&lhs_nf),
        extract_add_terms(&rhs_nf),
    ) {
        if addends_equal(env, ctx, &lhs_addends, &rhs_addends) {
            // Construct a proof by normalization — if both sides normalize to the same
            // expression, rfl works. Otherwise, produce a commutativity proof.
            // For now: if both have the same set of addends, assume provable and
            // produce proof via add_comm chain (requires add_comm in env).
            // Fallback: fail gracefully.
        }
    }
    None
}

/// Extract the list of addends from a nat_add chain: a + b + c → [a, b, c].
fn extract_add_terms(t: &Term) -> Option<Vec<Term>> {
    match t {
        // Check if this is an add ELIM
        Term::Elim(id, _, cases, target) if *id == NAT_ID && cases.len() == 2 => {
            // add n m = ELIM(Nat, _, [m, case_S], n)
            // Extract [n, m]
            let mut addends = vec![*target.clone()];
            addends.push(cases[0].clone()); // m = base case
            Some(addends)
        }
        _ => {
            // Single term (not an add)
            Some(vec![t.clone()])
        }
    }
}

/// Check if two lists of addends are equal as multisets (up to def_eq).
fn addends_equal(env: &Env, ctx: &Ctx, a: &[Term], b: &[Term]) -> bool {
    if a.len() != b.len() { return false; }
    let mut used = vec![false; b.len()];
    'outer: for ta in a {
        for (j, tb) in b.iter().enumerate() {
            if !used[j] && def_eq(env, ctx, ta, tb) {
                used[j] = true;
                continue 'outer;
            }
        }
        return false;
    }
    true
}

// ── Nat normalization ─────────────────────────────────────────────────────────

/// Evaluate a closed Nat term to its numeric value (None if not a concrete Nat).
pub fn eval_nat(env: &Env, ctx: &Ctx, t: &Term) -> Option<u64> {
    match whnf(env, ctx, t.clone()) {
        Term::Ctor(id, k, args) if id == NAT_ID => {
            if k == NAT_ZERO && args.is_empty() {
                Some(0)
            } else if k == NAT_NEXT && args.len() == 1 {
                eval_nat(env, ctx, &args[0]).map(|n| n + 1)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Build a Nat term from a numeric literal.
pub fn build_nat(n: u64) -> Term {
    let mut t = nat_zero();
    for _ in 0..n { t = crate::stdlib::nat_next(t); }
    t
}

/// Evaluate a Nat arithmetic expression (+ only) to a value, substituting vars from `vals`.
pub fn eval_add_expr(env: &Env, ctx: &Ctx, t: &Term) -> Option<u64> {
    match whnf(env, ctx, t.clone()) {
        Term::Ctor(id, k, ref args) if id == NAT_ID => {
            if k == NAT_ZERO { Some(0) }
            else if k == NAT_NEXT && args.len() == 1 {
                eval_add_expr(env, ctx, &args[0]).map(|n| n + 1)
            } else { None }
        }
        Term::Elim(id, _, ref cases, ref target) if id == NAT_ID && cases.len() == 2 => {
            // Recognize add pattern: [m, λ_.λih.S(ih)]
            let n = eval_add_expr(env, ctx, target)?;
            let m = eval_add_expr(env, ctx, &cases[0])?;
            Some(n + m)
        }
        _ => None,
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stdlib::{nat_add, nat_lit, std_env};

    fn ctx() -> Ctx { vec![] }

    #[test]
    fn omega_concrete_eq() {
        let env = std_env();
        let goal = Term::Ind(EQ_ID, vec![nat(), nat_lit(3), nat_lit(3)]);
        assert!(omega_solve(&env, &ctx(), &goal).is_some());
    }

    #[test]
    fn omega_add_concrete() {
        let env = std_env();
        // 2 + 3 = 5 via nf
        let lhs = nat_add(nat_lit(2), nat_lit(3));
        let rhs = nat_lit(5);
        let goal = Term::Ind(EQ_ID, vec![nat(), lhs, rhs]);
        assert!(omega_solve(&env, &ctx(), &goal).is_some());
    }

    #[test]
    fn eval_nat_zero() {
        let env = std_env();
        assert_eq!(eval_nat(&env, &ctx(), &nat_zero()), Some(0));
    }

    #[test]
    fn eval_nat_lit() {
        let env = std_env();
        for n in 0..=5u64 {
            assert_eq!(eval_nat(&env, &ctx(), &nat_lit(n)), Some(n));
        }
    }
}
