// reduce — WHNF, definitional equality, structural equality
// spec: specs/terms.md § reduction / whnf / definitional equality

use crate::{
    ctx::{push_var, Ctx, CtxEntry},
    env::Env,
    subst::{shift, subst},
    term::Term,
};

// ── instantiate ──────────────────────────────────────────────────────────────

/// instantiate(ctor_tel, params): simultaneous substitution of parameters into a constructor
/// return type. ctor_tel has free variables VAR(n-1)…VAR(0) for n params.
/// params is ordered outermost-first: params[0] replaces VAR(n-1), params[n-1] replaces VAR(0).
/// Uses simultaneous (not sequential) substitution to avoid corruption of free variables in params.
pub fn instantiate(ctor_tel: &Term, params: &[Term]) -> Term {
    inst_at(ctor_tel, params, 0)
}

fn inst_at(t: &Term, params: &[Term], depth: u64) -> Term {
    let n = params.len() as u64;
    match t {
        Term::Var(i) => {
            if *i < depth {
                Term::Var(*i)
            } else {
                let k = *i - depth;
                if k < n {
                    // params[0] → innermost (Var(n-1)), params[n-1] → outermost (Var(0))
                    shift(&params[(n - 1 - k) as usize], depth)
                } else {
                    Term::Var(*i - n)
                }
            }
        }
        Term::Sort(u) => Term::Sort(*u),
        Term::Pi(a, b) => Term::Pi(
            Box::new(inst_at(a, params, depth)),
            Box::new(inst_at(b, params, depth + 1)),
        ),
        Term::Lam(a, body) => Term::Lam(
            Box::new(inst_at(a, params, depth)),
            Box::new(inst_at(body, params, depth + 1)),
        ),
        Term::App(f, arg) => Term::App(
            Box::new(inst_at(f, params, depth)),
            Box::new(inst_at(arg, params, depth)),
        ),
        Term::Let(a, v, b) => Term::Let(
            Box::new(inst_at(a, params, depth)),
            Box::new(inst_at(v, params, depth)),
            Box::new(inst_at(b, params, depth + 1)),
        ),
        Term::Ind(id, ps) => Term::Ind(*id, ps.iter().map(|p| inst_at(p, params, depth)).collect()),
        Term::Ctor(id, k, args) => Term::Ctor(*id, *k, args.iter().map(|a| inst_at(a, params, depth)).collect()),
        Term::Elim(id, motive, cases, target) => Term::Elim(
            *id,
            Box::new(inst_at(motive, params, depth)),
            cases.iter().map(|c| inst_at(c, params, depth)).collect(),
            Box::new(inst_at(target, params, depth)),
        ),
        Term::EqSubst(p, h, pf) => Term::EqSubst(
            Box::new(inst_at(p, params, depth)),
            Box::new(inst_at(h, params, depth)),
            Box::new(inst_at(pf, params, depth)),
        ),
        Term::Const(id) => Term::Const(*id),
        Term::Meta(id) => Term::Meta(*id),
    }
}

// ── recargs ──────────────────────────────────────────────────────────────────

/// recargs: for each constructor argument at a recursive position (type IND(id,_)),
/// produce ELIM(id, motive, cases, arg).
/// inst_tel is the instantiated constructor type (nested PI, params already substituted).
/// We walk inst_tel in parallel with args to identify recursive positions.
pub fn recargs(
    env: &Env,
    ctx: &Ctx,
    id: u64,
    motive: &Term,
    cases: &[Term],
    mut inst_tel: Term,
    args: &[Term],
) -> Vec<Term> {
    let mut result = Vec::new();
    for arg in args {
        match whnf(env, ctx, inst_tel) {
            Term::Pi(a, rest) => {
                // Check if this field's type is the recursive inductive
                if let Term::Ind(fid, _) = whnf(env, ctx, *a) {
                    if fid == id {
                        result.push(Term::Elim(
                            id,
                            Box::new(motive.clone()),
                            cases.to_vec(),
                            Box::new(arg.clone()),
                        ));
                    }
                }
                inst_tel = subst(&rest, arg);
            }
            _ => break,
        }
    }
    result
}

// ── whnf ────────────────────────────────────────────────────────────────────

/// whnf(Σ, Γ, t) — reduce t to weak head normal form.
/// Applies β (App-Lam), δ (Let, CTX_LET VAR), ι (Elim-Ctor).
pub fn whnf(env: &Env, ctx: &Ctx, t: Term) -> Term {
    match t {
        // β: (λ_:A. body) a  →  subst(body, a)
        Term::App(f, a) => match whnf(env, ctx, *f) {
            Term::Lam(_, body) => whnf(env, ctx, subst(&body, &a)),
            f_whnf => Term::App(Box::new(f_whnf), a),
        },

        // δ (let): let _:=v in b  →  subst(b, v)
        Term::Let(_, v, b) => whnf(env, ctx, subst(&b, &v)),

        // δ (context): VAR(i) where ctx[i] is CTX_LET(_, v)
        Term::Var(i) => match ctx.get(i as usize) {
            Some(CtxEntry::Let(_, v)) => whnf(env, ctx, shift(v, i + 1)),
            _ => Term::Var(i),
        },

        // ι: ELIM(id, m, cs, CTOR(id, k, args))
        Term::Elim(id, motive, cases, target) => {
            match whnf(env, ctx, *target) {
                Term::Ctor(ctor_id, k, args) if ctor_id == id => {
                    // Look up descriptor; use placeholder params to identify recursive positions.
                    // Recursive positions are structurally fixed: IND(id, _) fields are always
                    // recursive regardless of what the params actually are.
                    let desc = match env.lookup(id) {
                        Some(d) => d,
                        None => {
                            let t = Term::Ctor(ctor_id, k, args);
                            return Term::Elim(id, motive, cases, Box::new(t));
                        }
                    };
                    let ctor_tel = match desc.constructors.get(k as usize) {
                        Some(t) => t.clone(),
                        None => {
                            let t = Term::Ctor(ctor_id, k, args);
                            return Term::Elim(id, motive, cases, Box::new(t));
                        }
                    };
                    // Substitute placeholder params (VAR(arity-1)…VAR(0)) so recursive
                    // positions appear as IND(id, _) after substitution.
                    let arity = desc.arity as usize;
                    let placeholders: Vec<Term> = (0..arity).rev().map(|i| Term::Var(i as u64)).collect();
                    let inst_tel = instantiate(&ctor_tel, &placeholders);
                    let rargs = recargs(env, ctx, id, &motive, &cases, inst_tel, &args);
                    let case_fn = cases[k as usize].clone();
                    // apply_case: foldl APP case_fn (args ++ rargs)
                    let mut f = case_fn;
                    for a in args.iter().chain(rargs.iter()) {
                        f = Term::App(Box::new(f), Box::new(a.clone()));
                    }
                    whnf(env, ctx, f)
                }
                target_whnf => Term::Elim(id, motive, cases, Box::new(target_whnf)),
            }
        }

        // ι: EqSubst(p, CTOR(EQ_ID, 0, _), pf_a) → pf_a
        Term::EqSubst(p, h, pf_a) => {
            match whnf(env, ctx, *h) {
                Term::Ctor(id, 0, _) if id == crate::stdlib::EQ_ID => {
                    whnf(env, ctx, *pf_a)
                }
                h_whnf => Term::EqSubst(p, Box::new(h_whnf), pf_a),
            }
        }

        // CONST: unfold transparent defs; leave axioms opaque
        Term::Const(id) => {
            if let Some(decl) = env.lookup_const(id) {
                if let Some(body) = &decl.body {
                    return whnf(env, ctx, body.clone());
                }
            }
            Term::Const(id)
        }

        // SORT, PI, LAM, IND, CTOR are already WHNF
        t => t,
    }
}

// ── full normalization ───────────────────────────────────────────────────────

/// nf(Σ, Γ, t) — reduce to full normal form (recursive WHNF under all binders).
/// Used by #eval; not needed for type checking.
pub fn nf(env: &Env, ctx: &Ctx, t: Term) -> Term {
    let h = whnf(env, ctx, t);
    match h {
        Term::Pi(a, b) => {
            let a_nf = nf(env, ctx, *a.clone());
            let mut ctx2 = ctx.clone();
            push_var(&mut ctx2, *a);
            Term::Pi(Box::new(a_nf), Box::new(nf(env, &ctx2, *b)))
        }
        Term::Lam(a, body) => {
            let a_nf = nf(env, ctx, *a.clone());
            let mut ctx2 = ctx.clone();
            push_var(&mut ctx2, *a);
            Term::Lam(Box::new(a_nf), Box::new(nf(env, &ctx2, *body)))
        }
        Term::App(f, a) => Term::App(Box::new(nf(env, ctx, *f)), Box::new(nf(env, ctx, *a))),
        Term::Let(a, v, b) => Term::Let(
            Box::new(nf(env, ctx, *a)),
            Box::new(nf(env, ctx, *v)),
            Box::new(nf(env, ctx, *b)),
        ),
        Term::Ind(id, params) => Term::Ind(id, params.into_iter().map(|p| nf(env, ctx, p)).collect()),
        Term::Ctor(id, k, args) => Term::Ctor(id, k, args.into_iter().map(|a| nf(env, ctx, a)).collect()),
        Term::Elim(id, m, cs, tg) => Term::Elim(
            id,
            Box::new(nf(env, ctx, *m)),
            cs.into_iter().map(|c| nf(env, ctx, c)).collect(),
            Box::new(nf(env, ctx, *tg)),
        ),
        Term::EqSubst(p, h, pf) => Term::EqSubst(
            Box::new(nf(env, ctx, *p)),
            Box::new(nf(env, ctx, *h)),
            Box::new(nf(env, ctx, *pf)),
        ),
        t => t, // Sort, Var, Const (already WHNF after whnf call above)
    }
}

// ── def_eq ──────────────────────────────────────────────────────────────────

/// def_eq(Σ, Γ, t, s) — definitional equality: reduce to WHNF then compare structurally.
pub fn def_eq(env: &Env, ctx: &Ctx, t: &Term, s: &Term) -> bool {
    let t_whnf = whnf(env, ctx, t.clone());
    let s_whnf = whnf(env, ctx, s.clone());
    structural_eq(env, ctx, &t_whnf, &s_whnf)
}

fn structural_eq(env: &Env, ctx: &Ctx, t: &Term, s: &Term) -> bool {
    match (t, s) {
        (Term::Sort(u), Term::Sort(v)) => u == v,

        (Term::Var(i), Term::Var(j)) => i == j,

        (Term::App(f, a), Term::App(g, b)) =>
            def_eq(env, ctx, f, g) && def_eq(env, ctx, a, b),

        (Term::Pi(a, b), Term::Pi(c, d)) => {
            if !def_eq(env, ctx, a, c) { return false; }
            let mut ctx2 = ctx.clone();
            push_var(&mut ctx2, *a.clone());
            def_eq(env, &ctx2, b, d)
        }

        (Term::Lam(a, tb), Term::Lam(b, sb)) => {
            if !def_eq(env, ctx, a, b) { return false; }
            let mut ctx2 = ctx.clone();
            push_var(&mut ctx2, *a.clone());
            def_eq(env, &ctx2, tb, sb)
        }

        (Term::Ind(id1, ps), Term::Ind(id2, qs)) =>
            id1 == id2 && ps.len() == qs.len()
            && ps.iter().zip(qs).all(|(p, q)| def_eq(env, ctx, p, q)),

        (Term::Ctor(id1, k1, as_), Term::Ctor(id2, k2, bs)) =>
            id1 == id2 && k1 == k2 && as_.len() == bs.len()
            && as_.iter().zip(bs).all(|(a, b)| def_eq(env, ctx, a, b)),

        (Term::Elim(id1, m1, cs1, tg1), Term::Elim(id2, m2, cs2, tg2)) =>
            id1 == id2
            && def_eq(env, ctx, m1, m2)
            && cs1.len() == cs2.len()
            && cs1.iter().zip(cs2).all(|(c1, c2)| def_eq(env, ctx, c1, c2))
            && def_eq(env, ctx, tg1, tg2),

        (Term::EqSubst(p1, h1, pf1), Term::EqSubst(p2, h2, pf2)) =>
            def_eq(env, ctx, p1, p2)
            && def_eq(env, ctx, h1, h2)
            && def_eq(env, ctx, pf1, pf2),

        (Term::Const(id1), Term::Const(id2)) => id1 == id2,

        // η: LAM vs non-LAM — expand the non-LAM side under a fresh binder
        (Term::Lam(a, body), other) => {
            let mut ctx2 = ctx.clone();
            push_var(&mut ctx2, *a.clone());
            let expanded = Term::App(Box::new(shift(other, 1)), Box::new(Term::Var(0)));
            def_eq(env, &ctx2, body, &expanded)
        }
        (other, Term::Lam(b, body)) => {
            let mut ctx2 = ctx.clone();
            push_var(&mut ctx2, *b.clone());
            let expanded = Term::App(Box::new(shift(other, 1)), Box::new(Term::Var(0)));
            def_eq(env, &ctx2, &expanded, body)
        }

        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Term;

    fn env() -> Env { Env::new() }
    fn ctx() -> Ctx { vec![] }

    #[test]
    fn whnf_sort() {
        assert_eq!(whnf(&env(), &ctx(), Term::Sort(0)), Term::Sort(0));
    }

    #[test]
    fn whnf_beta() {
        // (λ_:Sort(1). VAR(0)) Sort(0)  →β  Sort(0)
        let t = Term::App(
            Box::new(Term::Lam(Box::new(Term::Sort(1)), Box::new(Term::Var(0)))),
            Box::new(Term::Sort(0)),
        );
        assert_eq!(whnf(&env(), &ctx(), t), Term::Sort(0));
    }

    #[test]
    fn whnf_let_reduces() {
        // let _:Sort(1) := Sort(0) in VAR(0)  →δ  Sort(0)
        let t = Term::Let(
            Box::new(Term::Sort(1)),
            Box::new(Term::Sort(0)),
            Box::new(Term::Var(0)),
        );
        assert_eq!(whnf(&env(), &ctx(), t), Term::Sort(0));
    }

    #[test]
    fn def_eq_refl() {
        assert!(def_eq(&env(), &ctx(), &Term::Sort(0), &Term::Sort(0)));
        assert!(!def_eq(&env(), &ctx(), &Term::Sort(0), &Term::Sort(1)));
    }

    #[test]
    fn def_eq_beta() {
        let app = Term::App(
            Box::new(Term::Lam(Box::new(Term::Sort(1)), Box::new(Term::Var(0)))),
            Box::new(Term::Sort(0)),
        );
        assert!(def_eq(&env(), &ctx(), &app, &Term::Sort(0)));
    }

    #[test]
    fn def_eq_eta() {
        // In ctx with one var of type Sort(2),
        // λ_:Sort(1). APP(VAR(1), VAR(0))  def_eq  VAR(0)
        let mut c = ctx();
        push_var(&mut c, Term::Sort(2));
        let lam = Term::Lam(
            Box::new(Term::Sort(1)),
            Box::new(Term::App(Box::new(Term::Var(1)), Box::new(Term::Var(0)))),
        );
        assert!(def_eq(&env(), &c, &lam, &Term::Var(0)));
    }

    #[test]
    fn instantiate_empty_params() {
        let tel = Term::Pi(Box::new(Term::Sort(1)), Box::new(Term::Sort(0)));
        assert_eq!(instantiate(&tel, &[]), tel);
    }

    #[test]
    fn instantiate_one_param() {
        // ctor_tel = PI(VAR(0) → IND_return) with arity=1
        // After instantiate([Sort(0)]):  VAR(0) → Sort(0), and Sort(0) replaces return
        // Simple: tel = VAR(0); instantiate(VAR(0), [Sort(1)]) = Sort(1)
        let tel = Term::Var(0);
        let result = instantiate(&tel, &[Term::Sort(1)]);
        assert_eq!(result, Term::Sort(1));
    }
}
