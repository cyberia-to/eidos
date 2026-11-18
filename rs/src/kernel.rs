// kernel — trusted type checker: infer and check
// spec: specs/kernel.md
// TCB: this module plus term, ctx, env, subst, reduce.

use crate::{
    ctx::{ctx_lookup, push_let, push_var, Ctx, CtxEntry},
    env::Env,
    reduce::{def_eq, instantiate, whnf},
    subst::{shift, subst},
    term::Term,
};

// 2^64 - 2^32 + 1 (Goldilocks prime). Computed without overflow:
// u64::MAX = 2^64-1; u64::MAX - (2^32-1) = 2^64-2^32; +1 = 2^64-2^32+1
const GOLDILOCKS_P: u64 = u64::MAX - u32::MAX as u64 + 1;

/// Kernel error atoms (kernel.md § error encoding).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    UnboundVariable,                    // E000
    ExpectedSort,                       // E001
    ExpectedPi,                         // E002
    ExpectedInd,                        // E003
    TypeMismatch(Box<Term>, Box<Term>), // E004
    UnknownInductive,                   // E005
    ConstructorOutOfRange,              // E006
    BudgetExhausted,                    // E007
}

// ── Public entry points ──────────────────────────────────────────────────────

/// infer(Σ, Γ, term) → type | Error
pub fn infer(env: &Env, ctx: &Ctx, t: &Term) -> Result<Term, Error> {
    match t {
        // ── var ──────────────────────────────────────────────────────────────
        Term::Var(i) => {
            let entry = ctx_lookup(ctx, *i as usize).ok_or(Error::UnboundVariable)?;
            Ok(match entry {
                CtxEntry::Var(a) | CtxEntry::Let(a, _) => a,
            })
        }

        // ── sort ─────────────────────────────────────────────────────────────
        Term::Sort(u) => {
            if *u >= GOLDILOCKS_P - 1 {
                return Err(Error::ExpectedSort);
            }
            Ok(Term::Sort(u + 1))
        }

        // ── pi (Π-form) ──────────────────────────────────────────────────────
        Term::Pi(a, b) => {
            let s1 = require_sort(env, ctx, a)?;
            let mut ctx2 = ctx.clone();
            push_var(&mut ctx2, *a.clone());
            let s2 = require_sort(env, &ctx2, b)?;
            Ok(Term::Sort(Term::prop_max(s1, s2)))
        }

        // ── lam (Π-intro) ────────────────────────────────────────────────────
        Term::Lam(a, body) => {
            require_sort(env, ctx, a)?;
            let mut ctx2 = ctx.clone();
            push_var(&mut ctx2, *a.clone());
            let body_ty = infer(env, &ctx2, body)?;
            Ok(Term::Pi(a.clone(), Box::new(body_ty)))
        }

        // ── app (Π-elim) ─────────────────────────────────────────────────────
        Term::App(f, arg) => {
            let f_ty = infer(env, ctx, f)?;
            match whnf(env, ctx, f_ty) {
                Term::Pi(a, b) => {
                    check(env, ctx, arg, &a)?;
                    Ok(subst(&b, arg))
                }
                _ => Err(Error::ExpectedPi),
            }
        }

        // ── let ──────────────────────────────────────────────────────────────
        Term::Let(a, v, b) => {
            check(env, ctx, v, a)?;
            let mut ctx2 = ctx.clone();
            push_let(&mut ctx2, *a.clone(), *v.clone());
            let b_ty = infer(env, &ctx2, b)?;
            Ok(subst(&b_ty, v))
        }

        // ── ind (Ind-form) ───────────────────────────────────────────────────
        Term::Ind(id, params) => {
            let desc = env.lookup(*id).ok_or(Error::UnknownInductive)?;
            if params.len() as u64 != desc.arity {
                return Err(Error::TypeMismatch(
                    Box::new(Term::Ind(*id, params.clone())),
                    Box::new(Term::Sort(desc.sort)),
                ));
            }
            let param_types = unroll_telescope(&desc.param_tel, params);
            for (p, p_ty) in params.iter().zip(param_types.iter()) {
                check(env, ctx, p, p_ty)?;
            }
            Ok(Term::Sort(desc.sort))
        }

        // ── ctor (Ind-intro) ─────────────────────────────────────────────────
        // CTOR(id, k, args): args = params[0..arity] ++ field_args[arity..]
        Term::Ctor(id, k, args) => {
            let desc = env.lookup(*id).ok_or(Error::UnknownInductive)?;
            let ctor_tel = desc
                .constructors
                .get(*k as usize)
                .ok_or(Error::ConstructorOutOfRange)?
                .clone();
            let arity = desc.arity as usize;
            if args.len() < arity {
                return Err(Error::TypeMismatch(
                    Box::new(Term::Ctor(*id, *k, args.clone())),
                    Box::new(Term::Sort(0)),
                ));
            }
            let params = &args[..arity];
            let field_args = &args[arity..];
            let inst_type = instantiate(&ctor_tel, params);
            apply_args(env, ctx, inst_type, field_args)
        }

        // ── eq_subst (J-rule / Leibniz transport) ───────────────────────────
        // EqSubst(p, h, pf_a):
        //   h  : Eq A a b
        //   pf_a : p(a) = App(p, a)
        //   result type : p(b) = App(p, b)
        //   reduces to pf_a when h = refl
        Term::EqSubst(p, h, pf_a) => {
            use crate::stdlib::EQ_ID;
            let h_ty = infer(env, ctx, h)?;
            let (h_a, h_b) = match whnf(env, ctx, h_ty) {
                Term::Ind(id, params) if id == EQ_ID && params.len() == 3 => {
                    (params[1].clone(), params[2].clone())
                }
                _ => {
                    return Err(Error::TypeMismatch(
                        Box::new(h.as_ref().clone()),
                        Box::new(Term::Sort(0)),
                    ))
                }
            };
            let pf_a_ty = Term::App(p.clone(), Box::new(h_a));
            check(env, ctx, pf_a, &pf_a_ty)?;
            Ok(Term::App(p.clone(), Box::new(h_b)))
        }

        // ── const — look up type from env ────────────────────────────────────
        Term::Const(id) => {
            let decl = env.lookup_const(*id).ok_or(Error::UnknownInductive)?;
            Ok(decl.ty.clone())
        }

        // ── meta — rejected; call elab::meta::zonk before kernel ────────────
        Term::Meta(_) => Err(Error::ExpectedSort),

        // ── elim (Ind-elim) ──────────────────────────────────────────────────
        Term::Elim(id, motive, cases, target) => {
            let desc = env.lookup(*id).ok_or(Error::UnknownInductive)?.clone();

            // Target type must be IND(id, params)
            let t_ty = infer(env, ctx, target)?;
            let params = match whnf(env, ctx, t_ty) {
                Term::Ind(tid, p) if tid == *id => p,
                _ => return Err(Error::ExpectedInd),
            };

            // Motive must be: IND(id, params') → SORT(s)
            let m_ty = infer(env, ctx, motive)?;
            let elim_sort = match whnf(env, ctx, m_ty) {
                Term::Pi(dom, cod) => match (whnf(env, ctx, *dom), whnf(env, ctx, *cod)) {
                    (Term::Ind(mid, mparams), Term::Sort(s)) if mid == *id => {
                        if mparams.len() != params.len()
                            || !mparams
                                .iter()
                                .zip(&params)
                                .all(|(a, b)| def_eq(env, ctx, a, b))
                        {
                            return Err(Error::TypeMismatch(
                                Box::new(motive.as_ref().clone()),
                                Box::new(Term::Sort(0)),
                            ));
                        }
                        s
                    }
                    _ => {
                        return Err(Error::TypeMismatch(
                            Box::new(motive.as_ref().clone()),
                            Box::new(Term::Sort(0)),
                        ))
                    }
                },
                _ => return Err(Error::ExpectedPi),
            };

            // Large elimination gate: Prop inductive → Type only when proof-irrelevant
            if desc.sort == 0 && elim_sort > 0 {
                if desc.constructors.len() > 1 {
                    return Err(Error::TypeMismatch(
                        Box::new(motive.as_ref().clone()),
                        Box::new(Term::Sort(0)),
                    ));
                }
                for ctor_tel in &desc.constructors {
                    check_all_fields_prop(env, ctx, ctor_tel, &params)?;
                }
            }

            // Each case must have the expected type
            if cases.len() != desc.constructors.len() {
                return Err(Error::TypeMismatch(
                    Box::new(Term::Sort(0)),
                    Box::new(Term::Sort(0)),
                ));
            }
            for (k, (case, ctor_tel)) in cases.iter().zip(desc.constructors.iter()).enumerate() {
                let expected = case_type(env, ctx, ctor_tel, k, *id, motive, &params);
                check(env, ctx, case, &expected)?;
            }

            Ok(Term::App(motive.clone(), target.clone()))
        }
    }
}

/// check(Σ, Γ, term, expected) → Ok | Error
pub fn check(env: &Env, ctx: &Ctx, t: &Term, expected: &Term) -> Result<(), Error> {
    let actual = infer(env, ctx, t)?;
    if def_eq(env, ctx, &actual, expected) {
        Ok(())
    } else {
        Err(Error::TypeMismatch(
            Box::new(actual),
            Box::new(expected.clone()),
        ))
    }
}

// ── Helper functions ─────────────────────────────────────────────────────────

fn require_sort(env: &Env, ctx: &Ctx, t: &Term) -> Result<u64, Error> {
    match infer(env, ctx, t)? {
        Term::Sort(u) => Ok(u),
        _ => Err(Error::ExpectedSort),
    }
}

/// unroll_telescope(param_tel, params) → list of parameter types with earlier params substituted.
/// param_tel: PI(P₀, PI(P₁, … _)).
/// `Result[i]` is Pᵢ with `params[0..i]` substituted in.
pub fn unroll_telescope(param_tel: &Term, params: &[Term]) -> Vec<Term> {
    let mut result = Vec::with_capacity(params.len());
    let mut tel = param_tel.clone();
    let empty_env = Env::new();
    let empty_ctx: Ctx = vec![];
    for i in 0..params.len() {
        match whnf(&empty_env, &empty_ctx, tel) {
            Term::Pi(a, b) => {
                // Substitute params[0..i] into the type annotation, innermost-first (reverse)
                // so that VAR(0) refers to params[i-1], VAR(1) to params[i-2], etc.
                let mut ty = *a;
                for p in params[..i].iter().rev() {
                    ty = subst(&ty, p);
                }
                result.push(ty);
                tel = *b;
            }
            _ => break,
        }
    }
    result
}

/// apply_args: walk a nested PI constructor type, checking each arg and substituting.
/// Returns the final return type after all args are consumed.
pub fn apply_args(env: &Env, ctx: &Ctx, mut t: Term, args: &[Term]) -> Result<Term, Error> {
    for arg in args {
        match whnf(env, ctx, t) {
            Term::Pi(a, b) => {
                check(env, ctx, arg, &a)?;
                t = subst(&b, arg);
            }
            _ => return Err(Error::ExpectedPi),
        }
    }
    Ok(t)
}

/// Check all field types in an instantiated constructor telescope are in Prop (SORT(0)).
fn check_all_fields_prop(
    env: &Env,
    ctx: &Ctx,
    ctor_tel: &Term,
    params: &[Term],
) -> Result<(), Error> {
    let mut t = instantiate(ctor_tel, params);
    while let Term::Pi(a, rest) = whnf(env, ctx, t) {
        // Check this field type is in SORT(0)
        match infer(env, ctx, &a)? {
            Term::Sort(0) => {}
            _ => return Err(Error::TypeMismatch(Box::new(*a), Box::new(Term::Sort(0)))),
        }
        // Advance: substitute a fresh var (the field) into rest
        t = subst(&rest, &Term::Var(0));
    }
    Ok(())
}

/// case_type: expected type for the k-th case function.
/// spec: kernel.md § case_type / build
pub fn case_type(
    env: &Env,
    ctx: &Ctx,
    ctor_tel: &Term,
    k: usize,
    ind_id: u64,
    motive: &Term,
    params: &[Term],
) -> Term {
    let inst = instantiate(ctor_tel, params);
    build_case_type(env, ctx, inst, motive, k, ind_id, &[])
}

/// Recursive builder for the k-th case type.
/// tel: instantiated constructor type (nested PI; return type at the end).
/// rev_fields: field variables accumulated so far, innermost-first.
fn build_case_type(
    env: &Env,
    ctx: &Ctx,
    tel: Term,
    motive: &Term,
    ctor_idx: usize,
    ind_id: u64,
    rev_fields: &[Term],
) -> Term {
    match whnf(env, ctx, tel) {
        Term::Pi(a, rest) => {
            let a_whnf = whnf(env, ctx, *a.clone());
            let is_recursive = matches!(&a_whnf, Term::Ind(fid, _) if *fid == ind_id);

            if is_recursive {
                // Recursive field: PI(Aᵢ, PI(IH, inner))
                // IH type: APP(shift(motive, 1), VAR(0))  (motive shifted under field binder)
                let ih_ty = Term::App(Box::new(shift(motive, 1)), Box::new(Term::Var(0)));
                // Under 2 new binders (field=VAR(1), IH=VAR(0)):
                // - rest needs shift(1) because we add IH binder on top of field binder
                // - rev_fields shift by 2; current field = VAR(1)
                let rest_shifted = shift(&subst(&rest, &Term::Var(0)), 1);
                let new_rev: Vec<Term> = std::iter::once(Term::Var(1))
                    .chain(rev_fields.iter().map(|t| shift(t, 2)))
                    .collect();
                let inner = build_case_type(
                    env,
                    ctx,
                    rest_shifted,
                    &shift(motive, 2),
                    ctor_idx,
                    ind_id,
                    &new_rev,
                );
                Term::Pi(a, Box::new(Term::Pi(Box::new(ih_ty), Box::new(inner))))
            } else {
                // Non-recursive field: PI(Aᵢ, inner)
                // Under 1 new binder (field=VAR(0)):
                let rest_subst = subst(&rest, &Term::Var(0));
                let new_rev: Vec<Term> = std::iter::once(Term::Var(0))
                    .chain(rev_fields.iter().map(|t| shift(t, 1)))
                    .collect();
                let inner = build_case_type(
                    env,
                    ctx,
                    rest_subst,
                    &shift(motive, 1),
                    ctor_idx,
                    ind_id,
                    &new_rev,
                );
                Term::Pi(a, Box::new(inner))
            }
        }

        // Return type reached — all fields collected
        _ => {
            let mut fields: Vec<Term> = rev_fields.to_vec();
            fields.reverse();
            Term::App(
                Box::new(motive.clone()),
                Box::new(Term::Ctor(ind_id, ctor_idx as u64, fields)),
            )
        }
    }
}

#[cfg(test)]
mod tests;
