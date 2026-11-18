// tests for kernel — split out so that kernel.rs stays under the 500-line cap.

use super::*;
use crate::{ctx::CtxEntry, env::IndDesc, term::Term};

fn prop() -> Term {
    Term::Sort(0)
}
fn type0() -> Term {
    Term::Sort(1)
}
fn mk_env() -> Env {
    Env::new()
}
fn mk_ctx() -> Ctx {
    vec![]
}

#[test]
fn infer_var_unbound() {
    assert_eq!(
        infer(&mk_env(), &mk_ctx(), &Term::Var(0)),
        Err(Error::UnboundVariable)
    );
}

#[test]
fn infer_var_in_ctx() {
    let ctx = vec![CtxEntry::Var(Term::Sort(1))];
    // VAR(0) : Sort(1) (shift(Sort(1), 1) = Sort(1), no free vars)
    assert_eq!(infer(&mk_env(), &ctx, &Term::Var(0)), Ok(Term::Sort(1)));
}

#[test]
fn infer_sort() {
    assert_eq!(
        infer(&mk_env(), &mk_ctx(), &Term::Sort(0)),
        Ok(Term::Sort(1))
    );
    assert_eq!(
        infer(&mk_env(), &mk_ctx(), &Term::Sort(1)),
        Ok(Term::Sort(2))
    );
}

#[test]
fn infer_sort_overflow() {
    assert_eq!(
        infer(&mk_env(), &mk_ctx(), &Term::Sort(GOLDILOCKS_P - 1)),
        Err(Error::ExpectedSort)
    );
}

#[test]
fn infer_pi_sort_to_sort() {
    // PI(Sort(0), Sort(0)): infer(Sort(0))=Sort(1) → s1=1, s2=1, prop_max(1,1)=1 → Sort(1)
    // This is the UNIVERSE (Prop → Prop as sorts), not impredicative.
    let pi = Term::Pi(Box::new(prop()), Box::new(prop()));
    assert_eq!(infer(&mk_env(), &mk_ctx(), &pi), Ok(type0()));
}

#[test]
fn infer_pi_type() {
    // PI(Sort(1), Sort(1)): infer(Sort(1))=Sort(2) → s1=2, s2=2, prop_max(2,2)=2 → Sort(2)
    let pi = Term::Pi(Box::new(type0()), Box::new(type0()));
    assert_eq!(infer(&mk_env(), &mk_ctx(), &pi), Ok(Term::Sort(2)));
}

#[test]
fn infer_pi_impredicative() {
    // ∀ P : Prop, P → P  should be in Prop.
    // PI(Sort(0), PI(VAR(0), VAR(1)))  in de Bruijn.
    // Outer: s1 = level(infer(Sort(0))) = 1
    // Inner PI(VAR(0), VAR(1)):
    //   ctx has [Var(Sort(0))]; infer(VAR(0))=Sort(0), s1=0
    //   ctx has [Var(VAR(0)),Var(Sort(0))]; infer(VAR(1))=Sort(0), s2=0
    //   prop_max(0,0) = 0 → inner : Sort(0)
    // prop_max(1, 0) = 0 → outer : Sort(0) = Prop  ✓
    let inner = Term::Pi(Box::new(Term::Var(0)), Box::new(Term::Var(1)));
    let outer = Term::Pi(Box::new(prop()), Box::new(inner));
    assert_eq!(infer(&mk_env(), &mk_ctx(), &outer), Ok(prop()));
}

#[test]
fn infer_lam() {
    // λ(_:Type₀). VAR(0) : Type₀ → Type₀
    let lam = Term::Lam(Box::new(type0()), Box::new(Term::Var(0)));
    let expected = Term::Pi(Box::new(type0()), Box::new(type0()));
    assert_eq!(infer(&mk_env(), &mk_ctx(), &lam), Ok(expected));
}

#[test]
fn infer_app_reduces() {
    // (λ(_:Type₀). VAR(0)) Sort(0) : Type₀
    let lam = Term::Lam(Box::new(type0()), Box::new(Term::Var(0)));
    let app = Term::App(Box::new(lam), Box::new(Term::Sort(0)));
    assert_eq!(infer(&mk_env(), &mk_ctx(), &app), Ok(type0()));
}

#[test]
fn check_ok() {
    // Sort(0) : Sort(1)
    assert_eq!(
        check(&mk_env(), &mk_ctx(), &Term::Sort(0), &Term::Sort(1)),
        Ok(())
    );
}

#[test]
fn check_mismatch() {
    // Sort(0) is NOT Sort(0) (Sort(0) : Sort(1), not Sort(0))
    assert!(check(&mk_env(), &mk_ctx(), &Term::Sort(0), &Term::Sort(0)).is_err());
}

#[test]
fn prop_max_laws() {
    assert_eq!(Term::prop_max(0, 0), 0);
    assert_eq!(Term::prop_max(0, 5), 5);
    assert_eq!(Term::prop_max(5, 0), 0);
    assert_eq!(Term::prop_max(2, 3), 3);
}

#[test]
fn infer_ind_nat() {
    // Build a minimal Nat descriptor: arity=0, sort=1 (Type₀), no params, constructors later
    let nat_id: u64 = 1;
    let desc = IndDesc {
        arity: 0,
        sort: 1,
        param_tel: Term::Sort(0), // unused (arity=0)
        constructors: vec![
            // Nat.zero : Nat   — no fields, return type = IND(nat_id, [])
            Term::Ind(nat_id, vec![]),
            // Nat.next : Nat → Nat — one field of type Nat, return type Nat
            Term::Pi(
                Box::new(Term::Ind(nat_id, vec![])),
                Box::new(Term::Ind(nat_id, vec![])),
            ),
        ],
    };
    let mut env = mk_env();
    env.insert(nat_id, desc);
    // IND(nat_id, []) : Sort(1) = Type₀
    assert_eq!(
        infer(&env, &mk_ctx(), &Term::Ind(nat_id, vec![])),
        Ok(Term::Sort(1))
    );
}

#[test]
fn infer_ctor_zero() {
    // arity=0: no params, no fields; zero : Nat
    let nat_id: u64 = 1;
    let desc = IndDesc {
        arity: 0,
        sort: 1,
        param_tel: Term::Sort(0),
        constructors: vec![
            Term::Ind(nat_id, vec![]),
            Term::Pi(
                Box::new(Term::Ind(nat_id, vec![])),
                Box::new(Term::Ind(nat_id, vec![])),
            ),
        ],
    };
    let mut env = mk_env();
    env.insert(nat_id, desc);
    // CTOR(nat_id, 0, []) — arity=0, args=[], params=[], fields=[] → Nat
    assert_eq!(
        infer(&env, &mk_ctx(), &Term::Ctor(nat_id, 0, vec![])),
        Ok(Term::Ind(nat_id, vec![]))
    );
}

#[test]
fn infer_ctor_next() {
    // CTOR(nat_id, 1, [zero]) — arity=0, params=[], fields=[zero] → Nat
    let nat_id: u64 = 1;
    let desc = IndDesc {
        arity: 0,
        sort: 1,
        param_tel: Term::Sort(0),
        constructors: vec![
            Term::Ind(nat_id, vec![]),
            Term::Pi(
                Box::new(Term::Ind(nat_id, vec![])),
                Box::new(Term::Ind(nat_id, vec![])),
            ),
        ],
    };
    let mut env = mk_env();
    env.insert(nat_id, desc);
    let zero = Term::Ctor(nat_id, 0, vec![]);
    assert_eq!(
        infer(&env, &mk_ctx(), &Term::Ctor(nat_id, 1, vec![zero])),
        Ok(Term::Ind(nat_id, vec![]))
    );
}

#[test]
fn case_type_nat_zero() {
    // Nat.zero case: motive : Nat → Prop
    // case_type for constructor 0 (zero, no fields) = APP(motive, CTOR(nat, 0, []))
    let nat_id: u64 = 1;
    let zero_tel = Term::Ind(nat_id, vec![]); // return type only
    let motive = Term::Lam(Box::new(Term::Ind(nat_id, vec![])), Box::new(Term::Sort(0)));
    let env = mk_env();
    let ctx = mk_ctx();
    let ct = case_type(&env, &ctx, &zero_tel, 0, nat_id, &motive, &[]);
    // Should be: APP(motive, CTOR(nat_id, 0, []))
    let expected = Term::App(
        Box::new(motive.clone()),
        Box::new(Term::Ctor(nat_id, 0, vec![])),
    );
    assert_eq!(ct, expected);
}

#[test]
fn case_type_nat_next() {
    // Nat.next case: PI(n:Nat, PI(IH:motive n, APP(motive, CTOR(nat,1,[n]))))
    let nat_id: u64 = 1;
    let next_tel = Term::Pi(
        Box::new(Term::Ind(nat_id, vec![])), // field: n : Nat
        Box::new(Term::Ind(nat_id, vec![])), // return: Nat
    );
    let motive = Term::Var(0); // placeholder motive var
    let env = mk_env();
    let ctx = mk_ctx();
    let ct = case_type(&env, &ctx, &next_tel, 1, nat_id, &motive, &[]);
    // Expected: PI(Nat, PI(APP(shift(motive,1), VAR(0)), APP(shift(motive,2), CTOR(nat,1,[VAR(1)]))))
    let nat_ty = Term::Ind(nat_id, vec![]);
    let ih_ty = Term::App(Box::new(shift(&motive, 1)), Box::new(Term::Var(0)));
    let return_ty = Term::App(
        Box::new(shift(&motive, 2)),
        Box::new(Term::Ctor(nat_id, 1, vec![Term::Var(1)])),
    );
    let expected = Term::Pi(
        Box::new(nat_ty),
        Box::new(Term::Pi(Box::new(ih_ty), Box::new(return_ty))),
    );
    assert_eq!(ct, expected);
}
