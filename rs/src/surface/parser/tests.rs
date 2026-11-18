// tests for parser — split out so that surface/parser.rs stays under the 500-line cap.

use super::*;
use crate::surface::lexer::lex;

fn decls(src: &str) -> Vec<SurfaceDecl> {
    parse_file(&lex(src).unwrap()).unwrap()
}
fn tactics(src: &str) -> Vec<Tactic> {
    parse_tactic_block(&lex(src).unwrap()).unwrap()
}

#[test]
fn axiom_simple() {
    let ds = decls("axiom em : Prop");
    assert!(matches!(&ds[0], SurfaceDecl::Axiom { name, .. } if name == "em"));
}
#[test]
fn def_identity() {
    let ds = decls("def id (A : Type) (a : A) : A := a");
    match &ds[0] {
        SurfaceDecl::Def { name, params, .. } => {
            assert_eq!(name, "id");
            assert_eq!(params.len(), 2);
        }
        _ => panic!("expected Def"),
    }
}
#[test]
fn theorem_term_proof() {
    let ds = decls("theorem t : Prop := sorry");
    assert!(matches!(
        &ds[0],
        SurfaceDecl::Theorem {
            proof: Proof::Term(_),
            ..
        }
    ));
}
#[test]
fn theorem_tactic_proof() {
    let ds = decls("theorem t : Prop := by { sorry }");
    assert!(matches!(
        &ds[0],
        SurfaceDecl::Theorem {
            proof: Proof::Tactics(_),
            ..
        }
    ));
}
#[test]
fn inductive_nat() {
    let ds = decls("inductive Nat : Type where | zero : Nat | succ : Nat -> Nat");
    match &ds[0] {
        SurfaceDecl::Inductive { name, ctors, .. } => {
            assert_eq!(name, "Nat");
            assert_eq!(ctors.len(), 2);
        }
        _ => panic!("expected Inductive"),
    }
}
#[test]
fn check_cmd() {
    let ds = decls("#check Nat.zero");
    assert!(matches!(&ds[0], SurfaceDecl::CheckCmd(Expr::Name(n)) if n == "Nat.zero"));
}
#[test]
fn arrow_type() {
    let ds = decls("axiom f : Nat -> Nat");
    assert!(matches!(
        &ds[0],
        SurfaceDecl::Axiom {
            ty: Expr::Arrow(..),
            ..
        }
    ));
}
#[test]
fn forall_expr() {
    let ds = decls("axiom f : ∀ (n : Nat), Nat");
    assert!(matches!(
        &ds[0],
        SurfaceDecl::Axiom {
            ty: Expr::Pi(..),
            ..
        }
    ));
}
#[test]
fn tactic_intro_exact() {
    let ts = tactics("intro n; exact n");
    assert_eq!(ts.len(), 2);
    assert!(matches!(&ts[0], Tactic::Intro(ns) if ns[0] == "n"));
    assert!(matches!(&ts[1], Tactic::Exact(Expr::Name(n)) if n == "n"));
}
#[test]
fn tactic_simp_lemmas() {
    let ts = tactics("simp [Nat.add_comm, h]");
    assert!(matches!(&ts[0], Tactic::Simp(ls) if ls.len() == 2));
}
#[test]
fn tactic_have() {
    let ts = tactics("have h : Nat := Nat.zero");
    assert!(matches!(&ts[0], Tactic::Have { name, .. } if name == "h"));
}
#[test]
fn tactic_rewrite_reverse() {
    let ts = tactics("rewrite [← h]");
    assert!(matches!(&ts[0], Tactic::Rewrite { reverse: true, .. }));
}
#[test]
fn tactic_bullet_focus() {
    let ts = tactics("· exact h");
    assert!(matches!(&ts[0], Tactic::Focus(_)));
}
#[test]
fn tactic_case() {
    let ts = tactics("case zero => rfl");
    assert!(matches!(&ts[0], Tactic::Case { ctor, body, .. }
        if ctor == "zero" && matches!(body[0], Tactic::Rfl)));
}
#[test]
fn multi_name_binder() {
    let ds = decls("def swap (n m : Nat) : Nat := n");
    match &ds[0] {
        SurfaceDecl::Def { params, .. } => assert_eq!(params.len(), 2),
        _ => panic!("expected Def"),
    }
}
#[test]
fn type_universe_level() {
    let ds = decls("axiom big : Type 2");
    assert!(matches!(
        &ds[0],
        SurfaceDecl::Axiom {
            ty: Expr::Sort(Some(2)),
            ..
        }
    ));
}
#[test]
fn anon_ctor() {
    let ds = decls("def p : Unit := ⟨⟩");
    assert!(matches!(&ds[0], SurfaceDecl::Def { .. }));
}
#[test]
fn empty_file() {
    assert_eq!(decls(""), vec![]);
}
#[test]
fn eof_without_panic() {
    let toks = lex("def").unwrap();
    assert!(parse_file(&toks).is_err());
}
