// elab — elaborator: surface syntax → kernel terms (untrusted shell)
// spec: specs/surface.md
// Bugs here produce terms the kernel rejects — they cannot forge proofs.

pub mod ast;
pub mod meta;
pub mod core;
pub mod decl;

pub use meta::ElabError;
pub use core::{ElabState, elab_expr};
pub use decl::elab_decl;

#[cfg(test)]
mod tests {
    use super::{ast::*, core::*, elab_expr, elab_decl, ElabError};
    use crate::stdlib::std_env;

    fn st() -> ElabState {
        let mut s = ElabState::new();
        s.add_stdlib();
        s
    }

    #[test]
    fn elab_prop() {
        let mut st = st();
        let env = std_env();
        let (t, ty) = elab_expr(&mut st, &env, &Expr::Sort(None)).unwrap();
        assert_eq!(t,  crate::term::Term::Sort(0));
        assert_eq!(ty, crate::term::Term::Sort(1));
    }

    #[test]
    fn elab_type0() {
        let mut st = st();
        let env = std_env();
        let (t, ty) = elab_expr(&mut st, &env, &Expr::Sort(Some(0))).unwrap();
        assert_eq!(t,  crate::term::Term::Sort(1));
        assert_eq!(ty, crate::term::Term::Sort(2));
    }

    #[test]
    fn elab_nat_name() {
        let mut st = st();
        let env = std_env();
        let (t, ty) = elab_expr(&mut st, &env, &Expr::Name("Nat".into())).unwrap();
        assert_eq!(t,  crate::stdlib::nat());
        assert_eq!(ty, crate::term::Term::Sort(1));
    }

    #[test]
    fn elab_nat_lit() {
        let mut st = st();
        let env = std_env();
        let (t, ty) = elab_expr(&mut st, &env, &Expr::NatLit(3)).unwrap();
        assert_eq!(t,  crate::stdlib::nat_lit(3));
        assert_eq!(ty, crate::stdlib::nat());
    }

    #[test]
    fn elab_arrow_nat_nat() {
        // Nat -> Nat should elab to PI(Nat, Nat)
        let mut st = st();
        let env = std_env();
        let expr = Expr::Arrow(
            Box::new(Expr::Name("Nat".into())),
            Box::new(Expr::Name("Nat".into())),
        );
        let (t, ty) = elab_expr(&mut st, &env, &expr).unwrap();
        let nat = crate::stdlib::nat();
        let expected = crate::term::Term::Pi(Box::new(nat.clone()), Box::new(nat));
        assert_eq!(t, expected);
        assert_eq!(ty, crate::term::Term::Sort(1));
    }

    #[test]
    fn elab_fun_identity() {
        // fun (n: Nat) => n  should give LAM(Nat, VAR(0))
        let mut st = st();
        let env = std_env();
        let expr = Expr::Fun(
            Binder::Explicit("n".into(), Box::new(Expr::Name("Nat".into()))),
            Box::new(Expr::Name("n".into())),
        );
        let (t, _ty) = elab_expr(&mut st, &env, &expr).unwrap();
        let nat = crate::stdlib::nat();
        let expected = crate::term::Term::Lam(Box::new(nat), Box::new(crate::term::Term::Var(0)));
        assert_eq!(t, expected);
    }

    #[test]
    fn elab_app_nat_next() {
        // Nat.next 0  should reduce to nat_lit(1) and have type Nat
        let mut st = st();
        let env = std_env();
        let expr = Expr::App(
            Box::new(Expr::Name("Nat.next".into())),
            Box::new(Expr::NatLit(0)),
        );
        let (t, ty) = elab_expr(&mut st, &env, &expr).unwrap();
        // Type must be Nat
        assert_eq!(ty, crate::stdlib::nat());
        // Term reduces to nat_lit(1)
        let ctx = vec![];
        let nf = crate::reduce::nf(&env, &ctx, t);
        assert_eq!(nf, crate::stdlib::nat_lit(1));
    }

    #[test]
    fn elab_unknown_name_fails() {
        let mut st = st();
        let env = std_env();
        let r = elab_expr(&mut st, &env, &Expr::Name("DoesNotExist".into()));
        assert!(matches!(r, Err(ElabError::UnknownName(_))));
    }

    #[test]
    fn elab_hole_gives_metas() {
        let mut st = st();
        let env = std_env();
        let (t, ty) = elab_expr(&mut st, &env, &Expr::Hole).unwrap();
        // both should be Meta terms
        assert!(matches!(t,  crate::term::Term::Meta(_)));
        assert!(matches!(ty, crate::term::Term::Meta(_)));
    }

    #[test]
    fn elab_def_identity() {
        // def id (n : Nat) : Nat := n
        let mut st = st();
        let mut env = std_env();
        let decl = Decl::Def {
            name: "id".into(),
            params: vec![Binder::Explicit("n".into(), Box::new(Expr::Name("Nat".into())))],
            ty:   Box::new(Expr::Name("Nat".into())),
            body: Box::new(Expr::Name("n".into())),
        };
        elab_decl(&mut st, &mut env, &decl).unwrap();
        assert!(st.globals.contains_key("id"));
    }

    #[test]
    fn elab_match_nat() {
        // fun (n: Nat) => match n with | zero => 0 | next m _ih => m
        let mut st = st();
        let env = std_env();
        let expr = Expr::Fun(
            Binder::Explicit("n".into(), Box::new(Expr::Name("Nat".into()))),
            Box::new(Expr::Match(
                Box::new(Expr::Name("n".into())),
                None,
                vec![
                    Arm {
                        pattern: Pattern::App("zero".into(), vec![]),
                        body: Box::new(Expr::NatLit(0)),
                    },
                    Arm {
                        pattern: Pattern::App("next".into(), vec!["m".into(), "_ih".into()]),
                        body: Box::new(Expr::Name("m".into())),
                    },
                ],
            )),
        );
        let result = elab_expr(&mut st, &env, &expr);
        assert!(result.is_ok(), "match nat failed: {:?}", result);
    }
}
