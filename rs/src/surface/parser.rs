// surface/parser.rs — recursive-descent parser for .ei proof files
// spec: specs/surface.md § parser
//
// Input:  &[Token]  (from surface::lexer::lex)
// Output: Vec<SurfaceDecl>
//
// Tactic AST and tactic parsing live in surface::tactics (sibling module).

use crate::elab::ast::{Binder, Expr};
use crate::surface::lexer::Token;
use crate::surface::tactics;

pub use crate::surface::tactics::{Proof, Tactic};

// ── Top-level declaration type ────────────────────────────────────────────────

/// A top-level surface declaration.
#[derive(Debug, Clone, PartialEq)]
pub enum SurfaceDecl {
    Def {
        name: String,
        params: Vec<Binder>,
        ty: Expr,
        body: Expr,
    },
    Theorem {
        name: String,
        params: Vec<Binder>,
        ty: Expr,
        proof: Proof,
    },
    Axiom {
        name: String,
        params: Vec<Binder>,
        ty: Expr,
    },
    Inductive {
        name: String,
        params: Vec<Binder>,
        sort: Expr,
        ctors: Vec<(String, Expr)>,
    },
    Import { path: String },
    CheckCmd(Expr),
}

// ── Parser state ──────────────────────────────────────────────────────────────

pub(crate) struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(tokens: &'a [Token]) -> Self { Parser { tokens, pos: 0 } }

    pub(crate) fn peek(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or(&Token::Eof)
    }

    pub(crate) fn advance(&mut self) -> &Token {
        let t = self.tokens.get(self.pos).unwrap_or(&Token::Eof);
        if self.pos < self.tokens.len() { self.pos += 1; }
        t
    }

    pub(crate) fn eat(&mut self, expected: &Token) -> Result<(), String> {
        if self.peek() == expected {
            self.advance();
            Ok(())
        } else {
            Err(format!("expected {:?}, found {:?}", expected, self.peek()))
        }
    }

    pub(crate) fn eat_ident(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            Token::Ident(s) => { self.advance(); Ok(s) }
            other => Err(format!("expected identifier, found {:?}", other)),
        }
    }

    fn is_at_end(&self) -> bool { matches!(self.peek(), Token::Eof) }
}

// ── Binder parsing ────────────────────────────────────────────────────────────

fn parse_binder_group(p: &mut Parser) -> Result<Vec<Binder>, String> {
    match p.peek().clone() {
        Token::LParen => {
            p.advance();
            let names = parse_name_list(p)?;
            p.eat(&Token::Colon)?;
            let ty = parse_expr(p)?;
            p.eat(&Token::RParen)?;
            Ok(names.into_iter().map(|n| Binder::Explicit(n, Box::new(ty.clone()))).collect())
        }
        Token::LBrace => {
            p.advance();
            let names = parse_name_list(p)?;
            p.eat(&Token::Colon)?;
            let ty = parse_expr(p)?;
            p.eat(&Token::RBrace)?;
            Ok(names.into_iter().map(|n| Binder::Implicit(n, Box::new(ty.clone()))).collect())
        }
        other => Err(format!("expected binder '(' or '{{', found {:?}", other)),
    }
}

fn parse_name_list(p: &mut Parser) -> Result<Vec<String>, String> {
    let mut names = vec![p.eat_ident()?];
    while let Token::Ident(_) = p.peek() { names.push(p.eat_ident()?); }
    Ok(names)
}

pub(crate) fn parse_binders(p: &mut Parser) -> Result<Vec<Binder>, String> {
    let mut binders = Vec::new();
    loop {
        match p.peek() {
            Token::LParen | Token::LBrace => binders.extend(parse_binder_group(p)?),
            _ => break,
        }
    }
    Ok(binders)
}

// ── Expression parsing ────────────────────────────────────────────────────────

pub(crate) fn parse_expr(p: &mut Parser) -> Result<Expr, String> {
    parse_arrow_expr(p)
}

/// Parse a single expression from a token slice (used by REPL :check/:eval).
pub fn parse_expr_tokens(tokens: &[Token]) -> Result<Expr, String> {
    let mut p = Parser::new(tokens);
    let e = parse_expr(&mut p)?;
    if !p.is_at_end() {
        return Err(format!("unexpected token after expression: {:?}", p.peek()));
    }
    Ok(e)
}

fn parse_arrow_expr(p: &mut Parser) -> Result<Expr, String> {
    let lhs = parse_app_expr(p)?;
    if matches!(p.peek(), Token::Arrow) {
        p.advance();
        let rhs = parse_arrow_expr(p)?;
        Ok(Expr::Arrow(Box::new(lhs), Box::new(rhs)))
    } else {
        Ok(lhs)
    }
}

fn parse_app_expr(p: &mut Parser) -> Result<Expr, String> {
    let mut head = parse_atom(p)?;
    while is_atom_start(p.peek()) {
        head = Expr::App(Box::new(head), Box::new(parse_atom(p)?));
    }
    Ok(head)
}

fn is_atom_start(t: &Token) -> bool {
    matches!(t,
        Token::Ident(_) | Token::NatLit(_) | Token::LParen |
        Token::KwFun | Token::KwForall | Token::KwLet |
        Token::KwProp | Token::KwType | Token::At |
        Token::Underscore | Token::LAngle |
        Token::KwSorry | Token::KwRfl | Token::KwAssumption |
        Token::KwTrivial | Token::KwContradiction
    )
}

fn parse_atom(p: &mut Parser) -> Result<Expr, String> {
    match p.peek().clone() {
        Token::Ident(s)   => { p.advance(); Ok(Expr::Name(s)) }
        Token::NatLit(n)  => { p.advance(); Ok(Expr::NatLit(n)) }
        Token::Underscore => { p.advance(); Ok(Expr::Hole) }
        Token::KwProp     => { p.advance(); Ok(Expr::Sort(None)) }
        Token::KwType => {
            p.advance();
            if let Token::NatLit(n) = p.peek().clone() {
                p.advance(); Ok(Expr::Sort(Some(n)))
            } else {
                Ok(Expr::Sort(Some(0)))
            }
        }
        Token::LParen => {
            p.advance();
            let e = parse_expr(p)?;
            p.eat(&Token::RParen)?;
            Ok(e)
        }
        Token::KwFun => {
            p.advance();
            let bs = parse_binders_inline(p)?;
            p.eat(&Token::FatArrow)?;
            let body = parse_expr(p)?;
            Ok(bs.into_iter().rev().fold(body, |acc, b| Expr::Fun(b, Box::new(acc))))
        }
        Token::KwForall => {
            p.advance();
            let bs = parse_binders_inline(p)?;
            p.eat(&Token::Comma)?;
            let body = parse_expr(p)?;
            Ok(bs.into_iter().rev().fold(body, |acc, b| Expr::Pi(b, Box::new(acc))))
        }
        Token::KwLet => {
            p.advance();
            let name = p.eat_ident()?;
            let ty = if matches!(p.peek(), Token::Colon) {
                p.advance(); parse_expr(p)?
            } else { Expr::Hole };
            p.eat(&Token::ColonEq)?;
            let val = parse_expr(p)?;
            p.eat(&Token::KwIn)?;
            let body = parse_expr(p)?;
            Ok(Expr::Let(name, Box::new(ty), Box::new(val), Box::new(body)))
        }
        Token::At => {
            p.advance();
            Ok(Expr::Explicit(p.eat_ident()?, Vec::new()))
        }
        Token::LAngle => {
            p.advance();
            let mut args = Vec::new();
            if !matches!(p.peek(), Token::RAngle) {
                args.push(parse_expr(p)?);
                while matches!(p.peek(), Token::Comma) {
                    p.advance();
                    args.push(parse_expr(p)?);
                }
            }
            p.eat(&Token::RAngle)?;
            let mut acc = Expr::Name("⟨⟩".to_string());
            for a in args { acc = Expr::App(Box::new(acc), Box::new(a)); }
            Ok(acc)
        }
        // Tactic keywords that appear as term-proof heads
        Token::KwSorry         => { p.advance(); Ok(Expr::Name("sorry".into())) }
        Token::KwRfl            => { p.advance(); Ok(Expr::Name("rfl".into())) }
        Token::KwAssumption     => { p.advance(); Ok(Expr::Name("assumption".into())) }
        Token::KwTrivial        => { p.advance(); Ok(Expr::Name("trivial".into())) }
        Token::KwContradiction  => { p.advance(); Ok(Expr::Name("contradiction".into())) }
        other => Err(format!("expected expression, found {:?}", other)),
    }
}

fn parse_binders_inline(p: &mut Parser) -> Result<Vec<Binder>, String> {
    let mut binders = Vec::new();
    loop {
        match p.peek() {
            Token::LParen | Token::LBrace => binders.extend(parse_binder_group(p)?),
            Token::Ident(_) => {
                let n = p.eat_ident()?;
                binders.push(Binder::Explicit(n, Box::new(Expr::Hole)));
            }
            _ => break,
        }
    }
    if binders.is_empty() { Err("expected at least one binder".into()) } else { Ok(binders) }
}

// ── Declaration parsing ───────────────────────────────────────────────────────

fn parse_decl(p: &mut Parser) -> Result<SurfaceDecl, String> {
    match p.peek().clone() {
        Token::Hash => {
            p.advance();
            match p.peek().clone() {
                Token::Ident(kw) if kw == "check" => { p.advance(); }
                other => return Err(format!("expected 'check' after '#', found {:?}", other)),
            }
            Ok(SurfaceDecl::CheckCmd(parse_expr(p)?))
        }
        Token::KwDef => {
            p.advance();
            let name = p.eat_ident()?;
            let params = parse_binders(p)?;
            p.eat(&Token::Colon)?;
            let ty = parse_expr(p)?;
            p.eat(&Token::ColonEq)?;
            Ok(SurfaceDecl::Def { name, params, ty, body: parse_expr(p)? })
        }
        Token::KwTheorem => {
            p.advance();
            let name = p.eat_ident()?;
            let params = parse_binders(p)?;
            p.eat(&Token::Colon)?;
            let ty = parse_expr(p)?;
            p.eat(&Token::ColonEq)?;
            Ok(SurfaceDecl::Theorem { name, params, ty, proof: tactics::parse_proof(p)? })
        }
        Token::KwAxiom => {
            p.advance();
            let name = p.eat_ident()?;
            let params = parse_binders(p)?;
            p.eat(&Token::Colon)?;
            Ok(SurfaceDecl::Axiom { name, params, ty: parse_expr(p)? })
        }
        Token::KwInductive => {
            p.advance();
            let name = p.eat_ident()?;
            let params = parse_binders(p)?;
            p.eat(&Token::Colon)?;
            let sort = parse_expr(p)?;
            p.eat(&Token::KwWhere)?;
            let mut ctors = Vec::new();
            while matches!(p.peek(), Token::Pipe) {
                p.advance();
                let ctor_name = p.eat_ident()?;
                p.eat(&Token::Colon)?;
                ctors.push((ctor_name, parse_expr(p)?));
            }
            Ok(SurfaceDecl::Inductive { name, params, sort, ctors })
        }
        Token::KwImport => {
            p.advance();
            match p.peek().clone() {
                Token::Str(path) => { p.advance(); Ok(SurfaceDecl::Import { path }) }
                other => Err(format!("expected string path after 'import', found {:?}", other)),
            }
        }
        other => Err(format!("expected declaration keyword, found {:?}", other)),
    }
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Parse a sequence of top-level declarations from a token slice.
pub fn parse_file(tokens: &[Token]) -> Result<Vec<SurfaceDecl>, String> {
    let mut p = Parser::new(tokens);
    let mut decls = Vec::new();
    while !p.is_at_end() { decls.push(parse_decl(&mut p)?); }
    Ok(decls)
}

/// Parse a bare tactic sequence (without enclosing `by { }`).
pub fn parse_tactic_block(tokens: &[Token]) -> Result<Vec<Tactic>, String> {
    let mut p = Parser::new(tokens);
    tactics::parse_tactic_list(&mut p)
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::lexer::lex;

    fn decls(src: &str) -> Vec<SurfaceDecl> {
        parse_file(&lex(src).unwrap()).unwrap()
    }
    fn tactics(src: &str) -> Vec<Tactic> {
        parse_tactic_block(&lex(src).unwrap()).unwrap()
    }

    #[test] fn axiom_simple() {
        let ds = decls("axiom em : Prop");
        assert!(matches!(&ds[0], SurfaceDecl::Axiom { name, .. } if name == "em"));
    }
    #[test] fn def_identity() {
        let ds = decls("def id (A : Type) (a : A) : A := a");
        match &ds[0] {
            SurfaceDecl::Def { name, params, .. } => {
                assert_eq!(name, "id");
                assert_eq!(params.len(), 2);
            }
            _ => panic!("expected Def"),
        }
    }
    #[test] fn theorem_term_proof() {
        let ds = decls("theorem t : Prop := sorry");
        assert!(matches!(&ds[0], SurfaceDecl::Theorem { proof: Proof::Term(_), .. }));
    }
    #[test] fn theorem_tactic_proof() {
        let ds = decls("theorem t : Prop := by { sorry }");
        assert!(matches!(&ds[0], SurfaceDecl::Theorem { proof: Proof::Tactics(_), .. }));
    }
    #[test] fn inductive_nat() {
        let ds = decls("inductive Nat : Type where | zero : Nat | succ : Nat -> Nat");
        match &ds[0] {
            SurfaceDecl::Inductive { name, ctors, .. } => {
                assert_eq!(name, "Nat");
                assert_eq!(ctors.len(), 2);
            }
            _ => panic!("expected Inductive"),
        }
    }
    #[test] fn check_cmd() {
        let ds = decls("#check Nat.zero");
        assert!(matches!(&ds[0], SurfaceDecl::CheckCmd(Expr::Name(n)) if n == "Nat.zero"));
    }
    #[test] fn arrow_type() {
        let ds = decls("axiom f : Nat -> Nat");
        assert!(matches!(&ds[0], SurfaceDecl::Axiom { ty: Expr::Arrow(..), .. }));
    }
    #[test] fn forall_expr() {
        let ds = decls("axiom f : ∀ (n : Nat), Nat");
        assert!(matches!(&ds[0], SurfaceDecl::Axiom { ty: Expr::Pi(..), .. }));
    }
    #[test] fn tactic_intro_exact() {
        let ts = tactics("intro n; exact n");
        assert_eq!(ts.len(), 2);
        assert!(matches!(&ts[0], Tactic::Intro(ns) if ns[0] == "n"));
        assert!(matches!(&ts[1], Tactic::Exact(Expr::Name(n)) if n == "n"));
    }
    #[test] fn tactic_simp_lemmas() {
        let ts = tactics("simp [Nat.add_comm, h]");
        assert!(matches!(&ts[0], Tactic::Simp(ls) if ls.len() == 2));
    }
    #[test] fn tactic_have() {
        let ts = tactics("have h : Nat := Nat.zero");
        assert!(matches!(&ts[0], Tactic::Have { name, .. } if name == "h"));
    }
    #[test] fn tactic_rewrite_reverse() {
        let ts = tactics("rewrite [← h]");
        assert!(matches!(&ts[0], Tactic::Rewrite { reverse: true, .. }));
    }
    #[test] fn tactic_bullet_focus() {
        let ts = tactics("· exact h");
        assert!(matches!(&ts[0], Tactic::Focus(_)));
    }
    #[test] fn tactic_case() {
        let ts = tactics("case zero => rfl");
        assert!(matches!(&ts[0], Tactic::Case { ctor, body, .. }
            if ctor == "zero" && matches!(body[0], Tactic::Rfl)));
    }
    #[test] fn multi_name_binder() {
        let ds = decls("def swap (n m : Nat) : Nat := n");
        match &ds[0] {
            SurfaceDecl::Def { params, .. } => assert_eq!(params.len(), 2),
            _ => panic!("expected Def"),
        }
    }
    #[test] fn type_universe_level() {
        let ds = decls("axiom big : Type 2");
        assert!(matches!(&ds[0], SurfaceDecl::Axiom { ty: Expr::Sort(Some(2)), .. }));
    }
    #[test] fn anon_ctor() {
        let ds = decls("def p : Unit := ⟨⟩");
        assert!(matches!(&ds[0], SurfaceDecl::Def { .. }));
    }
    #[test] fn empty_file() {
        assert_eq!(decls(""), vec![]);
    }
    #[test] fn eof_without_panic() {
        let toks = lex("def").unwrap();
        assert!(parse_file(&toks).is_err());
    }
}
