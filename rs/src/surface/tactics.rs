// surface/tactics.rs — tactic AST and tactic parser
// Private submodule of surface::parser.
//
// parse_expr / Parser are imported from the parent module via super.

use crate::elab::ast::Expr;
use crate::surface::lexer::Token;
use crate::surface::parser::{Parser, parse_expr};

// ── Tactic AST ────────────────────────────────────────────────────────────────

/// A proof body: either a direct term or a `by { ... }` tactic block.
#[derive(Debug, Clone, PartialEq)]
pub enum Proof {
    Term(Box<Expr>),
    Tactics(Vec<Tactic>),
}

/// Tactic language recognised by the surface parser.
#[derive(Debug, Clone, PartialEq)]
pub enum Tactic {
    Intro(Vec<String>),
    Exact(Expr),
    Apply(Expr),
    Induction(String),
    Cases(String),
    Rfl,
    Assumption,
    Simp(Vec<Expr>),
    Omega,
    Decide,
    Have { name: String, ty: Expr, proof: Box<Proof> },
    Rewrite { expr: Expr, reverse: bool },
    Contradiction,
    Trivial,
    Sorry,
    Show(Expr),
    Clear(String),
    Revert(String),
    Case { ctor: String, vars: Vec<String>, body: Vec<Tactic> },
    Focus(Vec<Tactic>),   // · tactic block
    Seq(Vec<Tactic>),     // semicolon-separated sequence
}

// ── Proof ─────────────────────────────────────────────────────────────────────

pub(crate) fn parse_proof(p: &mut Parser) -> Result<Proof, String> {
    if matches!(p.peek(), Token::KwBy) {
        p.advance();
        p.eat(&Token::LBrace)?;
        let ts = parse_tactic_list(p)?;
        p.eat(&Token::RBrace)?;
        Ok(Proof::Tactics(ts))
    } else {
        Ok(Proof::Term(Box::new(parse_expr(p)?)))
    }
}

// ── Tactic lists ──────────────────────────────────────────────────────────────

/// Parse zero or more tactics, stopping at `}` or EOF.
/// Tactics may be separated by `;`.
pub(crate) fn parse_tactic_list(p: &mut Parser) -> Result<Vec<Tactic>, String> {
    let mut out = Vec::new();
    loop {
        while matches!(p.peek(), Token::Semicolon) { p.advance(); }
        if matches!(p.peek(), Token::RBrace | Token::Eof) { break; }
        if matches!(p.peek(), Token::Bullet) {
            p.advance();
            out.push(Tactic::Focus(parse_focus_body(p)?));
            continue;
        }
        out.push(parse_one_tactic(p)?);
        if matches!(p.peek(), Token::Semicolon) { p.advance(); }
    }
    Ok(out)
}

/// Body of a `·` bullet: tactics until next bullet, `}`, or EOF.
fn parse_focus_body(p: &mut Parser) -> Result<Vec<Tactic>, String> {
    let mut out = Vec::new();
    loop {
        while matches!(p.peek(), Token::Semicolon) { p.advance(); }
        if matches!(p.peek(), Token::Bullet | Token::RBrace | Token::Eof) { break; }
        out.push(parse_one_tactic(p)?);
        if matches!(p.peek(), Token::Semicolon) { p.advance(); }
    }
    Ok(out)
}

// ── Single tactic ─────────────────────────────────────────────────────────────

pub(crate) fn parse_one_tactic(p: &mut Parser) -> Result<Tactic, String> {
    match p.peek().clone() {
        Token::KwIntro => {
            p.advance();
            let mut names = vec![p.eat_ident()?];
            while let Token::Ident(_) = p.peek() { names.push(p.eat_ident()?); }
            Ok(Tactic::Intro(names))
        }
        Token::KwExact      => { p.advance(); Ok(Tactic::Exact(parse_expr(p)?)) }
        Token::KwApply      => { p.advance(); Ok(Tactic::Apply(parse_expr(p)?)) }
        Token::KwInduction  => { p.advance(); Ok(Tactic::Induction(p.eat_ident()?)) }
        Token::KwCases      => { p.advance(); Ok(Tactic::Cases(p.eat_ident()?)) }
        Token::KwRfl        => { p.advance(); Ok(Tactic::Rfl) }
        Token::KwAssumption => { p.advance(); Ok(Tactic::Assumption) }
        Token::KwOmega      => { p.advance(); Ok(Tactic::Omega) }
        Token::KwDecide     => { p.advance(); Ok(Tactic::Decide) }
        Token::KwContradiction => { p.advance(); Ok(Tactic::Contradiction) }
        Token::KwTrivial    => { p.advance(); Ok(Tactic::Trivial) }
        Token::KwSorry      => { p.advance(); Ok(Tactic::Sorry) }
        Token::KwShow       => { p.advance(); Ok(Tactic::Show(parse_expr(p)?)) }
        Token::KwClear      => { p.advance(); Ok(Tactic::Clear(p.eat_ident()?)) }
        Token::KwRevert     => { p.advance(); Ok(Tactic::Revert(p.eat_ident()?)) }

        Token::KwSimp => {
            p.advance();
            let mut lemmas = Vec::new();
            if matches!(p.peek(), Token::LBracket) {
                p.advance();
                if !matches!(p.peek(), Token::RBracket) {
                    lemmas.push(parse_expr(p)?);
                    while matches!(p.peek(), Token::Comma) {
                        p.advance();
                        lemmas.push(parse_expr(p)?);
                    }
                }
                p.eat(&Token::RBracket)?;
            }
            Ok(Tactic::Simp(lemmas))
        }

        Token::KwHave => {
            p.advance();
            let name = p.eat_ident()?;
            p.eat(&Token::Colon)?;
            let ty = parse_expr(p)?;
            p.eat(&Token::ColonEq)?;
            Ok(Tactic::Have { name, ty, proof: Box::new(parse_proof(p)?) })
        }

        Token::KwRewrite => {
            p.advance();
            p.eat(&Token::LBracket)?;
            let reverse = if matches!(p.peek(), Token::BackArrow) {
                p.advance(); true
            } else { false };
            let expr = parse_expr(p)?;
            p.eat(&Token::RBracket)?;
            Ok(Tactic::Rewrite { expr, reverse })
        }

        Token::KwCase => {
            p.advance();
            let ctor = p.eat_ident()?;
            let mut vars = Vec::new();
            while let Token::Ident(_) = p.peek() { vars.push(p.eat_ident()?); }
            p.eat(&Token::FatArrow)?;
            let mut body = Vec::new();
            loop {
                while matches!(p.peek(), Token::Semicolon) { p.advance(); }
                if matches!(p.peek(),
                    Token::KwCase | Token::Bullet | Token::RBrace | Token::Eof
                ) { break; }
                body.push(parse_one_tactic(p)?);
                if matches!(p.peek(), Token::Semicolon) { p.advance(); }
            }
            Ok(Tactic::Case { ctor, vars, body })
        }

        other => Err(format!("expected tactic, found {:?}", other)),
    }
}
