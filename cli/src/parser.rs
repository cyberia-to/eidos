// parser — minimal surface expression parser for the eval CLI command
// Handles: nat literals, identifiers (including dotted), application, parentheses.

use cyber_eidos::elab::ast::Expr;

/// Parse a surface expression string.
pub fn parse(src: &str) -> Result<Expr, String> {
    let toks = tokenize(src);
    let (e, rest) = parse_app(&toks)?;
    if !rest.is_empty() {
        return Err(format!("unexpected token after expression: {:?}", rest[0]));
    }
    Ok(e)
}

// ── Tokens ───────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
enum Tok {
    Nat(u64),
    Ident(String),
    LParen,
    RParen,
}

fn tokenize(s: &str) -> Vec<Tok> {
    let mut toks = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\n' | '\r' => { chars.next(); }
            '(' => { chars.next(); toks.push(Tok::LParen); }
            ')' => { chars.next(); toks.push(Tok::RParen); }
            '0'..='9' => {
                let mut n = 0u64;
                while let Some(&d @ '0'..='9') = chars.peek() {
                    n = n.saturating_mul(10).saturating_add(d as u64 - '0' as u64);
                    chars.next();
                }
                toks.push(Tok::Nat(n));
            }
            _ if c.is_alphabetic() || c == '_' => {
                let mut name = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch.is_alphanumeric() || ch == '_' || ch == '.' {
                        name.push(ch);
                        chars.next();
                    } else {
                        break;
                    }
                }
                toks.push(Tok::Ident(name));
            }
            _ => { chars.next(); }
        }
    }
    toks
}

// ── Grammar (recursive descent) ───────────────────────────────────────────────
//
//   app  ::= atom atom*
//   atom ::= NAT | IDENT | '(' app ')'

fn parse_atom<'a>(toks: &'a [Tok]) -> Result<(Expr, &'a [Tok]), String> {
    match toks.first() {
        Some(Tok::Nat(n)) => Ok((Expr::NatLit(*n), &toks[1..])),

        Some(Tok::Ident(s)) => {
            let expr = match s.as_str() {
                "Prop" => Expr::Sort(None),
                "Type" => Expr::Sort(Some(0)),
                "_"    => Expr::Hole,
                _      => Expr::Name(s.clone()),
            };
            Ok((expr, &toks[1..]))
        }

        Some(Tok::LParen) => {
            let (e, rest) = parse_app(&toks[1..])?;
            match rest.first() {
                Some(Tok::RParen) => Ok((e, &rest[1..])),
                Some(t)  => Err(format!("expected ')' but got {:?}", t)),
                None     => Err("expected ')' but reached end of input".into()),
            }
        }

        Some(Tok::RParen) => Err("unexpected ')'".into()),
        None => Err("unexpected end of input".into()),
    }
}

fn parse_app<'a>(toks: &'a [Tok]) -> Result<(Expr, &'a [Tok]), String> {
    let (mut e, mut rest) = parse_atom(toks)?;
    loop {
        match rest.first() {
            Some(Tok::Nat(_)) | Some(Tok::Ident(_)) | Some(Tok::LParen) => {
                let (a, rest2) = parse_atom(rest)?;
                e = Expr::App(Box::new(e), Box::new(a));
                rest = rest2;
            }
            _ => break,
        }
    }
    Ok((e, rest))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_nat_lit() {
        assert_eq!(parse("42"), Ok(Expr::NatLit(42)));
    }

    #[test]
    fn parse_name() {
        assert_eq!(parse("Nat"), Ok(Expr::Name("Nat".into())));
    }

    #[test]
    fn parse_dotted() {
        assert_eq!(parse("Nat.zero"), Ok(Expr::Name("Nat.zero".into())));
    }

    #[test]
    fn parse_application() {
        assert_eq!(
            parse("Nat.next 0"),
            Ok(Expr::App(
                Box::new(Expr::Name("Nat.next".into())),
                Box::new(Expr::NatLit(0)),
            ))
        );
    }

    #[test]
    fn parse_parens() {
        assert_eq!(
            parse("(Nat.next (Nat.next 0))"),
            Ok(Expr::App(
                Box::new(Expr::Name("Nat.next".into())),
                Box::new(Expr::App(
                    Box::new(Expr::Name("Nat.next".into())),
                    Box::new(Expr::NatLit(0)),
                )),
            ))
        );
    }

    #[test]
    fn parse_prop_type() {
        assert_eq!(parse("Prop"), Ok(Expr::Sort(None)));
        assert_eq!(parse("Type"), Ok(Expr::Sort(Some(0))));
    }

    #[test]
    fn parse_hole() {
        assert_eq!(parse("_"), Ok(Expr::Hole));
    }
}
