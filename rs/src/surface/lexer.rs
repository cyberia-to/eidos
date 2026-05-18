// surface/lexer.rs — tokenizer for .ei proof files
// spec: specs/surface.md § lexer
//
// Produces Vec<Token> from a UTF-8 source string.
// All input is consumed; line comments (--) are skipped.

/// All surface tokens.
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // ── Keywords ────────────────────────────────────────────────────────────
    KwDef,
    KwTheorem,
    KwAxiom,
    KwInductive,
    KwWhere,
    KwWith,
    KwBy,
    KwFun,
    KwForall,
    KwLet,
    KwIn,
    KwHave,
    KwMatch,
    // Tactics
    KwIntro,
    KwExact,
    KwApply,
    KwInduction,
    KwCases,
    KwRfl,
    KwAssumption,
    KwSimp,
    KwOmega,
    KwDecide,
    KwRewrite,
    KwContradiction,
    KwTrivial,
    KwSorry,
    KwCase,
    KwShow,
    KwClear,
    KwRevert,
    KwImport,
    // Universes
    KwProp,
    KwType,
    // ── Punctuation ─────────────────────────────────────────────────────────
    LParen,     // (
    RParen,     // )
    LBrace,     // {
    RBrace,     // }
    LBracket,   // [
    RBracket,   // ]
    LAngle,     // ⟨
    RAngle,     // ⟩
    Colon,      // :
    ColonEq,    // :=
    Arrow,      // -> or → (U+2192)
    FatArrow,   // =>
    BackArrow,  // ← (U+2190)
    Comma,      // ,
    Semicolon,  // ;
    Pipe,       // |
    Dot,        // . (standalone)
    Bullet,     // · (U+00B7)
    Hash,       // #
    At,         // @
    Underscore, // _
    // ── Literals / names ────────────────────────────────────────────────────
    Ident(String),   // identifier, possibly dotted: Nat.zero
    NatLit(u64),     // sequence of ASCII digits
    Str(String),     // "..." string literal (used for import paths)
    // ── Sentinel ────────────────────────────────────────────────────────────
    Eof,
}

// ── Keyword table ─────────────────────────────────────────────────────────────

fn keyword(s: &str) -> Option<Token> {
    match s {
        "def"          => Some(Token::KwDef),
        "theorem"      => Some(Token::KwTheorem),
        "axiom"        => Some(Token::KwAxiom),
        "inductive"    => Some(Token::KwInductive),
        "where"        => Some(Token::KwWhere),
        "with"         => Some(Token::KwWith),
        "by"           => Some(Token::KwBy),
        "fun"          => Some(Token::KwFun),
        "forall"       => Some(Token::KwForall),
        "let"          => Some(Token::KwLet),
        "in"           => Some(Token::KwIn),
        "have"         => Some(Token::KwHave),
        "match"        => Some(Token::KwMatch),
        "intro"        => Some(Token::KwIntro),
        "exact"        => Some(Token::KwExact),
        "apply"        => Some(Token::KwApply),
        "induction"    => Some(Token::KwInduction),
        "cases"        => Some(Token::KwCases),
        "rfl"          => Some(Token::KwRfl),
        "assumption"   => Some(Token::KwAssumption),
        "simp"         => Some(Token::KwSimp),
        "omega"        => Some(Token::KwOmega),
        "decide"       => Some(Token::KwDecide),
        "rewrite"      => Some(Token::KwRewrite),
        "contradiction"=> Some(Token::KwContradiction),
        "trivial"      => Some(Token::KwTrivial),
        "sorry"        => Some(Token::KwSorry),
        "case"         => Some(Token::KwCase),
        "show"         => Some(Token::KwShow),
        "clear"        => Some(Token::KwClear),
        "revert"       => Some(Token::KwRevert),
        "Prop"         => Some(Token::KwProp),
        "Type"         => Some(Token::KwType),
        "import"       => Some(Token::KwImport),
        _              => None,
    }
}

// ── Lexer state ───────────────────────────────────────────────────────────────

struct Lexer<'a> {
    src: &'a str,
    pos: usize, // byte offset
}

impl<'a> Lexer<'a> {
    fn new(src: &'a str) -> Self { Lexer { src, pos: 0 } }

    fn remaining(&self) -> &str { &self.src[self.pos..] }

    fn peek_char(&self) -> Option<char> {
        self.remaining().chars().next()
    }

    fn advance_char(&mut self) -> Option<char> {
        let c = self.peek_char()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    fn starts_with(&self, pat: &str) -> bool {
        self.remaining().starts_with(pat)
    }

    /// Skip ASCII whitespace.
    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek_char() {
            if c.is_whitespace() { self.advance_char(); } else { break; }
        }
    }

    /// Skip a `--` line comment through end-of-line.
    fn skip_line_comment(&mut self) {
        while let Some(c) = self.advance_char() {
            if c == '\n' { break; }
        }
    }

    /// Skip whitespace and comments until we reach a token or EOF.
    fn skip_trivia(&mut self) {
        loop {
            self.skip_whitespace();
            if self.starts_with("--") {
                self.skip_line_comment();
            } else {
                break;
            }
        }
    }

    /// Lex a dotted identifier: `[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*`
    fn lex_ident(&mut self, first: char) -> Token {
        let mut buf = String::new();
        buf.push(first);

        // consume the rest of the first segment
        loop {
            match self.peek_char() {
                Some(c) if c.is_alphanumeric() || c == '_' || c == '\'' => {
                    buf.push(c);
                    self.advance_char();
                }
                _ => break,
            }
        }

        // extend with dot-separated segments (Nat.succ, List.nil, etc.)
        loop {
            // look ahead: dot followed by an identifier start
            let rem = self.remaining();
            let mut chars = rem.chars();
            match (chars.next(), chars.next()) {
                (Some('.'), Some(c2)) if c2.is_alphabetic() || c2 == '_' => {
                    // consume the dot
                    self.advance_char();
                    buf.push('.');
                    // consume segment
                    while let Some(c) = self.peek_char() {
                        if c.is_alphanumeric() || c == '_' || c == '\'' {
                            buf.push(c);
                            self.advance_char();
                        } else {
                            break;
                        }
                    }
                }
                _ => break,
            }
        }

        keyword(&buf).unwrap_or(Token::Ident(buf))
    }

    /// Lex a decimal integer literal.
    fn lex_nat(&mut self, first: char) -> Result<Token, String> {
        let mut buf = String::new();
        buf.push(first);
        while let Some(c) = self.peek_char() {
            if c.is_ascii_digit() { buf.push(c); self.advance_char(); } else { break; }
        }
        buf.parse::<u64>()
            .map(Token::NatLit)
            .map_err(|_| format!("integer literal overflow: {buf}"))
    }

    fn next_token(&mut self) -> Result<Token, String> {
        self.skip_trivia();

        let c = match self.peek_char() {
            None    => return Ok(Token::Eof),
            Some(c) => c,
        };
        self.advance_char(); // consume c

        match c {
            // ── Multi-char punctuation ──────────────────────────────────────
            ':' => {
                if self.starts_with("=") { self.advance_char(); Ok(Token::ColonEq) }
                else { Ok(Token::Colon) }
            }
            '-' => {
                if self.starts_with(">") { self.advance_char(); Ok(Token::Arrow) }
                else {
                    Err(format!("unexpected character '-' (did you mean '->'?)"))
                }
            }
            '=' => {
                if self.starts_with(">") { self.advance_char(); Ok(Token::FatArrow) }
                else { Err(format!("unexpected '=' (did you mean '=>' or ':='?)")) }
            }
            // ── Single-char ASCII ───────────────────────────────────────────
            '(' => Ok(Token::LParen),
            ')' => Ok(Token::RParen),
            '{' => Ok(Token::LBrace),
            '}' => Ok(Token::RBrace),
            '[' => Ok(Token::LBracket),
            ']' => Ok(Token::RBracket),
            ',' => Ok(Token::Comma),
            ';' => Ok(Token::Semicolon),
            '|' => Ok(Token::Pipe),
            '.' => Ok(Token::Dot),
            '#' => Ok(Token::Hash),
            '@' => Ok(Token::At),
            '_' => {
                // distinguish bare underscore from identifier starting with _
                match self.peek_char() {
                    Some(c2) if c2.is_alphanumeric() || c2 == '_' => {
                        let tok = self.lex_ident('_');
                        Ok(tok)
                    }
                    _ => Ok(Token::Underscore),
                }
            }
            // ── Unicode punctuation ─────────────────────────────────────────
            '∀' => Ok(Token::KwForall),   // U+2200
            'λ' => Ok(Token::KwFun),      // U+03BB
            '→' => Ok(Token::Arrow),      // U+2192
            '←' => Ok(Token::BackArrow),  // U+2190
            '·' => Ok(Token::Bullet),     // U+00B7
            '⟨' => Ok(Token::LAngle),     // U+27E8
            '⟩' => Ok(Token::RAngle),     // U+27E9
            // ── Identifiers ─────────────────────────────────────────────────
            c if c.is_alphabetic() => Ok(self.lex_ident(c)),
            // ── Numeric literals ────────────────────────────────────────────
            c if c.is_ascii_digit() => self.lex_nat(c),
            // ── String literals ─────────────────────────────────────────────
            '"' => {
                let mut buf = String::new();
                loop {
                    match self.advance_char() {
                        Some('"') => break,
                        Some(c)   => buf.push(c),
                        None      => return Err("unterminated string literal".into()),
                    }
                }
                Ok(Token::Str(buf))
            }
            other => Err(format!("unexpected character: {:?} (U+{:04X})", other, other as u32)),
        }
    }
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Tokenize `src` into a `Vec<Token>`.
/// The last element is always `Token::Eof`.
/// Returns `Err(message)` on the first unrecognised character.
pub fn lex(src: &str) -> Result<Vec<Token>, String> {
    let mut lexer = Lexer::new(src);
    let mut tokens = Vec::new();
    loop {
        let tok = lexer.next_token()?;
        let is_eof = tok == Token::Eof;
        tokens.push(tok);
        if is_eof { break; }
    }
    Ok(tokens)
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(src: &str) -> Vec<Token> { lex(src).unwrap() }

    #[test]
    fn empty() {
        assert_eq!(toks(""), vec![Token::Eof]);
    }

    #[test]
    fn comment_only() {
        assert_eq!(toks("-- hello world"), vec![Token::Eof]);
    }

    #[test]
    fn keywords() {
        let ts = toks("def theorem axiom inductive");
        assert_eq!(ts[0], Token::KwDef);
        assert_eq!(ts[1], Token::KwTheorem);
        assert_eq!(ts[2], Token::KwAxiom);
        assert_eq!(ts[3], Token::KwInductive);
    }

    #[test]
    fn dotted_ident() {
        let ts = toks("Nat.zero");
        assert_eq!(ts[0], Token::Ident("Nat.zero".into()));
    }

    #[test]
    fn colon_eq() {
        let ts = toks(":=");
        assert_eq!(ts[0], Token::ColonEq);
    }

    #[test]
    fn arrows() {
        let ts = toks("-> => ← →");
        assert_eq!(ts[0], Token::Arrow);
        assert_eq!(ts[1], Token::FatArrow);
        assert_eq!(ts[2], Token::BackArrow);
        assert_eq!(ts[3], Token::Arrow);
    }

    #[test]
    fn unicode_punct() {
        let ts = toks("∀ λ · ⟨ ⟩");
        assert_eq!(ts[0], Token::KwForall);
        assert_eq!(ts[1], Token::KwFun);
        assert_eq!(ts[2], Token::Bullet);
        assert_eq!(ts[3], Token::LAngle);
        assert_eq!(ts[4], Token::RAngle);
    }

    #[test]
    fn nat_lit() {
        let ts = toks("42");
        assert_eq!(ts[0], Token::NatLit(42));
    }

    #[test]
    fn prop_type() {
        let ts = toks("Prop Type Type 3");
        assert_eq!(ts[0], Token::KwProp);
        assert_eq!(ts[1], Token::KwType);
        assert_eq!(ts[2], Token::KwType);
        assert_eq!(ts[3], Token::NatLit(3));
    }

    #[test]
    fn hash_check() {
        let ts = toks("#check");
        assert_eq!(ts[0], Token::Hash);
        assert_eq!(ts[1], Token::Ident("check".into()));
    }

    #[test]
    fn unknown_char_errors() {
        assert!(lex("$").is_err());
    }
}
