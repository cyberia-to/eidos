// surface — syntax frontend for .ei proof files
// spec: specs/surface.md

pub mod check;
pub mod lexer;
pub mod omega;
pub mod parser;
pub mod strict;
pub mod tactic_runner;
pub(crate) mod tactics;

pub use check::{check_file, check_path, CheckError, DeclKind, DeclResult};
pub use lexer::{lex, Token};
pub use parser::{parse_expr_tokens, parse_file, parse_tactic_block, SurfaceDecl};
pub use strict::{check_strict_path, check_strict_source, CheckedModule};
pub use tactics::{Proof, Tactic};
