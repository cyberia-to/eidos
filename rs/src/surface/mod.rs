// surface — syntax frontend for .ei proof files
// spec: specs/surface.md

pub mod lexer;
pub(crate) mod tactics;
pub mod parser;
pub mod omega;
pub mod tactic_runner;
pub mod check;

pub use lexer::{lex, Token};
pub use parser::{parse_file, parse_tactic_block, parse_expr_tokens, SurfaceDecl};
pub use tactics::{Proof, Tactic};
pub use check::{check_file, check_path, CheckError, DeclKind, DeclResult};
