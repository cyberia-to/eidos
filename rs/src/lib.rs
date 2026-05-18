// cyber-eidos — CIC proof assistant over the Goldilocks field
//
// trust boundary:
//   trusted  — term, ctx, env, subst, reduce, kernel  (TCB)
//   untrusted — elab, tactic, stdlib, certificate      (shell)

pub mod term;
pub mod ctx;
pub mod env;
pub mod subst;
pub mod reduce;
pub mod kernel;

pub mod elab;
pub mod tactic;
pub mod tactic_ext;
pub mod stdlib;
pub mod certificate;
pub mod surface;

pub use kernel::{check, infer, Error};
pub use term::Term;
