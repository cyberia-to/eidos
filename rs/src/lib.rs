// cyber-eidos — CIC proof assistant over the Goldilocks field
//
// trust boundary:
//   trusted  — term, ctx, env, subst, reduce, kernel  (TCB)
//   untrusted — elab, tactic, stdlib, certificate      (shell)

pub mod ctx;
pub mod env;
pub mod kernel;
pub mod reduce;
pub mod subst;
pub mod term;

pub mod certificate;
pub mod elab;
pub mod stdlib;
pub mod surface;
pub mod tactic;
pub mod tactic_ext;

pub use kernel::{check, infer, Error};
pub use term::Term;
