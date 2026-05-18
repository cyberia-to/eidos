// ctx — local typing context Γ
// spec: specs/terms.md § context

use crate::{subst::shift, term::Term};

/// One entry in the local context (innermost-first / de Bruijn order).
#[derive(Debug, Clone)]
pub enum CtxEntry {
    /// CTX_VAR(A) — variable of type A
    Var(Term),
    /// CTX_LET(A, v) — local definition x := v : A
    Let(Term, Term),
}

impl CtxEntry {
    /// The declared type of this entry.
    pub fn ty(&self) -> &Term {
        match self {
            CtxEntry::Var(a) | CtxEntry::Let(a, _) => a,
        }
    }
}

/// Local typing context: list of entries, innermost first.
pub type Ctx = Vec<CtxEntry>;

/// Look up the i-th entry (de Bruijn index i) and return it shifted by i+1.
/// shift(i+1) adjusts the entry's free indices for the i+1 binders crossed.
pub fn ctx_lookup(ctx: &Ctx, i: usize) -> Option<CtxEntry> {
    let entry = ctx.get(i)?;
    let n = (i + 1) as u64;
    Some(match entry {
        CtxEntry::Var(a)    => CtxEntry::Var(shift(a, n)),
        CtxEntry::Let(a, v) => CtxEntry::Let(shift(a, n), shift(v, n)),
    })
}

/// Push a variable binder onto the context (innermost = front).
pub fn push_var(ctx: &mut Ctx, ty: Term) {
    ctx.insert(0, CtxEntry::Var(ty));
}

/// Push a let-binding onto the context (innermost = front).
pub fn push_let(ctx: &mut Ctx, ty: Term, val: Term) {
    ctx.insert(0, CtxEntry::Let(ty, val));
}
