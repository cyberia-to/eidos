// term — CIC term grammar and noun encoding
// spec: specs/terms.md

/// Universe level. PROP = 0, TYPE_0 = 1, TYPE_1 = 2, ...
pub type Level = u64;

/// Constructor index (zero-based) within an inductive type.
pub type CtorIdx = u64;

/// Inductive type identifier: hemera hash of the declaration noun.
pub type IndId = u64;

/// De Bruijn index: 0 = innermost binder.
pub type Idx = u64;

/// Elaboration-only metavariable id.
pub type MetaId = u64;

/// CIC term — ten kernel constructors plus one elaboration-only Meta node.
///
/// `Meta(id)` is used exclusively during elaboration; the kernel rejects any
/// term containing Meta nodes. Call `elab::meta::zonk(metas, term)` to
/// substitute all solved metas before passing a term to the kernel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// VAR(i) — de Bruijn index
    Var(Idx),
    /// SORT(u) — universe at level u
    Sort(Level),
    /// PI(A, B) — dependent function type Πx:A. B
    Pi(Box<Term>, Box<Term>),
    /// LAM(A, t) — abstraction λx:A. t
    Lam(Box<Term>, Box<Term>),
    /// APP(f, a) — application f a
    App(Box<Term>, Box<Term>),
    /// LET(A, v, b) — local definition let x:=v:A in b
    Let(Box<Term>, Box<Term>, Box<Term>),
    /// IND(id, params) — inductive type applied to parameters
    Ind(IndId, Vec<Term>),
    /// CTOR(id, k, args) — k-th constructor of inductive id
    Ctor(IndId, CtorIdx, Vec<Term>),
    /// ELIM(id, motive, cases, target) — eliminator for inductive id
    Elim(IndId, Box<Term>, Vec<Term>, Box<Term>),
    /// EQ_SUBST(p, h, pf_a) — Leibniz transport / J-rule primitive.
    /// h : Eq A a b,  pf_a : p(a),  result type : p(b).
    /// Reduces to pf_a when h is refl.
    EqSubst(Box<Term>, Box<Term>, Box<Term>),
    /// CONST(id) — opaque declared constant (axiom or transparent def).
    /// Axioms have no body; whnf returns them as-is.
    /// Defs have a body in Env::consts; whnf unfolds them.
    Const(u64),
    /// META(id) — unsolved metavariable (elaboration only, not a kernel term)
    Meta(MetaId),
}

impl Term {
    pub fn prop()  -> Self { Term::Sort(0) }
    pub fn type0() -> Self { Term::Sort(1) }

    /// prop_max: universe level arithmetic respecting PROP impredicativity.
    /// prop_max(0, v) = 0, prop_max(u, 0) = 0, prop_max(u, v) = max(u, v).
    pub fn prop_max(u: Level, v: Level) -> Level {
        if u == 0 || v == 0 { 0 } else { u.max(v) }
    }

    /// True if the term contains no Meta nodes (safe for kernel).
    pub fn is_kernel_term(&self) -> bool {
        match self {
            Term::Meta(_) => false,
            Term::Var(_) | Term::Sort(_) | Term::Const(_) => true,
            Term::Pi(a, b) | Term::Lam(a, b) | Term::App(a, b) =>
                a.is_kernel_term() && b.is_kernel_term(),
            Term::Let(a, v, b) =>
                a.is_kernel_term() && v.is_kernel_term() && b.is_kernel_term(),
            Term::Ind(_, ps) => ps.iter().all(|p| p.is_kernel_term()),
            Term::Ctor(_, _, args) => args.iter().all(|a| a.is_kernel_term()),
            Term::Elim(_, m, cs, tg) =>
                m.is_kernel_term()
                && cs.iter().all(|c| c.is_kernel_term())
                && tg.is_kernel_term(),
            Term::EqSubst(p, h, pf) =>
                p.is_kernel_term() && h.is_kernel_term() && pf.is_kernel_term(),
        }
    }
}
