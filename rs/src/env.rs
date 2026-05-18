// env — global environment Σ (inductive descriptors + constant declarations)
// spec: specs/terms.md § global environment, specs/kernel.md § instantiate

use crate::term::{IndId, Level, Term};
use std::collections::HashMap;

/// Descriptor for one inductive type.
/// Encoding: IND_DESC(arity, sort, param_tel, constructors)
#[derive(Debug, Clone)]
pub struct IndDesc {
    /// Number of parameters.
    pub arity: u64,
    /// Universe level (0 = Prop, 1 = Type₀, …).
    pub sort: Level,
    /// PI-telescope of length `arity` encoding parameter types: PI(P₀, PI(P₁, … _)).
    pub param_tel: Term,
    /// Constructor types — one nested PI term per constructor.
    /// Each term has `arity` outermost free variables (VAR(arity-1)…VAR(0)) for parameters,
    /// followed by PI-binders for the constructor's own fields, ending in the return type.
    pub constructors: Vec<Term>,
}

/// Descriptor for a declared constant (axiom or transparent definition).
#[derive(Debug, Clone)]
pub struct ConstDecl {
    /// The type of the constant.
    pub ty: Term,
    /// Body for transparent defs; None for axioms (opaque).
    pub body: Option<Term>,
}

/// Global environment: maps IndId → IndDesc and const id → ConstDecl.
#[derive(Debug, Default, Clone)]
pub struct Env {
    inds: HashMap<IndId, IndDesc>,
    consts: HashMap<u64, ConstDecl>,
}

impl Env {
    pub fn new() -> Self { Self::default() }

    pub fn insert(&mut self, id: IndId, desc: IndDesc) {
        self.inds.insert(id, desc);
    }

    pub fn lookup(&self, id: IndId) -> Option<&IndDesc> {
        self.inds.get(&id)
    }

    pub fn insert_const(&mut self, id: u64, decl: ConstDecl) {
        self.consts.insert(id, decl);
    }

    pub fn lookup_const(&self, id: u64) -> Option<&ConstDecl> {
        self.consts.get(&id)
    }
}
