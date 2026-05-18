// surface AST — parsed representation of user-written terms
// spec: specs/surface.md § grammar

/// Surface expression
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Variable or global name
    Name(String),
    /// Universe: None=Prop, Some(0)=Type, Some(n)=Type_n
    Sort(Option<u64>),
    /// Application f a (left-associative)
    App(Box<Expr>, Box<Expr>),
    /// Lambda abstraction: fun (x:A) => body
    Fun(Binder, Box<Expr>),
    /// Dependent function type: (x:A) -> B
    Pi(Binder, Box<Expr>),
    /// Non-dependent function type: A -> B (B doesn't reference the binder)
    Arrow(Box<Expr>, Box<Expr>),
    /// Local definition: let x:A := v; body
    Let(String, Box<Expr>, Box<Expr>, Box<Expr>),
    /// Pattern match: target, optional motive, arms
    Match(Box<Expr>, Option<Box<Expr>>, Vec<Arm>),
    /// Hole — elaborator fills by unification
    Hole,
    /// Natural number literal
    NatLit(u64),
    /// Explicit application @name args (skips implicit insertion)
    Explicit(String, Vec<Expr>),
}

/// Binder — describes a single bound variable
#[derive(Debug, Clone, PartialEq)]
pub enum Binder {
    Explicit(String, Box<Expr>),
    Implicit(String, Box<Expr>),
    Instance(String, Box<Expr>),
}

impl Binder {
    pub fn name(&self) -> &str {
        match self {
            Binder::Explicit(n, _) | Binder::Implicit(n, _) | Binder::Instance(n, _) => n,
        }
    }
    pub fn ty(&self) -> &Expr {
        match self {
            Binder::Explicit(_, t) | Binder::Implicit(_, t) | Binder::Instance(_, t) => t,
        }
    }
    pub fn is_implicit(&self) -> bool {
        matches!(self, Binder::Implicit(..) | Binder::Instance(..))
    }
}

/// Match arm
#[derive(Debug, Clone, PartialEq)]
pub struct Arm {
    pub pattern: Pattern,
    pub body: Box<Expr>,
}

/// Pattern in a match arm
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Wildcard,
    Name(String),
    /// Constructor pattern: ctor name + field variable names
    App(String, Vec<String>),
}

/// Top-level declaration
#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    Def {
        name: String,
        params: Vec<Binder>,
        ty: Box<Expr>,
        body: Box<Expr>,
    },
    Theorem {
        name: String,
        params: Vec<Binder>,
        ty: Box<Expr>,
        body: Box<Expr>,
    },
    Axiom {
        name: String,
        ty: Box<Expr>,
    },
    Inductive {
        name: String,
        params: Vec<Binder>,
        sort: Box<Expr>,
        /// (ctor_name, ctor_type_expr)
        ctors: Vec<(String, Box<Expr>)>,
    },
}
