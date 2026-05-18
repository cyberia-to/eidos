// meta — metavariable context and first-order unification
// spec: specs/surface.md § implicit arguments / unification

use std::collections::HashMap;
use crate::{ctx::Ctx, env::Env, reduce::def_eq, term::{MetaId, Term}};

/// Elaboration errors (separate from kernel errors).
#[derive(Debug, Clone, PartialEq)]
pub enum ElabError {
    UnknownName(String),
    ExpectedSort(Term),
    ExpectedPi(Term),
    ExpectedInd(Term),
    UnsolvedMeta(MetaId),
    OccursCheck(MetaId),
    TypeMismatch(Term, Term),
    PositivityViolation(String),
    KernelRejection(crate::kernel::Error),
    WrongArgCount { ctor: String, expected: usize, got: usize },
    UnknownConstructor(String),
    CaseMismatch { expected: usize, got: usize },
    MissingArmBody,
}

impl From<crate::kernel::Error> for ElabError {
    fn from(e: crate::kernel::Error) -> Self { ElabError::KernelRejection(e) }
}

/// Metavariable context: tracks fresh meta IDs and assignments.
#[derive(Debug)]
pub struct MetaCtx {
    next_id: MetaId,
    pub assignments: HashMap<MetaId, Term>,
}

impl MetaCtx {
    pub fn new() -> Self { MetaCtx { next_id: 0, assignments: HashMap::new() } }

    /// Create a fresh unresolved metavariable.
    pub fn fresh(&mut self) -> Term {
        let id = self.next_id;
        self.next_id += 1;
        Term::Meta(id)
    }

    /// Substitute all solved metas in t (zonk).
    pub fn zonk(&self, t: &Term) -> Term {
        match t {
            Term::Var(_) | Term::Sort(_) | Term::Const(_) => t.clone(),
            Term::Pi(a, b)     => Term::Pi(Box::new(self.zonk(a)), Box::new(self.zonk(b))),
            Term::Lam(a, b)    => Term::Lam(Box::new(self.zonk(a)), Box::new(self.zonk(b))),
            Term::App(f, a)    => Term::App(Box::new(self.zonk(f)), Box::new(self.zonk(a))),
            Term::Let(a, v, b) => Term::Let(
                Box::new(self.zonk(a)),
                Box::new(self.zonk(v)),
                Box::new(self.zonk(b)),
            ),
            Term::Ind(id, ps)  =>
                Term::Ind(*id, ps.iter().map(|p| self.zonk(p)).collect()),
            Term::Ctor(id, k, args) =>
                Term::Ctor(*id, *k, args.iter().map(|a| self.zonk(a)).collect()),
            Term::Elim(id, m, cs, tg) => Term::Elim(
                *id,
                Box::new(self.zonk(m)),
                cs.iter().map(|c| self.zonk(c)).collect(),
                Box::new(self.zonk(tg)),
            ),
            Term::EqSubst(p, h, pf) => Term::EqSubst(
                Box::new(self.zonk(p)),
                Box::new(self.zonk(h)),
                Box::new(self.zonk(pf)),
            ),
            Term::Meta(id) => match self.assignments.get(id) {
                Some(v) => self.zonk(v),
                None    => t.clone(),
            },
        }
    }

    /// First-order unification: assign ?m := t or verify def_eq.
    pub fn unify(
        &mut self,
        env: &Env,
        ctx: &Ctx,
        t: &Term,
        s: &Term,
    ) -> Result<(), ElabError> {
        let t = self.zonk(t);
        let s = self.zonk(s);
        match (&t, &s) {
            (Term::Meta(i), _) => {
                let i = *i;
                if occurs(i, &s) { return Err(ElabError::OccursCheck(i)); }
                self.assignments.insert(i, s);
                Ok(())
            }
            (_, Term::Meta(j)) => {
                let j = *j;
                if occurs(j, &t) { return Err(ElabError::OccursCheck(j)); }
                self.assignments.insert(j, t);
                Ok(())
            }
            _ => {
                if def_eq(env, ctx, &t, &s) { Ok(()) }
                else { Err(ElabError::TypeMismatch(t, s)) }
            }
        }
    }
}

fn occurs(id: MetaId, t: &Term) -> bool {
    match t {
        Term::Meta(j)         => *j == id,
        Term::Var(_) | Term::Sort(_) | Term::Const(_) => false,
        Term::Pi(a, b) | Term::Lam(a, b) | Term::App(a, b) =>
            occurs(id, a) || occurs(id, b),
        Term::Let(a, v, b)    =>
            occurs(id, a) || occurs(id, v) || occurs(id, b),
        Term::Ind(_, ps)      => ps.iter().any(|p| occurs(id, p)),
        Term::Ctor(_, _, args) => args.iter().any(|a| occurs(id, a)),
        Term::Elim(_, m, cs, tg) =>
            occurs(id, m) || cs.iter().any(|c| occurs(id, c)) || occurs(id, tg),
        Term::EqSubst(p, h, pf) =>
            occurs(id, p) || occurs(id, h) || occurs(id, pf),
    }
}
