// subst — substitution and index shifting
// spec: specs/terms.md § substitution

use crate::term::Term;

/// shift(t, n) — increment all free indices in t by n.
/// A variable VAR(i) at binding depth d is free iff i >= d; free variables get +n.
pub fn shift(t: &Term, n: u64) -> Term {
    shift_at(t, n, 0)
}

fn shift_at(t: &Term, n: u64, depth: u64) -> Term {
    match t {
        Term::Var(i) => {
            if *i >= depth { Term::Var(i + n) } else { Term::Var(*i) }
        }
        Term::Sort(u) => Term::Sort(*u),
        Term::Pi(a, b) => Term::Pi(
            Box::new(shift_at(a, n, depth)),
            Box::new(shift_at(b, n, depth + 1)),
        ),
        Term::Lam(a, t) => Term::Lam(
            Box::new(shift_at(a, n, depth)),
            Box::new(shift_at(t, n, depth + 1)),
        ),
        Term::App(f, arg) => Term::App(
            Box::new(shift_at(f, n, depth)),
            Box::new(shift_at(arg, n, depth)),
        ),
        Term::Let(a, v, b) => Term::Let(
            Box::new(shift_at(a, n, depth)),
            Box::new(shift_at(v, n, depth)),
            Box::new(shift_at(b, n, depth + 1)),
        ),
        Term::Ind(id, params) => {
            Term::Ind(*id, params.iter().map(|p| shift_at(p, n, depth)).collect())
        }
        Term::Ctor(id, k, args) => {
            Term::Ctor(*id, *k, args.iter().map(|a| shift_at(a, n, depth)).collect())
        }
        Term::Elim(id, motive, cases, target) => Term::Elim(
            *id,
            Box::new(shift_at(motive, n, depth)),
            cases.iter().map(|c| shift_at(c, n, depth)).collect(),
            Box::new(shift_at(target, n, depth)),
        ),
        Term::EqSubst(p, h, pf) => Term::EqSubst(
            Box::new(shift_at(p, n, depth)),
            Box::new(shift_at(h, n, depth)),
            Box::new(shift_at(pf, n, depth)),
        ),
        Term::Const(id) => Term::Const(*id), // constants have no free variables
        Term::Meta(id) => Term::Meta(*id), // metas don't shift
    }
}

/// subst(t, s) — replace VAR(0) with s throughout t; decrement all other free indices.
pub fn subst(t: &Term, s: &Term) -> Term {
    subst_at(t, s, 0)
}

fn subst_at(t: &Term, s: &Term, depth: u64) -> Term {
    match t {
        Term::Var(i) => match i.cmp(&depth) {
            std::cmp::Ordering::Equal   => shift(s, depth),
            std::cmp::Ordering::Greater => Term::Var(i - 1),
            std::cmp::Ordering::Less    => Term::Var(*i),
        },
        Term::Sort(u) => Term::Sort(*u),
        Term::Pi(a, b) => Term::Pi(
            Box::new(subst_at(a, s, depth)),
            Box::new(subst_at(b, s, depth + 1)),
        ),
        Term::Lam(a, body) => Term::Lam(
            Box::new(subst_at(a, s, depth)),
            Box::new(subst_at(body, s, depth + 1)),
        ),
        Term::App(f, arg) => Term::App(
            Box::new(subst_at(f, s, depth)),
            Box::new(subst_at(arg, s, depth)),
        ),
        Term::Let(a, v, b) => Term::Let(
            Box::new(subst_at(a, s, depth)),
            Box::new(subst_at(v, s, depth)),
            Box::new(subst_at(b, s, depth + 1)),
        ),
        Term::Ind(id, params) => {
            Term::Ind(*id, params.iter().map(|p| subst_at(p, s, depth)).collect())
        }
        Term::Ctor(id, k, args) => {
            Term::Ctor(*id, *k, args.iter().map(|a| subst_at(a, s, depth)).collect())
        }
        Term::Elim(id, motive, cases, target) => Term::Elim(
            *id,
            Box::new(subst_at(motive, s, depth)),
            cases.iter().map(|c| subst_at(c, s, depth)).collect(),
            Box::new(subst_at(target, s, depth)),
        ),
        Term::EqSubst(p, h, pf) => Term::EqSubst(
            Box::new(subst_at(p, s, depth)),
            Box::new(subst_at(h, s, depth)),
            Box::new(subst_at(pf, s, depth)),
        ),
        Term::Const(id) => Term::Const(*id), // constants have no free variables
        Term::Meta(id) => Term::Meta(*id), // metas not substituted by regular subst
    }
}
