// pretty — term pretty-printer for display in CLI output

use cyber_eidos::term::Term;
use cyber_eidos::stdlib::{
    AND_ID, BOOL_FALSE_IDX, BOOL_ID, EQ_ID, FALSE_ID, LIST_ID,
    LIST_LINK_IDX, LIST_NIL_IDX, NAT_ID, NAT_NEXT, NAT_ZERO, OR_ID, TRUE_ID,
};

/// Top-level entry: format a term as a human-readable string.
pub fn pp(t: &Term) -> String {
    pp_prec(t, 0)
}

fn pp_prec(t: &Term, prec: u8) -> String {
    match t {
        Term::Sort(0) => "Prop".into(),
        Term::Sort(1) => "Type".into(),
        Term::Sort(n) => format!("Type {}", n - 1),

        Term::Var(i) => format!("#{}", i),

        Term::Meta(id) => format!("?{}", id),

        Term::Ind(id, params) => {
            let name = ind_name(*id);
            if params.is_empty() {
                name
            } else {
                let s = params.iter().map(|p| pp_prec(p, 10)).collect::<Vec<_>>().join(" ");
                paren(prec > 5, format!("{} {}", name, s))
            }
        }

        Term::Ctor(id, k, args) => pp_ctor(*id, *k, args, prec),

        Term::Pi(a, b) => {
            if !has_free_at(0, b) {
                paren(prec > 0, format!("{} → {}", pp_prec(a, 5), pp_prec(b, 0)))
            } else {
                paren(prec > 0, format!("Π(_ : {}), {}", pp_prec(a, 0), pp_prec(b, 0)))
            }
        }

        Term::Lam(a, body) => {
            paren(prec > 0, format!("fun _ : {} => {}", pp_prec(a, 0), pp_prec(body, 0)))
        }

        Term::App(f, x) => {
            paren(prec > 5, format!("{} {}", pp_prec(f, 5), pp_prec(x, 10)))
        }

        Term::Let(ty, val, body) => paren(
            prec > 0,
            format!(
                "let _ : {} := {} in {}",
                pp_prec(ty, 0),
                pp_prec(val, 0),
                pp_prec(body, 0)
            ),
        ),

        Term::Elim(id, _m, _cs, tg) => {
            paren(prec > 5, format!("@elim[{}] {}", ind_name(*id), pp_prec(tg, 10)))
        }
    }
}

fn pp_ctor(id: u64, k: u64, args: &[Term], prec: u8) -> String {
    if id == NAT_ID {
        if let Some(n) = try_nat(id, k, args) {
            return n.to_string();
        }
    }
    if id == BOOL_ID {
        return if k == BOOL_FALSE_IDX { "false".into() } else { "true".into() };
    }
    if id == LIST_ID && k == LIST_NIL_IDX {
        return "[]".into();
    }
    if id == LIST_ID && k == LIST_LINK_IDX && args.len() == 3 {
        let h = pp_prec(&args[1], 10);
        let t = pp_prec(&args[2], 0);
        return paren(prec > 2, format!("{} :: {}", h, t));
    }
    if id == EQ_ID && k == 0 {
        return "rfl".into();
    }
    let name = ctor_name(id, k);
    if args.is_empty() {
        name
    } else {
        let s = args.iter().map(|a| pp_prec(a, 10)).collect::<Vec<_>>().join(" ");
        paren(prec > 5, format!("{} {}", name, s))
    }
}

fn try_nat(id: u64, k: u64, args: &[Term]) -> Option<u64> {
    if id != NAT_ID { return None; }
    if k == NAT_ZERO && args.is_empty() { return Some(0); }
    if k == NAT_NEXT && args.len() == 1 {
        if let Term::Ctor(id2, k2, args2) = &args[0] {
            return try_nat(*id2, *k2, args2).map(|n| n + 1);
        }
    }
    None
}

fn ind_name(id: u64) -> String {
    match id {
        NAT_ID   => "Nat".into(),
        BOOL_ID  => "Bool".into(),
        LIST_ID  => "List".into(),
        EQ_ID    => "Eq".into(),
        TRUE_ID  => "True".into(),
        FALSE_ID => "False".into(),
        AND_ID   => "And".into(),
        OR_ID    => "Or".into(),
        _        => format!("Ind#{:#x}", id),
    }
}

fn ctor_name(id: u64, k: u64) -> String {
    match (id, k) {
        (NAT_ID,  0) => "Nat.zero".into(),
        (NAT_ID,  1) => "Nat.next".into(),
        (BOOL_ID, 0) => "false".into(),
        (BOOL_ID, 1) => "true".into(),
        _            => format!("Ctor#{:#x}.{}", id, k),
    }
}

/// Check if de Bruijn variable at `depth` appears free in `t`.
/// In Pi/Lam/Let-body, the depth for the new binder increases by 1.
fn has_free_at(depth: u64, t: &Term) -> bool {
    match t {
        Term::Var(i) => *i == depth,
        Term::Sort(_) | Term::Meta(_) => false,
        Term::Pi(a, b) | Term::Lam(a, b) =>
            has_free_at(depth, a) || has_free_at(depth + 1, b),
        Term::App(f, x) => has_free_at(depth, f) || has_free_at(depth, x),
        Term::Let(ty, v, b) =>
            has_free_at(depth, ty) || has_free_at(depth, v) || has_free_at(depth + 1, b),
        Term::Ind(_, ps)      => ps.iter().any(|p| has_free_at(depth, p)),
        Term::Ctor(_, _, as_) => as_.iter().any(|a| has_free_at(depth, a)),
        Term::Elim(_, m, cs, tg) =>
            has_free_at(depth, m)
            || cs.iter().any(|c| has_free_at(depth, c))
            || has_free_at(depth, tg),
    }
}

fn paren(cond: bool, s: String) -> String {
    if cond { format!("({})", s) } else { s }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cyber_eidos::stdlib::{nat, nat_lit, bool_true};

    #[test]
    fn pp_nat_lit() {
        assert_eq!(pp(&nat_lit(0)), "0");
        assert_eq!(pp(&nat_lit(3)), "3");
    }

    #[test]
    fn pp_bool() {
        assert_eq!(pp(&bool_true()), "true");
    }

    #[test]
    fn pp_sorts() {
        assert_eq!(pp(&Term::Sort(0)), "Prop");
        assert_eq!(pp(&Term::Sort(1)), "Type");
        assert_eq!(pp(&Term::Sort(2)), "Type 1");
    }

    #[test]
    fn pp_nat_type() {
        assert_eq!(pp(&nat()), "Nat");
    }

    #[test]
    fn pp_arrow() {
        // Pi(Nat, Nat) — non-dependent arrow
        let t = Term::Pi(
            Box::new(nat()),
            Box::new(cyber_eidos::stdlib::nat()),
        );
        assert_eq!(pp(&t), "Nat → Nat");
    }

    #[test]
    fn pp_dep_pi() {
        // Pi(Nat, Var(0)) — dependent, shows as Π
        let t = Term::Pi(Box::new(nat()), Box::new(Term::Var(0)));
        assert_eq!(pp(&t), "Π(_ : Nat), #0");
    }
}
