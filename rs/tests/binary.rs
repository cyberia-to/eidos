use cyber_eidos::{
    kernel,
    stdlib::{self, binary as b},
    term::Term,
};
fn check_sum(a: u128, c: u128) {
    let left = b::add(b::literal(a).unwrap(), b::literal(c).unwrap());
    let right = b::literal(a + c).unwrap();
    let ty = Term::Ind(stdlib::EQ_ID, vec![b::pos(), left, right.clone()]);
    kernel::check(
        &stdlib::std_env(),
        &vec![],
        &stdlib::eq_refl(b::pos(), right),
        &ty,
    )
    .unwrap();
}
#[test]
fn binary_carries_are_kernel_checked() {
    for a in 1..12 {
        for b in 1..12 {
            check_sum(a, b);
        }
    }
    for bit in [8, 16, 32, 64, 96, 127] {
        check_sum((1u128 << bit) - 1, 1);
    }
    assert!(b::literal(0).is_none());
}
#[test]
fn wrong_full_width_result_is_rejected() {
    let env = stdlib::std_env();
    let a = b::literal(1u128 << 64).unwrap();
    let ty = Term::Ind(
        stdlib::EQ_ID,
        vec![b::pos(), b::add(a.clone(), b::one()), a.clone()],
    );
    assert!(kernel::check(&env, &vec![], &stdlib::eq_refl(b::pos(), a), &ty).is_err());
}

#[test]
fn surface_binary_terms_recheck_and_false_carries_fail() {
    use cyber_eidos::surface::check_strict_source;
    check_strict_source("theorem carry (n : Pos) : Eq Pos (Pos.succ (Pos.bit1 n)) (Pos.bit0 (Pos.succ n)) := by { rfl }").unwrap();
    for source in [
        "theorem bad (n : Pos) : Eq Pos (Pos.succ (Pos.bit1 n)) (Pos.bit0 n) := by { rfl }",
        "def Pos.add (a b : Pos) : Pos := a",
        "theorem bad : Eq Pos Pos.one (Pos.bit0 Pos.one) := by { rfl }",
    ] {
        assert!(check_strict_source(source).is_err(), "accepted {source}");
    }
}
