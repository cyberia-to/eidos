use cyber_eidos::{
    kernel,
    stdlib::{self, binary_nat as b},
    term::Term,
};

fn check_value(term: Term, value: u128) {
    let expected = b::literal(value);
    let ty = Term::Ind(stdlib::EQ_ID, vec![b::bnat(), term, expected.clone()]);
    kernel::check(
        &stdlib::std_env(),
        &vec![],
        &stdlib::eq_refl(b::bnat(), expected),
        &ty,
    )
    .unwrap();
}

#[test]
fn arithmetic_and_order_include_zero() {
    for a in 0..8 {
        for c in 0..8 {
            check_value(b::add(b::literal(a), b::literal(c)), a + c);
            check_value(b::mul(b::literal(a), b::literal(c)), a * c);
            let expected = if a < c {
                stdlib::bool_true()
            } else {
                stdlib::bool_false()
            };
            let ty = Term::Ind(
                stdlib::EQ_ID,
                vec![
                    stdlib::bool_ty(),
                    b::less(b::literal(a), b::literal(c)),
                    expected.clone(),
                ],
            );
            kernel::check(
                &stdlib::std_env(),
                &vec![],
                &stdlib::eq_refl(stdlib::bool_ty(), expected),
                &ty,
            )
            .unwrap();
        }
    }
}

#[test]
fn full_width_product() {
    let a = (1u128 << 64) - 1;
    check_value(b::mul(b::literal(a), b::literal(a)), a * a);
}

#[test]
fn reduction_certificate_rejects_bad_witnesses_and_modular_aliases() {
    use stdlib::reduction_certificate::{check_reduction, prove_reduction};
    for (x, m) in [(0, 17), (16, 17), (17, 17), (35, 17), (255, 1)] {
        let cert = prove_reduction(x, m).unwrap();
        assert_eq!((cert.quotient, cert.remainder), (x / m, x % m));
    }
    assert!(check_reduction(35, 17, 2, 2).is_err());
    assert!(check_reduction(35, 17, 1, 18).is_err()); // equation true, range false
    assert!(prove_reduction(1, 0).is_err());
    // Must use unbounded arithmetic: 2^127*2 does not wrap to zero.
    assert!(check_reduction(0, 2, 1u128 << 127, 0).is_err());
}

#[test]
fn strict_surface_checks_binary_nonnegative_arithmetic() {
    use cyber_eidos::surface::check_strict_source;
    check_strict_source(
        "theorem ok : Eq Bool (BNat.lt BNat.zero (BNat.positive Pos.one)) Bool.true := by { rfl }",
    )
    .unwrap();
    assert!(
        check_strict_source(
            "theorem bad : Eq Bool (BNat.lt BNat.zero BNat.zero) Bool.true := by { rfl }"
        )
        .is_err()
    );
    assert!(check_strict_source("def BNat.mul (a b : BNat) : BNat := BNat.zero").is_err());
    for (a, c, less) in [
        (1u128 << 127, (1u128 << 127) - 1, false),
        (1u128 << 64, 1u128 << 65, true),
        (u128::MAX, u128::MAX, false),
    ] {
        let expected = if less {
            stdlib::bool_true()
        } else {
            stdlib::bool_false()
        };
        let ty = Term::Ind(
            stdlib::EQ_ID,
            vec![
                stdlib::bool_ty(),
                b::less(b::literal(a), b::literal(c)),
                expected.clone(),
            ],
        );
        kernel::check(
            &stdlib::std_env(),
            &vec![],
            &stdlib::eq_refl(stdlib::bool_ty(), expected),
            &ty,
        )
        .unwrap();
    }
}
