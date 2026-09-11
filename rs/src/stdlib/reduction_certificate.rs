//! Concrete Euclidean-division witnesses checked by binary CIC arithmetic.
//! Host division proposes a witness; it is never a kernel reduction rule.
use super::{EQ_ID, binary_nat as b, bool_true, bool_ty, eq_refl, std_env};
use crate::{kernel, term::Term};

#[derive(Debug)]
pub struct ReductionCertificate {
    pub quotient: u128,
    pub remainder: u128,
    /// Closed (proof, proposition) pairs: reconstruction and strict range.
    pub claims: [(Term, Term); 2],
}

pub fn check_reduction(
    x: u128,
    modulus: u128,
    quotient: u128,
    remainder: u128,
) -> Result<ReductionCertificate, String> {
    if modulus == 0 {
        return Err("modulus must be positive".into());
    }
    let reconstructed = b::add(
        b::mul(b::literal(quotient), b::literal(modulus)),
        b::literal(remainder),
    );
    let input = b::literal(x);
    let equation = Term::Ind(EQ_ID, vec![b::bnat(), reconstructed, input.clone()]);
    let range = Term::Ind(
        EQ_ID,
        vec![
            bool_ty(),
            b::less(b::literal(remainder), b::literal(modulus)),
            bool_true(),
        ],
    );
    let claims = [
        (eq_refl(b::bnat(), input), equation),
        (eq_refl(bool_ty(), bool_true()), range),
    ];
    let env = std_env();
    for (proof, proposition) in &claims {
        kernel::check(&env, &vec![], proof, proposition)
            .map_err(|e| format!("invalid reduction certificate: {e:?}"))?;
    }
    Ok(ReductionCertificate {
        quotient,
        remainder,
        claims,
    })
}

pub fn prove_reduction(x: u128, modulus: u128) -> Result<ReductionCertificate, String> {
    if modulus == 0 {
        return Err("modulus must be positive".into());
    }
    check_reduction(x, modulus, x / modulus, x % modulus)
}
