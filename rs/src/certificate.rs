// certificate — proof certificate format
// spec: specs/certificate.md
// Untrusted shell: certificate wrapping does not affect kernel soundness.
//
// Full zheng STARK and bbg cyberlink emission require the zheng and bbg crates
// which are not yet linked. This module implements the data model, CLAIM encoding,
// and axon computation (via a stub hash), leaving STARK generation as a TODO.

use crate::term::Term;

// ── Constants ─────────────────────────────────────────────────────────────────

/// OK signal in cyberlinks (atom 0x4F4B = ASCII "OK").
pub const OK: u64 = 0x4F4B;

/// CLAIM tag (0xC0) — prefix a type noun to produce a claim noun.
pub const CLAIM_TAG: u64 = 0xC0;

/// Domain separator for proof events (hemera input).
pub const PROOF_EVENT_DOMAIN: u8 = 0xA1;

// ── Noun-like encoding ─────────────────────────────────────────────────────────
// Simplified noun encoding for certificate computation.
// Production uses the nox noun type; here we use a byte-vector representation.

/// A simplified noun for certificate hashing purposes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Noun {
    Atom(u64),
    Cell(Box<Noun>, Box<Noun>),
}

impl Noun {
    pub fn atom(v: u64) -> Self { Noun::Atom(v) }
    pub fn cell(a: Noun, b: Noun) -> Self { Noun::Cell(Box::new(a), Box::new(b)) }

    /// Encode as bytes (little-endian for atoms, recursive for cells).
    pub fn to_bytes(&self) -> Vec<u8> {
        match self {
            Noun::Atom(v) => {
                let mut b = v.to_le_bytes().to_vec();
                // trim trailing zero bytes (canonical)
                while b.last() == Some(&0) && b.len() > 1 { b.pop(); }
                b
            }
            Noun::Cell(a, b_n) => {
                let mut bytes = vec![0xFFu8]; // cell tag
                bytes.extend(a.to_bytes());
                bytes.push(0xFEu8); // separator
                bytes.extend(b_n.to_bytes());
                bytes
            }
        }
    }
}

/// Encode a Term as a Noun for hashing.
pub fn term_to_noun(t: &Term) -> Noun {
    match t {
        Term::Var(i)       => Noun::cell(Noun::atom(0x00), Noun::atom(*i)),
        Term::Sort(u)      => Noun::cell(Noun::atom(0x01), Noun::atom(*u)),
        Term::Pi(a, b)     => Noun::cell(Noun::atom(0x02), Noun::cell(term_to_noun(a), term_to_noun(b))),
        Term::Lam(a, t)    => Noun::cell(Noun::atom(0x03), Noun::cell(term_to_noun(a), term_to_noun(t))),
        Term::App(f, a)    => Noun::cell(Noun::atom(0x04), Noun::cell(term_to_noun(f), term_to_noun(a))),
        Term::Let(a, v, b) => Noun::cell(Noun::atom(0x05), Noun::cell(term_to_noun(a), Noun::cell(term_to_noun(v), term_to_noun(b)))),
        Term::Ind(id, ps)  => Noun::cell(Noun::atom(0x06), Noun::cell(Noun::atom(*id), list_noun(ps))),
        Term::Ctor(id,k,a) => Noun::cell(Noun::atom(0x07), Noun::cell(Noun::atom(*id), Noun::cell(Noun::atom(*k), list_noun(a)))),
        Term::Elim(id,m,cs,tg) => Noun::cell(
            Noun::atom(0x08),
            Noun::cell(Noun::atom(*id), Noun::cell(term_to_noun(m), Noun::cell(list_noun(cs), term_to_noun(tg)))),
        ),
        Term::EqSubst(p, h, pf) => Noun::cell(
            Noun::atom(0x0A),
            Noun::cell(term_to_noun(p), Noun::cell(term_to_noun(h), term_to_noun(pf))),
        ),
        Term::Const(id)    => Noun::cell(Noun::atom(0x0B), Noun::atom(*id)),
        Term::Meta(id)     => Noun::cell(Noun::atom(0x09), Noun::atom(*id)),
    }
}

fn list_noun(terms: &[Term]) -> Noun {
    terms.iter().rev().fold(Noun::atom(0), |acc, t| {
        Noun::cell(term_to_noun(t), acc)
    })
}

/// CLAIM(T) = Cell(atom(0xC0), T_noun) — tag a type as a claim.
pub fn claim_noun(ty: &Term) -> Noun {
    Noun::cell(Noun::atom(CLAIM_TAG), term_to_noun(ty))
}

// ── Proof artifact ────────────────────────────────────────────────────────────

/// Proof artifact: the output of a successful kernel verification.
#[derive(Debug, Clone)]
pub struct ProofArtifact {
    /// The type (proposition) that was proved.
    pub claim_type: Term,
    /// The proof term (kernel-verified).
    pub proof_term: Term,
    /// The kernel ID (stub: all-zeros until nox kernel is linked).
    pub kernel_id: [u8; 32],
    /// The axon: content address of this proof event.
    pub axon: u64,
    /// STARK proof bytes (empty until zheng is linked).
    pub stark_bytes: Vec<u8>,
}

impl ProofArtifact {
    /// Build a ProofArtifact, computing the axon via stub_hemera.
    pub fn new(claim_type: Term, proof_term: Term) -> Self {
        let claim = claim_noun(&claim_type);
        let proof_noun = term_to_noun(&proof_term);
        let kernel_id = [0u8; 32];

        // axon = hemera(KERNEL_ID || CLAIM(T) || proof_noun) with domain sep 0xA1
        // Stub: concatenate bytes and hash with a simple checksum (real: Poseidon2)
        let axon = stub_hemera(PROOF_EVENT_DOMAIN, &kernel_id, &claim, &proof_noun);

        ProofArtifact {
            claim_type,
            proof_term,
            kernel_id,
            axon,
            stark_bytes: vec![],
        }
    }

    /// Produce a cyberlink record: (axon, OK).
    pub fn cyberlink(&self) -> (u64, u64) {
        (self.axon, OK)
    }
}

/// Stub hash function (placeholder for Poseidon2-Goldilocks / hemera).
/// Produces a deterministic u64 from the inputs.
fn stub_hemera(domain: u8, kernel_id: &[u8; 32], claim: &Noun, proof: &Noun) -> u64 {
    let mut bytes = vec![domain];
    bytes.extend_from_slice(kernel_id);
    bytes.extend(claim.to_bytes());
    bytes.extend(proof.to_bytes());
    // FNV-1a 64-bit hash as a placeholder
    let mut h: u64 = 0xcbf29ce484222325;
    for b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

// ── Verification ──────────────────────────────────────────────────────────────

/// Certificate verification result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyResult {
    Valid { claim: String, axon: u64 },
    Invalid { reason: String },
}

/// Verify a certificate: recompute the axon and check kernel accepts the proof.
pub fn verify_certificate(artifact: &ProofArtifact, env: &crate::env::Env) -> VerifyResult {
    use crate::kernel::check;
    let ctx = vec![];
    match check(env, &ctx, &artifact.proof_term, &artifact.claim_type) {
        Ok(()) => {
            let expected_axon = ProofArtifact::new(
                artifact.claim_type.clone(),
                artifact.proof_term.clone(),
            ).axon;
            if expected_axon == artifact.axon {
                VerifyResult::Valid {
                    claim: format!("{:?}", artifact.claim_type),
                    axon: artifact.axon,
                }
            } else {
                VerifyResult::Invalid { reason: "axon mismatch".into() }
            }
        }
        Err(e) => VerifyResult::Invalid { reason: format!("{e:?}") },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stdlib::{std_env, nat, nat_zero};

    #[test]
    fn noun_atom_roundtrip() {
        let n = Noun::atom(42);
        assert_eq!(n, Noun::Atom(42));
    }

    #[test]
    fn noun_cell_bytes_nonzero() {
        let c = Noun::cell(Noun::atom(1), Noun::atom(2));
        let b = c.to_bytes();
        assert!(!b.is_empty());
    }

    #[test]
    fn claim_noun_has_tag() {
        let ty = nat();
        let claim = claim_noun(&ty);
        assert_eq!(claim, Noun::cell(Noun::atom(CLAIM_TAG), term_to_noun(&ty)));
    }

    #[test]
    fn proof_artifact_axon_deterministic() {
        let ty = nat();
        let proof = nat_zero();
        let a1 = ProofArtifact::new(ty.clone(), proof.clone());
        let a2 = ProofArtifact::new(ty, proof);
        assert_eq!(a1.axon, a2.axon);
    }

    #[test]
    fn proof_artifact_different_claims_different_axons() {
        let ty1 = nat();
        let ty2 = Term::Sort(1);
        let a1 = ProofArtifact::new(ty1, nat_zero());
        let a2 = ProofArtifact::new(ty2, Term::Sort(0));
        assert_ne!(a1.axon, a2.axon);
    }

    #[test]
    fn verify_valid_proof() {
        let env = std_env();
        // zero : Nat
        let artifact = ProofArtifact::new(nat(), nat_zero());
        let result = verify_certificate(&artifact, &env);
        assert_eq!(result, VerifyResult::Valid {
            claim: format!("{:?}", nat()),
            axon: artifact.axon,
        });
    }

    #[test]
    fn verify_wrong_type_invalid() {
        let env = std_env();
        // Claim: Sort(1) (Type₀). Proof: nat_zero(). Wrong type.
        let artifact = ProofArtifact::new(Term::Sort(1), nat_zero());
        match verify_certificate(&artifact, &env) {
            VerifyResult::Invalid { .. } => {}
            other => panic!("expected Invalid, got {other:?}"),
        }
    }

    #[test]
    fn cyberlink_format() {
        let artifact = ProofArtifact::new(nat(), nat_zero());
        let (axon, ok) = artifact.cyberlink();
        assert_eq!(axon, artifact.axon);
        assert_eq!(ok, OK);
    }

    #[test]
    fn term_to_noun_sort() {
        assert_eq!(term_to_noun(&Term::Sort(0)), Noun::cell(Noun::atom(0x01), Noun::atom(0)));
        assert_eq!(term_to_noun(&Term::Sort(1)), Noun::cell(Noun::atom(0x01), Noun::atom(1)));
    }
}
