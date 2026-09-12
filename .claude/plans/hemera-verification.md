# Hemera verification foundation

User authorization: implement Eidos improvements for Hemera, investigate the
inverse S-box hypothesis, and upgrade the structural commitment architecture.

This implementation slice:

1. Make `sorry` an error; correct Pi universe computation to match kernel.md.
2. Provide a strict library/CLI checker with a restricted checked standard
   environment, closed-term rechecking, transitive imports and no admissions.
3. Move Hemera's custom strict-checking policy onto that public API.
4. Reproduce and repair inverse witness constraints; record mathematical
   results, experiments and limits of the security hypothesis.
5. Specify and implement an additive structural commitment layer and a
   section adapter, keeping explicit separation from existing particle roots.

Next dependency stages (not established by this slice): efficient proved binary
arithmetic / machine words, Goldilocks refinement, general validated inductives,
proof-producing algebraic automation, verified implementation translation.
The strict fragment must fail closed until those facilities are supported.

Validation: Eidos workspace tests and strict CLI negative tests; existing Hemera
proof suite against the shared checker; Hemera CPU/no_std checks and structural
proof tampering tests; reproducible small-field inverse experiments. No empirical
experiment is a full-round security proof.

Completed this slice: strict API/CLI, import policy, Pi universe fix and Hemera
checker integration; corrected inverse residuals and two conditional lemmas;
experimental structural commitments and `.cyb` extraction adapter. Eidos's
158 tests pass. Whole-repository strict clippy retains pre-existing diagnostics
(13 after changes vs 16 in an isolated baseline export). Remaining dependency
stages above are explicitly not completed.

2026-09-11 slice: added canonical binary Pos with CIC successor/addition,
strict prelude rechecking and full-width carry negative controls. All 161
workspace tests pass. Hemera now checks 15 theorems and rejects 11 negative
controls, including concrete Goldilocks modulus/exponent arithmetic; Rust/model
bridges remain tests. No machine-word wrapping or field reduction proof yet.

Follow-up 2026-09-11: BNat adds zero, multiplication and comparison as CIC terms.
Concrete Euclidean-division certificates reconstruct the input and check range.
Hemera checks 21 source theorems, rejects 13 negative controls and certifies two
actual Rust products. Eidos tests total 165; dense 64-bit product reduction is
still slow (~30 seconds debug, ~8 seconds release test suite). General resource
bounds and shared reduction remain open. Separate Z3 QF_LIA verification of
Hemera's manually translated reduce128 model is UNSAT; this is not an Eidos
proof or an automatically verified Rust translation. The user explicitly
requires actual hash-security resolution for production: the earlier choice
of an alternative on uncertainty is not task completion; no profile is finalized.
