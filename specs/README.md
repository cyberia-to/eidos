---
tags: eidos, spec
crystal-type: spec
crystal-domain: eidos
status: draft
---
# eidos reference

canonical specification of the eidos proof assistant. this is the source of truth — when code and reference disagree, fix reference first, then propagate to code.

## specifications

| page | scope | status |
|------|-------|--------|
| terms.md | CIC term syntax, encoding as nox nouns, universe hierarchy | draft |
| kernel.md | type checker: infer(), check(), all CIC rules as nox patterns | draft |
| surface.md | surface syntax, elaboration, implicit arguments | draft |
| tactics.md | tactic set, proof state, combinators | draft |
| stdlib.md | standard library: Nat, Bool, List, Vec, Fin, core theorems | draft |
| certificate.md | proof certificate format, STARK wrapping, cyberlink schema | draft |
| interaction.md | display layer: proof state format, queries, errors, rename | draft |

## reading order

1. terms.md — the data model (what eidos reasons about)
2. kernel.md — the type checker (the trusted core)
3. surface.md — the user-facing language (what users write)
4. tactics.md — the tactic engine (how users construct proofs)
5. stdlib.md — the standard library (reusable theorems)
6. certificate.md — the output format (how proofs enter the cybergraph)
7. interaction.md — the display layer (proof state, queries, errors)

## architecture

eidos has two layers with different trust properties:

trusted kernel — written directly as nox patterns. target: ~2,500 nox IR nodes encoding 9 CIC typing rules (one per term constructor). this is the TCB. no Trident, no Rs — any compiler in the trust chain is a liability.

untrusted shell — elaborator + tactic engine written in Rs. produces kernel terms that the trusted kernel then checks. if the shell is buggy, the kernel rejects the output. the shell cannot forge proofs.

this separation mirrors the Lean 4 kernel/elaborator split, but the trust boundary is enforced by the nox execution model, not by convention.

## CIC over Goldilocks

eidos implements the Calculus of Inductive Constructions (CIC) with universes, inductive types, and structural recursion, instantiated over the Goldilocks field (p = 2⁶⁴ − 2³² + 1).

terms are nox nouns — binary trees of field elements. the universe hierarchy is finite and field-bounded. the structural recursion measure is a well-founded order over nouns (axis traversal depth).

key CIC features in scope:

- dependent function types (Π-types)
- inductive type families with constructors and eliminators
- universe polymorphism (Type₀ : Type₁ : Type₂ : ...)
- structural recursion with termination checker
- definitional equality via β/δ/ι/η reduction

## dependencies

- nox (`~/cyber/nox/`) — runs the type checker kernel
- zheng (`~/cyber/zheng/`) — wraps kernel execution in a STARK certificate
- hemera (`~/cyber/hemera/`) — content-addresses terms and cyberlink keys
- bbg (`~/cyber/bbg/`) — stores proof cyberlinks in the graph state
