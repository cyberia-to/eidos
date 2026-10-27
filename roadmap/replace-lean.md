---
tags: eidos, roadmap, soft3, security
crystal-type: roadmap
crystal-domain: eidos
status: proposed
date: 2026-10-27
---
# eidos replaces lean — the registry ladder

owner's call (2026-10-27): lean is foreign, eidos is native; whatever eidos lacks to replace lean must be built. the proposal is `soft3/proposals/assumptions-registry.md`; this page is eidos's side of it, in order, each milestone proving something the stack uses.

| milestone | delivers | acceptance | when |
|---|---|---|---|
| E0 · the axiom file | `eidos axioms <file>` prints every axiom a theorem depends on; `soft3/proofs/Axioms.ei` holds one axiom per registry entry of class B, C, E, F, G, H with the statement mirrored verbatim | every registry id has one axiom and vice versa; the train's `assumptions-gate` is green | before 2026-11-02 |
| E1 · integers of the economy | `Int` with the kernel's bounded `u64`/`u128` semantics; floor division, isqrt, saturation lemmas; `Conservation.ei`, `Asert.ei`, `Settlement.ei`, `Attribution.ei` | the theorems check and quote the kernel's constants; kernel tests cite theorem ids | A-03, A-05 before 2026-11-02; A-08 with the economy fix |
| E2 · the field and the sum-check | `Goldilocks.ei` (field axioms, p concrete), `Poly.ei` (degree, evaluation, roots ≤ degree), `Multilinear.ei`, `Sumcheck.ei`; Schwartz–Zippel as a counting bound over the challenge space, no probability theory | each row of zheng's soundness ledger becomes a theorem id | first fork window |
| E3 · the zheng bridge | the type check runs on nox and zheng certifies it; certificate `H(check_kernel, H(π, P))` is a cyberlink in bbg, replacing the FNV stub; `eidos verify` returns | a registry theorem's certificate is a particle | with the proven present |
| E4 · oracle interfaces | random oracle and QROM as axiomatized interfaces with explicit query budgets; Fiat–Shamir composition takes the budget as a parameter | the transcript spec's security row cites a theorem with its budget | after E2 |
| E5 · the port | statement-level lean reader rendering a lean theorem's statement in eidos surface syntax; proofs rewritten by hand or by an agent; the hemera bounty names eidos canonical and lean accepted evidence | the first ported attacker certificate | when the first one arrives |

what is kept from v0.1.0's plan: the TCB split, spans, vectors, docs. what changes: the first real corpus is the stack's registry, so `Int` and the field library move ahead of tutorials.
