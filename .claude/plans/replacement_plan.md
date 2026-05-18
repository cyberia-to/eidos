# eidos replaces Lean 4 — replacement plan
# status: draft  2026-05-18

## objective

Port all proof obligations in `nox/proofs/lean/` and
`prysm/lean/Prysm/Layout/` from Lean 4 to `.ei` surface files
checked by the eidos kernel.  Zero Lean dependency post-migration.

---

## current eidos capabilities

### kernel (trusted)
- CIC with de Bruijn indices
- Pi, Lam, App, Let, Sort, Var, Ind, Ctor, Elim, EqSubst (J-rule)
- Decidable equality on terms
- WHNF + NF reduction, structural equality

### tactics (implemented)
intro, exact, apply, rfl, assumption, omega, simp, contradiction,
trivial, rewrite [←], induction, cases, have, revert, clear, show,
sorry, constructor, left, right, try, first, repeat, focus (·), seq

### stdlib (implemented)
- Nat: zero, succ, add, mul, sub, Eq, refl, EqSubst
- Bool: true, false, and, or, not
- Unit, Empty
- Basic propositional: True, False, And, Or, Not

### infrastructure concerns
| file | lines | limit | action needed |
|------|-------|-------|---------------|
| stdlib.rs | 695 | 500 | split into stdlib/{nat,bool,eq,list}.rs |
| tactic_ext.rs | 666 | 500 | split into tactic/{apply,induction,rewrite,omega}.rs |

---

## proof file inventory

### nox (4 files)

| file | theorems | status | porting blocker |
|------|----------|--------|-----------------|
| nox_model.lean | model defs only | vacuous | none — defs, no proofs |
| T1_sequential_equivalence.lean | 3 | vacuous (placeholders) | reduce_seq must be real |
| T2_bound_monotonicity.lean | 23 | 22 rfl + 1 omega/simp | none — portble now |
| T3_parallel_commutativity.lean | 4 | nil case ✓, 3 sorry | Perm + mergeSort theory |

### prysm (7 files)

| file | theorems | status | porting blocker |
|------|----------|--------|-----------------|
| Algebra.lean | 3 | 2 simp+omega + 1 rfl | none — portable now |
| Container.lean | 1 | simp + List.length_map | List.length_map in stdlib |
| Fold.lean | 1 | trivial (vacuous) | none — trivial |
| Gravity.lean | 7 | 5 native_decide + 2 simp+omega | `decide` tactic |
| Multimodal.lean | 1 | trivial via typeclass | typeclass mechanism |
| Protocol.lean | 4 | rfl + 3 Nat lemmas | 5 Nat stdlib lemmas |
| Sizing.lean | 3 | omega + simp + cases | Nat.mul_div_cancel_left |

---

## gap analysis

### G1 — `decide` tactic  [blocks: Gravity.lean ×5]
Evaluate ground propositions over Nat/Bool by computation.
`native_decide` in Lean = normalization to Bool true/false.
In eidos: reduce proposition to `True`/`False` via `nf`, then close.
**Effort**: 1 pomodoro — add `Tactic::Decide`, reduce goal to `True`, close.

### G2 — Nat stdlib lemmas  [blocks: Protocol.lean ×3, Sizing.lean ×1]
Missing lemmas (all provable by omega or induction + omega):
- `Nat.min_le_right (a b : Nat) : min a b ≤ b`
- `Nat.div_le_self (n k : Nat) : n / k ≤ n`
- `Nat.div_le_div_right (h : a ≤ b) (k : Nat) : a / k ≤ b / k`
- `Nat.mul_le_mul_right (k : Nat) (h : a ≤ b) : a * k ≤ b * k`
- `Nat.mul_div_cancel_left (a k : Nat) (h : 0 < k) : k * (a / k) ≤ a`
These are declared in stdlib.rs and proved in a `.ei` prelude file.
**Effort**: 2 pomodoros — prove each as a theorem, add to std_env.

### G3 — List type + basic operations  [blocks: Container.lean, Fold.lean defs]
Need `List` inductive + operations:
- Constructors: nil, cons
- map, foldl, filter, length, length_map (length of map = length)
- head?, tail?, reverse, any, indexOf?, eraseDups, enum
These are definitions only; the proof that matters is `length_map`.
**Effort**: 3 pomodoros — add List inductive to stdlib, prove length_map.

### G4 — `calc` block syntax  [blocks: Protocol.lean scale_respects]
`calc a = b := h1; _ ≤ c := h2; _ ≤ d := h3` chained proof.
In eidos: equivalent to nested `have` + `rewrite`. Can be desugared
at the surface level without a new tactic.
Alternative: port scale_respects directly as `have` chain.
**Effort**: 1 pomodoro — desugar via have at port time, no new infra.

### G5 — Typeclass mechanism  [blocks: Multimodal.lean]
`LayoutDomain` class with 3 instances.  `protocol_generalizes` is
proved by `trivial` (vacuous — the body is `True`).
Minimum viable: add `class` + `instance` syntax, elaborate to
Sigma/record types. Full typeclasses are a large feature.
Alternative: port Multimodal.lean as a record-based module.
**Effort**: record-based port = 1 pomodoro; full typeclasses = 2–3 sessions.

### G6 — Perm theory + mergeSort  [blocks: T3.1 non-nil cases]
T3.sort_permutation_invariant needs cons/swap/trans cases.
Lean T3 has these as sorry. This is genuinely open work.
Required: prove mergeSort is a permutation of its input.
This is non-trivial even in Mathlib. In eidos: need List.Perm
inductive + 3–4 lemmas.
**Effort**: 3–5 pomodoros — but T3 proofs are currently sorry in Lean too.
This gap exists equally in both systems. Not a blocker for the
migration itself — port the sorrys as sorrys.

---

## what can be ported now (no new infrastructure)

These can be written as `.ei` files today:

| target | proof strategy |
|--------|---------------|
| T2 (all 23 theorems) | rfl + omega — eidos already handles both |
| Algebra.lean (3 theorems) | simp + omega + rfl |
| Fold.lean | trivial (vacuous) |
| Sizing.lean (scale_irreducible, classify_injective) | omega + cases |
| add_zero, eq_symm (already tested) | induction + rewrite + rfl |

**Total portable now**: ~30 theorems.

---

## porting plan (prioritized)

### phase 0 — infra cleanup  (1 session)
- Split stdlib.rs → stdlib/{nat,bool,eq}.rs + mod.rs re-export
- Split tactic_ext.rs → tactic/{apply,induction,rewrite,omega}.rs + mod.rs
- Add `.claude/plans/` to .gitignore exception or commit

### phase 1 — port T2 + Algebra + Fold  (1 session)
- Write `eidos/proofs/nox/T2.ei`, `eidos/proofs/prysm/Algebra.ei`,
  `eidos/proofs/prysm/Fold.ei`
- All provable by existing tactics
- ~30 theorems

### phase 2 — G1 decide + G2 Nat lemmas  (1 session)
- Add `decide` tactic (1 pomodoro)
- Add 5 Nat stdlib lemmas as proved theorems (2 pomodoros)
- Port Gravity.lean + Protocol.lean + Sizing.lean
- ~15 theorems

### phase 3 — G3 List type  (1 session)
- Add List inductive + operations to stdlib.rs (or list.rs)
- Prove List.length_map
- Port Container.lean
- ~3 definitions + 1 theorem

### phase 4 — G4 calc / G5 Multimodal  (0.5 session)
- Port Protocol.scale_respects as have-chain (no new syntax)
- Port Multimodal.lean as record module (no full typeclasses)

### phase 5 — T3 sorry cases / nox model  (2+ sessions, future)
- Implement `reduce_seq` semantics
- Prove Perm + mergeSort invariant
- Discharge T3 sorry cases

---

## session estimate

| phase | sessions | pomodoros | current status |
|-------|----------|-----------|----------------|
| 0: infra | 0.5 | 3 | stdlib.rs + tactic_ext.rs over limit |
| 1: T2/Algebra/Fold | 1 | 6 | no blockers |
| 2: decide + Nat lemmas + 3 files | 1 | 6 | G1, G2 gaps |
| 3: List + Container | 1 | 6 | G3 gap |
| 4: calc/Multimodal | 0.5 | 3 | G4, G5 (record approach) |
| 5: T3/nox model | 2+ | 12+ | G6 + open research |
| **total migration** | **4** | **24** | phases 0–4 |
| **total incl. T3** | **6+** | **36+** | all phases |

---

## sign-off checklist

Before starting phase 1, confirm:
- [ ] .ei file format and `eidos check` CLI interface are stable
- [ ] `sorry` in `.ei` files is acceptable for T3 pending proofs
- [ ] Record-based approach is acceptable for Multimodal (no full typeclasses)
- [ ] nox model definitions (reduce_seq placeholder) stay as-is in phase 1–4

---

## notes

- T1, T3.2, T2.8 are vacuously proved in Lean because `reduce_seq` and
  `trace_seq/trace_par` are placeholders. The eidos ports will be equally
  vacuous until real semantics are implemented. This is not a regression.
- All 121 eidos tests pass as of 2026-05-18 (including add_zero induction
  and eq_symm via rewrite [← h]).
- EqSubst (J-rule) is the sole kernel extension from original CIC.
  Soundness is maintained: EqSubst reduces to pf_a when h=refl.
