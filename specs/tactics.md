---
tags: eidos, spec
crystal-type: spec
crystal-domain: eidos
status: draft
---
# tactics

the tactic engine for eidos. tactics are untrusted — they produce candidate proof terms that the kernel then verifies. a buggy tactic can fail to produce a proof, but cannot produce a false one.

## proof state

a proof state is a list of goals. each goal is a triple:

```
Goal = (local_ctx, metavar, expected_type)
```

- `local_ctx` — hypotheses in scope (named, with types)
- `metavar` — the hole `?m` this goal must fill
- `expected_type` — the type `?m` must have

the initial state for `theorem Name : T` is one goal `[(?root, T)]`. a tactic transforms `List(Goal) → List(Goal)`. when the list is empty, the proof is complete and the kernel verifies the assembled term.

the engine works on surface names throughout. de Bruijn conversion happens at assembly time.

---

## grammar

three layers: core tactics, decision procedures, combinators.

```
Tactic ::=

  -- core (map directly to kernel operations)
  | exact <Expr>
  | intro <Name>+
  | apply <Expr>
  | induction <Name> (generalizing <Name>*)? (with <Name>*)?
  | cases <Name> (with <Name>*)?
  | have <Name> : <Type> (:= <Expr> | by <Block>)
  | show <Type>
  | revert <Name>+
  | clear <Name>+
  | rewrite [ (<←>? <Expr>)+ ] (at (<Name>+ | *))?

  -- oracles (external decision procedures; output verified by kernel)
  | omega
  | simp [ <Expr>* ] (at (<Name>+ | *))?

  -- combinators
  | <Tactic> <;> <Tactic>
  | first (| <Tactic>)+
  | repeat <Tactic>
  | try <Tactic>
  | fail <String>?
  | skip

Block ::= { <Tactic>* }
```

---

## core tactics

### exact

closes the current goal with a fully elaborated term.

```
exact e:
  (e_term, e_type) = elab(e)
  require def_eq(e_type, expected_type)
  assign ?m := e_term
  goal removed
```

all other tactics ultimately reduce to sequences of `exact` on the assembled proof term.

### intro

introduces one or more hypotheses from a PI-type goal. each name peels one binder.

```
intro x:
  require whnf(expected_type) = PI(A, B)
  add (x : A) to local_ctx
  new expected_type = B[x/0]
  assign ?m := LAM(A, ?m_body)
```

`intro x y z` sequences three applications. fails if the goal type is not a PI after whnf.

### apply

applies a term whose conclusion unifies with the goal, generating one subgoal per explicit argument.

```
apply e:
  (e_term, _) = elab(Σ, Γ, e)
  f_type = infer(Σ, Γ, e_term)
  unfold f_type as PI(A₁, PI(A₂, ... PI(Aₙ, C)...))
  unify(C, expected_type)
  -- only generate subgoals for arguments not already determined by unification:
  subgoals = [(?mᵢ, Σ, Γ, Aᵢ) for each Aᵢ where ?mᵢ is not yet solved]
  assign ?m := APP*(e_term, ?m₁, ..., ?mₙ)   -- solved mᵢ are substituted in-place
```

implicit arguments are inserted before unification. unification may instantiate metavariables shared across goals.

### induction

applies the dependent eliminator for an inductive type. introduces constructor arguments and induction hypotheses per case.

```
induction x generalizing y₁ ... yₖ:
  x has type IND(id, params)
  revert y₁ ... yₖ (add back as PI-prefix in goal)
  motive = fun z => expected_type[x := z]
  for each constructor k of id:
    introduce constructor arguments as hypotheses
    for each recursive argument r : IND(id, ...):
      introduce IH : APP(motive, r)
    generate subgoal for this case
  assign ?m := ELIM(id, motive, cases, x)
```

`generalizing` reverts hypotheses before motive construction so they can depend on the induction variable. default case names are the constructor names; `with` overrides them.

### cases

applies the dependent eliminator without exposing induction hypotheses. for case analysis where the structure is not used recursively.

```
cases x:
  x has type IND(id, params)
  motive = fun z => expected_type[x := z]
  for each constructor k of id:
    introduce constructor arguments as hypotheses
    no IH introduced
    generate subgoal for this case
  assign ?m := ELIM(id, motive, cases, x)
```

`cases` and `induction` produce the same ELIM term. the difference is in what the tactic exposes: `cases` withholds the IH names. use `cases` when the target type is Prop and the structure is non-recursive; use `induction` when proof of each case requires an induction hypothesis.

### have

introduces a local fact, either by term or by sub-proof.

```
have h : T := e:
  (e_term, e_type) = elab(e)
  require def_eq(e_type, T)
  add (h : T) to local_ctx of current goal
  current goal unchanged

have h : T by block:
  insert new goal (?h, T) before current goal
  on completion: add (h : T) to local_ctx of the next goal
```

### show

asserts that the goal type equals a given expression up to definitional equality, then displays the given expression as the new goal form. a semantic no-op; a readability operation.

```
show T:
  require def_eq(T, expected_type)
  replace expected_type with T (same goal, new display form)
```

useful when whnf has reduced the goal to an unreadable form.

### revert

the inverse of `intro`. moves a hypothesis back into the goal as a PI-prefix.

```
revert h:
  h : A in local_ctx
  remove h from local_ctx
  expected_type becomes PI(A, expected_type)
  proof obligation: the ?m must now be a LAM
```

`revert h₁ h₂` sequences two reversions, right-to-left — the last named is outermost in the resulting PI-chain. all hypotheses that depend on `h` must be reverted before or together with `h`.

### clear

removes a hypothesis from the local context. only valid when the hypothesis does not appear in the goal type or in any remaining hypothesis type.

```
clear h:
  require h not free in expected_type
  require h not free in any other hypothesis type or let-binding body
  remove h from local_ctx
  proof term unchanged
```

`clear` produces no change to the proof term — it only shrinks the local context the tactic engine tracks. the check covers all entries in `local_ctx`: for `CTX_VAR(A)` entries, check A; for `CTX_LET(A, v)` entries, check both A and v.

### rewrite

rewrites the goal (or a hypothesis) using an equation, replacing one side with the other.

```
rewrite [h] at target:
  h_type = infer(h)
  require whnf(h_type) = Eq(A, lhs, rhs)
  replace all syntactic occurrences of lhs with rhs in target
  produce transport proof via Eq.transport

rewrite [← h] at target:
  same, but replace rhs with lhs (reverse direction)
```

`at target`:
- omitted — rewrite the goal
- `at h₁ h₂` — rewrite in named hypotheses
- `at *` — rewrite goal and all hypotheses

replacement is syntactic (structural noun equality), not definitional. `rewrite [h₁, h₂]` sequences two rewrites left-to-right.

---

## decision procedures

oracles that produce proof terms verified by the kernel. the oracle itself is untrusted shell.

### omega

closes linear arithmetic goals over Nat.

```
omega:
  parse expected_type as a linear arithmetic formula
  run Omega decision procedure
  if valid: synthesize a proof term (sequence of stdlib lemma applications)
  else: fail
```

supported connectives: `≤`, `<`, `=`, `≠`, `∧`, `∨`, `¬`, `∀`, `∃` over linear combinations of Nat variables and constants. non-linear terms (variable × variable) are not supported.

### simp

simplifies by applying a rewrite rule set to fixpoint.

```
simp [lemmas*] at target:
  simp_set = default_simp_set ∪ set(lemmas)
  apply simp_set left-to-right, repeatedly, until no rule fires
  if result is True: close the goal
  else: replace target with simplified form
```

`at target` follows the same syntax as `rewrite`. omitted means simplify the goal. `at *` simplifies goal and all hypotheses.

each rule in the simp set is an equation `Eq A lhs rhs` or a conditional `∀ x, P x → Eq A (lhs x) (rhs x)`. the default set is declared in [[stdlib]].

simp does not fail when it cannot close a goal — it leaves a simpler goal. simp may fail to simplify even when simplification exists (it is not complete).

**rewriting strategy**: innermost-first (bottom-up). for a term `t`, simp recursively simplifies all subterms before attempting rules on `t` itself. this continues to a fixpoint — the full term is stable when no rule fires at any position. congruence lemmas (automatically generated for each constructor and for PI/LAM) allow simp to descend under binders and inside constructor arguments.

conditional rules `∀ x, P x → lhs x = rhs x` fire when condition `P x` is dischargeable by `simp` itself (recursive side-condition solving, bounded to avoid loops). rules are applied left-to-right: `lhs` is replaced by `rhs`, never the reverse.

---

## combinator algebra

combinators compose tactics. they are defined over the tactic language itself, not over proof terms.

### broadcast: `t₁ <;> t₂`

apply `t₁` to the focused goal, then apply `t₂` to every goal `t₁` produced. if `t₂` fails on any subgoal, the entire `t₁ <;> t₂` fails — partially closed subgoals are not retained.

```
t₁ <;> t₂:
  goals₁ = run t₁ on current goal   -- if t₁ fails, the whole thing fails
  for each g in goals₁:
    if t₂ fails on g: fail           -- roll back all t₂ applications so far
  return remaining goals after all t₂ applications
```

### choice: `first | t₁ | ... | tₙ`

try each branch in order; commit to the first that succeeds. each branch is tried on the *original* proof state — if tᵢ produces subgoals and then fails internally (e.g., in a combinator like `intro <;> exact wrong`), the proof state is rolled back to the state before tᵢ was tried before attempting tᵢ₊₁.

```
first | t₁ | ... | tₙ:
  for each tᵢ:
    saved = current proof state
    try tᵢ:
      if succeeds: return result
      if fails: restore saved; continue to tᵢ₊₁
  fail  -- all branches exhausted
```

backtracking is proof-state backtracking only — metavariable assignments made inside a failing branch are undone when the state is restored.

### iteration: `repeat t`

apply `t` until it fails. always succeeds (zero applications is valid).

```
repeat t:
  while t succeeds on current goal: apply t
```

### identity: `skip`

always succeeds, leaves all goals unchanged. the identity element of tactic composition.

### failure: `fail <msg>?`

always fails with an optional message. used inside `first` branches to provide error context.

### derived: `try t`

```
try t  :=  first | t | skip
```

---

## tactic library

derived tactics defined entirely in terms of the core. not primitives — any of these can be reproduced in user code. collected here as standard names.

```
-- close a reflexivity goal
rfl  :=  exact Eq.refl _

-- find a matching hypothesis
assumption  :=
  first | exact h₁ | exact h₂ | ...   -- search local_ctx

-- find contradicting hypotheses P and ¬P
contradiction  :=
  find h₁ : P and h₂ : ¬P in local_ctx
  exact False.elim (h₂ h₁)

-- apply the sole (or first) constructor of a product type
constructor  :=  apply <inferred_ctor>

-- Or introduction
left   :=  apply Or.left
right  :=  apply Or.right

-- try obvious closures in order
trivial  :=  first | rfl | assumption | exact True.intro
```

`rename_i` (rename auto-generated inaccessible names) is a presentation concern only — it produces no proof term and is not specified here. implementations may support it as a UI feature.

---

## completeness and kernel call

when the goal list is empty, the engine substitutes all solved metavariables into the root term, then calls:

```
check(Σ, Γ, assembled_proof, T)
```

if the kernel accepts: proof is complete. pass to the certificate pipeline (see [[certificate]]).

if the kernel rejects: surface the error. the assembled term is retained for debugging — the user can inspect which metavar produced the bad term.
