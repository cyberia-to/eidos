---
tags: eidos, spec
crystal-type: spec
crystal-domain: eidos
status: draft
---
# kernel

the trusted type checker for eidos. a [[nox]] program of 9 CIC typing rules (one per term constructor) encoded as Layer 1 patterns. this is the TCB — the only component whose correctness must be assumed. everything outside the kernel is untrusted shell.

## interface

the kernel exposes two operations, each implemented as a nox formula noun:

```
infer : (Σ, Γ, term) → type | Error
check : (Σ, Γ, term, type) → Ok | Error
```

- Σ — global environment (inductive descriptors, accessed via the `look` pattern)
- Γ — local context (list of CTX_VAR / CTX_LET entries; see [[terms]])
- term — a term noun to type-check
- type — an expected type noun

`infer` derives the type of a term. `check` verifies that a term has a given type, using `infer` and definitional equality. `check` is the entry point for proof verification.

inputs and outputs are [[nox]] nouns following the encoding in [[terms]].

## nox program structure

the kernel formula is a depth-first case dispatch on the term tag (axis 2 of the term noun), implemented with nested `branch` patterns. each branch reads operands via `axis`, recurses via `compose`, and constructs result nouns via `cons`.

the kernel input noun shape:

```
input = cons(cons(Σ_ref, Γ), term)
  -- axis(2, input) = cons(Σ_ref, Γ)
  -- axis(3, input) = term
  -- axis(4, input) = Σ_ref
  -- axis(5, input) = Γ
  -- axis(6, input) = term tag
  -- axis(7, input) = term payload
```

`Σ_ref` is a pointer to the global environment, read via `look` (namespace 0). `Γ` is the local context noun.

## typing rules

each rule below corresponds to one branch in the kernel dispatch. the rule name matches the term tag.

### var

```
ctx_entry = ctx_lookup(Γ, i)
infer(Σ, Γ, VAR(i)) =
  | ctx_entry is CTX_VAR(A)    → shift(A, i+1)
  | ctx_entry is CTX_LET(A,_)   → shift(A, i+1)
```

`shift(A, i+1)` adjusts A's free indices for the i+1 binders crossed during lookup. the kernel implements ctx_lookup as a tail-recursive compose chain over the context list, decrementing i at each VAR/LET entry.

### sort

```
infer(Σ, Γ, SORT(u)) =
  require: u < p − 1      -- p = 2⁶⁴ − 2³² + 1; overflow would wrap to SORT(0)
  SORT(u + 1)
```

implemented via `lt(axis(7, term), atom(p−1))` before `add(..., atom(1))`. if the check fails, return `Error(expected_sort)`.

### pi

```
rule (Π-form):
  u = infer(Σ, Γ, A)
  require: u = SORT(s₁)          -- else Error(expected_sort)
  v = infer(Σ, Γ:VAR(A), B)
  require: v = SORT(s₂)          -- else Error(expected_sort)
  infer(Σ, Γ, PI(A, B)) = SORT(prop_max(s₁, s₂))
```

the kernel extends the context by prepending `CTX_VAR(A)` before inferring B. prop_max is computed via a branch: if s₂ = 0, return SORT(0); else return SORT(max(s₁, s₂)).

### lam

```
rule (Π-intro):
  u = infer(Σ, Γ, A)
  require: u = SORT(_)           -- else Error(expected_sort): A must be a type
  T = infer(Σ, Γ:VAR(A), t)
  infer(Σ, Γ, LAM(A, t)) = PI(A, T)
```

result type is constructed via `cons(atom(0x02), cons(A, T))`.

### app

```
rule (Π-elim):
  F = infer(Σ, Γ, f)
  require: whnf(Σ, Γ, F) = PI(A, B)   -- else Error(expected_pi)
  check(Σ, Γ, a, A)
  infer(Σ, Γ, APP(f, a)) = subst(B, a)
```

the kernel calls whnf on F and checks the head tag is PI (0x02). if not, returns Error(expected_pi). result is `subst(B, a)` — the body type with the argument substituted.

### let

```
rule (Let):
  check(Σ, Γ, v, A)               -- value must have declared type
  T = infer(Σ, Γ:LET(A,v), b)    -- body inferred under extended context
  infer(Σ, Γ, LET(A, v, b)) = subst(T, v)
```

the context extension is `CTX_LET(A, v)` — the bound variable unfolds to v during whnf inside the body.

### ind

```
rule (Ind-form):
  desc = env_lookup(Σ, id)         -- IND_DESC(arity, sort, param_tel, constructors)
  require: len(params) = arity     -- else Error(type_mismatch)
  -- param_tel is a telescope PI(P₀, PI(P₁, ... PI(Pₙ₋₁, _) ...))
  -- check each param against its type in the telescope (with prior params substituted):
  for (pᵢ, Pᵢ) in zip(params, unroll_telescope(desc.param_tel, params)):
    check(Σ, Γ, pᵢ, Pᵢ)
  infer(Σ, Γ, IND(id, params)) = SORT(sort)
```

the sort of the inductive type comes directly from its descriptor. `unroll_telescope(tel, params)` steps through the PI-chain, substituting prior params into each successive type. Substitution is innermost-first (most recent param substituted first): `P₀`, `subst(P₁, p₀)`, `subst(subst(P₂, p₁), p₀)`, etc. The innermost-first order is required because `subst` replaces VAR(0), which after peeling i binders refers to the i-th (most recent) parameter, not the first.

### ctor

```
rule (Ind-intro):
  desc = env_lookup(Σ, id)
  ctor_type = instantiate(desc.constructors[k], params)
  infer(Σ, Γ, CTOR(id, k, args)) = apply_args(ctor_type, args)
```

`instantiate` substitutes the inductive's parameters into the constructor type telescope. `apply_args` applies the resulting function type to each argument, returning the final type after all arguments are consumed.

### elim

```
rule (Ind-elim):
  desc = env_lookup(Σ, id)           -- else Error(unknown_inductive)
  T_target = infer(Σ, Γ, target)
  require: whnf(Σ, Γ, T_target) = IND(id, params)   -- else Error(expected_ind)
  -- motive must map the target type to some sort
  T_motive = infer(Σ, Γ, motive)
  require: whnf(Σ, Γ, T_motive) = PI(IND(id, params'), SORT(s))   -- else Error(type_mismatch)
  require: def_eq(Σ, Γ, params, params')       -- motive params must match target params
  -- large elimination gate: Prop inductives may only eliminate into Type if proof-irrelevant
  -- "field types" means constructor argument types AFTER parameter instantiation
  if desc.sort = 0 and s > 0:
    require: len(desc.constructors) ≤ 1
    -- for each constructor k, check all field types (post-instantiate) are in Prop:
    for k in 0..len(desc.constructors):
      tel = instantiate(desc.constructors[k], params)
      for each PI(A, _) in tel: require: infer(Σ, Γ, A) = SORT(0)
    -- admitted: False (0 ctors), True (1 ctor, 0 fields), And (1 ctor, 2 Prop fields),
    --           Eq (1 ctor, 0 post-param fields), Accessible (1 ctor, Prop field)
    -- rejected: Or (2 ctors), Nat.le (2 ctors)
  -- each case[k] must have the type case_type computes
  for k in 0..len(desc.constructors):
    check(Σ, Γ, cases[k], case_type(desc, k, motive, params))
  infer(Σ, Γ, ELIM(id, motive, cases, target)) = APP(motive, target)
```

`case_type` is defined in § helper functions below. the large elimination gate prevents extracting data from proofs: inductives in Prop (`desc.sort = 0`) may only eliminate into Type (`s > 0`) when they have at most one constructor and all fields are Props — the proof-irrelevance condition. `False`, `True`, `And`, and `Eq` satisfy this; `Or` and `Nat.le` do not.

## helper functions

the following functions are called from the typing rules. each is a nox formula composition in the kernel.

### instantiate

substitutes the inductive's actual parameters into a constructor telescope. constructor types are stored with the inductive's `a` parameters as the outermost free variables (VAR(a-1) = first param, VAR(0) = last param). `params` is ordered outermost-first.

`IND_DESC` now includes a `param_tel` field:
```
IND_DESC(arity, sort, param_tel, constructors)
```
`param_tel` is a PI-telescope of length `arity` encoding the types of the inductive's parameters. this is used by the `ind` typing rule to check parameter arguments. constructor telescopes in `constructors` have the same `arity` outermost free variables (the parameters) before any constructor-specific fields.

```
instantiate(ctor_tel, params):
  t = ctor_tel
  for p in reverse(params):   -- p_{a-1} first (replaces VAR(0)), then p_{a-2}, ...
    t = subst(t, p)
  return t
  -- result: constructor type with no parameter free variables;
  --   remaining free variables are the constructor's own field types
```

### apply_args

steps a constructor type telescope through its arguments, checking each one:

```
apply_args(Σ, Γ, ctor_type, args):
  -- Σ and Γ are threaded from the enclosing infer/check invocation
  t = ctor_type
  for a in args:
    require whnf(Σ, Γ, t) = PI(A, B)   -- else Error(type_mismatch)
    check(Σ, Γ, a, A)
    t = subst(B, a)
  return t     -- the final return type after all args are substituted in
```

### recargs

for ι-reduction: for each constructor argument whose type is the same inductive, produce the recursive eliminator call. this is the `recargs` referenced in the whnf ι step in [[terms]].

```
recargs(Σ, Γ, id, motive, cases, ctor_tel_inst, args):
  -- Σ, Γ threaded from enclosing invocation
  result = []
  t = ctor_tel_inst
  for aᵢ in args:
    require whnf(Σ, Γ, t) = PI(Aᵢ, rest)
    if whnf(Σ, Γ, Aᵢ) = IND(id, _):
      result = result ++ [ELIM(id, motive, cases, aᵢ)]
    t = subst(rest, aᵢ)
  return result
```

### case_type

computes the expected type for the k-th case function. for each constructor field, emits a PI-binder; for each field of recursive inductive type `IND(id, _)`, also emits an induction hypothesis binder `APP(motive, field)`.

```
case_type(desc, k, motive, params):
  tel = instantiate(desc.constructors[k], params)
  -- tel = Π(a₀:A₀)(a₁:A₁)...(aₙ₋₁:Aₙ₋₁). IND(id, params)  [named notation]
  -- result type structure (named notation):
  --   Π(a₀:A₀), [Π(_ : motive a₀),]
  --   Π(a₁:A₁), [Π(_ : motive a₁),]
  --   ...,
  --   APP(motive, CTOR(id, k, [a₀, ..., aₙ₋₁]))
  --   where [Π(_ : motive aᵢ)] is present iff whnf(Aᵢ) = IND(id, _)
  return build(tel, motive, id, k, rev_fields=[])

build(tel, motive, id, k, rev_fields):
  match tel with
  | PI(Aᵢ, rest), whnf(Aᵢ) = IND(id, _) →
      -- recursive field: emit field binder then IH binder
      -- field aᵢ = VAR(0); IH type = APP(motive_shifted_1, VAR(0))
      ih = APP(shift(motive, 1), VAR(0))
      inner = build(shift(rest, 1), shift(motive, 2), id, k,
                    [VAR(1)] ++ shift_all(rev_fields, 2))
      return PI(Aᵢ, PI(ih, inner))
  | PI(Aᵢ, rest) →
      -- non-recursive field: emit field binder only
      inner = build(rest, shift(motive, 1), id, k,
                    [VAR(0)] ++ shift_all(rev_fields, 1))
      return PI(Aᵢ, inner)
  | _ →
      -- all fields collected; rev_fields = [aₙ₋₁, ..., a₀] (innermost first)
      return APP(motive, CTOR(id, k, reverse(rev_fields)))
```

`shift_all(list, n)` applies `shift(_, n)` to each element. the `shift(motive, d)` calls keep motive valid under d new PI-binders introduced above it.

## check

`check` reduces to `infer` plus definitional equality:

```
check(Σ, Γ, term, expected) =
  actual = infer(Σ, Γ, term)
  if def_eq(Σ, Γ, actual, expected) then Ok
  else Error(type_mismatch, actual, expected)
```

definitional equality (`def_eq`) is defined in [[terms]]. the kernel calls whnf on both sides before structural comparison.

## whnf in the kernel

the kernel's whnf implementation uses the `look` pattern for δ-unfolding of CTX_LET entries, and recursive compose chains for β and ι steps. whnf results are memoized by noun id using the `call` pattern (tag 0x01 = optimization hint): the prover caches (input_id → whnf_id) so repeated whnf calls on the same noun are O(1).

whnf terminates because:
- β reduces the λ count in the head
- ι reduces the structural size of the target (by the inductive's well-founded order)
- δ unfolds each definition at most once per whnf call (guarded by memo)

## error encoding

errors are atom nouns with a high tag bit:

| error | atom value |
|-------|-----------|
| unbound_variable | 0xE000 |
| expected_sort | 0xE001 |
| expected_pi | 0xE002 |
| expected_ind | 0xE003 |
| type_mismatch | 0xE004 |
| unknown_inductive | 0xE005 |
| constructor_out_of_range | 0xE006 |
| budget_exhausted | 0xE007 |

the kernel propagates errors upward via branch: any Error atom from a recursive call short-circuits and returns the error from the enclosing rule.

## nox pattern usage

each CIC rule maps to a composition of [[nox]] Layer 1 patterns:

| rule | primary patterns used |
|------|-----------------------|
| var | axis (navigate context list), compose (chain lookup steps) |
| sort | axis (read level), add (increment) |
| pi | axis, compose (two infer calls), branch (prop_max), cons (build result) |
| lam | axis, compose (infer A, extend ctx, infer t), cons |
| app | axis, compose (infer f, whnf, branch on tag, check a), compose (subst) |
| let | axis, compose (check v, extend ctx, infer b), compose (subst) |
| ind | look (env_lookup), axis, compose |
| ctor | look, axis, compose (instantiate, apply_args) |
| elim | look, axis, compose (case_type loop), cons |
| whnf | compose + branch on tag; call (memo) |
| def_eq | compose (two whnf calls), eq (noun equality), branch |
| subst | compose + branch per constructor; recursive |

the kernel is a single formula noun of approximately 2,500 nox IR nodes. it uses no `call` for search (only for memoization) and no `look` for BBG state — only the Σ lookup namespace.

## budget

the kernel runs under nox budget. each reduce() call costs 1 unit; multi-row patterns (inv, lt, bitwise, hash) cost more. for a well-typed term of size N (noun node count), the kernel budget is bounded by O(N²) in the worst case (deeply nested definitional equality with large terms). practical proofs run well within O(N log N).

budget is tracked by nox's built-in metering. if the budget is exhausted, the kernel returns Error(budget_exhausted). the prover may increase the budget and retry — exhaustion is not a soundness failure.
