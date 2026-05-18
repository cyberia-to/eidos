---
tags: eidos, spec
crystal-type: spec
crystal-domain: eidos
status: draft
---
# terms

CIC term language for eidos. every program and every proof is a term. the type checker reasons about terms; the kernel accepts or rejects them.

## grammar

nine constructors cover all of mathematics:

```
Term ::=
  | VAR(i)                             -- de Bruijn index
  | SORT(u)                            -- universe at level u
  | PI(A, B)                           -- dependent function type  Πx:A. B
  | LAM(A, t)                          -- abstraction              λx:A. t
  | APP(f, a)                          -- application              f a
  | LET(A, v, b)                       -- local definition         let x:=v:A in b
  | IND(id, params)                    -- inductive type applied to parameters
  | CTOR(id, k, args)                  -- k-th constructor of inductive id
  | ELIM(id, motive, cases, target)    -- eliminator for inductive id
```

all variables use de Bruijn indices. index 0 refers to the innermost binder; each enclosing binder increments the index. no alpha-equivalence needed — two terms are syntactically equal iff their noun encodings are equal.

## universes

universes form a cumulative hierarchy:

```
PROP   = SORT(0)    -- propositions; impredicative
TYPE_0 = SORT(1)    -- first data universe
TYPE_1 = SORT(2)    -- second data universe
TYPE_u = SORT(u+1)  -- general form
```

PROP is impredicative: `PI(A, B)` lives in PROP whenever B lives in PROP, regardless of where A lives. this is what makes proof terms compact — logical connectives do not universe-inflate.

universe level arithmetic:

```
prop_max(0, v) = 0        -- PI into PROP stays in PROP
prop_max(u, 0) = 0
prop_max(u, v) = max(u,v) -- when both nonzero
```

`PI(A, B)` lives in `SORT(prop_max(u, v))` where `A : SORT(u)` and `B : SORT(v)`.

universe levels are [[Goldilocks field]] elements (p = 2⁶⁴ − 2³² + 1). the hierarchy is bounded by p — sufficient for any finite development. the kernel enforces: `u < p` at every SORT node. `SORT(u + 1)` uses field addition; if u = p − 1 the addition wraps to 0, which the kernel rejects as `expected_sort` (universe overflow). in practice no mathematical development reaches even SORT(100).

## noun encoding

terms encode as [[nox]] nouns. a nox noun is an atom (field element, 32-bit word, or hash) or a cell (pair of nouns). every term maps to a unique noun shape via the tag system below.

term constructor tags are field atoms 0x00 through 0x08:

| tag | constructor | noun encoding |
|-----|-------------|---------------|
| 0x00 | VAR | `cons(atom(0x00), atom(i))` |
| 0x01 | SORT | `cons(atom(0x01), atom(u))` |
| 0x02 | PI | `cons(atom(0x02), cons(A, B))` |
| 0x03 | LAM | `cons(atom(0x03), cons(A, t))` |
| 0x04 | APP | `cons(atom(0x04), cons(f, a))` |
| 0x05 | LET | `cons(atom(0x05), cons(A, cons(v, b)))` |
| 0x06 | IND | `cons(atom(0x06), cons(atom(id), params))` |
| 0x07 | CTOR | `cons(atom(0x07), cons(atom(id), cons(atom(k), args)))` |
| 0x08 | ELIM | `cons(atom(0x08), cons(atom(id), cons(motive, cons(cases, target))))` |

`axis(2, noun)` extracts the tag (head of the outer cell). `axis(3, noun)` extracts the payload.

`id` for IND and CTOR is a field atom — the [[hemera]] hash of the inductive type's declaration noun. `k` for CTOR is a field atom — the zero-based constructor index.

## list encoding

`params`, `args`, and `cases` are list nouns:

```
NIL        = atom(0)      -- empty list; atom, not cell
NODE(h, t) = cons(h, t)   -- h is a term or descriptor, t is a list
```

NIL is an atom; NODE is a cell. no tag needed to distinguish them — the shapes differ. list elements (terms) are always cells (tagged), so a bare `atom(0)` unambiguously marks the end.

## global environment

the global environment Σ maps inductive ids to their descriptors. a descriptor noun encodes:

```
IND_DESC(arity, sort, param_tel, constructors) =
  cons(atom(arity), cons(atom(sort), cons(param_tel, constructors)))
```

- `arity`: number of parameters (field atom)
- `sort`: universe level of the inductive type (field atom)
- `param_tel`: PI-telescope of length `arity` encoding parameter types (`PI(P₀, PI(P₁, ... _))`)
- `constructors`: list of constructor telescope nouns

each constructor telescope is a list of parameter type terms (the first `arity` entries are the inductive's parameters) followed by the constructor's own field types, ending in the return type `IND(id, params)`. the kernel reads descriptors via the [[nox]] `look` pattern (namespace 0 = particles, treated as the eidos descriptor store).

## context

a local typing context Γ is a list of entries, ordered innermost-first (de Bruijn order):

```
CTX_EMPTY            = atom(0xD2)   -- distinct tag; 0xD0/0xD1 are entry heads
CTX_VAR(A, rest)    = cons(cons(atom(0xD0), A), rest)   -- variable of type A
CTX_LET(A, v, rest)  = cons(cons(atom(0xD1), cons(A, v)), rest)  -- local definition x:=v:A
```

`CTX_EMPTY = atom(0xD2)` uses a dedicated tag distinct from `NIL = atom(0)` used for list encoding. the kernel reads context and list nouns in different argument positions and never confuses them, but giving CTX_EMPTY its own tag removes the ambiguity entirely.

`ctx_lookup(Γ, i)` descends i steps into the list and returns the entry. the function returns the raw entry (CTX_VAR or CTX_LET) without shifting; callers (e.g., the `var` rule) apply `shift(A, i+1)` after lookup to account for the i+1 binders crossed.

## substitution

`subst(t, s)` replaces `VAR(0)` with `s` throughout `t` and decrements all other free indices:

```
subst(VAR(0),    s) = s
subst(VAR(i),    s) = VAR(i − 1)                    when i > 0
subst(SORT(u),   _) = SORT(u)
subst(PI(A, B),  s) = PI(subst(A, s), subst(B, shift(s, 1)))
subst(LAM(A, t), s) = LAM(subst(A, s), subst(t, shift(s, 1)))
subst(APP(f, a), s) = APP(subst(f, s), subst(a, s))
subst(LET(A,v,b),s) = LET(subst(A,s), subst(v,s), subst(b, shift(s,1)))
subst(IND(id,ps),s) = IND(id, map(λt. subst(t,s), ps))
subst(CTOR(id,k,as),s) = CTOR(id, k, map(λt. subst(t,s), as))
subst(ELIM(id,m,cs,tg),s) = ELIM(id, subst(m,s), map(λt. subst(t,s), cs), subst(tg,s))
```

`shift(t, n)` increments all free indices in `t` by `n`. implemented via a depth-tracked traversal: a variable at depth d is free iff `i ≥ d`; free variables get `+n`.

`shift_all(list, n)` applies `shift(_, n)` to each element of a list: `map(λt. shift(t, n), list)`.

## reduction

four reduction rules define definitional equality. the kernel applies them during type checking; no proof term is required.

### β-reduction

```
APP(LAM(A, t), a)  →β  subst(t, a)
```

applying a lambda to an argument substitutes the argument for the bound variable.

### δ-reduction

let bindings unfold:

```
LET(A, v, b)  →δ  subst(b, v)
```

context definitions (CTX_LET entries) unfold when a variable referencing them is reduced.

### ι-reduction

the eliminator on a constructor fires:

```
ELIM(id, motive, cases, CTOR(id, k, args))
  →ι  apply_case(cases[k], args ++ recargs(id, motive, cases, ctor_tel_inst, args))
```

`apply_case(f, xs)` is left-fold application: `APP(APP(... APP(f, x₀) ..., xₙ₋₂), xₙ₋₁)`. `recargs` is defined in [[kernel]] § helper functions; it requires `ctor_tel_inst = instantiate(desc.constructors[k], params)` where `desc` and `params` come from the target's inferred type `IND(id, params)` — so ι-reduction in whnf has access to the descriptor via Σ (see whnf signature below).

### η-expansion

functions are equal up to η:

```
LAM(A, APP(f, VAR(0)))  →η  f    when VAR(0) not free in f
```

the kernel uses η-equality during definitional equality checking, not as a rewrite. two terms are definitionally equal if their η-long forms reduce to the same WHNF.

## weak head normal form

`whnf(Σ, Γ, t)` reduces the outermost redex until the head is neutral (a variable, sort, pi, inductive, or constructor):

```
whnf(Σ, Γ, APP(f, a)) =
  match whnf(Σ, Γ, f) with
  | LAM(_, b)  →  whnf(Σ, Γ, subst(b, a))      -- β
  | f'         →  APP(f', a)                    -- neutral

whnf(Σ, Γ, LET(A, v, b))  =  whnf(Σ, Γ, subst(b, v))   -- δ (let-binding)

whnf(Σ, Γ, VAR(i)) =
  match ctx_lookup(Γ, i) with
  | CTX_LET(_, v)  →  whnf(Σ, Γ, shift(v, i+1))   -- δ (context definition)
  | _              →  VAR(i)                         -- neutral

whnf(Σ, Γ, ELIM(id, m, cs, tg)) =
  match whnf(Σ, Γ, tg) with
  | CTOR(id, k, args)  →
      desc = env_lookup(Σ, id)
      params = (infer(Σ, Γ, CTOR(id, k, args)) gives IND(id, params))
      tel   = instantiate(desc.constructors[k], params)
      rargs = recargs(id, m, cs, tel, args)
      whnf(Σ, Γ, apply_case(cs[k], args ++ rargs))    -- ι
  | tg'  →  ELIM(id, m, cs, tg')                       -- neutral

whnf(Σ, Γ, t) = t     -- SORT, PI, LAM, IND, CTOR: already whnf
```

`apply_case(f, xs)` is left-fold application: `foldl APP f xs`.

whnf needs both Σ (to look up inductive descriptors for ι-reduction) and Γ (to δ-unfold CTX_LET variables). the kernel memoizes whnf results by (Σ_hash, Γ_hash, noun_id) triple using the [[hemera]] hash — including both environment hashes ensures correctness under different unfolding environments.

## definitional equality

`def_eq(Σ, Γ, t, s)` holds when `t` and `s` are definitionally equal in context Γ:

```
def_eq(Σ, Γ, t, s) =
  t' = whnf(Σ, Γ, t)
  s' = whnf(Σ, Γ, s)
  structural_eq(Σ, Γ, t', s')
```

`structural_eq` compares whnf forms constructor-by-constructor. LET never appears in WHNF (it reduces by δ before returning). ELIM on a neutral target is a valid WHNF and must be compared structurally:

```
structural_eq(Σ, Γ, SORT(u),    SORT(v))    = (u == v)
structural_eq(Σ, Γ, VAR(i),     VAR(j))     = (i == j)
structural_eq(Σ, Γ, APP(f,a),   APP(g,b))   = def_eq(Σ,Γ,f,g) ∧ def_eq(Σ,Γ,a,b)
structural_eq(Σ, Γ, PI(A,B),    PI(C,D))    = def_eq(Σ,Γ,A,C) ∧ def_eq(Σ,Γ:VAR(A),B,D)
structural_eq(Σ, Γ, LAM(A,t),   LAM(B,s))   = def_eq(Σ,Γ,A,B) ∧ def_eq(Σ,Γ:VAR(A),t,s)
structural_eq(Σ, Γ, IND(id,ps), IND(id,qs)) = all(def_eq(Σ,Γ,p,q) for p,q in zip(ps,qs))
structural_eq(Σ, Γ, CTOR(id,k,as), CTOR(id,k,bs)) = all(def_eq(Σ,Γ,a,b) for a,b in zip(as,bs))
structural_eq(Σ, Γ, ELIM(id,m,cs,tg), ELIM(id,m',cs',tg')) =
  def_eq(Σ,Γ,m,m') ∧ all(def_eq(Σ,Γ,c,c') for c,c' in zip(cs,cs')) ∧ def_eq(Σ,Γ,tg,tg')
structural_eq(_, _, _, _) = false  -- base case before η fallback
```

η-equality: the kernel uses lazy (adaptive) η — it η-expands only when `structural_eq` fails and one side is already a LAM. the fallback cases appended to the match:

```
structural_eq fallback:
  | LAM(A, body), other →
      def_eq(Σ, Γ:VAR(A), body, APP(shift(other, 1), VAR(0)))
  | other, LAM(B, body) →
      def_eq(Σ, Γ:VAR(B), APP(shift(other, 1), VAR(0)), body)
  | _, _ → false
```

`shift(other, 1)` lifts all free indices in `other` past the new binder. `APP(shift(other, 1), VAR(0))` is the η-expansion: apply `other` to the fresh variable. terms are not converted to η-long form before comparison — expansion happens on demand.

**termination**: def_eq terminates because whnf is terminating (β reduces the λ-spine; ι reduces structural noun size; δ is memoized per noun-id), and structural_eq recurses structurally on WHNF forms. the η-fallback is bounded: after one η-expansion, the inner `def_eq` call has a LAM on both sides or neither, so η does not re-trigger.
