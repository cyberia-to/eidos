---
tags: eidos, spec
crystal-type: spec
crystal-domain: eidos
status: draft
---
# surface

the user-facing language for eidos. surface syntax is what users write; the elaborator translates it to kernel terms (see [[terms]]). the elaborator is untrusted — bugs in it produce terms the kernel rejects, not false theorems.

## grammar

```
-- top-level declarations
Decl ::=
  | def   <Name> <Params> : <Type> := <Expr>
  | theorem <Name> <Params> : <Type> := <Proof>
  | lemma   <Name> <Params> : <Type> := <Proof>
  | axiom   <Name> : <Type>
  | inductive <Name> <Params> : <Sort> where <Ctors>
  | class   <Name> <Params> : <Sort> where <Fields>    -- typeclass declaration
  | instance <Type> where <Fields>                     -- typeclass instance
  | namespace <Name> <Decls> end
  | #check <Expr>
  | #print <Name>

-- typeclass fields (for class and instance bodies)
Field ::=
  | <Name> : <Type>                    -- method signature
  | <Name> : <Type> := <Expr>          -- method with default implementation

-- expressions (terms and types)
Expr ::=
  | <Name>                             -- variable or global reference
  | <Expr> <Expr>                      -- application (left-associative)
  | fun (<Binder>) => <Expr>           -- lambda abstraction
  | (<Binder>) -> <Expr>               -- dependent function type
  | <Expr> -> <Expr>                   -- non-dependent function type
  | let <Name> : <Type> := <Expr> ; <Expr>  -- local definition
  | match <Expr> with <Arms>           -- pattern match (sugar for ELIM)
  | ( <Expr> )                         -- grouping
  | _                                  -- hole (elaborator fills by unification)
  | Type                               -- TYPE_0
  | Type <Nat>                         -- TYPE_n
  | Prop                               -- PROP
  | <Nat>                              -- natural number literal
  | @<Name> <Expr>*                    -- explicit application (no implicit insertion)

-- binders
Binder ::=
  | <Name> : <Type>                    -- explicit argument
  | { <Name> : <Type> }               -- implicit argument
  | [ <Name> : <Type> ]               -- instance argument (typeclass)

-- constructor declarations
Ctor ::=
  | | <Name> : <Type>

-- pattern match arms
Arm ::=
  | | <Pattern> => <Expr>

Pattern ::=
  | <Name>                             -- constructor name
  | <Name> <Pattern>*                  -- constructor with sub-patterns
  | _                                  -- wildcard
```

application is left-associative: `f a b c` parses as `APP(APP(APP(f,a),b),c)`.

`->` is right-associative and non-dependent: `A -> B` elaborates to `PI(A, shift(B, 1))` where B has no free occurrence of the bound variable.

## name resolution

the elaborator maintains a name environment mapping surface names to kernel terms (global declarations) or de Bruijn depths (local binders).

```
NameEnv = List(Name, Binding)
Binding = | Local(depth)   -- de Bruijn: current_depth - depth - 1 gives the index
          | Global(term)   -- replaced by the full term (δ-reduces in kernel)
```

resolving a name at elaboration depth d:
- if `Local(d')`: emit `VAR(d - d' - 1)`
- if `Global(t)`: emit the global term (a reference noun pointing into Σ)

binders push to the name env and increment depth.

## implicit arguments

implicit binders `{x : A}` are not written at call sites. the elaborator inserts fresh metavariables and solves them by unification.

a metavariable `?m` is a hole in the term tree. after elaborating a full application, the elaborator runs constraint solving:

```
unify(Γ, ?m, t):
  if ?m is unsolved: assign ?m := t
  if ?m is solved to s: require def_eq(Γ, s, t)
```

unification is first-order (no higher-order unification). patterns:
- `?m` solved by any term not containing `?m` (occurs check)
- `APP(?m, x) = APP(f, a)` if x is a distinct variable: pattern unification, assign `?m := LAM(_, f[x:=VAR(0)])` (only if x appears exactly once)

if a metavariable remains unsolved after elaboration, it is reported as an elaboration error — the user must supply the argument explicitly or add a type annotation.

## elaboration algorithm

```
elab(NameEnv, depth, expr) → (kernel_term, inferred_type)
```

**advisory note**: the `inferred_type` returned by `elab` is computed by the elaborator itself (not by calling `infer` on the result at each step). it is *advisory* — used to thread type information through the elaboration of subexpressions. the actual soundness guarantee comes from the final `check(Σ, Γ, body_term, T_term)` kernel call at declaration elaboration. an elaborator bug that produces a wrong advisory type will cause the kernel call to fail — it cannot produce a false theorem.

### name

```
elab(env, d, Name(n)) =
  | Local(d') in env  → (VAR(d - d' - 1), look up type from context)
  | Global(t) in env  → (t, its declared type)
  | not found         → error(unknown_name, n)
```

### application

```
elab(env, d, App(f, a)) =
  (f_term, f_type) = elab(env, d, f)
  insert implicit args: while whnf(f_type) = PI({x:A}, B): insert ?m, apply
  (a_term, a_type) = elab(env, d, a)
  require whnf(f_type) = PI(A, B)
  unify(A, a_type)
  (APP(f_term, a_term), subst(B, a_term))
```

trailing implicit insertion: after the last explicit argument in a full application, any remaining implicit PI-binders in the result type are inserted automatically. for example, `f x` where `f : {a:A} → X → {b:B} → Y` inserts `{a}` before `x` and `{b}` after — yielding `APP(APP(APP(f, ?a), x_term), ?b)` with type `Y`. this insertion happens when the elaborated application is used in a position that determines the full type (e.g., as an argument or under `check`).

### lambda

```
elab(env, d, Fun(Binder(x, A), body)) =
  (A_term, A_sort) = elab(env, d, A)
  require A_sort = SORT(_)
  env' = env + Local(x, d)
  (body_term, body_type) = elab(env', d+1, body)
  (LAM(A_term, body_term), PI(A_term, body_type))
```

### pi

```
elab(env, d, Pi(Binder(x, A), B)) =
  (A_term, SORT(u)) = elab(env, d, A)
  env' = env + Local(x, d)
  (B_term, SORT(v)) = elab(env', d+1, B)
  (PI(A_term, B_term), SORT(prop_max(u, v)))
```

### let

```
elab(env, d, Let(x, A, v, body)) =
  (A_term, _) = elab(env, d, A)
  (v_term, v_type) = elab(env, d, v)
  unify(A_term, v_type)
  env' = env + Local(x, d)
  (body_term, body_type) = elab(env', d+1, body)
  (LET(A_term, v_term, body_term), subst(body_type, v_term))
```

### match (eliminator sugar)

`match target with | Ctor1 args1 => e1 | ...` elaborates to `ELIM`:

```
elab(env, d, Match(target, arms)) =
  (tg_term, tg_type) = elab(env, d, target)
  require whnf(tg_type) = IND(id, params)
  motive = fresh ?motive metavar
  cases = for each arm: elab case function
  (ELIM(id, motive, cases, tg_term), APP(motive, tg_term))
```

motive synthesis: the elaborator creates `?motive : IND(id, params) → ?result_type` as a fresh metavariable. when an expected return type is available (from the surrounding context), `?motive` is unified as `fun _ => expected_type` (non-dependent motive). when arm return types differ or the match is in an unannotated position, the user must provide: `match target return (fun x => T) with`. arm types are unified against `APP(?motive, arm_ctor_term)` — if two arms give incompatible types, the metavariable remains unsolved and an `unsolved_metavar` error is reported.

### hole

```
elab(env, d, Hole) = (?fresh_meta, ?fresh_type_meta)
```

both the term and its type are metavariables, to be solved by surrounding context.

## declaration elaboration

### def / theorem / lemma

```
elab_decl(def Name Params : T := body) =
  1. elab Params as a telescope of binders → (param_terms, extended_env)
  2. elab T in extended_env → T_term (must be a SORT)
  3. elab body in extended_env → body_term
  4. check(Σ, Γ_params, body_term, T_term)   -- kernel call
  5. if Ok: extend Σ with (Name ↦ LAM*(param_terms, body_term), type = PI*(param_terms, T_term))
```

`LAM*` and `PI*` fold a telescope of binders into nested LAM / PI terms.

`axiom` skips steps 3–4; the declared type is taken as given without a proof term.

### inductive

```
elab_decl(inductive Name Params : Sort where Ctors) =
  1. elab Params as telescope
  2. elab Sort → SORT(u)
  3. for each Ctor: elab constructor type in env extended with Name (for recursive occurrences)
  4. check positivity: Name appears only strictly positively in all ctor argument types
  5. if Ok: add IND_DESC(arity, u, constructors) to Σ under id = hemera(desc_noun)
```

positivity check ensures the inductive type is well-founded. a type T appears strictly positively in A when:
- T does not appear in A (trivially positive)
- A = PI(B, C) and T does not appear in B and T appears positively in C
- A = IND(other_id, ...) and T does not appear in the parameters

## instance resolution

instance arguments `[x : C A]` in a type are resolved automatically by the elaborator. when elaborating a term that requires an instance of class `C` at type `A`:

```
resolve_instance(C, A, depth=0):
  if depth > 32: error(instance_depth_limit, C, A)   -- prevent infinite search
  candidates = all `instance` declarations in scope with head class C
  filter: keep those whose declared type unifies with C A (up to definitional equality)
  -- for each candidate, recursively resolve any instance arguments it requires:
  resolved = []
  for cand in candidates:
    inst_args = collect_instance_args(cand)   -- the [_:D B] parameters of this instance
    ok = true
    for (D, B) in inst_args:
      sub = resolve_instance(D, B, depth+1)   -- recursive instance search
      if sub fails: ok = false; break
    if ok: resolved = resolved ++ [apply(cand, sub_instances)]
  | exactly one resolved → insert as the implicit argument
  | zero resolved        → error(missing_instance, C, A)
  | multiple resolved    → error(ambiguous_instance, C, A)
```

instances are registered in Σ alongside regular definitions, tagged as instances. lookup is by type-class head name (`C`) and then filtered by unification of the full instance type. the depth limit of 32 prevents infinite search on cyclic or diverging instance chains. resolution happens after implicit argument insertion. the resolved instance is a kernel term subject to normal type checking.

## namespace

declarations inside `namespace N ... end` are prefixed: `N.name`. the name environment maps both the short name (within the namespace) and the full qualified name (globally).

## commands

`#check expr` — elaborate `expr`, report its type (does not add to Σ).

`#print Name` — display the kernel term and type for `Name` from Σ.

## notation

operators and syntactic sugar expand to standard library terms before elaboration. the elaborator performs a single-pass substitution keyed on the operator token or pattern.

| notation | expands to |
|----------|-----------|
| `a + b` | `Nat.add a b` |
| `a * b` | `Nat.mul a b` |
| `n ≤ m` | `Nat.le n m` |
| `n < m` | `Nat.lt n m` |
| `a = b` | `Eq a b` |
| `P ↔ Q` | `Iff P Q` |
| `P ∧ Q` | `And P Q` |
| `P ∨ Q` | `Or P Q` |
| `¬P` | `Not P` |
| `a :: l` | `List.link a l` |
| `[]` | `List.nil` |
| `[a, b, c]` | `List.link a (List.link b (List.link c List.nil))` |
| `l₁ ++ l₂` | `List.append l₁ l₂` |
| `a ∈ l` | `List.Mem a l` |
| `a && b` | `Bool.and a b` |
| `a \|\| b` | `Bool.or a b` |
| `!a` | `Bool.not a` |
| `(a, b)` | `Prod.mk a b` |
| `A × B` | `Prod A B` |
| `⟨a, b⟩` | `Sigma.mk a b` |
| `(x : A) × B x` | `Sigma (fun x => B x)` |
| `≠` | `fun a b => Not (Eq a b)` |
| `∃ x, P x` | `Exists (fun x => P x)` |
| `n` (Nat literal) | `Nat.next (Nat.next ... Nat.zero ...)` (n applications) |

notation is not extensible in the surface language — the table above is fixed. user-defined notation must be emitted by a macro preprocessor before the elaborator runs (not specified here).

## elaboration errors

| error | meaning |
|-------|---------|
| unknown_name | name not in scope |
| expected_sort | type annotation is not a universe |
| expected_pi | application target is not a function type |
| expected_ind | match target is not an inductive type |
| unsolved_metavar | implicit argument could not be inferred |
| occurs_check | metavariable would be self-referential |
| positivity_violation | inductive type is not strictly positive |
| kernel_rejection | kernel returned an error after elaboration |

elaboration errors are reported with source locations. kernel_rejection includes the kernel error code.
