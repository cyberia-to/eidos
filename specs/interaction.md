---
tags: eidos, spec
crystal-type: spec
crystal-domain: eidos
status: draft
---
# interaction

the display layer of eidos. nothing here produces a proof term or affects the kernel. two implementations with identical semantics but different interaction layers produce the same certificates but different user experiences.

## proof state

the proof state is rendered after every tactic step. canonical format:

```
<n> goal(s)

case <label>
<name₁> : <type₁>
<name₂> : <type₂>
...
⊢ <goal type>
```

- `⊢` is the turnstile — separates hypotheses from the goal
- hypotheses are listed oldest-first (outermost binder first)
- the focused goal is rendered first; remaining goals follow, separated by blank lines
- when `n = 1`, the `case` label is omitted if there is no named case
- when `n = 0`, display: `proof complete`

example — two goals after `induction n`:

```
2 goals

case zero
⊢ P 0

case next
n : Nat
ih : P n
⊢ P (next n)
```

## hypothesis display

each hypothesis renders as `name : type`. the type is displayed in surface syntax (not de Bruijn), using the names in scope at that point.

local definitions (`have h : T := e` or `clear`-exempt lets) render as:

```
h : T := e
```

the `:= e` part signals the hypothesis unfolds — the kernel sees a CTX_LET; the user sees the value.

inaccessible hypotheses (auto-generated names from `induction`/`cases` when the user did not supply `with` names) render with a dagger suffix:

```
n† : Nat
ih† : P n†
```

the `†` signals: this name was generated, not declared. use `rename` (see below) or `with` in the original tactic to replace it.

## goal labels

every inductive type is defined by its constructors — the ways to build a value of that type. when you apply `induction` or `cases`, the proof splits into one subgoal per constructor. each subgoal is labeled with the constructor's short name.

the four most common constructors and what they mean:

| label | full name | meaning |
|-------|-----------|---------|
| `zero` | `Nat.zero` | the number 0; base case of the naturals |
| `next` | `Nat.next` | the number after n; `next zero` = 1, `next (next zero)` = 2 |
| `nil` | `List.nil` | the empty list `[]` |
| `link` | `List.link` | a list built from a head element and a tail list; `link 1 (link 2 nil)` = `[1, 2]` |

`induction n` on `n : Nat` splits into `zero` and `next` because Nat has exactly those two constructors. `induction l` on `l : List A` splits into `nil` and `link`.

example — `induction n` on a goal `⊢ P n`:

```
2 goals

case zero
⊢ P 0

case next
n : Nat
ih : P n        -- induction hypothesis: P holds for n
⊢ P (next n)    -- must prove P holds for the next number
```

example — `induction l` on a goal `⊢ Q l`:

```
2 goals

case nil
⊢ Q []

case link
head : A
tail : List A
ih : Q tail     -- induction hypothesis: Q holds for the tail
⊢ Q (link head tail)
```

the label lets you direct tactics to a specific subgoal by name:

```
induction n
case zero =>
  exact base_proof
case next n ih =>
  exact step_proof n ih
```

without `case`, tactics apply to the first open goal in the list.

when nested induction produces the same label twice, a numeric suffix disambiguates: `case next.1`, `case next.2`.

`with` names the constructor arguments inline, skipping the need for separate `case` blocks:

```
induction n with
| zero      => exact base_proof
| next n ih => exact step_proof n ih
```

## focus navigation

the focused goal is always the first in the list. tactics apply to the focused goal. after a tactic, the first remaining goal becomes the new focus.

### case

directs subsequent tactics to a specific named subgoal. does not affect the proof term.

```
case <label> (with <Name>*)? => <Block>
```

```
case zero =>
  exact Nat.zero_le _

case next n ih =>
  apply Nat.next_le_next
  exact ih
```

`with` renames the constructor arguments for this case — replaces the auto-generated or default names for the scope of the block. `case` fails if no subgoal carries the given label.

### all_goals

applies a tactic to every remaining goal. display-equivalent to `<;>` but not sequenced from a prior tactic.

```
all_goals <Tactic>
```

useful for closing trivial residual goals: `all_goals exact rfl`.

## rename

renames a hypothesis in the current goal's local context. no proof term effect.

```
rename <Name> => <Name>
```

```
rename n† => n
rename ih† => ih
```

the source name must exist in the local context. the target name must not clash with an existing name in scope. after renaming, subsequent tactics refer to the hypothesis by its new name.

`rename` is the only tactic defined in this spec — all others are in [[tactics]].

## query commands

commands are run at the top level or inline during tactic proofs (prefixed with `#`). they produce output but do not modify `Σ` or the proof state.

### #check

elaborates an expression and displays its type.

```
#check <Expr>
```

output:

```
<expr> : <type>
```

if elaboration fails, displays the elaboration error with location. does not call the kernel — elaboration is sufficient for type display.

### #print

displays the full definition of a global name from `Σ`.

```
#print <Name>
```

output format:

```
<kind> <Name> : <type>
  := <term>
```

`<kind>` is one of: `def`, `theorem`, `axiom`, `inductive`. for inductives, lists constructors with their types. the term is printed in surface syntax (de Bruijn converted back to named form).

### #eval

reduces an expression to normal form and displays the result.

```
#eval <Expr>
```

runs `whnf` then full reduction on the elaborated term. the result is displayed in surface syntax. only meaningful for terms of computable type (Nat, Bool, List, etc.) — for propositions, the normal form is the proof term itself.

### #search

queries the [[cybergraph]] for existing proofs of a claim. eidos-specific.

```
#search <Type>
```

computes `CLAIM(T)` (the claim noun for the elaborated type), then queries bbg namespace 0 for cyberlinks of the form `axon → OK` where `axon = hemera(KERNEL_ID || CLAIM(T) || _)` — using domain separator `0xA1` (proof-event domain; see [[certificate]]).

output when found:

```
found <n> proof(s) of <type>
  axon: <hash>  prover: <neuron>  block: <height>
  ...
```

output when not found:

```
no proof of <type> in cybergraph
```

`#search` does not verify the STARK — it reports existence. use `#verify <axon>` to fetch and check the full certificate.

### #verify

fetches a proof certificate from the cybergraph by axon and runs the zheng verifier.

```
#verify <axon>
```

output:

```
certificate valid   -- zheng verifier accepted
  claim:  <type>
  prover: <neuron>
  kernel: <kernel_id>
```

or:

```
certificate invalid
  reason: <verifier error>
```

## error format

all errors follow a common structure:

```
error[<code>]: <kind>
  --> <file>:<line>:<col>
  |
  | <source line>
  |       ^^^^^ <annotation>
  |
  = expected: <expected type>
  = got:      <actual type>
  = note:     <additional context>
```

error codes map to the kernel error atoms (see [[kernel]]) plus elaboration-layer errors:

| code | source | meaning |
|------|--------|---------|
| E000 | kernel | unbound variable |
| E001 | kernel | expected sort |
| E002 | kernel | expected pi (applied non-function) |
| E003 | kernel | expected inductive |
| E004 | kernel | type mismatch |
| E005 | kernel | unknown inductive |
| E006 | kernel | constructor index out of range |
| E007 | kernel | budget exhausted |
| E010 | elab | unknown name |
| E011 | elab | unsolved metavariable |
| E012 | elab | occurs check failed |
| E013 | elab | positivity violation |
| E020 | tactic | tactic failed |
| E021 | tactic | no matching hypothesis (assumption) |
| E022 | tactic | no contradicting hypotheses (contradiction) |
| E023 | tactic | case label not found |
| E024 | tactic | hypothesis still in use (clear) |

the `expected` / `got` fields are populated for type mismatch errors (E004). source locations are tracked through elaboration so kernel errors report back to the original surface syntax position.

E000–E007 are kernel errors: produced by `infer` / `check` and encoded as atom nouns (see [[kernel]]). they affect soundness — if the kernel returns one of these, no certificate is issued.

E010–E013 are elaboration errors: the kernel was never called. they indicate malformed surface syntax or unsolvable implicit arguments.

E020–E024 are library-tactic errors: they arise from the `contradiction`, `assumption`, `cases`, and `clear` tactics in the tactic library, not from the kernel. they indicate that a tactic strategy failed but the proof is not necessarily unprovable — a different tactic may succeed.

## information on hover

implementations that support an editor protocol (LSP or similar) expose:

- hovering a name: display its type (same as `#check`)
- hovering a tactic: display the proof state before and after
- hovering an inductive: display its constructors
- hovering a `#search` result: display the certificate summary

these are implementation guidelines, not normative requirements. the canonical interaction is the command-line output format above.
