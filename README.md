eidos (εἶδος — form, essence, type in ancient Greek) is the proof assistant for [[cyber]]. CIC type theory over [[Goldilocks field]] elements. the type checker is a [[nox]] program — executing it produces a [[zheng]] certificate. every proved theorem becomes a [[cyberlink]] in the [[cybergraph]]. zero trusted setup. post-quantum. cybergraph-native.

eidos closes the loop: [[zheng]] proves execution correct, eidos proves programs correct. together they make [[cyber]] civilization-grade software possible.

```
LAYER              │ ROLE                              │ LANGUAGE
───────────────────┼───────────────────────────────────┼──────────────────
term encoding      │ CIC terms as nox nouns            │ spec
CIC kernel         │ type checker as nox patterns      │ nox IR (~200 rules)
elaborator         │ surface syntax → kernel terms     │ rs
tactic engine      │ proof construction                │ rs
standard library   │ Nat, Bool, List, Vec, theorems    │ eidos
zheng bridge       │ wrap type check in zheng          │ rs
cybergraph bridge  │ store proof as cyberlink          │ rs
```

## CIC type theory

the Calculus of Inductive Constructions is a formal system where types and propositions are the same thing, and proofs are programs. a type `T` is simultaneously a proposition; a term of type `T` is simultaneously a proof that `T` holds. this is the [[Curry-Howard correspondence]] scaled to full mathematics.

four constructs cover all of mathematics:

- Π-types (dependent functions) — a function whose return type may depend on its argument. `(x : A) → B(x)`. universal quantification `∀x, P(x)` is a Π-type.
- inductive types — user-defined recursive types with named constructors and a structural eliminator. `Nat`, `List`, `Vec n`, `Fin n`, equality — all inductive. the eliminator is the only way to consume an inductive type, which is what guarantees termination.
- universes — `Type₀ : Type₁ : Type₂ : …`. every type lives at some universe level. universe polymorphism lets a definition quantify over levels.
- structural recursion — recursive functions must recurse on a structurally smaller argument. the termination checker enforces this syntactically. no general recursion, no divergence.

definitional equality in CIC goes beyond syntactic identity: β-reduction (apply a function), δ-reduction (unfold a definition), ι-reduction (eliminate an inductive constructor), and η-expansion (function extensionality for Π-types) are all definitionally equal. the type checker decides equality by reduction to a normal form.

in eidos, CIC is instantiated over the [[Goldilocks field]] (p = 2⁶⁴ − 2³² + 1). terms are [[nox]] nouns — binary trees of field elements. the universe hierarchy is finite and field-bounded. the structural recursion measure is axis traversal depth on nouns.

## trusted computing base

a TCB is the set of components whose correctness must be assumed rather than proved — the floor beneath which verification does not reach. everything outside the TCB is checked; bugs there cannot produce false theorems.

eidos TCB = 16 nox reduction patterns + [[zheng]] proof system math (SuperSpartan + Brakedown + sumcheck protocol).

the CIC kernel encodes ~200 typing rules as nox patterns written by hand. executing the kernel on a claimed proof either accepts or rejects. [[zheng]] then certifies that execution itself was correct — producing a certificate anyone can verify. the certificate attests: "nox ran these patterns on this term and accepted."

the trust chain is: CIC rules (human-auditable nox patterns) → nox execution (16 deterministic reductions) → zheng certificate (proven-correct sumcheck). the elaborator and tactic engine sit outside this chain — they produce candidate terms that the kernel checks. a buggy elaborator produces a term the kernel rejects. it cannot produce a term the kernel falsely accepts.

## trust boundary

## proof certificate

every proved theorem P with proof π produces:

```
axon = H(check_kernel, H(π, P))
cyberlink: axon → ok
```

the [[cybergraph]] is the universal theorem database. every theorem proved by anyone is memoized. proving the same theorem twice costs zero — the second prover reads the existing cyberlink.

## dependency graph

```
nebu (field)
  ↓
hemera (hash)
  ↓
nox (VM) ← runs the type checker kernel
  ↓
zheng (proofs) ← certifies the type check execution
  ↓
eidos (proof assistant) ← this repo
  ↓
bbg (state) ← stores proof certificates as cyberlinks
```

see [[CIC]] for type theory background, [[zheng]] for proof machinery, [[nox]] for the VM
