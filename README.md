eidos (εἶδος — form, essence, type in ancient Greek) is the proof assistant for [[cyber]]. CIC type theory over [[Goldilocks field]] elements. the type checker is a [[nox]] program — executing it produces a [[zheng]] STARK certificate. every proved theorem becomes a [[cyberlink]] in the [[cybergraph]]. zero trusted setup. post-quantum. cybergraph-native.

eidos closes the loop: [[zheng]] proves execution correct, eidos proves programs correct. together they make [[cyber]] civilization-grade software possible.

```
LAYER              │ ROLE                              │ LANGUAGE
───────────────────┼───────────────────────────────────┼──────────────────
term encoding      │ CIC terms as nox nouns            │ spec
CIC kernel         │ type checker as nox patterns      │ nox IR (~200 rules)
elaborator         │ surface syntax → kernel terms     │ rs
tactic engine      │ proof construction                │ rs
standard library   │ Nat, Bool, List, Vec, theorems    │ eidos
zheng bridge       │ wrap type check in STARK          │ rs
cybergraph bridge  │ store proof as cyberlink          │ rs
```

## trust boundary

TCB = 16 nox patterns + zheng math (SuperSpartan + Brakedown + sumcheck). the CIC kernel is written directly as nox patterns — not through Trident, not through Rs. the trust chain bottoms out at nox's 16 deterministic patterns without passing through any unverified compiler.

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
