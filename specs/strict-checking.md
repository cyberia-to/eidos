# Strict proof checking

`eidos check --strict file.ei` and `surface::check_strict_path` check a file
and its transitive imports. `check_strict_source` accepts source without imports.
The result contains the checked declarations, elaborated terms, and dependency
paths. A declaration is reported only after its closed body and type have been
rechecked in a fresh fixed environment. Theorems must inhabit `Prop`.

The supported inductives are Nat, Bool, Eq and binary Pos. The standard surface names in
this fragment are individually kernel-checked during initialization. Unsupported
bootstrap arithmetic is unavailable. Explicit theorem parameters may state laws;
such a theorem remains conditional on those parameters.

The strict checker rejects axioms, `sorry`, user inductives, unresolved metas,
opaque constants, `#check`, duplicate names and standard-name shadowing. Imports
use the same policy recursively. Paths are canonicalized; import cycles and
depths above 64 fail; a shared dependency is checked once. A failed check returns
no module. `sorry` also fails in ordinary checking, rather than being counted as
a proved theorem. Ordinary checking still supports explicit axioms.

Trusted base: Rust kernel, reduction/substitution, the fixed Nat/Bool/Eq/Pos
descriptors and Rust compilation/execution. This is neither an independent
checker nor a kernel soundness proof. General inductive environment validation,
bounded normalization, modular machine arithmetic and implementation refinement
are future obligations. The import-depth limit is not a general resource bound.

## Pi universes

For `A : Sort(u)` and `B : Sort(v)`, `Pi(A,B)` inhabits `Sort(0)` only when
`v=0`; otherwise it inhabits `Sort(max(u,v))`. In particular `proof → Nat`
is a data type. This follows kernel.md; the old symmetric `prop_max` rule in
terms.md and the Rust implementation was incorrect.

## Hemera

The sibling Hemera checker uses this public API for its algebraic proofs.
Its Rust/model comparisons remain separately labeled tests, not formal
refinement proofs. Run `python3 ../hemera/proofs/check.py` after changes to
the checker or kernel.
