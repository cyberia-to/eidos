# Eidos

Eidos is an experimental proof assistant with a Rust type-checking kernel,
elaborator, tactic engine and command-line interface. Its current useful boundary
is strict checking of closed proof terms in a fixed Nat/Bool/Eq/Pos/BNat fragment.
It is being used to check explicit algebraic statements and concrete arithmetic
certificates for [Hemera](https://github.com/cyberia-to/hemera).

The current workspace version is `0.1.0`. This is a development snapshot;
the first packaged release remains work in [the roadmap](roadmap/README.md).
[Snapshot validation and release scope](audit/release-2026-09-12.md) distinguish
the working checker from the planned integrations.

## Run a proof

The library has no external Rust dependencies. From this repository:

```sh
cargo run --locked --offline -- check --strict examples/binary.ei
cargo run --locked --offline -- check --strict examples/reduction.ei
```

`cargo install --path cli --locked` installs the local `eidos` binary.
Working commands are `repl`, `eval <expression>`, `check <file.ei>` and
`check --strict <file.ei>`. `--help` prints the current command list.
The listed `search` and `verify` commands are unimplemented stubs that exit
unsuccessfully. `--version` is not implemented in this snapshot.

Use `check --strict` for admission-free checking. Ordinary `check` permits
explicit axioms and is a broader experimental elaboration path.

## What strict checking establishes

Strict checking follows transitive imports, elaborates declarations and rechecks
their closed terms and types in a fresh fixed environment. It rejects axioms,
`sorry`, unresolved holes, opaque constants, user-defined inductives and standard
name shadowing. Import cycles and depths above 64 are rejected.

Binary positive and nonnegative integers use kernel-reduced constructor terms.
A concrete reduction certificate checks `modulus * quotient + remainder = input`
and `remainder < modulus`. Host arithmetic can propose witnesses; acceptance
comes from the kernel. Explicit law parameters remain assumptions of their
theorems. These statements do not prove Hemera's complete implementation or its
cryptographic security.

The trusted base is the Rust kernel, reduction/substitution, fixed inductive
descriptors and Rust compilation/execution. General inductive validation,
resource-bounded normalization and universal machine-arithmetic refinement
remain open. See [strict checking](specs/strict-checking.md) and
[binary arithmetic](specs/binary-arithmetic.md).

## Planned integration

Executing the checker in nox, certifying that execution with zheng and storing
proof links in cybergraph are design goals. This snapshot checks proofs locally
in Rust and produces no zheng certificate. The public `certificate` module still
contains prototype serialization and an FNV-1a placeholder hash; its artifacts
are unsuitable as cryptographic certificates or durable content identities.

The kernel itself has no independent soundness proof. A successful type check
does not establish post-quantum security of a cryptographic construction.

## Workspace and validation

| Directory | Role |
|---|---|
| `rs/` | `cyber-eidos` library |
| `cli/` | `eidos` binary |
| `examples/` | Strict binary arithmetic examples |
| `specs/` | Kernel, syntax and checking contracts |
| `audit/` | Dated validation and release evidence |

The full test suite currently embeds proof fixtures from sibling `../nox` and
`../prysm` repositories. A standalone clone builds the library and CLI, but needs
those fixtures to compile all tests. The snapshot audit pins their exact commits
and records passing formatting, strict lint, documentation and functional checks.

Eidos (εἶδος) means form or essence in ancient Greek.
