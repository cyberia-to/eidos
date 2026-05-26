# eidos v0.1.0 — first anchor release

## Context

eidos has solid bones: Cargo workspace (`rs/` library + `cli/` binary), CIC kernel + elaborator + tactic engine, 8 spec files, 139 lib tests, and 27+ theorems verified across `nox/proofs/` and `prysm/proofs/`. Replacement-plan phases 1–5 complete: the Lean→eidos port is done. What's missing is the **product packaging** that turns a working library into a release.

The reference is `~/cyber/hemera/` (v0.3.0): workspace + clean public API + multi-command CLI + Diataxis docs + `specs/` + `roadmap/` + CHANGELOG + `vectors/` + LICENSE + GitHub Actions CI. v0.1.0 means: a third party can `cargo install`, read the README, follow a tutorial, write and check a proof, and trust the result.

This plan delivers v0.1.0 in ~27 pomodoros (4–5 sessions), with explicit cuts so the release is **honest about scope**: no half-implemented subcommands, no claimed features that aren't ready, no overpromised STARK/cybergraph integration.

## Pitch sentence (for README hero)

> **eidos is a proof assistant whose type checker is a verifiable program — a small CIC kernel designed to be re-executed and certified by the nox VM, so every checked proof carries a path to its own STARK certificate.**

For tighter contexts: cut after the em-dash.

## Scope: cut / keep / defer

| item | decision | reason |
|---|---|---|
| `eidos verify` subcommand | **CUT** | blocked on zheng — no half-features in CLI |
| `eidos search` subcommand | **CUT** | blocked on bbg — no half-features in CLI |
| `certificate` public module | **DEMOTE** to `pub(crate)` or feature-gated | FNV-1a stub must not masquerade as hemera |
| `cli/src/pretty.rs:134` non-exhaustive `has_free_at` match | **FIX (P0)** | `cargo test --workspace` is currently broken; add `Term::EqSubst` + `Term::Const` arms |
| `kernel.rs` (620 LOC) | **SPLIT** | exceeds CLAUDE.md 500-LOC limit; this is the TCB — do carefully |
| `tactic.rs` (616 LOC) | **SPLIT** | exceeds limit |
| Display impls for `kernel::Error`, `ElabError`, `CheckError`, `RunError` | **ADD** | dogfooding unblock; today CLI uses `{:?}` Debug format |
| Source spans `(file, line, col)` through `CheckError` | **ADD** | lexer already tracks positions — thread through |
| `--version`, `--help` flags | **ADD** | minimum CLI hygiene |
| `eidos init <name>` scaffold | **DEFER** | nice-to-have |
| `vectors/v0.1.0/` frozen corpus | **ADD** | locks release contract for the kernel |
| `specs/terms.md`, `kernel.md`, `surface.md` → `status: stable` | **ADD** | honest "which parts of the spec are frozen" |
| `specs/tactics.md`, `stdlib.md`, `certificate.md`, `interaction.md` | **KEEP draft** | they will still evolve |
| `docs/` Diataxis tree (tutorials, guides, reference, explanation) | **ADD** | none exists today |
| `examples/*.ei` (3–4 files) | **ADD** | README links here |
| README rewrite (pitch + workspace + install + quick start + CLI) | **ADD** | current README is conceptual only |
| `CHANGELOG.md`, `LICENSE`, `roadmap/` | **ADD** | release plumbing |
| `.github/workflows/ci.yml` | **ADD** | clippy `-D warnings`, fmt, tests, docs, **vectors** |
| T3.1 `sort_permutation_invariant` axiom | **KEEP**, document | same gap as original Lean; honest in CHANGELOG |
| Path deps to nox/hemera in `rs/Cargo.toml` | **KEEP commented** | eidos is stand-alone for v0.1.0 |
| STARK proof generation, cybergraph link, LSP, T3.1 mergeSort theory | **DEFER** | tracked in `roadmap/` |
| `bench/` crate | **DEFER** | no perf claim in v0.1.0 |
| `nox model grounding` (Model.ei axiomatizes 4 ops) | **DEFER**, disclose | `docs/explanation/nox-model-status.md` is honest |

## Work breakdown (dependency order)

Pomodoro = 30 min. Total ≈ 27 pomodoros = 4.5 sessions.

### M0 — Unbreak the build (1 pom)
- **W0.1** Fix `cli/src/pretty.rs:134` `has_free_at` non-exhaustive match: add `Term::Const(_)` and `Term::EqSubst(p, h, x)` arms. Run `cargo test --workspace` and confirm green.

### M1 — TCB hygiene: split oversized files (3 pom)
- **W1.1** Split `rs/src/kernel.rs` (620 LOC) into `kernel/{mod.rs, infer.rs, check.rs, sort.rs, ind.rs}`. Keep public API identical. **TCB-sensitive — preserve exact semantics.** (2 pom)
- **W1.2** Split `rs/src/tactic.rs` (616 LOC) into `tactic/{mod.rs, state.rs, run.rs, combinators.rs}`. (1 pom)

### M2 — Error messages with source spans (5 pom)
- **W2.1** `Display for kernel::Error` using `pretty::pp` on embedded terms; show goal/context where available. (1 pom)
- **W2.2** `Display for ElabError`, `surface::CheckError`, `tactic_runner::RunError`. Walk codebase for `format!("{:?}", e)` / `eprintln!("...{:?}...", e)` and switch to `{}`. (1 pom)
- **W2.3** Thread source spans from `surface/lexer.rs` through parser and `check.rs` into `CheckError`. (2 pom)
- **W2.4** Format errors `eidos: error: file.ei:12:5: <message>` Unix-style; audit every example by hand. (1 pom)

### M3 — CLI polish + stub removal (2 pom)
- **W3.1** Remove `cmd_search`, `cmd_verify` from `cli/src/main.rs` (and from `usage()`). (0.5 pom)
- **W3.2** Add `--version` (from `CARGO_PKG_VERSION`) and richer `--help`. Hand-roll, no clap (keep deps minimal). (1 pom)
- **W3.3** Exit codes: 0 success, 1 user error, 2 internal. Document in `docs/reference/cli.md`. (0.5 pom)

### M4 — Vectors directory + frozen corpus (1.5 pom)
- **W4.1** Create `vectors/v0.1.0/{nox,prysm}/` and copy current `.ei` files. Add `vectors/README.md` with provenance table (source repo, source path, commit SHA at copy, theorem count). (0.5 pom)
- **W4.2** New test in `surface/check.rs`: walk `vectors/v0.1.0/**/*.ei` via `check_path`, assert all pass. Keep the existing `include_str!` sibling-repo tests too (upstream tripwire). (1 pom)

### M5 — Spec promotion (1 pom)
- **W5.1** Set `status: stable` and add `frozen-in: v0.1.0` to `specs/{terms,kernel,surface}.md`. Leave the other four `draft`. Update `specs/README.md` index table accordingly.

### M6 — Documentation: Diataxis tree (8 pom ≈ 1.3 sessions)
- **W6.1** `docs/tutorials/01-hello-proof.md` — install → write `add_zero : ∀n, n + 0 = n` → run `eidos check` → success. (2 pom)
- **W6.2** `docs/guides/write-inductive-type.md` (1 pom)
- **W6.3** `docs/guides/use-omega.md` (1 pom)
- **W6.4** `docs/guides/port-from-lean.md` — translation table for tactics + types. (1 pom)
- **W6.5** `docs/reference/tactics.md` — one entry per shipped tactic. (1 pom)
- **W6.6** `docs/reference/stdlib.md` — one section per submodule under `rs/src/stdlib/`. (1 pom)
- **W6.7** `docs/reference/cli.md` — exhaustive invocation reference. (0.5 pom)
- **W6.8** `docs/explanation/tcb.md` — what's in the TCB, what isn't. (0.5 pom)
- **W6.9** `docs/explanation/nox-model-status.md` — honest writeup of axiomatized vs proved. (0.5 pom)
- **W6.10** `docs/README.md` — Diataxis index, links to all four quadrants. (0.5 pom)

### M7 — README + LICENSE + CHANGELOG + roadmap entries (3 pom)
- **W7.1** Rewrite `README.md`: pitch → workspace table → Install (`cargo install --path cli`) → Quick Start (5-line `.ei` + `eidos check` output) → CLI usage examples → links to `docs/` and `specs/`. (1.5 pom)
- **W7.2** `LICENSE` file at repo root. Match hemera's format. (0.25 pom)
- **W7.3** `CHANGELOG.md` v0.1.0 section. Disclose T3.1 axiom and deferred items. (0.5 pom)
- **W7.4** `roadmap/` standalone proposals: `stark-certificates.md`, `cybergraph-link.md`, `nox-model-grounding.md`, `mergeSort-theory.md`, `lsp-integration.md`. Each: motivation, prerequisites, sketch. (0.75 pom)

### M8 — CI workflow (1.5 pom)
- **W8.1** `.github/workflows/ci.yml`: jobs `cargo test --workspace`, `cargo clippy --workspace -- -D warnings`, `cargo fmt --check`, `cargo doc --workspace --no-deps`. Template off `~/cyber/hemera/.github/workflows/ci.yml`. (1 pom)
- **W8.2** CI step: build `eidos` and run `eidos check` on every file in `vectors/v0.1.0/`. (0.5 pom)

### M9 — examples/ (1 pom)
- **W9.1** `examples/{hello,nat_lemmas,inductives,tactics_tour}.ei` — 4 files, ≤30 lines each, all check clean. README links here.

### M10 — Release ceremony (1.5 pom)
- **W10.1** Audit `Cargo.toml` metadata: `description`, `repository`, `homepage`, `keywords`, `categories`, `rust-version` (MSRV). Both `rs/` and `cli/`.
- **W10.2** `cargo publish --dry-run` for both crates.
- **W10.3** Write release notes from CHANGELOG.
- **W10.4** Tag `v0.1.0`, push, watch CI.

## Critical files to modify

- `cli/src/pretty.rs` — P0 build break (non-exhaustive `Term` match at `has_free_at`)
- `rs/src/kernel.rs` — TCB-sensitive split (620 → directory)
- `rs/src/tactic.rs` — split (616 → directory)
- `rs/src/lib.rs` — demote `certificate` from public re-exports
- `rs/src/surface/check.rs` — extend `CheckError` with source spans, add vectors test
- `rs/src/surface/lexer.rs` — surface span info upward
- `cli/src/main.rs` — remove stubs, add `--version`/`--help`, switch `{:?}` to `{}`
- `README.md` — full rewrite
- `specs/{terms,kernel,surface}.md` — frontmatter promotion
- new: `docs/**`, `vectors/v0.1.0/**`, `examples/**`, `roadmap/*.md`, `LICENSE`, `CHANGELOG.md`, `.github/workflows/ci.yml`

## Release criteria checklist

**Build & test**
- [ ] `cargo build --workspace` zero warnings
- [ ] `cargo test --workspace` 100% pass (not just `--lib`)
- [ ] `cargo clippy --workspace -- -D warnings` clean
- [ ] `cargo fmt --check` clean
- [ ] `cargo doc --workspace --no-deps` clean
- [ ] All `.rs` files ≤ 500 lines
- [ ] No `{:?}` on user-facing error paths

**CLI**
- [ ] `eidos --version` prints `eidos 0.1.0`
- [ ] `eidos --help` documents only the three real subcommands
- [ ] `eidos repl`, `eidos eval`, `eidos check` work
- [ ] `eidos search` and `eidos verify` removed
- [ ] Errors formatted `file:line:col: message`
- [ ] Exit codes 0 / 1 / 2 consistent

**Tests & vectors**
- [ ] `vectors/v0.1.0/` exists with frozen corpus + provenance README
- [ ] CI step runs `eidos check` on every file in `vectors/v0.1.0/`
- [ ] `include_str!` sibling-repo tests still pass

**Documentation**
- [ ] `README.md` rewritten with pitch + workspace + install + quick start + CLI
- [ ] `docs/tutorials/01-hello-proof.md` works step-by-step on fresh clone
- [ ] `docs/guides/` has ≥ 3 how-tos
- [ ] `docs/reference/{tactics,stdlib,cli}.md` complete
- [ ] `docs/explanation/{tcb,nox-model-status}.md` honest
- [ ] `examples/` has 3–4 checking `.ei` files

**Specs**
- [ ] `specs/{terms,kernel,surface}.md` `status: stable`, `frozen-in: v0.1.0`
- [ ] Other specs remain `status: draft`

**Release plumbing**
- [ ] `Cargo.toml`: version, repository, description, keywords, MSRV
- [ ] `LICENSE` at root
- [ ] `CHANGELOG.md` v0.1.0 section
- [ ] `roadmap/` with deferred items documented
- [ ] `.github/workflows/ci.yml` runs on push + PR
- [ ] `cargo publish --dry-run` succeeds

**Honesty checks**
- [ ] T3.1 `sort_permutation_invariant` axiom disclosed in CHANGELOG
- [ ] `certificate.rs` not in public re-exports
- [ ] No claim of STARK certification, cybergraph integration, or LSP in README
- [ ] Model.ei axiomatization disclosed in `docs/explanation/nox-model-status.md`
