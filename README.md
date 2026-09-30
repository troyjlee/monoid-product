# MonoidProduct: quantum query complexity of semigroup products in Lean

[![CI](https://github.com/troyjlee/monoid-product/actions/workflows/ci.yml/badge.svg)](https://github.com/troyjlee/monoid-product/actions/workflows/ci.yml)
<!-- Zenodo DOI badge: add after the first release is archived, e.g.
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX) -->

A Lean 4 and Mathlib formalization of *The quantum query complexity of the
semigroup product problem* by Troy Lee and Miklos Santha. The problem is to
compute a product `x₁ ⋯ xₙ` in a fixed finite semigroup, where one query
reveals one input element and the multiplication table is known.

The [library guide](docs/monoid-product/README.md) states the main results and
their Lean counterparts; the
[paper correspondence](docs/monoid-product/PAPER_CORRESPONDENCE.md) maps each
result of the paper to its Lean statement and records differences in
hypotheses, constants, or scope.

## Main results

The *product breadth* `β` of a semigroup is the smallest bound such that
every input word has a subsequence of at most `β` letters with the same
product.

- **Commutative aperiodic monoids.** For a nontrivial finite commutative
  aperiodic monoid, the bounded-error quantum query complexity is
  `Θ(min{n, √(nβ)})`. A monoid `M` with aperiodicity index `k` has
  `β = O(k log(|M|+1) log log(|M|+2))`, and products of capped counters
  nearly match this bound.
- **Stably ordered monoids.** For a monoid with a stable partial order whose
  minimum is the identity, the bounded-error quantum query complexity is at
  most `√(n+1) · ((β+2) log(n+2))^O(log(β+2))`. Applications include the best
  time to buy and sell stock problem and products of unitriangular tropical
  matrices of fixed dimension, each with `Õ(√n)` queries.
- **Finite aperiodic semigroups.** For a finite aperiodic semigroup of order
  `N−1`, the bounded-error quantum query complexity is at most
  `min{n, √n · log^O((N log(N+2))^(1/3))(n+2)}`. Bounded-depth Dyck languages
  give aperiodic monoids requiring `√n · 2^Ω(N^(1/3))` queries in the
  relevant parameter range.

## Dependencies

The library uses Lean **4.35.0-rc2** and Mathlib **v4.35.0-rc2**, pinned in
[lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json).
It depends on two further Lake packages, each pinned to a fixed commit in the
[lakefile](lakefile.toml):

- [QuantumQueryComplexity](https://github.com/troyjlee/quantum-query-complexity),
  for the quantum query model, adversary duality and composition, and the
  conversion of dual certificates into algorithms;
- [TCS formalizations](https://github.com/troyjlee/tcs-formalizations), for
  its `Sunflower` library, which provides the Rao–Bell–Chueluecha–Warnke
  sunflower bound (`Sunflower.RaoBCW`).

All three packages share the same Lean toolchain and Mathlib revision.

## Build

Install [elan](https://lean-lang.org/install/), then run from the repository
root:

```sh
lake exe cache get
lake build
```

The cache command fetches compiled Mathlib. The default build compiles the
`MonoidProduct` library and the `MonoidProductChecks` axiom checks, together
with the modules they import from QuantumQueryComplexity and Sunflower.
`LEAN_NUM_THREADS=1` is useful on machines with limited memory.

## Verification

The proof library is sorry-free.
[MonoidProductChecks.lean](MonoidProductChecks.lean), part of the default
build, uses `#guard_msgs` to require that each headline theorem depends on
exactly `[propext, Classical.choice, Quot.sound]`, the axioms of ordinary
classical mathematics in Lean. A new axiom or a `sorry` fails the build.

CI builds both targets and runs

```sh
python3 scripts/export-monoid.py --check-only
```

which scans the Lean sources and rejects imports outside the library,
Mathlib, QuantumQueryComplexity, Sunflower, and the Lean core.

Lean checks the encoded statements and proofs; comparing those statements
and definitions with the paper also requires mathematical interpretation,
which the paper correspondence records.

## License and attribution

Apache License 2.0. Formalization by Troy Lee, with AI-assisted development
using Claude and Codex. [CITATION.cff](CITATION.cff) provides citation
metadata for the software; please also cite the paper by Lee and Santha for
the mathematical results.
