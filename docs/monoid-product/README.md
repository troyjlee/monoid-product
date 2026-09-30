# MonoidProduct: quantum query complexity of semigroup products

<!-- Paper link: add the arXiv URL or DOI of the paper once available. -->

A Lean 4 and Mathlib formalization of *The quantum query complexity of the
semigroup product problem* by Troy Lee and Miklos Santha. The problem is to
compute a product `x₁ ⋯ xₙ` in a fixed finite semigroup, where one query
reveals one input element and the multiplication table is known. The
development builds on the adversary bounds and quantum query model of the
[QuantumQueryComplexity](https://github.com/troyjlee/quantum-query-complexity)
library.

The [paper-correspondence record](PAPER_CORRESPONDENCE.md) lists each
paper result with its Lean statement and any difference in hypotheses,
constants or scope.

## Main results

The *product breadth* `β` of a semigroup is the smallest bound such that
every input word has a subsequence of at most `β` letters with the same
product. The paper's main results are:

- **Commutative aperiodic monoids.** For a nontrivial finite commutative
  aperiodic monoid, the bounded-error quantum query complexity is
  `Θ(min{n, √(nβ)})`. If the monoid `M` has aperiodicity index `k`, then
  `β = O(k log(|M|+1) log log(|M|+2))`, and products of capped counters
  nearly match this bound.
- **Stably ordered monoids.** For a monoid with a stable partial order whose
  minimum is the identity, the bounded-error quantum query complexity is at
  most `√(n+1) · ((β+2) log(n+2))^O(log(β+2))`. Applications include the
  best time to buy and sell stock problem and products of unitriangular
  tropical matrices of fixed dimension, each with `Õ(√n)` queries.
- **Finite aperiodic semigroups.** For a finite aperiodic semigroup of order
  `N−1`, the bounded-error quantum query complexity is at most
  `min{n, √n · log^O((N log(N+2))^(1/3))(n+2)}`, improving the bound of
  Aaronson, Grier and Schaeffer. Bounded-depth Dyck languages give
  aperiodic monoids requiring `√n · 2^Ω(N^(1/3))` queries in the relevant
  parameter range.

The table of Lean statements, with their source files, is to be added.

| Theorem | Statement (informal) | Source |
| --- | --- | --- |

## Build

Install [elan](https://lean-lang.org/install/), then run from the repository root:

```sh
lake exe cache get
lake build MonoidProduct MonoidProductChecks
```

The package pins Lean **4.35.0-rc2** and Mathlib **v4.35.0-rc2** in
[lean-toolchain](../../lean-toolchain) and
[lake-manifest.json](../../lake-manifest.json). The library depends on
[QuantumQueryComplexity](https://github.com/troyjlee/quantum-query-complexity)
and on the Rao–BCW sunflower bound (`Sunflower.RaoBCW`) from the `Sunflower`
library of [TCS formalizations](https://github.com/troyjlee/tcs-formalizations),
each pinned to a fixed commit in the [lakefile](../../lakefile.toml).

## Verification

The proof library is sorry-free.
[MonoidProductChecks.lean](../../MonoidProductChecks.lean), included in the
default build, uses `#guard_msgs` to require exactly
`[propext, Classical.choice, Quot.sound]` for the headline theorems. A failed
guard fails the build. The GitHub Actions workflow runs the default
build, builds `MonoidProduct` and `MonoidProductChecks` explicitly,
and runs `python3 scripts/export-monoid.py --check-only`, which rejects
imports from outside the published modules, Mathlib, QuantumQueryComplexity
and Sunflower.

## References

- S. Aaronson, D. Grier, L. Schaeffer, *A quantum query complexity
  trichotomy for regular languages*, FOCS 2019.
- A. Ambainis, K. Balodis, J. Iraids, K. Khadiev, V. Kļevickis,
  K. Prūsis, Y. Shen, J. Smotrovs, J. Vihrovs, *Quantum lower and upper
  bounds for 2D-grid and Dyck language*, MFCS 2020.

## License

Copyright © 2026 Troy Lee. Released under the
[Apache License 2.0](../../LICENSE).
