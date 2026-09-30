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

The headline Lean statements are listed below; every name is in the
`MonoidProduct` namespace, and the source paths are relative to the
repository root. Constants are explicit throughout.

| Theorem | Statement (informal) | Source |
| --- | --- | --- |
| `advPM_prodFun_le_breadth` | Commutative aperiodic `M`: `ADV±(Prod_{M,G,n}) ≤ 16√(n·min{n, β_G})` | `MonoidProduct/Width/Breadth.lean` |
| `commutative_qQuery_sandwich` | Commutative aperiodic `M` with an identity letter, `n, β ≥ 1`: `√(n·min{n,β})/72 ≤ Q_{1/3} ≤ min{n, 2^18·√(n·min{n,β})}` | `MonoidProduct/Quantum/CommutativeLower.lean` |
| `commutative_qQuery_lower_total` | The lower bound over the full alphabet of a nontrivial `M` | `MonoidProduct/Quantum/CommutativeLower.lean` |
| `breadth_le_indexK_paper` | `x^{k+1} = x^k`: `β ≤ 2^64·(k+1)(log₂\|M\|+1)·log(log₂\|M\|+2)` | `MonoidProduct/Width/PaperForms.lean` |
| `cappedLen_qQuery_theta` | Capped counters `M_{k,r}`: `Q_{1/3} = Θ(√(n·min{n,kr}))`, explicit constants | `MonoidProduct/Capped/LengthBreadth.lean` |
| `Matroid.matroidBasis_minWeight_and_qQuery` | Minimum-weight basis of a rank-`r` matroid from `n` weighted records, `Q_{1/3} ≤ min{n, 2^18·√(nr)}` | `MonoidProduct/Matroid/Quantum.lean` |
| `ordered_qQuery_third_le_quasipoly` | Stably ordered `M`, breadth bound `b`: `Q_{1/3} ≤ min{n, √(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)}}`, `C = 2^17` | `MonoidProduct/Quantum/OrderedLogApplications.lean` |
| `ordered_truthful_core_alg_quasipoly` | The same bound (with `C = 2^18`) for an algorithm that returns a product-preserving record of at most `b` positions with probability `9/10`, truthful on every branch | `MonoidProduct/Quantum/OrderedTruthful.lean` |
| `GenStock.gstockProfit_qQuery_third_le` | Best time to buy and sell stock over any ordered price group: `Q_{1/3} ≤ min{n, 2^116·√n·L_n^{10}}` | `MonoidProduct/Stock/GeneralPrices.lean` |
| `utrop_qQuery_third_le_paper` | Unitriangular tropical `k×k` products: the ordered bound with `β ≤ C(k+1,3)` | `MonoidProduct/Tropical/Unitriangular.lean` |
| `aperiodic_qQuery_final_exact` | Aperiodic `M` of order `N`: `Q_{1/3} ≤ min{n, √n·L(n)^{2^18·(N·ln(N+2))^{1/3}}}`, `L(n) = 2 + log₂(n+2)` | `MonoidProduct/Quantum/CubeRootApplications.lean` |
| `aperiodic_qQuery_intro` | The introduction's form `min{n, √n·ln(n+2)^{2^20·(N·ln(N+2))^{1/3}}}` | `MonoidProduct/Quantum/CubeRootApplications.lean` |
| `aperiodic_semigroup_oneHotQQuery_intro` | Aperiodic semigroups, with `N = \|S\|+1`, in the one-hot value-oracle model | `MonoidProduct/Quantum/CubeRootApplications.lean` |
| `ags_oneHotQQuery_le_display_logb` | The AGS bound `√n·(2^55(\|M\|+1)^6(log₂(n+1)+3)^2)^{d_J(M)+1}` | `MonoidProduct/Quantum/AGSApplications.lean` |
| `envD_dyck_qQuery_lower` | Dyck monoids `M_k`: `Q_{1/3} ≥ c₀·(2^{1/20})^{d_J(M_k)}·√n` for `1 ≤ k ≤ log₂ n` | `MonoidProduct/Quantum/EnvelopeDisplays.lean` |
| `envD_aperiodic_envelope` | The worst-case aperiodic envelope is `√n·2^{Θ(N^{1/3})}` up to the power of `L(n)` | `MonoidProduct/Quantum/EnvelopeDisplays.lean` |

## Library structure

The root module `MonoidProduct.lean` imports the whole library. The
directories under `MonoidProduct/` are:

| Directory | Contents |
| --- | --- |
| `Width/` | Product breadth (`breadth`, `IsBreadthBound`), incremental summaries and the essential-width adversary theorem (total and promise forms), stable orders, and the commutative breadth bounds: idempotent, index two, and general index via the Rao–BCW sunflower bound. `Width/PaperForms.lean` and `Width/SmallClauses.lean` state several results in the paper's exact form. |
| `Semilattice/`, `Promise/` | Commutative idempotent products and join closures; the instance-sensitive promise bound. |
| `Capped/` | Capped counters `M_{k,r}`: breadth `kr`, the matching adversary lower bound, and the `R`-trivial depth. |
| `Matroid/` | Greedy bases, the greedy-basis monoid, weighted records, and minimum-weight bases of general, uniform, partition, graphic and vector matroids. |
| `Ordered/` | Stably ordered monoids: records, seeded sampling and merging, median frontiers, tree sampling, and rank doubling. |
| `Stock/`, `Tropical/` | Best time to buy and sell stock (integer and general prices) and unitriangular tropical matrices, including the path formula. |
| `UT/`, `Simon/` | Boolean unitriangular monoids `UT_k(𝔹)` and Simon's theorem for `J`-trivial monoids. |
| `Aperiodic/` | Green's relations and ideals, the AGS decomposition, prefix, suffix and infix search, the AGS induction, and `R`-trivial monoids. |
| `Aperiodic/CubeRoot/` | The cube-root bound: regular actions and owners, the action compiler, principal factors and Munn coordinates, the fixed-apex peel, radical lifts, and the size recurrence. |
| `Dyck/` | Dyck-language adversary lower bounds and the Dyck transition monoid `M_k` (normal form, Green structure, breadth, contracted algebra). |
| `Infix/` | The typed clean-infix adversary and uniform bounds for Rees matrix and Brandt monoids. |
| `Trichotomy/`, `Layer/` | The fixed-monoid trichotomy, the two-layer lower bound, and the aperiodicity-index lower bound. |
| `Quantum/` | Query-complexity consequences of the adversary results, in the native and one-hot oracle models: the main theorems, applications, division monotonicity, the envelope, and the Dyck lower bounds. The `Acceptance*.lean` files pin the exact form of the main statements. |

`WidthCerts.lean` and `SemilatticeCerts.lean` repackage the essential-width
and semilattice duals as `HasDual` certificates for the query extraction.

The main results live in `Quantum/CommutativeLower.lean` and
`Width/Breadth.lean` (commutative monoids),
`Quantum/OrderedLogApplications.lean` and `Quantum/OrderedTruthful.lean`
(stably ordered monoids), `Quantum/CubeRootApplications.lean` (aperiodic
monoids and semigroups), and `Matroid/Quantum.lean` (matroid bases).

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
