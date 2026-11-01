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

The applications of the commutative bound are formalized as well: a function
of a set of records whose strong certificates have at most `b` elements costs
`O(min{n, √(nb)})` queries, which gives minimum-weight matroid bases and, for
graphs on a known vertex set, the component partition, two-colourings, cycle
detection, planarity, every fixed proper minor-closed class (through Mader's
theorem), and the edge- and vertex-failure profiles, whose adjacency-matrix
cost is `Θ(min{v², v^{3/2}√k})`.

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
| `Certificates.certificate_breadth` | For `f : Finset U → O`: `β_{A_f}(M_f) = β(M_f) = b_f(U)`, the largest minimum strong-certificate size | `MonoidProduct/Certificates/Breadth.lean` |
| `Certificates.strongCertificate_qQuery_le_min_sqrt` | `f` of the nonnull records among `n`: `Q_{1/3} ≤ min{n, 2^18·√(n·b_f(U))}` | `MonoidProduct/Certificates/Quantum.lean` |
| `Matroid.matroidBasis_minWeight_and_qQuery` | Minimum-weight basis of a rank-`r` matroid from `n` weighted records, `Q_{1/3} ≤ min{n, 2^18·√(nr)}` | `MonoidProduct/Matroid/Quantum.lean` |
| `Graph.connectedComponents_strongCertificateSize_le` | The component partition of a graph on `v` vertices has strong certificates of at most `v − 1` edges | `MonoidProduct/Graph/Components.lean` |
| `Graph.twoColorings_strongCertificateSize_le` | The set of all proper two-colourings: certificates of at most `v` edges | `MonoidProduct/Graph/TwoColorings.lean` |
| `Graph.sparseYes_strongCertificateSize_le` | A property whose yes-instances have at most `L` edges: `b ≤ min{C(v, 2), L + 1}` | `MonoidProduct/Graph/Sparse.lean` |
| `Graph.qMatrix_le_two_mul_qList` | The adjacency-matrix model costs at most twice the edge-list model with `C(v, 2)` entries | `MonoidProduct/Graph/QueryModels.lean` |
| `Graph.planarity_strongCertificateSize_le` | Planarity (rotation systems of genus `0`): `b ≤ min{C(v, 2), 3v − 5}` | `MonoidProduct/Graph/PlanarCertificate.lean` |
| `Graph.IsPlanar.wagner_easy` | A planar graph on a finite vertex type has no `K₅` minor and no `K₃,₃` minor, as planarity is closed under minors (`Graph.IsPlanar.of_minor`) | `MonoidProduct/Graph/Wagner.lean` |
| `Graph.wagner_iff` | Wagner's theorem: a graph on a finite vertex type is planar (has a spherical rotation system) exactly when it has neither a `K₅` minor nor a `K₃,₃` minor; the converse is `Graph.wagner_hard`, first for `3`-connected graphs (`Graph.wagner_threeConnected`) | `MonoidProduct/Graph/Wagner.lean`, `MonoidProduct/Graph/WagnerConverse.lean` |
| `Graph.minorClosed_strongCertificateSize_le_linear` | Every fixed proper minor-closed class: `b ≤ C·v` with `C` depending only on the class | `MonoidProduct/Graph/SparseClasses.lean` |
| `Graph.exists_vertexFailureCertificate` | A subgraph with at most `2kv` edges and the same partition after every deletion of fewer than `k` vertices | `MonoidProduct/Graph/VertexCertificate.lean` |
| `Graph.edgeFailureProfile_qMatrix_theta`, `Graph.vertexFailureProfile_qMatrix_theta` | Edge- and vertex-failure profiles, `v ≥ 2`: `(1/10000)·min{v², v√(vk)} ≤ Q_matrix ≤ 2^18·min{v², v√(vk)}` | `MonoidProduct/Graph/FailureLower.lean`, `MonoidProduct/Graph/VertexQueries.lean` |
| `ordered_qQuery_third_le_quasipoly` | Stably ordered `M`, breadth bound `b`: `Q_{1/3} ≤ min{n, √(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)}}`, `C = 2^17` | `MonoidProduct/Quantum/OrderedLogApplications.lean` |
| `ordered_truthful_core_alg_quasipoly` | The same bound (with `C = 2^18`) for an algorithm that returns a product-preserving record of at most `b` positions with probability `9/10`, truthful on every branch | `MonoidProduct/Quantum/OrderedTruthful.lean` |
| `GenStock.gstockProfit_qQuery_third_le` | Best time to buy and sell stock over any ordered price group: `Q_{1/3} ≤ min{n, 2^116·√n·L_n^{10}}` | `MonoidProduct/Stock/GeneralPrices.lean` |
| `utrop_qQuery_third_le_paper` | Unitriangular tropical `k×k` products: the ordered bound with `β ≤ C(k+1,3)` | `MonoidProduct/Tropical/Unitriangular.lean` |
| `aperiodic_qQuery_final_exact` | Aperiodic `M` of order `N`: `Q_{1/3} ≤ min{n, √n·L(n)^{2^18·(N·ln(N+2))^{1/3}}}`, `L(n) = 2 + log₂(n+2)` | `MonoidProduct/Quantum/CubeRootApplications.lean` |
| `aperiodic_qQuery_intro` | The introduction's form `min{n, √n·ln(n+2)^{2^20·(N·ln(N+2))^{1/3}}}` | `MonoidProduct/Quantum/CubeRootApplications.lean` |
| `aperiodic_semigroup_oneHotQQuery_intro` | Aperiodic semigroups, with `N = \|S\|+1`, in the one-hot value-oracle model | `MonoidProduct/Quantum/CubeRootApplications.lean` |
| `ags_oneHotQQuery_le_display_logb` | The AGS bound `√n·(2^55(\|M\|+1)^6(log₂(n+1)+3)^2)^{d_J(M)+1}` | `MonoidProduct/Quantum/AGSApplications.lean` |
| `ags_oneHotQQuery_le_paper` | The AGS bound as displayed in the paper: `min{n, √n·((\|M\|+1)·ln(n+2))^{69(d_J(M)+1)}}` | `MonoidProduct/Quantum/AGSPaper.lean` |
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
| `Certificates/` | Equivalence under extensions, strong certificates and their size `b_f(U)`, the extension monoid and its cardinality bound, `β = b_f(U)`, the query bound from strong certificates, also for position-dependent encodings, the certificate bound for sparse yes-instances, and the bound for outputs determined by other outputs. `Certificates/Acceptance.lean` pins the exact form of these statements. |
| `Graph/` | Graphs on a fixed vertex set as subsets of the possible edges. Strong certificates of at most `v` edges for the component partition (with connectivity and `s`–`t` connectivity), the set of all proper two-colourings (with bipartiteness and a canonical colouring) and cycle detection, and the bound for properties with sparse yes-instances. Planarity, defined by rotation systems of genus `0` (a combinatorial embedding of each component), with the edge bound `3v − 6` and certificates of at most `min{C(v, 2), 3v − 5}` edges; `K₄` is planar, and `K₅` and `K₃,₃` are not. Euler's inequality `V − E + F ≤ 2` in every component, for every rotation system, through the Euler defect and its behaviour under edge deletion and contraction, so that planarity is closed under subgraphs, induced subgraphs, edge contraction and minors, and planar graphs have no `K₅` and no `K₃,₃` minor (the easy direction of Wagner's theorem). `k`-connectivity, proper separations and their marker-edge minors, and arcs of cyclic lists. Graph minors and Mader's theorem, so that every fixed proper minor-closed class has certificates of `O_P(v)` edges; outerplanarity, embeddings in surfaces (embedding schemes and the Euler genus) and bounded treewidth (tree decompositions), with explicit linear bounds. The edge-list, adjacency-matrix and adjacency-array query models, their comparison with factor two, and the query bounds of all these applications in each model. Edge-failure profiles: certificates of at most `k(v − 1)` edges from successive spanning forests, the bridges, the partitions after their deletion and `k`-edge-connectivity, with their query bounds. The vertex-failure profile, and the `Ω(min{v², v^{3/2}√k})` matrix lower bounds for both profiles through an enumeration adversary on Johnson exchange graphs. Vertex-failure profiles: certificates of at most `2kv` edges from a greedy construction (the sparse vertex-connectivity certificate the paper cites), the articulation points, the partitions after their deletion and `k`-vertex-connectivity, with their query bounds, so that both profiles cost `Θ(min{v², v^{3/2}√k})` matrix queries. `Graph/Acceptance.lean`, `Graph/QueryAcceptance.lean`, `Graph/PlanarAcceptance.lean`, `Graph/SparseClassesAcceptance.lean`, `Graph/FailureAcceptance.lean`, `Graph/LowerAcceptance.lean`, `Graph/VertexAcceptance.lean` and `Graph/WagnerAcceptance.lean` pin the exact form of these statements. |
| `Matroid/` | Greedy bases, the greedy-basis monoid, weighted records, and minimum-weight bases of general, uniform, partition, graphic and vector matroids. `Matroid/Certificates.lean` identifies greedy bases with strong certificates and rederives the basis query bound from them. |
| `Ordered/` | Stably ordered monoids: records, seeded sampling and merging, median frontiers, tree sampling, and rank doubling. |
| `Stock/`, `Tropical/` | Best time to buy and sell stock (integer and general prices) and unitriangular tropical matrices, including the path formula. |
| `UT/`, `Simon/` | Boolean unitriangular monoids `UT_k(𝔹)` and Simon's theorem for `J`-trivial monoids. |
| `Aperiodic/` | Green's relations and ideals, the AGS decomposition, prefix, suffix and infix search, the AGS induction, and `R`-trivial monoids. |
| `Aperiodic/CubeRoot/` | The cube-root bound: regular actions and owners, the action compiler, principal factors and Munn coordinates, the fixed-apex peel, radical lifts, and the size recurrence. |
| `Dyck/` | Dyck-language adversary lower bounds and the Dyck transition monoid `M_k` (normal form, Green structure, breadth, contracted algebra). |
| `Infix/` | The typed clean-infix adversary and uniform bounds for Rees matrix and Brandt monoids. |
| `Trichotomy/`, `Layer/` | The fixed-monoid trichotomy, the two-layer lower bound, and the aperiodicity-index lower bound. |
| `Quantum/` | Query-complexity consequences of the adversary results, in the native and one-hot oracle models: the main theorems, applications, division monotonicity, the envelope, and the Dyck lower bounds. Oracle simulations: renaming the query positions is free, and a position-dependent map of the answers costs a factor two. The `Acceptance*.lean` files pin the exact form of the main statements. |

`WidthCerts.lean` and `SemilatticeCerts.lean` repackage the essential-width
and semilattice duals as `HasDual` certificates for the query extraction.

The main results live in `Quantum/CommutativeLower.lean` and
`Width/Breadth.lean` (commutative monoids),
`Quantum/OrderedLogApplications.lean` and `Quantum/OrderedTruthful.lean`
(stably ordered monoids), `Quantum/CubeRootApplications.lean` (aperiodic
monoids and semigroups), `Certificates/Quantum.lean` (strong certificates),
`Graph/` (graph certificates and their query bounds) and
`Matroid/Quantum.lean` (matroid bases).

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
