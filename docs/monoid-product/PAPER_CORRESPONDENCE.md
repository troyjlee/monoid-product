# Paper correspondence

Part of the [MonoidProduct guide](README.md).

This record compares the Lean statements of the MonoidProduct library with
the results of *The quantum query complexity of the semigroup product
problem* (Troy Lee and Miklos Santha). For each paper result it lists the
corresponding Lean declaration, its source file, and any difference in
hypotheses, constants or scope.

<!-- Paper link: add the arXiv URL or DOI of the paper once available. -->

Paper results are identified by their LaTeX labels; "(text)" marks a claim
made in the running text. Declarations are fully qualified. File paths are
relative to the repository root, except that a path beginning with
`QuantumQueryComplexity/` refers to the
[QuantumQueryComplexity](https://github.com/troyjlee/quantum-query-complexity)
dependency, which provides the general adversary, duality and composition
machinery.

Lean checks the encoded statements and proofs; comparing those statements
and definitions with the paper also requires mathematical interpretation.

## Conventions

- **Problem.** `Prod_{M,G,n}` is `fun x : Fin n → σ => wordProd letter x`
  (written `∏ i, m (x i)` in the commutative files) for a letter map
  `letter : σ → M` from a finite type `σ`; the paper's alphabet `G` is the
  image of `letter`, and the full alphabet is `letter = id`. Products of
  nonempty words in a semigroup are `semigroupProd n : (Fin (n + 1) → S) → S`.
- **Product breadth.** `MonoidProduct.IsBreadthBound letter b` says that
  every word has a product core of at most `b` positions, and
  `MonoidProduct.breadth letter` is the least such `b` (the paper's
  `β_G(M)`, `eq:monoid-beta`). It is `0` when no bound exists, so theorems
  about monoids that may have infinite breadth take a bound `b` as a
  hypothesis.
- **Adversary bound and duals.** `ADV±` is `QuantumQueryComplexity.advPM`
  (`advPMOn` on a promise). An all-pairs dual of cost `T`
  (`eq:all-pairs-dual`) is `HasDual f T` (`HasDualOn` on a promise).
- **Query models.** `qQuery f ε` is the bounded-error query complexity with
  the library's native oracle, which swaps a blank answer register with the
  queried letter. `oneHotQQuery f ε` uses the whole-element XOR value oracle
  of the paper. The two agree up to a factor two in each direction; results
  whose constant depends on the model are stated in both.
- **Constants.** Each `O(·)`, `Ω(·)` and "absolute constant" of the paper is
  an explicit numeral in Lean. Recurring ones: a cost-`T` dual gives
  `Q_{1/3} ≤ 8192·(1 + T)` (`uniformExtractionConstant`), whose absorbed
  form for `√(n·min{n,b})` bounds is `2^18·√(n·min{n,b})`; and
  `(7/1376)·ADV± ≤ Q_{1/3}`.
- **Logarithms.** `Real.log` is natural, `Real.logb 2` is binary and
  `Nat.clog 2` is the ceiling of `log₂`. The paper's `L(n) = 2 + log₂(n+2)`
  is `MonoidProduct.paperLog n`, and `L_n = ⌈log₂(n+1)⌉` in the ordered
  results.

## Main results

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `res:commutative`, `thm:commutative-beta` | `ADV± ≤ 16√(n·min{n,β_G})`; `Q_{1/3} = Θ(min{n,√(nβ_G)})` when `1 ∈ G` | `MonoidProduct.advPM_prodFun_le_breadth`, `MonoidProduct.commutative_qQuery_sandwich`, `MonoidProduct.commutative_qQuery_lower_total`, `MonoidProduct.qQuery_prodFun_le_min_of_breadth_le` | `MonoidProduct/Width/Breadth.lean`, `MonoidProduct/Quantum/CommutativeLower.lean`, `MonoidProduct/Width/PaperForms.lean` | Explicit sandwich `√(n·min{n,β})/72 ≤ Q_{1/3} ≤ min{n, 2^18·√(n·min{n,β})}` for `n, β ≥ 1`, given a letter mapped to `1`. The full-alphabet lower bound assumes `Nontrivial M`. |
| `def:stable-least-order` | Stable partial order whose minimum is the identity | `MonoidProduct.IsStableOrder`, `MonoidProduct.IsStableOrder.stable` | `MonoidProduct/Width/StableOrder.lean` | Defined by left and right monotonicity, equivalent to two-sided stability. |
| `res:ordered`, `thm:ordered-beta-log-product`, `eq:beta-log-product` | `Q_{1/3} ≤ min{n, √(n+1)·(C(β+2)log(n+2))^{C log(β+2)}}` for stably ordered monoids | `MonoidProduct.ordered_qQuery_third_le_quasipoly`, `MonoidProduct.quasipolyBound`, `MonoidProduct.ordered_qQuery_le_quasipoly_breadth`, `MonoidProduct.ordered_exists_core_alg_quasipoly`, `MonoidProduct.ordered_exists_verified_core_alg_quasipoly`, `MonoidProduct.ordered_truthful_core_alg_quasipoly` | `MonoidProduct/Quantum/OrderedLogApplications.lean`, `MonoidProduct/Quantum/OrderedVerified.lean`, `MonoidProduct/Quantum/OrderedTruthful.lean` | `C = 2^17`, natural logarithms, real exponent. `M` may be infinite (with finite `σ`) and `β ≥ 1` is not needed for the bound. The core algorithm (success `9/10`, at most `β` positions) assumes `1 ≤ β < n`. Truthfulness on every branch costs `+β` queries at `C = 2^17`, or fits the displayed bound at `C = 2^18`. |
| `res:aperiodic-size`, `thm:ags-cuberoot-size`, `eq:ags-cuberoot-final` | `Q_{1/3} ≤ min{n, √n·L(n)^{C(N log(N+2))^{1/3}}}` for aperiodic `M` of order `N` | `MonoidProduct.aperiodic_qQuery_final_exact`, `MonoidProduct.aperiodic_oneHotQQuery_final_exact`, `MonoidProduct.aperiodic_qQuery_intro`, `MonoidProduct.aperiodic_oneHotQQuery_intro` | `MonoidProduct/Quantum/CubeRootApplications.lean` | `C = 2^18` in the `L(n)` form; the introduction's `log(n+2)` form (natural logarithm) has `C = 2^20`. Both oracle models; `n ≥ 1`. |
| `eq:ags-cuberoot-unabsorbed` | `Q_{1/3} ≤ √n·(N L(n))^{C(N log(N+2))^{1/3}}` | `MonoidProduct.aperiodic_qQuery_paper_real` | `MonoidProduct/Quantum/CubeRootApplications.lean` | `C = 16384`, native model. The exponent is written with `(N·L(N))^{1/3}`, which is within a constant factor of `(N log(N+2))^{1/3}`. |
| `thm:ags-cuberoot-size`, semigroup clause | The same bounds with `N = \|S\|+1` | `MonoidProduct.aperiodic_semigroup_oneHotQQuery_final_exact`, `MonoidProduct.aperiodic_semigroup_oneHotQQuery_intro` | `MonoidProduct/Quantum/CubeRootApplications.lean` | One-hot model, words `Fin (n + 1) → S`. |

## Introduction (`sec:overview`)

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `eq:monoid-beta` | Product breadth | `MonoidProduct.IsBreadthBound`, `MonoidProduct.breadth`, `MonoidProduct.exists_isBreadthBound` | `MonoidProduct/Width/Breadth.lean` | See Conventions. |
| (text) | `β ≥ ι` for nontrivial `M` | `MonoidProduct.aperiodicIndex_le_breadth`, `MonoidProduct.aperiodicIndex_le_breadth_comm` | `MonoidProduct/Width/SmallClauses.lean` | Assumes a surjective letter map and a finite breadth. |
| (text) | A finite monoid is aperiodic iff it has no nontrivial subgroup | `MonoidProduct.isAperiodicMonoid_iff_not_hasNontrivialSubgroup` | `MonoidProduct/Width/SmallClauses.lean` | |
| `ex:max` | `(ℕ, max)` has `β = 1`; `O(√n)` queries | `MonoidProduct.MaxNat.breadth_eq_one`, `MonoidProduct.MaxNat.breadth_id_eq_one`, `MonoidProduct.advPM_maxFun_le_of_summary` | `MonoidProduct/Width/SmallClauses.lean`, `MonoidProduct/Width/Instances.lean` | `ADV± ≤ 16√n` for maximum over any finite alphabet. |
| `ex:union` | `β = m = log₂\|M\|` for `(2^{[m]}, ∪)` | `MonoidProduct.UnionSet.breadth_id_eq`, `MonoidProduct.UnionSet.breadth_id_eq_log` | `MonoidProduct/Width/SmallClauses.lean` | The query upper bound is `thm:semilattice-product`. |
| `ex:spanning-forest` | Minimum spanning forests: `β = v−1`, `O(√(nβ))` | `MonoidProduct.Matroid.minSpanningForest_minWeight_and_qQuery`, `MonoidProduct.Matroid.adjacencyArray_minSpanningForest` | `MonoidProduct/Matroid/Graphic.lean` | Through the graphic matroid of `sec:matroid-bases`. |
| `ex:capped-addition` | Capped addition: `ι = β = m`, `Θ(min{n,√(mn)})` | `MonoidProduct.Capped.aperiodicIndex_eq`, `MonoidProduct.breadth_capped_eq`, `MonoidProduct.cappedLen_qQuery_theta` | `MonoidProduct/Width/SmallClauses.lean`, `MonoidProduct/Capped/Breadth.lean`, `MonoidProduct/Capped/LengthBreadth.lean` | The case `r = 1` of `thm:capped-counter-product`. |
| `ex:btbs-breadth` | BTBS monoid: `s² = s³`, noncommutative, `β_G = 4`, attained by `(10,2,5,0)` | `MonoidProduct.StrictStock.strictStock_pow_two_eq_pow_three`, `MonoidProduct.StrictStock.strictStock_not_commutative`, `MonoidProduct.StrictStock.isBreadthBound_strict`, `MonoidProduct.GenStock.gstock_sharp_int` | `MonoidProduct/Stock/Aperiodic.lean`, `MonoidProduct/Stock/Strict.lean`, `MonoidProduct/Stock/GeneralPrices.lean` | Integer prices; `prop:stock-beta` covers general prices. |
| `ex:dyck-breadth` | Dyck monoid: `β = Θ(k)`, yet `Ω(c^k√n)` queries | `MonoidProduct.breadth_dyck`, `MonoidProduct.dyckLB_qQuery` | `MonoidProduct/Dyck/Breadth.lean`, `MonoidProduct/Quantum/DyckLanguageLower.lean` | See `prop:dyck-breadth` and `thm:dyck-lb`. |

## Algebraic preliminaries and basic lower bounds (`sec:prelim`)

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `prop:division-monotonicity` | `Q(Prod_R) ≤ 2Q(Prod_S)` when `R ≺ S`, and the section form | `MonoidProduct.qQuery_semigroupProd_le_of_division_lift`, `MonoidProduct.qQuery_semigroupProd_le_of_division_letters_inf`, `MonoidProduct.qQuery_prodFun_le_of_division` | `MonoidProduct/Quantum/DivisionInfinite.lean`, `MonoidProduct/Quantum/Division.lean` | Arbitrary semigroups with finite letter alphabets, every error `ε ≥ 0`. With the same letters on both sides the factor is one. |
| `prop:rank-mono` | `ρ(p), ρ(q) ≤ ρ(pq)` | `MonoidProduct.idealRank_mono`, `MonoidProduct.idealRank`, `MonoidProduct.twoIdeal_mul_subset_left`, `MonoidProduct.twoIdeal_mul_subset_right` | `MonoidProduct/Trichotomy/PaperForms.lean`, `MonoidProduct/Aperiodic/Ideals.lean` | `idealRank m = \|M\| − \|MmM\|`. |
| `lem:sandwich` | `pqr = q ⇒ q = pq = qr` | `MonoidProduct.sandwich_left`, `MonoidProduct.sandwich_right` | `MonoidProduct/Aperiodic/Defs.lean` | |
| `prop:identity` | `p₁⋯pₙ = 1 ⇒ pᵢ = 1`; `ρ(m) = 0 ⇔ m = 1` | `MonoidProduct.prop_identity`, `MonoidProduct.idealRank_eq_zero_iff`, `MonoidProduct.mul_eq_one_iff'`, `MonoidProduct.orderedProd_eq_one_iff` | `MonoidProduct/Trichotomy/PaperForms.lean`, `MonoidProduct/Aperiodic/Defs.lean` | |
| `lem:singleton` | `{m} = (mM ∩ Mm) \ J_m` | `MonoidProduct.eq_iff_mem_ideals` | `MonoidProduct/Aperiodic/Ideals.lean` | |
| `eq:adversary-tightness`, `eq:all-pairs-dual` | `Q_{1/3} = Θ(ADV±)`; duals of cost about `2·ADV±` | `QuantumQueryComplexity.mul_advPMOn_le_qQueryOn_third_finiteOutput`, `QuantumQueryComplexity.hasDualOn_of_two_mul_advPMOn_lt`, `QuantumQueryComplexity.qQueryOn_third_le_of_hasDualOn_uniform` | `QuantumQueryComplexity/Quantum/Plurality.lean`, `QuantumQueryComplexity/Duality/FiniteOutputOn.lean`, `QuantumQueryComplexity/Quantum/UniformHasDual.lean` | `(7/1376)·ADV± ≤ Q_{1/3}`; a dual of every cost above `2·ADV±`; a cost-`T` dual gives `Q_{1/3} ≤ 8192(1+T)`. |
| `thm:fixed-monoid-trichotomy` | Nonaperiodic semigroups need `Θ_S(n)`; trichotomy for fixed finite monoids | `MonoidProduct.fixed_monoid_trichotomy_qQuery`, `MonoidProduct.fixed_semigroup_trichotomy_qQuery`, `MonoidProduct.qQuery_prodFun_of_subsingleton`, `MonoidProduct.qQuery_semigroupProd_lower_of_not_aperiodic`, `MonoidProduct.nonaperiodic_semigroup_qQuery_upper`, `MonoidProduct.half_le_advPM_semigroupProd_of_not_aperiodic`, `MonoidProduct.trichotomy_lower_bounds`, `MonoidProduct.qQuery_lower_of_not_aperiodic`, `MonoidProduct.qQuery_lower_of_not_subsingleton` | `MonoidProduct/Trichotomy/PaperForms.lean`, `MonoidProduct/Quantum/Applications.lean`, `MonoidProduct/Trichotomy/Semigroup.lean`, `MonoidProduct/Trichotomy/Main.lean` | Lower constants `(1/36)·(n/2)` and `(1/36)·√n`. The aperiodic upper bound is `thm:main-ags` or `thm:ags-cuberoot-size`. The Boolean-postprocessing lower bounds are the `advPMOn` statements of `Trichotomy/Main.lean`. `fixed_monoid_trichotomy_qQuery` assembles the three monoid regimes at `ε = 1/3` (`Q = 0` for `\|M\| = 1`); semigroup words are indexed by `Fin (n+1)`. |
| `thm:aperiodicity-index-lower` | `Q_{1/3} = Ω(√(n·min{n,ι}))` | `MonoidProduct.aperiodicIndex`, `MonoidProduct.sqrt_index_le_advPM_prodFun`, `MonoidProduct.sqrt_index_le_advPMOn_prodFun`, `MonoidProduct.index_qQuery_lower` | `MonoidProduct/Trichotomy/Index.lean`, `MonoidProduct/Quantum/Applications.lean` | `ADV± ≥ √(n·min{n,ι})/2` and `Q_{1/3} ≥ (1/72)·√(n·min{n,ι})`. |

## General techniques for adversary upper bounds (`sec:width`)

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `def:essential-width` | Incremental summary and essential width | `MonoidProduct.IncrementalSummary`, `MonoidProduct.PromiseSummary` | `MonoidProduct/Width/Summary.lean`, `MonoidProduct/Width/PromiseWidth.lean` | `IncrementalSummary` is the total-input case; `PromiseSummary` has a promise domain `D`. |
| `thm:essential-width` | `ADV± ≤ 16√(nB)`; width `0` gives a constant function | `MonoidProduct.advPM_le_of_summary_nonneg`, `MonoidProduct.PromiseSummary.advPMOn_le_of_width`, `MonoidProduct.PromiseSummary.qQueryOn_third_le_of_width`, `MonoidProduct.PromiseSummary.out_const_of_width_zero`, `MonoidProduct.summary_qQuery_le_min_sqrt` | `MonoidProduct/Width/Main.lean`, `MonoidProduct/Width/PromiseWidth.lean`, `MonoidProduct/Quantum/WidthApplications.lean` | |
| `eq:weighted-width` | Weighted essential width | `MonoidProduct.PromiseSummary.exists_dualPairOn_isWeightedCostLe`, `MonoidProduct.PromiseSummary.exists_weightedDualOn`, `MonoidProduct.exists_summary_dual_isWeightedCostLe` | `MonoidProduct/Width/PromiseWidth.lean`, `MonoidProduct/Width/Main.lean` | |
| `lem:bounded-change-scan` | `ADV± ≤ 8√(nC)` for at most `C` state changes | `QuantumQueryComplexity.hasDualOn_scan` | `QuantumQueryComplexity/Scan/Bounded.lean` | |
| `thm:bt-subroutine-composition` | Decision trees with subroutine calls: dual of cost `O(T√(qG))` | `QuantumQueryComplexity.PredTree.hasDualOn_compose`, `QuantumQueryComplexity.PredTree.hasDualOn_compose_of_advPMOn`, `QuantumQueryComplexity.PredTree.qQueryOn_third_compose_le_of_advPMOn` | `QuantumQueryComplexity/Promise/PredictionTreeCompose.lean`, `QuantumQueryComplexity/PredictionTreeAdversary.lean`, `QuantumQueryComplexity/Quantum/PredictionTreeCompose.lean` | `8A√(qG)` from cost-`A` duals; `24T√(qG)` from adversary values. |
| `thm:rtrivial` | `ADV± ≤ 8√(n·min{n,d_R})` for `R`-trivial `M`; the promise form | `MonoidProduct.rtrivial_qQuery_le_paper`, `MonoidProduct.advPM_wordProd_le_of_isRTrivial`, `MonoidProduct.advPMOn_wordProd_le_of_changeCount`, `MonoidProduct.rtrivial_qQuery_le_min`, `MonoidProduct.isAperiodicMonoid_of_isRTrivial` | `MonoidProduct/Quantum/RTrivialPaper.lean`, `MonoidProduct/Aperiodic/RTrivial.lean`, `MonoidProduct/Quantum/RTrivialApplications.lean` | `Q_{1/3} ≤ min{n, 8192(1 + 8√(n·min{n,d_R}))}`. As displayed: `Q_{1/3} ≤ 73728·min{n, √(n·d_R)}` (`rtrivial_qQuery_le_paper`). |

## Commutative monoids (`sec:lattice`)

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `thm:commutative-beta`, `eq:comm-width` | See Main results | `MonoidProduct.advPM_prodFun_le_breadth`, `MonoidProduct.advPM_prodFun_le_of_breadth_le`, `MonoidProduct.commutative_qQuery_sandwich` | `MonoidProduct/Width/Breadth.lean`, `MonoidProduct/Width/PaperForms.lean`, `MonoidProduct/Quantum/CommutativeLower.lean` | |
| `prop:comm-jtrivial` | Finite commutative aperiodic ⇒ `J`-, `R`- and `L`-trivial | `MonoidProduct.isJTrivialMonoid_of_comm`, `MonoidProduct.isRTrivialMonoid_of_comm`, `MonoidProduct.leftIdeal_injective_of_comm` | `MonoidProduct/Aperiodic/CommJTrivial.lean`, `MonoidProduct/Width/PaperForms.lean` | `L`-triviality is stated as injectivity of principal left ideals. |
| `lem:comm-beta-width`, `eq:monoid-width` | `κ_G(M) = β_G(M)` | `MonoidProduct.isWidthBound_iff_isBreadthBound`, `MonoidProduct.prodEss_subset_of_prod_eq` | `MonoidProduct/Width/Breadth.lean` | |
| `lem:critical` | The subset joins of a shortest preserving word are distinct | `MonoidProduct.two_pow_card_prodEss_le_joinClosure`, `MonoidProduct.two_pow_card_prodEss_le_of_idem`, `MonoidProduct.two_pow_card_criticalSet_le` | `MonoidProduct/Width/PaperForms.lean`, `MonoidProduct/Width/BreadthBounds.lean`, `MonoidProduct/Semilattice/Critical.lean` | Stated through its counting consequence `2^B ≤ \|L_G\| + 1`. |
| `thm:semilattice-product`, `eq:semilattice-beta`, `eq:semilattice-adv` | `β_G ≤ ⌊log₂(\|L_G\|+1)⌋`, with the `ADV±` and query bounds | `MonoidProduct.breadth_le_log_joinClosure`, `MonoidProduct.advPM_prodFun_le_joinClosure`, `MonoidProduct.qQuery_prodFun_le_joinClosure`, `MonoidProduct.breadth_le_log_of_idem` | `MonoidProduct/Width/PaperForms.lean`, `MonoidProduct/Width/BreadthBounds.lean` | `L_G` is `joinClosureFin m`; query constant `2^18`. |
| (remark after `thm:semilattice-product`) | At most `K` joins on a promise | `MonoidProduct.advPMOn_joinMap_le_of_joinCount`, `MonoidProduct.advPMOn_joinMap_le_of_bound` | `MonoidProduct/Width/PaperForms.lean`, `MonoidProduct/Promise/Semilattice.lean` | Stated for semilattice joins. |
| `thm:index-two-width`, `eq:index-two-width`, `eq:index-two-adv` | Under `x³ = x²`: `β_G ≤ 5 log₂\|M\|`, strict when `\|M\| ≥ 2` | `MonoidProduct.breadth_le_five_logb`, `MonoidProduct.breadth_lt_five_logb`, `MonoidProduct.advPM_prodFun_le_indexTwo_min`, `MonoidProduct.qQuery_prodFun_le_indexTwo_min` | `MonoidProduct/Width/PaperForms.lean`, `MonoidProduct/Width/BreadthBounds.lean` | Query form `min{n, 2^18·√(n·min{n, 5 log₂\|M\|})}`. |
| `lem:no-product-sunflower` | Product fibers contain no `(k+1)`-sunflower | `MonoidProduct.not_isSunflower_of_subset_fullProdFiber` | `MonoidProduct/Width/ProductSunflower.lean` | |
| `thm:index-k-width`, `eq:index-k-width`, `eq:index-k-adv` | Under `x^{k+1} = x^k`: `β_G ≤ C(k+1)(log₂\|M\|+1)log(log₂\|M\|+2)` | `MonoidProduct.breadth_le_indexK_paper`, `MonoidProduct.breadth_le_bcw`, `MonoidProduct.advPM_prodFun_le_indexK_min`, `MonoidProduct.qQuery_prodFun_le_indexK_min` | `MonoidProduct/Width/PaperForms.lean`, `MonoidProduct/Width/BreadthBounds.lean` | `C = 2^64` with a natural outer logarithm; `k ≥ 1`. The sunflower bound is `Sunflower.RaoBCW`. |
| `eq:elementary-index-k` | Erdős–Rado comparison: `β < 2k(log₂\|M\|+1)²` | `MonoidProduct.erdosRado_breadth_lt`, `MonoidProduct.erdosRado_card_le` | `MonoidProduct/Width/ErdosRadoComparison.lean` | |
| `rem:scope-records` | The capped counter of height `K` needs `K` copies of its generator | `MonoidProduct.breadth_capped_eq` | `MonoidProduct/Capped/Breadth.lean` | One-coordinate case. |
| `thm:capped-counter-product`, `eq:capped-counter-theta`, `eq:capped-counter-size` | `β(M_{k,r}) = kr`; largest shortest core among length-`n` words is `min{n,kr}`; `Q = Θ(√(n·min{n,kr}))` | `MonoidProduct.cappedLen_qQuery_size`, `MonoidProduct.breadth_capped_eq`, `MonoidProduct.cappedLen_isGreatest`, `MonoidProduct.cappedLen_qQuery_theta`, `MonoidProduct.advPM_cappedProd_sandwich` | `MonoidProduct/Capped/Breadth.lean`, `MonoidProduct/Capped/LengthBreadth.lean`, `MonoidProduct/Capped/Theta.lean` | `M_{k,r}` is `ρ → Capped k` with `r = \|ρ\|`. `ADV±` sandwich with constants `1/4` and `16`. |
| `prop:jtrivial-log-fails` | Capped counter `C_{K+1}`: `d_R = K`, `Ω(√(nK))` on binary inputs | `MonoidProduct.Capped.rDepth_eq`, `MonoidProduct.capped_binary_qQuery_lower`, `MonoidProduct.capped_qQuery_lower_total` | `MonoidProduct/Capped/RTrivial.lean`, `MonoidProduct/Quantum/RTrivialApplications.lean`, `MonoidProduct/Quantum/Envelope.lean` | `(7/1376)·√(n·min{n,K})/4 ≤ Q_{1/3}` for every `n`. |

## Minimum-weight matroid bases (`sec:matroid-bases`)

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `eq:matroid-prefix-closure` | Greedy keeps a basis of every order prefix | `MonoidProduct.Matroid.isBasis_greedy_inter`, `MonoidProduct.Matroid.closure_greedy_inter` | `MonoidProduct/Matroid/Greedy.lean` | Mathlib's `Matroid` on a finite linearly ordered ground type. |
| `lem:matroid-greedy-merge` | `B(S ∪ T) = B(B(S) ∪ B(T))` | `MonoidProduct.Matroid.greedy_union_eq_greedy_union_greedy` | `MonoidProduct/Matroid/Greedy.lean` | The ground set is the whole type (`M.E = univ`). |
| `prop:matroid-greedy-monoid` | The greedy-basis monoid is commutative and idempotent; `β_G(H) = r` | `MonoidProduct.Matroid.GreedyBasisMonoid`, `MonoidProduct.Matroid.GreedyBasisMonoid.mul_self_greedyBasis`, `MonoidProduct.Matroid.greedyBasis_breadth_eq_rank`, `MonoidProduct.Matroid.greedyBasis_qQuery_le_min` | `MonoidProduct/Matroid/GreedyMonoid.lean` | The alphabet is `Option E`, with `none` the identity letter. |
| `thm:matroid-basis-query` | Canonical minimum-weight basis with `O(min{n,√(nr)})` queries; `r = 0` needs none | `MonoidProduct.Matroid.matroidBasis_minWeight_and_qQuery`, `MonoidProduct.Matroid.matroidBasisRecords_qQuery_le_min_sqrt`, `MonoidProduct.Matroid.matroidBasisIndices_qQuery_le_min_sqrt`, `MonoidProduct.Matroid.matroidBasisIndices_qQuery_eq_zero`, `MonoidProduct.Matroid.basisRecords_isMinimumWeightBasis` | `MonoidProduct/Matroid/Quantum.lean`, `MonoidProduct/Matroid/Records.lean` | Constant `2^18`. Records are `Option (E × W)`, with weights in a finite linearly ordered type that embeds order-preservingly in `ℝ`. |
| (examples) | Uniform matroid: the `r` smallest weights; partition matroid: a lightest record of each type; truncated partition matroid: the `r` cheapest types | `MonoidProduct.Matroid.smallestWeights_select_and_qQuery`, `MonoidProduct.Matroid.lightestPerType_select_and_qQuery`, `MonoidProduct.Matroid.cheapestTypes_select_and_qQuery` | `MonoidProduct/Matroid/Selection.lean` | |
| (examples) | Minimum spanning forests: `O(min{n,√(nv)})` record queries, `O(v^{3/2})` in the adjacency-matrix model, `O(√(vm))` in the adjacency-array model | `MonoidProduct.Matroid.minSpanningForest_minWeight_and_qQuery`, `MonoidProduct.Matroid.adjacencyMatrix_minSpanningForest`, `MonoidProduct.Matroid.adjacencyArray_minSpanningForest` | `MonoidProduct/Matroid/Graphic.lean` | Query counts, as in the paper. |
| (examples) | Vector matroid on `𝔽_q^d`: `O(min{n,√(nd)})`, uniformly in `q`; spans | `MonoidProduct.Matroid.vectorBasis_minWeight_and_qQuery`, `MonoidProduct.Matroid.spanBasis_isBasis_and_qQuery` | `MonoidProduct/Matroid/Vector.lean` | |

## Product breadth and ordered monoid products (`sec:beta`)

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| (two elementary observations) | Monotonicity of subword products, sandwiching, compression | `MonoidProduct.IsStableOrder.subwordProd_mono`, `MonoidProduct.subwordProd_eq_of_sandwich`, `MonoidProduct.exists_compress` | `MonoidProduct/Width/StableOrder.lean`, `MonoidProduct/Ordered/Records.lean` | |
| `lem:beta-essential-subword-list` | At most `β` members of a list are essential | `MonoidProduct.card_essential_le` | `MonoidProduct/Ordered/Records.lean` | |
| `lem:beta-rejection-dual` | Bounded rejection sampling has a dual of cost `O(TD√k)` | `QuantumQueryComplexity.DrawProgram.hasDual_run` | `QuantumQueryComplexity/RejectionTree.lean` | Cost `8TD√k`. |
| `lem:beta-sampling`, `eq:beta-small-mass` | A short record dominating almost all samples | `MonoidProduct.Seeded.hasDual_mergeK_seeded`, `MonoidProduct.Seeded.seeded_small_mass`, `MonoidProduct.halving`, `MonoidProduct.merge_small_mass` | `MonoidProduct/Ordered/MergeSeeded.lean`, `MonoidProduct/Ordered/Merge.lean` | Separate cost and probability statements with explicit parameters. |
| `thm:ordered-beta-product` | `Q_{1/3} ≤ min{n, (Cβ)^β√n·L^{5β/2}}`; core algorithm; `β = 0` is query-free | `MonoidProduct.ordered_qQuery_third_le_five_halves`, `MonoidProduct.ordered_exists_core_alg`, `MonoidProduct.ordered_truthful_core_alg_five_halves`, `MonoidProduct.qQuery_wordProd_zero_breadth` | `MonoidProduct/Quantum/OrderedApplications.lean`, `MonoidProduct/Quantum/OrderedTruthful.lean` | `C = 2^27` with `L = L_n = ⌈log₂(n+1)⌉`, as recorded in `rem:ordered-formalization`; the core algorithm is stated with exponent `3β`; `C = 2^28` with truthfulness on every branch. |
| `lem:beta-median-frontier` | Median-frontier coverage | `MonoidProduct.median_frontier_covers` | `MonoidProduct/Ordered/MedianFrontier.lean` | |
| `lem:beta-adaptive-sum` | Dual costs of adaptive calls add | `QuantumQueryComplexity.hasDual_chain`, `QuantumQueryComplexity.HasDual.adaptiveCall`, `QuantumQueryComplexity.HasDual.postcomp_of_determined` | `QuantumQueryComplexity/Chain.lean`, `QuantumQueryComplexity/Adaptive.lean`, `QuantumQueryComplexity/HasDual.lean` | |
| `thm:weighted-tree-search`, `eq:tree-recursive-cost` | Tree search with dual cost `C_ρ`, `C_v = t_v + √(Σ C_u²)` | `QuantumQueryComplexity.AncTree.hasWeightedDual_treeSearch_recCost`, `QuantumQueryComplexity.AncTree.optValue_eq`, `QuantumQueryComplexity.AncTree.qQuery_third_treeSearch`, `MonoidProduct.hasDual_tsDec_recCost` | `QuantumQueryComplexity/TreeSearch/Optimal.lean`, `MonoidProduct/Ordered/TreeSampling.lean` | Query form `≤ 16384·C_ρ` in `QuantumQueryComplexity/Quantum/TreeSearch.lean`. |
| `cor:beta-tree-search-depth`, `eq:beta-tree-budget` | `C_ρ ≤ √((d+1)Σ t_v²)` | `QuantumQueryComplexity.AncTree.recCost_le_sqrt_depth_sqSum` | `QuantumQueryComplexity/TreeSearch/Optimal.lean` | |
| `lem:beta-tree-sampling`, `eq:beta-tree-combine` | Seeded batch sampling on a tree | `MonoidProduct.tree_sampling` | `MonoidProduct/Ordered/TreeSampling.lean` | Dual cost `40·β·R·B·log(q+2)`. |
| `lem:beta-rank-doubling` | Rank doubling | `MonoidProduct.hasDual_dblOut`, `MonoidProduct.costB_le`, `MonoidProduct.summary2_correct`, `MonoidProduct.amp_fail_le` | `MonoidProduct/Ordered/RankDoubling.lean`, `MonoidProduct/Ordered/LogRankCost.lean`, `MonoidProduct/Ordered/LogRankCorrect.lean`, `MonoidProduct/Ordered/LogRank.lean` | Formalized as the induction step of the cost and failure-probability recurrences rather than as one standalone lemma. |
| `eq:beta-doubling-iterated` | `(C₂(β+2)L_n⁴)^{⌈log₂(β+2)⌉+2}√n` | `MonoidProduct.ordered_qQuery_third_le_logrank`, `MonoidProduct.ordered_qQuery_le_logrank` | `MonoidProduct/Quantum/OrderedLogApplications.lean` | `C₂ = 2^15`. |
| `thm:ordered-beta-log-product` | See Main results | `MonoidProduct.ordered_qQuery_third_le_quasipoly`, `MonoidProduct.ordered_truthful_core_alg_quasipoly` | `MonoidProduct/Quantum/OrderedLogApplications.lean`, `MonoidProduct/Quantum/OrderedTruthful.lean` | |
| `rem:ordered-formalization` | Constants, oracle and error conventions of the formalization | `MonoidProduct.ordered_qQuery_le_five_halves`, `MonoidProduct.ordered_qQuery_le_logrank`, `MonoidProduct.ordered_exists_verified_core_alg_quasipoly` | `MonoidProduct/Quantum/OrderedApplications.lean`, `MonoidProduct/Quantum/OrderedLogApplications.lean`, `MonoidProduct/Quantum/OrderedVerified.lean` | Error-`1/10` forms, and the `β` verification queries. |

## Applications: stock and unitriangular products (`sec:applications`)

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `prop:stock-beta` | `M_P` is stably ordered, `β_{G_P} ≤ 4`, `O(√n log^{10}(n+2))` queries | `MonoidProduct.GenStock.gstock_isStableOrder`, `MonoidProduct.GenStock.gstock_isBreadthBound`, `MonoidProduct.GenStock.gstock_qQuery_third_le`, `MonoidProduct.GenStock.gstockProfit_qQuery_third_le`, `MonoidProduct.GenStock.gstock_sharp` | `MonoidProduct/Stock/GeneralPrices.lean` | Prices in any linearly ordered additive commutative group; bound `min{n, (2^29)^4·√n·L_n^{10}}`. The integer case is `MonoidProduct.StrictStock.strictProfit_qQuery_third_le` in `MonoidProduct/Quantum/StrictStockApplications.lean`. |
| `prop:path` | Path formula for unitriangular tropical products; at most `t−s` strict transitions | `MonoidProduct.linProd_eq_sup_tpathMono`, `MonoidProduct.card_tpathStrict_le`, `MonoidProduct.exists_optimal_tpath`, `MonoidProduct.UTrop.wordProd_val_apply_eq_sup_tpath` | `MonoidProduct/Tropical/Path.lean` | |
| `cor:unitriangular-beta` | `⟨G⟩` is finite; `β_G ≤ C(k+1,3)`; the quasipolynomial bound; `k = 1` is query-free | `MonoidProduct.utrop_closure_finite`, `MonoidProduct.utrop_isStableOrder`, `MonoidProduct.utrop_isBreadthBound_choose`, `MonoidProduct.utrop_qQuery_third_le_paper`, `MonoidProduct.utrop_qQuery_eq_zero` | `MonoidProduct/Tropical/Unitriangular.lean` | `C = 2^17`. The stock and signed-sum encodings of the surrounding text are `MonoidProduct.utropStockHom` and `MonoidProduct.utropSignedChain_wordProd`. |

## Boolean unitriangular products (`sec:boolean-unitriangular`)

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `thm:boolean-unitriangular` | `β = C(k,2)`; the `ADV±` sandwich; `Q = Θ(min{n,k√n})`, and `0` at `k = 1` | `MonoidProduct.but_breadth_id`, `MonoidProduct.advPM_wordProd_but_sandwich`, `MonoidProduct.ut_qQuery_sandwich`, `MonoidProduct.but_qQuery_theta`, `MonoidProduct.ut_qQuery_eq_zero_dim_one`, `MonoidProduct.ut_oneHotQQuery_sandwich` | `MonoidProduct/UT/Breadth.lean`, `MonoidProduct/UT/Main.lean`, `MonoidProduct/Quantum/Applications.lean`, `MonoidProduct/Quantum/OneHotApplications.lean` | `min{n,k√n}/144 ≤ Q_{1/3} ≤ 73728·min{n,k√n}` for `k ≥ 2`, `n ≥ 1`. |
| `cor:jtrivial-division` | `Q = O(√(n·min{n,C(τ,2)})) = O(min{n,τ√n})` for `J`-trivial `M` | `MonoidProduct.tau`, `MonoidProduct.jtrivial_qQuery_le_min`, `MonoidProduct.jtrivial_qQuery_le_min_tau` | `MonoidProduct/Simon/Main.lean`, `MonoidProduct/Quantum/Applications.lean`, `MonoidProduct/Width/PaperForms.lean` | Constant `147456`. Simon's theorem is formalized in `MonoidProduct/Simon/`. |

## General aperiodic monoids: the AGS bound and Dyck obstruction (`sec:ags`)

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `thm:decomp` | `x ∈ P_m` iff (U), (V), (C) and (W); the strict ideal drops | `MonoidProduct.orderedProd_eq_iff`, `MonoidProduct.twoIdeal_lt_of_mem_setE`, `MonoidProduct.twoIdeal_lt_of_mem_setF`, `MonoidProduct.twoIdeal_lt_of_mem_setG` | `MonoidProduct/Aperiodic/Decomposition.lean` | |
| `lem:prefix` | Prefix search | `MonoidProduct.hasDual_prefixEvent`, `MonoidProduct.hasDual_suffixEvent` | `MonoidProduct/Aperiodic/Prefix.lean`, `MonoidProduct/Aperiodic/Suffix.lean` | Dual-cost form with `O(√\|M\|·log n)` recursive tests and no amplification factor. |
| `prop:split` | Splitting a word; at most `\|M\|²` pairs | `MonoidProduct.splitPairs`, `MonoidProduct.card_splitPairs_le`, `MonoidProduct.twoIdeal_lt_of_split_left`, `MonoidProduct.twoIdeal_lt_of_split_right` | `MonoidProduct/Aperiodic/Split.lean` | |
| `lem:infix` | Infix search | `MonoidProduct.hasDual_badInfixFor`, `MonoidProduct.hasDual_badInfixFor_strict` | `MonoidProduct/Aperiodic/InfixCost.lean` | Dual-cost form. |
| `lem:ags-local-step` | Localized AGS step with `A_{n₀} = 2^40(q+1)^5H²` | `MonoidProduct.hasDual_eqProd_localStep`, `MonoidProduct.qQuery_eqProd_localStep`, `MonoidProduct.qQuery_eqProd_localStep_paper`, `MonoidProduct.hasDual_eqProd_step_strict`, `MonoidProduct.agsStep` | `MonoidProduct/Quantum/PaperForms.lean`, `MonoidProduct/Aperiodic/Induction.lean` | Dual clause exactly with `A_{n₀}`; query clause with `c₀ = 37` (sharper: `294912·A_{n₀}·(B+1)·√n`), native model. |
| `thm:main-ags` | `Q_{1/3} ≤ min{n, √n(2^55(\|M\|+1)^6(log₂(n+1)+3)²)^{d_J+1}}` | `MonoidProduct.ags_oneHotQQuery_le_display_logb`, `MonoidProduct.ags_qQuery_le_display_logb`, `MonoidProduct.ags_qQuery_le_display`, `MonoidProduct.ags_qQuery_le_min`, `MonoidProduct.advPM_wordProd_le`, `MonoidProduct.hasDual_eqProd` | `MonoidProduct/Quantum/AGSApplications.lean`, `MonoidProduct/Aperiodic/Induction.lean` | `2^55` in the one-hot model, `2^54` in the native model; the `min{n, ·}` cap is in the `…_le_min` forms. |
| (remark after `thm:main-ags`) | `d_J = m` for the union semilattice | `MonoidProduct.UnionSet.jDepth_eq` | `MonoidProduct/Width/SmallClauses.lean` | |
| `thm:dyck-lb` | `Q(Dyck_{k,n}) = Ω(c^k√n)`, and `Ω(n^{1−ε})` for `k ≥ c'_ε log₂ n` | `MonoidProduct.dyckLB_qQuery`, `MonoidProduct.sqrt_mul_sqrt_two_pow_le_advPM_dyck` | `MonoidProduct/Quantum/DyckLanguageLower.lean`, `MonoidProduct/Dyck/Lower.lean` | Proved in the library, not assumed: `c = 2^{1/20}`, even `n`, and `k ≥ 1` in the first part. |
| `prop:dyck-monoid` | Normal form of `M_k`; `\|M_k\| = Θ(k³)`; aperiodic; `d_J = k+1`; neither `R`- nor `L`-trivial | `MonoidProduct.DyckTriple`, `MonoidProduct.DyckNF.toEnd_injective`, `MonoidProduct.card_dyckNF_closed`, `MonoidProduct.card_dyckNF_theta`, `MonoidProduct.jDepth_dyckNF`, `MonoidProduct.not_isRTrivialMonoid_dyckNF`, `MonoidProduct.not_isLTrivial_dyckNF`, `MonoidProduct.dyckNF_not_commutative` | `MonoidProduct/Dyck/Monoid/NormalForm.lean`, `MonoidProduct/Dyck/Monoid/Green.lean`, `MonoidProduct/Dyck/Breadth.lean` | The aperiodicity instance is in `Dyck/Monoid/Green.lean`. |
| `cor:dyck` | `Q(Prod_{M_k,n}) = Ω(√n·c^{d_J})`; (i) no bound `f(\|M\|)√n` with `f = exp(o(\|M\|^{1/3}))`; (iii) `Ω(n^{1−ε})` at size `O(log³ n)` | `MonoidProduct.envD_dyck_qQuery_lower`, `MonoidProduct.envD_dyck_qQuery_lower_card`, `MonoidProduct.envD_dyck_no_subexp_bound`, `MonoidProduct.dyckNL_nearLinear_lower`, `MonoidProduct.dyck_qQuery_sandwich` | `MonoidProduct/Quantum/EnvelopeDisplays.lean`, `MonoidProduct/Quantum/DyckNearLinear.lean`, `MonoidProduct/Quantum/DyckApplications.lean` | Base `2^{1/20}` with leading constant `7/(11008·2^{1/20})`, every `n`. Clause (ii) compares this bound with `thm:main-ags`. |
| `prop:dyck-breadth` | `β_G(M_k) = β_{M_k}(M_k) = max{2k,3k−2}` | `MonoidProduct.breadth_dyck` | `MonoidProduct/Dyck/Breadth.lean` | |

## A cube-root bound in terms of monoid size (`sec:ags-cuberoot-size`)

The cube-root construction works with dual adversary costs throughout. A
lemma the paper phrases with query costs appears in Lean with the cost of an
all-pairs dual, or with the length- and alphabet-uniform contract
`HasWordProdDualPoly`, and is converted to a query bound once, at the end.

| Paper label | Statement | Lean declaration(s) | File | Notes |
| --- | --- | --- | --- | --- |
| `lem:ags-green-stability` | `a J b` and `aH ⊆ bH` ⇒ `a R b`, and dually | `MonoidProduct.rEq_of_twoIdeal_eq_of_rLe`, `MonoidProduct.lEq_of_twoIdeal_eq_of_lLe` | `MonoidProduct/Aperiodic/CubeRoot/Green.lean` | |
| `lem:ags-owner-cover` | The regular-owner cover is onto and intertwines the actions | `MonoidProduct.exists_minimalOwner`, `MonoidProduct.ownerCover_surjective`, `MonoidProduct.ownerCover_intertwine` | `MonoidProduct/Aperiodic/CubeRoot/FiniteAction.lean` | |
| `lem:ags-action-compiler` | Orbit endpoint and first death | `MonoidProduct.hasDual_actionPacket` | `MonoidProduct/Aperiodic/CubeRoot/ActionCompiler.lean` | Dual cost `2\|M\|(B√n + 2)`. |
| `lem:ags-target-action` | The target-reachability action; `MtM ⊆ MpM ⊆ MeM` | `MonoidProduct.targetAction`, `MonoidProduct.targetAction_run_eq_iff`, `MonoidProduct.regHeight_drop` | `MonoidProduct/Aperiodic/CubeRoot/TargetAction.lean` | The owner is taken at the chosen point `p` of the component. |
| `prop:ags-axis-recurrence`, `eq:ags-axis-solved` | The regular-axis recurrence and its solution | `MonoidProduct.axisBoundUpTo_zero`, `MonoidProduct.axisBoundUpTo_succ`, `MonoidProduct.axisBoundUpTo_pow` | `MonoidProduct/Aperiodic/CubeRoot/AxisRecurrence.lean` | Under a horizon budget `ℓ + h ≤ H`. |
| `prop:ags-action-height` | Action compiler by regular height | `MonoidProduct.hasDual_actionPacket_of_regHeight` | `MonoidProduct/Aperiodic/CubeRoot/AxisRecurrence.lean` | |
| `lem:ags-matrix-rank-ceiling` | Equal rank ⇒ `J`-equivalent; strict regular chains have at most `d` steps | `MonoidProduct.twoIdeal_eq_of_mrank_eq`, `MonoidProduct.regHeight_le_deg` | `MonoidProduct/Aperiodic/CubeRoot/MatrixRank.lean` | |
| (matrix-image compiler) | Products in a faithful matrix image | `MonoidProduct.hasWordProdDualUpTo_of_faithful` | `MonoidProduct/Aperiodic/CubeRoot/MatrixWord.lean` | |
| `lem:ags-munn-decomposition` | Surjective simple coordinates, nilpotent kernel, `d_J² ≤ \|J\|` | `MonoidProduct.PrincipalFactor.coordAlgHom_surjective`, `MonoidProduct.PrincipalFactor.ker_jointAlgHom_pow_card`, `MonoidProduct.PrincipalFactor.rank_sq_le_card_jClass` | `MonoidProduct/Aperiodic/CubeRoot/PrincipalMatrix.lean`, `MonoidProduct/Aperiodic/CubeRoot/MunnPackage.lean` | Over the full rational monoid algebra rather than the contracted one. |
| (small-coordinate assembly) | Assembly over the simple coordinates | `MonoidProduct.hasWordProdDualPoly_mrange`, `MonoidProduct.ApexPackage.bottomCoord_injective` | `MonoidProduct/Aperiodic/CubeRoot/Assembly.lean` | |
| `lem:ags-fixed-apex-peel`, `eq:ags-fixed-apex-drop` | Fixed-apex Rees peel; `\|M/I_J\| ≤ \|M\| − d_J² + 1` | `MonoidProduct.ApexAdapter.hasWordProdDualPoly_apexCoord`, `MonoidProduct.ReesQuot.card_reesQuot_add_sq_le`, `MonoidProduct.ReesQuot.card_reesQuot_lt` | `MonoidProduct/Aperiodic/CubeRoot/ApexAdapter.lean`, `MonoidProduct/Aperiodic/CubeRoot/Rees.lean` | |
| `lem:ags-square-zero-lift` | Square-zero product lift | `MonoidProduct.LocallyThin.liftsWordProd_of_locallyThin`, `MonoidProduct.LocallyThin.locallyThinKernel_of_squareZero` | `MonoidProduct/Aperiodic/CubeRoot/LocallyThinCompiler.lean`, `MonoidProduct/Aperiodic/CubeRoot/LocallyThin.lean` | No characteristic-zero hypothesis is needed. |
| (radical lift) | Lifting through the radical | `MonoidProduct.ApexPackage.radical_lift'`, `MonoidProduct.ApexPackage.hasWordProdDualPoly_tower` | `MonoidProduct/Aperiodic/CubeRoot/RadicalTower.lean` | |
| `prop:ags-cuberoot-recurrence`, `eq:ags-cuberoot-recurrence-solved` | `C_N ≤ (NL)^{O(t + (N/t²+1)log N)}` for every `t ≥ 2` | `MonoidProduct.solvRec_hasWordProdDualPoly`, `MonoidProduct.solvRec_qQuery_le`, `MonoidProduct.ApexPackage.hasWordProdDualPoly_step`, `MonoidProduct.hasWordProdDualPoly_rec` | `MonoidProduct/Aperiodic/CubeRoot/SolvedRecurrence.lean`, `MonoidProduct/Aperiodic/CubeRoot/Assembly.lean`, `MonoidProduct/Aperiodic/CubeRoot/Main.lean` | The induction runs over monoids of bounded order rather than through a maximum `C_s`; explicit exponent `256·(t + (s/t²+1)⌈log₂(s+2)⌉)`. |
| `thm:ags-cuberoot-size` | See Main results | `MonoidProduct.aperiodic_qQuery_final_exact`, `MonoidProduct.aperiodic_qQuery_paper_real` | `MonoidProduct/Quantum/CubeRootApplications.lean` | |
| `prop:dyck-munn-peel` | (i) inverse monoid; (ii) Brandt principal factors, `d_{J_s} = s+1`; (iii) `ℚ₀[M_k] ≅ ⊕ M_{s+1}(ℚ)` with zero radical; (iv) `M_k/I_k ≅ M_{k−1}` | `MonoidProduct.DyckNF.inv`, `MonoidProduct.mul_inv_mul`, `MonoidProduct.live_mul_live_of_eq`, `MonoidProduct.dyck_sandwichMat_rank`, `MonoidProduct.dyck_card_jClass`, `MonoidProduct.dyckContractedEquiv`, `MonoidProduct.jacobson_dyckContracted`, `MonoidProduct.peelHom`, `MonoidProduct.peel_injOn`, `MonoidProduct.card_dyckNF_succ` | `MonoidProduct/Dyck/Monoid/Peel.lean`, `MonoidProduct/Dyck/Monoid/Sandwich.lean`, `MonoidProduct/Dyck/Monoid/Algebra.lean` | |
| `prop:brandt-two-colour` | `q₂ ≤ q_k ≤ C(q₂ + √n)`; `Ω(√n) ≤ Q ≤ O(√n log^A(n+2))` | `MonoidProduct.Infix.brandt_two_colour`, `MonoidProduct.Infix.brandt_qQuery_theta`, `MonoidProduct.Infix.brandt_qQuery_sqrt_log` | `MonoidProduct/Quantum/BrandtTwoColour.lean` | `C = 10^8`; the final display holds with `A = 1`. |
| `thm:aperiodic-envelope` | `𝒬_ap(N,n) ≤ min{n, √n·2^{CN^{1/3}}L(n)^{CN^{1/3}log^{1/3}(N+2)}}`; `𝒬_ap(N,n) ≥ √n·2^{bN^{1/3}}` for `N₀ ≤ N ≤ a log³(n+2)` | `MonoidProduct.aperiodicEnvelope`, `MonoidProduct.envD_aperiodic_envelope`, `MonoidProduct.envD_aperiodicEnvelope_le_display`, `MonoidProduct.envD_aperiodicEnvelope_lower_paper` | `MonoidProduct/Quantum/Envelope.lean`, `MonoidProduct/Quantum/EnvelopeDisplays.lean` | `aperiodicEnvelope N n` is the supremum over aperiodic monoids of order at most `N`, in the native model. |
| `cor:aperiodic-envelope-transition` | `N ≥ C_ε log³(n+2) ⇒ Ω(n^{1−ε})`; `N ≥ ⌊n/2⌋+1 ⇒ Θ(n)` | `MonoidProduct.dyckNL_aperiodicEnvelope_nearLinear`, `MonoidProduct.aperiodic_envelope_linear` | `MonoidProduct/Quantum/DyckNearLinear.lean`, `MonoidProduct/Quantum/Envelope.lean` | `(7/11008)·n ≤ 𝒬_ap(N,n) ≤ n` in the linear regime. |

## Not formalized in this release

Every labelled theorem, lemma, proposition and corollary of the paper has a
Lean counterpart above. The following parts of labelled examples are cited
from the literature and are not formalized:

- `ex:max`: the maximum-finding lower bound;
- `ex:union`: the query lower bound `Ω(min{n,√(nm)})`.

Some statements are formalized in a slightly different form:

- `ex:spanning-forest`: `β ≤ v−1` is proved; the equality `β = v−1` is not.
- `prop:jtrivial-log-fails`: the lower bound is proved; the informal
  conclusion that no uniform `Õ(√(n log|M|))` bound exists is not stated.
- `lem:beta-sampling`, `lem:beta-rank-doubling`: every clause is proved for
  general parameters (the sampling parameter choice for dyadic `N`); the
  packaged cost bounds are proved in the iterated form used by
  `thm:ordered-beta-log-product`.
- `cor:dyck` (iii): proved with height `dyckNL_height ⌈1/ε⌉ n = O_ε(log n)`
  for `0 < ε < 1`.
- Several intermediate lemmas of `sec:width` and `sec:ags` are stated for
  adversary duals (`HasDual`); the query forms follow from the library's
  conversions.
