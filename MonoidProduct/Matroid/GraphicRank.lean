import MonoidProduct.Matroid.Graphic
import MonoidProduct.Matroid.GreedyMonoid
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The rank of the graphic matroid and the breadth of minimum spanning forests

This file proves the equality `β = v - 1` of the example `ex:spanning-forest` in `monoid.tex`
(section `sec:overview`): on `v ≥ 1` vertices, the monoid of minimum spanning forests (with a
fixed order breaking weight ties) has product breadth exactly `v - 1`.

* `eRank_graphicMatroid`: the graphic matroid `graphicMatroid V` of `Graphic.lean` has rank
  exactly `#V - 1`.  The upper bound is `eRank_graphicMatroid_le_card`.  For the lower bound,
  a base `B` is a maximal forest, so every pair of vertices is connected by `B` (otherwise the
  edge joining them would extend `B` to a larger forest); hence `B` spans a connected graph,
  and `#V ≤ #B + 1` by `natCard_le_ncard_add_natCard`.
* `spanningForest_breadth_eq`: the unweighted form (all weights equal, so the tie-breaking
  order alone decides): in the greedy-basis monoid of `graphicMatroid V`, with letters the
  edges `Sym2 V` (`greedyBasisLetter`), the product breadth is `#V - 1`.
* `weightedGraphicMatroid V W`: the matroid on weighted edges `W ×ₗ Sym2 V` in which a set is
  independent when its edges are distinct and form a forest (copies of the same edge with
  different weights are parallel).  The lexicographic order compares weights first and breaks
  ties by the public edge order, so the greedy basis of a set of weighted edges is its
  minimum spanning forest with that tie-breaking rule, and the product of the greedy-basis
  monoid is the operation of `ex:spanning-forest`.
  `weightedSpanningForest_breadth_eq`: its product breadth is `#V - 1`.
* `ex_spanning_forest`: the equality `β = v - 1` together with the adjacency-array bound
  `adjacencyArray_minSpanningForest_qQuery_le` for the canonical minimum spanning forest of
  the weighted edges listed in adjacency arrays with public degrees.
-/

namespace MonoidProduct.Matroid

open Set SimpleGraph QuantumQueryComplexity

/-! ### The rank of the graphic matroid -/

section Rank

variable {V : Type*}

/-- A base of the graphic matroid (a maximal forest) connects every pair of vertices. -/
lemma reachable_of_isBase_graphicMatroid [Finite V] {B : Set (Sym2 V)}
    (hB : (graphicMatroid V).IsBase B) (u v : V) : (fromEdgeSet B).Reachable u v := by
  by_contra hnr
  have huv : u ≠ v := fun h => hnr (h ▸ Reachable.refl u)
  have hnB : s(u, v) ∉ B := fun h => hnr ((fromEdgeSet_adj _).2 ⟨h, huv⟩).reachable
  have hI := graphicMatroid_indep_iff.1 hB.indep
  have hins : (graphicMatroid V).Indep (insert s(u, v) B) := by
    refine graphicMatroid_indep_iff.2 ⟨fun e he => ?_, ?_⟩
    · rcases Set.mem_insert_iff.1 he with rfl | he
      · exact fun h => huv (Sym2.mk_isDiag_iff.1 h)
      · exact hI.1 e he
    · rw [fromEdgeSet_insert_mk]
      exact hI.2.sup_edge_of_not_reachable hnr
  exact hnB (hB.eq_of_subset_indep hins (Set.subset_insert _ _) ▸ Set.mem_insert _ _)

/-- **The graphic matroid has rank exactly `#V - 1`** (`Nat.card` form). -/
theorem eRank_graphicMatroid_natCard [Finite V] [Nonempty V] :
    (graphicMatroid V).eRank = ((Nat.card V - 1 : ℕ) : ℕ∞) := by
  refine le_antisymm eRank_graphicMatroid_le ?_
  obtain ⟨B, hB⟩ := (graphicMatroid V).exists_isBase
  rw [← hB.encard_eq_eRank, ← (Set.toFinite B).cast_ncard_eq, Nat.cast_le]
  have hsub : Subsingleton (fromEdgeSet B).ConnectedComponent := by
    refine ⟨fun c d => ?_⟩
    induction c using ConnectedComponent.ind with
    | h u =>
      induction d using ConnectedComponent.ind with
      | h v => exact ConnectedComponent.eq.2 (reachable_of_isBase_graphicMatroid hB u v)
  have h1 : Nat.card (fromEdgeSet B).ConnectedComponent ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.2 hsub
  have h2 := natCard_le_ncard_add_natCard B
  omega

/-- **The graphic matroid has rank exactly `#V - 1`.** -/
theorem eRank_graphicMatroid (V : Type*) [Fintype V] [Nonempty V] :
    (graphicMatroid V).eRank = ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
  rw [← Nat.card_eq_fintype_card]
  exact eRank_graphicMatroid_natCard

end Rank

/-! ### Product breadth of the spanning-forest monoid -/

section Breadth

variable (V : Type) [Fintype V] [Nonempty V] [LinearOrder (Sym2 V)]

/-- **`ex:spanning-forest`, unweighted form**: in the greedy-basis monoid of the graphic
matroid, whose letters are the edges and whose product is the spanning forest chosen greedily
in the public edge order, the product breadth is `#V - 1`. -/
theorem spanningForest_breadth_eq :
    breadth (greedyBasisLetter (graphicMatroid V) graphicMatroid_ground) =
      Fintype.card V - 1 :=
  greedyBasis_breadth_eq_rank (eRank_graphicMatroid V)

variable (W : Type) [LinearOrder W]

/-- The **matroid of weighted edges** of `ex:spanning-forest`: a set of weighted edges
`(w, e) ∈ W ×ₗ Sym2 V` is independent when its edges are distinct and form a forest.  The
lexicographic order compares weights first and breaks ties by the public edge order, so the
greedy basis of a finite set of weighted edges is its minimum spanning forest. -/
def weightedGraphicMatroid : _root_.Matroid (W ×ₗ Sym2 V) :=
  (graphicMatroid V).comap fun p => (ofLex p).2

omit [Nonempty V] [LinearOrder (Sym2 V)] [LinearOrder W] in
lemma weightedGraphicMatroid_ground : (weightedGraphicMatroid V W).E = univ := by
  simp [weightedGraphicMatroid, graphicMatroid_ground]

omit [LinearOrder (Sym2 V)] [LinearOrder W] in
/-- The weighted-edge matroid has the rank of the graphic matroid, `#V - 1`. -/
theorem eRank_weightedGraphicMatroid [Nonempty W] :
    (weightedGraphicMatroid V W).eRank = ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  have hsurj : Function.Surjective fun p : W ×ₗ Sym2 V => (ofLex p).2 :=
    fun e => ⟨toLex (w, e), rfl⟩
  rw [_root_.Matroid.eRank_def, weightedGraphicMatroid_ground, weightedGraphicMatroid,
    _root_.Matroid.eRk_comap, Set.image_univ_of_surjective hsurj, ← graphicMatroid_ground,
    ← _root_.Matroid.eRank_def]
  exact eRank_graphicMatroid V

/-- **`ex:spanning-forest`**: weighted edges on `v = #V` vertices, with the public edge order
breaking weight ties, summarized by their minimum spanning forest; the product breadth of
this monoid is `β = v - 1`. -/
theorem weightedSpanningForest_breadth_eq [Nonempty W] :
    breadth (greedyBasisLetter (weightedGraphicMatroid V W)
      (weightedGraphicMatroid_ground V W)) = Fintype.card V - 1 :=
  greedyBasis_breadth_eq_rank (eRank_weightedGraphicMatroid V W)

end Breadth

/-! ### The example `ex:spanning-forest` -/

section Example

variable {V W : Type} [Fintype V] [Nonempty V] [LinearOrder V] [LinearOrder (Sym2 V)]
  [Fintype W] [Nonempty W] [LinearOrder W]

/-- **`ex:spanning-forest`**: the minimum-spanning-forest monoid on `v = #V` vertices has
product breadth `β = v - 1`, and in the adjacency-array model with public degrees `deg` the
canonical minimum spanning forest costs `Q_{1/3} ≤ min{m, 2^18·√(m·β)}`, where `m = ∑ᵥ deg v`
is the total array length. -/
theorem ex_spanning_forest (deg : V → ℕ) :
    breadth (greedyBasisLetter (weightedGraphicMatroid V W)
      (weightedGraphicMatroid_ground V W)) = Fintype.card V - 1 ∧
    (qQuery (fun y : (Σₗ v : V, Fin (deg v)) → V × W =>
        basisIndices (graphicMatroid V) (adjacencyArrayRecords deg y) Finset.univ) (1 / 3) : ℝ)
      ≤ min ((∑ v, deg v : ℕ) : ℝ)
        (2 ^ 18 * Real.sqrt (((∑ v, deg v : ℕ) : ℝ) * (Fintype.card V - 1 : ℕ))) :=
  ⟨weightedSpanningForest_breadth_eq V W, adjacencyArray_minSpanningForest_qQuery_le deg⟩

end Example

end MonoidProduct.Matroid
