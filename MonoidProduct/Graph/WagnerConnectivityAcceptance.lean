import MonoidProduct.Graph.Wagner
import MonoidProduct.Graph.WagnerConnectivity
set_option linter.style.header false

/-!
# Acceptance statements for connectivity, separations and cyclic arcs

The statements of `Graph/WagnerConnectivity.lean` and `Graph/CycleArcs.lean`, restated with the
definitions unfolded where that makes their meaning visible, followed by small sanity checks.  Lean
checks every `example` here against the library's statement.

* `k`-connectivity, its agreement with the Boolean readout, monotonicity, the degree bound, vertex
  deletion and minimum separators.
* Proper separations: from a separator, with smaller sides and with every vertex of a minimum
  separator adjacent to every component of the rest; the marker-edge minors.
* The exclusion of `K₅` and `K₃,₃`, inherited by minors.
* Arcs of cyclic lists: membership, rotation invariance, concatenation and disjointness.

The sanity checks cover:
* arcs of `[0, 1, 2, 3, 4]`, including one across the end of the list, a rotated copy of the list,
  and the three arcs between three marks;
* the cycle `C₄`, which is `2`-connected but not `3`-connected; its separator `{0, 2}` gives a
  proper separation whose marker edge `{0, 2}` is not an edge, and each side with the marker
  edge, a triangle, is a minor of `C₄`;
* `K₄`, which is `3`-connected and has neither excluded minor, and `K₅`, which has one.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-! ## Statements -/

section Statements

variable {V W : Type*} {G : SimpleGraph V}

/-- **`k`-connectivity**: more than `k` vertices, and connected after deleting any fewer than `k`
vertices. -/
example (k : ℕ) : IsKConnected G k ↔
    k < Nat.card V ∧ ∀ S : Finset V, S.card < k → (G.induce {v | v ∉ S}).Connected :=
  Iff.rfl

/-- **The Boolean readout of `Graph/VertexReadouts.lean` agrees.** -/
example [Fintype V] [DecidableEq V] (k : ℕ) (S : Finset (Edge V)) :
    isVertexConnected k S = true ↔ IsKConnected (toGraph S) k :=
  isVertexConnected_eq_true_iff_isKConnected

/-- **Monotonicity, the degree bound and vertex deletion**: a `(k + 1)`-connected graph is
`k`-connected, its vertices have at least `k + 1` neighbours, and deleting any vertex leaves a
`k`-connected graph. -/
example [Finite V] {k : ℕ} (h : IsKConnected G (k + 1)) (z v : V) :
    IsKConnected G k ∧ k + 1 ≤ (G.neighborSet v).ncard ∧ IsKConnected (G.induce {v | v ≠ z}) k :=
  ⟨h.mono (by omega), h.le_ncard_neighborSet v, h.induce_ne z⟩

/-- **Minimum separators.** -/
example {k : ℕ} (hk : k < Nat.card V) (h : ¬ IsKConnected G k) :
    ∃ S : Finset V, S.card < k ∧ ¬ (G.induce {v | v ∉ S}).Connected ∧ IsKConnected G S.card :=
  exists_minimum_separator hk h

/-- **Proper separations**, unfolded. -/
example (A B : Set V) : IsProperSeparation G A B ↔
    A ∪ B = Set.univ ∧ (∀ ⦃u w : V⦄, u ∈ A \ B → w ∈ B \ A → ¬ G.Adj u w) ∧
      (A \ B).Nonempty ∧ (B \ A).Nonempty :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- **A separator gives a proper separation with smaller sides.** -/
example [Finite V] (S : Finset V) (hS : ¬ (G.induce {v | v ∉ S}).Connected) {u : V} (hu : u ∉ S) :
    ∃ A B : Set V, IsProperSeparation G A B ∧ A ∩ B = ↑S ∧ Nat.card A < Nat.card V ∧
      Nat.card B < Nat.card V := by
  obtain ⟨A, B, hAB, hS'⟩ := exists_isProperSeparation S hS hu
  exact ⟨A, B, hAB, hS', hAB.natCard_lt_left, hAB.natCard_lt_right⟩

/-- **Every vertex of a minimum separator has a neighbour in every component of the rest.** -/
example {S : Finset V} (hmin : IsKConnected G S.card) {s v : V} (hs : s ∈ S) (hv : v ∉ S) :
    ∃ d, d ∉ S ∧ (restrictTo G {w | w ∉ S}).Reachable v d ∧ G.Adj s d :=
  exists_adj_reachable hmin hs hv

/-- **Marker edges**: both sides of a proper separation of a `2`-connected graph with separator
`{x, y}`, with the edge `xy` added, are minors of `G`. -/
example {A B : Set V} {x y : V} (h2 : IsKConnected G 2) (hAB : IsProperSeparation G A B)
    (hxy : x ≠ y) (hS : A ∩ B = {x, y}) :
    IsMinor ((G ⊔ edge x y).induce A) G ∧ IsMinor ((G ⊔ edge x y).induce B) G :=
  ⟨isMinor_sup_edge_induce_left h2 hAB hxy hS, isMinor_sup_edge_induce_right h2 hAB hxy hS⟩

/-- **The exclusions**, inherited by minors. -/
example {H : SimpleGraph W} (hG : NoKuratowskiMinor G) (hHG : IsMinor H G) :
    (NoKuratowskiMinor G ↔ ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G ∧
      ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G) ∧ NoKuratowskiMinor H :=
  ⟨Iff.rfl, hG.of_isMinor hHG⟩

variable [DecidableEq V] {C : List V} {a b c v : V}

/-- **Arcs**: membership by distances from the start, and independence of the starting point of
the cyclic list. -/
example (hC : C.Nodup) (ha : a ∈ C) (k : ℕ) :
    (v ∈ arc C a b ↔ v ∈ C ∧ cycDist C a v < cycDist C a b) ∧
    (v ∈ closedArc C a b ↔ v ∈ C ∧ cycDist C a v ≤ cycDist C a b) ∧
    arc (C.rotate k) a b = arc C a b ∧ closedArc (C.rotate k) a b = closedArc C a b :=
  ⟨mem_arc_iff hC, mem_closedArc_iff hC, arc_rotate hC ha k, closedArc_rotate hC ha k⟩

/-- **Successive arcs**: they concatenate and are disjoint, and two arcs between distinct vertices
make up the cycle. -/
example (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) (hab : a ≠ b)
    (h : cycDist C a b ≤ cycDist C a c) :
    arc C a b ++ arc C b c = arc C a c ∧ (arc C a b).Disjoint (arc C b c) ∧
      arc C a b ++ arc C b a = startAt C a :=
  ⟨arc_append_arc hC ha hb hc h, disjoint_arc_arc hC ha hb hc h,
    arc_append_arc_self hC ha hb hab⟩

/-- **Consecutive marks**: every vertex of the cycle lies between one pair of consecutive marks. -/
example (hC : C.Nodup) {X : Finset V} (hXC : ∀ x ∈ X, x ∈ C) (hX : 1 < X.card) (hv : v ∈ C) :
    ∃ p q, IsConsecutive C X p q ∧ v ∈ arc C p q ∧
      ∀ p' q', IsConsecutive C X p' q' → v ∈ arc C p' q' → p' = p ∧ q' = q := by
  obtain ⟨p, q, hpq, hvpq⟩ := exists_isConsecutive_mem_arc hC hXC hX hv
  exact ⟨p, q, hpq, hvpq, fun p' q' h' hv' =>
    (hpq.eq_of_mem_arc hC hXC h' hvpq hv').imp Eq.symm Eq.symm⟩

end Statements

/-! ## Sanity checks: arcs -/

/-- **Arcs of `[0, 1, 2, 3, 4]`**: from `3` to `1` across the end of the list, its closed version,
and the distance `3`. -/
example : arc [0, 1, 2, 3, 4] 3 1 = [3, 4, 0] ∧ closedArc [0, 1, 2, 3, 4] 3 1 = [3, 4, 0, 1] ∧
    cycDist [0, 1, 2, 3, 4] 3 1 = 3 := by
  decide

/-- **Rotation invariance**: the same arc in the rotated list `[2, 3, 4, 0, 1]`. -/
example : arc [2, 3, 4, 0, 1] 3 1 = arc [0, 1, 2, 3, 4] 3 1 := by decide

/-- **Three marks cut the cycle into three arcs.** -/
example : arc [0, 1, 2, 3, 4] 0 2 ++ arc [0, 1, 2, 3, 4] 2 4 ++ arc [0, 1, 2, 3, 4] 4 0 =
    [0, 1, 2, 3, 4] := by
  decide

/-- **A cycle of the cycle graph**, and the connected arc from `3` to `1`. -/
example : IsCycleList (cycleGraph 5) [0, 1, 2, 3, 4] ∧
    IsConnectedSet (cycleGraph 5) {v | v ∈ arc [0, 1, 2, 3, 4] 3 1} := by
  have h : IsCycleList (cycleGraph 5) [0, 1, 2, 3, 4] := by
    unfold IsCycleList
    decide
  exact ⟨h, h.isConnectedSet_arc (by decide) (by decide) (by decide)⟩

/-! ## Sanity checks: `C₄` -/

/-- **`C₄` is `2`-connected but not `3`-connected**: deleting the opposite vertices `0` and `2`
disconnects it. -/
example : IsKConnected (cycleGraph 4) 2 ∧ ¬ IsKConnected (cycleGraph 4) 3 := by
  have hcard : Nat.card (Fin 4) = 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨⟨by rw [hcard]; norm_num, by decide⟩, fun h => ?_⟩
  exact (by decide : ¬ ((cycleGraph 4).induce {v | v ∉ ({0, 2} : Finset (Fin 4))}).Connected)
    (h.2 {0, 2} (by decide))

/-- The separation of `C₄` at `{0, 2}`: the sides `{0, 1, 2}` and `{2, 3, 0}`. -/
private theorem c4_separation :
    IsProperSeparation (cycleGraph 4) ({0, 1, 2} : Set (Fin 4)) ({2, 3, 0} : Set (Fin 4)) := by
  refine ⟨?_, ?_, ⟨1, by decide, by decide⟩, ⟨3, by decide, by decide⟩⟩
  · ext v
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    revert v
    decide
  · intro u w hu hw
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
    revert u w
    decide

/-- **A marker edge that is not an edge**: the separator `{0, 2}` of `C₄` is not an edge, and each
side with the marker edge, a triangle, is a minor of `C₄`. -/
example : ¬ (cycleGraph 4).Adj 0 2 ∧
    IsMinor ((cycleGraph 4 ⊔ edge 0 2).induce ({0, 1, 2} : Set (Fin 4))) (cycleGraph 4) ∧
    IsMinor ((cycleGraph 4 ⊔ edge 0 2).induce ({2, 3, 0} : Set (Fin 4))) (cycleGraph 4) := by
  have h2 : IsKConnected (cycleGraph 4) 2 :=
    ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩
  have hS : ({0, 1, 2} : Set (Fin 4)) ∩ {2, 3, 0} = {0, 2} := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert v
    decide
  exact ⟨by decide, isMinor_sup_edge_induce_left h2 c4_separation (by decide) hS,
    isMinor_sup_edge_induce_right h2 c4_separation (by decide) hS⟩

/-! ## Sanity checks: `K₄` and `K₅` -/

/-- **`K₄` is `3`-connected, has degree `3`, and has neither excluded minor; `K₅` has one.** -/
example : IsKConnected (⊤ : SimpleGraph (Fin 4)) 3 ∧
    3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet 0).ncard ∧
    NoKuratowskiMinor (⊤ : SimpleGraph (Fin 4)) ∧
      ¬ NoKuratowskiMinor (⊤ : SimpleGraph (Fin 5)) := by
  have h3 : IsKConnected (⊤ : SimpleGraph (Fin 4)) 3 :=
    ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩
  exact ⟨h3, h3.le_ncard_neighborSet 0, isPlanar_top_four.wagner_easy,
    fun h => h.1 (IsMinor.refl _)⟩

end MonoidProduct.Graph
