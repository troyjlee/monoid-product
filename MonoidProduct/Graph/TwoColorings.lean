import MonoidProduct.Graph.Components
import Mathlib.Combinatorics.SimpleGraph.Bipartite
set_option linter.style.header false

/-!
# Two-colourings and bipartiteness: certificates of at most `v` edges

`monoid.tex`, section `sec:graph-certificates`, paragraph "Bipartiteness".  Write `v = #V`.
The set `𝒞(G)` of **all** proper two-colourings has strong certificates of at most `v` edges.
So do bipartiteness and a canonical proper two-colouring.

* `twoColorings S : Finset (V → Fin 2)` is the set of maps `c` with `c u ≠ c w` for every edge
  `{u, w}` of `S` (`mem_twoColorings`).  Union of graphs is intersection of these sets
  (`twoColorings_union`), so `C ∼_𝒞 S`, for every extension, exactly when `𝒞(C) = 𝒞(S)`
  (`extensionEquiv_twoColorings_iff`).
* Two proper two-colourings of a graph either agree on all of a connected component or
  disagree on all of it (`eq_iff_eq_of_reachable`).
* If `S` is bipartite, a spanning forest has the same two-colourings.  A colouring `c'` of the
  forest is compared with a colouring of `S` on each component.
* Otherwise, take a spanning forest and one of its proper two-colourings, which some edge `uw`
  of `S` violates.  The forest connects `u` and `w`.  Every proper colouring of the forest
  therefore gives `u` and `w` the same colour, so the forest plus `uw` has no proper
  two-colouring at all.  This certificate has at most `(v - 1) + 1 = v` edges.  It replaces the
  paper's odd cycle and needs no odd-cycle characterization.
* `twoColorings_strongCertificateSize_le`: `b_𝒞 ≤ v`.  Postprocessing then gives
  `bipartite_strongCertificateSize_le` and `properTwoColoring_strongCertificateSize_le`, with
  the certificates `hasStrongCertificateBound_isBipartite` and
  `hasStrongCertificateBound_properTwoColoring`.
-/

namespace MonoidProduct.Graph

open SimpleGraph Certificates

variable {V : Type*}

/-! ## Colourings along walks -/

private theorem fin_two_eq_iff_eq_of_ne :
    ∀ a b a' b' : Fin 2, a ≠ b → a' ≠ b' → (a = a' ↔ b = b') := by
  decide

private theorem fin_two_ne_of_eq_iff_eq :
    ∀ a b a' b' : Fin 2, a ≠ b → (a = a' ↔ b = b') → a' ≠ b' := by
  decide

private theorem fin_two_eq_of_eq_iff_eq :
    ∀ a b a' b' : Fin 2, a = b → (a = a' ↔ b = b') → a' = b' := by
  decide

/-- **Two proper two-colourings agree on a whole component or disagree on all of it**: for
connected `u` and `w`, `c u = c' u ↔ c w = c' w`. -/
theorem eq_iff_eq_of_reachable {H : SimpleGraph V} {c c' : V → Fin 2}
    (hc : ∀ u w, H.Adj u w → c u ≠ c w) (hc' : ∀ u w, H.Adj u w → c' u ≠ c' w) {u w : V}
    (h : H.Reachable u w) : (c u = c' u ↔ c w = c' w) := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Iff.rfl
  | tail _ hab ih => exact ih.trans (fin_two_eq_iff_eq_of_ne _ _ _ _ (hc _ _ hab) (hc' _ _ hab))

/-! ## The set of proper two-colourings -/

section Colorings

variable [Fintype V] [DecidableEq V]

/-- **All proper two-colourings** `𝒞(S)`: the maps `c : V → Fin 2` with `c u ≠ c w` for every
edge `{u, w}` of `S`. -/
noncomputable def twoColorings (S : Finset (Edge V)) : Finset (V → Fin 2) := by
  classical exact Finset.univ.filter fun c => ∀ u w, (toGraph S).Adj u w → c u ≠ c w

@[simp] theorem mem_twoColorings {S : Finset (Edge V)} {c : V → Fin 2} :
    c ∈ twoColorings S ↔ ∀ u w, (toGraph S).Adj u w → c u ≠ c w := by
  simp [twoColorings]

/-- The proper two-colourings of `S` are the Mathlib colourings of `toGraph S` by `Fin 2`. -/
theorem mem_twoColorings_iff_exists_coloring {S : Finset (Edge V)} {c : V → Fin 2} :
    c ∈ twoColorings S ↔ ∃ C : (toGraph S).Coloring (Fin 2), ⇑C = c := by
  rw [mem_twoColorings]
  exact ⟨fun h => ⟨Coloring.mk c fun {u w} huw => h u w huw, rfl⟩,
    fun ⟨C, hC⟩ u w huw => hC ▸ C.valid huw⟩

/-- **Union is intersection**: `𝒞(S ∪ T) = 𝒞(S) ∩ 𝒞(T)`. -/
theorem twoColorings_union (S T : Finset (Edge V)) :
    twoColorings (S ∪ T) = twoColorings S ∩ twoColorings T := by
  ext c
  simp only [Finset.mem_inter, mem_twoColorings, toGraph_union, sup_adj]
  exact ⟨fun h => ⟨fun u w huw => h u w (Or.inl huw), fun u w huw => h u w (Or.inr huw)⟩,
    fun h u w huw => huw.elim (h.1 u w) (h.2 u w)⟩

/-- More edges, fewer colourings. -/
theorem twoColorings_anti {S T : Finset (Edge V)} (h : S ⊆ T) :
    twoColorings T ⊆ twoColorings S := fun c hc => by
  rw [mem_twoColorings] at hc ⊢
  exact fun u w huw => hc u w (toGraph_mono h huw)

/-- **A graph is bipartite exactly when it has a proper two-colouring.** -/
theorem twoColorings_nonempty_iff {S : Finset (Edge V)} :
    (twoColorings S).Nonempty ↔ (toGraph S).IsBipartite := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨C, -⟩ := mem_twoColorings_iff_exists_coloring.mp hc
    exact ⟨C⟩
  · rintro ⟨C⟩
    exact ⟨C, mem_twoColorings_iff_exists_coloring.mpr ⟨C, rfl⟩⟩

/-- **Equivalence under extensions is equality of the colouring sets**, since union is
intersection. -/
theorem extensionEquiv_twoColorings_iff {S T : Finset (Edge V)} :
    ExtensionEquiv twoColorings S T ↔ twoColorings S = twoColorings T :=
  extensionEquiv_iff_of_merge (f := twoColorings) fun S S' T T' hS hT => by
    rw [twoColorings_union, twoColorings_union, hS, hT]

/-! ## Certificates -/

/-- **Bipartite inputs**: if `S` has a proper two-colouring and `C ⊆ S` connects every edge of
`S`, then `C` has the same proper two-colourings as `S`. -/
theorem twoColorings_eq_of_reachable {C S : Finset (Edge V)} (hCS : C ⊆ S)
    (hreach : ∀ u w, (toGraph S).Adj u w → (toGraph C).Reachable u w)
    (hS : (twoColorings S).Nonempty) : twoColorings C = twoColorings S := by
  obtain ⟨c, hc⟩ := hS
  refine (Finset.Subset.antisymm_iff.mpr ⟨fun c' hc' => ?_, twoColorings_anti hCS⟩)
  rw [mem_twoColorings] at hc hc' ⊢
  intro u w huw
  have hcC : ∀ a b, (toGraph C).Adj a b → c a ≠ c b := fun a b h => hc a b (toGraph_mono hCS h)
  exact fin_two_ne_of_eq_iff_eq _ _ _ _ (hc u w huw)
    (eq_iff_eq_of_reachable hcC hc' (hreach u w huw))

/-- **Nonbipartite inputs**: if a proper two-colouring `c` of `C` gives both ends of a pair
`uw` connected in `C` the same colour, then `C` plus the edge `uw` has no proper
two-colouring. -/
theorem twoColorings_insert_eq_empty {C : Finset (Edge V)} {e : Edge V} {u w : V}
    (he : (e : Sym2 V) = s(u, w)) {c : V → Fin 2} (hc : c ∈ twoColorings C) (hcuw : c u = c w)
    (hreach : (toGraph C).Reachable u w) : twoColorings (insert e C) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun c' hc' => ?_
  have hc'C : c' ∈ twoColorings C := twoColorings_anti (Finset.subset_insert e C) hc'
  have hagree := eq_iff_eq_of_reachable (mem_twoColorings.mp hc) (mem_twoColorings.mp hc'C)
    hreach
  have hadj : (toGraph (insert e C)).Adj u w :=
    toGraph_adj.mpr ⟨e, Finset.mem_insert_self e C, he⟩
  exact mem_twoColorings.mp hc' u w hadj (fin_two_eq_of_eq_iff_eq _ _ _ _ hcuw hagree)

/-- **Every graph has a strong certificate for its two-colourings with at most `v` edges**: a
spanning forest, plus one edge when the graph is not bipartite. -/
theorem hasStrongCertificateBound_twoColorings :
    HasStrongCertificateBound (twoColorings (V := V)) (Fintype.card V) := fun S => by
  obtain ⟨C, hCS, hC, hreach⟩ := exists_spanningForest S
  have hcard := card_le_of_isAcyclic hC
  have hconn : ∀ u w, (toGraph S).Adj u w → (toGraph C).Reachable u w := fun u w huw => by
    rw [hreach]
    exact huw.reachable
  by_cases hbip : (twoColorings S).Nonempty
  · exact ⟨C, ⟨hCS, extensionEquiv_twoColorings_iff.mpr
      (twoColorings_eq_of_reachable hCS hconn hbip)⟩, hcard.trans (Nat.sub_le _ _)⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hbip
    let c : V → Fin 2 := hC.coloringTwo
    have hcC : c ∈ twoColorings C := mem_twoColorings_iff_exists_coloring.mpr ⟨hC.coloringTwo, rfl⟩
    have hcS : c ∉ twoColorings S := by
      rw [hbip]
      exact Finset.notMem_empty c
    rw [mem_twoColorings] at hcS
    push Not at hcS
    obtain ⟨u, w, huw, hcuw⟩ := hcS
    obtain ⟨e, heS, he⟩ := toGraph_adj.mp huw
    have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    refine ⟨insert e C, ⟨Finset.insert_subset heS hCS, extensionEquiv_twoColorings_iff.mpr ?_⟩,
      (Finset.card_insert_le e C).trans (by omega)⟩
    rw [hbip]
    exact twoColorings_insert_eq_empty he hcC hcuw (hconn u w huw)

/-- **All proper two-colourings** (`sec:graph-certificates`): `b_𝒞 ≤ v`. -/
theorem twoColorings_strongCertificateSize_le :
    strongCertificateSize (twoColorings (V := V)) ≤ Fintype.card V :=
  strongCertificateSize_le hasStrongCertificateBound_twoColorings

end Colorings

/-! ## Bipartiteness and a canonical colouring -/

/-- **Bipartiteness**: whether `toGraph S` is bipartite, that is, two-colourable (Mathlib's
`IsBipartite`, which is `Colorable 2`). -/
noncomputable def isBipartite (S : Finset (Edge V)) : Bool := by
  classical exact decide (toGraph S).IsBipartite

theorem isBipartite_eq_true_iff {S : Finset (Edge V)} :
    isBipartite S = true ↔ (toGraph S).IsBipartite := by
  simp [isBipartite]

/-- A fixed choice of an element of a set of colourings, or `none` for the empty set. -/
noncomputable def chooseColoring (A : Finset (V → Fin 2)) : Option (V → Fin 2) :=
  if h : A.Nonempty then some h.choose else none

theorem chooseColoring_mem {A : Finset (V → Fin 2)} {c : V → Fin 2}
    (h : chooseColoring A = some c) : c ∈ A := by
  unfold chooseColoring at h
  split_ifs at h with hA
  exact Option.some_injective _ h ▸ hA.choose_spec

theorem chooseColoring_eq_none_iff {A : Finset (V → Fin 2)} :
    chooseColoring A = none ↔ A = ∅ := by
  unfold chooseColoring
  split_ifs with hA
  · simp [hA.ne_empty]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

variable [Fintype V] [DecidableEq V]

/-- **A canonical proper two-colouring, or failure**: `some c` for a fixed proper two-colouring
`c` of `toGraph S` when one exists, and `none` when `toGraph S` is not bipartite.  It is a
function of `𝒞(S)`. -/
noncomputable def properTwoColoring (S : Finset (Edge V)) : Option (V → Fin 2) :=
  chooseColoring (twoColorings S)

/-- The output colouring is proper. -/
theorem properTwoColoring_spec {S : Finset (Edge V)} {c : V → Fin 2}
    (h : properTwoColoring S = some c) : ∀ u w, (toGraph S).Adj u w → c u ≠ c w :=
  mem_twoColorings.mp (chooseColoring_mem h)

/-- The output is `none` exactly for nonbipartite graphs. -/
theorem properTwoColoring_eq_none_iff {S : Finset (Edge V)} :
    properTwoColoring S = none ↔ ¬(toGraph S).IsBipartite := by
  rw [properTwoColoring, chooseColoring_eq_none_iff, ← twoColorings_nonempty_iff,
    Finset.not_nonempty_iff_eq_empty]

/-- **Bipartiteness** (`sec:graph-certificates`): its strong-certificate size is at most `v`. -/
theorem bipartite_strongCertificateSize_le :
    strongCertificateSize (isBipartite (V := V)) ≤ Fintype.card V := by
  classical
  have h : isBipartite (V := V) = fun S => decide (twoColorings S).Nonempty :=
    funext fun S => Bool.eq_iff_iff.mpr
      (isBipartite_eq_true_iff.trans (twoColorings_nonempty_iff.symm.trans decide_eq_true_iff.symm))
  rw [h]
  exact (strongCertificateSize_postcomp_le twoColorings
    (fun A : Finset (V → Fin 2) => decide A.Nonempty)).trans twoColorings_strongCertificateSize_le

/-- **A canonical proper two-colouring, or failure** (`sec:graph-certificates`): its
strong-certificate size is at most `v`. -/
theorem properTwoColoring_strongCertificateSize_le :
    strongCertificateSize (properTwoColoring (V := V)) ≤ Fintype.card V :=
  (strongCertificateSize_postcomp_le twoColorings chooseColoring).trans
    twoColorings_strongCertificateSize_le

/-- **Certificates for bipartiteness**: every graph has a strong certificate of at most `v`
edges. -/
theorem hasStrongCertificateBound_isBipartite :
    HasStrongCertificateBound (isBipartite (V := V)) (Fintype.card V) :=
  hasStrongCertificateBound_iff_size_le.mpr bipartite_strongCertificateSize_le

/-- **Certificates for a canonical proper two-colouring**: every graph has a strong certificate
of at most `v` edges. -/
theorem hasStrongCertificateBound_properTwoColoring :
    HasStrongCertificateBound (properTwoColoring (V := V)) (Fintype.card V) :=
  hasStrongCertificateBound_iff_size_le.mpr properTwoColoring_strongCertificateSize_le

end MonoidProduct.Graph
