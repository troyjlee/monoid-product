import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.OrderOfElement
import MonoidProduct.Graph.Planar
set_option linter.style.header false

/-!
# Planar and nonplanar examples

Checks that `IsPlanar` (`Graph/Planar.lean`) means planarity, and is not an edge-count condition.

* `isPlanar_bot`: a graph without edges is planar; there is no dart.
* `isPlanar_top_four`: the complete graph `K₄` is planar.  The rotation system is read off a
  drawing with `3` inside the triangle `0 1 2` (`k4Next`); its four faces are triangles, so
  `4 − 6 + 4 = 2`.  As `K₄` has `6 = 3·4 − 6` edges, the bound `3v - 6` is attained.
* `not_isPlanar_top_five`: `K₅`, with `10 > 3·5 − 6` edges, is not planar.
* `not_isPlanar_completeBipartite_three_three`: `K₃,₃` is not planar, by the two-colourable bound
  `9 > 2·6 − 4`, although it has `9 ≤ 3·6 − 6` edges.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-! ## No edges -/

/-- **A graph without edges is planar**: it has no darts, and no component has an edge. -/
theorem isPlanar_bot {V : Type*} : IsPlanar (⊥ : SimpleGraph V) := by
  refine ⟨⟨1, fun _ => rfl, fun d => d.adj.elim⟩, fun c ⟨e, he, _⟩ => ?_⟩
  rw [edgeSet_bot] at he
  exact he.elim

/-! ## `K₄` -/

/-- **The rotation of `K₄`**: the neighbour after `w` around `u`, in a drawing with `3` inside
the triangle `0 1 2`.  Row `u` lists `k4Next u w` for `w = 0, 1, 2, 3`; the diagonal is
unused. -/
def k4Next : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 3, 1, 2], ![2, 1, 3, 0], ![3, 0, 2, 1], ![1, 2, 0, 3]]

/-- The inverse rotation of `K₄`. -/
def k4Prev : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 2, 3, 1], ![3, 1, 0, 2], ![1, 3, 2, 0], ![2, 0, 1, 3]]

private theorem k4Next_ne : ∀ u w : Fin 4, u ≠ w → u ≠ k4Next u w := by decide
private theorem k4Prev_ne : ∀ u w : Fin 4, u ≠ w → u ≠ k4Prev u w := by decide
private theorem k4Prev_next : ∀ u w : Fin 4, u ≠ w → k4Prev u (k4Next u w) = w := by decide
private theorem k4Next_prev : ∀ u w : Fin 4, u ≠ w → k4Next u (k4Prev u w) = w := by decide

/-- The rotation at each vertex is one cycle through its three neighbours. -/
private theorem k4_cycle : ∀ u w w' : Fin 4, u ≠ w → u ≠ w' →
    w' = w ∨ w' = k4Next u w ∨ w' = k4Next u (k4Next u w) := by decide

/-- Two steps of a face change the tail. -/
private theorem k4_face_two : ∀ u w : Fin 4, u ≠ w → k4Next w u ≠ u := by decide

/-- Every face returns after three steps. -/
private theorem k4_face : ∀ u w : Fin 4, u ≠ w →
    k4Next (k4Next w u) w = u ∧ k4Next (k4Next (k4Next w u) w) (k4Next w u) = w := by decide

/-- The rotation of `K₄`, as a permutation of its darts. -/
def k4Rot : Equiv.Perm (⊤ : SimpleGraph (Fin 4)).Dart where
  toFun d := ⟨(d.fst, k4Next d.fst d.snd), k4Next_ne _ _ d.adj⟩
  invFun d := ⟨(d.fst, k4Prev d.fst d.snd), k4Prev_ne _ _ d.adj⟩
  left_inv d := Dart.ext _ _ (Prod.ext rfl (k4Prev_next _ _ d.adj))
  right_inv d := Dart.ext _ _ (Prod.ext rfl (k4Next_prev _ _ d.adj))

/-- **The rotation system of `K₄`.** -/
def k4Rotation : RotationSystem (⊤ : SimpleGraph (Fin 4)) where
  rot := k4Rot
  fst_rot _ := rfl
  sameCycle_rot d d' h := by
    have hd' : d.fst ≠ d'.snd := by
      rw [h]
      exact d'.adj
    rcases k4_cycle d.fst d.snd d'.snd d.adj hd' with h' | h' | h'
    · have : d' = d := Dart.ext _ _ (Prod.ext h.symm h')
      subst this
      exact .rfl
    · have : d' = k4Rot d := Dart.ext _ _ (Prod.ext h.symm h')
      subst this
      exact Equiv.Perm.sameCycle_apply_right.mpr .rfl
    · have : d' = k4Rot (k4Rot d) := Dart.ext _ _ (Prod.ext h.symm h')
      subst this
      exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.sameCycle_apply_right.mpr .rfl)

/-- Every face of `K₄` has three darts. -/
theorem k4_face_three (d : (⊤ : SimpleGraph (Fin 4)).Dart) :
    k4Rotation.face (k4Rotation.face (k4Rotation.face d)) = d := by
  obtain ⟨h1, h2⟩ := k4_face d.fst d.snd d.adj
  exact Dart.ext _ _ (Prod.ext h1 h2)

/-- The face of a dart of `K₄`: the dart and its next two. -/
theorem k4_sameCycle_iff (d d' : (⊤ : SimpleGraph (Fin 4)).Dart) :
    k4Rotation.face.SameCycle d d' ↔
      d' = d ∨ d' = k4Rotation.face d ∨ d' = k4Rotation.face (k4Rotation.face d) := by
  constructor
  · intro h
    have h3 : k4Rotation.face ^ 3 = 1 := Equiv.ext fun x => by
      simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact k4_face_three x
    obtain ⟨i, hi, rfl⟩ := h.exists_pow_eq'
    have hi3 := hi.trans_le (orderOf_le_of_pow_eq_one (by norm_num) h3)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (by simp [pow_two]))
  · rintro (rfl | rfl | rfl)
    · exact .rfl
    · exact Equiv.Perm.sameCycle_apply_right.mpr .rfl
    · exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.sameCycle_apply_right.mpr .rfl)

/-- `K₄` has four faces. -/
theorem natCard_k4Face : Nat.card k4Rotation.Face = 4 := by
  classical
  have : Fintype k4Rotation.Face := Fintype.ofFinite _
  -- Each face has three darts.
  have hfib : ∀ q : k4Rotation.Face,
      (Finset.univ.filter fun d : (⊤ : SimpleGraph (Fin 4)).Dart =>
        (⟦d⟧ : k4Rotation.Face) = q).card = 3 := by
    intro q
    induction q using Quotient.inductionOn with
    | h d₀ =>
    have hne1 := k4Rotation.face_ne d₀
    have hne2 := k4Rotation.face_ne (k4Rotation.face d₀)
    have hne3 : k4Rotation.face (k4Rotation.face d₀) ≠ d₀ := fun h =>
      k4_face_two d₀.fst d₀.snd d₀.adj
        (congrArg (fun d : (⊤ : SimpleGraph (Fin 4)).Dart => d.fst) h)
    have hset : (Finset.univ.filter fun d : (⊤ : SimpleGraph (Fin 4)).Dart =>
        (⟦d⟧ : k4Rotation.Face) = ⟦d₀⟧) =
        {d₀, k4Rotation.face d₀, k4Rotation.face (k4Rotation.face d₀)} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [Quotient.eq]
      exact Equiv.Perm.sameCycle_comm.trans (k4_sameCycle_iff d₀ d)
    rw [hset, Finset.card_insert_of_notMem (by simp [Ne.symm hne1, Ne.symm hne3]),
      Finset.card_pair (Ne.symm hne2)]
  have hdarts : Fintype.card (⊤ : SimpleGraph (Fin 4)).Dart = 12 := by
    rw [dart_card_eq_twice_card_edges, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    rfl
  rw [Nat.card_eq_fintype_card]
  have := Finset.card_eq_sum_card_fiberwise (f := fun d : (⊤ : SimpleGraph (Fin 4)).Dart =>
    (⟦d⟧ : k4Rotation.Face)) (s := Finset.univ) (t := Finset.univ)
    fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  rw [Finset.card_univ, hdarts, Finset.sum_congr rfl fun q _ => hfib q, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at this
  omega

/-- In `K₄` all vertices lie in one component. -/
private theorem k4_comp (u w : Fin 4) :
    (⊤ : SimpleGraph (Fin 4)).connectedComponentMk u =
      (⊤ : SimpleGraph (Fin 4)).connectedComponentMk w := by
  by_cases h : u = w
  · rw [h]
  · exact ConnectedComponent.eq.mpr ((top_adj u w).mpr h).reachable

/-- **`K₄` is planar**: `4 − 6 + 4 = 2`. -/
theorem isPlanar_top_four : IsPlanar (⊤ : SimpleGraph (Fin 4)) := by
  refine ⟨k4Rotation, fun c _ => ?_⟩
  induction c using ConnectedComponent.ind with
  | h v =>
  have hsupp : ((⊤ : SimpleGraph (Fin 4)).connectedComponentMk v).supp = Set.univ :=
    Set.eq_univ_of_forall fun z => (ConnectedComponent.mem_supp_iff _ z).mpr (k4_comp z v)
  have hedges : componentEdges ⊤ ((⊤ : SimpleGraph (Fin 4)).connectedComponentMk v) =
      (⊤ : SimpleGraph (Fin 4)).edgeSet := by
    ext e
    exact ⟨fun h => h.1, fun h => ⟨h, fun z _ => k4_comp z v⟩⟩
  have hfaces : k4Rotation.facesIn ((⊤ : SimpleGraph (Fin 4)).connectedComponentMk v) =
      Set.univ := Set.eq_univ_of_forall fun f => by
    induction f using Quotient.inductionOn with
    | h d => exact k4_comp d.fst v
  have hV : (Set.univ : Set (Fin 4)).ncard = 4 := by simp
  have hE : (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard = 6 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
    rfl
  have hF : (Set.univ : Set k4Rotation.Face).ncard = 4 := by
    rw [Set.ncard_univ, natCard_k4Face]
  rw [hsupp, hedges, hfaces, hV, hE, hF]

/-- **`K₄` attains the bound**: it has `6 = 3·4 − 6` edges. -/
theorem ncard_edgeSet_top_four : (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard = 3 * 4 - 6 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin]
  rfl

/-! ## `K₅` and `K₃,₃` -/

/-- **`K₅` is not planar**: it has `10 > 3·5 − 6` edges. -/
theorem not_isPlanar_top_five : ¬IsPlanar (⊤ : SimpleGraph (Fin 5)) := fun h => by
  have := h.ncard_edgeSet_le (by simp)
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin] at this
  exact absurd this (by decide)

/-- `K₃,₃` has nine edges. -/
theorem ncard_edgeSet_completeBipartite_three_three :
    (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet.ncard = 9 := by
  rw [Set.ncard_def, encard_edgeSet_completeBipartiteGraph]
  simp

/-- **`K₃,₃` is not planar**: it is two-colourable with `9 > 2·6 − 4` edges, although
`9 ≤ 3·6 − 6`. -/
theorem not_isPlanar_completeBipartite_three_three :
    ¬IsPlanar (completeBipartiteGraph (Fin 3) (Fin 3)) := fun h => by
  have hcol : (completeBipartiteGraph (Fin 3) (Fin 3)).Colorable 2 := by
    simpa using (CompleteBipartiteGraph.bicoloring (Fin 3) (Fin 3)).colorable
  have := h.ncard_edgeSet_le_of_colorable hcol (by simp)
  rw [ncard_edgeSet_completeBipartite_three_three, Fintype.card_sum, Fintype.card_fin] at this
  omega

end MonoidProduct.Graph
