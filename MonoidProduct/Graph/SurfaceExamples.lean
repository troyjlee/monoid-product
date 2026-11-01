import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.OrderOfElement
import MonoidProduct.Graph.Surface
set_option linter.style.header false

/-!
# `K₇` on the torus

Checks the normalization of `GenusLE` and `EulerGenusLE` (`Graph/Surface.lean`) at a positive
genus.  `K₇` embeds in the torus: rotating the neighbours of `u` in the order
`u + 1, u + 3, u + 2, u + 6, u + 4, u + 5` modulo `7` gives `14` triangular faces, so
`7 − 21 + 14 = 0`, an orientable embedding of genus `1` (`k7Rotation`, `natCard_k7Face`).

* `genusLE_one_top_seven`: `K₇` has orientable genus at most `1`, hence Euler genus at most `2`.
* `not_eulerGenusLE_one_top_seven`: `K₇` does not have Euler genus at most `1`, since
  `21 > 3·7 − 6 + 3`; it does not embed in the projective plane.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-- **The rotation of `K₇` on the torus**: row `u` lists the neighbour after `w` around `u`, for
`w = 0, …, 6`, in the cyclic order `u + 1, u + 3, u + 2, u + 6, u + 4, u + 5`; the diagonal is
unused. -/
def k7Next : Fin 7 → Fin 7 → Fin 7 :=
  ![![0, 3, 6, 2, 5, 1, 4], ![5, 1, 4, 0, 3, 6, 2], ![3, 6, 2, 5, 1, 4, 0],
    ![1, 4, 0, 3, 6, 2, 5], ![6, 2, 5, 1, 4, 0, 3], ![4, 0, 3, 6, 2, 5, 1],
    ![2, 5, 1, 4, 0, 3, 6]]

/-- The inverse rotation of `K₇`. -/
def k7Prev : Fin 7 → Fin 7 → Fin 7 :=
  ![![0, 5, 3, 1, 6, 4, 2], ![3, 1, 6, 4, 2, 0, 5], ![6, 4, 2, 0, 5, 3, 1],
    ![2, 0, 5, 3, 1, 6, 4], ![5, 3, 1, 6, 4, 2, 0], ![1, 6, 4, 2, 0, 5, 3],
    ![4, 2, 0, 5, 3, 1, 6]]

private theorem k7Next_ne : ∀ u w : Fin 7, u ≠ w → u ≠ k7Next u w := by decide
private theorem k7Prev_ne : ∀ u w : Fin 7, u ≠ w → u ≠ k7Prev u w := by decide
private theorem k7Prev_next : ∀ u w : Fin 7, u ≠ w → k7Prev u (k7Next u w) = w := by decide
private theorem k7Next_prev : ∀ u w : Fin 7, u ≠ w → k7Next u (k7Prev u w) = w := by decide

/-- The rotation at each vertex is one cycle through its six neighbours. -/
private theorem k7_cycle : ∀ u w w' : Fin 7, u ≠ w → u ≠ w' →
    w' = w ∨ w' = k7Next u w ∨ w' = k7Next u (k7Next u w) ∨
      w' = k7Next u (k7Next u (k7Next u w)) ∨
      w' = k7Next u (k7Next u (k7Next u (k7Next u w))) ∨
      w' = k7Next u (k7Next u (k7Next u (k7Next u (k7Next u w)))) := by decide

/-- The rotation of `K₇`, as a permutation of its darts. -/
def k7Rot : Equiv.Perm (⊤ : SimpleGraph (Fin 7)).Dart where
  toFun d := ⟨(d.fst, k7Next d.fst d.snd), k7Next_ne _ _ d.adj⟩
  invFun d := ⟨(d.fst, k7Prev d.fst d.snd), k7Prev_ne _ _ d.adj⟩
  left_inv d := Dart.ext _ _ (Prod.ext rfl (k7Prev_next _ _ d.adj))
  right_inv d := Dart.ext _ _ (Prod.ext rfl (k7Next_prev _ _ d.adj))

/-- **The rotation system of `K₇` on the torus.** -/
def k7Rotation : RotationSystem (⊤ : SimpleGraph (Fin 7)) where
  rot := k7Rot
  fst_rot _ := rfl
  sameCycle_rot d d' h := by
    have hd' : d.fst ≠ d'.snd := by
      rw [h]
      exact d'.adj
    rcases k7_cycle d.fst d.snd d'.snd d.adj hd' with h' | h' | h' | h' | h' | h'
    · have he : d' = d := Dart.ext _ _ (Prod.ext h.symm h')
      subst he
      exact .rfl
    · have he : d' = k7Rot d := Dart.ext _ _ (Prod.ext h.symm h')
      subst he
      exact Equiv.Perm.sameCycle_apply_right.mpr .rfl
    · have he : d' = k7Rot (k7Rot d) := Dart.ext _ _ (Prod.ext h.symm h')
      subst he
      exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.sameCycle_apply_right.mpr .rfl)
    · have he : d' = k7Rot (k7Rot (k7Rot d)) := Dart.ext _ _ (Prod.ext h.symm h')
      subst he
      repeat apply Equiv.Perm.sameCycle_apply_right.mpr
      exact .rfl
    · have he : d' = k7Rot (k7Rot (k7Rot (k7Rot d))) := Dart.ext _ _ (Prod.ext h.symm h')
      subst he
      repeat apply Equiv.Perm.sameCycle_apply_right.mpr
      exact .rfl
    · have he : d' = k7Rot (k7Rot (k7Rot (k7Rot (k7Rot d)))) :=
        Dart.ext _ _ (Prod.ext h.symm h')
      subst he
      repeat apply Equiv.Perm.sameCycle_apply_right.mpr
      exact .rfl

/-- Two steps of a face change the tail. -/
private theorem k7_face_two : ∀ u w : Fin 7, u ≠ w → k7Next w u ≠ u := by decide

/-- Every face returns after three steps. -/
private theorem k7_face_three : ∀ u w : Fin 7, u ≠ w →
    k7Next (k7Next w u) w = u ∧ k7Next (k7Next (k7Next w u) w) (k7Next w u) = w := by decide

/-- **Every face of `K₇` on the torus is a triangle.** -/
theorem k7_face_face_face (d : (⊤ : SimpleGraph (Fin 7)).Dart) :
    k7Rotation.face (k7Rotation.face (k7Rotation.face d)) = d := by
  obtain ⟨h1, h2⟩ := k7_face_three d.fst d.snd d.adj
  exact Dart.ext _ _ (Prod.ext h1 h2)

/-- The face of a dart: the dart and its next two. -/
theorem k7_sameCycle_iff (d d' : (⊤ : SimpleGraph (Fin 7)).Dart) :
    k7Rotation.face.SameCycle d d' ↔
      d' = d ∨ d' = k7Rotation.face d ∨ d' = k7Rotation.face (k7Rotation.face d) := by
  constructor
  · intro h
    have h3 : k7Rotation.face ^ 3 = 1 := Equiv.ext fun x => by
      simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact k7_face_face_face x
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

/-- **`K₇` on the torus has `14` faces.** -/
theorem natCard_k7Face : Nat.card k7Rotation.Face = 14 := by
  classical
  have : Fintype k7Rotation.Face := Fintype.ofFinite _
  have hfib : ∀ q : k7Rotation.Face,
      (Finset.univ.filter fun d : (⊤ : SimpleGraph (Fin 7)).Dart =>
        (⟦d⟧ : k7Rotation.Face) = q).card = 3 := by
    intro q
    induction q using Quotient.inductionOn with
    | h d₀ =>
    have hne1 := k7Rotation.face_ne d₀
    have hne2 := k7Rotation.face_ne (k7Rotation.face d₀)
    have hne3 : k7Rotation.face (k7Rotation.face d₀) ≠ d₀ := fun h =>
      k7_face_two d₀.fst d₀.snd d₀.adj
        (congrArg (fun d : (⊤ : SimpleGraph (Fin 7)).Dart => d.fst) h)
    have hset : (Finset.univ.filter fun d : (⊤ : SimpleGraph (Fin 7)).Dart =>
        (⟦d⟧ : k7Rotation.Face) = ⟦d₀⟧) =
        {d₀, k7Rotation.face d₀, k7Rotation.face (k7Rotation.face d₀)} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [Quotient.eq]
      exact Equiv.Perm.sameCycle_comm.trans (k7_sameCycle_iff d₀ d)
    rw [hset, Finset.card_insert_of_notMem (by simp [Ne.symm hne1, Ne.symm hne3]),
      Finset.card_pair (Ne.symm hne2)]
  have hdarts : Fintype.card (⊤ : SimpleGraph (Fin 7)).Dart = 42 := by
    rw [dart_card_eq_twice_card_edges, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    rfl
  rw [Nat.card_eq_fintype_card]
  have := Finset.card_eq_sum_card_fiberwise (f := fun d : (⊤ : SimpleGraph (Fin 7)).Dart =>
    (⟦d⟧ : k7Rotation.Face)) (s := Finset.univ) (t := Finset.univ)
    fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  rw [Finset.card_univ, hdarts, Finset.sum_congr rfl fun q _ => hfib q, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at this
  omega

/-- In `K₇` all vertices lie in one component. -/
private theorem k7_comp (u w : Fin 7) :
    (⊤ : SimpleGraph (Fin 7)).connectedComponentMk u =
      (⊤ : SimpleGraph (Fin 7)).connectedComponentMk w := by
  by_cases h : u = w
  · rw [h]
  · exact ConnectedComponent.eq.mpr ((top_adj u w).mpr h).reachable

/-- **The embedding of `K₇` has Euler genus `2`**, twice its genus `1`: `7 − 21 + 14 = 0`. -/
theorem twiceEulerGenus_k7 (c : (⊤ : SimpleGraph (Fin 7)).ConnectedComponent) :
    k7Rotation.toScheme.twiceEulerGenus c = 4 := by
  induction c using ConnectedComponent.ind with
  | h v =>
  have hsupp : ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v).supp = Set.univ :=
    Set.eq_univ_of_forall fun z => (ConnectedComponent.mem_supp_iff _ z).mpr (k7_comp z v)
  have hedges : componentEdges ⊤ ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v) =
      (⊤ : SimpleGraph (Fin 7)).edgeSet := by
    ext e
    exact ⟨fun h => h.1, fun h => ⟨h, fun z _ => k7_comp z v⟩⟩
  have hfaces : k7Rotation.facesIn ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v) =
      Set.univ := Set.eq_univ_of_forall fun f => by
    induction f using Quotient.inductionOn with
    | h d => exact k7_comp d.fst v
  have hV : ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v).supp.ncard = 7 := by
    rw [hsupp]
    simp
  have hE : (componentEdges ⊤ ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v)).ncard =
      21 := by
    rw [hedges, ← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
    rfl
  have hF : (k7Rotation.facesIn ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v)).ncard =
      14 := by
    rw [hfaces, Set.ncard_univ, natCard_k7Face]
  -- Twice the Euler genus is at least `4` (the edge bound) and at most `4` (the faces).
  have hlow := k7Rotation.toScheme.edges_le (by rw [hV]; decide)
  have horbits := k7Rotation.two_mul_ncard_facesIn_le
    ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v)
  rw [hE, hV] at hlow
  rw [hF] at horbits
  have hne : (componentEdges ⊤ ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v)).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by rw [hE]; decide)
  have hformula :
      k7Rotation.toScheme.twiceEulerGenus ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v) =
        46 - (14 + (k7Rotation.toScheme.orbitsIn
          ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk v)).ncard) := by
    unfold EmbeddingScheme.twiceEulerGenus
    rw [ite_eq_left hne, hE, hV]
  omega

/-- **`K₇` has orientable genus at most `1`**: it embeds in the torus. -/
theorem genusLE_one_top_seven : GenusLE (⊤ : SimpleGraph (Fin 7)) 1 := by
  classical
  have : Fintype (⊤ : SimpleGraph (Fin 7)).ConnectedComponent := Fintype.ofFinite _
  refine ⟨k7Rotation.toScheme, fun _ => rfl, ?_⟩
  have hall : ∀ c : (⊤ : SimpleGraph (Fin 7)).ConnectedComponent,
      c = (⊤ : SimpleGraph (Fin 7)).connectedComponentMk 0 := by
    intro c
    induction c using ConnectedComponent.ind with
    | h v => exact k7_comp v 0
  rw [finsum_eq_sum_of_fintype, Fintype.sum_eq_single
    ((⊤ : SimpleGraph (Fin 7)).connectedComponentMk 0) (fun c hc => absurd (hall c) hc),
    twiceEulerGenus_k7]

/-- **`K₇` does not have Euler genus at most `1`**: it has `21 > 3·7 − 6 + 3` edges, so it does not
embed in the projective plane. -/
theorem not_eulerGenusLE_one_top_seven : ¬EulerGenusLE (⊤ : SimpleGraph (Fin 7)) 1 := fun h => by
  have := h.ncard_edgeSet_le (by simp)
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin] at this
  exact absurd this (by decide)

end MonoidProduct.Graph
