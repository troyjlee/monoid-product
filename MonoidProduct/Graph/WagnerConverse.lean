import MonoidProduct.Graph.FaceWalk
import MonoidProduct.Graph.PlanarExamples
import MonoidProduct.Graph.PlanarMinor
import MonoidProduct.Graph.WagnerContractible
import MonoidProduct.Graph.WagnerObstructions
import MonoidProduct.Graph.RotationFaces
import MonoidProduct.Graph.RotationInsert
import MonoidProduct.Graph.PlanarGlue
set_option linter.style.header false

/-!
# The converse of Wagner's theorem

**A finite graph with neither a `K₅` minor nor a `K₃,₃` minor is planar** (`wagner_hard`).
Planarity is `IsPlanar` (`Graph/Planar.lean`: a rotation system satisfying Euler's formula in every
component with an edge), minors are minor models (`Graph/Minor.lean`), and the vertex type is only
assumed finite: the graph need not be connected, and nothing is assumed of its edges.  The proof
follows Doczkal's combinatorial proof (*A Variant of Wagner's Theorem Based on Combinatorial
Hypermaps*, ITP 2021), by two inductions on the number of vertices.

* `isPlanar_of_natCard_le_four`: **every graph on at most four vertices is planar**, as it embeds
  in `K₄`.
* `wagner_threeConnected`: **a `3`-connected graph with no Kuratowski minor is planar.**  Contract
  an edge `xy` keeping `3`-connectivity (`exists_contractEdge_isKConnected_three`), embed the
  contraction, which has fewer vertices, and delete its merged vertex.  This leaves a spherical
  rotation system of `G - {x, y}` with a face through all the neighbours of `x` and `y`; the face
  is a cycle, since `G - {x, y}` is `2`-connected.  By the interval lemma
  (`exists_isConsecutive_subset_closedArc`), the neighbours of `y` on it lie on the closed arc
  between two consecutive neighbours `p, q` of `x`.  Attach `x` to its neighbours, keeping a face
  through the vertex `x` and that closed arc, and attach `y` inside that face, to `x` and to its
  neighbours.  The result is `G` (`attachVertexAttachVertexIso`).
* `wagner_hard`: **the converse of Wagner's theorem.**  A graph on at least five vertices that is
  not `3`-connected has a minimum separator of at most two vertices (`exists_minimum_separator`).
  The two sides of a separation along it have fewer vertices, and are minors of `G` once the edge
  between two separator vertices is added (`isMinor_sup_edge_induce_left`); their embeddings glue
  to an embedding of `G`, or of `G` with that edge added.
* Positions, arcs and consecutive marks of a cyclic list are kept by injective maps
  (`arc_map_of_injective`, `closedArc_map_of_injective`, `isConsecutive_map_iff`), and so are
  cycles by injective homomorphisms (`IsCycleList.map_of_injective`).
-/

namespace MonoidProduct.Graph

open SimpleGraph Function

/-! ## Arcs along an injective map -/

section MapArcs

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- **Positions are kept by an injective map.** -/
theorem idxOf_map_of_injective {f : α → β} (hf : Injective f) (L : List α) (a : α) :
    (L.map f).idxOf (f a) = L.idxOf a := by
  induction L with
  | nil => rfl
  | cons b L ih => simp only [List.map_cons, List.idxOf_cons, ih, beq_iff_eq, hf.eq_iff]

/-- **Reading from a vertex commutes with an injective map.** -/
theorem startAt_map_of_injective {f : α → β} (hf : Injective f) (C : List α) (a : α) :
    startAt (C.map f) (f a) = (startAt C a).map f := by
  rw [startAt, startAt, idxOf_map_of_injective hf, List.map_rotate]

/-- **Distances are kept by an injective map.** -/
theorem cycDist_map_of_injective {f : α → β} (hf : Injective f) (C : List α) (a b : α) :
    cycDist (C.map f) (f a) (f b) = cycDist C a b := by
  rw [cycDist, cycDist, startAt_map_of_injective hf, idxOf_map_of_injective hf]

/-- **Arcs commute with an injective map.** -/
theorem arc_map_of_injective {f : α → β} (hf : Injective f) (C : List α) (a b : α) :
    arc (C.map f) (f a) (f b) = (arc C a b).map f := by
  rw [arc, arc, startAt_map_of_injective hf, cycDist_map_of_injective hf, List.map_take]

/-- **Closed arcs commute with an injective map.** -/
theorem closedArc_map_of_injective {f : α → β} (hf : Injective f) (C : List α) (a b : α) :
    closedArc (C.map f) (f a) (f b) = (closedArc C a b).map f := by
  rw [closedArc, closedArc, startAt_map_of_injective hf, cycDist_map_of_injective hf,
    List.map_take]

/-- **Consecutive marks correspond under an embedding.** -/
theorem isConsecutive_map_iff (f : α ↪ β) {C : List α} {X : Finset α} {p q : α} :
    IsConsecutive (C.map f) (X.map f) (f p) (f q) ↔ IsConsecutive C X p q := by
  simp only [IsConsecutive, Finset.mem_map' f, f.injective.ne_iff,
    arc_map_of_injective f.injective, Finset.forall_mem_map, List.mem_map_of_injective f.injective,
    f.injective.eq_iff]

end MapArcs

/-- **Cycles are kept by injective homomorphisms.** -/
theorem IsCycleList.map_of_injective {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}
    (f : G →g G') (hf : Injective f) {C : List α} (h : IsCycleList G C) :
    IsCycleList G' (C.map f) := by
  refine ⟨h.1.map hf, fun i hi => ?_⟩
  simp only [List.getElem_map, List.length_map]
  exact f.map_adj (h.2 i (by simpa using hi))

/-! ## Small graphs -/

/-- **Every graph on at most four vertices is planar**: it embeds in `K₄`. -/
theorem isPlanar_of_natCard_le_four {V : Type*} [Finite V] {G : SimpleGraph V}
    (hV : Nat.card V ≤ 4) : IsPlanar G := by
  have := Fintype.ofFinite V
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := V) (β := Fin 4)
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact hV)
  exact isPlanar_top_four.of_injective ⟨f, fun h => (top_adj _ _).mpr (f.injective.ne h.ne)⟩
    f.injective

/-! ## Putting back an edge -/

section Attach

variable {V : Type*} {G : SimpleGraph V} {x y : V}

open Classical in
/-- The vertices other than `x` and `y`, with `y` and `x` put back as `none` and `some none`. -/
private noncomputable def optionOptionEquiv (hxy : x ≠ y) :
    Option (Option ↥({v | v ≠ x ∧ v ≠ y} : Set V)) ≃ V where
  toFun
    | none => y
    | some none => x
    | some (some v) => v.1
  invFun w :=
    if hy : w = y then none else if hx : w = x then some none else some (some ⟨w, hx, hy⟩)
  left_inv := by
    rintro (_ | _ | ⟨v, hvx, hvy⟩)
    · simp
    · simp [hxy]
    · simp [hvx, hvy]
  right_inv w := by
    by_cases hy : w = y
    · simp [hy]
    · by_cases hx : w = x
      · simp [hx, hxy]
      · simp [hx, hy]

/-- **Putting back `x` and `y`**: attach to `G - {x, y}` a new vertex adjacent to the neighbours
`X` of `x`, then a new vertex adjacent to it and to the neighbours `Y` of `y`.  If `xy` is an
edge, the result is isomorphic to `G`, with the second new vertex `none` sent to `y`, the first
`some none` to `x`, and `some (some v)` to `v`. -/
noncomputable def attachVertexAttachVertexIso (hxy : G.Adj x y)
    {X Y : Finset ↥({v | v ≠ x ∧ v ≠ y} : Set V)} (hX : ∀ u, u ∈ X ↔ G.Adj x u.1)
    (hY : ∀ u, u ∈ Y ↔ G.Adj y u.1) :
    attachVertex (attachVertex (G.induce {v | v ≠ x ∧ v ≠ y}) ↑X) ↑(Finset.insertNone Y) ≃g
      G where
  toEquiv := optionOptionEquiv hxy.ne
  map_rel_iff' := by
    rintro (_ | _ | u) (_ | _ | w)
    all_goals simp only [optionOptionEquiv, Equiv.coe_fn_mk, ne_eq, Set.mem_ofPred_eq,
      SetLike.mem_coe, SimpleGraph.irrefl, G.adj_comm, hxy, attachVertex_adj_none_some,
      attachVertex_adj_some_none, attachVertex_adj_some_some, Finset.mem_insertNone, Option.mem_def,
      reduceCtorEq, Option.some.injEq, IsEmpty.forall_iff, implies_true, forall_eq', hX, hY,
      comap_adj, Embedding.subtype_apply]

end Attach

/-! ## The `3`-connected converse -/

section ThreeConnected

variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- **Two neighbours besides `y`**: in a `3`-connected graph, a set of vertices meeting every
neighbour of `x` other than `y` has at least two elements. -/
private theorem two_le_card_of_forall_adj [Finite V] (hG : IsKConnected G 3) {s : Set V}
    {X : Finset s} (hX : ∀ w, G.Adj x w → w ≠ y → ∃ u ∈ X, u.1 = w) : 2 ≤ X.card := by
  have hsub : G.neighborSet x ⊆ insert y (Subtype.val '' (X : Set s)) := by
    intro w hw
    by_cases hwy : w = y
    · exact Or.inl hwy
    · obtain ⟨u, hu, rfl⟩ := hX w hw hwy
      exact Or.inr ⟨u, hu, rfl⟩
  have h3 := hG.le_ncard_neighborSet x
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_insert_le y (Subtype.val '' (X : Set s))
  rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset] at h2
  omega

/-- **Deleting the merged vertex**: from a spherical rotation system of the `3`-connected
contraction of `xy`, a spherical rotation system of `G - {x, y}` with a face, without repeated
vertices, through every neighbour of `x` and of `y`. -/
private theorem exists_faceWalk_induce [Finite V] (hxy : G.Adj x y)
    (hK3 : IsKConnected (contractEdge G x y) 3) (hK : IsPlanar (contractEdge G x y)) :
    ∃ σ : RotationSystem (G.induce {v | v ≠ x ∧ v ≠ y}), σ.IsSpherical ∧ ∃ d,
      (σ.faceWalk d).Nodup ∧
      (∀ u : ↥({v | v ≠ x ∧ v ≠ y} : Set V), G.Adj x u.1 → u ∈ σ.faceWalk d) ∧
      ∀ u : ↥({v | v ≠ x ∧ v ≠ y} : Set V), G.Adj y u.1 → u ∈ σ.faceWalk d := by
  obtain ⟨ρ, hρ⟩ := hK
  obtain ⟨σ, hσ, d₀, hd₀⟩ := exists_induce_ne_faceWalk hρ (hK3.mono (by norm_num)) ⟨x, hxy.ne⟩
  have hnd := RotationSystem.nodup_faceWalk_of_isKConnected hσ (hK3.induce_ne _) d₀
  let e : (contractEdge G x y).induce {v | v ≠ ⟨x, hxy.ne⟩} ≃g G.induce {v | v ≠ x ∧ v ≠ y} :=
    contractEdgeInduceIso G (fun v => ⟨fun hv => ⟨hv.2, fun he => hv.1 (congrArg Subtype.val he)⟩,
      fun ⟨hvy, hv⟩ => ⟨fun he => hv (Subtype.ext he), hvy⟩⟩) fun h => h.1 rfl
  have hmem : ∀ u : ↥({v | v ≠ x ∧ v ≠ y} : Set V),
      (contractEdge G x y).Adj ⟨x, hxy.ne⟩ ⟨u.1, u.2.2⟩ →
        u ∈ (σ.mapIso e).faceWalk (dartEquivOfIso e d₀) := fun u hu => by
    rw [RotationSystem.faceWalk_mapIso]
    exact List.mem_map_of_mem (hd₀ _ hu)
  have hne : ∀ u : ↥({v | v ≠ x ∧ v ≠ y} : Set V),
      (⟨x, hxy.ne⟩ : {v // v ≠ y}) ≠ ⟨u.1, u.2.2⟩ := fun u he =>
    u.2.1 (congrArg Subtype.val he).symm
  refine ⟨σ.mapIso e, hσ.mapIso e, dartEquivOfIso e d₀, ?_, fun u hu => hmem u ?_,
    fun u hu => hmem u ?_⟩
  · rw [RotationSystem.faceWalk_mapIso]
    exact hnd.map e.injective
  · exact contractEdge_adj.mpr ⟨hne u, Or.inl (Or.inl hu)⟩
  · exact contractEdge_adj.mpr ⟨hne u, Or.inl (Or.inr ⟨rfl, hu⟩)⟩

/-- **The interval lemma on a face of `G - {x, y}`**: if `G` has no Kuratowski minor and the
neighbours `X` of `x` and `Y` of `y` on a cycle `C` of `G - {x, y}` each have at least two
elements, then `Y` lies on the closed arc between two consecutive vertices of `X`. -/
private theorem exists_isConsecutive_of_induce [DecidableEq V] (h : NoKuratowskiMinor G)
    (hxy : G.Adj x y) {C : List ↥({v | v ≠ x ∧ v ≠ y} : Set V)}
    (hC : IsCycleList (G.induce {v | v ≠ x ∧ v ≠ y}) C)
    {X Y : Finset ↥({v | v ≠ x ∧ v ≠ y} : Set V)}
    (hX : ∀ u, u ∈ X ↔ u ∈ C ∧ G.Adj x u.1) (hY : ∀ u, u ∈ Y ↔ u ∈ C ∧ G.Adj y u.1)
    (hX2 : 2 ≤ X.card) (hY2 : 2 ≤ Y.card) :
    ∃ p q, IsConsecutive C X p q ∧ ∀ v ∈ Y, v ∈ closedArc C p q := by
  set f : ↥({v | v ≠ x ∧ v ≠ y} : Set V) ↪ V := Function.Embedding.subtype _
  have hC' : IsCycleList G (C.map f) :=
    hC.map_of_injective (Embedding.induce _).toHom Subtype.val_injective
  have hxC : x ∉ C.map f := by
    simp only [List.mem_map, not_exists, not_and]
    exact fun u _ hu => u.2.1 hu
  have hyC : y ∉ C.map f := by
    simp only [List.mem_map, not_exists, not_and]
    exact fun u _ hu => u.2.2 hu
  have hmap : ∀ (Z : Finset ↥({v | v ≠ x ∧ v ≠ y} : Set V)) (z : V),
      (∀ u, u ∈ Z ↔ u ∈ C ∧ G.Adj z u.1) → ∀ v, v ∈ Z.map f ↔ v ∈ C.map f ∧ G.Adj z v := by
    intro Z z hZ v
    simp only [Finset.mem_map, List.mem_map, hZ]
    constructor
    · rintro ⟨u, ⟨hu, hzu⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, hzu⟩
    · rintro ⟨⟨u, hu, rfl⟩, hzu⟩
      exact ⟨u, ⟨hu, hzu⟩, rfl⟩
  obtain ⟨p, q, hpq, hYpq⟩ := exists_isConsecutive_subset_closedArc h hxy hC' hxC hyC
    (hmap X x hX) (hmap Y y hY) (by rwa [Finset.card_map]) (by rwa [Finset.card_map])
  obtain ⟨hp, hq, -⟩ := id hpq
  obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hq
  refine ⟨p, q, (isConsecutive_map_iff f).mp hpq, fun v hv => ?_⟩
  have := hYpq (f v) (Finset.mem_map_of_mem f hv)
  rwa [closedArc_map_of_injective f.injective, List.mem_map_of_injective f.injective] at this

/-- **Putting the edge back into a face**: if `G - {x, y}` has a spherical rotation system with a
face, without repeated vertices, through every neighbour of `x` and of `y`, and `G` is
`3`-connected without a Kuratowski minor, then `G` is planar.  The neighbours of `y` lie between
two consecutive neighbours `p, q` of `x`; attach `x` to its neighbours keeping a face through the
closed arc from `p` to `q`, then attach `y` inside that face. -/
private theorem isPlanar_of_faceWalk_induce [Finite V] (hG : IsKConnected G 3)
    (h : NoKuratowskiMinor G) (hxy : G.Adj x y)
    {σ : RotationSystem (G.induce {v | v ≠ x ∧ v ≠ y})} (hσ : σ.IsSpherical)
    {d : (G.induce {v | v ≠ x ∧ v ≠ y}).Dart} (hnd : (σ.faceWalk d).Nodup)
    (hx : ∀ u : ↥({v | v ≠ x ∧ v ≠ y} : Set V), G.Adj x u.1 → u ∈ σ.faceWalk d)
    (hy : ∀ u : ↥({v | v ≠ x ∧ v ≠ y} : Set V), G.Adj y u.1 → u ∈ σ.faceWalk d) :
    IsPlanar G := by
  classical
  -- The neighbours of `x` and of `y`, all on the face.
  set X := (σ.faceWalk d).toFinset.filter fun u => G.Adj x u.1 with hXdef
  set Y := (σ.faceWalk d).toFinset.filter fun u => G.Adj y u.1 with hYdef
  have hXC : ∀ u, u ∈ X ↔ u ∈ σ.faceWalk d ∧ G.Adj x u.1 := fun u => by
    rw [hXdef, Finset.mem_filter, List.mem_toFinset]
  have hYC : ∀ u, u ∈ Y ↔ u ∈ σ.faceWalk d ∧ G.Adj y u.1 := fun u => by
    rw [hYdef, Finset.mem_filter, List.mem_toFinset]
  have hXm : ∀ u, u ∈ X ↔ G.Adj x u.1 := fun u => by
    rw [hXC]
    exact ⟨And.right, fun h => ⟨hx u h, h⟩⟩
  have hYm : ∀ u, u ∈ Y ↔ G.Adj y u.1 := fun u => by
    rw [hYC]
    exact ⟨And.right, fun h => ⟨hy u h, h⟩⟩
  -- Each has at least two vertices.
  have hX2 : 2 ≤ X.card := two_le_card_of_forall_adj (y := y) hG fun w hw hwy =>
    ⟨⟨w, hw.ne', hwy⟩, (hXm _).mpr hw, rfl⟩
  have hY2 : 2 ≤ Y.card := two_le_card_of_forall_adj (y := x) hG fun w hw hwx =>
    ⟨⟨w, hwx, hw.ne'⟩, (hYm _).mpr hw, rfl⟩
  -- The neighbours of `y` lie between consecutive neighbours `p, q` of `x`.
  obtain ⟨p, q, hpq, hYpq⟩ := exists_isConsecutive_of_induce h hxy (σ.isCycleList_faceWalk hnd)
    hXC hYC hX2 hY2
  -- Attach `x`, keeping a face through the closed arc from `p` to `q`.
  obtain ⟨τ, hτ, d', hd'⟩ := exists_isSpherical_attachVertex_faceWalk hσ hnd
    (fun a ha => hx a ((hXm a).mp ha)) hX2 hpq
  have hnd' : (τ.faceWalk d').Nodup := hd'.nodup_iff.mpr (List.nodup_cons.mpr
    ⟨by simp, (nodup_closedArc hnd).map (Option.some_injective _)⟩)
  -- Attach `y` inside that face, to `x` and to its own neighbours.
  have hA : ∀ a ∈ Finset.insertNone Y, a ∈ τ.faceWalk d' := fun a ha => by
    refine hd'.mem_iff.mpr ?_
    cases a with
    | none => exact List.mem_cons_self
    | some v => exact List.mem_cons_of_mem _ (List.mem_map_of_mem
        (hYpq v (Finset.some_mem_insertNone.mp ha)))
  have hP := isPlanar_attachVertex_of_subset_faceWalk hτ hnd' hA
    (by rw [Finset.card_insertNone]; omega)
  exact hP.of_iso (attachVertexAttachVertexIso hxy hXm hYm)

/-- **The converse of Wagner's theorem for `3`-connected graphs**: a `3`-connected finite graph
with neither a `K₅` minor nor a `K₃,₃` minor is planar.  By induction on the number of vertices:
contract an edge `xy` keeping `3`-connectivity, embed the contraction, delete the merged vertex,
and put `x` and `y` back into the face left behind. -/
theorem wagner_threeConnected {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : IsKConnected G 3) (h : NoKuratowskiMinor G) : IsPlanar G := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card V = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  by_cases h4 : Nat.card V ≤ 4
  · exact isPlanar_of_natCard_le_four h4
  obtain ⟨x, y, hxy, hK3⟩ := exists_contractEdge_isKConnected_three hG (by omega)
  have hK := ih _ (by have := natCard_subtype_ne_add_one y; omega) hK3
    (h.of_isMinor (isMinor_contractEdge hxy)) rfl
  obtain ⟨σ, hσ, d, hnd, hx, hy⟩ := exists_faceWalk_induce hxy hK3 hK
  exact isPlanar_of_faceWalk_induce hG h hxy hσ hnd hx hy

end ThreeConnected

/-! ## The general converse -/

/-- **The converse of Wagner's theorem**: a finite graph with neither a `K₅` minor nor a `K₃,₃`
minor is planar.  By induction on the number of vertices: a graph on at most four vertices is
planar, and a `3`-connected one by `wagner_threeConnected`.  Otherwise a minimum separator has at
most two vertices; the two sides of the separation it gives have fewer vertices and are minors of
`G`, after adding the edge between the two separator vertices if there are two, and their
embeddings glue to one of `G`, or of `G` with that edge added. -/
theorem wagner_hard {V : Type*} [Finite V] {G : SimpleGraph V}
    (h5 : ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G)
    (h33 : ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G) : IsPlanar G := by
  classical
  have h : NoKuratowskiMinor G := ⟨h5, h33⟩
  clear h5 h33
  obtain ⟨n, hn⟩ : ∃ n, Nat.card V = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  by_cases h4 : Nat.card V ≤ 4
  · exact isPlanar_of_natCard_le_four h4
  by_cases h3 : IsKConnected G 3
  · exact wagner_threeConnected h3 h
  -- A minimum separator, with at most two vertices, and its separation.
  obtain ⟨S, hS3, hSc, hmin⟩ := exists_minimum_separator (by omega : 3 < Nat.card V) h3
  obtain ⟨u, hu⟩ : ∃ u, u ∉ S := by
    have := Fintype.ofFinite V
    obtain ⟨u, -, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := Finset.univ)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨u, hu⟩
  obtain ⟨A, B, hAB, hS⟩ := exists_isProperSeparation S hSc hu
  -- Both sides, and their minors, have fewer vertices.
  have hA : ∀ {H : SimpleGraph V}, IsMinor (H.induce A) G → IsPlanar (H.induce A) := fun hm =>
    ih _ (hn ▸ hAB.natCard_lt_left) (h.of_isMinor hm) rfl
  have hB : ∀ {H : SimpleGraph V}, IsMinor (H.induce B) G → IsPlanar (H.induce B) := fun hm =>
    ih _ (hn ▸ hAB.natCard_lt_right) (h.of_isMinor hm) rfl
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2) with hc | hc | hc
  · -- No separator vertex.
    rw [Finset.card_eq_zero] at hc
    subst hc
    exact isPlanar_of_induce_of_inter_eq_empty hAB.union_eq hAB.not_adj
      (by rw [hS, Finset.coe_empty]) (hA (isMinor_induce G A)) (hB (isMinor_induce G B))
  · -- One separator vertex.
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc
    exact isPlanar_of_induce_of_inter_eq_singleton hAB.union_eq hAB.not_adj
      (by rw [hS, Finset.coe_singleton]) (hA (isMinor_induce G A)) (hB (isMinor_induce G B))
  · -- Two separator vertices `x, y`: add the edge `xy` on both sides.
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
    have h2 : IsKConnected G 2 := hc ▸ hmin
    have hS' : A ∩ B = {x, y} := by rw [hS, Finset.coe_pair]
    have hxB : x ∈ B := (show x ∈ A ∩ B by rw [hS']; exact Set.mem_insert x {y}).2
    have hyB : y ∈ B := (show y ∈ A ∩ B by rw [hS']; exact Set.mem_insert_of_mem x rfl).2
    have hplus : IsPlanar (G ⊔ edge x y) := by
      refine isPlanar_of_induce_of_inter_eq_pair hAB.union_eq (fun a b ha hb hab => ?_) ?_ hS'
        (hA (isMinor_sup_edge_induce_left h2 hAB hxy hS'))
        (hB (isMinor_sup_edge_induce_right h2 hAB hxy hS'))
      · rw [sup_adj, edge_adj] at hab
        rcases hab with hab | ⟨⟨rfl, -⟩ | ⟨rfl, -⟩, -⟩
        · exact hAB.not_adj ha hb hab
        · exact ha.2 hxB
        · exact ha.2 hyB
      · rw [sup_adj, edge_adj]
        exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
    exact hplus.mono le_sup_left

end MonoidProduct.Graph
