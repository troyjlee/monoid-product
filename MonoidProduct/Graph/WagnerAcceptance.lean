import MonoidProduct.Graph.PlanarSubgraphAcceptance
import MonoidProduct.Graph.Wagner
set_option linter.style.header false

/-!
# Acceptance statements for Wagner's theorem

Wagner's theorem (`Graph/Wagner.lean`), restated with the definitions unfolded, and checked on
boundary cases of the pieces of its proof.  Lean checks every `example` here against the
library's statement.

* **Wagner's theorem** for an arbitrary finite vertex type, with planarity unfolded to a rotation
  system satisfying Euler's formula in every component with an edge, and with the excluded minors
  unfolded to branch sets.
* Graphs without edges: the empty graph, on an empty vertex type, and the edgeless graphs, every
  rotation system of which is spherical.
* Disjoint unions: neither excluded minor appears in a disjoint union of graphs without them; `K₄`
  next to two isolated vertices.
* Deleting a vertex: the triangle is `2`-connected but not `3`-connected, and the face through the
  neighbours of a deleted vertex has two darts, one edge in both directions; in `K₄`, which is
  `3`-connected, it is a cycle with three vertices.
* A leaf and then a chord, on `K₂`: the face after the leaf repeats a vertex, and the chord splits
  it into two triangles.
* A fan across the end of a face: on the face `[0, 1, 2]` of `K₄`, a new vertex joined to `1` and
  `2` keeps a face through the whole closed interval `[2, 0, 1]`, which runs across the end of the
  list and contains the unattached vertex `0`.
* Gluing: `K₄` glued at a vertex to an isolated vertex; two copies of `K₂` glued along their edge;
  the diamond, two triangles glued along an edge, whose marker edge is already present.
* `K₅` minus an edge: planar by the converse, since five disjoint branch sets would be its five
  vertices, joined by all ten edges, and six do not fit; it is `3`-connected and larger than
  `K₄`, so planar by the `3`-connected converse too.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-! ## Wagner's theorem, unfolded -/

/-- A minor model of `Kₙ`: `n` disjoint connected sets, with an edge between any two. -/
private theorem isMinor_top_iff {V : Type*} {G : SimpleGraph V} {n : ℕ} :
    IsMinor (⊤ : SimpleGraph (Fin n)) G ↔ ∃ B : Fin n → Set V, (∀ i, IsConnectedSet G (B i)) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ ∀ i j, i ≠ j → ∃ a ∈ B i, ∃ b ∈ B j, G.Adj a b :=
  ⟨fun ⟨m⟩ => ⟨m.branch, m.connected, m.disjoint, fun i j h => m.adj i j ((top_adj i j).mpr h)⟩,
    fun ⟨B, hc, hd, ha⟩ => ⟨⟨B, hc, hd, fun i j h => ha i j ((top_adj i j).mp h)⟩⟩⟩

/-- A minor model of `K₃,₃`: six disjoint connected sets in two triples, with an edge between each
set of the first triple and each set of the second. -/
private theorem isMinor_completeBipartite_iff {V : Type*} {G : SimpleGraph V} :
    IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G ↔
      ∃ L R : Fin 3 → Set V, (∀ i, IsConnectedSet G (L i) ∧ IsConnectedSet G (R i)) ∧
        (∀ i j, i ≠ j → Disjoint (L i) (L j) ∧ Disjoint (R i) (R j)) ∧
        (∀ i j, Disjoint (L i) (R j)) ∧ ∀ i j, ∃ a ∈ L i, ∃ b ∈ R j, G.Adj a b := by
  constructor
  · rintro ⟨m⟩
    exact ⟨fun i => m.branch (.inl i), fun j => m.branch (.inr j),
      fun i => ⟨m.connected _, m.connected _⟩,
      fun i j h => ⟨m.disjoint _ _ (Sum.inl_injective.ne h),
        m.disjoint _ _ (Sum.inr_injective.ne h)⟩,
      fun i j => m.disjoint _ _ Sum.inl_ne_inr, fun i j => m.adj _ _ (by simp)⟩
  · rintro ⟨L, R, hc, hd, hLR, ha⟩
    refine ⟨⟨Sum.elim L R, ?_, ?_, ?_⟩⟩
    · rintro (i | i)
      exacts [(hc i).1, (hc i).2]
    · rintro (i | i) (j | j) h
      · exact (hd i j fun e => h (congrArg Sum.inl e)).1
      · exact hLR i j
      · exact (hLR j i).symm
      · exact (hd i j fun e => h (congrArg Sum.inr e)).2
    · rintro (i | i) (j | j) h
      · simp at h
      · exact ha i j
      · obtain ⟨a, ha', b, hb, hab⟩ := ha j i
        exact ⟨b, hb, a, ha', hab.symm⟩
      · simp at h

section Statements

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- **Wagner's theorem, with planarity unfolded**: a graph on a finite vertex type has a rotation
system satisfying Euler's formula `V + F = E + 2` in every component with an edge exactly when it
has neither a `K₅` minor nor a `K₃,₃` minor. -/
example :
    (∃ ρ : RotationSystem G, ∀ c : G.ConnectedComponent, (componentEdges G c).Nonempty →
        c.supp.ncard + (ρ.facesIn c).ncard = (componentEdges G c).ncard + 2) ↔
      ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G ∧
        ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G :=
  wagner_iff

/-- **Wagner's theorem, with the minors unfolded**: a graph on a finite vertex type is planar
exactly when it has neither five disjoint connected sets of vertices with an edge between any two,
nor six disjoint connected sets in two triples with an edge between each set of the first triple
and each set of the second. -/
example : IsPlanar G ↔
    (¬ ∃ B : Fin 5 → Set V, (∀ i, IsConnectedSet G (B i)) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ ∀ i j, i ≠ j → ∃ a ∈ B i, ∃ b ∈ B j, G.Adj a b) ∧
      ¬ ∃ L R : Fin 3 → Set V, (∀ i, IsConnectedSet G (L i) ∧ IsConnectedSet G (R i)) ∧
        (∀ i j, i ≠ j → Disjoint (L i) (L j) ∧ Disjoint (R i) (R j)) ∧
        (∀ i j, Disjoint (L i) (R j)) ∧ ∀ i j, ∃ a ∈ L i, ∃ b ∈ R j, G.Adj a b := by
  rw [wagner_iff, isMinor_top_iff, isMinor_completeBipartite_iff]

end Statements

/-! ## Graphs without edges -/

/-- **The empty graph**: a graph on an empty vertex type has neither excluded minor, since branch
sets are nonempty, and it is planar by the converse. -/
example (G : SimpleGraph Empty) : NoKuratowskiMinor G ∧ IsPlanar G := by
  have h : NoKuratowskiMinor G := by
    refine ⟨fun ⟨m⟩ => ?_, fun ⟨m⟩ => ?_⟩
    · obtain ⟨v, -⟩ := (m.connected 0).1
      exact isEmptyElim v
    · obtain ⟨v, -⟩ := (m.connected (.inl 0)).1
      exact isEmptyElim v
  exact ⟨h, wagner_hard h.1 h.2⟩

/-- **Edgeless graphs**, on any finite vertex type: every rotation system is spherical, since
Euler's formula is asked only of components with an edge, and there is no excluded minor, since
`K₅` and `K₃,₃` have edges; so both sides of Wagner's theorem hold. -/
example {V : Type*} [Finite V] :
    (∀ ρ : RotationSystem (⊥ : SimpleGraph V), ρ.IsSpherical) ∧
      NoKuratowskiMinor (⊥ : SimpleGraph V) ∧ IsPlanar (⊥ : SimpleGraph V) := by
  have h : NoKuratowskiMinor (⊥ : SimpleGraph V) := by
    refine ⟨fun ⟨m⟩ => ?_, fun ⟨m⟩ => ?_⟩
    · obtain ⟨a, -, b, -, hab⟩ := m.adj 0 1 (by decide)
      exact hab
    · obtain ⟨a, -, b, -, hab⟩ := m.adj (.inl 0) (.inr 0) (by simp)
      exact hab
  refine ⟨fun ρ c ⟨e, he, _⟩ => ?_, h, wagner_hard h.1 h.2⟩
  rw [edgeSet_bot] at he
  exact he.elim

/-! ## Disjoint unions -/

/-- **Disjoint unions**: if neither of two graphs has a `K₅` or a `K₃,₃` minor, neither has their
disjoint union, since both are planar by Wagner's theorem, and so is their disjoint union. -/
example {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : NoKuratowskiMinor G) (hH : NoKuratowskiMinor H) : NoKuratowskiMinor (G ⊕g H) :=
  wagner_iff.mp ((wagner_hard hG.1 hG.2).sum (wagner_hard hH.1 hH.2))

/-- **`K₄` next to two isolated vertices**: the graph is not connected, so the `3`-connected
converse does not apply to it; it is planar as a disjoint union of planar graphs, and so has
neither excluded minor. -/
example : ¬ ((⊤ : SimpleGraph (Fin 4)) ⊕g (⊥ : SimpleGraph (Fin 2))).Connected ∧
    (∀ i, Sum.inr i ∈ isolatedVerts ((⊤ : SimpleGraph (Fin 4)) ⊕g (⊥ : SimpleGraph (Fin 2)))) ∧
    IsPlanar ((⊤ : SimpleGraph (Fin 4)) ⊕g (⊥ : SimpleGraph (Fin 2))) ∧
    NoKuratowskiMinor ((⊤ : SimpleGraph (Fin 4)) ⊕g (⊥ : SimpleGraph (Fin 2))) := by
  have hP := isPlanar_top_four.sum (isPlanar_bot (V := Fin 2))
  refine ⟨not_connected_sum, fun i => ?_, hP, wagner_iff.mp hP⟩
  rintro (w | w) h <;> simp at h

/-! ## Faces on two vertices -/

/-- On at most two vertices, the face of every dart is the dart and its reversal: a vertex has at
most one dart, so the rotation fixes every dart. -/
private theorem faceDarts_eq_pair_of_two {V : Type*} {G : SimpleGraph V} (ρ : RotationSystem G)
    (hV : ∀ x y z : V, x ≠ z → y ≠ z → x = y) (d : G.Dart) : ρ.faceDarts d = [d, d.symm] := by
  have hface : ∀ e : G.Dart, ρ.face e = e.symm := fun e =>
    Dart.ext _ _ (Prod.ext (ρ.fst_rot e.symm) (hV _ _ e.snd
      (fun h => (ρ.rot e.symm).adj.ne ((ρ.fst_rot e.symm).trans h.symm)) e.adj.ne))
  exact orbitList_eq_of_getElem (L := [d, d.symm]) (by simpa using d.symm_ne.symm) (by simp)
    fun i hi => by
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i <;> simp [hface]

/-! ## Deleting a vertex -/

/-- The triangle is `2`-connected. -/
private theorem isKConnected_top_three_two : IsKConnected (⊤ : SimpleGraph (Fin 3)) 2 :=
  ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩

/-- **Deleting a vertex of the triangle**: the triangle is `2`-connected but not `3`-connected.
Deleting `0` leaves a copy of `K₂`, with a spherical rotation system and a face through both
neighbours `1` and `2` of `0`.  That face has two darts, the edge `12` in both directions: a
closed walk through the neighbours, but not a cycle with three or more vertices. -/
example : IsKConnected (⊤ : SimpleGraph (Fin 3)) 2 ∧ ¬ IsKConnected (⊤ : SimpleGraph (Fin 3)) 3 ∧
    ∃ σ : RotationSystem ((⊤ : SimpleGraph (Fin 3)).induce {v | v ≠ 0}), σ.IsSpherical ∧
      ∃ d₀, σ.faceDarts d₀ = [d₀, d₀.symm] ∧
        (⟨1, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 3))) ∈ σ.faceWalk d₀ ∧
        (⟨2, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 3))) ∈ σ.faceWalk d₀ := by
  obtain ⟨ρ, hρ⟩ : IsPlanar (⊤ : SimpleGraph (Fin 3)) := isPlanar_of_natCard_le_four (by simp)
  obtain ⟨σ, hσ, d₀, h⟩ := exists_induce_ne_faceWalk hρ isKConnected_top_three_two 0
  refine ⟨isKConnected_top_three_two, fun h3 => ?_, σ, hσ, d₀,
    faceDarts_eq_pair_of_two σ (by decide) d₀, h 1 ((top_adj 0 1).mpr (by decide)),
    h 2 ((top_adj 0 2).mpr (by decide))⟩
  have := h3.1
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- **Deleting a vertex of `K₄`**, which is `3`-connected: the face through the neighbours `1`, `2`
and `3` of `0` is a cycle with three vertices. -/
example : ∃ σ : RotationSystem ((⊤ : SimpleGraph (Fin 4)).induce {v | v ≠ 0}), σ.IsSpherical ∧
    ∃ d₀, IsCycleList ((⊤ : SimpleGraph (Fin 4)).induce {v | v ≠ 0}) (σ.faceWalk d₀) ∧
      (σ.faceWalk d₀).length = 3 ∧
      (⟨1, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 4))) ∈ σ.faceWalk d₀ ∧
      (⟨2, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 4))) ∈ σ.faceWalk d₀ ∧
      (⟨3, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 4))) ∈ σ.faceWalk d₀ := by
  obtain ⟨ρ, hρ⟩ := isPlanar_top_four
  have h3 : IsKConnected (⊤ : SimpleGraph (Fin 4)) 3 :=
    ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩
  obtain ⟨σ, hσ, d₀, hC, h⟩ := exists_induce_ne_isCycleList_faceWalk hρ h3 0
  have h1 := h 1 ((top_adj 0 1).mpr (by decide))
  have h2 := h 2 ((top_adj 0 2).mpr (by decide))
  have h3' := h 3 ((top_adj 0 3).mpr (by decide))
  refine ⟨σ, hσ, d₀, hC, le_antisymm (hC.1.length_le_card.trans_eq (by decide)) ?_, h1, h2, h3'⟩
  have hsub : [(⟨1, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 4))), ⟨2, by decide⟩, ⟨3, by decide⟩] ⊆
      σ.faceWalk d₀ := by
    intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl
    exacts [h1, h2, h3']
  exact (List.subperm_of_subset (by decide) hsub).length_le

/-! ## A leaf and a chord -/

/-- The dart from `0` to `1` in `K₂`. -/
private abbrev k2d₀₁ : (⊤ : SimpleGraph (Fin 2)).Dart := ⟨(0, 1), (top_adj 0 1).mpr (by decide)⟩

/-- **A leaf, then a chord, on `K₂`**: joining a new vertex to `0` alone keeps a spherical rotation
system, with a face whose walk `0`, new vertex, `0`, `1` repeats the vertex `0`.  The chord from
the new vertex to `1` inside that face splits it into two faces, both triangles on the new vertex,
`0` and `1`. -/
example : ∃ τ : RotationSystem (attachVertex (⊤ : SimpleGraph (Fin 2)) {0}), τ.IsSpherical ∧
    ∃ d, τ.faceWalk d = [some 0, none, some 0, some 1] ∧ ¬ (τ.faceWalk d).Nodup ∧
    ∃ τ' : RotationSystem (attachVertex (⊤ : SimpleGraph (Fin 2)) {0} ⊔ edge none (some 1)),
      τ'.IsSpherical ∧ ∃ d₁ d₂, τ'.faceWalk d₁ = [some 1, none, some 0] ∧
        τ'.faceWalk d₂ = [none, some 1, some 0] := by
  obtain ⟨ρ, hρ⟩ : IsPlanar (⊤ : SimpleGraph (Fin 2)) := isPlanar_of_natCard_le_four (by simp)
  have hS : ∀ x, x ∈ ({0} : Set (Fin 2)) ↔ x = k2d₀₁.fst := fun _ => Set.mem_singleton_iff
  -- The face of the leaf dart, from the leaf dart and from its reversal.
  have hD : (ρ.insertLeaf hS).faceDarts (leafDart hS) =
      [leafDart hS, (leafDart hS).symm, attachDart {0} k2d₀₁, attachDart {0} k2d₀₁.symm] := by
    rw [RotationSystem.faceDarts_insertLeaf, faceDarts_eq_pair_of_two ρ (by decide) k2d₀₁]
    rfl
  have hW : (ρ.insertLeaf hS).faceWalk (leafDart hS) = [some 0, none, some 0, some 1] := by
    rw [RotationSystem.faceWalk, hD]
    rfl
  have hD' : (ρ.insertLeaf hS).faceDarts (leafDart hS).symm =
      (leafDart hS).symm :: [attachDart {0} k2d₀₁] ++
        attachDart {0} k2d₀₁.symm :: [leafDart hS] := by
    have h := (ρ.insertLeaf hS).faceDarts_face (leafDart hS)
    rw [RotationSystem.insertLeaf_face_leafDart, hD] at h
    exact h
  -- The chord from the new vertex to `1`.
  have hc := isAddEdge_sup_edge (G := attachVertex (⊤ : SimpleGraph (Fin 2)) {0})
    (u := none) (v := some 1) (by simp)
  have hn : ¬ (attachVertex (⊤ : SimpleGraph (Fin 2)) {0}).Adj none (some 1) := by
    rw [attachVertex_adj_none_some, Set.mem_singleton_iff]
    decide
  have hab : (ρ.insertLeaf hS).face.SameCycle (leafDart hS).symm (attachDart {0} k2d₀₁.symm) :=
    (ρ.insertLeaf hS).mem_faceDarts_iff.mp (by rw [hD']; simp)
  obtain ⟨h₁, h₂⟩ := (ρ.insertLeaf hS).faceWalk_insertChord (a := (leafDart hS).symm)
    (b := attachDart {0} k2d₀₁.symm) hc hn hD'
  exact ⟨ρ.insertLeaf hS, hρ.insertLeaf hS, leafDart hS, hW, by rw [hW]; decide,
    (ρ.insertLeaf hS).insertChord hc hn, (hρ.insertLeaf hS).insertChord hc hn hab, _, _, h₁, h₂⟩

/-! ## A fan across the end of a face -/

/-- The dart from `0` to `1` in `K₄`. -/
private abbrev k4d₀₁ : (⊤ : SimpleGraph (Fin 4)).Dart := ⟨(0, 1), by decide⟩

/-- The dart from `1` to `2` in `K₄`. -/
private abbrev k4d₁₂ : (⊤ : SimpleGraph (Fin 4)).Dart := ⟨(1, 2), by decide⟩

/-- The dart from `2` to `0` in `K₄`. -/
private abbrev k4d₂₀ : (⊤ : SimpleGraph (Fin 4)).Dart := ⟨(2, 0), by decide⟩

/-- The face of `K₄`'s spherical rotation system through the dart from `0` to `1` is the triangle
`[0, 1, 2]`. -/
private theorem faceWalk_k4Rotation_k4d₀₁ : k4Rotation.faceWalk k4d₀₁ = [0, 1, 2] := by
  have hD : k4Rotation.faceDarts k4d₀₁ = [k4d₀₁, k4d₁₂, k4d₂₀] :=
    orbitList_eq_of_getElem (L := [k4d₀₁, k4d₁₂, k4d₂₀]) (by decide) (by decide) fun i hi => by
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i <;> rfl
  simp [RotationSystem.faceWalk, hD]

/-- **A fan whose retained interval crosses the end of the face list**: on the face `[0, 1, 2]` of
`K₄`, the attachments `1` and `2` are consecutive from `2` to `1`, and the closed interval between
them is `[2, 0, 1]`, across the end of the list.  A new vertex joined to `1` and `2` keeps a
spherical rotation system with a face through itself and that whole interval, including the
unattached vertex `0`. -/
example : closedArc [0, 1, 2] (2 : Fin 4) 1 = [2, 0, 1] ∧
    ∃ τ : RotationSystem (attachVertex (⊤ : SimpleGraph (Fin 4)) ↑({1, 2} : Finset (Fin 4))),
      τ.IsSpherical ∧ ∃ d, τ.faceWalk d ~r [none, some 2, some 0, some 1] := by
  have harc : closedArc [0, 1, 2] (2 : Fin 4) 1 = [2, 0, 1] := by decide
  have hpq : IsConsecutive (k4Rotation.faceWalk k4d₀₁) {1, 2} 2 1 := by
    rw [faceWalk_k4Rotation_k4d₀₁]
    unfold IsConsecutive
    decide
  obtain ⟨τ, hτ, d, hd⟩ := exists_isSpherical_attachVertex_faceWalk isSpherical_k4Rotation
    (by rw [faceWalk_k4Rotation_k4d₀₁]; decide) (by rw [faceWalk_k4Rotation_k4d₀₁]; decide)
    (by decide) hpq
  rw [faceWalk_k4Rotation_k4d₀₁, harc] at hd
  exact ⟨harc, τ, hτ, d, by simpa using hd⟩

/-! ## Gluing -/

/-- **Gluing at an isolated vertex**: `K₄` glued at `0` to the edgeless graph on two vertices at
its vertex `0`, which is isolated, is planar; the other vertex of the edgeless graph stays
isolated. -/
example : IsPlanar (contractEdge ((⊤ : SimpleGraph (Fin 4)) ⊕g (⊥ : SimpleGraph (Fin 2)))
      (.inl 0) (.inr 0)) ∧
    (⟨.inr 1, by simp⟩ : {s : Fin 4 ⊕ Fin 2 // s ≠ .inr 0}) ∈
      isolatedVerts (contractEdge ((⊤ : SimpleGraph (Fin 4)) ⊕g (⊥ : SimpleGraph (Fin 2)))
        (.inl 0) (.inr 0)) := by
  refine ⟨isPlanar_top_four.glueVertex isPlanar_bot 0 0, ?_⟩
  rintro ⟨w | w, hw⟩ h <;> simp [contractEdge_adj] at h

/-- **Two copies of `K₂` glued along their edge**: the separation of `K₂` whose two sides are both
all of `K₂` meets in the ends of the edge `01`, and gluing the sides along it gives `K₂` back. -/
example : IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  refine isPlanar_of_induce_of_inter_eq_pair (A := Set.univ) (B := Set.univ) (x := 0) (y := 1)
    (Set.union_self _) (fun u w hu _ => absurd (Set.mem_univ u) hu.2)
    ((top_adj 0 1).mpr (by decide)) ?_ (isPlanar_of_natCard_le_four (by simp))
    (isPlanar_of_natCard_le_four (by simp))
  ext v
  simp only [Set.inter_self, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
  revert v
  decide

/-- The diamond: `K₄` without the edge `23`, that is, the triangles `0 1 2` and `0 1 3` sharing
the edge `01`. -/
private def diamond : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v => ¬ (u = 2 ∧ v = 3) ∧ ¬ (u = 3 ∧ v = 2)

/-- **The diamond, two triangles glued along an edge**: its sides `{0, 1, 2}` and `{0, 1, 3}` are
triangles meeting in the ends of the edge `01`, so the marker edge of this separation is already
present, and there is no edge between `2` and `3`. -/
example : ¬ diamond.Adj 2 3 ∧ IsPlanar diamond := by
  refine ⟨by rw [diamond, fromRel_adj]; decide, ?_⟩
  refine isPlanar_of_induce_of_inter_eq_pair (A := {0, 1, 2}) (B := {0, 1, 3}) (x := 0) (y := 1)
    ?_ ?_ (by rw [diamond, fromRel_adj]; decide) ?_
    (isPlanar_of_natCard_le_four ((Finite.card_subtype_le _).trans (by simp)))
    (isPlanar_of_natCard_le_four ((Finite.card_subtype_le _).trans (by simp)))
  · ext v
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    revert v
    decide
  · intro u w hu hw h
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
    rw [diamond, fromRel_adj] at h
    revert u w
    decide
  · ext v
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert v
    decide

/-! ## `K₅` minus an edge -/

/-- `K₅` without the edge `01`. -/
private def k5MinusEdge : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun u v => ¬ (u = 0 ∧ v = 1) ∧ ¬ (u = 1 ∧ v = 0)

/-- Adjacency in `K₅` minus an edge is decidable, so `decide` checks its connectivity. -/
private instance : DecidableRel k5MinusEdge.Adj := fun u v =>
  inferInstanceAs (Decidable ((SimpleGraph.fromRel fun u v : Fin 5 =>
    ¬ (u = 0 ∧ v = 1) ∧ ¬ (u = 1 ∧ v = 0)).Adj u v))

/-- `K₅` minus an edge has neither excluded minor.  A minor model of `K₃,₃` would need six
disjoint nonempty branch sets in five vertices.  A minor model of `K₅` has five, so they are the
single vertices, and all ten edges between them would be present. -/
private theorem noKuratowskiMinor_k5MinusEdge : NoKuratowskiMinor k5MinusEdge := by
  refine ⟨fun ⟨m⟩ => ?_, fun ⟨m⟩ => ?_⟩
  · choose f hf using fun w => (m.connected w).1
    have hinj : Function.Injective f := fun w w' hww => by
      by_contra hne
      exact Set.disjoint_left.mp (m.disjoint w w' hne) (hf w) (hww ▸ hf w')
    have hsurj := Finite.surjective_of_injective hinj
    -- Each branch set is a single vertex.
    have hmem : ∀ w v, v ∈ m.branch w → v = f w := fun w v hv => by
      obtain ⟨w', rfl⟩ := hsurj v
      by_cases hww : w = w'
      · rw [hww]
      · exact absurd (hf w') (Set.disjoint_left.mp (m.disjoint w w' hww) hv)
    obtain ⟨w₀, hw₀⟩ := hsurj 0
    obtain ⟨w₁, hw₁⟩ := hsurj 1
    have hne : w₀ ≠ w₁ := fun h => absurd (hw₀.symm.trans (h ▸ hw₁)) (by decide)
    obtain ⟨a, ha, b, hb, hab⟩ := m.adj w₀ w₁ ((top_adj w₀ w₁).mpr hne)
    rw [hmem _ _ ha, hmem _ _ hb, hw₀, hw₁] at hab
    exact absurd hab (by decide)
  · choose f hf using fun w => (m.connected w).1
    have hinj : Function.Injective f := fun w w' hww => by
      by_contra hne
      exact Set.disjoint_left.mp (m.disjoint w w' hne) (hf w) (hww ▸ hf w')
    have := Fintype.card_le_of_injective f hinj
    simp at this

/-- **`K₅` minus an edge is planar by the converse**, without an explicit rotation system: five
disjoint branch sets would be its five vertices, joined by all ten edges, and six do not fit. -/
example : NoKuratowskiMinor k5MinusEdge ∧ IsPlanar k5MinusEdge :=
  ⟨noKuratowskiMinor_k5MinusEdge,
    wagner_hard noKuratowskiMinor_k5MinusEdge.1 noKuratowskiMinor_k5MinusEdge.2⟩

/-- **`K₅` minus an edge is `3`-connected**: a `3`-connected graph larger than `K₄` with neither
excluded minor, so planar by the `3`-connected converse.  It has `9 = 3·5 − 6` edges, the most a
planar graph on five vertices can have, and the two ends of every edge have a common neighbour. -/
example : IsKConnected k5MinusEdge 3 ∧ k5MinusEdge.edgeSet.ncard = 3 * 5 - 6 ∧
    (∀ u w, k5MinusEdge.Adj u w → ∃ z, k5MinusEdge.Adj u z ∧ k5MinusEdge.Adj w z) ∧
    IsPlanar k5MinusEdge := by
  have h3 : IsKConnected k5MinusEdge 3 :=
    ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩
  exact ⟨h3, by rw [← coe_edgeFinset, Set.ncard_coe_finset]; decide, by decide,
    wagner_threeConnected h3 noKuratowskiMinor_k5MinusEdge⟩

end MonoidProduct.Graph
