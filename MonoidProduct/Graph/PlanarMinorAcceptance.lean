import MonoidProduct.Graph.Wagner
import MonoidProduct.Graph.PlanarSubgraphAcceptance
set_option linter.style.header false

/-!
# Acceptance statements for contraction, minors and the easy direction of Wagner's theorem

The statements of `Graph/MinorContraction.lean`, `Graph/PlanarContraction.lean`,
`Graph/PlanarMinor.lean` and `Graph/Wagner.lean`, restated with the definitions unfolded where that
makes their meaning visible, followed by sanity checks.  Lean checks every `example` here against
the library's statement.

* The vertex map of a contraction; contracting an edge without common neighbours: the darts, the
  spliced rotation, the faces, and the unchanged components, completed faces and Euler defect;
  thinning away common neighbours.
* Minor models pushed through a contraction inside a branch set.
* Closure under contraction, injective homomorphisms and minors, and the easy direction of
  Wagner's theorem, with only `[Finite V]` and planarity as hypotheses: no connectedness and no
  bipartiteness is assumed.  Planarity is a proper minor-closed class.

The sanity checks cover:
* contractions of explicit spherical rotation systems: `K₂` (its face disappears and the contracted
  vertex is isolated), a leaf edge of a star, an edge of a `4`-cycle, and an edge of `K₄`, whose
  ends have two common neighbours that must be thinned away first;
* deletions: an edge whose deletion leaves two components that both keep an edge, a leaf edge, and
  the edge of a `K₂` component; an induced subgraph with isolated vertices;
* a minor model of `K₂` in `K₄` with a branch set of two vertices, an unused vertex and unused
  edges, pushed through the contraction of its internal edge;
* the Petersen graph, which has `15 ≤ 3·10 − 6` edges but a `K₅` minor, so is not planar.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm RotationSystem

/-! ## Statements -/

section Statements

variable {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}

/-- **The vertex map of contracting `xy`**: `y` goes to `x`; two vertices are identified exactly
when they are equal or both ends of the edge. -/
example {x y : V} (hxy : x ≠ y) (u w : V) :
    (contractVertex hxy u : V) = (if u = y then x else u) ∧
      (contractVertex hxy u = contractVertex hxy w ↔
        u = w ∨ ((u = x ∨ u = y) ∧ (w = x ∨ w = y))) :=
  ⟨val_contractVertex hxy u, contractVertex_eq_iff hxy⟩

/-- **Edges after contracting**: every edge other than `xy` survives; reachability and the number
of components do not change. -/
example {x y : V} (hxy : G.Adj x y) :
    (∀ {u w : V}, G.Adj u w → s(u, w) ≠ s(x, y) →
      (contractEdge G x y).Adj (contractVertex hxy.ne u) (contractVertex hxy.ne w)) ∧
    (∀ {u w : V}, G.Reachable u w →
      (contractEdge G x y).Reachable (contractVertex hxy.ne u) (contractVertex hxy.ne w)) ∧
    Nat.card (contractEdge G x y).ConnectedComponent = Nat.card G.ConnectedComponent :=
  ⟨fun h he => contractEdge_adj_contractVertex hxy h he, fun h => reachable_contractVertex hxy h,
    natCard_connectedComponent_contractEdge hxy⟩

variable (ρ : RotationSystem G) (a : G.Dart)
  (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd))

/-- **Contracting the edge of `a`, without common neighbours**: a surviving dart goes to the dart
between the images of its ends; the rotation splices the cycles around the two ends by the
transposition of `a` and `a.symm` and erases both; the faces are those of `ρ` with `a` and
`a.symm` erased. -/
example :
    (∀ d, ((contractDartEquiv a hdisj d).fst, (contractDartEquiv a hdisj d).snd) =
      (contractVertex a.adj.ne d.1.fst, contractVertex a.adj.ne d.1.snd)) ∧
    (ρ.contract a hdisj).rot =
      (contractDartEquiv a hdisj).permCongr (eraseTwo (ρ.rot * swap a a.symm) a a.symm) ∧
    (ρ.contract a hdisj).face = (contractDartEquiv a hdisj).permCongr (eraseTwo ρ.face a a.symm) :=
  ⟨fun _ => rfl, rfl, ρ.contract_face a hdisj⟩

/-- **The counts after contracting**: one vertex and one edge fewer, the same components and
completed faces, hence the same Euler defect; a face is lost exactly when the edge is a whole
component, and then the contracted vertex is isolated. -/
example :
    Nat.card {v // v ≠ a.snd} + 1 = Nat.card V ∧
    (contractEdge G a.fst a.snd).edgeSet.ncard + 1 = G.edgeSet.ncard ∧
    Nat.card (ρ.contract a hdisj).Face +
      (if ρ.rot a = a ∧ ρ.rot a.symm = a.symm then 1 else 0) = Nat.card ρ.Face ∧
    (isolatedVerts (contractEdge G a.fst a.snd)).ncard = (isolatedVerts G).ncard +
      (if ρ.rot a = a ∧ ρ.rot a.symm = a.symm then 1 else 0) ∧
    (ρ.contract a hdisj).completedFaceCount = ρ.completedFaceCount ∧
    (ρ.contract a hdisj).eulerDefect = ρ.eulerDefect :=
  ⟨natCard_subtype_ne_add_one a.snd, ncard_edgeSet_contractEdge_add_one a hdisj,
    ρ.natCard_face_contract_add a hdisj, ρ.ncard_isolatedVerts_contractEdge a,
    ρ.completedFaceCount_contract a hdisj, ρ.eulerDefect_contract a hdisj⟩

/-- **Thinning away common neighbours**: delete the edges from `y` to the common neighbours of `x`
and `y`; the edge `xy` stays, no common neighbour is left, and the contraction is the same. -/
example {x y : V} (hxy : G.Adj x y) :
    thinEdges G x y = {e | ∃ z, G.Adj x z ∧ G.Adj y z ∧ e = s(y, z)} ∧
    (G.deleteEdges (thinEdges G x y)).Adj x y ∧
    Disjoint ((G.deleteEdges (thinEdges G x y)).neighborSet x)
      ((G.deleteEdges (thinEdges G x y)).neighborSet y) ∧
    contractEdge (G.deleteEdges (thinEdges G x y)) x y = contractEdge G x y :=
  ⟨rfl, deleteEdges_thinEdges_adj hxy, disjoint_neighborSet_deleteEdges_thinEdges,
    contractEdge_deleteEdges_thinEdges hxy⟩

/-- **Minor models through a contraction**: when both ends of `xy` lie in one branch set, the
images of the branch sets form a minor model in the contraction. -/
example {W : Type*} {H : SimpleGraph W} (m : MinorModel H G) {x y : V} (hxy : G.Adj x y) {w₀ : W}
    (hx : x ∈ m.branch w₀) (hy : y ∈ m.branch w₀) (w : W) :
    (m.contractEdge hxy hx hy).branch w = contractVertex hxy.ne '' m.branch w :=
  rfl

end Statements

/-- **Connected sets**: they go to connected sets under any map sending adjacent vertices to equal
or adjacent vertices, and contain an edge if they have two vertices. -/
example {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} {s : Set V}
    (h : IsConnectedSet G s) (f : V → W)
    (hf : ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → f u = f v ∨ G'.Adj (f u) (f v)) :
    IsConnectedSet G' (f '' s) ∧ (s.Nontrivial → ∃ x ∈ s, ∃ y ∈ s, G.Adj x y) :=
  ⟨h.image_of_eq_or_adj f hf, fun ⟨_, hu, _, hv, huv⟩ => h.exists_adj_of_ne hu hv huv⟩

/-- **Closure under contraction, injective homomorphisms and minors**, with only `[Finite V]` and
planarity as hypotheses; nothing is assumed of the vertex type `W` of the minor. -/
example {V W : Type*} [Finite V] {G : SimpleGraph V} {H : SimpleGraph W} (hG : IsPlanar G) :
    (∀ {x y : V}, G.Adj x y → IsPlanar (contractEdge G x y)) ∧
      (∀ f : H →g G, Function.Injective f → IsPlanar H) ∧ (IsMinor H G → IsPlanar H) :=
  ⟨fun hxy => hG.contractEdge hxy, fun f hf => hG.of_injective f hf, fun h => hG.of_minor h⟩

/-- **The easy direction of Wagner's theorem**: a planar graph on a finite vertex type, connected
or not, bipartite or not, has neither a `K₅` minor nor a `K₃,₃` minor. -/
example {V : Type*} [Finite V] {G : SimpleGraph V} (hG : IsPlanar G) :
    ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G ∧
      ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G :=
  hG.wagner_easy

/-- **Planarity is a proper minor-closed class**, so Mader's theorem gives it a linear edge bound
too, besides `3v − 6`. -/
example : IsMinorClosed (fun _ G => IsPlanar G) ∧ IsProperClass (fun _ G => IsPlanar G) ∧
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsPlanar G →
      G.edgeSet.ncard ≤ C * Fintype.card V :=
  ⟨isMinorClosed_isPlanar, isProperClass_isPlanar,
    IsMinorClosed.exists_ncard_edgeSet_le isMinorClosed_isPlanar isProperClass_isPlanar⟩

/-! ## Sanity checks: contractions -/

/-- A set that no edge leaves contains everything reachable from it. -/
private theorem mem_of_reachable_of_closed {V : Type*} {G : SimpleGraph V} {s : Set V}
    (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s) {u w : V} (h : G.Reachable u w) (hu : u ∈ s) :
    w ∈ s :=
  let ⟨p⟩ := h
  (exists_reachable_induce_of_walk_closed hs p hu).1

section K2

/-- `K₂` is acyclic. -/
private theorem isAcyclic_top_fin_two : (⊤ : SimpleGraph (Fin 2)).IsAcyclic := by
  have h2 : ∀ x y z : Fin 2, x ≠ z → y ≠ z → x = y := by decide
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro v w h
  rw [isBridge_iff]
  have hiso : v ∈ isolatedVerts ((⊤ : SimpleGraph (Fin 2)).deleteEdges {s(v, w)}) := by
    intro z hz
    rw [deleteEdges_adj, Set.mem_singleton_iff] at hz
    exact hz.2 (by rw [h2 z w v hz.1.ne.symm h.ne.symm])
  exact fun hr => h.ne (eq_of_reachable_of_mem_isolatedVerts hiso hr)

/-- The dart from `0` to `1` in `K₂`. -/
private abbrev k2e : (⊤ : SimpleGraph (Fin 2)).Dart := ⟨(0, 1), (top_adj 0 1).mpr (by decide)⟩

private theorem k2e_disj :
    Disjoint ((⊤ : SimpleGraph (Fin 2)).neighborSet k2e.fst)
      ((⊤ : SimpleGraph (Fin 2)).neighborSet k2e.snd) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  rw [mem_neighborSet, top_adj] at h1 h2
  exact (by decide : ∀ z : Fin 2, (0 : Fin 2) ≠ z → (1 : Fin 2) ≠ z → False) z h1 h2

/-- **Contracting `K₂`**: its rotation system stays spherical; its only face disappears, and the
contracted vertex, the only one left, is isolated and supplies the extra face. -/
example : (k2Rotation.contract k2e k2e_disj).IsSpherical ∧
    Nat.card (k2Rotation.contract k2e k2e_disj).Face = 0 ∧ Nat.card k2Rotation.Face = 1 ∧
    isolatedVerts (contractEdge (⊤ : SimpleGraph (Fin 2)) 0 1) = Set.univ := by
  have hρ : k2Rotation.IsSpherical := IsSpherical.of_isAcyclic _ isAcyclic_top_fin_two
  -- The contraction has one vertex, so no edge and no dart.
  have hone : ∀ p r : {v : Fin 2 // v ≠ 1}, p = r := fun p r =>
    Subtype.ext ((by decide : ∀ p r : Fin 2, p ≠ 1 → r ≠ 1 → p = r) _ _ p.2 r.2)
  have hiso : isolatedVerts (contractEdge (⊤ : SimpleGraph (Fin 2)) 0 1) = Set.univ :=
    Set.eq_univ_of_forall fun p r h => h.ne (hone p r)
  have hF : Nat.card (k2Rotation.contract k2e k2e_disj).Face = 0 := by
    have : IsEmpty (contractEdge (⊤ : SimpleGraph (Fin 2)) 0 1).Dart :=
      ⟨fun d => d.adj.ne (hone _ _)⟩
    have : IsEmpty (k2Rotation.contract k2e k2e_disj).Face :=
      ⟨fun q => Quotient.inductionOn q fun d => isEmptyElim d⟩
    exact Nat.card_of_isEmpty
  have h := k2Rotation.natCard_face_contract_add k2e k2e_disj
  rw [ite_eq_left ⟨rfl, rfl⟩, hF] at h
  exact ⟨hρ.contract k2e k2e_disj, hF, by omega, hiso⟩

end K2

section Star

/-- The dart from `1` to `2` in `K₄`. -/
private abbrev st12 : (⊤ : SimpleGraph (Fin 4)).Dart := ⟨(1, 2), (top_adj 1 2).mpr (by decide)⟩

/-- `K₄` without `{1, 2}`. -/
private abbrev stG₁ : SimpleGraph (Fin 4) := (⊤ : SimpleGraph (Fin 4)).deleteEdges {st12.edge}

private abbrev st13 : stG₁.Dart :=
  ⟨(1, 3), deleteEdges_adj.mpr ⟨(top_adj 1 3).mpr (by decide), by decide⟩⟩

private abbrev stG₂ : SimpleGraph (Fin 4) := stG₁.deleteEdges {st13.edge}

private abbrev st23 : stG₂.Dart :=
  ⟨(2, 3), deleteEdges_adj.mpr ⟨deleteEdges_adj.mpr ⟨(top_adj 2 3).mpr (by decide), by decide⟩,
    by decide⟩⟩

/-- **The star** `K₁,₃` with centre `0`: `K₄` without the triangle `1 2 3`. -/
private abbrev star : SimpleGraph (Fin 4) := stG₂.deleteEdges {st23.edge}

/-- Its rotation system, obtained from `K₄`'s by deleting the triangle. -/
private noncomputable abbrev starRotation : RotationSystem star :=
  ((k4Rotation.deleteEdge st12).deleteEdge st13).deleteEdge st23

private theorem isSpherical_starRotation : starRotation.IsSpherical :=
  ((isSpherical_k4Rotation.deleteEdge st12).deleteEdge st13).deleteEdge st23

/-- The leaf edge from the centre `0` to `1`. -/
private abbrev star01 : star.Dart :=
  ⟨(0, 1), deleteEdges_adj.mpr ⟨deleteEdges_adj.mpr ⟨deleteEdges_adj.mpr
    ⟨(top_adj 0 1).mpr (by decide), by decide⟩, by decide⟩, by decide⟩⟩

private theorem star_adj_iff (u w : Fin 4) : star.Adj u w ↔ u ≠ w ∧ (u = 0 ∨ w = 0) := by
  simp only [deleteEdges_adj, top_adj, Set.mem_singleton_iff]
  revert u w
  decide

private theorem star01_disj :
    Disjoint (star.neighborSet star01.fst) (star.neighborSet star01.snd) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  rw [mem_neighborSet, star_adj_iff] at h1 h2
  revert z
  decide

/-- **The star is a tree**: connected, with three edges on four vertices. -/
private theorem isTree_star : star.IsTree := by
  have hE : star.edgeSet.ncard = 3 := by
    have h1 : stG₁.edgeSet.ncard + 1 = (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard :=
      ncard_edgeSet_deleteEdges_add_one st12
    have h2 : stG₂.edgeSet.ncard + 1 = stG₁.edgeSet.ncard := ncard_edgeSet_deleteEdges_add_one st13
    have h3 : star.edgeSet.ncard + 1 = stG₂.edgeSet.ncard := ncard_edgeSet_deleteEdges_add_one st23
    have h6 : (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard = 6 := by
      rw [ncard_edgeSet_top_four]
    omega
  rw [isTree_iff_connected_and_card]
  refine ⟨(connected_iff_exists_forall_reachable star).mpr ⟨0, fun w => ?_⟩, ?_⟩
  · by_cases hw : w = 0
    · rw [hw]
    · exact ((star_adj_iff 0 w).mpr ⟨Ne.symm hw, Or.inl rfl⟩).reachable
  · rw [Nat.card_coe_set_eq, hE, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **Contracting a leaf edge of a tree**: the leaf `1` of the star, whose only neighbour is the
centre `0`.  The rotation system obtained from `K₄`'s stays spherical; the contraction is a path on
the three remaining vertices, with two edges. -/
example : star.IsTree ∧ (∀ w, star.Adj 1 w → w = 0) ∧
    (starRotation.contract star01 star01_disj).IsSpherical ∧
    (contractEdge star 0 1).edgeSet.ncard = 2 := by
  have hE := ncard_edgeSet_contractEdge_add_one star01 star01_disj
  have h3 : star.edgeSet.ncard = 3 := by
    have := isTree_star.card_edgeFinset
    have h := (isTree_iff_connected_and_card.mp isTree_star).2
    rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega
  refine ⟨isTree_star, fun w h => ?_, isSpherical_starRotation.contract star01 star01_disj, ?_⟩
  · rw [star_adj_iff] at h
    revert w
    decide
  · change (contractEdge star star01.fst star01.snd).edgeSet.ncard = 2
    omega

/-- **Deleting a leaf edge** of the star: the rotation system stays spherical and the leaf becomes
isolated. -/
example : (starRotation.deleteEdge star01).IsSpherical ∧
    (1 : Fin 4) ∈ isolatedVerts (star.deleteEdges {star01.edge}) := by
  refine ⟨isSpherical_starRotation.deleteEdge star01, fun w hw => ?_⟩
  rw [deleteEdges_adj, star_adj_iff, Set.mem_singleton_iff] at hw
  revert w
  decide

end Star

section Cycle

private abbrev cy02 : (⊤ : SimpleGraph (Fin 4)).Dart := ⟨(0, 2), (top_adj 0 2).mpr (by decide)⟩

private abbrev cyG₁ : SimpleGraph (Fin 4) := (⊤ : SimpleGraph (Fin 4)).deleteEdges {cy02.edge}

private abbrev cy13 : cyG₁.Dart :=
  ⟨(1, 3), deleteEdges_adj.mpr ⟨(top_adj 1 3).mpr (by decide), by decide⟩⟩

/-- **The `4`-cycle** `0 - 1 - 2 - 3 - 0`: `K₄` without its diagonals. -/
private abbrev cycle4 : SimpleGraph (Fin 4) := cyG₁.deleteEdges {cy13.edge}

private abbrev cy01 : cycle4.Dart :=
  ⟨(0, 1), deleteEdges_adj.mpr ⟨deleteEdges_adj.mpr ⟨(top_adj 0 1).mpr (by decide), by decide⟩,
    by decide⟩⟩

private theorem cycle4_adj_iff (u w : Fin 4) :
    cycle4.Adj u w ↔ u ≠ w ∧ ¬ (u.val + w.val = 2 ∧ u.val * w.val = 0) ∧
      ¬ (u.val + w.val = 4 ∧ u.val * w.val = 3) := by
  simp only [deleteEdges_adj, top_adj, Set.mem_singleton_iff]
  revert u w
  decide

private theorem cy01_disj :
    Disjoint (cycle4.neighborSet cy01.fst) (cycle4.neighborSet cy01.snd) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  rw [mem_neighborSet, cycle4_adj_iff] at h1 h2
  revert z
  decide

/-- **Contracting an edge of a cycle**: the edge `{0, 1}` of the `4`-cycle lies on the cycle, so it
is not a bridge; contracting it keeps the rotation system obtained from `K₄`'s spherical, and leaves
a triangle. -/
example : ¬ cycle4.IsBridge cy01.edge ∧
    (((k4Rotation.deleteEdge cy02).deleteEdge cy13).contract cy01 cy01_disj).IsSpherical ∧
    (contractEdge cycle4 0 1).edgeSet.ncard = 3 := by
  refine ⟨?_, ((isSpherical_k4Rotation.deleteEdge cy02).deleteEdge cy13).contract cy01 cy01_disj,
    ?_⟩
  · rw [show cy01.edge = s(0, 1) from rfl, isBridge_iff, not_not]
    have hadj : ∀ u w : Fin 4, (u, w) ∈ [((0 : Fin 4), (3 : Fin 4)), (3, 2), (2, 1)] →
        (cycle4.deleteEdges {s(0, 1)}).Adj u w := by
      intro u w h
      rw [deleteEdges_adj, cycle4_adj_iff, Set.mem_singleton_iff]
      revert u w
      decide
    exact (hadj 0 3 (by simp)).reachable.trans ((hadj 3 2 (by simp)).reachable.trans
      (hadj 2 1 (by simp)).reachable)
  · have hE : (contractEdge cycle4 0 1).edgeSet.ncard + 1 = cycle4.edgeSet.ncard :=
      ncard_edgeSet_contractEdge_add_one cy01 cy01_disj
    have h1 : cyG₁.edgeSet.ncard + 1 = (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard :=
      ncard_edgeSet_deleteEdges_add_one cy02
    have h2 : cycle4.edgeSet.ncard + 1 = cyG₁.edgeSet.ncard :=
      ncard_edgeSet_deleteEdges_add_one cy13
    have h6 : (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard = 6 := by rw [ncard_edgeSet_top_four]
    omega

end Cycle

section K4

private abbrev k12 : (⊤ : SimpleGraph (Fin 4)).Dart := ⟨(1, 2), (top_adj 1 2).mpr (by decide)⟩

private abbrev kG₁ : SimpleGraph (Fin 4) := (⊤ : SimpleGraph (Fin 4)).deleteEdges {k12.edge}

private abbrev k13 : kG₁.Dart :=
  ⟨(1, 3), deleteEdges_adj.mpr ⟨(top_adj 1 3).mpr (by decide), by decide⟩⟩

/-- `K₄` thinned for contracting `{0, 1}`: the edges `{1, 2}` and `{1, 3}` to the common
neighbours `2` and `3` are deleted. -/
private abbrev kG₂ : SimpleGraph (Fin 4) := kG₁.deleteEdges {k13.edge}

private abbrev k01 : kG₂.Dart :=
  ⟨(0, 1), deleteEdges_adj.mpr ⟨deleteEdges_adj.mpr ⟨(top_adj 0 1).mpr (by decide), by decide⟩,
    by decide⟩⟩

private theorem k01_disj : Disjoint (kG₂.neighborSet k01.fst) (kG₂.neighborSet k01.snd) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  simp only [mem_neighborSet, deleteEdges_adj, top_adj, Set.mem_singleton_iff] at h1 h2
  revert z
  decide

/-- **Contracting an edge of `K₄`**: its ends `0` and `1` have the common neighbours `2` and `3`,
so the dart map is not one to one; the thinning deletes `{1, 2}` and `{1, 3}`.  The thinned rotation
system obtained from `K₄`'s contracts to a spherical one, on the same graph as the contraction of
`K₄`, a triangle; and `K₄`'s contraction is planar. -/
example : ¬ Disjoint ((⊤ : SimpleGraph (Fin 4)).neighborSet 0)
      ((⊤ : SimpleGraph (Fin 4)).neighborSet 1) ∧
    thinEdges (⊤ : SimpleGraph (Fin 4)) 0 1 = {s(1, 2), s(1, 3)} ∧
    (((k4Rotation.deleteEdge k12).deleteEdge k13).contract k01 k01_disj).IsSpherical ∧
    contractEdge kG₂ 0 1 = contractEdge (⊤ : SimpleGraph (Fin 4)) 0 1 ∧
    IsPlanar (contractEdge (⊤ : SimpleGraph (Fin 4)) 0 1) := by
  refine ⟨fun h => Set.disjoint_left.mp h
      (show (2 : Fin 4) ∈ (⊤ : SimpleGraph (Fin 4)).neighborSet 0 from
        (top_adj 0 2).mpr (by decide))
      ((top_adj 1 2).mpr (by decide)), ?_,
    ((isSpherical_k4Rotation.deleteEdge k12).deleteEdge k13).contract k01 k01_disj, ?_,
    isPlanar_top_four.contractEdge ((top_adj 0 1).mpr (by decide))⟩
  · ext e
    induction e using Sym2.ind with
    | h u w =>
    simp only [thinEdges, top_adj, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, h0, h1, he⟩
      rw [he]
      clear he
      revert z
      decide
    · rintro (h | h)
      · exact ⟨2, by decide, by decide, h⟩
      · exact ⟨3, by decide, by decide, h⟩
  · ext p r
    simp only [contractEdge_adj, deleteEdges_adj, top_adj, Set.mem_singleton_iff]
    revert p r
    decide

end K4

/-! ## Sanity checks: deletions and induced subgraphs -/

section Path

private abbrev pa02 : (⊤ : SimpleGraph (Fin 4)).Dart := ⟨(0, 2), (top_adj 0 2).mpr (by decide)⟩

private abbrev paG₁ : SimpleGraph (Fin 4) := (⊤ : SimpleGraph (Fin 4)).deleteEdges {pa02.edge}

private abbrev pa03 : paG₁.Dart :=
  ⟨(0, 3), deleteEdges_adj.mpr ⟨(top_adj 0 3).mpr (by decide), by decide⟩⟩

private abbrev paG₂ : SimpleGraph (Fin 4) := paG₁.deleteEdges {pa03.edge}

private abbrev pa13 : paG₂.Dart :=
  ⟨(1, 3), deleteEdges_adj.mpr ⟨deleteEdges_adj.mpr ⟨(top_adj 1 3).mpr (by decide), by decide⟩,
    by decide⟩⟩

/-- **The path** `0 - 1 - 2 - 3`: `K₄` without `{0, 2}`, `{0, 3}` and `{1, 3}`. -/
private abbrev path4 : SimpleGraph (Fin 4) := paG₂.deleteEdges {pa13.edge}

private noncomputable abbrev pathRotation : RotationSystem path4 :=
  ((k4Rotation.deleteEdge pa02).deleteEdge pa03).deleteEdge pa13

private theorem isSpherical_pathRotation : pathRotation.IsSpherical :=
  ((isSpherical_k4Rotation.deleteEdge pa02).deleteEdge pa03).deleteEdge pa13

private abbrev pa12 : path4.Dart :=
  ⟨(1, 2), deleteEdges_adj.mpr ⟨deleteEdges_adj.mpr ⟨deleteEdges_adj.mpr
    ⟨(top_adj 1 2).mpr (by decide), by decide⟩, by decide⟩, by decide⟩⟩

private theorem path4_adj_iff (u w : Fin 4) :
    path4.Adj u w ↔ u ≠ w ∧ (u.val + 1 = w.val ∨ w.val + 1 = u.val) := by
  simp only [deleteEdges_adj, top_adj, Set.mem_singleton_iff]
  revert u w
  decide

/-- The path without its middle edge: the edges `{0, 1}` and `{2, 3}`. -/
private abbrev twoEdges : SimpleGraph (Fin 4) := path4.deleteEdges {pa12.edge}

private theorem twoEdges_adj_iff (u w : Fin 4) :
    twoEdges.Adj u w ↔ u ≠ w ∧ ((u.val + w.val = 1) ∨ (u.val + w.val = 5)) := by
  rw [deleteEdges_adj, path4_adj_iff, Set.mem_singleton_iff]
  revert u w
  decide

/-- **Deleting an edge whose two sides keep edges**: deleting the middle edge of the path
`0 - 1 - 2 - 3` keeps the rotation system spherical and splits the path into the two components
`{0, 1}` and `{2, 3}`, which both keep an edge. -/
example : path4.IsBridge pa12.edge ∧ (pathRotation.deleteEdge pa12).IsSpherical ∧
    Nat.card twoEdges.ConnectedComponent = Nat.card path4.ConnectedComponent + 1 ∧
    twoEdges.Adj 0 1 ∧ twoEdges.Adj 2 3 := by
  have hb : path4.IsBridge pa12.edge := by
    rw [show pa12.edge = s(1, 2) from rfl, isBridge_iff]
    intro h
    have hs : ∀ ⦃u w : Fin 4⦄, twoEdges.Adj u w → u ∈ ({0, 1} : Set (Fin 4)) →
        w ∈ ({0, 1} : Set (Fin 4)) := by
      intro u w huw hu
      rw [twoEdges_adj_iff] at huw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
      revert u w
      decide
    have := mem_of_reachable_of_closed hs h (by simp)
    simp at this
  exact ⟨hb, isSpherical_pathRotation.deleteEdge pa12,
    natCard_connectedComponent_deleteEdges_of_isBridge hb,
    (twoEdges_adj_iff 0 1).mpr (by decide), (twoEdges_adj_iff 2 3).mpr (by decide)⟩

private abbrev pa01 : twoEdges.Dart := ⟨(0, 1), (twoEdges_adj_iff 0 1).mpr (by decide)⟩

/-- `{2, 3}` alone. -/
private abbrev oneEdge : SimpleGraph (Fin 4) := twoEdges.deleteEdges {pa01.edge}

private theorem oneEdge_adj_iff (u w : Fin 4) : oneEdge.Adj u w ↔ u ≠ w ∧ u.val + w.val = 5 := by
  rw [deleteEdges_adj, twoEdges_adj_iff, Set.mem_singleton_iff]
  revert u w
  decide

/-- **Deleting the edge of a `K₂` component**, `{0, 1}`: the rotation system stays spherical and
both ends become isolated.  **An induced subgraph with isolated vertices**: the graph induced on
`{0, 1, 2}`, where `0` and `1` are isolated, is planar. -/
example : ((pathRotation.deleteEdge pa12).deleteEdge pa01).IsSpherical ∧
    (0 : Fin 4) ∈ isolatedVerts oneEdge ∧ (1 : Fin 4) ∈ isolatedVerts oneEdge ∧
    IsPlanar (oneEdge.induce {0, 1, 2}) := by
  have hρ := (isSpherical_pathRotation.deleteEdge pa12).deleteEdge pa01
  refine ⟨hρ, fun w hw => ?_, fun w hw => ?_, IsPlanar.induce ⟨_, hρ⟩ _⟩
  · rw [oneEdge_adj_iff] at hw
    revert w
    decide
  · rw [oneEdge_adj_iff] at hw
    revert w
    decide

end Path

/-! ## Sanity checks: minor models -/

section Model

/-- **A minor model of `K₂` in `K₄`**: the branch sets `{0, 1}` and `{2}`.  The vertex `3` is
unused, and only one of the five edges between or inside the branch sets is needed, besides
`{0, 1}`. -/
private def k2InK4 : MinorModel (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 4)) where
  branch w := if w = 0 then {0, 1} else {2}
  connected w := by
    split_ifs
    · exact isConnectedSet_pair ((top_adj 0 1).mpr (by decide))
    · exact isConnectedSet_singleton _ _
  disjoint w w' h := by
    have hw : ∀ w : Fin 2, w = 0 ∨ w = 1 := by decide
    rcases hw w with rfl | rfl <;> rcases hw w' with rfl | rfl
    · exact absurd rfl h
    · simp
    · simp
    · exact absurd rfl h
  adj w w' h := by
    have hw : ∀ w : Fin 2, w = 0 ∨ w = 1 := by decide
    rcases hw w with rfl | rfl <;> rcases hw w' with rfl | rfl
    · exact absurd rfl h.ne
    · exact ⟨1, by simp, 2, by simp, (top_adj 1 2).mpr (by decide)⟩
    · exact ⟨2, by simp, 1, by simp, (top_adj 2 1).mpr (by decide)⟩
    · exact absurd rfl h.ne

/-- **Pushing the model through the contraction of its internal edge `{0, 1}`**: both branch sets
become single vertices, the contracted vertex and `2`; then the representatives give an injective
homomorphism.  And `K₂` is planar as a minor of `K₄`. -/
example : (k2InK4.contractEdge ((top_adj 0 1).mpr (by decide)) (w₀ := 0) (by simp [k2InK4])
      (by simp [k2InK4])).branch 0 = {⟨0, by decide⟩} ∧
    (k2InK4.contractEdge ((top_adj 0 1).mpr (by decide)) (w₀ := 0) (by simp [k2InK4])
      (by simp [k2InK4])).branch 1 = {⟨2, by decide⟩} ∧
    IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨?_, ?_, isPlanar_top_four.of_minor ⟨k2InK4⟩⟩
  · rw [MinorModel.branch_contractEdge]
    simp only [k2InK4, ite_true, Set.image_insert_eq, Set.image_singleton]
    rw [contractVertex_self, contractVertex_of_ne _ (by decide)]
    simp
  · rw [MinorModel.branch_contractEdge]
    simp only [k2InK4]
    rw [ite_eq_right (by decide), Set.image_singleton, contractVertex_of_ne _ (by decide)]

end Model

/-! ## Sanity check: the Petersen graph -/

/-- **The Petersen graph**: the outer cycle `0 - 1 - 2 - 3 - 4`, the spokes `i - (i + 5)`, and the
inner pentagram `5 - 7 - 9 - 6 - 8`. -/
def petersen : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun u v =>
  (u.val < 5 ∧ v.val = (u.val + 1) % 5) ∨ (u.val < 5 ∧ v.val = u.val + 5) ∨
    (5 ≤ u.val ∧ v.val = (u.val - 5 + 2) % 5 + 5)

instance : DecidableRel petersen.Adj := fun u v =>
  decidable_of_iff _ (fromRel_adj _ u v).symm

/-- The branch set of `i`: the spoke from `i` to `i + 5`. -/
private def petBranch (i : Fin 5) : Finset (Fin 10) := {⟨i, by omega⟩, ⟨i + 5, by omega⟩}

private theorem petBranch_adj : ∀ i : Fin 5,
    petersen.Adj ⟨i, by omega⟩ ⟨i + 5, by omega⟩ := by decide

private theorem petBranch_disjoint :
    ∀ i j : Fin 5, i ≠ j → Disjoint (petBranch i) (petBranch j) := by
  decide

private theorem petBranch_edges : ∀ i j : Fin 5, i ≠ j →
    ∃ a ∈ petBranch i, ∃ b ∈ petBranch j, petersen.Adj a b := by
  decide

/-- **A `K₅` minor of the Petersen graph**: contract the five spokes. -/
private def petersenModel : MinorModel (⊤ : SimpleGraph (Fin 5)) petersen where
  branch i := ↑(petBranch i)
  connected i := by
    rw [petBranch, Finset.coe_insert, Finset.coe_singleton]
    exact isConnectedSet_pair (petBranch_adj i)
  disjoint i j h := Finset.disjoint_coe.mpr (petBranch_disjoint i j h)
  adj i j h := by
    obtain ⟨a, ha, b, hb, hab⟩ := petBranch_edges i j h.ne
    exact ⟨a, Finset.mem_coe.mpr ha, b, Finset.mem_coe.mpr hb, hab⟩

/-- **The Petersen graph is not planar**, although its `15` edges are within `3·10 − 6 = 24`: it
has a `K₅` minor. -/
example : ¬ IsPlanar petersen ∧ petersen.edgeFinset.card = 15 :=
  ⟨fun h => h.not_isMinor_top_five ⟨petersenModel⟩, by decide⟩

end MonoidProduct.Graph
