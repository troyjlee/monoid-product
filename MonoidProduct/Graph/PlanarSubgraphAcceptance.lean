import MonoidProduct.Graph.PlanarSubgraph
import MonoidProduct.Graph.PlanarExamples
set_option linter.style.header false

/-!
# Acceptance statements for edge deletion and subgraph closure of planarity

The statements of `Graph/RotationPermutation.lean`, `Graph/RotationDeletion.lean` and
`Graph/PlanarSubgraph.lean`, restated with the definitions unfolded where that makes their
meaning visible, followed by small sanity checks.  Lean checks every `example` here against the
library's statement.

* Cycle counts include fixed points; a transposition splits or merges cycles; erasing an element
  bypasses it and loses a cycle only if it was fixed.
* The Euler defect `2C − V + E − (F + I)`, Euler's inequality for every rotation system, globally
  and componentwise (`V_c + F_c ≤ E_c + 2`), and sphericity as defect zero.
* Deleting an edge: the rotation and the faces after the deletion, and the table of changes of the
  components, completed faces and defect for a bridge, for a non-bridge on two faces, and for a
  non-bridge on one face.
* Closure: subgraphs, deleted edges and induced subgraphs of planar graphs are planar, with only
  `[Finite V]` and planarity as hypotheses.

The sanity checks cover:
* the identity of `Fin 3` (three cycles), a transposition (two), and erasing from a `3`-cycle;
* `K₄`: its explicit rotation system has defect `2·1 − 4 + 6 − (4 + 0) = 0`; deleting the edge
  `{0, 1}`, which is on a cycle, keeps it spherical, with its two darts on two faces, which merge
  into one, leaving three faces;
* a bridge: deleting `{0, 1}` and then `{0, 2}` from `K₄`'s rotation system leaves `0` hanging
  from `3`; deleting that bridge keeps the rotation system spherical, adds a component and makes
  `0` isolated;
* `K₂`: its rotation system has one face; deleting the only edge keeps it spherical, removes the
  face and isolates both ends;
* `K₅`: every rotation system has positive defect.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm RotationSystem

/-! ## Cycle counts -/

section Perm

variable {α : Type*} [Finite α] [DecidableEq α]

/-- **The cycle count** of a permutation counts its orbits, fixed points included. -/
example (p : Perm α) : cycleCount p = Nat.card (Quotient (SameCycle.setoid p)) := rfl

/-- **A transposition splits or merges cycles**: right multiplication by `swap a b` adds a cycle
when `a ≠ b` lie in one cycle, and removes one when they lie in two. -/
example (p : Perm α) {a b : α} (hab : a ≠ b) :
    (p.SameCycle a b → cycleCount (p * swap a b) = cycleCount p + 1) ∧
      (¬ p.SameCycle a b → cycleCount (p * swap a b) + 1 = cycleCount p) :=
  ⟨cycleCount_mul_swap_of_sameCycle hab, cycleCount_mul_swap_of_not_sameCycle⟩

/-- **Erasing an element**: the successor is `p d`, or `p a` when `p d = a`; the survivors keep
their cycles; a cycle is lost exactly when `a` was a fixed point. -/
example (p : Perm α) (a : α) :
    (∀ d : {d // d ≠ a}, (eraseOne p a d : α) = if p d = a then p a else p d) ∧
      (∀ d d' : {d // d ≠ a}, (eraseOne p a).SameCycle d d' ↔ p.SameCycle d d') ∧
      cycleCount (eraseOne p a) + (if p a = a then 1 else 0) = cycleCount p :=
  ⟨eraseOne_apply p a, fun _ _ => sameCycle_eraseOne_iff p a, cycleCount_eraseOne p a⟩

/-- **Erasing two elements** at once, and conjugation by an equivalence. -/
example (p : Perm α) {a b : α} (hab : a ≠ b) {β : Type*} (e : α ≃ β) :
    cycleCount (eraseTwo p a b) + (if p a = a then 1 else 0) +
        (if bypass p a b = b then 1 else 0) = cycleCount p ∧
      cycleCount (e.permCongr p) = cycleCount p :=
  ⟨cycleCount_eraseTwo_add p hab, cycleCount_permCongr e p⟩

end Perm

/-- The identity has a cycle for each element. -/
private theorem cycleCount_one {α : Type*} : cycleCount (1 : Perm α) = Nat.card α :=
  (Nat.card_eq_of_bijective (fun x : α => Quotient.mk (SameCycle.setoid 1) x)
    ⟨fun _ _ h => sameCycle_one.mp (Quotient.exact h),
      fun q => Quotient.inductionOn q fun x => ⟨x, rfl⟩⟩).symm

/-- **Fixed points count**: the identity of `Fin 3` has three cycles, and the transposition
`(0 1)`, which merges two of them, has two. -/
example : cycleCount (1 : Perm (Fin 3)) = 3 ∧ cycleCount (swap (0 : Fin 3) 1) = 2 := by
  have h3 : cycleCount (1 : Perm (Fin 3)) = 3 := by rw [cycleCount_one, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  refine ⟨h3, ?_⟩
  have h := cycleCount_mul_swap_of_not_sameCycle (p := (1 : Perm (Fin 3))) (a := 0) (b := 1)
    (fun h => absurd (sameCycle_one.mp h) (by decide))
  rw [one_mul, h3] at h
  omega

/-- **Bypassing in a `3`-cycle**: erasing `1` from `0 ↦ 1 ↦ 2 ↦ 0` sends `0` to `2`. -/
example : (eraseOne (swap (0 : Fin 3) 1 * swap 1 2) 1 ⟨0, by decide⟩ : Fin 3) = 2 := by
  rw [eraseOne_apply]
  decide

/-! ## The Euler defect and deletion -/

section Graphs

variable {V : Type*} [Finite V] {G : SimpleGraph V} (ρ : RotationSystem G)

/-- **The Euler defect**, unfolded: `2C − V + E − (F + I)`, with `I` the isolated vertices. -/
example : ρ.eulerDefect = 2 * Nat.card G.ConnectedComponent - Nat.card V + G.edgeSet.ncard -
    (Nat.card ρ.Face + {v | ∀ w, ¬ G.Adj v w}.ncard) := rfl

/-- **Euler's inequality** for every rotation system of every graph on a finite vertex type,
globally, `0 ≤ 2C − V + E − F̂`, and in every component with an edge,
`V_c + F_c ≤ E_c + 2`. -/
example : 0 ≤ ρ.eulerDefect ∧ ∀ c : G.ConnectedComponent, (componentEdges G c).Nonempty →
    c.supp.ncard + (ρ.facesIn c).ncard ≤ (componentEdges G c).ncard + 2 :=
  ⟨ρ.eulerDefect_nonneg, fun _ hc => ρ.ncard_supp_add_ncard_facesIn_le hc⟩

/-- **Spherical means defect zero**, and the defect is the sum of the component defects. -/
example : (ρ.IsSpherical ↔ ρ.eulerDefect = 0) ∧ ρ.eulerDefect = ∑ᶠ c, ρ.componentDefect c :=
  ⟨ρ.isSpherical_iff_eulerDefect_eq_zero, ρ.eulerDefect_eq_finsum⟩

variable [DecidableEq V] (a : G.Dart)

/-- **Deleting the edge of `a`**: the rotation erases `a` and `a.symm`, and the face permutation
is that of `face * swap a a.symm` with `a` and `a.symm` erased. -/
example : (ρ.deleteEdge a).rot = (deleteEdgeDartEquiv a).permCongr (eraseTwo ρ.rot a a.symm) ∧
    (ρ.deleteEdge a).face =
      (deleteEdgeDartEquiv a).permCongr (eraseTwo (ρ.face * swap a a.symm) a a.symm) :=
  ⟨rfl, ρ.deleteEdge_face a⟩

/-- **The table**: the changes of the components `C`, the completed faces `F̂` and the defect
`Δ` when deleting a bridge, a non-bridge whose darts lie on two faces, and a non-bridge whose
darts lie on one face. -/
example :
    (G.IsBridge a.edge → ρ.face.SameCycle a a.symm ∧
      Nat.card (G.deleteEdges {a.edge}).ConnectedComponent = Nat.card G.ConnectedComponent + 1 ∧
      (ρ.deleteEdge a).completedFaceCount = ρ.completedFaceCount + 1 ∧
      (ρ.deleteEdge a).eulerDefect = ρ.eulerDefect) ∧
    (¬ G.IsBridge a.edge → ¬ ρ.face.SameCycle a a.symm →
      Nat.card (G.deleteEdges {a.edge}).ConnectedComponent = Nat.card G.ConnectedComponent ∧
      (ρ.deleteEdge a).completedFaceCount + 1 = ρ.completedFaceCount ∧
      (ρ.deleteEdge a).eulerDefect = ρ.eulerDefect) ∧
    (¬ G.IsBridge a.edge → ρ.face.SameCycle a a.symm →
      Nat.card (G.deleteEdges {a.edge}).ConnectedComponent = Nat.card G.ConnectedComponent ∧
      (ρ.deleteEdge a).completedFaceCount = ρ.completedFaceCount + 1 ∧
      (ρ.deleteEdge a).eulerDefect = ρ.eulerDefect - 2) := by
  refine ⟨fun hb => ⟨ρ.sameCycle_face_of_isBridge hb,
      natCard_connectedComponent_deleteEdges_of_isBridge hb,
      ρ.completedFaceCount_deleteEdge_of_sameCycle (ρ.sameCycle_face_of_isBridge hb),
      ρ.eulerDefect_deleteEdge_of_isBridge hb⟩,
    fun hb h => ⟨natCard_connectedComponent_deleteEdges_of_not_isBridge hb,
      ρ.completedFaceCount_deleteEdge_of_not_sameCycle h,
      ρ.eulerDefect_deleteEdge_of_not_sameCycle h⟩,
    fun hb h => ⟨natCard_connectedComponent_deleteEdges_of_not_isBridge hb,
      ρ.completedFaceCount_deleteEdge_of_sameCycle h,
      ρ.eulerDefect_deleteEdge_of_sameCycle hb h⟩⟩

/-- **Deleting an edge of a spherical rotation system** keeps it spherical; its two darts lie on
one face exactly when the edge is a bridge. -/
example (hρ : ρ.IsSpherical) :
    (ρ.deleteEdge a).IsSpherical ∧ (ρ.face.SameCycle a a.symm ↔ G.IsBridge a.edge) :=
  ⟨hρ.deleteEdge a, hρ.sameCycle_face_iff a⟩

end Graphs

/-- **Closure under subgraphs, deleted edges and induced subgraphs**, with only `[Finite V]` and
planarity as hypotheses: no connectedness is assumed. -/
example {V : Type*} [Finite V] {G H : SimpleGraph V} (hG : IsPlanar G) (hHG : H ≤ G)
    (s : Set (Sym2 V)) (t : Set V) :
    IsPlanar H ∧ IsPlanar (G.deleteEdges s) ∧ IsPlanar (G.induce t) :=
  ⟨hG.mono hHG, hG.deleteEdges s, hG.induce t⟩

/-- **Every rotation system of a forest is spherical.** -/
example {V : Type*} [Finite V] {G : SimpleGraph V} (ρ : RotationSystem G) (h : G.IsAcyclic) :
    ρ.IsSpherical :=
  IsSpherical.of_isAcyclic ρ h

/-! ## Sanity checks -/

section K4

/-- `K₄` is connected. -/
private theorem natCard_connectedComponent_top_four :
    Nat.card (⊤ : SimpleGraph (Fin 4)).ConnectedComponent = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨(⊤ : SimpleGraph (Fin 4)).connectedComponentMk 0, fun c => ?_⟩
  induction c using ConnectedComponent.ind with
  | h v =>
  by_cases hv : v = 0
  · rw [hv]
  · exact ConnectedComponent.eq.mpr ((top_adj v 0).mpr hv).reachable

/-- `K₄` has no isolated vertex. -/
private theorem isolatedVerts_top_four : isolatedVerts (⊤ : SimpleGraph (Fin 4)) = ∅ := by
  have h : ∀ v : Fin 4, v ≠ v + 1 := by decide
  exact Set.eq_empty_of_forall_notMem fun v hv => hv (v + 1) ((top_adj v (v + 1)).mpr (h v))

/-- **`K₄`'s rotation system is spherical, through its defect**: one component, four vertices,
six edges, four faces and no isolated vertex, `2·1 − 4 + 6 − (4 + 0) = 0`. -/
theorem isSpherical_k4Rotation : k4Rotation.IsSpherical := by
  rw [isSpherical_iff_eulerDefect_eq_zero, eulerDefect, completedFaceCount,
    natCard_connectedComponent_top_four, natCard_k4Face, isolatedVerts_top_four, Set.ncard_empty,
    ncard_edgeSet_top_four, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

/-- The dart from `0` to `1` in `K₄`. -/
private abbrev k4d01 : (⊤ : SimpleGraph (Fin 4)).Dart := ⟨(0, 1), (top_adj 0 1).mpr (by decide)⟩

/-- **Deleting an edge on a cycle**: the edge `{0, 1}` of `K₄` is not a bridge, its darts lie on
two faces, and deleting it keeps the rotation system spherical, with the two faces merged into
one: three faces. -/
example : ¬ (⊤ : SimpleGraph (Fin 4)).IsBridge k4d01.edge ∧
    ¬ k4Rotation.face.SameCycle k4d01 k4d01.symm ∧
    (k4Rotation.deleteEdge k4d01).IsSpherical ∧
    Nat.card (k4Rotation.deleteEdge k4d01).Face = 3 := by
  have hb : ¬ (⊤ : SimpleGraph (Fin 4)).IsBridge k4d01.edge := by
    rw [show k4d01.edge = s(0, 1) from rfl, isBridge_iff, not_not]
    have h02 : ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}).Adj 0 2 :=
      deleteEdges_adj.mpr ⟨(top_adj 0 2).mpr (by decide), by decide⟩
    have h21 : ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}).Adj 2 1 :=
      deleteEdges_adj.mpr ⟨(top_adj 2 1).mpr (by decide), by decide⟩
    exact h02.reachable.trans h21.reachable
  have hf : ¬ k4Rotation.face.SameCycle k4d01 k4d01.symm :=
    fun h => hb ((isSpherical_k4Rotation.sameCycle_face_iff k4d01).mp h)
  refine ⟨hb, hf, isSpherical_k4Rotation.deleteEdge k4d01, ?_⟩
  have hF := k4Rotation.completedFaceCount_deleteEdge_of_not_sameCycle hf
  have hI := k4Rotation.ncard_isolatedVerts_deleteEdges k4d01
  have hfix : k4Rotation.rot k4d01 ≠ k4d01 := fun h =>
    absurd (congrArg (fun d : (⊤ : SimpleGraph (Fin 4)).Dart => d.snd) h) (by decide)
  have hfix' : k4Rotation.rot k4d01.symm ≠ k4d01.symm := fun h =>
    absurd (congrArg (fun d : (⊤ : SimpleGraph (Fin 4)).Dart => d.snd) h) (by decide)
  rw [ite_eq_right hfix, ite_eq_right hfix', isolatedVerts_top_four, Set.ncard_empty] at hI
  rw [completedFaceCount, completedFaceCount, hI, natCard_k4Face, isolatedVerts_top_four,
    Set.ncard_empty] at hF
  omega

/-- `K₄` without the edge `{0, 1}`, with its rotation system. -/
private abbrev k4G₁ : SimpleGraph (Fin 4) := (⊤ : SimpleGraph (Fin 4)).deleteEdges {k4d01.edge}

/-- The dart from `0` to `2` without the edge `{0, 1}`. -/
private abbrev k4d02 : k4G₁.Dart :=
  ⟨(0, 2), deleteEdges_adj.mpr ⟨(top_adj 0 2).mpr (by decide), by decide⟩⟩

/-- `K₄` without the edges `{0, 1}` and `{0, 2}`: `0` hangs from `3`. -/
private abbrev k4G₂ : SimpleGraph (Fin 4) := k4G₁.deleteEdges {k4d02.edge}

/-- The dart from `0` to `3`, a bridge of `k4G₂`. -/
private abbrev k4d03 : k4G₂.Dart :=
  ⟨(0, 3), deleteEdges_adj.mpr ⟨deleteEdges_adj.mpr ⟨(top_adj 0 3).mpr (by decide), by decide⟩,
    by decide⟩⟩

/-- **Deleting a bridge**: deleting `{0, 1}` and then `{0, 2}` from `K₄`'s rotation system leaves a
spherical rotation system in which `{0, 3}` is a bridge.  Its two darts lie on one face, and
deleting it keeps the rotation system spherical, adds a component, and makes `0` isolated. -/
example : k4G₂.IsBridge k4d03.edge ∧
    ((k4Rotation.deleteEdge k4d01).deleteEdge k4d02).face.SameCycle k4d03 k4d03.symm ∧
    (((k4Rotation.deleteEdge k4d01).deleteEdge k4d02).deleteEdge k4d03).IsSpherical ∧
    Nat.card (k4G₂.deleteEdges {k4d03.edge}).ConnectedComponent =
      Nat.card k4G₂.ConnectedComponent + 1 ∧
    (0 : Fin 4) ∈ isolatedVerts (k4G₂.deleteEdges {k4d03.edge}) := by
  have hiso : (0 : Fin 4) ∈ isolatedVerts (k4G₂.deleteEdges {k4d03.edge}) := by
    intro w
    simp only [deleteEdges_adj, top_adj, Set.mem_singleton_iff]
    revert w
    decide
  have hb : k4G₂.IsBridge k4d03.edge := by
    rw [show k4d03.edge = s(0, 3) from rfl, isBridge_iff]
    exact fun h => absurd (eq_of_reachable_of_mem_isolatedVerts hiso h) (by decide)
  have hρ : ((k4Rotation.deleteEdge k4d01).deleteEdge k4d02).IsSpherical :=
    (isSpherical_k4Rotation.deleteEdge k4d01).deleteEdge k4d02
  exact ⟨hb, sameCycle_face_of_isBridge _ hb, hρ.deleteEdge k4d03,
    natCard_connectedComponent_deleteEdges_of_isBridge hb, hiso⟩

end K4

section K2

private theorem fin_two_eq : ∀ x y z : Fin 2, x ≠ z → y ≠ z → x = y := by decide

/-- **The rotation system of `K₂`**: each vertex has one dart. -/
def k2Rotation : RotationSystem (⊤ : SimpleGraph (Fin 2)) where
  rot := 1
  fst_rot _ := rfl
  sameCycle_rot d d' h := by
    have : d = d' := Dart.ext _ _ (Prod.ext h (fin_two_eq _ _ _
      (fun e => d.adj.ne (h.trans e.symm)) d'.adj.ne.symm))
    rw [this]

/-- `K₂` is a tree, so acyclic. -/
private theorem isAcyclic_top_two : (⊤ : SimpleGraph (Fin 2)).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro v w h
  rw [isBridge_iff]
  have hiso : v ∈ isolatedVerts ((⊤ : SimpleGraph (Fin 2)).deleteEdges {s(v, w)}) := by
    intro z hz
    rw [deleteEdges_adj, Set.mem_singleton_iff] at hz
    exact hz.2 (by rw [fin_two_eq z w v hz.1.ne.symm h.ne.symm])
  exact fun hr => h.ne (eq_of_reachable_of_mem_isolatedVerts hiso hr)

/-- The dart from `0` to `1` in `K₂`. -/
private abbrev k2d01 : (⊤ : SimpleGraph (Fin 2)).Dart := ⟨(0, 1), (top_adj 0 1).mpr (by decide)⟩

/-- **`K₂`**: its rotation system is spherical with one face.  Deleting the only edge keeps it
spherical; the face disappears and both ends become isolated, each with its extra face. -/
example : k2Rotation.IsSpherical ∧ Nat.card k2Rotation.Face = 1 ∧
    (k2Rotation.deleteEdge k2d01).IsSpherical ∧ Nat.card (k2Rotation.deleteEdge k2d01).Face = 0 ∧
    isolatedVerts ((⊤ : SimpleGraph (Fin 2)).deleteEdges {k2d01.edge}) = Set.univ := by
  have hρ : k2Rotation.IsSpherical := IsSpherical.of_isAcyclic _ isAcyclic_top_two
  have hb : (⊤ : SimpleGraph (Fin 2)).IsBridge k2d01.edge :=
    isAcyclic_iff_forall_adj_isBridge.mp isAcyclic_top_two k2d01.adj
  -- After the deletion there is no edge.
  have hiso : isolatedVerts ((⊤ : SimpleGraph (Fin 2)).deleteEdges {k2d01.edge}) = Set.univ := by
    refine Set.eq_univ_of_forall fun v w hw => ?_
    rw [deleteEdges_adj, Set.mem_singleton_iff] at hw
    revert v w
    decide
  have hfix : k2Rotation.rot k2d01 = k2d01 := rfl
  have hfix' : k2Rotation.rot k2d01.symm = k2d01.symm := rfl
  have hC : Nat.card (⊤ : SimpleGraph (Fin 2)).ConnectedComponent = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨(⊤ : SimpleGraph (Fin 2)).connectedComponentMk 0, fun c => ?_⟩
    induction c using ConnectedComponent.ind with
    | h v =>
    by_cases hv : v = 0
    · rw [hv]
    · exact ConnectedComponent.eq.mpr ((top_adj v 0).mpr hv).reachable
  have hI : isolatedVerts (⊤ : SimpleGraph (Fin 2)) = ∅ := by
    have h : ∀ v : Fin 2, v ≠ v + 1 := by decide
    exact Set.eq_empty_of_forall_notMem fun v hv => hv (v + 1) ((top_adj v (v + 1)).mpr (h v))
  have hE : (⊤ : SimpleGraph (Fin 2)).edgeSet.ncard = 1 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
    rfl
  -- One face, from `Δ = 2·1 − 2 + 1 − (F + 0) = 0`.
  have hF : Nat.card k2Rotation.Face = 1 := by
    have h0 := (k2Rotation.isSpherical_iff_eulerDefect_eq_zero).mp hρ
    rw [eulerDefect, completedFaceCount, hC, hI, Set.ncard_empty, hE, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h0
    omega
  have hF' := k2Rotation.natCard_face_deleteEdge_add k2d01
  have hsc := k2Rotation.sameCycle_face_of_isBridge hb
  rw [ite_eq_left hfix, ite_eq_left hfix',
    cycleCount_mul_swap_of_sameCycle (Ne.symm k2d01.symm_ne) hsc] at hF'
  change _ = Nat.card k2Rotation.Face + 1 at hF'
  refine ⟨hρ, hF, hρ.deleteEdge k2d01, by omega, hiso⟩

end K2

/-- **`K₅`**: every rotation system has positive defect, since `K₅` is not planar. -/
example (ρ : RotationSystem (⊤ : SimpleGraph (Fin 5))) : 0 < ρ.eulerDefect :=
  lt_of_le_of_ne ρ.eulerDefect_nonneg fun h =>
    not_isPlanar_top_five ⟨ρ, (ρ.isSpherical_iff_eulerDefect_eq_zero).mpr h.symm⟩

/-- **Induced subgraphs**: the triangle `K₄[{0, 1, 2}]` and the empty induced graph are planar. -/
example : IsPlanar ((⊤ : SimpleGraph (Fin 4)).induce {0, 1, 2}) ∧
    IsPlanar ((⊤ : SimpleGraph (Fin 4)).induce ∅) :=
  ⟨isPlanar_top_four.induce _, isPlanar_top_four.induce _⟩

end MonoidProduct.Graph
