import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import MonoidProduct.Graph.Planar
import MonoidProduct.Graph.RotationPermutation
set_option linter.style.header false

/-!
# Deleting an edge of a rotation system, and the Euler defect

An inequality of Euler type for every rotation system, and the effect of deleting an edge on it.
`Graph/PlanarSubgraph.lean` deduces that planarity (`Graph/Planar.lean`) is closed under subgraphs
and induced subgraphs.

* `RotationSystem.eulerDefect ρ = 2C − V + E − F̂`, an integer: `C` counts the connected
  components, isolated vertices included, `V` the vertices, `E` the edges, and
  `F̂ = F + I` (`completedFaceCount`) the faces with one more for each of the `I` isolated
  vertices.  For a connected graph with an edge it is `2 − V + E − F`, twice the genus of the
  embedding.
* `RotationSystem.deleteEdge ρ a`: the rotation system of `G.deleteEdges {a.edge}` that erases
  the dart `a` and its reversal from the rotation, `eraseTwo ρ.rot a a.symm`.  Its face
  permutation is `eraseTwo (face * swap a a.symm) a a.symm` (`deleteEdge_face`); in Lean
  `(p * q) d = p (q d)`.
* The counts after the deletion: one edge fewer; one component more exactly when the edge is a
  bridge (`natCard_connectedComponent_deleteEdges_of_isBridge`, `_of_not_isBridge`); and the
  completed face count goes up by one when the two darts lie on one face, down by one otherwise
  (`completedFaceCount_deleteEdge_of_sameCycle`, `_of_not_sameCycle`).  An end of the edge that
  becomes isolated loses a face, a fixed point of `face * swap a a.symm`, and gains its extra
  face, so `F̂` after the deletion is the cycle count of `face * swap a a.symm` plus the isolated
  vertices of `G` (`completedFaceCount_deleteEdge`).
* `sameCycle_face_of_isBridge`: the two darts of a bridge lie on one face.  Otherwise the face of
  `a` would return from the head of `a` to its tail along other edges.
* The table: deleting a bridge, or an edge whose darts lie on two faces, keeps the defect, and
  deleting a non-bridge whose darts lie on one face lowers it by two
  (`eulerDefect_deleteEdge_of_isBridge`, `_of_not_sameCycle`, `_of_sameCycle`); so
  `eulerDefect_deleteEdge_le`.
* `eulerDefect_nonneg`: `0 ≤ Δ` for every rotation system of every graph on a finite vertex type,
  by induction on the edges down to the edgeless graph, where `C = I = V` and `F = E = 0`.  No
  planarity is assumed and no topology is used.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*} {G : SimpleGraph V}

/-- The darts of a graph on a finite vertex type form a finite type. -/
theorem finite_dart [Finite V] : Finite G.Dart :=
  Finite.of_injective (fun d : G.Dart => d.toProd) fun _ _ h => Dart.ext _ _ h

/-! ## The Euler defect -/

variable (G) in
/-- **The isolated vertices** of `G`: those without a neighbour. -/
def isolatedVerts : Set V := {v | ∀ w, ¬ G.Adj v w}

namespace RotationSystem

variable (ρ : RotationSystem G)

/-- **The completed face count** `F̂ = F + I`: the faces, and one more for each isolated vertex.
An isolated vertex has no dart and so lies on no face; with its extra face it satisfies
`V − E + F̂ = 1 − 0 + 1 = 2`. -/
noncomputable def completedFaceCount : ℕ := Nat.card ρ.Face + (isolatedVerts G).ncard

/-- **The Euler defect** `Δ = 2C − V + E − F̂`: `C` counts the connected components, isolated
vertices included, `V` the vertices, `E` the edges and `F̂` the completed faces.  It is the sum
over the components of `2 − V_c + E_c − F̂_c`. -/
noncomputable def eulerDefect : ℤ :=
  2 * Nat.card G.ConnectedComponent - Nat.card V + G.edgeSet.ncard - ρ.completedFaceCount

end RotationSystem

/-! ## Deleting an edge -/

/-- A dart has another edge than `a` exactly when it is neither `a` nor its reversal. -/
theorem dart_edge_ne_iff (d a : G.Dart) : d.edge ≠ a.edge ↔ d ≠ a ∧ d ≠ a.symm := by
  rw [Ne, dart_edge_eq_iff, not_or]

/-- **The darts after deleting the edge of `a`**: the darts of `G` other than `a` and its
reversal. -/
def deleteEdgeDartEquiv (a : G.Dart) :
    {d : G.Dart // d ≠ a ∧ d ≠ a.symm} ≃ (G.deleteEdges {a.edge}).Dart where
  toFun d := ⟨d.1.toProd, deleteEdges_adj.mpr ⟨d.1.adj, (dart_edge_ne_iff d.1 a).mpr d.2⟩⟩
  invFun d := ⟨⟨d.toProd, (deleteEdges_adj.mp d.adj).1⟩,
    (dart_edge_ne_iff ⟨d.toProd, (deleteEdges_adj.mp d.adj).1⟩ a).mp
      (deleteEdges_adj.mp d.adj).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace RotationSystem

variable (ρ : RotationSystem G)

/-- The rotation never sends `a` to its reversal: their tails differ. -/
theorem rot_ne_symm (a : G.Dart) : ρ.rot a ≠ a.symm := fun h => by
  have := congrArg (fun d : G.Dart => d.fst) h
  simp only [ρ.fst_rot] at this
  exact a.adj.ne this

/-- The rotation never sends the reversal of `a` to `a`: their tails differ. -/
theorem rot_symm_ne (a : G.Dart) : ρ.rot a.symm ≠ a := fun h => by
  have := congrArg (fun d : G.Dart => d.fst) h
  simp only [ρ.fst_rot] at this
  exact a.adj.ne this.symm

/-- **The rotation fixes `a` exactly when `a` is the only dart at its tail.** -/
theorem rot_eq_self_iff (a : G.Dart) : ρ.rot a = a ↔ ∀ w, G.Adj a.fst w → w = a.snd := by
  constructor
  · intro h w hw
    have := (ρ.sameCycle_rot a ⟨(a.fst, w), hw⟩ rfl).eq_of_left h
    exact (congrArg (fun d : G.Dart => d.snd) this).symm
  · intro h
    refine Dart.ext _ _ (Prod.ext (ρ.fst_rot a) ?_)
    have hadj : G.Adj a.fst (ρ.rot a).snd := by
      have := (ρ.rot a).adj
      rwa [ρ.fst_rot] at this
    exact h _ hadj

variable [DecidableEq V]

/-- The rotation keeps tails after bypassing two darts. -/
theorem fst_bypass_bypass_rot (a b d : G.Dart) : (bypass (bypass ρ.rot a) b d).fst = d.fst :=
  apply_bypass_eq (g := fun d : G.Dart => d.fst)
    (apply_bypass_eq (g := fun d : G.Dart => d.fst) ρ.fst_rot a) b d

/-- **Deleting the edge of `a`**: the rotation system of `G.deleteEdges {a.edge}` that skips `a`
around its tail and `a.symm` around its head, `eraseTwo ρ.rot a a.symm`. -/
def deleteEdge [Finite V] (a : G.Dart) : RotationSystem (G.deleteEdges {a.edge}) where
  rot := (deleteEdgeDartEquiv a).permCongr (eraseTwo ρ.rot a a.symm)
  fst_rot d := ρ.fst_bypass_bypass_rot a a.symm ((deleteEdgeDartEquiv a).symm d).1
  sameCycle_rot d d' h := by
    have := finite_dart (G := G)
    obtain ⟨z, rfl⟩ := (deleteEdgeDartEquiv a).surjective d
    obtain ⟨z', rfl⟩ := (deleteEdgeDartEquiv a).surjective d'
    rw [sameCycle_permCongr, sameCycle_eraseTwo_iff]
    exact ρ.sameCycle_rot z.1 z'.1 h

/-- At the reversal of a surviving dart `z`, the rotation with `a` and `a.symm` bypassed agrees
with the face permutation after the transposition of `a` and `a.symm`, with both bypassed. -/
theorem bypass_bypass_rot_symm (a z : G.Dart) (hza : z ≠ a) (hzb : z ≠ a.symm) :
    bypass (bypass ρ.rot a) a.symm z.symm =
      bypass (bypass (ρ.face * swap a a.symm) a) a.symm z := by
  have hba : a.symm ≠ a := a.symm_ne
  have hza' : z.symm ≠ a := fun h => hzb (by rw [← h, Dart.symm_symm])
  have hzb' : z.symm ≠ a.symm := fun h => hza (by rw [← Dart.symm_symm z, h, Dart.symm_symm])
  have hX : (ρ.face * swap a a.symm) z = ρ.rot z.symm := by
    rw [mul_swap_apply_of_ne _ hza hzb, face_apply]
  have hXa : (ρ.face * swap a a.symm) a = ρ.rot a := by
    rw [mul_apply, swap_apply_left, face_apply, Dart.symm_symm]
  have hXb : (ρ.face * swap a a.symm) a.symm = ρ.rot a.symm := by
    rw [mul_apply, swap_apply_right, face_apply]
  rw [bypass_apply_of_ne _ hzb', bypass_apply_of_ne _ hza', bypass_apply_of_ne _ hba,
    bypass_apply_of_ne _ hzb, bypass_apply_of_ne _ hza, bypass_apply_of_ne _ hba, hX, hXa, hXb]

/-- **The faces after deleting the edge of `a`**: the face permutation is
`eraseTwo (face * swap a a.symm) a a.symm`, the face permutation after the transposition of the
two darts, with both erased. -/
theorem deleteEdge_face [Finite V] (a : G.Dart) :
    (ρ.deleteEdge a).face =
      (deleteEdgeDartEquiv a).permCongr (eraseTwo (ρ.face * swap a a.symm) a a.symm) := by
  refine Equiv.ext fun d => ?_
  change deleteEdgeDartEquiv a (eraseTwo ρ.rot a a.symm ((deleteEdgeDartEquiv a).symm d.symm)) =
    deleteEdgeDartEquiv a
      (eraseTwo (ρ.face * swap a a.symm) a a.symm ((deleteEdgeDartEquiv a).symm d))
  congr 1
  exact Subtype.ext (ρ.bypass_bypass_rot_symm a _ ((deleteEdgeDartEquiv a).symm d).2.1
    ((deleteEdgeDartEquiv a).symm d).2.2)

/-- **The face count after deleting an edge**: the faces of `face * swap a a.symm`, less a face
for each end that loses its last dart. -/
theorem natCard_face_deleteEdge_add [Finite V] (a : G.Dart) :
    Nat.card (ρ.deleteEdge a).Face + (if ρ.rot a = a then 1 else 0) +
      (if ρ.rot a.symm = a.symm then 1 else 0) = cycleCount (ρ.face * swap a a.symm) := by
  have := finite_dart (G := G)
  have h := cycleCount_eraseTwo_add (ρ.face * swap a a.symm) (Ne.symm a.symm_ne)
  have hXa : (ρ.face * swap a a.symm) a = ρ.rot a := by
    rw [mul_apply, swap_apply_left, face_apply, Dart.symm_symm]
  have hXb' : (ρ.face * swap a a.symm) a.symm = ρ.rot a.symm := by
    rw [mul_apply, swap_apply_right, face_apply]
  have hXb : bypass (ρ.face * swap a a.symm) a a.symm = ρ.rot a.symm := by
    rw [bypass_apply_of_ne _ a.symm_ne, hXb', ite_eq_right (ρ.rot_symm_ne a)]
  rw [hXa, hXb] at h
  change cycleCount (ρ.deleteEdge a).face + _ + _ = _
  rw [deleteEdge_face, cycleCount_permCongr]
  exact h

omit [DecidableEq V] in
/-- **The tail of `a` becomes isolated** when its edge is deleted exactly when `a` is the only dart
at its tail, that is, when the rotation fixes `a`. -/
theorem fst_mem_isolatedVerts_deleteEdges_iff (a : G.Dart) :
    a.fst ∈ isolatedVerts (G.deleteEdges {a.edge}) ↔ ρ.rot a = a := by
  rw [ρ.rot_eq_self_iff]
  simp only [isolatedVerts, Set.mem_ofPred_eq, deleteEdges_adj, Set.mem_singleton_iff, not_and,
    not_not]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  change s(a.fst, w) = s(a.fst, a.snd) ↔ w = a.snd
  exact Sym2.congr_right

omit [DecidableEq V] in
/-- **The isolated vertices after deleting an edge**: those of `G`, and the ends that lose their
last dart. -/
theorem mem_isolatedVerts_deleteEdges_iff (a : G.Dart) (v : V) :
    v ∈ isolatedVerts (G.deleteEdges {a.edge}) ↔
      v ∈ isolatedVerts G ∨ (v = a.fst ∧ ρ.rot a = a) ∨ (v = a.snd ∧ ρ.rot a.symm = a.symm) := by
  by_cases hx : v = a.fst
  · subst hx
    have hnot : a.fst ∉ isolatedVerts G := fun h => h a.snd a.adj
    rw [ρ.fst_mem_isolatedVerts_deleteEdges_iff]
    simp [hnot, a.adj.ne]
  by_cases hy : v = a.snd
  · subst hy
    have hnot : a.snd ∉ isolatedVerts G := fun h => h a.fst a.adj.symm
    have h := ρ.fst_mem_isolatedVerts_deleteEdges_iff a.symm
    rw [Dart.edge_symm] at h
    change a.snd ∈ _ ↔ _ at h
    rw [h]
    simp [hnot, hx]
  · have hadj : ∀ w, (G.deleteEdges {a.edge}).Adj v w ↔ G.Adj v w := fun w => by
      rw [deleteEdges_adj, Set.mem_singleton_iff]
      refine ⟨And.left, fun h => ⟨h, fun he => ?_⟩⟩
      have hv : v ∈ s(a.fst, a.snd) := (show s(v, w) = s(a.fst, a.snd) from he) ▸
        Sym2.mem_mk_left v w
      rcases Sym2.mem_iff.mp hv with h | h
      exacts [hx h, hy h]
    simp only [isolatedVerts, Set.mem_ofPred_eq, hadj, hx, hy, false_and, or_false]

/-- **The number of isolated vertices after deleting an edge.** -/
theorem ncard_isolatedVerts_deleteEdges [Finite V] (a : G.Dart) :
    (isolatedVerts (G.deleteEdges {a.edge})).ncard = (isolatedVerts G).ncard +
      (if ρ.rot a = a then 1 else 0) + (if ρ.rot a.symm = a.symm then 1 else 0) := by
  have hset : isolatedVerts (G.deleteEdges {a.edge}) = isolatedVerts G ∪
      ({v | v = a.fst ∧ ρ.rot a = a} ∪ {v | v = a.snd ∧ ρ.rot a.symm = a.symm}) := by
    ext v
    rw [ρ.mem_isolatedVerts_deleteEdges_iff]
    rfl
  have hdisj1 : Disjoint (isolatedVerts G)
      ({v | v = a.fst ∧ ρ.rot a = a} ∪ {v | v = a.snd ∧ ρ.rot a.symm = a.symm}) := by
    rw [Set.disjoint_left]
    rintro v hv (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact hv a.snd a.adj
    · exact hv a.fst a.adj.symm
  have hdisj2 : Disjoint {v | v = a.fst ∧ ρ.rot a = a}
      {v | v = a.snd ∧ ρ.rot a.symm = a.symm} := by
    rw [Set.disjoint_left]
    rintro v ⟨rfl, -⟩ ⟨h, -⟩
    exact a.adj.ne h
  have h1 : {v | v = a.fst ∧ ρ.rot a = a}.ncard = if ρ.rot a = a then 1 else 0 := by
    split_ifs with h <;> simp [h]
  have h2 : {v | v = a.snd ∧ ρ.rot a.symm = a.symm}.ncard =
      if ρ.rot a.symm = a.symm then 1 else 0 := by
    split_ifs with h <;> simp [h]
  rw [hset, Set.ncard_union_eq hdisj1, Set.ncard_union_eq hdisj2, h1, h2, add_assoc]

/-- **The completed face count after deleting an edge** is the cycle count of
`face * swap a a.symm` plus the isolated vertices of `G`: an end that becomes isolated loses a
face and gains its extra face. -/
theorem completedFaceCount_deleteEdge [Finite V] (a : G.Dart) :
    (ρ.deleteEdge a).completedFaceCount =
      cycleCount (ρ.face * swap a a.symm) + (isolatedVerts G).ncard := by
  have h1 := ρ.natCard_face_deleteEdge_add a
  have h2 := ρ.ncard_isolatedVerts_deleteEdges a
  unfold completedFaceCount
  split_ifs at h1 h2 <;> omega

/-- **Deleting an edge whose two darts lie on one face** adds a completed face. -/
theorem completedFaceCount_deleteEdge_of_sameCycle [Finite V] {a : G.Dart}
    (h : ρ.face.SameCycle a a.symm) :
    (ρ.deleteEdge a).completedFaceCount = ρ.completedFaceCount + 1 := by
  have := finite_dart (G := G)
  rw [completedFaceCount_deleteEdge, cycleCount_mul_swap_of_sameCycle (Ne.symm a.symm_ne) h]
  unfold completedFaceCount
  change cycleCount ρ.face + 1 + _ = cycleCount ρ.face + _ + 1
  omega

/-- **Deleting an edge whose two darts lie on two faces** joins them into one. -/
theorem completedFaceCount_deleteEdge_of_not_sameCycle [Finite V] {a : G.Dart}
    (h : ¬ ρ.face.SameCycle a a.symm) :
    (ρ.deleteEdge a).completedFaceCount + 1 = ρ.completedFaceCount := by
  have := finite_dart (G := G)
  have h' := cycleCount_mul_swap_of_not_sameCycle h
  rw [completedFaceCount_deleteEdge]
  unfold completedFaceCount
  change _ = cycleCount ρ.face + _
  omega

end RotationSystem

/-! ## Components after deleting an edge -/

/-- **Reachability before and after deleting an edge**: `G` joins the classes of the two ends of
the edge. -/
theorem reachable_iff_deleteEdges (a : G.Dart) (u w : V) :
    G.Reachable u w ↔ (G.deleteEdges {a.edge}).Reachable u w ∨
      (((G.deleteEdges {a.edge}).Reachable u a.fst ∨
          (G.deleteEdges {a.edge}).Reachable u a.snd) ∧
        ((G.deleteEdges {a.edge}).Reachable w a.fst ∨
          (G.deleteEdges {a.edge}).Reachable w a.snd)) := by
  set H := G.deleteEdges {a.edge}
  have hend : ∀ z, z ∈ s(a.fst, a.snd) → H.Reachable z a.fst ∨ H.Reachable z a.snd := by
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    exacts [Or.inl .rfl, Or.inr .rfl]
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Or.inl Reachable.rfl
    | @cons u v w huv p ih =>
      by_cases he : s(u, v) = a.edge
      · have he' : s(u, v) = s(a.fst, a.snd) := he
        have hu := hend u (he' ▸ Sym2.mem_mk_left u v)
        have hv := hend v (he' ▸ Sym2.mem_mk_right u v)
        refine Or.inr ⟨hu, ?_⟩
        rcases ih with h | ⟨_, h⟩
        · exact hv.imp (fun h' => h.symm.trans h') fun h' => h.symm.trans h'
        · exact h
      · have hH : H.Adj u v := deleteEdges_adj.mpr ⟨huv, he⟩
        rcases ih with h | ⟨hv, hw⟩
        · exact Or.inl (hH.reachable.trans h)
        · exact Or.inr ⟨hv.imp hH.reachable.trans hH.reachable.trans, hw⟩
  · have hle : H ≤ G := deleteEdges_le _
    have hxy : G.Reachable a.fst a.snd := a.adj.reachable
    have hto : ∀ z, (H.Reachable z a.fst ∨ H.Reachable z a.snd) → G.Reachable z a.fst :=
      fun z hz => hz.elim (fun h => h.mono hle) fun h => (h.mono hle).trans hxy.symm
    rintro (h | ⟨hu, hw⟩)
    · exact h.mono hle
    · exact (hto u hu).trans (hto w hw).symm

/-- **Deleting a bridge** adds a component. -/
theorem natCard_connectedComponent_deleteEdges_of_isBridge [Finite V] {a : G.Dart}
    (h : G.IsBridge a.edge) :
    Nat.card (G.deleteEdges {a.edge}).ConnectedComponent = Nat.card G.ConnectedComponent + 1 :=
  natCard_quotient_eq_add_one_of_join (R := (G.deleteEdges {a.edge}).reachableSetoid)
    (R' := G.reachableSetoid) (reachable_iff_deleteEdges a) h

/-- **Deleting an edge that is not a bridge** keeps the components. -/
theorem natCard_connectedComponent_deleteEdges_of_not_isBridge {a : G.Dart}
    (h : ¬ G.IsBridge a.edge) :
    Nat.card (G.deleteEdges {a.edge}).ConnectedComponent = Nat.card G.ConnectedComponent :=
  natCard_quotient_eq_of_join (R := (G.deleteEdges {a.edge}).reachableSetoid)
    (R' := G.reachableSetoid) (reachable_iff_deleteEdges a) (not_not.mp h)

/-- **Deleting an edge** removes it from the edge set. -/
theorem ncard_edgeSet_deleteEdges_add_one [Finite V] (a : G.Dart) :
    (G.deleteEdges {a.edge}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one a.edge_mem

namespace RotationSystem

variable (ρ : RotationSystem G)

/-- **The two darts of a bridge lie on one face**: otherwise the face of `a` would return from the
head of `a` to its tail along darts of other edges, joining the two ends without the bridge. -/
theorem sameCycle_face_of_isBridge [Finite V] {a : G.Dart} (h : G.IsBridge a.edge) :
    ρ.face.SameCycle a a.symm := by
  have := finite_dart (G := G)
  by_contra hne
  set H := G.deleteEdges {a.edge}
  obtain ⟨m, hm0, hmS, hmin⟩ := exists_first_pow_mem ρ.face (S := {a, a.symm}) (x := a)
    (let ⟨n, hn, h⟩ := exists_pos_pow_apply_eq_self ρ.face a; ⟨n, hn, Or.inl h⟩)
  have hma : (ρ.face ^ m) a = a := by
    rcases hmS with h' | h'
    · exact h'
    · exact (hne ⟨m, by rw [zpow_natCast]; exact h'⟩).elim
  -- The face of `a` walks from the head of `a` back to its tail without the edge of `a`.
  have key : ∀ i, 0 < i → i ≤ m → H.Reachable a.snd ((ρ.face ^ i) a).fst := by
    intro i hi him
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi'
      · rw [zero_add, pow_one, fst_face]
      · have hS := hmin i hi' (by omega)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hS
        have hadj : H.Adj ((ρ.face ^ i) a).fst ((ρ.face ^ i) a).snd :=
          deleteEdges_adj.mpr ⟨((ρ.face ^ i) a).adj, (dart_edge_ne_iff _ a).mpr hS⟩
        rw [pow_succ', mul_apply, fst_face]
        exact (ih hi' (by omega)).trans hadj.reachable
  have hr := key m hm0 le_rfl
  rw [hma] at hr
  exact h hr.symm

/-! ## The Euler defect after deleting an edge -/

variable [DecidableEq V]

/-- **Deleting a bridge keeps the defect**: one component more, one edge fewer, one completed face
more. -/
theorem eulerDefect_deleteEdge_of_isBridge [Finite V] {a : G.Dart} (h : G.IsBridge a.edge) :
    (ρ.deleteEdge a).eulerDefect = ρ.eulerDefect := by
  have hC := natCard_connectedComponent_deleteEdges_of_isBridge h
  have hE := ncard_edgeSet_deleteEdges_add_one (G := G) a
  have hF := ρ.completedFaceCount_deleteEdge_of_sameCycle (ρ.sameCycle_face_of_isBridge h)
  unfold eulerDefect
  rw [hC, hF, ← hE]
  push_cast
  ring

/-- **Deleting an edge whose darts lie on two faces keeps the defect**: it is not a bridge, and
the two faces become one. -/
theorem eulerDefect_deleteEdge_of_not_sameCycle [Finite V] {a : G.Dart}
    (h : ¬ ρ.face.SameCycle a a.symm) : (ρ.deleteEdge a).eulerDefect = ρ.eulerDefect := by
  have hb : ¬ G.IsBridge a.edge := fun hb => h (ρ.sameCycle_face_of_isBridge hb)
  have hC := natCard_connectedComponent_deleteEdges_of_not_isBridge hb
  have hE := ncard_edgeSet_deleteEdges_add_one (G := G) a
  have hF := ρ.completedFaceCount_deleteEdge_of_not_sameCycle h
  unfold eulerDefect
  rw [hC, ← hE, ← hF]
  push_cast
  ring

/-- **Deleting a non-bridge whose darts lie on one face lowers the defect by two**: the face
splits in two, with the components unchanged. -/
theorem eulerDefect_deleteEdge_of_sameCycle [Finite V] {a : G.Dart} (hb : ¬ G.IsBridge a.edge)
    (h : ρ.face.SameCycle a a.symm) : (ρ.deleteEdge a).eulerDefect = ρ.eulerDefect - 2 := by
  have hC := natCard_connectedComponent_deleteEdges_of_not_isBridge hb
  have hE := ncard_edgeSet_deleteEdges_add_one (G := G) a
  have hF := ρ.completedFaceCount_deleteEdge_of_sameCycle h
  unfold eulerDefect
  rw [hC, ← hE, hF]
  push_cast
  ring

/-- **Deleting an edge never raises the Euler defect.** -/
theorem eulerDefect_deleteEdge_le [Finite V] (a : G.Dart) :
    (ρ.deleteEdge a).eulerDefect ≤ ρ.eulerDefect := by
  by_cases h : ρ.face.SameCycle a a.symm
  · by_cases hb : G.IsBridge a.edge
    · exact (ρ.eulerDefect_deleteEdge_of_isBridge hb).le
    · rw [ρ.eulerDefect_deleteEdge_of_sameCycle hb h]
      linarith
  · exact (ρ.eulerDefect_deleteEdge_of_not_sameCycle h).le

omit [DecidableEq V] in
/-- **Without edges the defect is zero**: every vertex is an isolated component, with its extra
face, and there are no faces. -/
theorem eulerDefect_eq_zero_of_edgeSet_eq_empty [Finite V] (h : G.edgeSet = ∅) :
    ρ.eulerDefect = 0 := by
  have hadj : ∀ u w, ¬ G.Adj u w := fun u w huw => by
    have : s(u, w) ∈ G.edgeSet := huw
    rw [h] at this
    exact this
  have hC : Nat.card G.ConnectedComponent = Nat.card V := by
    refine (Nat.card_eq_of_bijective G.connectedComponentMk ⟨fun u w huw => ?_, fun c =>
      c.exists_rep⟩).symm
    obtain ⟨p⟩ := ConnectedComponent.eq.mp huw
    cases p with
    | nil => rfl
    | cons h' _ => exact absurd h' (hadj _ _)
  have hF : Nat.card ρ.Face = 0 := by
    have : IsEmpty ρ.Face := ⟨fun q => Quotient.inductionOn q fun d => (hadj _ _ d.adj).elim⟩
    exact Nat.card_of_isEmpty
  have hI : (isolatedVerts G).ncard = Nat.card V := by
    rw [show isolatedVerts G = Set.univ from Set.eq_univ_of_forall fun v w => hadj v w,
      Set.ncard_univ]
  unfold eulerDefect completedFaceCount
  rw [hC, hF, hI, h, Set.ncard_empty]
  push_cast
  ring

omit [DecidableEq V] in
/-- **Euler's inequality for every rotation system**: `0 ≤ 2C − V + E − F̂`, for every graph on a
finite vertex type.  By induction on the edges: deleting an edge never raises the defect, and the
edgeless graph has defect zero. -/
theorem eulerDefect_nonneg [Finite V] : 0 ≤ ρ.eulerDefect := by
  classical
  suffices h : ∀ n (G : SimpleGraph V) (ρ : RotationSystem G), G.edgeSet.ncard = n →
      0 ≤ ρ.eulerDefect from h _ G ρ rfl
  intro n
  induction n with
  | zero =>
    intro G ρ hn
    rw [ρ.eulerDefect_eq_zero_of_edgeSet_eq_empty ((Set.ncard_eq_zero (Set.toFinite _)).mp hn)]
  | succ n ih =>
    intro G ρ hn
    obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (s := G.edgeSet) (by omega)
    induction e using Sym2.ind with
    | h x y =>
    let a : G.Dart := ⟨(x, y), G.mem_edgeSet.mp he⟩
    have hE := ncard_edgeSet_deleteEdges_add_one (G := G) a
    exact (ih _ (ρ.deleteEdge a) (by omega)).trans (ρ.eulerDefect_deleteEdge_le a)

end RotationSystem

end MonoidProduct.Graph
