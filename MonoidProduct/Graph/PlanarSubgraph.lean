import Mathlib.Combinatorics.SimpleGraph.Acyclic
import MonoidProduct.Graph.RotationDeletion
set_option linter.style.header false

/-!
# Planarity is closed under subgraphs

From Euler's inequality `0 ≤ Δ` for every rotation system (`Graph/RotationDeletion.lean`) to the
componentwise definition of planarity, and then to subgraphs and induced subgraphs.

* `RotationSystem.componentDefect ρ c = 2 − V_c + E_c − F̂_c`, with `F̂_c` the faces in `c` and
  one more if `c` is an isolated vertex; the Euler defect is the sum of the component defects
  (`eulerDefect_eq_finsum`).
* `RotationSystem.restrict ρ s hs`: the restriction of a rotation system to the graph induced on a
  set `s` that no edge leaves.  Its components are components of `G`, with the same vertices,
  edges and faces (`componentDefect_restrict`).
* `componentDefect_nonneg`: `V_c + F_c ≤ E_c + 2` for every component with an edge, by Euler's
  inequality for the restriction to the component, which is connected.  Hence
  `isSpherical_iff_eulerDefect_eq_zero`: a rotation system is spherical exactly when its total
  defect is zero; the nonnegative summands justify this.
* `RotationSystem.IsSpherical.deleteEdge`: `0 ≤ Δ(ρ.deleteEdge a) ≤ Δ(ρ) = 0`, so deleting an edge
  keeps a spherical rotation system spherical.  In a spherical rotation system the two darts of an
  edge lie on one face exactly when the edge is a bridge (`IsSpherical.sameCycle_face_iff`).
* `IsPlanar.mono`, `IsPlanar.deleteEdges`: **planarity is closed under subgraphs** on the same
  vertex type, by deleting the missing edges one at a time.
* `IsPlanar.induce`: **planarity is closed under induced subgraphs**: delete the edges leaving
  `s`, then restrict to `s`.
* `RotationSystem.IsSpherical.of_isAcyclic`: every rotation system of a forest is spherical, since
  each edge is a bridge.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*} {G : SimpleGraph V}

/-! ## Counting by components -/

/-- **Counting by fibres**: the sizes of the fibres of `f` in `s` add up to the size of `s`. -/
theorem sum_ncard_inter_preimage {α β : Type*} [Finite α] [Fintype β] (f : α → β) (s : Set α) :
    ∑ b, (s ∩ f ⁻¹' {b}).ncard = s.ncard := by
  classical
  have := Fintype.ofFinite α
  rw [Set.ncard_eq_toFinset_card' s, Finset.card_eq_sum_card_fiberwise (f := f)
    (t := Finset.univ) fun _ _ => Finset.mem_univ _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Set.ncard_coe_finset]
  congr 1
  ext
  simp

/-- An isolated vertex reaches only itself. -/
theorem eq_of_reachable_of_mem_isolatedVerts {v w : V} (hv : v ∈ isolatedVerts G)
    (h : G.Reachable v w) : v = w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons h' _ => exact absurd h' (hv _)

/-- A component with an edge has no isolated vertex. -/
theorem isolatedVerts_inter_supp_eq_empty {c : G.ConnectedComponent}
    (hc : (componentEdges G c).Nonempty) : isolatedVerts G ∩ c.supp = ∅ := by
  obtain ⟨e, he, hec⟩ := hc
  induction e using Sym2.ind with
  | h u u' =>
  refine Set.eq_empty_of_forall_notMem fun v ⟨hv, hvc⟩ => ?_
  have hu : G.connectedComponentMk u = G.connectedComponentMk v :=
    (hec u (Sym2.mem_mk_left u u')).trans ((ConnectedComponent.mem_supp_iff _ _).mp hvc).symm
  have := eq_of_reachable_of_mem_isolatedVerts hv (ConnectedComponent.eq.mp hu).symm
  subst this
  exact hv u' he

/-- A component without an edge is an isolated vertex. -/
theorem supp_subset_isolatedVerts {c : G.ConnectedComponent}
    (hc : ¬ (componentEdges G c).Nonempty) : c.supp ⊆ isolatedVerts G := fun v hv w hw => hc
  ⟨s(v, w), hw, fun z hz => by
    have hvc := (ConnectedComponent.mem_supp_iff _ _).mp hv
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hvc
    · exact (ConnectedComponent.eq.mpr hw.reachable.symm).trans hvc⟩

namespace RotationSystem

variable (ρ : RotationSystem G)

/-- A component without an edge has no face. -/
theorem facesIn_eq_empty {c : G.ConnectedComponent} (hc : ¬ (componentEdges G c).Nonempty) :
    ρ.facesIn c = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun f hf => ?_
  induction f using Quotient.inductionOn with
  | h d =>
  have hd : G.connectedComponentMk d.fst = c := hf
  refine hc ⟨d.edge, d.edge_mem, fun z hz => ?_⟩
  rcases Sym2.mem_iff.mp hz with rfl | rfl
  · exact hd
  · exact (ConnectedComponent.eq.mpr d.adj.reachable.symm).trans hd

/-! ## The defect of a component -/

/-- **The Euler defect of a component** `c`: `2 − V_c + E_c − F̂_c`, where `F̂_c` counts the faces
in `c`, and one more if `c` is an isolated vertex. -/
noncomputable def componentDefect (c : G.ConnectedComponent) : ℤ :=
  2 - c.supp.ncard + (componentEdges G c).ncard -
    ((ρ.facesIn c).ncard + (isolatedVerts G ∩ c.supp).ncard)

/-- The defect of a component with an edge is `2 − V_c + E_c − F_c`. -/
theorem componentDefect_of_nonempty {c : G.ConnectedComponent}
    (hc : (componentEdges G c).Nonempty) :
    ρ.componentDefect c = 2 - c.supp.ncard + (componentEdges G c).ncard - (ρ.facesIn c).ncard := by
  rw [componentDefect, isolatedVerts_inter_supp_eq_empty hc, Set.ncard_empty]
  push_cast
  ring

/-- An isolated vertex has defect `2 − 1 + 0 − (0 + 1) = 0`. -/
theorem componentDefect_of_not_nonempty [Finite V] {c : G.ConnectedComponent}
    (hc : ¬ (componentEdges G c).Nonempty) : ρ.componentDefect c = 0 := by
  have hV : c.supp.ncard = 1 := by
    have := one_le_ncard_supp c
    by_contra h
    exact hc (componentEdges_nonempty (by omega))
  have hE : (componentEdges G c).ncard = 0 := by
    rw [Set.not_nonempty_iff_eq_empty.mp hc, Set.ncard_empty]
  rw [componentDefect, ρ.facesIn_eq_empty hc, Set.inter_eq_right.mpr (supp_subset_isolatedVerts hc),
    hV, hE, Set.ncard_empty]
  norm_num

/-- **The Euler defect is the sum of the component defects.** -/
theorem eulerDefect_eq_finsum [Finite V] : ρ.eulerDefect = ∑ᶠ c, ρ.componentDefect c := by
  classical
  have := Fintype.ofFinite V
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have := finite_dart (G := G)
  have : Fintype ρ.Face := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  -- The vertices, faces and isolated vertices are counted by their components.
  have hV : ∑ c : G.ConnectedComponent, c.supp.ncard = Nat.card V := by
    rw [← Set.ncard_univ, ← sum_ncard_inter_preimage G.connectedComponentMk Set.univ]
    refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
    ext v
    simp [ConnectedComponent.mem_supp_iff]
  have hF : ∑ c : G.ConnectedComponent, (ρ.facesIn c).ncard = Nat.card ρ.Face := by
    rw [← Set.ncard_univ, ← sum_ncard_inter_preimage (fun f : ρ.Face => f.component) Set.univ]
    refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
    ext f
    simp [facesIn]
  have hI : ∑ c : G.ConnectedComponent, (isolatedVerts G ∩ c.supp).ncard =
      (isolatedVerts G).ncard := by
    rw [← sum_ncard_inter_preimage G.connectedComponentMk (isolatedVerts G)]
    refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
    ext v
    simp [ConnectedComponent.mem_supp_iff]
  -- The edges, through the darts: each edge of a component has two darts in it.
  have hE : ∑ c : G.ConnectedComponent, (componentEdges G c).ncard = G.edgeSet.ncard := by
    have hD : ∑ c : G.ConnectedComponent, (dartsIn G c).ncard = Nat.card G.Dart := by
      rw [← Set.ncard_univ, ← sum_ncard_inter_preimage
        (fun d : G.Dart => G.connectedComponentMk d.fst) Set.univ]
      refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
      ext d
      simp [dartsIn]
    simp only [ncard_dartsIn_eq, ← Finset.mul_sum] at hD
    rw [Nat.card_eq_fintype_card, dart_card_eq_twice_card_edges, ← coe_edgeFinset,
      Set.ncard_coe_finset] at *
    omega
  have hsum : ∑ c, ρ.componentDefect c =
      2 * (Fintype.card G.ConnectedComponent : ℤ) - (∑ c : G.ConnectedComponent, c.supp.ncard : ℕ) +
        (∑ c : G.ConnectedComponent, (componentEdges G c).ncard : ℕ) -
        ((∑ c : G.ConnectedComponent, (ρ.facesIn c).ncard : ℕ) +
          (∑ c : G.ConnectedComponent, (isolatedVerts G ∩ c.supp).ncard : ℕ)) := by
    simp only [componentDefect, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Nat.cast_sum, nsmul_eq_mul]
    ring
  rw [hsum, hV, hE, hF, hI, eulerDefect, completedFaceCount, ← Nat.card_eq_fintype_card]
  push_cast
  ring

/-- **Spherical means every component has defect zero.** -/
theorem isSpherical_iff_forall_componentDefect_eq_zero [Finite V] :
    ρ.IsSpherical ↔ ∀ c, ρ.componentDefect c = 0 := by
  refine ⟨fun h c => ?_, fun h c hc => ?_⟩
  · by_cases hc : (componentEdges G c).Nonempty
    · rw [ρ.componentDefect_of_nonempty hc]
      have := h c hc
      omega
    · exact ρ.componentDefect_of_not_nonempty hc
  · have := h c
    rw [ρ.componentDefect_of_nonempty hc] at this
    omega

end RotationSystem

/-! ## Restriction to a set that no edge leaves -/

section Restrict

variable {s : Set V}

/-- **Walks stay in a set that no edge leaves**, and give walks of the graph induced on it. -/
theorem exists_reachable_induce_of_walk_closed (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s) :
    ∀ {u w : V} (_ : G.Walk u w) (hu : u ∈ s), ∃ hw : w ∈ s,
      (G.induce s).Reachable ⟨u, hu⟩ ⟨w, hw⟩
  | _, _, .nil, hu => ⟨hu, .rfl⟩
  | _, _, .cons huv p, hu => by
    obtain ⟨hw, hr⟩ := exists_reachable_induce_of_walk_closed hs p (hs huv hu)
    exact ⟨hw, (show (G.induce s).Adj ⟨_, hu⟩ ⟨_, hs huv hu⟩ from huv).reachable.trans hr⟩

variable (G) in
/-- **The darts of the graph induced on `s`**, when no edge leaves `s`: the darts of `G` with
their tail in `s`. -/
def induceDartEquiv (s : Set V) (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s) :
    {d : G.Dart // d.fst ∈ s} ≃ (G.induce s).Dart where
  toFun d := ⟨(⟨d.1.fst, d.2⟩, ⟨d.1.snd, hs d.1.adj d.2⟩), d.1.adj⟩
  invFun d := ⟨⟨(d.fst.1, d.snd.1), d.adj⟩, d.fst.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The component of `G` containing a component of the graph induced on `s`. -/
abbrev induceComponentMap (s : Set V) :
    (G.induce s).ConnectedComponent → G.ConnectedComponent :=
  ConnectedComponent.map (Embedding.induce s).toHom

@[simp] theorem induceComponentMap_mk (v : s) :
    induceComponentMap s ((G.induce s).connectedComponentMk v) = G.connectedComponentMk v.1 :=
  rfl

/-- **A component of the induced graph has the vertices of its component of `G`**, when no edge
leaves `s`. -/
theorem supp_induceComponentMap (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s)
    (c' : (G.induce s).ConnectedComponent) :
    (induceComponentMap s c').supp = Subtype.val '' c'.supp := by
  induction c' using ConnectedComponent.ind with
  | h v =>
  ext u
  rw [ConnectedComponent.mem_supp_iff, induceComponentMap_mk]
  constructor
  · intro h
    obtain ⟨p⟩ := (ConnectedComponent.eq.mp h).symm
    obtain ⟨hu, hr⟩ := exists_reachable_induce_of_walk_closed hs p v.2
    exact ⟨⟨u, hu⟩, (ConnectedComponent.mem_supp_iff _ _).mpr (ConnectedComponent.eq.mpr hr.symm),
      rfl⟩
  · rintro ⟨u', hu', rfl⟩
    rw [ConnectedComponent.mem_supp_iff] at hu'
    exact ConnectedComponent.eq.mpr ((ConnectedComponent.eq.mp hu').map (Embedding.induce s).toHom)

/-- **A component of the induced graph has the edges of its component of `G`.** -/
theorem componentEdges_induceComponentMap (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s)
    (c' : (G.induce s).ConnectedComponent) :
    componentEdges G (induceComponentMap s c') =
      Sym2.map Subtype.val '' componentEdges (G.induce s) c' := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
  constructor
  · rintro ⟨hab, hc⟩
    have ha : a ∈ (induceComponentMap s c').supp :=
      (ConnectedComponent.mem_supp_iff _ _).mpr (hc a (Sym2.mem_mk_left a b))
    have hb : b ∈ (induceComponentMap s c').supp :=
      (ConnectedComponent.mem_supp_iff _ _).mpr (hc b (Sym2.mem_mk_right a b))
    rw [supp_induceComponentMap hs] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    refine ⟨s(a', b'), ⟨hab, fun z hz => ?_⟩, rfl⟩
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact (ConnectedComponent.mem_supp_iff _ _).mp ha'
    · exact (ConnectedComponent.mem_supp_iff _ _).mp hb'
  · rintro ⟨e', ⟨he', hc'⟩, hee⟩
    induction e' using Sym2.ind with
    | h a' b' =>
    rw [Sym2.map_mk] at hee
    rw [← hee]
    refine ⟨he', fun z hz => ?_⟩
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · rw [← hc' a' (Sym2.mem_mk_left _ _), induceComponentMap_mk]
    · rw [← hc' b' (Sym2.mem_mk_right _ _), induceComponentMap_mk]

namespace RotationSystem

variable (ρ : RotationSystem G)

/-- **The restriction of a rotation system** to the graph induced on a set `s` that no edge
leaves: the rotation of the darts with their tail in `s`. -/
def restrict (s : Set V) (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s) :
    RotationSystem (G.induce s) where
  rot := (induceDartEquiv G s hs).permCongr (ρ.rot.subtypePerm fun d => by rw [ρ.fst_rot])
  fst_rot d := Subtype.ext (ρ.fst_rot ((induceDartEquiv G s hs).symm d).1)
  sameCycle_rot d d' h := by
    obtain ⟨z, rfl⟩ := (induceDartEquiv G s hs).surjective d
    obtain ⟨z', rfl⟩ := (induceDartEquiv G s hs).surjective d'
    rw [sameCycle_permCongr, sameCycle_subtypePerm]
    exact ρ.sameCycle_rot z.1 z'.1 (congrArg Subtype.val h)

variable {ρ}

/-- A face of `G` stays in a set that no edge leaves. -/
theorem fst_face_mem_iff (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s) (d : G.Dart) :
    (ρ.face d).fst ∈ s ↔ d.fst ∈ s := by
  rw [fst_face]
  exact ⟨hs d.adj.symm, hs d.adj⟩

/-- **The faces of the restriction** are the faces of `ρ` through darts with their tail in `s`. -/
theorem restrict_face (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s) :
    (ρ.restrict s hs).face =
      (induceDartEquiv G s hs).permCongr (ρ.face.subtypePerm (fst_face_mem_iff hs)) := by
  refine Equiv.ext fun d => ?_
  change induceDartEquiv G s hs (ρ.rot.subtypePerm (fun d => by rw [ρ.fst_rot])
      ((induceDartEquiv G s hs).symm d.symm)) =
    induceDartEquiv G s hs (ρ.face.subtypePerm (fst_face_mem_iff hs)
      ((induceDartEquiv G s hs).symm d))
  rfl

theorem sameCycle_restrict_face_iff (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s)
    (z z' : {d : G.Dart // d.fst ∈ s}) :
    (ρ.restrict s hs).face.SameCycle (induceDartEquiv G s hs z) (induceDartEquiv G s hs z') ↔
      ρ.face.SameCycle z.1 z'.1 := by
  rw [restrict_face, sameCycle_permCongr, sameCycle_subtypePerm]

/-- The faces of the restriction, as faces of `ρ`. -/
def restrictFaceMap (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s) :
    (ρ.restrict s hs).Face → ρ.Face :=
  Quotient.map (fun d => ((induceDartEquiv G s hs).symm d).1) fun d d' h => by
    obtain ⟨z, rfl⟩ := (induceDartEquiv G s hs).surjective d
    obtain ⟨z', rfl⟩ := (induceDartEquiv G s hs).surjective d'
    exact (sameCycle_restrict_face_iff hs z z').mp h

theorem restrictFaceMap_injective (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s) :
    Function.Injective (restrictFaceMap (ρ := ρ) hs) := by
  intro f f' hff
  induction f using Quotient.inductionOn with
  | h d =>
  induction f' using Quotient.inductionOn with
  | h d' =>
  obtain ⟨z, rfl⟩ := (induceDartEquiv G s hs).surjective d
  obtain ⟨z', rfl⟩ := (induceDartEquiv G s hs).surjective d'
  exact Quotient.sound ((sameCycle_restrict_face_iff hs z z').mpr (Quotient.exact hff))

/-- **A component of the induced graph has the faces of its component of `G`.** -/
theorem facesIn_induceComponentMap (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s)
    (c' : (G.induce s).ConnectedComponent) :
    ρ.facesIn (induceComponentMap s c') =
      restrictFaceMap hs '' (ρ.restrict s hs).facesIn c' := by
  ext f
  induction f using Quotient.inductionOn with
  | h d =>
  constructor
  · intro hf
    have hd : d.fst ∈ (induceComponentMap s c').supp := (ConnectedComponent.mem_supp_iff _ _).mpr hf
    rw [supp_induceComponentMap hs] at hd
    obtain ⟨u, hu, hud⟩ := hd
    have hds : d.fst ∈ s := hud ▸ u.2
    refine ⟨⟦induceDartEquiv G s hs ⟨d, hds⟩⟧, ?_, rfl⟩
    change (G.induce s).connectedComponentMk ⟨d.fst, hds⟩ = c'
    rw [show (⟨d.fst, hds⟩ : s) = u from Subtype.ext hud.symm]
    exact (ConnectedComponent.mem_supp_iff _ _).mp hu
  · rintro ⟨f', hf', hff⟩
    induction f' using Quotient.inductionOn with
    | h d' =>
    have hd : ρ.face.SameCycle ((induceDartEquiv G s hs).symm d').1 d := Quotient.exact hff
    change G.connectedComponentMk d.fst = induceComponentMap s c'
    rw [← eq_of_sameCycle_of_forall (g := fun d : G.Dart => G.connectedComponentMk d.fst)
      ρ.connectedComponentMk_fst_face hd,
      ← (show (G.induce s).connectedComponentMk d'.fst = c' from hf'), induceComponentMap_mk]
    rfl

/-- **The components of the restriction have the defects of their components of `G`.** -/
theorem componentDefect_restrict [Finite V] (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s)
    (c' : (G.induce s).ConnectedComponent) :
    (ρ.restrict s hs).componentDefect c' = ρ.componentDefect (induceComponentMap s c') := by
  have hV : (induceComponentMap s c').supp.ncard = c'.supp.ncard := by
    rw [supp_induceComponentMap hs, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hE : (componentEdges G (induceComponentMap s c')).ncard =
      (componentEdges (G.induce s) c').ncard := by
    rw [componentEdges_induceComponentMap hs,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  have hF : (ρ.facesIn (induceComponentMap s c')).ncard = ((ρ.restrict s hs).facesIn c').ncard := by
    rw [facesIn_induceComponentMap hs,
      Set.ncard_image_of_injective _ (restrictFaceMap_injective hs)]
  have hne : (componentEdges G (induceComponentMap s c')).Nonempty ↔
      (componentEdges (G.induce s) c').Nonempty := by
    rw [componentEdges_induceComponentMap hs, Set.image_nonempty]
  by_cases hc : (componentEdges (G.induce s) c').Nonempty
  · rw [componentDefect_of_nonempty _ hc, componentDefect_of_nonempty _ (hne.mpr hc), hV, hE, hF]
  · rw [componentDefect_of_not_nonempty _ hc,
      componentDefect_of_not_nonempty _ (fun h => hc (hne.mp h))]

/-- **Restricting a spherical rotation system** to a set that no edge leaves keeps it
spherical. -/
theorem IsSpherical.restrict [Finite V] (hρ : ρ.IsSpherical)
    (hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s) : (ρ.restrict s hs).IsSpherical := by
  rw [isSpherical_iff_forall_componentDefect_eq_zero] at hρ ⊢
  intro c'
  rw [componentDefect_restrict hs]
  exact hρ _

end RotationSystem

end Restrict

/-! ## Euler's inequality for each component -/

namespace RotationSystem

variable (ρ : RotationSystem G)

/-- **Euler's inequality for a component**: `0 ≤ 2 − V_c + E_c − F̂_c`, that is,
`V_c + F_c ≤ E_c + 2` for a component with an edge.  The component induces a connected graph,
whose Euler defect is nonnegative. -/
theorem componentDefect_nonneg [Finite V] (c : G.ConnectedComponent) :
    0 ≤ ρ.componentDefect c := by
  induction c using ConnectedComponent.ind with
  | h v =>
  set s := (G.connectedComponentMk v).supp
  have hs : ∀ ⦃u w⦄, G.Adj u w → u ∈ s → w ∈ s := fun u w h hu =>
    (ConnectedComponent.mem_supp_iff _ _).mpr ((ConnectedComponent.eq.mpr h.reachable).symm.trans
      ((ConnectedComponent.mem_supp_iff _ _).mp hu))
  have hv : v ∈ s := (ConnectedComponent.mem_supp_iff _ _).mpr rfl
  -- The induced graph is connected: all its components are that of `v`.
  have hall : ∀ c' : (G.induce s).ConnectedComponent,
      c' = (G.induce s).connectedComponentMk ⟨v, hv⟩ := by
    intro c'
    induction c' using ConnectedComponent.ind with
    | h u =>
    obtain ⟨p⟩ := ConnectedComponent.eq.mp ((ConnectedComponent.mem_supp_iff _ _).mp u.2).symm
    obtain ⟨hu, hr⟩ := exists_reachable_induce_of_walk_closed hs p hv
    exact ConnectedComponent.eq.mpr hr.symm
  have h0 := (ρ.restrict s hs).eulerDefect_nonneg
  rw [eulerDefect_eq_finsum, finsum_eq_single _ ((G.induce s).connectedComponentMk ⟨v, hv⟩)
    fun c' hc' => absurd (hall c') hc', componentDefect_restrict hs, induceComponentMap_mk] at h0
  exact h0

/-- **Euler's inequality** `V_c + F_c ≤ E_c + 2` in every component with an edge, for every
rotation system: no embedding has negative genus. -/
theorem ncard_supp_add_ncard_facesIn_le [Finite V] {c : G.ConnectedComponent}
    (hc : (componentEdges G c).Nonempty) :
    c.supp.ncard + (ρ.facesIn c).ncard ≤ (componentEdges G c).ncard + 2 := by
  have h := ρ.componentDefect_nonneg c
  rw [ρ.componentDefect_of_nonempty hc] at h
  omega

/-- **Spherical means total defect zero**: a rotation system satisfies Euler's formula in every
component with an edge exactly when `2C − V + E − F̂ = 0`.  The component defects are
nonnegative, so they vanish when their sum does. -/
theorem isSpherical_iff_eulerDefect_eq_zero [Finite V] :
    ρ.IsSpherical ↔ ρ.eulerDefect = 0 := by
  classical
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [isSpherical_iff_forall_componentDefect_eq_zero, eulerDefect_eq_finsum,
    finsum_eq_sum_of_fintype,
    Finset.sum_eq_zero_iff_of_nonneg fun c _ => ρ.componentDefect_nonneg c]
  simp

/-! ## Deleting an edge of a spherical rotation system -/

variable {ρ}

/-- **Deleting an edge keeps a spherical rotation system spherical**: `0 ≤ Δ(ρ.deleteEdge a) ≤
Δ(ρ) = 0`. -/
theorem IsSpherical.deleteEdge [Finite V] [DecidableEq V] (hρ : ρ.IsSpherical) (a : G.Dart) :
    (ρ.deleteEdge a).IsSpherical := by
  rw [isSpherical_iff_eulerDefect_eq_zero] at hρ ⊢
  exact le_antisymm ((ρ.eulerDefect_deleteEdge_le a).trans hρ.le)
    (ρ.deleteEdge a).eulerDefect_nonneg

/-- **In a spherical rotation system the two darts of an edge lie on one face exactly when the
edge is a bridge**: deleting a non-bridge whose darts lie on one face would make the defect
negative. -/
theorem IsSpherical.sameCycle_face_iff [Finite V] (hρ : ρ.IsSpherical) (a : G.Dart) :
    ρ.face.SameCycle a a.symm ↔ G.IsBridge a.edge := by
  classical
  refine ⟨fun h => ?_, ρ.sameCycle_face_of_isBridge⟩
  by_contra hb
  have h1 := ρ.eulerDefect_deleteEdge_of_sameCycle hb h
  have h2 := (ρ.deleteEdge a).eulerDefect_nonneg
  rw [(isSpherical_iff_eulerDefect_eq_zero ρ).mp hρ] at h1
  omega

/-- **Forests**: the defect of every rotation system of an acyclic graph is zero, since each edge
is a bridge. -/
theorem eulerDefect_eq_zero_of_isAcyclic [Finite V] (ρ : RotationSystem G) (h : G.IsAcyclic) :
    ρ.eulerDefect = 0 := by
  classical
  suffices H : ∀ n (G : SimpleGraph V) (ρ : RotationSystem G), G.IsAcyclic →
      G.edgeSet.ncard = n → ρ.eulerDefect = 0 from H _ G ρ h rfl
  intro n
  induction n with
  | zero =>
    intro G ρ _ hn
    exact ρ.eulerDefect_eq_zero_of_edgeSet_eq_empty ((Set.ncard_eq_zero (Set.toFinite _)).mp hn)
  | succ n ih =>
    intro G ρ hG hn
    obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (s := G.edgeSet) (by omega)
    induction e using Sym2.ind with
    | h x y =>
    let a : G.Dart := ⟨(x, y), G.mem_edgeSet.mp he⟩
    have hE := ncard_edgeSet_deleteEdges_add_one (G := G) a
    rw [← ρ.eulerDefect_deleteEdge_of_isBridge (a := a)
      (isAcyclic_iff_forall_adj_isBridge.mp hG (G.mem_edgeSet.mp he))]
    exact ih _ (ρ.deleteEdge a) (hG.anti (deleteEdges_le _)) (by omega)

/-- **Every rotation system of a forest is spherical.** -/
theorem IsSpherical.of_isAcyclic [Finite V] (ρ : RotationSystem G) (h : G.IsAcyclic) :
    ρ.IsSpherical :=
  (isSpherical_iff_eulerDefect_eq_zero ρ).mpr (ρ.eulerDefect_eq_zero_of_isAcyclic h)

end RotationSystem

/-! ## Subgraphs and induced subgraphs -/

/-- **Deleting one edge keeps planarity.** -/
theorem IsPlanar.deleteEdges_singleton [Finite V] (hG : IsPlanar G) (e : Sym2 V) :
    IsPlanar (G.deleteEdges {e}) := by
  classical
  by_cases he : e ∈ G.edgeSet
  · induction e using Sym2.ind with
    | h x y =>
    obtain ⟨ρ, hρ⟩ := hG
    let a : G.Dart := ⟨(x, y), G.mem_edgeSet.mp he⟩
    exact ⟨ρ.deleteEdge a, hρ.deleteEdge a⟩
  · rwa [deleteEdges_eq_self.mpr (Set.disjoint_singleton_right.mpr he)]

/-- **Planarity is closed under subgraphs**: a subgraph, on the same vertex set, of a planar graph
is planar.  The missing edges are deleted one at a time. -/
theorem IsPlanar.mono [Finite V] {H G : SimpleGraph V} (hG : IsPlanar G) (hHG : H ≤ G) :
    IsPlanar H := by
  suffices h : ∀ n (G : SimpleGraph V), IsPlanar G → H ≤ G → (G.edgeSet \ H.edgeSet).ncard = n →
      IsPlanar H from h _ G hG hHG rfl
  intro n
  induction n with
  | zero =>
    intro G hG hHG hn
    have hsub : G.edgeSet ⊆ H.edgeSet :=
      Set.sdiff_eq_empty.mp ((Set.ncard_eq_zero (Set.toFinite _)).mp hn)
    have : H = G := le_antisymm hHG fun u w h => H.mem_edgeSet.mp (hsub (G.mem_edgeSet.mpr h))
    rwa [this]
  | succ n ih =>
    intro G hG hHG hn
    obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (s := G.edgeSet \ H.edgeSet) (by omega)
    refine ih (G.deleteEdges {e}) (hG.deleteEdges_singleton e) (fun u w h => ?_) ?_
    · rw [deleteEdges_adj, Set.mem_singleton_iff]
      exact ⟨hHG h, fun h' => he.2 (h' ▸ (H.mem_edgeSet.mpr h))⟩
    · rw [edgeSet_deleteEdges, sdiff_right_comm]
      have := Set.ncard_sdiff_singleton_add_one he (Set.toFinite _)
      omega

/-- **Deleting any edges keeps planarity.** -/
theorem IsPlanar.deleteEdges [Finite V] (hG : IsPlanar G) (s : Set (Sym2 V)) :
    IsPlanar (G.deleteEdges s) :=
  hG.mono (deleteEdges_le s)

/-- **Planarity is closed under induced subgraphs**: delete the edges leaving `s`, which keeps
planarity, and restrict to `s`, which no edge leaves any more. -/
theorem IsPlanar.induce [Finite V] (hG : IsPlanar G) (s : Set V) : IsPlanar (G.induce s) := by
  set G' := G.deleteEdges {e | ∃ v ∈ e, v ∉ s}
  have hs : ∀ ⦃u w⦄, G'.Adj u w → u ∈ s → w ∈ s := fun u w h hu => by
    by_contra hw
    exact (deleteEdges_adj.mp h).2 ⟨w, Sym2.mem_mk_right u w, hw⟩
  have heq : G'.induce s = G.induce s := by
    ext u w
    simp only [comap_adj, Function.Embedding.subtype_apply, G', deleteEdges_adj,
      Set.mem_ofPred_eq, and_iff_left_iff_imp]
    rintro - ⟨z, hz, hzs⟩
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    exacts [hzs u.2, hzs w.2]
  obtain ⟨ρ, hρ⟩ := hG.deleteEdges {e | ∃ v ∈ e, v ∉ s}
  rw [← heq]
  exact ⟨ρ.restrict s hs, hρ.restrict hs⟩

end MonoidProduct.Graph
