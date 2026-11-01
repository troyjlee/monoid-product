import MonoidProduct.Graph.MinorContraction
import MonoidProduct.Graph.PlanarSubgraph
set_option linter.style.header false

/-!
# Planarity is closed under contracting an edge

For a dart `a` from `x` to `y`, `contractEdge G x y` (`Graph/Minor.lean`) identifies `y` with
`x`.

* **Darts** (`contractDart`): every dart other than `a` and `a.symm` goes to a dart of the
  contraction, with its ends mapped by `contractVertex`.  This is onto, and one-to-one when `x` and
  `y` have no common neighbour (`contractDartEquiv`); a common neighbour `z` would give the two
  darts `xz` and `yz` the same image.
* **Rotation** (`RotationSystem.contract`): the cycles around `x` and `y` are spliced by the
  transposition of `a` and `a.symm`, which lie on different cycles, and then `a` and `a.symm` are
  erased: `eraseTwo (rot * swap a a.symm) a a.symm`.  **Faces** (`contract_face`): the face
  permutation is `eraseTwo face a a.symm`, the faces of `ρ` with the two darts erased.
* **Counts**: one vertex and one edge fewer, the same components, and the same completed faces
  `F̂`.  A whole face disappears only when the component of the edge is a single edge; then the new
  isolated vertex supplies its extra face.  So the Euler defect does not change
  (`eulerDefect_contract`), and a spherical rotation system stays spherical
  (`IsSpherical.contract`).
* **Common neighbours**: deleting the edges from `y` to the common neighbours of `x` and `y`
  (`thinEdges`) keeps planarity, leaves no common neighbour, and does not change the contraction
  (`contractEdge_deleteEdges_thinEdges`).  Hence `IsPlanar.contractEdge`: **contracting any edge of
  a planar graph gives a planar graph**.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*} {G : SimpleGraph V}

/-! ## Counting survivors -/

/-- Removing two distinct elements from a finite type. -/
theorem natCard_subtype_ne_and_ne_add_two {α : Type*} [Finite α] {a b : α} (hab : a ≠ b) :
    Nat.card {d // d ≠ a ∧ d ≠ b} + 2 = Nat.card α := by
  have h := Set.ncard_add_ncard_compl ({a, b} : Set α)
  rw [Set.ncard_pair hab, ← Nat.card_coe_set_eq] at h
  rw [← h, add_comm]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun d => by simp)

/-- Removing one element from a finite type. -/
theorem natCard_subtype_ne_add_one {α : Type*} [Finite α] (b : α) :
    Nat.card {d // d ≠ b} + 1 = Nat.card α := by
  have h := Set.ncard_add_ncard_compl ({b} : Set α)
  rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at h
  rw [← h, add_comm]
  rfl

/-- **Twice the edges are the darts.** -/
theorem two_mul_ncard_edgeSet_eq_natCard_dart [Finite V] :
    2 * G.edgeSet.ncard = Nat.card G.Dart := by
  classical
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, dart_card_eq_twice_card_edges, ← coe_edgeFinset,
    Set.ncard_coe_finset]

/-! ## The darts of a contraction -/

section Darts

variable [DecidableEq V] (a : G.Dart)

omit [DecidableEq V] in
/-- The ends of `a`, in the tail-head order. -/
private theorem dart_eq_of_fst_snd {d : G.Dart} (h1 : d.fst = a.fst) (h2 : d.snd = a.snd) :
    d = a :=
  Dart.ext _ _ (Prod.ext h1 h2)

omit [DecidableEq V] in
private theorem dart_eq_symm_of_fst_snd {d : G.Dart} (h1 : d.fst = a.snd) (h2 : d.snd = a.fst) :
    d = a.symm :=
  Dart.ext _ _ (Prod.ext h1 h2)

/-- **A surviving dart goes to a dart of the contraction**: its edge is not the edge of `a`. -/
theorem contractEdge_adj_of_dart (d : {d : G.Dart // d ≠ a ∧ d ≠ a.symm}) :
    (contractEdge G a.fst a.snd).Adj (contractVertex a.adj.ne d.1.fst)
      (contractVertex a.adj.ne d.1.snd) :=
  contractEdge_adj_contractVertex a.adj d.1.adj ((dart_edge_ne_iff d.1 a).mpr d.2)

/-- **The darts of the contraction**: a dart other than `a` and `a.symm`, with its ends mapped. -/
def contractDart (d : {d : G.Dart // d ≠ a ∧ d ≠ a.symm}) :
    (contractEdge G a.fst a.snd).Dart :=
  ⟨(contractVertex a.adj.ne d.1.fst, contractVertex a.adj.ne d.1.snd), contractEdge_adj_of_dart a d⟩

/-- The reversal of a surviving dart survives. -/
def survivorSymm (d : {d : G.Dart // d ≠ a ∧ d ≠ a.symm}) : {d : G.Dart // d ≠ a ∧ d ≠ a.symm} :=
  ⟨d.1.symm, fun h => d.2.2 ((Dart.symm_symm d.1).symm.trans (congrArg Dart.symm h)),
    fun h => d.2.1 ((Dart.symm_symm d.1).symm.trans
      ((congrArg Dart.symm h).trans (Dart.symm_symm a)))⟩

theorem contractDart_survivorSymm (d : {d : G.Dart // d ≠ a ∧ d ≠ a.symm}) :
    contractDart a (survivorSymm a d) = (contractDart a d).symm :=
  rfl

/-- **Every dart of the contraction comes from a surviving dart.** -/
theorem contractDart_surjective : Function.Surjective (contractDart a) := by
  rintro ⟨⟨p, r⟩, hpr⟩
  have hx : a.fst ≠ a.snd := a.adj.ne
  obtain ⟨hne, (h | ⟨hp, h⟩) | (h | ⟨hr, h⟩)⟩ := contractEdge_adj.mp hpr
  · refine ⟨⟨⟨(p.1, r.1), h⟩, fun he => r.2 ?_, fun he => p.2 ?_⟩, ?_⟩
    · exact congrArg (fun d : G.Dart => d.snd) he
    · exact congrArg (fun d : G.Dart => d.fst) he
    · exact Dart.ext _ _ (Prod.ext (contractVertex_val _ p) (contractVertex_val _ r))
  · have hr : r.1 ≠ a.fst := fun h' => hne (Subtype.ext (hp.trans h'.symm))
    refine ⟨⟨⟨(a.snd, r.1), h⟩, fun he => hx ?_, fun he => hr ?_⟩, ?_⟩
    · exact (congrArg (fun d : G.Dart => d.fst) he).symm
    · exact congrArg (fun d : G.Dart => d.snd) he
    · refine Dart.ext _ _ (Prod.ext ?_ (contractVertex_val _ r))
      change contractVertex a.adj.ne a.snd = p
      rw [contractVertex_self]
      exact Subtype.ext hp.symm
  · refine ⟨⟨⟨(p.1, r.1), h.symm⟩, fun he => r.2 ?_, fun he => p.2 ?_⟩, ?_⟩
    · exact congrArg (fun d : G.Dart => d.snd) he
    · exact congrArg (fun d : G.Dart => d.fst) he
    · exact Dart.ext _ _ (Prod.ext (contractVertex_val _ p) (contractVertex_val _ r))
  · have hp : p.1 ≠ a.fst := fun h' => hne (Subtype.ext (h'.trans hr.symm))
    refine ⟨⟨⟨(p.1, a.snd), h.symm⟩, fun he => hp ?_, fun he => p.2 ?_⟩, ?_⟩
    · exact congrArg (fun d : G.Dart => d.fst) he
    · exact congrArg (fun d : G.Dart => d.fst) he
    · refine Dart.ext _ _ (Prod.ext (contractVertex_val _ p) ?_)
      change contractVertex a.adj.ne a.snd = r
      rw [contractVertex_self]
      exact Subtype.ext hr.symm

/-- **Without common neighbours the darts correspond one to one**: the only darts with the same
image would be `xz` and `yz` for a common neighbour `z`. -/
theorem contractDart_injective (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    Function.Injective (contractDart a) := by
  have hcommon : ∀ z, G.Adj a.fst z → G.Adj a.snd z → False := fun z h1 h2 =>
    Set.disjoint_left.mp hdisj h1 h2
  have hxy : a.fst ≠ a.snd := a.adj.ne
  -- Two distinct ends of the edge are its two ends, in some order.
  have hpair : ∀ {u u' : V}, (u = a.fst ∨ u = a.snd) → (u' = a.fst ∨ u' = a.snd) → u ≠ u' →
      (u = a.fst ∧ u' = a.snd) ∨ (u = a.snd ∧ u' = a.fst) := by
    rintro u u' (rfl | rfl) (rfl | rfl) h
    · exact absurd rfl h
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl h
  rintro ⟨⟨⟨u, w⟩, huw⟩, hda, hdb⟩ ⟨⟨⟨u', w'⟩, huw'⟩, hda', hdb'⟩ h
  have h1 : contractVertex a.adj.ne u = contractVertex a.adj.ne u' :=
    congrArg (fun d : (contractEdge G a.fst a.snd).Dart => d.fst) h
  have h2 : contractVertex a.adj.ne w = contractVertex a.adj.ne w' :=
    congrArg (fun d : (contractEdge G a.fst a.snd).Dart => d.snd) h
  change G.Adj u w at huw
  change G.Adj u' w' at huw'
  -- The tails agree.
  have hu : u = u' := by
    by_contra hne
    obtain ⟨hu, hu'⟩ := ((contractVertex_eq_iff hxy).mp h1).resolve_left hne
    rcases (contractVertex_eq_iff hxy).mp h2 with rfl | ⟨hw, hw'⟩
    · rcases hpair hu hu' hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcommon w huw huw'
      · exact hcommon w huw' huw
    · rcases hpair hu hw huw.ne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hda (dart_eq_of_fst_snd a rfl rfl)
      · exact hdb (dart_eq_symm_of_fst_snd a rfl rfl)
  subst hu
  -- And so do the heads.
  have hw : w = w' := by
    by_contra hne
    obtain ⟨hw, hw'⟩ := ((contractVertex_eq_iff hxy).mp h2).resolve_left hne
    rcases hpair hw hw' hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcommon u huw.symm huw'.symm
    · exact hcommon u huw'.symm huw.symm
  subst hw
  rfl

/-- **The darts of the contraction**, without common neighbours: the darts of `G` other than `a`
and `a.symm`. -/
noncomputable def contractDartEquiv
    (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    {d : G.Dart // d ≠ a ∧ d ≠ a.symm} ≃ (contractEdge G a.fst a.snd).Dart :=
  Equiv.ofBijective (contractDart a) ⟨contractDart_injective a hdisj, contractDart_surjective a⟩

theorem contractDartEquiv_apply (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd))
    (d : {d : G.Dart // d ≠ a ∧ d ≠ a.symm}) : contractDartEquiv a hdisj d = contractDart a d :=
  rfl

end Darts

/-! ## The rotation of a contraction -/

namespace RotationSystem

variable [DecidableEq V] (ρ : RotationSystem G)

/-- **Splicing the rotations at the two ends keeps tails up to the identification**: after the
transposition of `a` and `a.symm`, a dart at `x` or `y` goes to a dart at `x` or `y`. -/
theorem contractVertex_fst_rot_mul_swap (a d : G.Dart) :
    contractVertex a.adj.ne ((ρ.rot * swap a a.symm) d).fst = contractVertex a.adj.ne d.fst := by
  have hq : contractVertex a.adj.ne a.snd = contractVertex a.adj.ne a.fst := by
    rw [contractVertex_self, contractVertex_of_ne _ a.adj.ne]
  by_cases h1 : d = a
  · subst h1
    rw [mul_apply, swap_apply_left, ρ.fst_rot]
    exact hq
  · by_cases h2 : d = a.symm
    · subst h2
      rw [mul_apply, swap_apply_right, ρ.fst_rot]
      exact hq.symm
    · rw [mul_swap_apply_of_ne _ h1 h2, ρ.fst_rot]

/-- **Contracting the edge of `a`**, when its ends have no common neighbour: the rotation splices
the cycles around the two ends by the transposition of `a` and `a.symm` and erases both,
`eraseTwo (rot * swap a a.symm) a a.symm`. -/
noncomputable def contract [Finite V] (a : G.Dart)
    (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    RotationSystem (contractEdge G a.fst a.snd) where
  rot := (contractDartEquiv a hdisj).permCongr (eraseTwo (ρ.rot * swap a a.symm) a a.symm)
  fst_rot d := by
    obtain ⟨z, rfl⟩ := (contractDartEquiv a hdisj).surjective d
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change contractVertex a.adj.ne (bypass (bypass (ρ.rot * swap a a.symm) a) a.symm z.1).fst =
      contractVertex a.adj.ne z.1.fst
    exact apply_bypass_eq (g := fun d : G.Dart => contractVertex a.adj.ne d.fst)
      (apply_bypass_eq (g := fun d : G.Dart => contractVertex a.adj.ne d.fst)
        (ρ.contractVertex_fst_rot_mul_swap a) a) a.symm z.1
  sameCycle_rot d d' h := by
    have := finite_dart (G := G)
    obtain ⟨z, rfl⟩ := (contractDartEquiv a hdisj).surjective d
    obtain ⟨z', rfl⟩ := (contractDartEquiv a hdisj).surjective d'
    rw [sameCycle_permCongr, sameCycle_eraseTwo_iff]
    -- The rotation cycles at the two ends are different, and the transposition joins them.
    have hab : ¬ ρ.rot.SameCycle a a.symm := fun hs =>
      a.adj.ne (eq_of_sameCycle_of_forall (g := fun d : G.Dart => d.fst) ρ.fst_rot hs)
    rw [sameCycle_mul_swap_iff_of_not_sameCycle hab]
    have h' : contractVertex a.adj.ne z.1.fst = contractVertex a.adj.ne z'.1.fst := h
    rcases (contractVertex_eq_iff a.adj.ne).mp h' with he | ⟨hz, hz'⟩
    · exact Or.inl (ρ.sameCycle_rot _ _ he)
    · refine Or.inr ⟨?_, ?_⟩
      · rcases hz with hz | hz
        · exact Or.inl (ρ.sameCycle_rot _ _ hz)
        · exact Or.inr (ρ.sameCycle_rot _ _ hz)
      · rcases hz' with hz' | hz'
        · exact Or.inl (ρ.sameCycle_rot _ _ hz')
        · exact Or.inr (ρ.sameCycle_rot _ _ hz')

theorem contract_rot [Finite V] (a : G.Dart)
    (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    (ρ.contract a hdisj).rot =
      (contractDartEquiv a hdisj).permCongr (eraseTwo (ρ.rot * swap a a.symm) a a.symm) :=
  rfl

/-- At the reversal of a surviving dart `z`, the spliced rotation with `a` and `a.symm` bypassed
agrees with the face permutation with `a` and `a.symm` bypassed. -/
theorem bypass_bypass_rot_mul_swap_symm (a z : G.Dart) (hza : z ≠ a) (hzb : z ≠ a.symm) :
    bypass (bypass (ρ.rot * swap a a.symm) a) a.symm z.symm =
      bypass (bypass ρ.face a) a.symm z := by
  have hba : a.symm ≠ a := a.symm_ne
  have hza' : z.symm ≠ a := fun h => hzb (by rw [← h, Dart.symm_symm])
  have hzb' : z.symm ≠ a.symm := fun h => hza (by rw [← Dart.symm_symm z, h, Dart.symm_symm])
  have hX : (ρ.rot * swap a a.symm) z.symm = ρ.face z := by
    rw [mul_swap_apply_of_ne _ hza' hzb', face_apply]
  have hXa : (ρ.rot * swap a a.symm) a = ρ.rot a.symm := by rw [mul_apply, swap_apply_left]
  have hXb : (ρ.rot * swap a a.symm) a.symm = ρ.rot a := by rw [mul_apply, swap_apply_right]
  have hFa : ρ.face a = ρ.rot a.symm := face_apply _ _
  have hFb : ρ.face a.symm = ρ.rot a := by rw [face_apply, Dart.symm_symm]
  rw [bypass_apply_of_ne _ hzb', bypass_apply_of_ne _ hza', bypass_apply_of_ne _ hba,
    bypass_apply_of_ne _ hzb, bypass_apply_of_ne _ hza, bypass_apply_of_ne _ hba, hX, hXa, hXb,
    hFa, hFb]

/-- **The faces of the contraction**: the face permutation is `eraseTwo face a a.symm`, the face
permutation of `ρ` with the two darts of the contracted edge erased. -/
theorem contract_face [Finite V] (a : G.Dart)
    (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    (ρ.contract a hdisj).face =
      (contractDartEquiv a hdisj).permCongr (eraseTwo ρ.face a a.symm) := by
  refine Equiv.ext fun d => ?_
  obtain ⟨z, rfl⟩ := (contractDartEquiv a hdisj).surjective d
  have hs : (contractDartEquiv a hdisj z).symm = contractDartEquiv a hdisj (survivorSymm a z) :=
    rfl
  rw [face_apply, contract_rot, Equiv.permCongr_apply, Equiv.permCongr_apply, hs,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  congr 1
  exact Subtype.ext (ρ.bypass_bypass_rot_mul_swap_symm a z.1 z.2.1 z.2.2)

/-! ## The counts after contracting -/

/-- **The faces of the contraction**: those of `ρ`, less one when the component of the edge is a
single edge, whose face disappears. -/
theorem natCard_face_contract_add [Finite V] (a : G.Dart)
    (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    Nat.card (ρ.contract a hdisj).Face +
      (if ρ.rot a = a ∧ ρ.rot a.symm = a.symm then 1 else 0) = Nat.card ρ.Face := by
  have := finite_dart (G := G)
  have h := cycleCount_eraseTwo_add ρ.face (Ne.symm a.symm_ne)
  have hFa : ρ.face a = ρ.rot a.symm := face_apply _ _
  have hFb : ρ.face a.symm = ρ.rot a := by rw [face_apply, Dart.symm_symm]
  rw [hFa, ite_eq_right (ρ.rot_symm_ne a), add_zero, bypass_apply_of_ne _ a.symm_ne, hFb,
    hFa] at h
  change cycleCount (ρ.contract a hdisj).face + _ = cycleCount ρ.face
  rw [contract_face, cycleCount_permCongr, ← h]
  congr 1
  by_cases h1 : ρ.rot a = a
  · rw [ite_eq_left h1]
    by_cases h2 : ρ.rot a.symm = a.symm
    · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h2]
    · rw [ite_eq_right fun h' => h2 h'.2, ite_eq_right h2]
  · rw [ite_eq_right h1, ite_eq_right fun h' => h1 h'.1, ite_eq_right (ρ.rot_ne_symm a)]

omit [DecidableEq V] in
/-- The tail of `a` loses all its neighbours other than the head, and the head all its neighbours
other than the tail, exactly when the rotation fixes `a` and `a.symm`. -/
theorem rot_eq_self_and_iff (a : G.Dart) :
    (ρ.rot a = a ∧ ρ.rot a.symm = a.symm) ↔
      (∀ w, G.Adj a.fst w → w = a.snd) ∧ ∀ w, G.Adj a.snd w → w = a.fst := by
  rw [ρ.rot_eq_self_iff, ρ.rot_eq_self_iff]
  rfl

/-- **The isolated vertices of the contraction**: those of `G`, and the contracted vertex when the
component of the edge is a single edge. -/
theorem ncard_isolatedVerts_contractEdge [Finite V] (a : G.Dart) :
    (isolatedVerts (contractEdge G a.fst a.snd)).ncard = (isolatedVerts G).ncard +
      if ρ.rot a = a ∧ ρ.rot a.symm = a.symm then 1 else 0 := by
  set x' : {v // v ≠ a.snd} := ⟨a.fst, a.adj.ne⟩
  have hxnot : a.fst ∉ isolatedVerts G := fun h => h a.snd a.adj
  -- Away from the contracted vertex, isolation does not change.
  have hother : ∀ p : {v // v ≠ a.snd}, p.1 ≠ a.fst →
      (p ∈ isolatedVerts (contractEdge G a.fst a.snd) ↔ p.1 ∈ isolatedVerts G) := by
    intro p hp
    constructor
    · intro hiso w hw
      by_cases hwy : w = a.snd
      · subst hwy
        refine hiso x' (contractEdge_adj.mpr ⟨fun h => hp (congrArg Subtype.val h),
          Or.inr (Or.inr ⟨rfl, hw.symm⟩)⟩)
      · refine hiso ⟨w, hwy⟩ (contractEdge_adj.mpr ⟨fun h => hw.ne (congrArg Subtype.val h),
          Or.inl (Or.inl hw)⟩)
    · intro hiso r hr
      obtain ⟨-, (h | ⟨hx, -⟩) | (h | ⟨-, h⟩)⟩ := contractEdge_adj.mp hr
      · exact hiso _ h
      · exact hp hx
      · exact hiso _ h.symm
      · exact hiso _ h.symm
  -- The contracted vertex is isolated exactly when the edge was a whole component.
  have hx' : x' ∈ isolatedVerts (contractEdge G a.fst a.snd) ↔
      (ρ.rot a = a ∧ ρ.rot a.symm = a.symm) := by
    rw [ρ.rot_eq_self_and_iff]
    constructor
    · intro hiso
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · by_contra hwy
        exact hiso ⟨w, hwy⟩ (contractEdge_adj.mpr ⟨fun h => hw.ne (congrArg Subtype.val h),
          Or.inl (Or.inl hw)⟩)
      · by_contra hwx
        have hwy : w ≠ a.snd := hw.ne.symm
        exact hiso ⟨w, hwy⟩ (contractEdge_adj.mpr ⟨fun h => hwx (congrArg Subtype.val h).symm,
          Or.inl (Or.inr ⟨rfl, hw⟩)⟩)
    · rintro ⟨h1, h2⟩ r hr
      obtain ⟨hne, (h | ⟨-, h⟩) | (h | ⟨hr', -⟩)⟩ := contractEdge_adj.mp hr
      · exact r.2 (h1 _ h)
      · exact hne (Subtype.ext (h2 _ h).symm)
      · exact r.2 (h1 _ h.symm)
      · exact hne (Subtype.ext hr'.symm)
  have hset : isolatedVerts (contractEdge G a.fst a.snd) =
      Subtype.val ⁻¹' isolatedVerts G ∪ {p | p = x' ∧ ρ.rot a = a ∧ ρ.rot a.symm = a.symm} := by
    ext p
    by_cases hp : p = x'
    · subst hp
      rw [hx']
      have hxnot' : ¬ (x'.1 ∈ isolatedVerts G) := hxnot
      simp [hxnot']
    · rw [hother p fun h => hp (Subtype.ext h)]
      simp [hp]
  have hdisj : Disjoint (Subtype.val ⁻¹' isolatedVerts G)
      {p : {v // v ≠ a.snd} | p = x' ∧ ρ.rot a = a ∧ ρ.rot a.symm = a.symm} := by
    rw [Set.disjoint_left]
    rintro p hp ⟨rfl, -⟩
    exact hxnot hp
  have hpre : (Subtype.val ⁻¹' isolatedVerts G : Set {v // v ≠ a.snd}).ncard =
      (isolatedVerts G).ncard := by
    refine Set.ncard_preimage_of_injective_subset_range Subtype.val_injective fun v hv => ?_
    have hvy : v ≠ a.snd := fun h => hv a.fst (h ▸ a.adj.symm)
    exact ⟨⟨v, hvy⟩, rfl⟩
  rw [hset, Set.ncard_union_eq hdisj, hpre]
  congr 1
  split_ifs with h
  · simp [h]
  · simp [h]

omit [DecidableEq V] in
theorem natCard_contractEdge_vertices_add_one [Finite V] (a : G.Dart) :
    Nat.card {v // v ≠ a.snd} + 1 = Nat.card V :=
  natCard_subtype_ne_add_one a.snd

omit [DecidableEq V] in
/-- **The edges of the contraction**: one fewer, without common neighbours. -/
theorem ncard_edgeSet_contractEdge_add_one [Finite V] (a : G.Dart)
    (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    (contractEdge G a.fst a.snd).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  classical
  have := finite_dart (G := G)
  have h1 := two_mul_ncard_edgeSet_eq_natCard_dart (G := contractEdge G a.fst a.snd)
  have h2 := two_mul_ncard_edgeSet_eq_natCard_dart (G := G)
  have h3 := Nat.card_congr (contractDartEquiv a hdisj)
  have h4 := natCard_subtype_ne_and_ne_add_two (Ne.symm a.symm_ne)
  omega

/-- **Contracting keeps the completed faces**: when the component of the edge is a single edge, its
face disappears and the contracted vertex, now isolated, supplies its extra face. -/
theorem completedFaceCount_contract [Finite V] (a : G.Dart)
    (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    (ρ.contract a hdisj).completedFaceCount = ρ.completedFaceCount := by
  have hF := ρ.natCard_face_contract_add a hdisj
  have hI := ρ.ncard_isolatedVerts_contractEdge a
  unfold completedFaceCount
  rw [hI, ← hF]
  ring

/-- **Contracting an edge without common neighbours keeps the Euler defect**: one vertex and one
edge fewer, with the same components and completed faces. -/
theorem eulerDefect_contract [Finite V] (a : G.Dart)
    (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    (ρ.contract a hdisj).eulerDefect = ρ.eulerDefect := by
  have hC := natCard_connectedComponent_contractEdge a.adj
  have hV := natCard_contractEdge_vertices_add_one (G := G) a
  have hE := ncard_edgeSet_contractEdge_add_one a hdisj
  unfold eulerDefect
  rw [hC, ρ.completedFaceCount_contract a hdisj, ← hV, ← hE]
  push_cast
  ring

/-- **Contracting an edge without common neighbours keeps a spherical rotation system
spherical.** -/
theorem IsSpherical.contract [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) (a : G.Dart)
    (hdisj : Disjoint (G.neighborSet a.fst) (G.neighborSet a.snd)) :
    (ρ.contract a hdisj).IsSpherical := by
  rw [isSpherical_iff_eulerDefect_eq_zero] at hρ ⊢
  rw [eulerDefect_contract, hρ]

end RotationSystem

/-! ## Common neighbours -/

section Thin

variable {x y : V}

variable (G x y) in
/-- **The edges from `y` to the common neighbours of `x` and `y`**: deleting them keeps `xz` for
every common neighbour `z`, and leaves the contraction unchanged. -/
def thinEdges : Set (Sym2 V) := {e | ∃ z, G.Adj x z ∧ G.Adj y z ∧ e = s(y, z)}

theorem deleteEdges_thinEdges_adj_iff {u w : V} :
    (G.deleteEdges (thinEdges G x y)).Adj u w ↔
      G.Adj u w ∧ ¬ ∃ z, G.Adj x z ∧ G.Adj y z ∧ s(u, w) = s(y, z) := by
  rw [deleteEdges_adj]
  rfl

/-- The edge `xy` is kept. -/
theorem deleteEdges_thinEdges_adj (hxy : G.Adj x y) :
    (G.deleteEdges (thinEdges G x y)).Adj x y := by
  refine deleteEdges_thinEdges_adj_iff.mpr ⟨hxy, ?_⟩
  rintro ⟨z, hxz, -, he⟩
  rcases Sym2.eq_iff.mp he with ⟨h, -⟩ | ⟨h, -⟩
  · exact hxy.ne h
  · exact G.loopless.irrefl _ (h ▸ hxz)

/-- **No common neighbours are left.** -/
theorem disjoint_neighborSet_deleteEdges_thinEdges :
    Disjoint ((G.deleteEdges (thinEdges G x y)).neighborSet x)
      ((G.deleteEdges (thinEdges G x y)).neighborSet y) := by
  rw [Set.disjoint_left]
  intro z hxz hyz
  have hxz' := (deleteEdges_thinEdges_adj_iff.mp hxz).1
  obtain ⟨hyz', hnot⟩ := deleteEdges_thinEdges_adj_iff.mp hyz
  exact hnot ⟨z, hxz', hyz', rfl⟩

/-- **Thinning does not change the contraction**: `x` keeps its edge to each common neighbour. -/
theorem contractEdge_deleteEdges_thinEdges (hxy : G.Adj x y) :
    contractEdge (G.deleteEdges (thinEdges G x y)) x y = contractEdge G x y := by
  -- Edges avoiding `y` are kept; an edge `yz` is kept unless `z` is a common neighbour.
  have hkeep : ∀ {u w : V}, u ≠ y → w ≠ y →
      ((G.deleteEdges (thinEdges G x y)).Adj u w ↔ G.Adj u w) := fun {u w} hu hw => by
    rw [deleteEdges_thinEdges_adj_iff]
    refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
    rintro ⟨z, -, -, he⟩
    rcases Sym2.eq_iff.mp he with ⟨h', -⟩ | ⟨-, h'⟩
    · exact hu h'
    · exact hw h'
  have hy : ∀ {w : V}, ((G.deleteEdges (thinEdges G x y)).Adj y w ↔ G.Adj y w ∧ ¬ G.Adj x w) :=
    fun {w} => by
      rw [deleteEdges_thinEdges_adj_iff]
      refine and_congr_right fun hyw => not_congr ⟨?_, fun h => ⟨w, h, hyw, rfl⟩⟩
      rintro ⟨z, hxz, -, he⟩
      rcases Sym2.eq_iff.mp he with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]
        exact hxz
      · rw [h]
        exact hxy
  ext p r
  rw [contractEdge_adj, contractEdge_adj, hkeep p.2 r.2, hkeep r.2 p.2, hy, hy]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ((h | ⟨hp, h, -⟩) | (h | ⟨hr, h, -⟩))
    exacts [Or.inl (Or.inl h), Or.inl (Or.inr ⟨hp, h⟩), Or.inr (Or.inl h),
      Or.inr (Or.inr ⟨hr, h⟩)]
  · rintro ((h | ⟨hp, h⟩) | (h | ⟨hr, h⟩))
    · exact Or.inl (Or.inl h)
    · by_cases hxr : G.Adj x r
      · exact Or.inl (Or.inl (hp ▸ hxr))
      · exact Or.inl (Or.inr ⟨hp, h, hxr⟩)
    · exact Or.inr (Or.inl h)
    · by_cases hxp : G.Adj x p
      · exact Or.inr (Or.inl (hr ▸ hxp))
      · exact Or.inr (Or.inr ⟨hr, h, hxp⟩)

end Thin

/-- **Planarity is closed under contracting an edge**: delete the edges from `y` to the common
neighbours of `x` and `y`, which keeps planarity and leaves the contraction unchanged, and
contract the edge `xy` of the thinned graph, whose ends have no common neighbour. -/
theorem IsPlanar.contractEdge [Finite V] (hG : IsPlanar G) {x y : V} (hxy : G.Adj x y) :
    IsPlanar (Graph.contractEdge G x y) := by
  classical
  obtain ⟨ρ, hρ⟩ := hG.deleteEdges (thinEdges G x y)
  let a : (G.deleteEdges (thinEdges G x y)).Dart := ⟨(x, y), deleteEdges_thinEdges_adj hxy⟩
  rw [← contractEdge_deleteEdges_thinEdges hxy]
  exact ⟨ρ.contract a disjoint_neighborSet_deleteEdges_thinEdges,
    hρ.contract a disjoint_neighborSet_deleteEdges_thinEdges⟩

end MonoidProduct.Graph
