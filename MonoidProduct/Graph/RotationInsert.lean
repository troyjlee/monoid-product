import MonoidProduct.Graph.RotationChord
set_option linter.style.header false

/-!
# Inserting a vertex into a face of a rotation system

A new vertex placed inside a face of a spherical rotation system can be joined to vertices of that
face, keeping the rotation system spherical.  The construction keeps one face explicit: the new
vertex followed by the interval of the face between two consecutive attachments.

* `attachVertex G A`: `G` on `Option V`, with a new vertex `none` adjacent to the vertices of `A`
  (`attachVertex_adj_none_some`, `attachVertex_adj_some_none`, `attachVertex_adj_some_some`,
  `attachVertex_adj_none_none`); `attachDart A` carries the darts of `G` along.  Attaching one more
  vertex of `A` adds one edge (`isAddEdge_attachVertex`, `attachVertex_insert`), so chords apply
  (`Graph/RotationChord.lean`).
* `RotationSystem.insertLeaf ρ hS`: a new leaf at the tail `u` of a dart `a`, its dart
  `leafDart hS` just before `a` around `u`.  One vertex and one edge more, with the same faces and
  components (`eulerDefect_insertLeaf`, `IsSpherical.insertLeaf`).  Read from the leaf dart, the
  face through `a` goes to the new vertex and back, then around the old face from `a`
  (`faceDarts_insertLeaf`): its walk acquires the excursion `u`, new vertex, `u`.
* `exists_isSpherical_attachVertex_faceWalk`: **the marked fan**.  For a face walk `C` with
  distinct vertices, a set `A` of at least two of its vertices, and consecutive vertices `p` and `q`
  of `A` around `C`, the new vertex can be joined to `A` by a spherical rotation system with a face
  whose walk is the new vertex followed by the whole closed interval `closedArc C p q`.  The leaf at
  `p` comes first, then chords from the new vertex to the other vertices of `A` in the reverse
  cyclic order, ending with `q`; each chord cuts off the part of the face beyond its end
  (`RotationSystem.exists_fan_aux`).  For `k = |A|` this adds one vertex, `k` edges and `k - 1`
  faces.
* `isPlanar_attachVertex_of_subset_faceWalk`: **a new vertex joined to at least two vertices of a
  face with distinct vertices keeps planarity.**
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*}

/-! ## Attaching a new vertex -/

/-- **Attaching a new vertex**: `G` on `Option V`, with a new vertex `none` adjacent to the
vertices of `A`. -/
def attachVertex (G : SimpleGraph V) (A : Set V) : SimpleGraph (Option V) :=
  SimpleGraph.fromRel fun a b => match a, b with
    | none, some v => v ∈ A
    | some u, some w => G.Adj u w
    | _, _ => False

variable {G : SimpleGraph V} {A : Set V}

@[simp] theorem attachVertex_adj_none_some {v : V} :
    (attachVertex G A).Adj none (some v) ↔ v ∈ A := by
  simp [attachVertex]

@[simp] theorem attachVertex_adj_some_none {v : V} :
    (attachVertex G A).Adj (some v) none ↔ v ∈ A := by
  simp [attachVertex]

@[simp] theorem attachVertex_adj_some_some {u w : V} :
    (attachVertex G A).Adj (some u) (some w) ↔ G.Adj u w := by
  simp only [attachVertex, fromRel_adj, ne_eq, Option.some.injEq]
  exact ⟨fun h => h.2.elim id fun h' => h'.symm, fun h => ⟨h.ne, Or.inl h⟩⟩

@[simp] theorem attachVertex_adj_none_none : ¬ (attachVertex G A).Adj none none :=
  (attachVertex G A).irrefl

variable (A) in
/-- **The darts of `G` in `attachVertex G A`.** -/
def attachDart (d : G.Dart) : (attachVertex G A).Dart :=
  ⟨(some d.fst, some d.snd), attachVertex_adj_some_some.mpr d.adj⟩

@[simp] theorem fst_attachDart (d : G.Dart) : (attachDart A d).fst = some d.fst := rfl

@[simp] theorem snd_attachDart (d : G.Dart) : (attachDart A d).snd = some d.snd := rfl

theorem attachDart_injective : Function.Injective (attachDart (G := G) A) := fun d e hde => by
  have h1 : some d.fst = some e.fst := congrArg (fun d : (attachVertex G A).Dart => d.fst) hde
  have h2 : some d.snd = some e.snd := congrArg (fun d : (attachVertex G A).Dart => d.snd) hde
  exact Dart.ext _ _ (Prod.ext (Option.some.inj h1) (Option.some.inj h2))

theorem attachDart_symm (d : G.Dart) : attachDart A d.symm = (attachDart A d).symm := rfl

/-- **Attaching one more vertex of `A`** adds one edge from the new vertex. -/
theorem isAddEdge_attachVertex {A' : Set V} {r : V} (hA : ∀ x, x ∈ A ↔ x = r ∨ x ∈ A') :
    IsAddEdge (attachVertex G A') (attachVertex G A) none (some r) := by
  intro x y
  cases x <;> cases y <;> simp [hA, or_comm]

/-- **Attaching one more vertex** is adding the edge from the new vertex. -/
theorem attachVertex_insert (r : V) (A : Set V) :
    attachVertex G (insert r A) = attachVertex G A ⊔ edge none (some r) :=
  (isAddEdge_attachVertex fun _ => Set.mem_insert_iff).eq_sup_edge

/-! ## Inserting a leaf -/

section Leaf

variable {S : Set V} {a : G.Dart} (hS : ∀ x, x ∈ S ↔ x = a.fst)
include hS

/-- **The dart to a new leaf**, from the tail of `a` to the new vertex, when the new vertex is
adjacent to the tail of `a` alone. -/
def leafDart : (attachVertex G S).Dart :=
  ⟨(some a.fst, none), attachVertex_adj_some_none.mpr ((hS _).mpr rfl)⟩

@[simp] theorem fst_leafDart : (leafDart hS).fst = some a.fst := rfl

@[simp] theorem snd_leafDart : (leafDart hS).snd = none := rfl

theorem leafDart_symm_ne : (leafDart hS).symm ≠ leafDart hS := (leafDart hS).symm_ne

theorem attachDart_ne_leafDart (e : G.Dart) : attachDart S e ≠ leafDart hS := fun he =>
  Option.some_ne_none _ (congrArg (fun d : (attachVertex G S).Dart => d.snd) he)

theorem attachDart_ne_leafDart_symm (e : G.Dart) : attachDart S e ≠ (leafDart hS).symm := fun he =>
  Option.some_ne_none _ (congrArg (fun d : (attachVertex G S).Dart => d.fst) he)

/-- Every dart of the graph with the leaf is the leaf dart, its reversal, or a dart of `G`. -/
theorem eq_leafDart_or (d : (attachVertex G S).Dart) :
    d = leafDart hS ∨ d = (leafDart hS).symm ∨ ∃ e, d = attachDart S e := by
  obtain ⟨⟨s, t⟩, hst⟩ := d
  cases s with
  | none =>
    cases t with
    | none => exact absurd hst attachVertex_adj_none_none
    | some y =>
      obtain rfl : y = a.fst := (hS y).mp (attachVertex_adj_none_some.mp hst)
      exact Or.inr (Or.inl rfl)
  | some x =>
    cases t with
    | none =>
      obtain rfl : x = a.fst := (hS x).mp (attachVertex_adj_some_none.mp hst)
      exact Or.inl rfl
    | some y => exact Or.inr (Or.inr ⟨⟨(x, y), attachVertex_adj_some_some.mp hst⟩, rfl⟩)

/-- **The darts of the graph with the leaf**: those of `G`, and the leaf dart and its reversal. -/
noncomputable def leafDartEquiv :
    G.Dart ≃ {d : (attachVertex G S).Dart // d ≠ leafDart hS ∧ d ≠ (leafDart hS).symm} :=
  Equiv.ofBijective
    (fun e => ⟨attachDart S e, attachDart_ne_leafDart hS e, attachDart_ne_leafDart_symm hS e⟩)
    ⟨fun _ _ he => attachDart_injective (congrArg Subtype.val he), fun ⟨d, h1, h2⟩ => by
      rcases eq_leafDart_or hS d with rfl | rfl | ⟨e, rfl⟩
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact ⟨e, rfl⟩⟩

@[simp] theorem coe_leafDartEquiv (e : G.Dart) :
    (leafDartEquiv hS e : (attachVertex G S).Dart) = attachDart S e := rfl

/-- **A new leaf joins the component of its neighbour.** -/
theorem natCard_connectedComponent_attachVertex_leaf :
    Nat.card (attachVertex G S).ConnectedComponent = Nat.card G.ConnectedComponent := by
  let φ : G →g attachVertex G S := ⟨some, attachVertex_adj_some_some.mpr⟩
  refine (Nat.card_eq_of_bijective (ConnectedComponent.map φ) ⟨fun c c' hcc => ?_,
    fun c => ?_⟩).symm
  · induction c using ConnectedComponent.ind with | h x =>
    induction c' using ConnectedComponent.ind with | h y =>
    rw [ConnectedComponent.map_mk, ConnectedComponent.map_mk, ConnectedComponent.eq] at hcc
    refine ConnectedComponent.eq.mpr
      (chord_reachable_map_of_adj (G := G) (fun o : Option V => o.getD a.fst)
        (fun s t hst => ?_) hcc)
    cases s with
    | none =>
      cases t with
      | none => exact absurd hst attachVertex_adj_none_none
      | some y =>
        obtain rfl : y = a.fst := (hS y).mp (attachVertex_adj_none_some.mp hst)
        exact Reachable.rfl
    | some x =>
      cases t with
      | none =>
        obtain rfl : x = a.fst := (hS x).mp (attachVertex_adj_some_none.mp hst)
        exact Reachable.rfl
      | some y => exact (attachVertex_adj_some_some.mp hst).reachable
  · induction c using ConnectedComponent.ind with | h o =>
    cases o with
    | none =>
      refine ⟨G.connectedComponentMk a.fst, ?_⟩
      rw [ConnectedComponent.map_mk]
      exact ConnectedComponent.eq.mpr
        (attachVertex_adj_some_none.mpr ((hS _).mpr rfl)).reachable
    | some x => exact ⟨G.connectedComponentMk x, ConnectedComponent.map_mk _ _⟩

/-- **The isolated vertices with a new leaf**: those of `G`. -/
theorem isolatedVerts_attachVertex_leaf :
    isolatedVerts (attachVertex G S) = some '' isolatedVerts G := by
  ext o
  cases o with
  | none =>
    simp only [Set.mem_image, reduceCtorEq, and_false, exists_false, iff_false]
    exact fun hiso => hiso (some a.fst) (attachVertex_adj_none_some.mpr ((hS _).mpr rfl))
  | some x =>
    constructor
    · intro hiso
      exact ⟨x, fun y hy => hiso (some y) (attachVertex_adj_some_some.mpr hy), rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hx : x ∈ isolatedVerts G := by rw [← Option.some.inj hyx]; exact hy
      intro w hw
      cases w with
      | none =>
        have hxa : x = a.fst := (hS x).mp (attachVertex_adj_some_none.mp hw)
        rw [hxa] at hx
        exact hx a.snd a.adj
      | some z => exact hx z (attachVertex_adj_some_some.mp hw)

namespace RotationSystem

variable [DecidableEq V] (ρ : RotationSystem G)

/-- **The rotation after inserting a leaf**: the leaf dart goes just before `a` around its
tail, and is alone around the new vertex. -/
noncomputable def leafRot : Perm (attachVertex G S).Dart :=
  ρ.rot.extendDomain (leafDartEquiv hS) *
    swap (leafDartEquiv hS (ρ.rot.symm a) : (attachVertex G S).Dart) (leafDart hS)

theorem fst_extendDomain_leaf (d : (attachVertex G S).Dart) :
    (ρ.rot.extendDomain (leafDartEquiv hS) d).fst = d.fst := by
  by_cases hd : d ≠ leafDart hS ∧ d ≠ (leafDart hS).symm
  · obtain ⟨e, he⟩ := (leafDartEquiv hS).surjective ⟨d, hd⟩
    have hde : d = leafDartEquiv hS e := by rw [he]
    rw [hde, extendDomain_apply_image, coe_leafDartEquiv, coe_leafDartEquiv, fst_attachDart,
      fst_attachDart, ρ.fst_rot]
  · rw [extendDomain_apply_not_subtype ρ.rot (leafDartEquiv hS) hd]

theorem fst_leafRot (d : (attachVertex G S).Dart) : (ρ.leafRot hS d).fst = d.fst := by
  simp only [leafRot, mul_apply]
  rw [fst_extendDomain_leaf]
  refine apply_swap_eq_self (v := fun d : (attachVertex G S).Dart => d.fst) ?_ _
  change some (ρ.rot.symm a).fst = some a.fst
  rw [ρ.chord_fst_rot_symm]

theorem sameCycle_leafRot_attachDart [Finite V] {e e' : G.Dart} (he : ρ.rot.SameCycle e e') :
    (ρ.leafRot hS).SameCycle (attachDart S e) (attachDart S e') := by
  have := finite_dart (G := attachVertex G S)
  exact chord_sameCycle_mul_swap_of_apply_eq (chord_extendDomain_apply_left _ _)
    (leafDartEquiv hS _).2.1
    (sameCycle_extendDomain.mpr he)

theorem sameCycle_leafRot_leafDart [Finite V] :
    (ρ.leafRot hS).SameCycle (attachDart S (ρ.rot.symm a)) (leafDart hS) := by
  have := finite_dart (G := attachVertex G S)
  exact chord_sameCycle_mul_swap_self_of_apply_eq (chord_extendDomain_apply_left _ _)
    (leafDartEquiv hS _).2.1

/-- **Inserting a leaf** at the corner before `a`: the rotation system of `attachVertex G S`, with
`S` the tail of `a` alone, that puts the dart to the new vertex just before `a` around its tail.
The face through `a` acquires the excursion to the new vertex and back (`faceDarts_insertLeaf`). -/
noncomputable def insertLeaf [Finite V] : RotationSystem (attachVertex G S) where
  rot := ρ.leafRot hS
  fst_rot := ρ.fst_leafRot hS
  sameCycle_rot d d' hdd' := by
    have key : ∀ d : (attachVertex G S).Dart, d = (leafDart hS).symm ∨
        ∃ e : G.Dart, some e.fst = d.fst ∧ (ρ.leafRot hS).SameCycle d (attachDart S e) := by
      intro d
      rcases eq_leafDart_or hS d with rfl | rfl | ⟨e, rfl⟩
      · exact Or.inr ⟨ρ.rot.symm a, by rw [ρ.chord_fst_rot_symm]; rfl,
          (ρ.sameCycle_leafRot_leafDart hS).symm⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e, rfl, SameCycle.refl _ _⟩
    rcases key d with rfl | ⟨e, he, hde⟩
    · rcases key d' with rfl | ⟨e', he', -⟩
      · exact SameCycle.refl _ _
      · exact absurd (he'.trans hdd'.symm) (Option.some_ne_none _)
    · rcases key d' with rfl | ⟨e', he', hde'⟩
      · exact absurd (he.trans hdd') (Option.some_ne_none _)
      · exact hde.trans ((ρ.sameCycle_leafRot_attachDart hS (ρ.sameCycle_rot e e'
          (Option.some.inj (he.trans (hdd'.trans he'.symm))))).trans hde'.symm)

theorem leafRot_apply_attachDart {e : G.Dart} (hx : e ≠ ρ.rot.symm a) :
    ρ.leafRot hS (attachDart S e) = attachDart S (ρ.rot e) := by
  simp only [leafRot, mul_apply, coe_leafDartEquiv]
  rw [swap_apply_of_ne_of_ne (fun he => hx (attachDart_injective he))
    (attachDart_ne_leafDart hS e)]
  exact extendDomain_apply_image _ _ e

theorem leafRot_apply_left : ρ.leafRot hS (attachDart S (ρ.rot.symm a)) = leafDart hS := by
  simp only [leafRot, mul_apply, coe_leafDartEquiv]
  rw [swap_apply_left, chord_extendDomain_apply_left]

theorem leafRot_apply_leafDart : ρ.leafRot hS (leafDart hS) = attachDart S a := by
  simp only [leafRot, mul_apply, coe_leafDartEquiv]
  rw [swap_apply_right]
  refine (extendDomain_apply_image _ _ (ρ.rot.symm a)).trans ?_
  rw [Equiv.apply_symm_apply]
  rfl

theorem leafRot_apply_leafDart_symm : ρ.leafRot hS (leafDart hS).symm = (leafDart hS).symm := by
  simp only [leafRot, mul_apply, coe_leafDartEquiv]
  rw [swap_apply_of_ne_of_ne (attachDart_ne_leafDart_symm hS _).symm (leafDart_symm_ne hS),
    chord_extendDomain_apply_right]

variable [Finite V]

theorem insertLeaf_face_attachDart {e : G.Dart} (hx : e ≠ (ρ.rot.symm a).symm) :
    (ρ.insertLeaf hS).face (attachDart S e) = attachDart S (ρ.face e) := by
  rw [face_apply, ← attachDart_symm]
  exact ρ.leafRot_apply_attachDart hS fun he => hx (by rw [← he, Dart.symm_symm])

theorem insertLeaf_face_left :
    (ρ.insertLeaf hS).face (attachDart S (ρ.rot.symm a).symm) = leafDart hS := by
  rw [face_apply, ← attachDart_symm, Dart.symm_symm]
  exact ρ.leafRot_apply_left hS

theorem insertLeaf_face_leafDart : (ρ.insertLeaf hS).face (leafDart hS) = (leafDart hS).symm := by
  rw [face_apply]
  exact ρ.leafRot_apply_leafDart_symm hS

theorem insertLeaf_face_leafDart_symm :
    (ρ.insertLeaf hS).face (leafDart hS).symm = attachDart S a := by
  rw [face_apply, Dart.symm_symm]
  exact ρ.leafRot_apply_leafDart hS

/-- **The face permutation after inserting a leaf**: the old one with the two new darts joined,
then joined to the face through the dart before `a`. -/
theorem insertLeaf_face_eq :
    (ρ.insertLeaf hS).face = ρ.face.extendDomain (leafDartEquiv hS) *
      swap (leafDart hS) (leafDart hS).symm *
      swap (leafDartEquiv hS (ρ.rot.symm a).symm : (attachVertex G S).Dart) (leafDart hS).symm :=
  chord_extendDomain_mul_swap_mul (leafDartEquiv hS) ρ.rot (dartReverse G) (dartReverse _)
    (fun _ => rfl) rfl rfl (fun e => Dart.symm_symm e) _

/-- **A leaf keeps the number of faces.** -/
theorem natCard_face_insertLeaf : Nat.card (ρ.insertLeaf hS).Face = Nat.card ρ.Face := by
  have := finite_dart (G := attachVertex G S)
  change cycleCount (ρ.insertLeaf hS).face = cycleCount ρ.face
  rw [insertLeaf_face_eq]
  exact chord_cycleCount_extendDomain_mul_swap_mul_swap _ (leafDart_symm_ne hS).symm ρ.face _

/-- **A leaf keeps the Euler defect**: one vertex and one edge more, with the same components,
faces and isolated vertices. -/
theorem eulerDefect_insertLeaf : (ρ.insertLeaf hS).eulerDefect = ρ.eulerDefect := by
  have hC := natCard_connectedComponent_attachVertex_leaf hS
  have hV : Nat.card (Option V) = Nat.card V + 1 := Finite.card_option
  have hE : (attachVertex G S).edgeSet.ncard = G.edgeSet.ncard + 1 := by
    have := finite_dart (G := attachVertex G S)
    have h1 := two_mul_ncard_edgeSet_eq_natCard_dart (G := attachVertex G S)
    have h2 := two_mul_ncard_edgeSet_eq_natCard_dart (G := G)
    have h3 := Nat.card_congr (leafDartEquiv hS)
    have h4 := natCard_subtype_ne_and_ne_add_two (leafDart_symm_ne hS).symm
    omega
  have hF := ρ.natCard_face_insertLeaf hS
  have hI : (isolatedVerts (attachVertex G S)).ncard = (isolatedVerts G).ncard := by
    rw [isolatedVerts_attachVertex_leaf hS,
      Set.ncard_image_of_injective _ (Option.some_injective V)]
  unfold eulerDefect completedFaceCount
  rw [hC, hV, hE, hF, hI]
  push_cast
  ring

variable {ρ} in
/-- **A leaf keeps a spherical rotation system spherical.** -/
theorem IsSpherical.insertLeaf (hρ : ρ.IsSpherical) : (ρ.insertLeaf hS).IsSpherical := by
  rw [isSpherical_iff_eulerDefect_eq_zero] at hρ ⊢
  rw [ρ.eulerDefect_insertLeaf hS, hρ]

/-- **The face of a new leaf**: the face through `a`, read from the leaf dart, goes to the new
vertex and back and then around the old face from `a`.  On tails: the face walk from the tail `u`
of `a` acquires the excursion `u`, new vertex, `u`. -/
theorem faceDarts_insertLeaf :
    (ρ.insertLeaf hS).faceDarts (leafDart hS) =
      leafDart hS :: (leafDart hS).symm :: (ρ.faceDarts a).map (attachDart S) := by
  have := finite_dart (G := G)
  have hD : orbitList ρ.face a = [] ++ ρ.faceDarts a := rfl
  have hDne : ρ.faceDarts a ≠ [] := orbitList_ne_nil _ _
  have hx : (ρ.faceDarts a).getLast hDne = (ρ.rot.symm a).symm := ρ.face.injective (by
    rw [chord_apply_getLast_right_of_orbitList_eq_append hD hDne, chord_face_symm_rot_symm])
  have hM : (ρ.faceDarts a).map (attachDart S) ≠ [] := by
    rw [Ne, List.map_eq_nil_iff]; exact hDne
  refine chord_orbitList_eq_cons ?_ (List.cons_ne_nil _ _) (ρ.insertLeaf_face_leafDart hS)
    (fun i hi => ?_) ?_
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
      (ρ.nodup_faceDarts a).map attachDart_injective⟩⟩
    · simp only [List.mem_cons, List.mem_map, not_or, not_exists, not_and]
      exact ⟨(leafDart_symm_ne hS).symm, fun e _ => attachDart_ne_leafDart hS e⟩
    · simp only [List.mem_map, not_exists, not_and]
      exact fun e _ => attachDart_ne_leafDart_symm hS e
  · rcases i with _ | j
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.getElem_map]
      rw [ρ.insertLeaf_face_leafDart_symm hS, getElem_faceDarts, pow_zero, one_apply]
    · simp only [List.length_cons, List.length_map] at hi
      simp only [List.getElem_cons_succ, List.getElem_map]
      have hj : (ρ.faceDarts a)[j] ≠ (ρ.rot.symm a).symm := by
        rw [← hx, List.getLast_eq_getElem, Ne, (ρ.nodup_faceDarts a).getElem_inj_iff]
        omega
      rw [ρ.insertLeaf_face_attachDart hS hj,
        chord_apply_getElem_of_orbitList_eq_append (L := ρ.faceDarts a) (R := [])
          (List.append_nil _).symm j (by omega)]
  · rw [List.getLast_cons hM, List.getLast_map, hx]
    exact ρ.insertLeaf_face_left hS

end RotationSystem

end Leaf

/-! ## The fan -/

namespace RotationSystem

variable [DecidableEq V] [Finite V] {ρ : RotationSystem G}

/-- **The fan, built backwards around a face.**  Let the face walk `C` from the dart `e` have
distinct vertices, and let `A` contain the tail of `e`, the vertex `C[0]`, and otherwise only
vertices at positions at least `t` along `C`, with `C[t] ∈ A` if `t < |C|`.  Then the new vertex
can be joined to `A`, with a face that reads: the dart from `C[t]` (from `C[0]` if `t = |C|`) to
the new vertex, the dart back to `C[0]`, and then the first `t` darts of the old face.

For `A = {C[0]}` this is a leaf.  Otherwise the vertex `C[t]` is joined last, by a chord inside the
face of the fan for `A` without `C[t]`: it cuts off the part of that face beyond `C[t]`. -/
theorem exists_fan_aux (hρ : ρ.IsSpherical) (e : G.Dart) (hC : (ρ.faceWalk e).Nodup) :
    ∀ (k : ℕ) (A : Finset V), A.card = k → e.fst ∈ A → (∀ x ∈ A, x ∈ ρ.faceWalk e) →
    ∀ t, 0 < t → t ≤ (ρ.faceWalk e).length →
      (∀ x ∈ A, x ≠ e.fst → t ≤ (ρ.faceWalk e).idxOf x) →
      (∀ ht : t < (ρ.faceWalk e).length, (ρ.faceWalk e)[t] ∈ A) →
      ∃ τ : RotationSystem (attachVertex G ↑A), τ.IsSpherical ∧
        ∃ g c : (attachVertex G ↑A).Dart, g.fst = some ((ρ.faceWalk e).getD t e.fst) ∧
          c.fst = none ∧
          τ.faceDarts g = g :: c :: ((ρ.faceDarts e).take t).map (attachDart (↑A : Set V)) := by
  have hlen : (ρ.faceWalk e).length = (ρ.faceDarts e).length := ρ.length_faceWalk e
  have hC0 : ∀ h0 : 0 < (ρ.faceWalk e).length, (ρ.faceWalk e)[0] = e.fst := fun h0 => by
    rw [getElem_faceWalk, pow_zero, one_apply]
  intro k
  induction k with
  | zero =>
    intro A hA hp
    rw [Finset.card_eq_zero] at hA
    subst hA
    exact absurd hp (Finset.notMem_empty _)
  | succ k ih =>
    intro A hA hp hAC t ht0 htn hmin hmem
    by_cases htlt : t < (ρ.faceWalk e).length
    · -- The last vertex `r = C[t]` is joined by a chord.
      have hrA : (ρ.faceWalk e)[t] ∈ A := hmem htlt
      have hrp : (ρ.faceWalk e)[t] ≠ e.fst := fun h => by
        rw [← hC0 (by omega), hC.getElem_inj_iff] at h
        omega
      have hA' : (A.erase (ρ.faceWalk e)[t]).card = k := by
        rw [Finset.card_erase_of_mem hrA, hA]
        rfl
      have hpA' : e.fst ∈ A.erase (ρ.faceWalk e)[t] := Finset.mem_erase.mpr ⟨hrp.symm, hp⟩
      have hA'C : ∀ x ∈ A.erase (ρ.faceWalk e)[t], x ∈ ρ.faceWalk e := fun x hx =>
        hAC x (Finset.mem_of_mem_erase hx)
      -- The next position of a vertex of `A`, or the end of the walk.
      have hex : ∃ s, t < s ∧ ∀ hs : s < (ρ.faceWalk e).length, (ρ.faceWalk e)[s] ∈ A :=
        ⟨_, htlt, fun hs => absurd hs (lt_irrefl _)⟩
      obtain ⟨htt', ht'A⟩ := Nat.find_spec hex
      have ht'n : Nat.find hex ≤ (ρ.faceWalk e).length :=
        Nat.find_min' hex ⟨htlt, fun hs => absurd hs (lt_irrefl _)⟩
      have hmin' : ∀ x ∈ A.erase (ρ.faceWalk e)[t], x ≠ e.fst →
          Nat.find hex ≤ (ρ.faceWalk e).idxOf x := by
        intro x hx hxp
        have hxA := Finset.mem_of_mem_erase hx
        have hxr := Finset.ne_of_mem_erase hx
        have hxlt : (ρ.faceWalk e).idxOf x < (ρ.faceWalk e).length :=
          List.idxOf_lt_length_iff.mpr (hAC x hxA)
        have hxt : t < (ρ.faceWalk e).idxOf x := by
          rcases (hmin x hxA hxp).lt_or_eq with h | h
          · exact h
          · exfalso
            apply hxr
            simp only [h]
            exact (List.getElem_idxOf hxlt).symm
        refine Nat.find_min' hex ⟨hxt, fun hs => ?_⟩
        rw [List.getElem_idxOf]
        exact hxA
      have hmem' : ∀ ht' : Nat.find hex < (ρ.faceWalk e).length,
          (ρ.faceWalk e)[Nat.find hex] ∈ A.erase (ρ.faceWalk e)[t] := by
        intro ht'
        refine Finset.mem_erase.mpr ⟨fun h => ?_, ht'A ht'⟩
        rw [hC.getElem_inj_iff] at h
        omega
      obtain ⟨τ', hτ', g', c', -, hc', hτ'g⟩ :=
        ih _ hA' hpA' hA'C _ (by omega) ht'n hmin' hmem'
      -- The face of the smaller fan, read from the dart `c'` at the new vertex.
      have hfg : τ'.face g' = c' := by
        have h1 : 1 < (τ'.faceDarts g').length := by rw [hτ'g]; simp
        have h2 := τ'.getElem_faceDarts g' 1 h1
        rw [pow_one] at h2
        rw [← h2, List.getElem_of_eq hτ'g h1]
        rfl
      have htD : t < (ρ.faceDarts e).length := by omega
      obtain ⟨rest, hsplit⟩ : ∃ rest, (ρ.faceDarts e).take (Nat.find hex) =
          (ρ.faceDarts e).take t ++ (ρ.faceDarts e)[t] :: rest := by
        have h1 : t < ((ρ.faceDarts e).take (Nat.find hex)).length := by
          rw [List.length_take]; omega
        refine ⟨((ρ.faceDarts e).take (Nat.find hex)).drop (t + 1), ?_⟩
        conv_lhs => rw [← List.take_append_drop t ((ρ.faceDarts e).take (Nat.find hex))]
        rw [List.take_take, List.drop_eq_getElem_cons h1, List.getElem_take,
          min_eq_left htt'.le]
      have hPQ : τ'.faceDarts c' =
          c' :: ((ρ.faceDarts e).take t).map (attachDart (↑(A.erase (ρ.faceWalk e)[t]) : Set V)) ++
            attachDart (↑(A.erase (ρ.faceWalk e)[t]) : Set V) (ρ.faceDarts e)[t] ::
              (rest.map (attachDart (↑(A.erase (ρ.faceWalk e)[t]) : Set V)) ++ [g']) := by
        have hrot := τ'.faceDarts_face g'
        rw [hfg] at hrot
        rw [hrot, hτ'g, hsplit, List.rotate_cons_succ, List.rotate_zero]
        simp
      -- The chord from the new vertex to `r`.
      have hbfst : (attachDart (↑(A.erase (ρ.faceWalk e)[t]) : Set V) (ρ.faceDarts e)[t]).fst =
          some (ρ.faceWalk e)[t] := by
        rw [fst_attachDart, getElem_faceWalk_eq_fst]
      have hAA' : ∀ x, x ∈ (↑A : Set V) ↔
          x = (ρ.faceWalk e)[t] ∨ x ∈ (↑(A.erase (ρ.faceWalk e)[t]) : Set V) := by
        intro x
        simp only [Finset.mem_coe, Finset.mem_erase]
        constructor
        · intro hx
          by_cases hxr : x = (ρ.faceWalk e)[t]
          · exact Or.inl hxr
          · exact Or.inr ⟨hxr, hx⟩
        · rintro (rfl | ⟨-, hx⟩)
          · exact hrA
          · exact hx
      have hadd : IsAddEdge (attachVertex G ↑(A.erase (ρ.faceWalk e)[t])) (attachVertex G ↑A)
          c'.fst (attachDart (↑(A.erase (ρ.faceWalk e)[t]) : Set V) (ρ.faceDarts e)[t]).fst := by
        rw [hc', hbfst]
        exact isAddEdge_attachVertex hAA'
      have hn : ¬ (attachVertex G ↑(A.erase (ρ.faceWalk e)[t])).Adj c'.fst
          (attachDart (↑(A.erase (ρ.faceWalk e)[t]) : Set V) (ρ.faceDarts e)[t]).fst := by
        rw [hc', hbfst, attachVertex_adj_none_some, Finset.mem_coe]
        exact Finset.notMem_erase _ _
      have hab : τ'.face.SameCycle c'
          (attachDart (↑(A.erase (ρ.faceWalk e)[t]) : Set V) (ρ.faceDarts e)[t]) := by
        rw [← τ'.mem_faceDarts_iff, hPQ]
        simp
      obtain ⟨hF1, -⟩ := τ'.faceDarts_insertChord hadd hn hPQ
      refine ⟨τ'.insertChord hadd hn, hτ'.insertChord hadd hn hab, hadd.dart.symm, hadd.incl c',
        ?_, hc', ?_⟩
      · change (attachDart (↑(A.erase (ρ.faceWalk e)[t]) : Set V) (ρ.faceDarts e)[t]).fst = _
        rw [hbfst, List.getD_eq_getElem _ _ htlt]
      · rw [hF1, List.map_cons, List.map_map]
        rfl
    · -- No vertex beyond the start: a leaf.
      have htC : t = (ρ.faceWalk e).length := le_antisymm htn (not_lt.mp htlt)
      have hS : ∀ x, x ∈ (↑A : Set V) ↔ x = e.fst := by
        intro x
        rw [Finset.mem_coe]
        refine ⟨fun hx => ?_, fun hx => hx ▸ hp⟩
        by_contra hne
        have h1 := hmin x hx hne
        have h2 := List.idxOf_lt_length_iff.mpr (hAC x hx)
        omega
      refine ⟨ρ.insertLeaf hS, hρ.insertLeaf hS, leafDart hS, (leafDart hS).symm, ?_, rfl, ?_⟩
      · rw [fst_leafDart, List.getD_eq_default _ _ (by omega)]
      · rw [faceDarts_insertLeaf, List.take_of_length_le (by omega)]

omit [DecidableEq V] [Finite V] in
/-- **Reading a face from a vertex**: for a vertex `p` of a face walk `C` with distinct vertices,
some dart of the face has tail `p` and walk `C` read from `p`. -/
theorem fan_exists_faceWalk_eq_startAt [DecidableEq V] [Finite V] {d : G.Dart} {p : V}
    (hp : p ∈ ρ.faceWalk d) :
    ∃ e : G.Dart, e.fst = p ∧ ρ.faceWalk e = startAt (ρ.faceWalk d) p := by
  have := finite_dart (G := G)
  refine ⟨(ρ.face ^ (ρ.faceWalk d).idxOf p) d, ?_, ?_⟩
  · rw [← getElem_faceWalk _ _ _ (List.idxOf_lt_length_iff.mpr hp)]
    exact List.getElem_idxOf _
  · rw [faceWalk, faceDarts, orbitList_pow_apply, List.map_rotate]
    rfl

end RotationSystem

open RotationSystem in
/-- **Joining a new vertex to a face, keeping an interval of the face** (the marked fan).  Let a
face of a spherical rotation system have a walk `C` with distinct vertices, let `A` be a set of at
least two of its vertices, and let `p` and `q` be consecutive in `A` around `C`.  Then the new
vertex can be joined to the vertices of `A` by a spherical rotation system with a face whose walk
is the new vertex followed by the whole closed interval of `C` from `p` to `q`.

The construction adds a leaf at `p`, then chords from the new vertex to the other vertices of `A`
in the reverse cyclic order, ending with `q`; each chord cuts off the part of the face beyond its
end, and the last one leaves the face over the interval from `p` to `q`.  The bound `2 ≤ |A|`
already follows from the consecutive pair `p ≠ q`. -/
theorem exists_isSpherical_attachVertex_faceWalk [Finite V] [DecidableEq V]
    {ρ : RotationSystem G} (hρ : ρ.IsSpherical) {d : G.Dart} (hC : (ρ.faceWalk d).Nodup)
    {A : Finset V} (hA : ∀ a ∈ A, a ∈ ρ.faceWalk d) (_hA2 : 2 ≤ A.card) {p q : V}
    (hpq : IsConsecutive (ρ.faceWalk d) A p q) :
    ∃ τ : RotationSystem (attachVertex G ↑A), τ.IsSpherical ∧
      ∃ d' : (attachVertex G ↑A).Dart,
        τ.faceWalk d' ~r none :: (closedArc (ρ.faceWalk d) p q).map some := by
  obtain ⟨hpA, hqA, hpq', hmid⟩ := hpq
  have hpC : p ∈ ρ.faceWalk d := hA p hpA
  have hqC : q ∈ ρ.faceWalk d := hA q hqA
  obtain ⟨e, hep, hwalk⟩ := ρ.fan_exists_faceWalk_eq_startAt hpC
  have hCe : (ρ.faceWalk e).Nodup := by rw [hwalk]; exact nodup_startAt.mpr hC
  have hAe : ∀ x ∈ A, x ∈ ρ.faceWalk e := fun x hx => by
    rw [hwalk]; exact mem_startAt.mpr (hA x hx)
  have ht0 : 0 < cycDist (ρ.faceWalk d) p q := cycDist_pos hC hpC hqC hpq'
  have htn : cycDist (ρ.faceWalk d) p q < (ρ.faceWalk e).length := by
    rw [hwalk, length_startAt]; exact cycDist_lt_length hqC
  have hidx : ∀ x, (ρ.faceWalk e).idxOf x = cycDist (ρ.faceWalk d) p x := fun x => by
    rw [hwalk]; rfl
  have hmin : ∀ x ∈ A, x ≠ e.fst → cycDist (ρ.faceWalk d) p q ≤ (ρ.faceWalk e).idxOf x := by
    intro x hx hxp
    rw [hep] at hxp
    by_contra hlt
    push Not at hlt
    rw [hidx] at hlt
    exact hxp (hmid x hx ((mem_arc_iff hC).mpr ⟨hA x hx, hlt⟩))
  have hq : (ρ.faceWalk e)[cycDist (ρ.faceWalk d) p q] = q := by
    rw [List.getElem_of_eq hwalk]
    exact getElem_startAt_cycDist hqC
  obtain ⟨τ, hτ, g, c, hg, hc, hτg⟩ := ρ.exists_fan_aux hρ e hCe A.card A rfl (hep ▸ hpA) hAe _
    ht0 htn.le hmin (fun _ => by rw [hq]; exact hqA)
  have hgq : g.fst = some q := by rw [hg, List.getD_eq_getElem _ _ htn, hq]
  have hwg : τ.faceWalk g = some q :: none :: (arc (ρ.faceWalk d) p q).map some := by
    have harc : arc (ρ.faceWalk d) p q = (ρ.faceWalk e).take (cycDist (ρ.faceWalk d) p q) := by
      rw [hwalk]
      rfl
    rw [harc, faceWalk, hτg]
    simp only [List.map_cons, hgq, hc, List.map_map, RotationSystem.faceWalk, List.map_take]
    rfl
  refine ⟨τ, hτ, g, ⟨1, ?_⟩⟩
  rw [hwg, List.rotate_cons_succ, List.rotate_zero, closedArc_eq_arc_append hqC, List.map_append]
  rfl

/-- **Joining a new vertex to vertices of a face keeps planarity**: for a face of a spherical
rotation system whose walk has distinct vertices, and a set `A` of at least two of its vertices,
the graph with a new vertex adjacent to the vertices of `A` is planar. -/
theorem isPlanar_attachVertex_of_subset_faceWalk [Finite V] {ρ : RotationSystem G}
    (hρ : ρ.IsSpherical) {d : G.Dart} (hC : (ρ.faceWalk d).Nodup) {A : Finset V}
    (hA : ∀ a ∈ A, a ∈ ρ.faceWalk d) (hA2 : 2 ≤ A.card) : IsPlanar (attachVertex G ↑A) := by
  classical
  obtain ⟨p, hp⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p', q, hpq, hparc⟩ := exists_isConsecutive_mem_arc hC hA (by omega) (hA p hp)
  obtain rfl : p = p' := hpq.2.2.2 p hp hparc
  obtain ⟨τ, hτ, -⟩ := exists_isSpherical_attachVertex_faceWalk hρ hC hA hA2 hpq
  exact ⟨τ, hτ⟩

end MonoidProduct.Graph
