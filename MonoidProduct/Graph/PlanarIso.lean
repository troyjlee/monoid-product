import MonoidProduct.Graph.Surface
set_option linter.style.header false

/-!
# Planarity is invariant under isomorphism

An isomorphism `G ≃g G'` carries a rotation system of `G` to one of `G'`
(`RotationSystem.mapIso`): the darts correspond (`dartEquivOfIso`) and the rotation is
conjugated, so the faces correspond (`mapIso_face_apply`, `sameCycle_iff_of_semiconj`).  The
components, with their vertices, edges and faces, correspond too, so a spherical rotation system
stays spherical (`RotationSystem.IsSpherical.mapIso`), and `IsPlanar.of_iso` follows: planarity
is a property of the graph, not of its labelling.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- **The darts of isomorphic graphs correspond.** -/
def dartEquivOfIso (e : G ≃g G') : G.Dart ≃ G'.Dart where
  toFun := e.toHom.mapDart
  invFun := e.symm.toHom.mapDart
  left_inv d := Dart.ext _ _ (Prod.ext (e.symm_apply_apply d.fst) (e.symm_apply_apply d.snd))
  right_inv d := Dart.ext _ _ (Prod.ext (e.apply_symm_apply d.fst) (e.apply_symm_apply d.snd))

@[simp] theorem fst_dartEquivOfIso (e : G ≃g G') (d : G.Dart) :
    (dartEquivOfIso e d).fst = e d.fst := rfl

@[simp] theorem fst_dartEquivOfIso_symm (e : G ≃g G') (d : G'.Dart) :
    ((dartEquivOfIso e).symm d).fst = e.symm d.fst := rfl

theorem dartEquivOfIso_symm_symm (e : G ≃g G') (d : G'.Dart) :
    (dartEquivOfIso e).symm d.symm = ((dartEquivOfIso e).symm d).symm := rfl

/-- Components correspond under an isomorphism. -/
private theorem connectedComponentEquiv_mk (e : G ≃g G') (v : V) :
    e.connectedComponentEquiv (G.connectedComponentMk v) = G'.connectedComponentMk (e v) := rfl

namespace RotationSystem

/-- **A rotation system carried along an isomorphism**: the rotation conjugated by the
correspondence of darts. -/
def mapIso (e : G ≃g G') (ρ : RotationSystem G) : RotationSystem G' where
  rot := (dartEquivOfIso e).permCongr ρ.rot
  fst_rot d := by
    rw [Equiv.permCongr_apply, fst_dartEquivOfIso, ρ.fst_rot, fst_dartEquivOfIso_symm,
      e.apply_symm_apply]
  sameCycle_rot d d' hdd' := by
    have hrot : ∀ x, (dartEquivOfIso e).permCongr ρ.rot (dartEquivOfIso e x) =
        dartEquivOfIso e (ρ.rot x) := fun x => by
      rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    have hs := ρ.sameCycle_rot ((dartEquivOfIso e).symm d) ((dartEquivOfIso e).symm d') (by
      rw [fst_dartEquivOfIso_symm, fst_dartEquivOfIso_symm, hdd'])
    have := (sameCycle_iff_of_semiconj hrot (dartEquivOfIso e).injective).mpr hs
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this

theorem mapIso_rot_apply (e : G ≃g G') (ρ : RotationSystem G) (d : G.Dart) :
    (ρ.mapIso e).rot (dartEquivOfIso e d) = dartEquivOfIso e (ρ.rot d) := by
  change (dartEquivOfIso e).permCongr ρ.rot _ = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- **Faces correspond under an isomorphism**: the face permutation is conjugated too. -/
theorem mapIso_face_apply (e : G ≃g G') (ρ : RotationSystem G) (d : G.Dart) :
    (ρ.mapIso e).face (dartEquivOfIso e d) = dartEquivOfIso e (ρ.face d) := by
  rw [face_apply, face_apply]
  exact mapIso_rot_apply e ρ d.symm

theorem face_mapIso (e : G ≃g G') (ρ : RotationSystem G) :
    (ρ.mapIso e).face = (dartEquivOfIso e).permCongr ρ.face := by
  refine Equiv.ext fun d => ?_
  rw [Equiv.permCongr_apply, ← mapIso_face_apply, Equiv.apply_symm_apply]

/-- **A spherical rotation system stays spherical under an isomorphism.** -/
theorem IsSpherical.mapIso (e : G ≃g G') {ρ : RotationSystem G} (hρ : ρ.IsSpherical) :
    (ρ.mapIso e).IsSpherical := by
  classical
  set D := dartEquivOfIso e
  set ρ' := ρ.mapIso e
  have hface : ∀ x, ρ'.face (D x) = D (ρ.face x) := mapIso_face_apply e ρ
  -- The faces correspond.
  let Φ : ρ.Face → ρ'.Face := Quotient.map D fun _ _ h =>
    (sameCycle_iff_of_semiconj hface D.injective).mpr h
  have hΦ : Function.Injective Φ := by
    intro f f' hff
    induction f using Quotient.inductionOn
    induction f' using Quotient.inductionOn
    exact Quotient.sound ((sameCycle_iff_of_semiconj hface D.injective).mp (Quotient.exact hff))
  intro c' hc'
  set c := e.connectedComponentEquiv.symm c'
  have hcc : e.connectedComponentEquiv c = c' := Equiv.apply_symm_apply _ _
  have hmk : ∀ v, G'.connectedComponentMk (e v) = c' ↔ G.connectedComponentMk v = c := fun v => by
    rw [← connectedComponentEquiv_mk, ← hcc, Equiv.apply_eq_iff_eq]
  have hsupp : c'.supp = e '' c.supp := by
    ext v'
    rw [ConnectedComponent.mem_supp_iff]
    constructor
    · intro hv
      refine ⟨e.symm v', (ConnectedComponent.mem_supp_iff _ _).mpr ?_, e.apply_symm_apply v'⟩
      rw [← hmk, e.apply_symm_apply]
      exact hv
    · rintro ⟨v, hv, rfl⟩
      exact (hmk v).mpr ((ConnectedComponent.mem_supp_iff _ _).mp hv)
  have hedges : componentEdges G' c' = Sym2.map e '' componentEdges G c := by
    ext e'
    induction e' using Sym2.ind with
    | h a b =>
    constructor
    · rintro ⟨hab, hc⟩
      refine ⟨s(e.symm a, e.symm b), ⟨?_, fun z hz => ?_⟩, by simp⟩
      · rw [mem_edgeSet, e.symm.map_adj_iff]
        exact hab
      · rcases Sym2.mem_iff.mp hz with rfl | rfl
        · rw [← hmk, e.apply_symm_apply]
          exact hc a (Sym2.mem_mk_left a b)
        · rw [← hmk, e.apply_symm_apply]
          exact hc b (Sym2.mem_mk_right a b)
    · rintro ⟨f, ⟨hf, hc⟩, hfe⟩
      induction f using Sym2.ind with
      | h u w =>
      rw [Sym2.map_mk] at hfe
      rw [← hfe]
      refine ⟨by rw [mem_edgeSet, e.map_adj_iff]; exact hf, fun z hz => ?_⟩
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact (hmk u).mpr (hc u (Sym2.mem_mk_left u w))
      · exact (hmk w).mpr (hc w (Sym2.mem_mk_right u w))
  have hfaces : ρ'.facesIn c' = Φ '' ρ.facesIn c := by
    ext f'
    induction f' using Quotient.inductionOn with
    | h d' =>
    constructor
    · intro hf
      refine ⟨⟦D.symm d'⟧, ?_, by simp [Φ]⟩
      change G.connectedComponentMk (D.symm d').fst = c
      rw [fst_dartEquivOfIso_symm, ← hmk, e.apply_symm_apply]
      exact hf
    · rintro ⟨f, hf, hff⟩
      induction f using Quotient.inductionOn with
      | h d =>
      rw [← hff]
      change G'.connectedComponentMk (D d).fst = c'
      rw [fst_dartEquivOfIso]
      exact (hmk d.fst).mpr hf
  have hne : (componentEdges G c).Nonempty := by
    obtain ⟨x, hx⟩ := hc'
    rw [hedges] at hx
    obtain ⟨y, hy, -⟩ := hx
    exact ⟨y, hy⟩
  have heul := hρ c hne
  rw [hsupp, hedges, hfaces, Set.ncard_image_of_injective _ e.injective,
    Set.ncard_image_of_injective _ (Sym2.map.injective e.injective), hΦ.injOn.ncard_image]
  exact heul

end RotationSystem

/-- **Planarity is invariant under isomorphism.** -/
theorem IsPlanar.of_iso (e : G ≃g G') (h : IsPlanar G) : IsPlanar G' := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ.mapIso e, hρ.mapIso e⟩

/-- **Isomorphic graphs are planar together.** -/
theorem isPlanar_iff_of_iso (e : G ≃g G') : IsPlanar G ↔ IsPlanar G' :=
  ⟨IsPlanar.of_iso e, IsPlanar.of_iso e.symm⟩

end MonoidProduct.Graph
