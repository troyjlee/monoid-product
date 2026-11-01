import MonoidProduct.Graph.Surface
set_option linter.style.header false

/-!
# Planarity is invariant under isomorphism

`IsPlanar.of_iso`: an isomorphism `G ≃g G'` carries a spherical rotation system of `G` to one of
`G'`: the darts correspond (`dartEquivOfIso`), the rotation is conjugated, the faces correspond
(`sameCycle_iff_of_semiconj`), and the components, with their vertices, edges and faces,
correspond.  So planarity is a property of the graph, not of its labelling.
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

/-- **Planarity is invariant under isomorphism.** -/
theorem IsPlanar.of_iso (e : G ≃g G') (h : IsPlanar G) : IsPlanar G' := by
  classical
  obtain ⟨ρ, hρ⟩ := h
  set D := dartEquivOfIso e
  have hrot : ∀ x, D.permCongr ρ.rot (D x) = D (ρ.rot x) := fun x => by
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  let ρ' : RotationSystem G' :=
    { rot := D.permCongr ρ.rot
      fst_rot := fun d => by
        rw [Equiv.permCongr_apply, fst_dartEquivOfIso, ρ.fst_rot, fst_dartEquivOfIso_symm,
          e.apply_symm_apply]
      sameCycle_rot := fun d d' hdd' => by
        have hs := ρ.sameCycle_rot (D.symm d) (D.symm d') (by
          rw [fst_dartEquivOfIso_symm, fst_dartEquivOfIso_symm, hdd'])
        have := (sameCycle_iff_of_semiconj hrot D.injective).mpr hs
        rwa [D.apply_symm_apply, D.apply_symm_apply] at this }
  have hface : ∀ x, ρ'.face (D x) = D (ρ.face x) := fun x => by
    rw [RotationSystem.face_apply, RotationSystem.face_apply]
    change D.permCongr ρ.rot (D x).symm = D (ρ.rot x.symm)
    rw [show (D x).symm = D x.symm from rfl, hrot]
  -- The faces correspond.
  let Φ : ρ.Face → ρ'.Face := Quotient.map D fun _ _ h =>
    (sameCycle_iff_of_semiconj hface D.injective).mpr h
  have hΦ : Function.Injective Φ := by
    intro f f' hff
    induction f using Quotient.inductionOn
    induction f' using Quotient.inductionOn
    exact Quotient.sound ((sameCycle_iff_of_semiconj hface D.injective).mp (Quotient.exact hff))
  refine ⟨ρ', fun c' hc' => ?_⟩
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

/-- **Isomorphic graphs are planar together.** -/
theorem isPlanar_iff_of_iso (e : G ≃g G') : IsPlanar G ↔ IsPlanar G' :=
  ⟨IsPlanar.of_iso e, IsPlanar.of_iso e.symm⟩

end MonoidProduct.Graph
