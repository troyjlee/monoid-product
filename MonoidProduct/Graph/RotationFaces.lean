import MonoidProduct.Graph.FaceWalk
import MonoidProduct.Graph.RotationSplit
set_option linter.style.header false

/-!
# Faces of `2`-connected spherical rotation systems, and deleting a vertex

In a spherical rotation system of a `2`-connected graph every face is a cycle of the graph, and
deleting a vertex leaves a spherical rotation system with one face through all the neighbours of
the deleted vertex.

* `RotationSystem.fst_injective_on_face`: **distinct darts of one face have distinct tails**.
  Otherwise splitting their common tail (`Graph/RotationSplit.lean`) would give a rotation system
  of Euler defect `-2`.  Hence every face walk has distinct vertices
  (`RotationSystem.nodup_faceWalk_of_isKConnected`) and is a cycle of the graph
  (`RotationSystem.isCycleList_faceWalk_of_isKConnected`).
* `exists_rotationSystem_induce_ne`: **deleting a vertex** `z` of a spherical rotation system gives
  a spherical rotation system of `G.induce {v | v ≠ z}`, whose rotation at a surviving vertex
  skips the dart to `z`.  The edges at `z` are deleted one at a time
  (`RotationSystem.deleteEdge`); then `z` is isolated, and the restriction to the other vertices
  (`RotationSystem.restrict`) is carried to `G.induce {v | v ≠ z}`.  No connectivity is assumed.
* `exists_induce_ne_faceWalk`: for a `2`-connected graph, **the deleted vertex leaves a face
  through all its neighbours**, for the rotation system above (`exists_mem_faceWalk_induce_ne`).
  The face of a dart `a` leaving `z` meets `z` only in `a` and in the dart arriving just before
  it, so the darts of that face away from `z` join the face after `a` to the face after the dart
  before `a` around `z`; around the rotation at `z`, all the faces after darts leaving `z` become
  one.  The new face may repeat vertices; for a `3`-connected graph it is a cycle
  (`exists_induce_ne_isCycleList_faceWalk`).
* Darts of `G.induce s` are read as darts of `G` by `ofInduceDart`.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*} {G : SimpleGraph V}

/-! ## Faces are cycles -/

/-- **In a spherical rotation system of a `2`-connected graph, distinct darts of one face have
distinct tails**: splitting the common tail of two such darts would give a rotation system of the
split graph with Euler defect `-2 < 0`. -/
theorem RotationSystem.fst_injective_on_face [Finite V] {ρ : RotationSystem G}
    (hρ : ρ.IsSpherical) (hG : IsKConnected G 2) {d e : G.Dart} (hface : ρ.face.SameCycle d e)
    (hfst : d.fst = e.fst) : d = e := by
  classical
  by_contra hne
  have h1 := ρ.eulerDefect_splitRotation hne hfst hface hG
  have h2 := (ρ.splitRotation d e hfst).eulerDefect_nonneg
  rw [(isSpherical_iff_eulerDefect_eq_zero ρ).mp hρ] at h1
  omega

/-- **The face walks of a `2`-connected spherical rotation system have distinct vertices.** -/
theorem RotationSystem.nodup_faceWalk_of_isKConnected [Finite V] {ρ : RotationSystem G}
    (hρ : ρ.IsSpherical) (hG : IsKConnected G 2) (d : G.Dart) : (ρ.faceWalk d).Nodup :=
  ρ.nodup_faceWalk_iff.mpr fun _ _ he he' h =>
    RotationSystem.fst_injective_on_face hρ hG (he.symm.trans he') h

/-- **Every face walk of a `2`-connected spherical rotation system is a cycle of the graph.** -/
theorem RotationSystem.isCycleList_faceWalk_of_isKConnected [Finite V] {ρ : RotationSystem G}
    (hρ : ρ.IsSpherical) (hG : IsKConnected G 2) (d : G.Dart) : IsCycleList G (ρ.faceWalk d) :=
  ρ.isCycleList_faceWalk (RotationSystem.nodup_faceWalk_of_isKConnected hρ hG d)

/-! ## Deleting a vertex -/

section DeleteVertex

/-- A dart of an induced graph, as a dart of `G`. -/
def ofInduceDart {s : Set V} (d : (G.induce s).Dart) : G.Dart := ⟨(d.fst.1, d.snd.1), d.adj⟩

@[simp] theorem fst_ofInduceDart {s : Set V} (d : (G.induce s).Dart) :
    (ofInduceDart d).fst = d.fst.1 :=
  rfl

@[simp] theorem snd_ofInduceDart {s : Set V} (d : (G.induce s).Dart) :
    (ofInduceDart d).snd = d.snd.1 :=
  rfl

theorem ofInduceDart_symm {s : Set V} (d : (G.induce s).Dart) :
    ofInduceDart d.symm = (ofInduceDart d).symm :=
  rfl

theorem ofInduceDart_injective {s : Set V} :
    Function.Injective (ofInduceDart (G := G) (s := s)) := fun _ _ h =>
  Dart.ext _ _ (Prod.ext (Subtype.ext (congrArg (fun e : G.Dart => e.fst) h))
    (Subtype.ext (congrArg (fun e : G.Dart => e.snd) h)))

/-- The identity map between two graphs with the same adjacency, as an isomorphism. -/
def isoOfAdjIff {W : Type*} {H H' : SimpleGraph W} (h : ∀ u w, H'.Adj u w ↔ H.Adj u w) :
    H ≃g H' where
  toEquiv := Equiv.refl W
  map_rel_iff' {u w} := h u w

/-- **Deleting a vertex, by induction on its degree**: for a graph `H` that agrees with `G` away
from `z`, a spherical rotation system `τ` of `H` gives one of `G.induce {v | v ≠ z}` whose
rotation at a surviving vertex skips the dart to `z`.  An edge `zw` of `H` is deleted first, which
removes the dart to `z` from the rotation at `w`. -/
private theorem exists_rotationSystem_induce_ne_aux [Finite V] (z : V) (n : ℕ) :
    ∀ (H : SimpleGraph V) (τ : RotationSystem H),
      (∀ u w, u ≠ z → w ≠ z → (H.Adj u w ↔ G.Adj u w)) → (H.neighborSet z).ncard = n →
      τ.IsSpherical →
      ∃ σ : RotationSystem (G.induce {v | v ≠ z}), σ.IsSpherical ∧
        ∀ (d : (G.induce {v | v ≠ z}).Dart) (x : H.Dart), x.fst = d.fst.1 → x.snd = d.snd.1 →
          ((τ.rot x).snd = z → ((σ.rot d).snd : V) = (τ.rot (τ.rot x)).snd) ∧
          ((τ.rot x).snd ≠ z → ((σ.rot d).snd : V) = (τ.rot x).snd) := by
  classical
  induction n with
  | zero =>
    intro H τ hHG hn hτ
    -- `z` is isolated in `H`, so the other vertices form a set that no edge leaves.
    have hz : ∀ w, ¬ H.Adj z w := fun w hw => by
      have hw' : w ∈ H.neighborSet z := hw
      rw [(Set.ncard_eq_zero (Set.toFinite _)).mp hn] at hw'
      exact hw'
    have hs : ∀ ⦃u w⦄, H.Adj u w → u ∈ {v | v ≠ z} → w ∈ {v | v ≠ z} := fun u w huw _ hwz =>
      hz u (hwz ▸ huw.symm)
    let e : H.induce {v | v ≠ z} ≃g G.induce {v | v ≠ z} :=
      isoOfAdjIff fun u w => (hHG u.1 w.1 u.2 w.2).symm
    refine ⟨(τ.restrict _ hs).mapIso e, (hτ.restrict hs).mapIso e, fun d x hx1 hx2 => ?_⟩
    have hne : (τ.rot x).snd ≠ z := fun h => hz _ (h ▸ (τ.rot x).adj).symm
    refine ⟨fun h => absurd h hne, fun _ => ?_⟩
    obtain rfl : x = ⟨(d.fst.1, d.snd.1), (hHG _ _ d.fst.2 d.snd.2).mpr d.adj⟩ :=
      Dart.ext _ _ (Prod.ext hx1 hx2)
    rfl
  | succ n ih =>
    intro H τ hHG hn hτ
    obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (s := H.neighborSet z) (by omega)
    have hw' : H.Adj z w := hw
    have hzw : w ≠ z := hw'.ne.symm
    obtain ⟨a, ha1, ha2⟩ : ∃ a : H.Dart, a.fst = z ∧ a.snd = w := ⟨⟨(z, w), hw'⟩, rfl, rfl⟩
    have hedge : a.edge = s(z, w) := by
      rw [← ha1, ← ha2]
      rfl
    -- Deleting the edge `zw` keeps the graph away from `z`, and lowers the degree of `z`.
    have hH1 : ∀ u w', u ≠ z → w' ≠ z →
        ((H.deleteEdges {a.edge}).Adj u w' ↔ G.Adj u w') := by
      intro u w' hu hw''
      rw [deleteEdges_adj, Set.mem_singleton_iff, ← hHG u w' hu hw'', hedge]
      refine ⟨And.left, fun h => ⟨h, fun he => ?_⟩⟩
      rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hu h1
      · exact hw'' h2
    have hn1 : ((H.deleteEdges {a.edge}).neighborSet z).ncard = n := by
      have hnb : (H.deleteEdges {a.edge}).neighborSet z = H.neighborSet z \ {w} := by
        ext w'
        simp only [mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff, Set.mem_sdiff, hedge]
        exact and_congr_right fun _ => not_congr Sym2.congr_right
      rw [hnb, Set.ncard_sdiff_singleton_of_mem hw, hn, Nat.add_sub_cancel]
    obtain ⟨σ, hσ, hform⟩ :=
      ih (H.deleteEdges {a.edge}) (τ.deleteEdge a) hH1 hn1 (hτ.deleteEdge a)
    refine ⟨σ, hσ, fun d x hx1 hx2 => ?_⟩
    have hxz : x.fst ≠ z := fun h => d.fst.2 (hx1.symm.trans h)
    have hxz' : x.snd ≠ z := fun h => d.snd.2 (hx2.symm.trans h)
    have hxa : x ≠ a := fun h => hxz (by rw [h]; exact ha1)
    have hxb : x ≠ a.symm := fun h => hxz' (by rw [h]; exact ha1)
    -- After deleting `zw`, the rotation at a vertex other than `z` skips the dart to `z` at `w`.
    have hB : ∀ y : H.Dart, y.fst ≠ z → y ≠ a.symm →
        bypass (bypass τ.rot a) a.symm y =
          if τ.rot y = a.symm then τ.rot a.symm else τ.rot y := by
      intro y hy hya
      have hya' : y ≠ a := fun h => hy (by rw [h]; exact ha1)
      have h1 : bypass τ.rot a y = τ.rot y :=
        (bypass_apply_of_ne _ hya').trans (ite_eq_right fun h => hy
          ((τ.fst_rot y).symm.trans ((congrArg (fun d : H.Dart => d.fst) h).trans ha1)))
      have h2 : bypass τ.rot a a.symm = τ.rot a.symm :=
        (bypass_apply_of_ne _ a.symm_ne).trans (ite_eq_right fun h => hzw
          (ha2.symm.trans ((τ.fst_rot a.symm).symm.trans
            ((congrArg (fun d : H.Dart => d.fst) h).trans ha1))))
      rw [bypass_apply_of_ne _ hya, h1, h2]
    have e1 : ((τ.deleteEdge a).rot (deleteEdgeDartEquiv a ⟨x, hxa, hxb⟩)).snd =
        (bypass (bypass τ.rot a) a.symm x).snd :=
      rfl
    have e2 : ((τ.deleteEdge a).rot ((τ.deleteEdge a).rot
        (deleteEdgeDartEquiv a ⟨x, hxa, hxb⟩))).snd =
        (bypass (bypass τ.rot a) a.symm (bypass (bypass τ.rot a) a.symm x)).snd :=
      rfl
    obtain ⟨hf1, hf2⟩ := hform d (deleteEdgeDartEquiv a ⟨x, hxa, hxb⟩) hx1 hx2
    rw [e1, e2] at hf1
    rw [e1] at hf2
    have hBx := hB x hxz hxb
    by_cases hpx : τ.rot x = a.symm
    · rw [ite_eq_left hpx] at hBx
      -- The dart after the one to `z` at `w` does not go to `z`.
      have hpa : (τ.rot a.symm).snd ≠ z := by
        intro h
        refine hxb (τ.rot.injective (hpx.trans ?_))
        exact (Dart.ext _ _ (Prod.ext (τ.fst_rot a.symm) (h.trans ha1.symm))).symm
      refine ⟨fun _ => ?_, fun h => absurd (by rw [hpx]; exact ha1) h⟩
      rw [hpx, hf2 (by rw [hBx]; exact hpa), hBx]
    · rw [ite_eq_right hpx] at hBx
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hppx : τ.rot (τ.rot x) ≠ a.symm := by
          intro h'
          refine hpx (Dart.ext _ _ (Prod.ext ?_ (h.trans ha1.symm)))
          exact (τ.fst_rot (τ.rot x)).symm.trans (congrArg (fun d : H.Dart => d.fst) h')
        rw [hf1 (by rw [hBx]; exact h), hBx,
          hB (τ.rot x) (by rw [τ.fst_rot]; exact hxz) hpx, ite_eq_right hppx]
      · rw [hf2 (by rw [hBx]; exact h), hBx]

/-- **Deleting a vertex keeps a spherical rotation system spherical**: `G.induce {v | v ≠ z}` has
a spherical rotation system whose rotation at each surviving vertex is that of `ρ`, skipping the
dart to `z`. -/
theorem exists_rotationSystem_induce_ne [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical)
    (z : V) :
    ∃ σ : RotationSystem (G.induce {v | v ≠ z}), σ.IsSpherical ∧
      ∀ d : (G.induce {v | v ≠ z}).Dart,
        ((ρ.rot (ofInduceDart d)).snd = z →
          ofInduceDart (σ.rot d) = ρ.rot (ρ.rot (ofInduceDart d))) ∧
        ((ρ.rot (ofInduceDart d)).snd ≠ z → ofInduceDart (σ.rot d) = ρ.rot (ofInduceDart d)) := by
  obtain ⟨σ, hσ, hform⟩ := exists_rotationSystem_induce_ne_aux (G := G) z _ G ρ
    (fun _ _ _ _ => Iff.rfl) rfl hρ
  refine ⟨σ, hσ, fun d => ?_⟩
  obtain ⟨h1, h2⟩ := hform d (ofInduceDart d) rfl rfl
  have hfst : ((σ.rot d).fst : V) = d.fst.1 := congrArg Subtype.val (σ.fst_rot d)
  refine ⟨fun h => Dart.ext _ _ (Prod.ext ?_ (h1 h)), fun h => Dart.ext _ _ (Prod.ext ?_ (h2 h))⟩
  · exact hfst.trans ((ρ.fst_rot (ρ.rot (ofInduceDart d))).trans (ρ.fst_rot (ofInduceDart d))).symm
  · exact hfst.trans (ρ.fst_rot (ofInduceDart d)).symm

/-- **Following a face around the deleted vertex**: in `G − z`, the face after a dart `a` leaving
`z` contains the face after the dart before `a` around `z`.  The face of `ρ` through `a` meets `z`
only in `a` and in the dart arriving before `a`, and between them its darts are darts of `G − z`,
on which the face permutation of `σ` is that of `ρ`. -/
private theorem sameCycle_face_induce_ne [Finite V] {ρ : RotationSystem G} {z : V}
    {σ : RotationSystem (G.induce {v | v ≠ z})}
    (hsimple : ∀ e e' : G.Dart, ρ.face.SameCycle e e' → e.fst = e'.fst → e = e')
    (hrot : ∀ y : G.Dart, ρ.rot y ≠ y)
    (hface : ∀ d : (G.induce {v | v ≠ z}).Dart,
      ((ρ.face (ofInduceDart d)).snd = z →
        ofInduceDart (σ.face d) = ρ.rot (ρ.face (ofInduceDart d))) ∧
      ((ρ.face (ofInduceDart d)).snd ≠ z → ofInduceDart (σ.face d) = ρ.face (ofInduceDart d)))
    {a : G.Dart} (ha : a.fst = z) {d d' : (G.induce {v | v ≠ z}).Dart}
    (hd : ofInduceDart d = ρ.face a) (hd' : ofInduceDart d' = ρ.face (ρ.rot.symm a)) :
    σ.face.SameCycle d d' := by
  have := finite_dart (G := G)
  have hpow : ∀ (n : ℕ) (y : G.Dart), (ρ.face ^ (n + 1)) y = ρ.face ((ρ.face ^ n) y) :=
    fun n y => by rw [pow_succ', mul_apply]
  -- The face after `a` starts away from `z`, since no vertex has degree one.
  have hx₀ : (ρ.face a).fst ≠ z := by
    rw [ρ.fst_face]
    exact fun h => a.adj.ne (ha.trans h.symm)
  have hx₀' : (ρ.face a).snd ≠ z := fun h =>
    hrot a.symm (Dart.ext _ _ (Prod.ext (ρ.fst_rot a.symm) (h.trans ha.symm)))
  -- The face returns to `z` for the first time at `a`.
  obtain ⟨N, hN, hNa⟩ := exists_pos_pow_apply_eq_self ρ.face a
  have hN1 : 1 < N := by
    by_contra hle
    obtain rfl : N = 1 := by omega
    rw [pow_one] at hNa
    exact ρ.face_ne a hNa
  have hret : (ρ.face ^ (N - 1)) (ρ.face a) = a := by
    rw [← mul_apply, ← pow_succ, Nat.sub_add_cancel hN1.le, hNa]
  obtain ⟨m, hm0, hmS, hmin⟩ := exists_first_pow_mem ρ.face (S := {y | y.fst = z})
    (x := ρ.face a) ⟨N - 1, by omega, by rw [Set.mem_ofPred_eq, hret]; exact ha⟩
  have hma : (ρ.face ^ m) (ρ.face a) = a :=
    (hsimple _ _ (sameCycle_pow_right.mpr (sameCycle_apply_right.mpr (SameCycle.refl _ a)))
      (ha.trans (Set.mem_ofPred_eq.mp hmS).symm)).symm
  -- Before that, the darts of the face avoid `z`.
  have hsnd : ∀ i, i + 1 < m → ((ρ.face ^ i) (ρ.face a)).snd ≠ z := by
    intro i hi h
    refine hmin (i + 1) (Nat.succ_pos i) hi ?_
    rw [Set.mem_ofPred_eq, hpow, ρ.fst_face]
    exact h
  have hm2 : 2 ≤ m := by
    by_contra hlt
    obtain rfl : m = 1 := by omega
    have h := Set.mem_ofPred_eq.mp hmS
    rw [pow_one, ρ.fst_face] at h
    exact hx₀' h
  -- Along these darts, the face of `σ` follows the face of `ρ`.
  have hiter : ∀ i, i + 1 < m → ofInduceDart ((σ.face ^ i) d) = (ρ.face ^ i) (ρ.face a) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [pow_zero, one_apply, pow_zero, one_apply]
      exact hd
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hcond : (ρ.face (ofInduceDart ((σ.face ^ i) d))).snd ≠ z := by
        rw [ih', ← hpow]
        exact hsnd (i + 1) hi
      rw [pow_succ', mul_apply, (hface _).2 hcond, ih', hpow]
  -- At the last of them, the face of `σ` skips `z` and continues after the dart before `a`.
  have hlast : ofInduceDart ((σ.face ^ (m - 1)) d) = ρ.face (ρ.rot.symm a) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hk := hiter k (by omega)
    have hy : ((ρ.face ^ (k + 1)) (ρ.face a)).snd = z := by
      rw [← ρ.fst_face, ← hpow]
      exact Set.mem_ofPred_eq.mp hmS
    have hy' : ρ.face ((ρ.face ^ (k + 1)) (ρ.face a)) = a := by
      rw [← hpow]
      exact hma
    have hcond : (ρ.face (ofInduceDart ((σ.face ^ k) d))).snd = z := by
      rw [hk, ← hpow]
      exact hy
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ', mul_apply, (hface _).1 hcond, hk, ← hpow]
    generalize (ρ.face ^ (k + 1)) (ρ.face a) = y at hy' ⊢
    have hys : y.symm = ρ.rot.symm a := by
      rw [← hy', RotationSystem.face_apply, Equiv.symm_apply_apply]
    rw [RotationSystem.face_apply, ← hys, Dart.symm_symm]
  rw [← ofInduceDart_injective (hlast.trans hd'.symm)]
  exact sameCycle_pow_right.mpr (SameCycle.refl _ _)

/-- **The face through the neighbours of a deleted vertex**: if `ρ` is a spherical rotation system
of a `2`-connected graph and the rotation system `σ` of `G.induce {v | v ≠ z}` is that of `ρ`
skipping the darts to `z`, then some face walk of `σ` passes through every neighbour of `z`. -/
theorem exists_mem_faceWalk_induce_ne [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical)
    (hG : IsKConnected G 2) {z : V} {σ : RotationSystem (G.induce {v | v ≠ z})}
    (hrotσ : ∀ d : (G.induce {v | v ≠ z}).Dart,
      ((ρ.rot (ofInduceDart d)).snd = z →
        ofInduceDart (σ.rot d) = ρ.rot (ρ.rot (ofInduceDart d))) ∧
      ((ρ.rot (ofInduceDart d)).snd ≠ z → ofInduceDart (σ.rot d) = ρ.rot (ofInduceDart d))) :
    ∃ d₀ : (G.induce {v | v ≠ z}).Dart, ∀ w (hw : G.Adj z w),
      (⟨w, hw.ne'⟩ : ↥({v | v ≠ z} : Set V)) ∈ σ.faceWalk d₀ := by
  have := finite_dart (G := G)
  have hdeg := hG.le_ncard_neighborSet
  -- Every vertex has two neighbours, so the rotation fixes no dart.
  have hrot : ∀ y : G.Dart, ρ.rot y ≠ y := fun y h => by
    have hsub : G.neighborSet y.fst ⊆ {y.snd} := fun w hw => (ρ.rot_eq_self_iff y).mp h w hw
    have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    rw [Set.ncard_singleton] at h1
    have := hdeg y.fst
    omega
  have hsimple : ∀ e e' : G.Dart, ρ.face.SameCycle e e' → e.fst = e'.fst → e = e' :=
    fun _ _ h h' => RotationSystem.fst_injective_on_face hρ hG h h'
  -- The face permutation of `σ` is that of `ρ`, skipping the darts at `z`.
  have hface : ∀ d : (G.induce {v | v ≠ z}).Dart,
      ((ρ.face (ofInduceDart d)).snd = z →
        ofInduceDart (σ.face d) = ρ.rot (ρ.face (ofInduceDart d))) ∧
      ((ρ.face (ofInduceDart d)).snd ≠ z → ofInduceDart (σ.face d) = ρ.face (ofInduceDart d)) :=
    fun d => hrotσ d.symm
  -- The dart after a dart leaving `z` along its face is a dart of `G − z`.
  have hlift : ∀ b : G.Dart, b.fst = z →
      ∃ d : (G.induce {v | v ≠ z}).Dart, ofInduceDart d = ρ.face b := by
    intro b hb
    have h1 : (ρ.face b).fst ≠ z := by
      rw [ρ.fst_face]
      exact fun h => b.adj.ne (hb.trans h.symm)
    have h2 : (ρ.face b).snd ≠ z := fun h =>
      hrot b.symm (Dart.ext _ _ (Prod.ext (ρ.fst_rot b.symm) (h.trans hb.symm)))
    exact ⟨⟨(⟨_, h1⟩, ⟨_, h2⟩), (ρ.face b).adj⟩, rfl⟩
  obtain ⟨w₀, hw₀⟩ := Set.nonempty_of_ncard_ne_zero (s := G.neighborSet z)
    (by have := hdeg z; omega)
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : G.Dart, a₀.fst = z := ⟨⟨(z, w₀), hw₀⟩, rfl⟩
  obtain ⟨d₀, hd₀⟩ := hlift a₀ ha₀
  refine ⟨d₀, fun w hw => ?_⟩
  -- Around the rotation at `z`, the faces after the darts leaving `z` are one face of `σ`.
  have hfst_pow : ∀ k : ℕ, ((ρ.rot ^ k) a₀).fst = z := fun k =>
    (eq_of_sameCycle_of_forall (g := fun d : G.Dart => d.fst) ρ.fst_rot
      (sameCycle_pow_right.mpr (SameCycle.refl _ a₀))).symm.trans ha₀
  have hP : ∀ k : ℕ, ∀ d, ofInduceDart d = ρ.face ((ρ.rot ^ k) a₀) → σ.face.SameCycle d₀ d := by
    intro k
    induction k with
    | zero =>
      intro d hd
      rw [pow_zero, one_apply, ← hd₀] at hd
      rw [ofInduceDart_injective hd]
    | succ k ih =>
      intro d hd
      obtain ⟨d', hd'⟩ := hlift _ (hfst_pow k)
      have hsc := sameCycle_face_induce_ne hsimple hrot hface (hfst_pow (k + 1)) hd
        (by rw [hd', pow_succ', mul_apply, Equiv.symm_apply_apply])
      exact (ih d' hd').trans hsc.symm
  obtain ⟨k, hk⟩ := (ρ.sameCycle_rot a₀ ⟨(z, w), hw⟩ ha₀).exists_nat_pow_eq
  obtain ⟨d, hd⟩ := hlift ⟨(z, w), hw⟩ rfl
  refine σ.mem_faceWalk_iff.mpr ⟨d, hP k d (by rw [hk]; exact hd), Subtype.ext ?_⟩
  change (ofInduceDart d).fst = w
  rw [hd, ρ.fst_face]

/-- **Deleting a vertex of a `2`-connected graph leaves a face through all its neighbours**: a
spherical rotation system of a `2`-connected graph gives one of `G.induce {v | v ≠ z}` with a face
whose walk passes through every neighbour of `z`.  The face may repeat vertices. -/
theorem exists_induce_ne_faceWalk [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical)
    (hG : IsKConnected G 2) (z : V) :
    ∃ σ : RotationSystem (G.induce {v | v ≠ z}), σ.IsSpherical ∧
      ∃ d₀ : (G.induce {v | v ≠ z}).Dart, ∀ w (hw : G.Adj z w),
        (⟨w, hw.ne'⟩ : ↥({v | v ≠ z} : Set V)) ∈ σ.faceWalk d₀ := by
  obtain ⟨σ, hσ, hrotσ⟩ := exists_rotationSystem_induce_ne hρ z
  exact ⟨σ, hσ, exists_mem_faceWalk_induce_ne hρ hG hrotσ⟩

/-- **Deleting a vertex of a `3`-connected graph leaves a cycle through all its neighbours** as a
face: the graph left is `2`-connected, so the face through the neighbours is a cycle. -/
theorem exists_induce_ne_isCycleList_faceWalk [Finite V] {ρ : RotationSystem G}
    (hρ : ρ.IsSpherical) (hG : IsKConnected G 3) (z : V) :
    ∃ σ : RotationSystem (G.induce {v | v ≠ z}), σ.IsSpherical ∧
      ∃ d₀ : (G.induce {v | v ≠ z}).Dart, IsCycleList (G.induce {v | v ≠ z}) (σ.faceWalk d₀) ∧
        ∀ w (hw : G.Adj z w), (⟨w, hw.ne'⟩ : ↥({v | v ≠ z} : Set V)) ∈ σ.faceWalk d₀ := by
  obtain ⟨σ, hσ, d₀, hd₀⟩ := exists_induce_ne_faceWalk hρ (hG.mono (by norm_num)) z
  exact ⟨σ, hσ, d₀,
    RotationSystem.isCycleList_faceWalk_of_isKConnected hσ (hG.induce_ne z) d₀, hd₀⟩

end DeleteVertex

end MonoidProduct.Graph
