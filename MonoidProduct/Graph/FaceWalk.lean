import MonoidProduct.Graph.CycleArcs
import MonoidProduct.Graph.PlanarIso
import MonoidProduct.Graph.RotationDeletion
set_option linter.style.header false

/-!
# Face walks of a rotation system

The faces of a rotation system are the cycles of its face permutation.  Read in order from a
chosen dart, a face is a list of darts, and their tails form a closed walk around the face.

* `orbitList p x`: the orbit `x, p x, p² x, …` of a permutation, for one period.  Its entries are
  distinct (`nodup_orbitList`), its members are the elements of the cycle of `x`
  (`mem_orbitList_iff`), it rotates as its start moves along the cycle (`orbitList_apply`,
  `orbitList_pow_apply`, `isRotated_orbitList`), and each entry is followed by its image
  (`getElem_orbitList_succ_mod`).  Conversely, a list of distinct entries that `p` shifts
  cyclically is an orbit (`orbitList_eq_of_getElem`, `isRotated_orbitList_of_mem`); this
  identifies the faces of a modified rotation system.  Orbits correspond under conjugation
  (`orbitList_permCongr`).
* `RotationSystem.faceDarts ρ d`: the darts of the face through `d`, in order from `d`, and
  `RotationSystem.faceWalk ρ d`: their tails.  A face has at least two darts
  (`two_le_length_faceDarts`); the head of each dart is the tail of the next
  (`snd_getElem_faceDarts`), so consecutive vertices of a face walk, cyclically, are adjacent
  (`adj_getElem_faceWalk`).  A face walk with distinct vertices is a cycle of the graph
  (`isCycleList_faceWalk`).  Face walks through darts of one face are rotations of each other
  (`isRotated_faceWalk`).
* Under an isomorphism, the face walks of the transported rotation system are the images of the
  old ones (`faceDarts_mapIso`, `faceWalk_mapIso`).
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm Function

variable {α β : Type*}

/-! ## Orbits as lists -/

/-- **The orbit of `x` under `p`, as a list**: `x, p x, p² x, …`, for one period. -/
noncomputable def orbitList (p : Perm α) (x : α) : List α :=
  (List.range (minimalPeriod p x)).map fun k => (p ^ k) x

@[simp] theorem length_orbitList (p : Perm α) (x : α) :
    (orbitList p x).length = minimalPeriod p x := by
  simp [orbitList]

@[simp] theorem getElem_orbitList (p : Perm α) (x : α) (k : ℕ)
    (hk : k < (orbitList p x).length) : (orbitList p x)[k] = (p ^ k) x := by
  simp [orbitList]

/-- After one period, the orbit is back at its start. -/
theorem pow_minimalPeriod_apply (p : Perm α) (x : α) : (p ^ minimalPeriod p x) x = x := by
  rw [coe_pow]
  exact iterate_minimalPeriod

/-- Iterates are periodic with the minimal period. -/
theorem pow_apply_eq_pow_mod_minimalPeriod (p : Perm α) (x : α) (n : ℕ) :
    (p ^ n) x = (p ^ (n % minimalPeriod p x)) x :=
  pow_apply_eq_pow_mod_apply p (pow_minimalPeriod_apply p x) n

/-- In a finite set every element is periodic. -/
theorem mem_periodicPts_perm [Finite α] (p : Perm α) (x : α) : x ∈ periodicPts p := by
  obtain ⟨n, hn, h⟩ := exists_pos_pow_apply_eq_self p x
  refine ⟨n, hn, ?_⟩
  change (⇑p)^[n] x = x
  rw [← coe_pow]
  exact h

theorem minimalPeriod_perm_pos [Finite α] (p : Perm α) (x : α) : 0 < minimalPeriod p x :=
  minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts_perm p x)

theorem orbitList_ne_nil [Finite α] (p : Perm α) (x : α) : orbitList p x ≠ [] := by
  rw [← List.length_pos_iff, length_orbitList]
  exact minimalPeriod_perm_pos p x

/-- **The entries of an orbit are distinct.** -/
theorem nodup_orbitList (p : Perm α) (x : α) : (orbitList p x).Nodup := by
  refine List.Nodup.map_on (fun i hi j hj hij => ?_) List.nodup_range
  rw [List.mem_range] at hi hj
  simp only [coe_pow] at hij
  exact iterate_injOn_Iio_minimalPeriod hi hj hij

/-- **The members of an orbit** are the elements of the cycle. -/
theorem mem_orbitList_iff [Finite α] {p : Perm α} {x y : α} :
    y ∈ orbitList p x ↔ p.SameCycle x y := by
  constructor
  · intro hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    rw [getElem_orbitList]
    exact ⟨k, by simp⟩
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    rw [pow_apply_eq_pow_mod_minimalPeriod]
    have hk : k % minimalPeriod p x < (orbitList p x).length := by
      rw [length_orbitList]
      exact Nat.mod_lt _ (minimalPeriod_perm_pos p x)
    rw [← getElem_orbitList p x _ hk]
    exact List.getElem_mem hk

theorem mem_orbitList_self [Finite α] (p : Perm α) (x : α) : x ∈ orbitList p x :=
  mem_orbitList_iff.mpr (SameCycle.refl p x)

theorem getElem_orbitList_zero (p : Perm α) (x : α) (h : 0 < (orbitList p x).length) :
    (orbitList p x)[0] = x := by
  simp

/-- **Each entry of an orbit is followed by its image**, the last by the first. -/
theorem getElem_orbitList_succ_mod (p : Perm α) (x : α) (k : ℕ)
    (hk : k < (orbitList p x).length) :
    (orbitList p x)[(k + 1) % (orbitList p x).length]'(Nat.mod_lt _ (by omega)) =
      p (orbitList p x)[k] := by
  simp only [getElem_orbitList, length_orbitList]
  rw [← pow_apply_eq_pow_mod_minimalPeriod, pow_succ', mul_apply]

theorem minimalPeriod_perm_apply [Finite α] (p : Perm α) (x : α) :
    minimalPeriod p (p x) = minimalPeriod p x :=
  minimalPeriod_apply (mem_periodicPts_perm p x)

/-- **Moving the start one step along the cycle rotates the orbit.** -/
theorem orbitList_apply [Finite α] (p : Perm α) (x : α) :
    orbitList p (p x) = (orbitList p x).rotate 1 := by
  refine List.ext_getElem (by simp [minimalPeriod_perm_apply]) fun k h1 h2 => ?_
  rw [List.getElem_rotate, getElem_orbitList, getElem_orbitList, length_orbitList,
    ← pow_apply_eq_pow_mod_minimalPeriod, pow_succ, mul_apply]

theorem orbitList_pow_apply [Finite α] (p : Perm α) (x : α) (k : ℕ) :
    orbitList p ((p ^ k) x) = (orbitList p x).rotate k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply, orbitList_apply, ih, List.rotate_rotate]

/-- **Orbits through elements of one cycle are rotations of each other.** -/
theorem isRotated_orbitList [Finite α] {p : Perm α} {x y : α} (h : p.SameCycle x y) :
    orbitList p x ~r orbitList p y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  rw [orbitList_pow_apply]
  exact ⟨k, rfl⟩

/-- Along a list that `p` shifts cyclically, the iterates of the first entry run through the
list. -/
private theorem pow_apply_getElem_zero {p : Perm α} {L : List α} (h0 : 0 < L.length)
    (hsucc : ∀ (i : ℕ) (hi : i < L.length),
      p L[i] = L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega))) (k : ℕ) :
    (p ^ k) L[0] = L[k % L.length]'(Nat.mod_lt _ h0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply, ih, hsucc]
    congr 1
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- **A list that `p` shifts cyclically is an orbit**: if `L` has distinct entries and `p` sends
each entry to the next, and the last to the first, then `L` is the orbit of its first entry. -/
theorem orbitList_eq_of_getElem {p : Perm α} {L : List α} (hL : L.Nodup) (h0 : 0 < L.length)
    (hsucc : ∀ (i : ℕ) (hi : i < L.length),
      p L[i] = L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega))) :
    orbitList p L[0] = L := by
  have hpow := pow_apply_getElem_zero h0 hsucc
  have hper : minimalPeriod p L[0] = L.length := by
    have hfix : IsPeriodicPt p L.length L[0] := by
      change (⇑p)^[L.length] L[0] = L[0]
      rw [← coe_pow, hpow]
      simp
    refine le_antisymm (hfix.minimalPeriod_le h0) ?_
    by_contra hlt
    push Not at hlt
    have hm0 : 0 < minimalPeriod p L[0] := minimalPeriod_pos_of_mem_periodicPts ⟨_, h0, hfix⟩
    have h := pow_minimalPeriod_apply p L[0]
    rw [hpow] at h
    have := (hL.getElem_inj_iff).mp h
    rw [Nat.mod_eq_of_lt hlt] at this
    omega
  refine List.ext_getElem (by simp [hper]) fun k h1 h2 => ?_
  rw [getElem_orbitList, hpow]
  simp only [Nat.mod_eq_of_lt h2]

/-- **A list that `p` shifts cyclically is an orbit, up to rotation**, from any of its entries. -/
theorem isRotated_orbitList_of_mem [Finite α] {p : Perm α} {L : List α} (hL : L.Nodup)
    (hsucc : ∀ (i : ℕ) (hi : i < L.length),
      p L[i] = L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega)))
    {x : α} (hx : x ∈ L) : orbitList p x ~r L := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have h0 : 0 < L.length := by omega
  have hpow : (p ^ k) L[0] = L[k] := by
    rw [pow_apply_getElem_zero h0 hsucc k]
    congr 1
    exact Nat.mod_eq_of_lt hk
  rw [← hpow, orbitList_pow_apply, orbitList_eq_of_getElem hL h0 hsucc]
  exact List.IsRotated.symm ⟨k, rfl⟩

/-- **Orbits correspond under conjugation.** -/
theorem orbitList_permCongr (e : α ≃ β) (p : Perm α) (x : α) :
    orbitList (e.permCongr p) (e x) = (orbitList p x).map e := by
  have hpow : ∀ k : ℕ, (e.permCongr p ^ k) (e x) = e ((p ^ k) x) := fun k => by
    have h := map_pow e.permCongrHom p k
    change e.permCongr (p ^ k) = e.permCongr p ^ k at h
    rw [← h, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  have hper : minimalPeriod (e.permCongr p) (e x) = minimalPeriod p x := by
    rw [minimalPeriod_eq_minimalPeriod_iff]
    intro n
    change (⇑(e.permCongr p))^[n] (e x) = e x ↔ (⇑p)^[n] x = x
    rw [← coe_pow, ← coe_pow, hpow, e.apply_eq_iff_eq]
  simp only [orbitList, hper, List.map_map]
  exact List.map_congr_left fun k _ => hpow k

/-! ## Face darts and face walks -/

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

namespace RotationSystem

variable (ρ : RotationSystem G)

/-- **The darts of the face through `d`**, in order from `d`. -/
noncomputable def faceDarts (d : G.Dart) : List G.Dart := orbitList ρ.face d

/-- **The face walk through `d`**: the tails of the darts of its face, in order from `d`.
Consecutive vertices, and the last and the first, are adjacent; vertices may repeat. -/
noncomputable def faceWalk (d : G.Dart) : List V := (ρ.faceDarts d).map (·.fst)

@[simp] theorem length_faceDarts (d : G.Dart) :
    (ρ.faceDarts d).length = minimalPeriod ρ.face d :=
  length_orbitList _ _

@[simp] theorem length_faceWalk (d : G.Dart) :
    (ρ.faceWalk d).length = (ρ.faceDarts d).length :=
  List.length_map _

@[simp] theorem getElem_faceDarts (d : G.Dart) (k : ℕ) (hk : k < (ρ.faceDarts d).length) :
    (ρ.faceDarts d)[k] = (ρ.face ^ k) d :=
  getElem_orbitList _ _ _ hk

@[simp] theorem getElem_faceWalk (d : G.Dart) (k : ℕ) (hk : k < (ρ.faceWalk d).length) :
    (ρ.faceWalk d)[k] = ((ρ.face ^ k) d).fst := by
  simp [faceWalk]

theorem getElem_faceWalk_eq_fst (d : G.Dart) (k : ℕ) (hk : k < (ρ.faceWalk d).length) :
    (ρ.faceWalk d)[k] = ((ρ.faceDarts d)[k]'(by simpa using hk)).fst := by
  simp [faceWalk]

/-- **The darts of a face are distinct.** -/
theorem nodup_faceDarts (d : G.Dart) : (ρ.faceDarts d).Nodup :=
  nodup_orbitList _ _

/-- **A face has at least two darts.** -/
theorem two_le_length_faceDarts [Finite V] (d : G.Dart) : 2 ≤ (ρ.faceDarts d).length := by
  have := finite_dart (G := G)
  rw [length_faceDarts]
  have hpos := minimalPeriod_perm_pos ρ.face d
  have hne : minimalPeriod ρ.face d ≠ 1 := fun h =>
    ρ.face_ne d (minimalPeriod_eq_one_iff_isFixedPt.mp h)
  omega

theorem two_le_length_faceWalk [Finite V] (d : G.Dart) : 2 ≤ (ρ.faceWalk d).length := by
  rw [length_faceWalk]
  exact ρ.two_le_length_faceDarts d

/-- **The darts of a face** are the darts in the cycle of the face permutation. -/
theorem mem_faceDarts_iff [Finite V] {d e : G.Dart} :
    e ∈ ρ.faceDarts d ↔ ρ.face.SameCycle d e := by
  have := finite_dart (G := G)
  exact mem_orbitList_iff

/-- **The vertices of a face walk** are the tails of the darts of the face. -/
theorem mem_faceWalk_iff [Finite V] {d : G.Dart} {v : V} :
    v ∈ ρ.faceWalk d ↔ ∃ e, ρ.face.SameCycle d e ∧ e.fst = v := by
  simp only [faceWalk, List.mem_map, mem_faceDarts_iff]

theorem fst_mem_faceWalk [Finite V] {d e : G.Dart} (h : ρ.face.SameCycle d e) :
    e.fst ∈ ρ.faceWalk d :=
  (ρ.mem_faceWalk_iff).mpr ⟨e, h, rfl⟩

theorem fst_mem_faceWalk_self [Finite V] (d : G.Dart) : d.fst ∈ ρ.faceWalk d :=
  ρ.fst_mem_faceWalk (SameCycle.refl _ d)

/-- **Each dart of a face is followed by its image under the face permutation**, the last by the
first. -/
theorem getElem_faceDarts_succ_mod (d : G.Dart) (k : ℕ) (hk : k < (ρ.faceDarts d).length) :
    (ρ.faceDarts d)[(k + 1) % (ρ.faceDarts d).length]'(Nat.mod_lt _ (by omega)) =
      ρ.face (ρ.faceDarts d)[k] :=
  getElem_orbitList_succ_mod _ _ _ hk

/-- **The head of each dart of a face is the tail of the next.** -/
theorem snd_getElem_faceDarts (d : G.Dart) (k : ℕ) (hk : k < (ρ.faceDarts d).length) :
    ((ρ.faceDarts d)[k]).snd =
      ((ρ.faceDarts d)[(k + 1) % (ρ.faceDarts d).length]'(Nat.mod_lt _ (by omega))).fst := by
  rw [getElem_faceDarts_succ_mod, fst_face]

/-- **Consecutive vertices of a face walk are adjacent**, the last and the first too. -/
theorem adj_getElem_faceWalk (d : G.Dart) (k : ℕ) (hk : k < (ρ.faceWalk d).length) :
    G.Adj (ρ.faceWalk d)[k]
      ((ρ.faceWalk d)[(k + 1) % (ρ.faceWalk d).length]'(Nat.mod_lt _ (by omega))) := by
  have hk' : k < (ρ.faceDarts d).length := by simpa using hk
  have h := ((ρ.faceDarts d)[k]).adj
  rw [snd_getElem_faceDarts _ _ _ hk'] at h
  simpa only [getElem_faceWalk_eq_fst, length_faceWalk] using h

/-- **A face walk with distinct vertices is a cycle of the graph.** -/
theorem isCycleList_faceWalk {d : G.Dart} (h : (ρ.faceWalk d).Nodup) :
    IsCycleList G (ρ.faceWalk d) :=
  ⟨h, ρ.adj_getElem_faceWalk d⟩

/-- **A face walk has distinct vertices** exactly when distinct darts of the face have distinct
tails. -/
theorem nodup_faceWalk_iff [Finite V] {d : G.Dart} :
    (ρ.faceWalk d).Nodup ↔ ∀ e e', ρ.face.SameCycle d e → ρ.face.SameCycle d e' →
      e.fst = e'.fst → e = e' := by
  rw [faceWalk, List.nodup_map_iff_inj_on (ρ.nodup_faceDarts d)]
  simp only [mem_faceDarts_iff]
  exact ⟨fun h e e' he he' hee => h e he e' he' hee, fun h e he e' he' hee => h e e' he he' hee⟩

/-- **Moving the start one step along the face rotates the face darts.** -/
theorem faceDarts_face [Finite V] (d : G.Dart) :
    ρ.faceDarts (ρ.face d) = (ρ.faceDarts d).rotate 1 := by
  have := finite_dart (G := G)
  exact orbitList_apply _ _

theorem faceWalk_face [Finite V] (d : G.Dart) :
    ρ.faceWalk (ρ.face d) = (ρ.faceWalk d).rotate 1 := by
  rw [faceWalk, faceDarts_face, List.map_rotate, faceWalk]

/-- **Face walks through darts of one face are rotations of each other.** -/
theorem isRotated_faceDarts [Finite V] {d e : G.Dart} (h : ρ.face.SameCycle d e) :
    ρ.faceDarts d ~r ρ.faceDarts e := by
  have := finite_dart (G := G)
  exact isRotated_orbitList h

theorem isRotated_faceWalk [Finite V] {d e : G.Dart} (h : ρ.face.SameCycle d e) :
    ρ.faceWalk d ~r ρ.faceWalk e :=
  (ρ.isRotated_faceDarts h).map _

/-- **Face darts under an isomorphism** are the images of the old ones. -/
theorem faceDarts_mapIso (e : G ≃g G') (d : G.Dart) :
    (ρ.mapIso e).faceDarts (dartEquivOfIso e d) = (ρ.faceDarts d).map (dartEquivOfIso e) := by
  rw [faceDarts, face_mapIso, orbitList_permCongr, faceDarts]

/-- **Face walks under an isomorphism** are the images of the old ones. -/
theorem faceWalk_mapIso (e : G ≃g G') (d : G.Dart) :
    (ρ.mapIso e).faceWalk (dartEquivOfIso e d) = (ρ.faceWalk d).map e := by
  rw [faceWalk, faceDarts_mapIso, faceWalk, List.map_map, List.map_map]
  rfl

end RotationSystem

end MonoidProduct.Graph
