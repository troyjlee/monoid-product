import MonoidProduct.Graph.FaceWalk
import MonoidProduct.Graph.PlanarSubgraphAcceptance
set_option linter.style.header false

/-!
# Acceptance statements for face walks

The statements of `Graph/FaceWalk.lean` and the transport of rotation systems along isomorphisms
in `Graph/PlanarIso.lean`, restated, followed by small sanity checks.  Lean checks every
`example` here against the library's statement.

* Orbits as lists: their entries, members, rotation along the cycle, and the identification of a
  list shifted cyclically by a permutation as an orbit.
* Face darts and face walks: at least two darts, membership, adjacency of consecutive vertices,
  cycles of the graph when the vertices are distinct, and rotation along the face.
* Isomorphisms: the transported rotation system is spherical and its face walks are the images of
  the old ones.

The sanity checks compute the orbit of `0` under the rotation `0 ↦ 1 ↦ 2 ↦ 0` of `Fin 3`, and the
only face of `K₂`, whose walk `[0, 1]` runs along the edge and back.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv

/-! ## Statements -/

section Statements

variable {α V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- **Orbits as lists**: one period of iterates, with distinct entries, whose members are the
elements of the cycle. -/
example [Finite α] (p : Perm α) (x y : α) :
    orbitList p x = (List.range (Function.minimalPeriod p x)).map (fun k => (p ^ k) x) ∧
      (orbitList p x).Nodup ∧ (y ∈ orbitList p x ↔ p.SameCycle x y) :=
  ⟨rfl, nodup_orbitList p x, mem_orbitList_iff⟩

/-- **Each entry is followed by its image**, and moving the start rotates the orbit. -/
example [Finite α] (p : Perm α) (x : α) (k : ℕ) (hk : k < (orbitList p x).length) :
    (orbitList p x)[(k + 1) % (orbitList p x).length]'(Nat.mod_lt _ (by omega)) =
      p (orbitList p x)[k] ∧ orbitList p ((p ^ k) x) = (orbitList p x).rotate k :=
  ⟨getElem_orbitList_succ_mod p x k hk, orbitList_pow_apply p x k⟩

/-- **A list of distinct entries that `p` shifts cyclically is an orbit**, from its first entry,
and up to rotation from any entry. -/
example [Finite α] {p : Perm α} {L : List α} (hL : L.Nodup) (h0 : 0 < L.length)
    (hsucc : ∀ (i : ℕ) (hi : i < L.length),
      p L[i] = L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega))) {x : α} (hx : x ∈ L) :
    orbitList p L[0] = L ∧ orbitList p x ~r L :=
  ⟨orbitList_eq_of_getElem hL h0 hsucc, isRotated_orbitList_of_mem hL hsucc hx⟩

/-- **Face walks**: the tails of the darts of the face, read along the face permutation. -/
example (ρ : RotationSystem G) (d : G.Dart) :
    ρ.faceDarts d = orbitList ρ.face d ∧ ρ.faceWalk d = (ρ.faceDarts d).map (·.fst) :=
  ⟨rfl, rfl⟩

/-- **A face has at least two darts, and its walk passes through the tails of its darts.** -/
example [Finite V] (ρ : RotationSystem G) (d : G.Dart) (v : V) :
    2 ≤ (ρ.faceDarts d).length ∧ (ρ.faceWalk d).length = (ρ.faceDarts d).length ∧
      (v ∈ ρ.faceWalk d ↔ ∃ e, ρ.face.SameCycle d e ∧ e.fst = v) :=
  ⟨ρ.two_le_length_faceDarts d, ρ.length_faceWalk d, ρ.mem_faceWalk_iff⟩

/-- **Consecutive vertices of a face walk are adjacent**, the last and the first too; with
distinct vertices, the walk is a cycle of the graph. -/
example (ρ : RotationSystem G) (d : G.Dart) (k : ℕ) (hk : k < (ρ.faceWalk d).length) :
    G.Adj (ρ.faceWalk d)[k]
      ((ρ.faceWalk d)[(k + 1) % (ρ.faceWalk d).length]'(Nat.mod_lt _ (by omega))) ∧
      ((ρ.faceWalk d).Nodup → IsCycleList G (ρ.faceWalk d)) :=
  ⟨ρ.adj_getElem_faceWalk d k hk, ρ.isCycleList_faceWalk⟩

/-- **Distinct vertices** exactly when distinct darts of the face have distinct tails. -/
example [Finite V] (ρ : RotationSystem G) (d : G.Dart) :
    (ρ.faceWalk d).Nodup ↔ ∀ e e', ρ.face.SameCycle d e → ρ.face.SameCycle d e' →
      e.fst = e'.fst → e = e' :=
  ρ.nodup_faceWalk_iff

/-- **Along the face**: the walk rotates as its start moves, and walks through darts of one face
are rotations of each other. -/
example [Finite V] (ρ : RotationSystem G) {d e : G.Dart} (h : ρ.face.SameCycle d e) :
    ρ.faceWalk (ρ.face d) = (ρ.faceWalk d).rotate 1 ∧ ρ.faceWalk d ~r ρ.faceWalk e :=
  ⟨ρ.faceWalk_face d, ρ.isRotated_faceWalk h⟩

/-- **Isomorphisms**: the transported rotation is conjugated, stays spherical, and has the image
face walks. -/
example (e : G ≃g G') (ρ : RotationSystem G) (hρ : ρ.IsSpherical) (d : G.Dart) :
    (ρ.mapIso e).rot = (dartEquivOfIso e).permCongr ρ.rot ∧
      (ρ.mapIso e).face = (dartEquivOfIso e).permCongr ρ.face ∧ (ρ.mapIso e).IsSpherical ∧
      (ρ.mapIso e).faceWalk (dartEquivOfIso e d) = (ρ.faceWalk d).map e :=
  ⟨rfl, ρ.face_mapIso e, hρ.mapIso e, ρ.faceWalk_mapIso e d⟩

end Statements

/-! ## Sanity checks -/

/-- **The orbit of `0` under the rotation of `Fin 3`** is `[0, 1, 2]`. -/
example : orbitList (finRotate 3) 0 = [0, 1, 2] :=
  orbitList_eq_of_getElem (L := [0, 1, 2]) (by decide) (by decide) (by decide)

/-- The dart from `0` to `1` in `K₂`. -/
private abbrev k2d₀₁ : (⊤ : SimpleGraph (Fin 2)).Dart := ⟨(0, 1), (top_adj 0 1).mpr (by decide)⟩

/-- The dart from `1` to `0` in `K₂`. -/
private abbrev k2d₁₀ : (⊤ : SimpleGraph (Fin 2)).Dart := ⟨(1, 0), (top_adj 1 0).mpr (by decide)⟩

/-- **The face of `K₂`**: its two darts, and the walk `[0, 1]` along the edge and back, which is
a cycle of length two in the sense of `IsCycleList`. -/
example : k2Rotation.faceDarts k2d₀₁ = [k2d₀₁, k2d₁₀] ∧ k2Rotation.faceWalk k2d₀₁ = [0, 1] ∧
    IsCycleList (⊤ : SimpleGraph (Fin 2)) [0, 1] := by
  have hface : ∀ d, k2Rotation.face d = d.symm := fun _ => rfl
  have hD : k2Rotation.faceDarts k2d₀₁ = [k2d₀₁, k2d₁₀] :=
    orbitList_eq_of_getElem (L := [k2d₀₁, k2d₁₀]) (by decide) (by decide) fun i hi => by
      rw [hface]
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i <;> rfl
  refine ⟨hD, by simp [RotationSystem.faceWalk, hD], ?_⟩
  rw [← show k2Rotation.faceWalk k2d₀₁ = [0, 1] by simp [RotationSystem.faceWalk, hD]]
  exact k2Rotation.isCycleList_faceWalk (by simp [RotationSystem.faceWalk, hD])

end MonoidProduct.Graph
