import MonoidProduct.Graph.RotationFaces
import MonoidProduct.Graph.PlanarSubgraphAcceptance
set_option linter.style.header false

/-!
# Acceptance statements for faces of `2`-connected rotation systems

The statements of `Graph/RotationSplit.lean` and `Graph/RotationFaces.lean`, restated, followed by
sanity checks on `K₄`.  Lean checks every `example` here against the library's statement.

* Left multiplication by a transposition splits a cycle.
* Splitting a vertex at two darts of one face: the split graph, its rotation system, and the
  Euler defect less two.
* Faces of a spherical rotation system of a `2`-connected graph: distinct darts of a face have
  distinct tails, and every face walk is a cycle of the graph.
* Deleting a vertex: a spherical rotation system that skips the deleted vertex, and, for a
  `2`-connected graph, a face through all its neighbours, a cycle for a `3`-connected graph.

The sanity checks: every face walk of the spherical rotation system of `K₄` is a cycle of `K₄`,
and deleting the vertex `0` of `K₄` leaves a spherical rotation system of the triangle on `1`,
`2` and `3` with a face through all three, which is a cycle since `K₄` is `3`-connected.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm

/-! ## Statements -/

section Statements

variable {α V : Type*} {G : SimpleGraph V}

/-- **A transposition on the left inside a cycle splits it**: `a` and `b` end up in different
cycles, and there is one cycle more. -/
example [DecidableEq α] [Finite α] {p : Perm α} {a b : α} (hne : a ≠ b) (hab : p.SameCycle a b) :
    swap a b * p = (swap a b).permCongr (p * swap a b) ∧
      ¬ (swap a b * p).SameCycle a b ∧ cycleCount (swap a b * p) = cycleCount p + 1 :=
  ⟨swap_mul_eq_permCongr p a b, not_sameCycle_swap_mul_of_sameCycle hne hab,
    cycleCount_swap_mul_of_sameCycle hne hab⟩

/-- **The split graph** presents the darts of `G` with their new tails, and its rotation system is
`swap a b * ρ.rot` on them. -/
example [DecidableEq V] [Finite V] (ρ : RotationSystem G) {a b : G.Dart} (hfst : a.fst = b.fst)
    (p q : Option V) :
    ((ρ.splitGraph a b).Adj p q ↔ ∃ d : G.Dart, ρ.splitTail a b d = p ∧
      ρ.splitTail a b d.symm = q) ∧
      (ρ.splitRotation a b hfst).rot = (dartGraphEquiv (ρ.splitTail a b)
        (RotationSystem.splitTail_ne_symm ρ a b) (RotationSystem.splitTail_inj ρ a b)).permCongr
          (swap a b * ρ.rot) ∧
      (ρ.splitGraph a b).edgeSet.ncard = G.edgeSet.ncard :=
  ⟨Iff.rfl, rfl, ρ.ncard_edgeSet_splitGraph⟩

/-- **Splitting a vertex at two darts of one face of a `2`-connected graph**: the split graph is
connected, has one face more, and the Euler defect drops by two. -/
example [DecidableEq V] [Finite V] (ρ : RotationSystem G) {a b : G.Dart} (hab : a ≠ b)
    (hfst : a.fst = b.fst) (hface : ρ.face.SameCycle a b) (hG : IsKConnected G 2) :
    (ρ.splitGraph a b).Connected ∧
      Nat.card (ρ.splitRotation a b hfst).Face = Nat.card ρ.Face + 1 ∧
      (ρ.splitRotation a b hfst).eulerDefect = ρ.eulerDefect - 2 :=
  ⟨ρ.splitGraph_connected hab hfst hG, ρ.natCard_face_splitRotation hab hfst hface,
    ρ.eulerDefect_splitRotation hab hfst hface hG⟩

/-- **Distinct darts of one face have distinct tails**, in a spherical rotation system of a
`2`-connected graph. -/
example [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) (hG : IsKConnected G 2)
    {d e : G.Dart} (hface : ρ.face.SameCycle d e) (hfst : d.fst = e.fst) : d = e :=
  RotationSystem.fst_injective_on_face hρ hG hface hfst

/-- **Every face walk is a cycle of the graph**, in a spherical rotation system of a
`2`-connected graph. -/
example [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) (hG : IsKConnected G 2)
    (d : G.Dart) : (ρ.faceWalk d).Nodup ∧ IsCycleList G (ρ.faceWalk d) :=
  ⟨RotationSystem.nodup_faceWalk_of_isKConnected hρ hG d,
    RotationSystem.isCycleList_faceWalk_of_isKConnected hρ hG d⟩

/-- **Deleting a vertex keeps a spherical rotation system spherical**, with the rotation at each
surviving vertex skipping the dart to the deleted vertex; no connectivity is assumed. -/
example [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) (z : V) :
    ∃ σ : RotationSystem (G.induce {v | v ≠ z}), σ.IsSpherical ∧
      ∀ d : (G.induce {v | v ≠ z}).Dart,
        ((ρ.rot (ofInduceDart d)).snd = z →
          ofInduceDart (σ.rot d) = ρ.rot (ρ.rot (ofInduceDart d))) ∧
        ((ρ.rot (ofInduceDart d)).snd ≠ z → ofInduceDart (σ.rot d) = ρ.rot (ofInduceDart d)) :=
  exists_rotationSystem_induce_ne hρ z

/-- **Deleting a vertex of a `2`-connected graph leaves a face through all its neighbours.** -/
example [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) (hG : IsKConnected G 2) (z : V) :
    ∃ σ : RotationSystem (G.induce {v | v ≠ z}), σ.IsSpherical ∧
      ∃ d₀ : (G.induce {v | v ≠ z}).Dart, ∀ w (hw : G.Adj z w),
        (⟨w, hw.ne'⟩ : ↥({v | v ≠ z} : Set V)) ∈ σ.faceWalk d₀ :=
  exists_induce_ne_faceWalk hρ hG z

/-- **The face through the neighbours exists for the rotation system that skips the deleted
vertex**, so the rotation and the face are available together. -/
example [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) (hG : IsKConnected G 2) {z : V}
    {σ : RotationSystem (G.induce {v | v ≠ z})}
    (hrot : ∀ d : (G.induce {v | v ≠ z}).Dart,
      ((ρ.rot (ofInduceDart d)).snd = z →
        ofInduceDart (σ.rot d) = ρ.rot (ρ.rot (ofInduceDart d))) ∧
      ((ρ.rot (ofInduceDart d)).snd ≠ z → ofInduceDart (σ.rot d) = ρ.rot (ofInduceDart d))) :
    ∃ d₀ : (G.induce {v | v ≠ z}).Dart, ∀ w (hw : G.Adj z w),
      (⟨w, hw.ne'⟩ : ↥({v | v ≠ z} : Set V)) ∈ σ.faceWalk d₀ :=
  exists_mem_faceWalk_induce_ne hρ hG hrot

/-- **For a `3`-connected graph the face through the neighbours is a cycle.** -/
example [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) (hG : IsKConnected G 3) (z : V) :
    ∃ σ : RotationSystem (G.induce {v | v ≠ z}), σ.IsSpherical ∧
      ∃ d₀ : (G.induce {v | v ≠ z}).Dart, IsCycleList (G.induce {v | v ≠ z}) (σ.faceWalk d₀) ∧
        ∀ w (hw : G.Adj z w), (⟨w, hw.ne'⟩ : ↥({v | v ≠ z} : Set V)) ∈ σ.faceWalk d₀ :=
  exists_induce_ne_isCycleList_faceWalk hρ hG z

end Statements

/-! ## Sanity checks: `K₄` -/

/-- `K₄` is `3`-connected. -/
private theorem isKConnected_top_four_three : IsKConnected (⊤ : SimpleGraph (Fin 4)) 3 :=
  ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩

/-- `K₄` is `2`-connected. -/
private theorem isKConnected_top_four_two : IsKConnected (⊤ : SimpleGraph (Fin 4)) 2 :=
  isKConnected_top_four_three.mono (by norm_num)

/-- **The faces of `K₄` are cycles**: every face walk of its spherical rotation system has distinct
vertices. -/
example (d : (⊤ : SimpleGraph (Fin 4)).Dart) :
    IsCycleList (⊤ : SimpleGraph (Fin 4)) (k4Rotation.faceWalk d) :=
  RotationSystem.isCycleList_faceWalk_of_isKConnected isSpherical_k4Rotation
    isKConnected_top_four_two d

/-- **Deleting a vertex of `K₄`**: the triangle on `1`, `2` and `3` has a spherical rotation
system with a face through all three. -/
example : ∃ σ : RotationSystem ((⊤ : SimpleGraph (Fin 4)).induce {v | v ≠ 0}), σ.IsSpherical ∧
    ∃ d₀, (⟨1, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 4))) ∈ σ.faceWalk d₀ ∧
      (⟨2, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 4))) ∈ σ.faceWalk d₀ ∧
      (⟨3, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 4))) ∈ σ.faceWalk d₀ := by
  obtain ⟨σ, hσ, d₀, h⟩ := exists_induce_ne_faceWalk isSpherical_k4Rotation
    isKConnected_top_four_two 0
  exact ⟨σ, hσ, d₀, h 1 ((top_adj 0 1).mpr (by decide)), h 2 ((top_adj 0 2).mpr (by decide)),
    h 3 ((top_adj 0 3).mpr (by decide))⟩

/-- **The face left by deleting a vertex of `K₄` is a cycle**, since `K₄` is `3`-connected. -/
example : ∃ σ : RotationSystem ((⊤ : SimpleGraph (Fin 4)).induce {v | v ≠ 0}), σ.IsSpherical ∧
    ∃ d₀, IsCycleList ((⊤ : SimpleGraph (Fin 4)).induce {v | v ≠ 0}) (σ.faceWalk d₀) ∧
      (⟨1, by decide⟩ : ↥({v | v ≠ 0} : Set (Fin 4))) ∈ σ.faceWalk d₀ := by
  obtain ⟨σ, hσ, d₀, hC, h⟩ := exists_induce_ne_isCycleList_faceWalk isSpherical_k4Rotation
    isKConnected_top_four_three 0
  exact ⟨σ, hσ, d₀, hC, h 1 ((top_adj 0 1).mpr (by decide))⟩

end MonoidProduct.Graph
