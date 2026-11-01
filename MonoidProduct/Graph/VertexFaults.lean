import MonoidProduct.Graph.Components
set_option linter.style.header false

/-!
# Vertex-failure profiles

`monoid.tex`, section `sec:failure-profiles`, `eq:vertex-failure-profile`: for every set `X` of
fewer than `k` vertices, the component partition of `G − X`, which deletes the vertices of `X`
and their incident edges.  Its partition is on `V \ X`.

* `vertexFailureProfile k S` (`Σ^V_k(S)`): one coordinate for every `X` with `|X| < k`
  (`VertexFailureSet V k`).  The coordinate at `X` relates two vertices exactly when both
  survive and they are connected in Mathlib's induced graph `(toGraph S).induce {z | z ∉ X}`
  (`mem_vertexFailureProfile`).  Deleted vertices appear in no pair, so the coordinate is the
  partition of `V \ X` itself, not a partition of `V` in which deleted vertices are isolated.
  It is one output in the fixed finite type `VertexFailureSet V k → Finset (V × V)`.
* Truncation in `k` (`vertexFailureProfile_of_le`); at `X = ∅` the coordinate is the component
  partition of `toGraph S` (`mem_vertexFailureProfile_empty`), so for `k = 1` the profile is
  the component partition (`vertexFailureProfile_one_eq_iff`); for `k = 0` it is constant.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-- The failure sets of the `k`-vertex-failure profile: the sets of fewer than `k` vertices. -/
abbrev VertexFailureSet (V : Type*) (k : ℕ) : Type _ := {X : Finset V // X.card < k}

/-! ## Reachability in induced graphs -/

section Induce

variable {V : Type*}

/-- A walk whose vertices all lie in `s` is a walk of the induced graph on `s`. -/
theorem reachable_induce_of_walk {G : SimpleGraph V} {s : Set V} :
    ∀ {u w : V} (p : G.Walk u w) (hs : ∀ z ∈ p.support, z ∈ s),
      (G.induce s).Reachable ⟨u, hs u p.start_mem_support⟩ ⟨w, hs w p.end_mem_support⟩
  | _, _, .nil, _ => Reachable.rfl
  | _, _, @Walk.cons _ _ u v _ h p, hs => by
      have hadj : (G.induce s).Adj ⟨u, hs u (by simp)⟩ ⟨v, hs v (by simp)⟩ := h
      exact hadj.reachable.trans (reachable_induce_of_walk p fun z hz => hs z (by simp [hz]))

/-- Reachability in an induced graph is reachability in the graph. -/
theorem reachable_of_induce {G : SimpleGraph V} {s : Set V} {u w : s}
    (h : (G.induce s).Reachable u w) : G.Reachable u w :=
  h.map (Embedding.induce s).toHom

/-- A vertex with no neighbours is reachable only from itself. -/
theorem eq_of_reachable_of_forall_not_adj {G : SimpleGraph V} {u w : V}
    (hu : ∀ x, ¬G.Adj u x) (h : G.Reachable u w) : w = u := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hu _)

end Induce

/-! ## The profile -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The vertex-failure profile** `Σ^V_k(S)` (`eq:vertex-failure-profile`): for every set `X`
of fewer than `k` vertices, the component partition of `G − X` on `V \ X`, recorded as the pairs
of surviving vertices connected in the graph induced on `V \ X`. -/
noncomputable def vertexFailureProfile (k : ℕ) (S : Finset (Edge V)) :
    VertexFailureSet V k → Finset (V × V) := fun X => by
  classical exact Finset.univ.filter fun p => ∃ (hu : p.1 ∉ X.1) (hw : p.2 ∉ X.1),
    ((toGraph S).induce {z | z ∉ X.1}).Reachable ⟨p.1, hu⟩ ⟨p.2, hw⟩

/-- The coordinate at `X` is the reachability relation of `G − X` on the surviving vertices. -/
theorem mem_vertexFailureProfile {k : ℕ} {S : Finset (Edge V)} {X : VertexFailureSet V k}
    {u w : V} : (u, w) ∈ vertexFailureProfile k S X ↔
      ∃ (hu : u ∉ X.1) (hw : w ∉ X.1),
        ((toGraph S).induce {z | z ∉ X.1}).Reachable ⟨u, hu⟩ ⟨w, hw⟩ := by
  simp [vertexFailureProfile]

/-- A deleted vertex lies in no pair of the coordinate. -/
theorem fst_notMem_of_mem_vertexFailureProfile {k : ℕ} {S : Finset (Edge V)}
    {X : VertexFailureSet V k} {u w : V} (h : (u, w) ∈ vertexFailureProfile k S X) :
    u ∉ X.1 ∧ w ∉ X.1 := by
  obtain ⟨hu, hw, _⟩ := mem_vertexFailureProfile.mp h
  exact ⟨hu, hw⟩

/-- **Truncation**: for `k' ≤ k`, the profile for `k'` is a restriction of the profile for
`k`. -/
theorem vertexFailureProfile_of_le {k k' : ℕ} (h : k' ≤ k) (S : Finset (Edge V))
    (X : VertexFailureSet V k') :
    vertexFailureProfile k' S X = vertexFailureProfile k S ⟨X.1, X.2.trans_le h⟩ :=
  rfl

/-- **Deleting no vertex**: the coordinate at `X = ∅` is the reachability relation of
`toGraph S`. -/
theorem mem_vertexFailureProfile_empty {k : ℕ} (hk : 0 < k) {S : Finset (Edge V)} {u w : V} :
    (u, w) ∈ vertexFailureProfile k S ⟨∅, by simpa using hk⟩ ↔ (toGraph S).Reachable u w := by
  rw [mem_vertexFailureProfile]
  constructor
  · rintro ⟨hu, hw, h⟩
    exact reachable_of_induce h
  · rintro ⟨p⟩
    exact ⟨Finset.notMem_empty u, Finset.notMem_empty w,
      reachable_induce_of_walk p fun z _ => Finset.notMem_empty z⟩

/-- **`k = 1`**: the only failure set is `∅`, so two graphs have the same profile exactly when
they have the same component partition. -/
theorem vertexFailureProfile_one_eq_iff {S T : Finset (Edge V)} :
    vertexFailureProfile 1 S = vertexFailureProfile 1 T ↔
      connectedComponents S = connectedComponents T := by
  have hX : ∀ X : VertexFailureSet V 1, X = ⟨∅, by simp⟩ := fun X =>
    Subtype.ext (Finset.card_eq_zero.mp (Nat.lt_one_iff.mp X.2))
  constructor
  · intro h
    ext ⟨u, w⟩
    rw [mem_connectedComponents, mem_connectedComponents,
      ← mem_vertexFailureProfile_empty (k := 1) Nat.one_pos,
      ← mem_vertexFailureProfile_empty (k := 1) Nat.one_pos, h]
  · intro h
    funext X
    rw [hX X]
    ext ⟨u, w⟩
    rw [mem_vertexFailureProfile_empty Nat.one_pos, mem_vertexFailureProfile_empty Nat.one_pos,
      ← mem_connectedComponents, h, mem_connectedComponents]

/-- **`k = 0`**: there are no failure sets, and the profile is the same for every graph. -/
theorem vertexFailureProfile_zero (S T : Finset (Edge V)) :
    vertexFailureProfile 0 S = vertexFailureProfile 0 T :=
  funext fun X => absurd X.2 (Nat.not_lt_zero _)

end MonoidProduct.Graph
