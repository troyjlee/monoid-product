import MonoidProduct.Graph.VertexCertificate
set_option linter.style.header false

/-!
# Readouts of the vertex-failure profile

`monoid.tex`, section `sec:failure-profiles`, the text after `eq:failure-profile-queries`: for
`k = 2` the vertex profile identifies all articulation points and the partitions after their
deletion, and the profile for `k` decides `k`-vertex-connectivity for `v > k`.  Write `v = #V`
and `N = C(v, 2)`.  Mathlib has neither notion, so both are defined here.

* **Articulation points** (`articulationPoints`): the vertices whose deletion increases the
  number of connected components, as the paper characterizes them (`mem_articulationPoints`).
  Deleting `x` leaves the graph induced on `V \ {x}`.  Equivalently, `x` separates two other
  vertices of one component (`mem_articulationPoints_iff_separates`), the textbook definition of
  a cut vertex.  So the coordinates of `Σ^V_2` at `∅` and at `{x}` decide whether `x` is one
  (`mem_articulationPoints_iff_vertexFailureProfile`), and the certificate size of the
  articulation points is at most `min{N, 4v}`.
* **The partitions after their deletion** (`articulationPartitions`): `some π(G − x)` on
  `V \ {x}` (`deletionPartition`, the coordinate of `Σ^V_2` at `{x}`) for an articulation point
  `x`, and `none` otherwise.  Their certificate size is also at most `min{N, 4v}`.
* **`k`-vertex-connectivity** (`isVertexConnected`): more than `k` vertices, and `G − X` connected
  for every set `X` of fewer than `k` vertices.  The condition `k < v` is part of the definition,
  so the profile for `k` decides it for every `k`
  (`isVertexConnected_iff_vertexFailureProfile`), with certificate size at most `min{N, 2kv}`.
  For `k = 1` it is connectivity on at least two vertices (`isVertexConnected_one_iff`).
-/

namespace MonoidProduct.Graph

open SimpleGraph Certificates

/-- Graphs with the same reachability have the same number of components. -/
theorem natCard_connectedComponent_congr {W : Type*} {G G' : SimpleGraph W}
    (h : ∀ a b, G.Reachable a b ↔ G'.Reachable a b) :
    Nat.card G.ConnectedComponent = Nat.card G'.ConnectedComponent :=
  Nat.card_congr (Quot.congrRight h)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Articulation points -/

/-- **The articulation points** of `toGraph S`: the vertices whose deletion increases the number
of connected components.  Deleting `x` leaves the graph induced on `V \ {x}`. -/
noncomputable def articulationPoints (S : Finset (Edge V)) : Finset V := by
  classical exact Finset.univ.filter fun x => Nat.card (toGraph S).ConnectedComponent <
    Nat.card ((toGraph S).induce {z | z ≠ x}).ConnectedComponent

omit [DecidableEq V] in
/-- **An articulation point is a vertex whose deletion increases the number of components.** -/
theorem mem_articulationPoints {S : Finset (Edge V)} {x : V} :
    x ∈ articulationPoints S ↔ Nat.card (toGraph S).ConnectedComponent <
      Nat.card ((toGraph S).induce {z | z ≠ x}).ConnectedComponent := by
  simp [articulationPoints]

omit [DecidableEq V] in
/-- **Articulation points separate**: `x` is an articulation point exactly when two vertices
other than `x`, connected in `G`, are not connected in `G − x`. -/
theorem mem_articulationPoints_iff_separates {S : Finset (Edge V)} {x : V} :
    x ∈ articulationPoints S ↔ ∃ a b, ∃ (ha : a ≠ x) (hb : b ≠ x), (toGraph S).Reachable a b ∧
      ¬((toGraph S).induce {z | z ≠ x}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  rw [mem_articulationPoints]
  set G := toGraph S
  let φ : (G.induce {z | z ≠ x}).ConnectedComponent → G.ConnectedComponent :=
    ConnectedComponent.map (Embedding.induce {z | z ≠ x}).toHom
  have hφ : ∀ (a : V) (ha : a ≠ x), φ ((G.induce {z | z ≠ x}).connectedComponentMk ⟨a, ha⟩) =
      G.connectedComponentMk a := fun _ _ => ConnectedComponent.map_mk _ _
  constructor
  · intro hlt
    by_contra hno
    have hinj : Function.Injective φ := by
      intro c d hcd
      induction c using ConnectedComponent.ind with
      | h a =>
      induction d using ConnectedComponent.ind with
      | h b =>
      rw [hφ a.1 a.2, hφ b.1 b.2, ConnectedComponent.eq] at hcd
      rw [ConnectedComponent.eq]
      by_contra hr
      exact hno ⟨a.1, b.1, a.2, b.2, hcd, hr⟩
    exact absurd (Nat.card_le_card_of_injective φ hinj) (not_le.mpr hlt)
  · rintro ⟨a, b, ha, hb, hab, hsep⟩
    -- `x` has a neighbour: otherwise every path between `a` and `b` avoids it.
    have hnbr : ∃ y, G.Adj x y := by
      by_contra hno
      have hiso : ∀ y, ¬G.Adj x y := fun y h => hno ⟨y, h⟩
      have hG : ∀ c d, G.Adj c d ↔ G.Adj c d ∧ c ≠ x ∧ d ≠ x := fun c d =>
        ⟨fun h => ⟨h, fun hc => hiso d (hc ▸ h), fun hd => hiso c (hd ▸ h.symm)⟩, fun h => h.1⟩
      exact hsep ((reachable_induce_iff (s := {z | z ≠ x}) hG ha hb).mpr hab)
    obtain ⟨y, hxy⟩ := hnbr
    have hsurj : Function.Surjective φ := fun c => by
      induction c using ConnectedComponent.ind with
      | h z =>
      by_cases hz : z = x
      · rw [hz]
        refine ⟨(G.induce {z | z ≠ x}).connectedComponentMk ⟨y, hxy.ne.symm⟩, ?_⟩
        rw [hφ, ConnectedComponent.eq]
        exact hxy.symm.reachable
      · exact ⟨_, hφ z hz⟩
    have hnotinj : ¬Function.Injective φ := fun hinj => by
      have := hinj (a₁ := (G.induce {z | z ≠ x}).connectedComponentMk ⟨a, ha⟩)
        (a₂ := (G.induce {z | z ≠ x}).connectedComponentMk ⟨b, hb⟩)
        (by rw [hφ, hφ, ConnectedComponent.eq]; exact hab)
      exact hsep (ConnectedComponent.eq.mp this)
    refine lt_of_le_of_ne (Nat.card_le_card_of_surjective φ hsurj) fun heq => hnotinj ?_
    exact (hsurj.bijective_of_nat_card_le heq.ge).1

/-- **Deleting one vertex**: reachability in `G − x` is the coordinate of `Σ^V_2` at `{x}`. -/
theorem reachable_induce_ne_iff {S : Finset (Edge V)} {x a b : V} (ha : a ≠ x) (hb : b ≠ x) :
    ((toGraph S).induce {z | z ≠ x}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ ↔
      (a, b) ∈ vertexFailureProfile 2 S ⟨{x}, by simp⟩ := by
  have hG : ∀ c d, (toGraph (edgesWithin ({x} : Finset V)ᶜ S)).Adj c d ↔
      (toGraph S).Adj c d ∧ c ≠ x ∧ d ≠ x := fun c d => by
    rw [toGraph_edgesWithin_compl_adj, Finset.mem_singleton, Finset.mem_singleton]
  rw [mem_vertexFailureProfile_iff_edgesWithin, reachable_induce_iff (s := {z | z ≠ x}) hG ha hb]
  exact ⟨fun h => ⟨fun h' => ha (Finset.mem_singleton.mp h'),
    fun h' => hb (Finset.mem_singleton.mp h'), h⟩, fun h => h.2.2⟩

/-- **The profile for `k = 2` determines the articulation points**: `x` is one exactly when two
vertices other than `x` are related at `∅` and not at `{x}`. -/
theorem mem_articulationPoints_iff_vertexFailureProfile {S : Finset (Edge V)} {x : V} :
    x ∈ articulationPoints S ↔ ∃ a b, a ≠ x ∧ b ≠ x ∧
      (a, b) ∈ vertexFailureProfile 2 S ⟨∅, by simp⟩ ∧
      (a, b) ∉ vertexFailureProfile 2 S ⟨{x}, by simp⟩ := by
  rw [mem_articulationPoints_iff_separates]
  constructor
  · rintro ⟨a, b, ha, hb, hab, hsep⟩
    exact ⟨a, b, ha, hb, (mem_vertexFailureProfile_empty two_pos).mpr hab,
      fun h => hsep ((reachable_induce_ne_iff ha hb).mpr h)⟩
  · rintro ⟨a, b, ha, hb, hab, hsep⟩
    exact ⟨a, b, ha, hb, (mem_vertexFailureProfile_empty two_pos).mp hab,
      fun h => hsep ((reachable_induce_ne_iff ha hb).mp h)⟩

/-- The profile for `k = 2` determines the articulation points. -/
theorem articulationPoints_eq_of_vertexFailureProfile {S T : Finset (Edge V)}
    (h : vertexFailureProfile 2 S = vertexFailureProfile 2 T) :
    articulationPoints S = articulationPoints T := by
  ext x
  rw [mem_articulationPoints_iff_vertexFailureProfile,
    mem_articulationPoints_iff_vertexFailureProfile, h]

/-- The certificate bound of the profile for `k = 2`, as `4v`. -/
theorem vertexFailureProfile_two_strongCertificateSize_le :
    strongCertificateSize (vertexFailureProfile (V := V) 2) ≤
      min ((Fintype.card V).choose 2) (4 * Fintype.card V) := by
  have h := vertexFailureProfile_strongCertificateSize_le (V := V) 2
  rwa [show 2 * 2 * Fintype.card V = 4 * Fintype.card V by ring] at h

/-- **Articulation points** (`sec:failure-profiles`): through the profile for `k = 2`, their
certificate size is at most `min{C(v, 2), 4v}`. -/
theorem articulationPoints_strongCertificateSize_le :
    strongCertificateSize (articulationPoints (V := V)) ≤
      min ((Fintype.card V).choose 2) (4 * Fintype.card V) :=
  (strongCertificateSize_le_of_determined fun _ _ =>
    articulationPoints_eq_of_vertexFailureProfile).trans
    vertexFailureProfile_two_strongCertificateSize_le

/-- **Certificates for the articulation points within `min{C(v, 2), 4v}` edges.** -/
theorem hasStrongCertificateBound_articulationPoints :
    HasStrongCertificateBound (articulationPoints (V := V))
      (min ((Fintype.card V).choose 2) (4 * Fintype.card V)) :=
  hasStrongCertificateBound_iff_size_le.mpr articulationPoints_strongCertificateSize_le

/-! ## The partitions after deleting an articulation point -/

/-- **The partition of `G − x`**, on `V \ {x}`: the pairs of surviving vertices connected in the
graph induced on `V \ {x}`. -/
noncomputable def deletionPartition (S : Finset (Edge V)) (x : V) : Finset (V × V) := by
  classical exact Finset.univ.filter fun p => ∃ (ha : p.1 ≠ x) (hb : p.2 ≠ x),
    ((toGraph S).induce {z | z ≠ x}).Reachable ⟨p.1, ha⟩ ⟨p.2, hb⟩

theorem mem_deletionPartition {S : Finset (Edge V)} {x a b : V} :
    (a, b) ∈ deletionPartition S x ↔ ∃ (ha : a ≠ x) (hb : b ≠ x),
      ((toGraph S).induce {z | z ≠ x}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [deletionPartition]

/-- The partition of `G − x` is the coordinate of `Σ^V_2` at `{x}`. -/
theorem deletionPartition_eq_vertexFailureProfile (S : Finset (Edge V)) (x : V) :
    deletionPartition S x = vertexFailureProfile 2 S ⟨{x}, by simp⟩ := by
  ext ⟨a, b⟩
  rw [mem_deletionPartition]
  constructor
  · rintro ⟨ha, hb, h⟩
    exact (reachable_induce_ne_iff ha hb).mp h
  · intro h
    obtain ⟨ha, hb, -⟩ := mem_vertexFailureProfile_iff_edgesWithin.mp h
    have ha' : a ≠ x := fun h' => ha (Finset.mem_singleton.mpr h')
    have hb' : b ≠ x := fun h' => hb (Finset.mem_singleton.mpr h')
    exact ⟨ha', hb', (reachable_induce_ne_iff ha' hb').mpr h⟩

/-- **The articulation points with the partitions after their deletion**: `some π(G − x)` when
`x` is an articulation point of `toGraph S`, and `none` otherwise. -/
noncomputable def articulationPartitions (S : Finset (Edge V)) : V → Option (Finset (V × V)) :=
  fun x => if x ∈ articulationPoints S then some (deletionPartition S x) else none

theorem articulationPartitions_eq_some_iff {S : Finset (Edge V)} {x : V} {P : Finset (V × V)} :
    articulationPartitions S x = some P ↔
      x ∈ articulationPoints S ∧ P = deletionPartition S x := by
  unfold articulationPartitions
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem articulationPartitions_eq_none_iff {S : Finset (Edge V)} {x : V} :
    articulationPartitions S x = none ↔ x ∉ articulationPoints S := by
  unfold articulationPartitions
  split_ifs with h <;> simp [h]

/-- The profile for `k = 2` determines the articulation points and the partitions after their
deletion. -/
theorem articulationPartitions_eq_of_vertexFailureProfile {S T : Finset (Edge V)}
    (h : vertexFailureProfile 2 S = vertexFailureProfile 2 T) :
    articulationPartitions S = articulationPartitions T := by
  funext x
  have ha := articulationPoints_eq_of_vertexFailureProfile h
  have hπ : deletionPartition S x = deletionPartition T x := by
    rw [deletionPartition_eq_vertexFailureProfile, deletionPartition_eq_vertexFailureProfile, h]
  simp only [articulationPartitions, ha, hπ]

/-- **The articulation points and the partitions after their deletion** (`sec:failure-profiles`):
their certificate size is at most `min{C(v, 2), 4v}`. -/
theorem articulationPartitions_strongCertificateSize_le :
    strongCertificateSize (articulationPartitions (V := V)) ≤
      min ((Fintype.card V).choose 2) (4 * Fintype.card V) :=
  (strongCertificateSize_le_of_determined fun _ _ =>
    articulationPartitions_eq_of_vertexFailureProfile).trans
    vertexFailureProfile_two_strongCertificateSize_le

/-- **Certificates for the articulation points and their partitions within
`min{C(v, 2), 4v}` edges.** -/
theorem hasStrongCertificateBound_articulationPartitions :
    HasStrongCertificateBound (articulationPartitions (V := V))
      (min ((Fintype.card V).choose 2) (4 * Fintype.card V)) :=
  hasStrongCertificateBound_iff_size_le.mpr articulationPartitions_strongCertificateSize_le

/-! ## `k`-vertex-connectivity -/

/-- **`k`-vertex-connectivity**: `toGraph S` has more than `k` vertices, and deleting any set of
fewer than `k` vertices leaves a connected graph on the surviving vertices.  Mathlib has no such
predicate. -/
noncomputable def isVertexConnected (k : ℕ) (S : Finset (Edge V)) : Bool := by
  classical exact decide (k < Fintype.card V ∧
    ∀ X : Finset V, X.card < k → ((toGraph S).induce {z | z ∉ X}).Connected)

theorem isVertexConnected_eq_true_iff {k : ℕ} {S : Finset (Edge V)} :
    isVertexConnected k S = true ↔ k < Fintype.card V ∧
      ∀ X : Finset V, X.card < k → ((toGraph S).induce {z | z ∉ X}).Connected := by
  simp [isVertexConnected]

/-- **The profile for `k` determines `k`-vertex-connectivity**: for `k < v`, every coordinate of
the profile must relate every pair of surviving vertices. -/
theorem isVertexConnected_iff_vertexFailureProfile {k : ℕ} {S : Finset (Edge V)} :
    isVertexConnected k S = true ↔ k < Fintype.card V ∧
      ∀ (X : VertexFailureSet V k) (u w : V), u ∉ X.1 → w ∉ X.1 →
        (u, w) ∈ vertexFailureProfile k S X := by
  rw [isVertexConnected_eq_true_iff]
  refine and_congr_right fun hkv => ⟨fun h X u w hu hw => ?_, fun h X hX => ?_⟩
  · exact mem_vertexFailureProfile.mpr ⟨hu, hw, (h X.1 X.2).preconnected ⟨u, hu⟩ ⟨w, hw⟩⟩
  · obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := X)
      (t := Finset.univ) (by rw [Finset.card_univ]; omega)
    rw [connected_iff]
    refine ⟨fun a b => ?_, ⟨⟨z, hz⟩⟩⟩
    obtain ⟨_, _, hr⟩ := mem_vertexFailureProfile.mp (h ⟨X, hX⟩ a.1 b.1 a.2 b.2)
    exact hr

/-- The profile for `k` determines `k`-vertex-connectivity. -/
theorem isVertexConnected_eq_of_vertexFailureProfile {k : ℕ} {S T : Finset (Edge V)}
    (h : vertexFailureProfile k S = vertexFailureProfile k T) :
    isVertexConnected k S = isVertexConnected k T := by
  rw [Bool.eq_iff_iff, isVertexConnected_iff_vertexFailureProfile,
    isVertexConnected_iff_vertexFailureProfile, h]

/-- **`1`-vertex-connectivity is connectivity on at least two vertices.** -/
theorem isVertexConnected_one_iff {S : Finset (Edge V)} :
    isVertexConnected 1 S = true ↔ 1 < Fintype.card V ∧ (toGraph S).Connected := by
  rw [isVertexConnected_iff_vertexFailureProfile]
  refine and_congr_right fun hv => ?_
  have hX : ∀ X : VertexFailureSet V 1, X = ⟨∅, by simp⟩ := fun X =>
    Subtype.ext (Finset.card_eq_zero.mp (Nat.lt_one_iff.mp X.2))
  rw [connected_iff]
  constructor
  · intro h
    refine ⟨fun u w => ?_, Fintype.card_pos_iff.mp (by omega)⟩
    exact (mem_vertexFailureProfile_empty Nat.one_pos).mp
      (h ⟨∅, by simp⟩ u w (Finset.notMem_empty u) (Finset.notMem_empty w))
  · rintro ⟨h, -⟩ X u w - -
    rw [hX X]
    exact (mem_vertexFailureProfile_empty Nat.one_pos).mpr (h u w)

/-- **`k`-vertex-connectivity** (`sec:failure-profiles`): its certificate size is at most
`min{C(v, 2), 2kv}`. -/
theorem vertexConnectivity_strongCertificateSize_le (k : ℕ) :
    strongCertificateSize (isVertexConnected (V := V) k) ≤
      min ((Fintype.card V).choose 2) (2 * k * Fintype.card V) :=
  (strongCertificateSize_le_of_determined fun _ _ =>
    isVertexConnected_eq_of_vertexFailureProfile).trans
    (vertexFailureProfile_strongCertificateSize_le k)

/-- **Certificates for `k`-vertex-connectivity within `min{C(v, 2), 2kv}` edges.** -/
theorem hasStrongCertificateBound_isVertexConnected (k : ℕ) :
    HasStrongCertificateBound (isVertexConnected (V := V) k)
      (min ((Fintype.card V).choose 2) (2 * k * Fintype.card V)) :=
  hasStrongCertificateBound_iff_size_le.mpr (vertexConnectivity_strongCertificateSize_le k)

end MonoidProduct.Graph
