import MonoidProduct.Graph.FailureQueries
set_option linter.style.header false

/-!
# Acceptance statements for edge-failure profiles

The paper-facing statements of `monoid.tex`, section `sec:failure-profiles`, for edge failures:
`eq:edge-failure-profile`, the paragraph "Edge failures", the edge-failure half of
`eq:failure-profile-queries`, the readouts of the text after it, and the upper bound of
`prop:failure-profile-complexity` for `Σ^E_k`.  They are restated with the definitions unfolded
where that makes their meaning visible, followed by small sanity checks.  Lean checks every
`example` here against the library's statement.

* The profile: one coordinate for every set of fewer than `k` possible edges, present or absent,
  holding the full partition after their deletion.
* Union and certificates: a strong certificate is exactly a subgraph with the same profile.
* Successive spanning forests: `H = F_1 ∪ ⋯ ∪ F_k` with each `F_{i+1}` a spanning forest of what
  the earlier forests leave; `H` has at most `k(v - 1)` edges and the same profile.
* Truncation, `k = 0` and `k = 1`.
* Bridges (also by the number of components), the partitions after their deletion, and
  `k`-edge-connectivity, read off the profile.
* The list, matrix and adjacency-list bounds.

The sanity checks cover:
* the path `0 - 1 - 2`, both of whose edges are bridges, and which is not 2-edge-connected;
* the triangle, which has no bridge and is 2-edge-connected;
* a spanning tree of the triangle, with the same partition but not the same profile, so the
  profile is more than the partition and the extension clause matters;
* a failure set made of an absent edge;
* the constant profile at `k = 0`.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

/-! ## The profile and its certificates -/

section Statements

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`Σ^E_k`** (`eq:edge-failure-profile`): one coordinate for every set `F` of fewer than `k`
possible edges, present or absent, holding the full partition of `toGraph S \ toGraph F`. -/
example (k : ℕ) (S F : Finset (Edge V)) (hF : F.card < k) (u w : V) :
    edgeFailureProfile k S ⟨F, hF⟩ = connectedComponents (S \ F) ∧
      ((u, w) ∈ edgeFailureProfile k S ⟨F, hF⟩ ↔ (toGraph S \ toGraph F).Reachable u w) :=
  ⟨rfl, by rw [mem_edgeFailureProfile, toGraph_sdiff]⟩

/-- **Profiles combine under union**, so a strong certificate for the profile is exactly a
subgraph with the same profile; unfolded, `Σ^E_k(C ∪ K) = Σ^E_k(S ∪ K)` for every
extension `K`. -/
example (k : ℕ) (C S : Finset (Edge V)) :
    (IsStrongCertificate (edgeFailureProfile k) C S ↔
      C ⊆ S ∧ edgeFailureProfile k C = edgeFailureProfile k S) ∧
    (C ⊆ S → edgeFailureProfile k C = edgeFailureProfile k S →
      ∀ K, edgeFailureProfile k (C ∪ K) = edgeFailureProfile k (S ∪ K)) :=
  ⟨⟨fun h => ⟨h.1, h.2.apply_eq⟩, fun h => isStrongCertificate_edgeFailureProfile h.1 h.2⟩,
    fun hCS h K => (isStrongCertificate_edgeFailureProfile hCS h).2 K⟩

/-- **Successive spanning forests** (`sec:failure-profiles`, "Edge failures"):
`H = F_1 ∪ ⋯ ∪ F_k`, where `F_{i+1}` is a spanning forest of `S \ (F_1 ∪ ⋯ ∪ F_i)`.  The forests
are pairwise disjoint, `H ⊆ S` has at most `k(v - 1)` edges, and `π(H \ F) = π(S \ F)` for every
set `F` of fewer than `k` possible edges. -/
example (k i : ℕ) (S F : Finset (Edge V)) (hF : F.card < k) :
    forestStack S k = (Finset.range k).biUnion (forestLayer S) ∧
      forestLayer S i ⊆ S \ forestStack S i ∧ (toGraph (forestLayer S i)).IsAcyclic ∧
      (toGraph (forestLayer S i)).Reachable = (toGraph (S \ forestStack S i)).Reachable ∧
      (∀ j, i ≠ j → Disjoint (forestLayer S i) (forestLayer S j)) ∧
      forestStack S k ⊆ S ∧ (forestStack S k).card ≤ k * (Fintype.card V - 1) ∧
      connectedComponents (forestStack S k \ F) = connectedComponents (S \ F) :=
  ⟨forestStack_eq_biUnion S k, forestLayer_subset S i, isAcyclic_forestLayer S i,
    reachable_forestLayer S i, fun _ hij => disjoint_forestLayer S hij, forestStack_subset S k,
    card_forestStack_le S k, connectedComponents_forestStack_sdiff S hF⟩

/-- **`b_{Σ^E_k} ≤ k(v - 1)`**, capped by `C(v, 2)`, with the certificates. -/
example (k : ℕ) :
    strongCertificateSize (edgeFailureProfile (V := V) k) ≤
        min ((Fintype.card V).choose 2) (k * (Fintype.card V - 1)) ∧
      HasStrongCertificateBound (edgeFailureProfile (V := V) k) (k * (Fintype.card V - 1)) ∧
      HasStrongCertificateBound (edgeFailureProfile (V := V) k)
        (min ((Fintype.card V).choose 2) (k * (Fintype.card V - 1))) :=
  ⟨edgeFailureProfile_strongCertificateSize_le k, hasStrongCertificateBound_edgeFailureProfile k,
    hasStrongCertificateBound_min_edgeFailureProfile k⟩

/-- **Truncation, `k = 0` and `k = 1`**: the profile for `k' ≤ k` is a restriction of the profile
for `k`; at `k = 0` it is constant; at `k = 1` it is the component partition. -/
example (k k' : ℕ) (h : k' ≤ k) (S T : Finset (Edge V)) (F : EdgeFailureSet V k') :
    edgeFailureProfile k' S F = edgeFailureProfile k S ⟨F.1, F.2.trans_le h⟩ ∧
      strongCertificateSize (edgeFailureProfile (V := V) k') ≤
        strongCertificateSize (edgeFailureProfile (V := V) k) ∧
      strongCertificateSize (edgeFailureProfile (V := V) 0) = 0 ∧
      edgeFailureProfile 1 S ⟨∅, by simp⟩ = connectedComponents S ∧
      (edgeFailureProfile 1 S = edgeFailureProfile 1 T ↔
        connectedComponents S = connectedComponents T) ∧
      strongCertificateSize (edgeFailureProfile (V := V) 1) =
        strongCertificateSize (connectedComponents (V := V)) :=
  ⟨edgeFailureProfile_of_le h S F, edgeFailureProfile_strongCertificateSize_mono h,
    edgeFailureProfile_zero_strongCertificateSize, edgeFailureProfile_one S,
    edgeFailureProfile_one_eq_iff, edgeFailureProfile_one_strongCertificateSize⟩

/-! ## The readouts -/

/-- **Bridges**: an edge `e = s(u, w)` of `S` whose deletion disconnects `u` and `w`;
equivalently, whose deletion increases the number of components.  The profile for `k = 2`
determines them: `u` and `w` are connected before, and not after, deleting `e`. -/
example (S : Finset (Edge V)) (e : Edge V) (u w : V) (he : (e : Sym2 V) = s(u, w)) :
    (e ∈ bridges S ↔ e ∈ S ∧ ¬(toGraph (S \ {e})).Reachable u w) ∧
      (e ∈ bridges S ↔ e ∈ S ∧ Nat.card (toGraph S).ConnectedComponent <
        Nat.card (toGraph (S \ {e})).ConnectedComponent) ∧
      (e ∈ bridges S ↔ (u, w) ∈ edgeFailureProfile 2 S ⟨∅, by simp⟩ ∧
        (u, w) ∉ edgeFailureProfile 2 S ⟨{e}, by simp⟩) := by
  refine ⟨?_, mem_bridges_iff_card_lt, mem_bridges_iff_edgeFailureProfile he⟩
  rw [mem_bridges, isBridge_iff_not_reachable_sdiff he]

/-- **The bridges and the partitions after their deletion** (`sec:failure-profiles`): `some π(S \
{e})` for a bridge `e` and `none` otherwise; with the bridges, certificate size at most
`min{C(v, 2), 2(v - 1)}`. -/
example (S : Finset (Edge V)) (e : Edge V) (P : Finset (V × V)) :
    (bridgePartitions S e = some P ↔ e ∈ bridges S ∧ P = connectedComponents (S \ {e})) ∧
      (bridgePartitions S e = none ↔ e ∉ bridges S) ∧
      strongCertificateSize (bridges (V := V)) ≤
        min ((Fintype.card V).choose 2) (2 * (Fintype.card V - 1)) ∧
      strongCertificateSize (bridgePartitions (V := V)) ≤
        min ((Fintype.card V).choose 2) (2 * (Fintype.card V - 1)) ∧
      HasStrongCertificateBound (bridges (V := V))
        (min ((Fintype.card V).choose 2) (2 * (Fintype.card V - 1))) ∧
      HasStrongCertificateBound (bridgePartitions (V := V))
        (min ((Fintype.card V).choose 2) (2 * (Fintype.card V - 1))) :=
  ⟨bridgePartitions_eq_some_iff, bridgePartitions_eq_none_iff, bridges_strongCertificateSize_le,
    bridgePartitions_strongCertificateSize_le, hasStrongCertificateBound_bridges,
    hasStrongCertificateBound_bridgePartitions⟩

/-- **`k`-edge-connectivity** is Mathlib's `IsEdgeConnected`: every coordinate of the profile
relates every pair of vertices.  Certificate size at most `min{C(v, 2), k(v - 1)}`. -/
example (k : ℕ) (S : Finset (Edge V)) :
    (isEdgeConnected k S = true ↔ (toGraph S).IsEdgeConnected k) ∧
      ((toGraph S).IsEdgeConnected k ↔
        ∀ (F : EdgeFailureSet V k) (u w : V), (toGraph (S \ F.1)).Reachable u w) ∧
      strongCertificateSize (isEdgeConnected (V := V) k) ≤
        min ((Fintype.card V).choose 2) (k * (Fintype.card V - 1)) ∧
      HasStrongCertificateBound (isEdgeConnected (V := V) k)
        (min ((Fintype.card V).choose 2) (k * (Fintype.card V - 1))) := by
  refine ⟨isEdgeConnected_eq_true_iff, ?_, edgeConnectivity_strongCertificateSize_le k,
    hasStrongCertificateBound_isEdgeConnected k⟩
  simp only [isEdgeConnected_iff_edgeFailureProfile, mem_edgeFailureProfile]

end Statements

/-! ## Query bounds -/

section Queries

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **`eq:failure-profile-queries`** (edge failures) and **`prop:failure-profile-complexity`**
(upper bound for `Σ^E_k`): `Q_list(Σ^E_k; n) ≤ min{n, 2^18·√(n·k(v - 1))}` and
`Q_matrix(Σ^E_k) ≤ 2^18·min{v², v·√(v·k)}`, with the adjacency-list form. -/
example (k n m : ℕ) :
    (qList (edgeFailureProfile (V := V) k) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (k * (Fintype.card V - 1) : ℕ))) ∧
      (qMatrix (edgeFailureProfile (V := V) k) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
        (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (k * (Fintype.card V - 1) : ℕ))) ∧
      (qMatrix (edgeFailureProfile (V := V) k) : ℝ) ≤ 2 ^ 18 *
        min ((Fintype.card V : ℝ) ^ 2) (Fintype.card V * Real.sqrt (Fintype.card V * k)) ∧
      (qAdjEdges (edgeFailureProfile (V := V) k) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (k * (Fintype.card V - 1) : ℕ))) :=
  ⟨edgeFailureProfile_qList_le k n, edgeFailureProfile_qMatrix_le k,
    edgeFailureProfile_qMatrix_le_min k, edgeFailureProfile_qAdjEdges_le k m⟩

/-- **The bridges, and the partitions after their deletion**: `O(min{n, √(nv)})` edge-list
queries and `O(v^{3/2})` matrix queries, as `min{n, 2^18·√(n·2(v - 1))}` and `2^19·v·√v`. -/
example (n m : ℕ) :
    (qList (bridges (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * (Fintype.card V - 1) : ℕ))) ∧
      (qMatrix (bridges (V := V)) : ℝ) ≤ 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (bridges (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (2 * (Fintype.card V - 1) : ℕ))) ∧
      (qList (bridgePartitions (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * (Fintype.card V - 1) : ℕ))) ∧
      (qMatrix (bridgePartitions (V := V)) : ℝ)
        ≤ 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (bridgePartitions (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (2 * (Fintype.card V - 1) : ℕ))) :=
  ⟨bridges_qList_le n, bridges_qMatrix_le_mul_sqrt, bridges_qAdjEdges_le m,
    bridgePartitions_qList_le n, bridgePartitions_qMatrix_le_mul_sqrt,
    bridgePartitions_qAdjEdges_le m⟩

/-- **`k`-edge-connectivity**: the bounds of the profile. -/
example (k n m : ℕ) :
    (qList (isEdgeConnected (V := V) k) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (k * (Fintype.card V - 1) : ℕ))) ∧
      (qMatrix (isEdgeConnected (V := V) k) : ℝ) ≤ 2 ^ 18 *
        min ((Fintype.card V : ℝ) ^ 2) (Fintype.card V * Real.sqrt (Fintype.card V * k)) ∧
      (qAdjEdges (isEdgeConnected (V := V) k) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (k * (Fintype.card V - 1) : ℕ))) :=
  ⟨edgeConnectivity_qList_le k n, edgeConnectivity_qMatrix_le_min k,
    edgeConnectivity_qAdjEdges_le k m⟩

end Queries

/-! ## Sanity checks -/

section Sanity

/-- A vertex with no neighbours is reachable only from itself. -/
private theorem eq_of_reachable_of_isolated {V : Type*} {G : SimpleGraph V} {u w : V}
    (hw : ∀ x, ¬G.Adj w x) (h : G.Reachable u w) : u = w := by
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hw _)

private theorem adj_singleton {V : Type*} {e : Edge V} {u w : V} :
    (toGraph {e}).Adj u w ↔ (e : Sym2 V) = s(u, w) := by
  rw [toGraph_adj]
  simp

/-- The edges `{0, 1}`, `{1, 2}` and `{0, 2}` on three vertices. -/
private def e01 : Edge (Fin 3) := ⟨s(0, 1), by decide⟩
private def e12 : Edge (Fin 3) := ⟨s(1, 2), by decide⟩
private def e02 : Edge (Fin 3) := ⟨s(0, 2), by decide⟩

private theorem iso0 : ∀ x, ¬(toGraph {e12}).Adj 0 x := fun x h => by
  rw [adj_singleton] at h
  simp [e12] at h

private theorem iso2 : ∀ x, ¬(toGraph {e01}).Adj 2 x := fun x h => by
  rw [adj_singleton] at h
  simp [e01] at h

/-- The triangle with at most one edge deleted is connected. -/
private theorem reachable_univ_sdiff {F : Finset (Edge (Fin 3))} (hF : F.card ≤ 1) (u w : Fin 3) :
    (toGraph (Finset.univ \ F)).Reachable u w := by
  by_cases huw : u = w
  · subst huw
    rfl
  have key : ∀ a b : Fin 3, ∃ x, x ≠ a ∧ x ≠ b := by decide
  obtain ⟨x, hxu, hxw⟩ := key u w
  have hadj : ∀ (a b : Fin 3) (hab : a ≠ b),
      (⟨s(a, b), by simpa using hab⟩ : Edge (Fin 3)) ∉ F → (toGraph (Finset.univ \ F)).Adj a b :=
    fun a b hab h => toGraph_adj.mpr ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  by_cases hF' : (⟨s(u, w), by simpa using huw⟩ : Edge (Fin 3)) ∈ F
  · have h1 : (⟨s(u, x), by simpa using hxu.symm⟩ : Edge (Fin 3)) ∉ F := fun h => by
      have h' : s(u, x) = s(u, w) := congrArg Subtype.val (Finset.card_le_one.mp hF _ h _ hF')
      rcases Sym2.eq_iff.mp h' with ⟨-, h⟩ | ⟨h, -⟩
      exacts [hxw h, huw h]
    have h2 : (⟨s(x, w), by simpa using hxw⟩ : Edge (Fin 3)) ∉ F := fun h => by
      have h' : s(x, w) = s(u, w) := congrArg Subtype.val (Finset.card_le_one.mp hF _ h _ hF')
      rcases Sym2.eq_iff.mp h' with ⟨h, -⟩ | ⟨h, -⟩
      exacts [hxu h, hxw h]
    exact (hadj u x hxu.symm h1).reachable.trans (hadj x w hxw h2).reachable
  · exact (hadj u w huw hF').reachable

/-- **The path `0 - 1 - 2`**: both edges are bridges, and the path is not 2-edge-connected. -/
example : bridges ({e01, e12} : Finset (Edge (Fin 3))) = {e01, e12} ∧
    isEdgeConnected 2 ({e01, e12} : Finset (Edge (Fin 3))) = false := by
  have h01 : ¬(toGraph (({e01, e12} : Finset (Edge (Fin 3))) \ {e01})).Reachable 0 1 := by
    rw [show ({e01, e12} : Finset (Edge (Fin 3))) \ {e01} = {e12} by decide]
    exact fun h => absurd (eq_of_reachable_of_isolated iso0 h.symm) (by decide)
  have h12 : ¬(toGraph (({e01, e12} : Finset (Edge (Fin 3))) \ {e12})).Reachable 1 2 := by
    rw [show ({e01, e12} : Finset (Edge (Fin 3))) \ {e12} = {e01} by decide]
    exact fun h => absurd (eq_of_reachable_of_isolated iso2 h) (by decide)
  refine ⟨?_, ?_⟩
  · ext e
    rw [mem_bridges]
    refine ⟨fun h => h.1, fun he => ⟨he, ?_⟩⟩
    rcases Finset.mem_insert.mp he with rfl | he'
    · exact (isBridge_iff_not_reachable_sdiff (u := 0) (w := 1) rfl).mpr h01
    · rw [Finset.mem_singleton.mp he']
      exact (isBridge_iff_not_reachable_sdiff (u := 1) (w := 2) rfl).mpr h12
  · rw [Bool.eq_false_iff, ne_eq, isEdgeConnected_eq_true_iff,
      isEdgeConnected_iff_edgeFailureProfile]
    intro h
    exact h01 (mem_edgeFailureProfile.mp (h ⟨{e01}, by decide⟩ 0 1))

/-- **The triangle**: it has no bridge and is 2-edge-connected. -/
example : bridges (Finset.univ : Finset (Edge (Fin 3))) = ∅ ∧
    isEdgeConnected 2 (Finset.univ : Finset (Edge (Fin 3))) = true := by
  refine ⟨?_, ?_⟩
  · refine Finset.eq_empty_of_forall_notMem fun e he => ?_
    obtain ⟨u, w, hue⟩ := exists_edge_eq_mk e
    exact ((isBridge_iff_not_reachable_sdiff hue).mp (mem_bridges.mp he).2)
      (reachable_univ_sdiff (by simp) u w)
  · rw [isEdgeConnected_eq_true_iff, isEdgeConnected_iff_edgeFailureProfile]
    intro F u w
    exact mem_edgeFailureProfile.mpr (reachable_univ_sdiff (by have := F.2; omega) u w)

/-- **The profile is more than the partition**: the path `0 - 1 - 2` is a spanning tree of the
triangle, with the same partition, but not a strong certificate for the profile at `k = 2`:
deleting `{0, 1}` disconnects the path and not the triangle. -/
example : connectedComponents ({e01, e12} : Finset (Edge (Fin 3))) =
      connectedComponents Finset.univ ∧
    ¬IsStrongCertificate (edgeFailureProfile 2) {e01, e12} Finset.univ := by
  refine ⟨?_, fun hcert => ?_⟩
  · rw [connectedComponents_eq_iff]
    intro u w
    refine ⟨fun h => h.mono (toGraph_mono (Finset.subset_univ _)), fun _ => ?_⟩
    have r1 : ∀ x : Fin 3, (toGraph ({e01, e12} : Finset (Edge (Fin 3)))).Reachable 1 x := by
      intro x
      fin_cases x
      · exact (toGraph_adj.mpr ⟨e01, by simp, Sym2.eq_swap⟩).reachable
      · rfl
      · exact (toGraph_adj.mpr ⟨e12, by simp, rfl⟩).reachable
    exact (r1 u).symm.trans (r1 w)
  · have h := congrFun (extensionEquiv_edgeFailureProfile_iff.mp hcert.2) ⟨{e01}, by decide⟩
    have h1 : (0, 1) ∈ edgeFailureProfile 2 Finset.univ ⟨{e01}, by decide⟩ :=
      mem_edgeFailureProfile.mpr (reachable_univ_sdiff (by simp) 0 1)
    rw [← h, mem_edgeFailureProfile,
      show ({e01, e12} : Finset (Edge (Fin 3))) \ {e01} = {e12} by decide] at h1
    exact absurd (eq_of_reachable_of_isolated iso0 h1.symm) (by decide)

/-- **Absent edges are failure sets too**: deleting the absent edge `{0, 2}` from the path leaves
its partition unchanged. -/
example : edgeFailureProfile 2 ({e01, e12} : Finset (Edge (Fin 3))) ⟨{e02}, by decide⟩ =
    connectedComponents {e01, e12} := by
  change connectedComponents (({e01, e12} : Finset (Edge (Fin 3))) \ {e02}) = _
  rw [show ({e01, e12} : Finset (Edge (Fin 3))) \ {e02} = {e01, e12} by decide]

/-- **`k = 0`**: the profile has no coordinates and is the same for every graph. -/
example {V : Type*} [Fintype V] [DecidableEq V] (S T : Finset (Edge V)) :
    edgeFailureProfile 0 S = edgeFailureProfile 0 T :=
  funext fun F => absurd F.2 (Nat.not_lt_zero _)

end Sanity

end MonoidProduct.Graph
