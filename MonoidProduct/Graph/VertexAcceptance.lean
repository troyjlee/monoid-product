import MonoidProduct.Graph.VertexQueries
set_option linter.style.header false

/-!
# Acceptance statements for vertex-failure certificates

The paper-facing statements of `monoid.tex`, section `sec:failure-profiles`, for vertex
failures: the paragraph "Vertex failures" (the sparse certificate and `b_{Σ^V_k} = O(kv)`), the
vertex half of `eq:failure-profile-queries`, the readouts of the text after it, and
`prop:failure-profile-complexity` with both halves for both profiles.  They are restated with the
definitions unfolded where that makes their meaning visible, followed by small sanity checks.
Lean checks every `example` here against the library's statement.

* The sparse certificate: every graph `G` has a subgraph `H` with at most `2kv` edges such that
  `H − X` and `G − X` have the same reachability on `V \ X` for every `|X| < k`, in Mathlib's
  induced graphs.
* The greedy construction, the blocking property and the count, unfolded.
* Union and certificates: a strong certificate is exactly a subgraph with the same profile, and
  `b_{Σ^V_k} ≤ min{N, 2kv}`; truncation, `k = 0` and `k = 1`.
* Articulation points (by the number of components, and by separation), the partitions after
  their deletion, and `k`-vertex-connectivity, read off the profile.
* The list, matrix and adjacency-list bounds, `eq:failure-profile-queries` for both profiles, and
  `prop:failure-profile-complexity` over its whole range, with its upper end `k = v`, where both
  profiles cost `Θ(v²)`.

The sanity checks cover:
* the path `0 - 1 - 2`: its middle vertex is an articulation point and an end is not; it is
  `1`-vertex-connected and not `2`-vertex-connected;
* the complete graph on `v` vertices, which is `k`-vertex-connected exactly when `k < v`;
* the constant profile at `k = 0`.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

/-! ## The certificate -/

section Statements

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The sparse vertex-connectivity certificate** (`sec:failure-profiles`, "Vertex failures"):
every graph has a subgraph `H ⊆ G` with at most `2kv` edges and `π(H − X) = π(G − X)` for every
set `X` of fewer than `k` vertices.  The partitions are compared as the reachability relations
of the graphs induced on `V \ X`. -/
example (k : ℕ) (S : Finset (Edge V)) :
    ∃ H ⊆ S, H.card ≤ 2 * k * Fintype.card V ∧ ∀ X : Finset V, X.card < k →
      ((toGraph H).induce {z | z ∉ X}).Reachable = ((toGraph S).induce {z | z ∉ X}).Reachable := by
  obtain ⟨H, hHS, hcard, hprof⟩ := exists_vertexFailureCertificate k S
  exact ⟨H, hHS, hcard, vertexFailureProfile_eq_iff.mp hprof⟩

/-- **The profile through edge sets**: the coordinate at `X` relates `u` and `w` exactly when both
survive and they are connected using the edges of `S` with both ends outside `X`. -/
example (k : ℕ) (S : Finset (Edge V)) (X : Finset V) (hX : X.card < k) (u w : V) (e : Edge V)
    (W : Finset V) :
    ((u, w) ∈ vertexFailureProfile k S ⟨X, hX⟩ ↔
      u ∉ X ∧ w ∉ X ∧ (toGraph (edgesWithin Xᶜ S)).Reachable u w) ∧
    (e ∈ edgesWithin W S ↔ e ∈ S ∧ ∀ z ∈ (e : Sym2 V), z ∈ W) :=
  ⟨mem_vertexFailureProfile_iff_edgesWithin, mem_edgesWithin⟩

/-- **The greedy construction**, unfolded: an edge is separable in `T` when fewer than `k`
vertices, avoiding both of its ends, separate them in the graph induced on the other vertices;
the edges of `S` are processed in the order of `S.toList`, and an edge is kept exactly when it is
separable in the edges kept so far. -/
example (k : ℕ) (S H : Finset (Edge V)) (e : Edge V) :
    (Separable k H e ↔ ∃ X : Finset V, X.card < k ∧ ∃ u w, (e : Sym2 V) = s(u, w) ∧
      ∃ (hu : u ∉ X) (hw : w ∉ X),
        ¬((toGraph H).induce {z | z ∉ X}).Reachable ⟨u, hu⟩ ⟨w, hw⟩) ∧
    (Separable k H e → greedyStep k H e = insert e H) ∧
    (¬Separable k H e → greedyStep k H e = H) ∧
    greedyCert k S = S.toList.foldl (greedyStep k) ∅ := by
  refine ⟨⟨?_, ?_⟩, greedyStep_of_separable, greedyStep_of_not_separable, rfl⟩
  · rintro ⟨X, hX, u, w, he, hu, hw, hr⟩
    exact ⟨X, hX, u, w, he, hu, hw, fun h => hr ((reachable_induce_compl_iff hu hw).mp h)⟩
  · rintro ⟨X, hX, u, w, he, hu, hw, hr⟩
    exact ⟨X, hX, u, w, he, hu, hw, fun h => hr ((reachable_induce_compl_iff hu hw).mpr h)⟩

/-- **The greedy certificate** is a subgraph with the same vertex profile.  It is blocking: every
nonempty set `T` of its edges contains an edge separable in `T` without it.  Blocking edge sets
have at most `2kv` edges. -/
example (k : ℕ) (S H : Finset (Edge V)) :
    greedyCert k S ⊆ S ∧
      vertexFailureProfile k (greedyCert k S) = vertexFailureProfile k S ∧
      (Blocking k H ↔ ∀ T ⊆ H, T.Nonempty → ∃ e ∈ T, Separable k (T.erase e) e) ∧
      Blocking k (greedyCert k S) ∧
      (Blocking k H → H.card ≤ 2 * k * Fintype.card V) ∧
      (greedyCert k S).card ≤ 2 * k * Fintype.card V :=
  ⟨greedyCert_subset k S, vertexFailureProfile_greedyCert k S, Iff.rfl, blocking_greedyCert k S,
    card_le_of_blocking, card_greedyCert_le k S⟩

/-- **The counting argument**: for `k ≥ 1`, a vertex set `W` with `|W| ≥ 2k` has at most
`2k(|W| - k)` edges of a blocking `H` inside it. -/
example (k : ℕ) (hk : 1 ≤ k) (H : Finset (Edge V)) (hH : Blocking k H) (W : Finset V)
    (hW : 2 * k ≤ W.card) : (edgesWithin W H).card ≤ 2 * k * (W.card - k) :=
  card_edgesWithin_le_of_blocking hk hH hW

/-- **Profiles combine under union**, so a strong certificate for the vertex profile is exactly
a subgraph with the same profile; unfolded, `Σ^V_k(C ∪ K) = Σ^V_k(S ∪ K)` for every
extension `K`. -/
example (k : ℕ) (C S : Finset (Edge V)) :
    (IsStrongCertificate (vertexFailureProfile k) C S ↔
      C ⊆ S ∧ vertexFailureProfile k C = vertexFailureProfile k S) ∧
    (C ⊆ S → vertexFailureProfile k C = vertexFailureProfile k S →
      ∀ K, vertexFailureProfile k (C ∪ K) = vertexFailureProfile k (S ∪ K)) :=
  ⟨⟨fun h => ⟨h.1, h.2.apply_eq⟩, fun h => isStrongCertificate_vertexFailureProfile h.1 h.2⟩,
    fun hCS h K => (isStrongCertificate_vertexFailureProfile hCS h).2 K⟩

/-- **`b_{Σ^V_k} ≤ 2kv`** (`sec:failure-profiles`, "Vertex failures"), capped by `C(v, 2)`, with
the certificates. -/
example (k : ℕ) :
    strongCertificateSize (vertexFailureProfile (V := V) k) ≤
        min ((Fintype.card V).choose 2) (2 * k * Fintype.card V) ∧
      HasStrongCertificateBound (vertexFailureProfile (V := V) k) (2 * k * Fintype.card V) ∧
      HasStrongCertificateBound (vertexFailureProfile (V := V) k)
        (min ((Fintype.card V).choose 2) (2 * k * Fintype.card V)) :=
  ⟨vertexFailureProfile_strongCertificateSize_le k,
    hasStrongCertificateBound_vertexFailureProfile k,
    hasStrongCertificateBound_min_vertexFailureProfile k⟩

/-- **Truncation, `k = 0` and `k = 1`** for certificate sizes. -/
example (k k' : ℕ) (h : k' ≤ k) :
    strongCertificateSize (vertexFailureProfile (V := V) k') ≤
        strongCertificateSize (vertexFailureProfile (V := V) k) ∧
      strongCertificateSize (vertexFailureProfile (V := V) 0) = 0 ∧
      strongCertificateSize (vertexFailureProfile (V := V) 1) =
        strongCertificateSize (connectedComponents (V := V)) :=
  ⟨vertexFailureProfile_strongCertificateSize_mono h,
    vertexFailureProfile_zero_strongCertificateSize,
    vertexFailureProfile_one_strongCertificateSize⟩

/-! ## The readouts -/

/-- **Articulation points**: the vertices whose deletion increases the number of components;
equivalently, those separating two other vertices of one component.  The profile for `k = 2`
determines them, with certificate size at most `min{C(v, 2), 4v}`. -/
example (S : Finset (Edge V)) (x : V) :
    (x ∈ articulationPoints S ↔ Nat.card (toGraph S).ConnectedComponent <
      Nat.card ((toGraph S).induce {z | z ≠ x}).ConnectedComponent) ∧
    (x ∈ articulationPoints S ↔ ∃ a b, ∃ (ha : a ≠ x) (hb : b ≠ x), (toGraph S).Reachable a b ∧
      ¬((toGraph S).induce {z | z ≠ x}).Reachable ⟨a, ha⟩ ⟨b, hb⟩) ∧
    (x ∈ articulationPoints S ↔ ∃ a b, a ≠ x ∧ b ≠ x ∧
      (a, b) ∈ vertexFailureProfile 2 S ⟨∅, by simp⟩ ∧
      (a, b) ∉ vertexFailureProfile 2 S ⟨{x}, by simp⟩) ∧
    strongCertificateSize (articulationPoints (V := V)) ≤
      min ((Fintype.card V).choose 2) (4 * Fintype.card V) ∧
    HasStrongCertificateBound (articulationPoints (V := V))
      (min ((Fintype.card V).choose 2) (4 * Fintype.card V)) :=
  ⟨mem_articulationPoints, mem_articulationPoints_iff_separates,
    mem_articulationPoints_iff_vertexFailureProfile, articulationPoints_strongCertificateSize_le,
    hasStrongCertificateBound_articulationPoints⟩

/-- **The articulation points and the partitions after their deletion**: `some π(G − x)`, the
partition of `V \ {x}` in the graph induced on it, for an articulation point `x`, and `none`
otherwise; certificate size at most `min{C(v, 2), 4v}`. -/
example (S : Finset (Edge V)) (x a b : V) (P : Finset (V × V)) :
    (articulationPartitions S x = some P ↔
      x ∈ articulationPoints S ∧ P = deletionPartition S x) ∧
    (articulationPartitions S x = none ↔ x ∉ articulationPoints S) ∧
    ((a, b) ∈ deletionPartition S x ↔ ∃ (ha : a ≠ x) (hb : b ≠ x),
      ((toGraph S).induce {z | z ≠ x}).Reachable ⟨a, ha⟩ ⟨b, hb⟩) ∧
    deletionPartition S x = vertexFailureProfile 2 S ⟨{x}, by simp⟩ ∧
    strongCertificateSize (articulationPartitions (V := V)) ≤
      min ((Fintype.card V).choose 2) (4 * Fintype.card V) ∧
    HasStrongCertificateBound (articulationPartitions (V := V))
      (min ((Fintype.card V).choose 2) (4 * Fintype.card V)) :=
  ⟨articulationPartitions_eq_some_iff, articulationPartitions_eq_none_iff, mem_deletionPartition,
    deletionPartition_eq_vertexFailureProfile S x, articulationPartitions_strongCertificateSize_le,
    hasStrongCertificateBound_articulationPartitions⟩

/-- **`k`-vertex-connectivity**: more than `k` vertices, and `G − X` connected for every set `X`
of fewer than `k` vertices.  The profile for `k` decides it, with certificate size at most
`min{C(v, 2), 2kv}`; for `k = 1` it is connectivity on at least two vertices. -/
example (k : ℕ) (S : Finset (Edge V)) :
    (isVertexConnected k S = true ↔ k < Fintype.card V ∧
      ∀ X : Finset V, X.card < k → ((toGraph S).induce {z | z ∉ X}).Connected) ∧
    (isVertexConnected k S = true ↔ k < Fintype.card V ∧
      ∀ (X : VertexFailureSet V k) (u w : V), u ∉ X.1 → w ∉ X.1 →
        (u, w) ∈ vertexFailureProfile k S X) ∧
    (isVertexConnected 1 S = true ↔ 1 < Fintype.card V ∧ (toGraph S).Connected) ∧
    strongCertificateSize (isVertexConnected (V := V) k) ≤
      min ((Fintype.card V).choose 2) (2 * k * Fintype.card V) ∧
    HasStrongCertificateBound (isVertexConnected (V := V) k)
      (min ((Fintype.card V).choose 2) (2 * k * Fintype.card V)) :=
  ⟨isVertexConnected_eq_true_iff, isVertexConnected_iff_vertexFailureProfile,
    isVertexConnected_one_iff, vertexConnectivity_strongCertificateSize_le k,
    hasStrongCertificateBound_isVertexConnected k⟩

end Statements

/-! ## Query bounds -/

section Queries

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **`eq:failure-profile-queries`**: `max{Q_list(Σ^E_k; n), Q_list(Σ^V_k; n)} ≤
min{n, 2^18·√(n·2kv)}`, the paper's `O(min{n, √(nkv)})`; the vertex profile also has the matrix
and adjacency-list forms. -/
example (k n m : ℕ) :
    max (qList (edgeFailureProfile (V := V) k) n : ℝ) (qList (vertexFailureProfile (V := V) k) n)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * k * Fintype.card V : ℕ))) ∧
      (qMatrix (vertexFailureProfile (V := V) k) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
        (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (2 * k * Fintype.card V : ℕ))) ∧
      (qAdjEdges (vertexFailureProfile (V := V) k) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (2 * k * Fintype.card V : ℕ))) :=
  ⟨failureProfiles_qList_le k n, vertexFailureProfile_qMatrix_le k,
    vertexFailureProfile_qAdjEdges_le k m⟩

/-- **`prop:failure-profile-complexity`**: for every `v ≥ 2` and every `k`, both profiles cost
`Θ(min{v², v^{3/2}·√k})` matrix queries, with the constants `1/10000` and `2^18`. -/
example (hv : 2 ≤ Fintype.card V) (k : ℕ) :
    ((1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (edgeFailureProfile (V := V) k) ∧
    (qMatrix (edgeFailureProfile (V := V) k) : ℝ) ≤
      2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k))) ∧
    ((1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (vertexFailureProfile (V := V) k) ∧
    (qMatrix (vertexFailureProfile (V := V) k) : ℝ) ≤
      2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k))) :=
  failureProfiles_qMatrix_theta hv k

/-- **The paper's range** `1 ≤ k ≤ v` is a special case. -/
example (hv : 2 ≤ Fintype.card V) (k : ℕ) (_hk1 : 1 ≤ k) (_hkv : k ≤ Fintype.card V) :
    (1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (vertexFailureProfile (V := V) k) ∧
    (qMatrix (vertexFailureProfile (V := V) k) : ℝ) ≤
      2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) :=
  vertexFailureProfile_qMatrix_theta hv k

/-- **The upper end of the range**, `k = v`: the scale `min{v², v·√(v·k)}` is `v²`, so both
profiles cost `Θ(v²)` matrix queries, the cost of reading all `C(v, 2)` pairs up to constants. -/
example (hv : 2 ≤ Fintype.card V) :
    ((1 / 10000 : ℝ) * (Fintype.card V : ℝ) ^ 2 ≤
        qMatrix (edgeFailureProfile (V := V) (Fintype.card V)) ∧
      (qMatrix (edgeFailureProfile (V := V) (Fintype.card V)) : ℝ) ≤
        2 ^ 18 * (Fintype.card V : ℝ) ^ 2) ∧
    ((1 / 10000 : ℝ) * (Fintype.card V : ℝ) ^ 2 ≤
        qMatrix (vertexFailureProfile (V := V) (Fintype.card V)) ∧
      (qMatrix (vertexFailureProfile (V := V) (Fintype.card V)) : ℝ) ≤
        2 ^ 18 * (Fintype.card V : ℝ) ^ 2) := by
  have h := failureProfiles_qMatrix_theta hv (Fintype.card V)
  rwa [Real.sqrt_mul_self (Nat.cast_nonneg _), ← sq, min_self] at h

/-- **The articulation points, and the partitions after their deletion**:
`O(min{n, √(nv)})` edge-list queries and `O(v^{3/2})` matrix queries, as
`min{n, 2^18·√(n·4v)}` and `2^19·v·√v`. -/
example (n m : ℕ) :
    (qList (articulationPoints (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (4 * Fintype.card V : ℕ))) ∧
      (qMatrix (articulationPoints (V := V)) : ℝ) ≤
        2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (articulationPoints (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (4 * Fintype.card V : ℕ))) ∧
      (qList (articulationPartitions (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (4 * Fintype.card V : ℕ))) ∧
      (qMatrix (articulationPartitions (V := V)) : ℝ)
        ≤ 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (articulationPartitions (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (4 * Fintype.card V : ℕ))) :=
  ⟨articulationPoints_qList_le n, articulationPoints_qMatrix_le_mul_sqrt,
    articulationPoints_qAdjEdges_le m, articulationPartitions_qList_le n,
    articulationPartitions_qMatrix_le_mul_sqrt, articulationPartitions_qAdjEdges_le m⟩

/-- **`k`-vertex-connectivity**: the bounds of the profile. -/
example (k n m : ℕ) :
    (qList (isVertexConnected (V := V) k) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * k * Fintype.card V : ℕ))) ∧
      (qMatrix (isVertexConnected (V := V) k) : ℝ) ≤ 2 ^ 18 *
        min ((Fintype.card V : ℝ) ^ 2) (Fintype.card V * Real.sqrt (Fintype.card V * k)) ∧
      (qAdjEdges (isVertexConnected (V := V) k) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (2 * k * Fintype.card V : ℕ))) :=
  ⟨vertexConnectivity_qList_le k n, vertexConnectivity_qMatrix_le_min k,
    vertexConnectivity_qAdjEdges_le k m⟩

end Queries

/-! ## Sanity checks -/

section Sanity

/-- The edges `{0, 1}` and `{1, 2}` on three vertices. -/
private def e01 : Edge (Fin 3) := ⟨s(0, 1), by decide⟩
private def e12 : Edge (Fin 3) := ⟨s(1, 2), by decide⟩

/-- Without the middle vertex of the path `0 - 1 - 2`, the ends are not connected. -/
private theorem path_not_reachable {s : Set (Fin 3)} (hs : (1 : Fin 3) ∉ s) (h0 : (0 : Fin 3) ∈ s)
    (h2 : (2 : Fin 3) ∈ s) :
    ¬((toGraph ({e01, e12} : Finset (Edge (Fin 3)))).induce s).Reachable ⟨0, h0⟩ ⟨2, h2⟩ := by
  intro h
  have hiso : ∀ z, ¬((toGraph ({e01, e12} : Finset (Edge (Fin 3)))).induce s).Adj ⟨0, h0⟩ z := by
    intro z hz
    have hadj : (toGraph ({e01, e12} : Finset (Edge (Fin 3)))).Adj 0 z.1 := hz
    obtain ⟨e, he, hez⟩ := toGraph_adj.mp hadj
    have hz1 : z.1 ≠ 1 := fun h => hs (h ▸ z.2)
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Sym2.eq_iff.mp hez with ⟨-, h⟩ | ⟨-, h⟩
      · exact hz1 h.symm
      · exact absurd (h : (1 : Fin 3) = 0) (by decide)
    · rw [Finset.mem_singleton.mp he] at hez
      rcases Sym2.eq_iff.mp hez with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd (h : (1 : Fin 3) = 0) (by decide)
      · exact absurd (h : (2 : Fin 3) = 0) (by decide)
  have := eq_of_reachable_of_forall_not_adj hiso h
  have h20 : (2 : Fin 3) = 0 := congrArg Subtype.val this
  exact absurd h20 (by decide)

/-- The path `0 - 1 - 2` is connected. -/
private theorem path_connected : (toGraph ({e01, e12} : Finset (Edge (Fin 3)))).Connected := by
  have r1 : ∀ x : Fin 3, (toGraph ({e01, e12} : Finset (Edge (Fin 3)))).Reachable 1 x := by
    intro x
    fin_cases x
    · exact (toGraph_adj.mpr ⟨e01, by simp, Sym2.eq_swap⟩).reachable
    · rfl
    · exact (toGraph_adj.mpr ⟨e12, by simp, rfl⟩).reachable
  exact (connected_iff _).mpr ⟨fun u w => (r1 u).symm.trans (r1 w), ⟨0⟩⟩

/-- **The path `0 - 1 - 2`**: its middle vertex is an articulation point and its end `0` is not;
it is `1`-vertex-connected and not `2`-vertex-connected. -/
example : (1 : Fin 3) ∈ articulationPoints ({e01, e12} : Finset (Edge (Fin 3))) ∧
    (0 : Fin 3) ∉ articulationPoints ({e01, e12} : Finset (Edge (Fin 3))) ∧
    isVertexConnected 1 ({e01, e12} : Finset (Edge (Fin 3))) = true ∧
    isVertexConnected 2 ({e01, e12} : Finset (Edge (Fin 3))) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_articulationPoints_iff_separates]
    exact ⟨0, 2, by decide, by decide, path_connected.preconnected 0 2,
      path_not_reachable (s := {z | z ≠ 1}) (by simp) (by decide) (by decide)⟩
  · rw [mem_articulationPoints_iff_separates]
    rintro ⟨a, b, ha, hb, -, hsep⟩
    apply hsep
    have key : ∀ (c : Fin 3) (hc : c ≠ 0),
        ((toGraph ({e01, e12} : Finset (Edge (Fin 3)))).induce {z | z ≠ 0}).Reachable
          ⟨1, by decide⟩ ⟨c, hc⟩ := by
      intro c hc
      fin_cases c
      · exact absurd rfl hc
      · rfl
      · have h12 : ((toGraph ({e01, e12} : Finset (Edge (Fin 3)))).induce {z | z ≠ 0}).Adj
            ⟨1, by decide⟩ ⟨2, by decide⟩ := toGraph_adj.mpr ⟨e12, by simp, rfl⟩
        exact h12.reachable
    exact (key a ha).symm.trans (key b hb)
  · exact isVertexConnected_one_iff.mpr ⟨by simp, path_connected⟩
  · rw [Bool.eq_false_iff, ne_eq, isVertexConnected_eq_true_iff]
    rintro ⟨-, h⟩
    exact path_not_reachable (s := {z | z ∉ ({1} : Finset (Fin 3))}) (by simp) (by decide)
      (by decide) ((h {1} (by decide)).preconnected _ _)

/-- **The complete graph** on `v` vertices is `k`-vertex-connected exactly when `k < v`. -/
example {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ) :
    isVertexConnected k (Finset.univ : Finset (Edge V)) = true ↔ k < Fintype.card V := by
  rw [isVertexConnected_eq_true_iff]
  refine ⟨fun h => h.1, fun hk => ⟨hk, fun X hX => ?_⟩⟩
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := X) (t := Finset.univ)
    (by rw [Finset.card_univ]; omega)
  rw [connected_iff]
  refine ⟨fun a b => ?_, ⟨⟨z, hz⟩⟩⟩
  by_cases hab : a = b
  · rw [hab]
  · have hadj : (toGraph (Finset.univ : Finset (Edge V))).Adj a b := by
      rw [toGraph_univ]
      exact (top_adj _ _).mpr fun h => hab (Subtype.ext h)
    exact Adj.reachable (G := (toGraph Finset.univ).induce {z | z ∉ X}) hadj

/-- **`k = 0`**: the profile has no coordinates and is the same for every graph; every graph on
at least one vertex is `0`-vertex-connected. -/
example {V : Type*} [Fintype V] [DecidableEq V] (S T : Finset (Edge V)) :
    vertexFailureProfile 0 S = vertexFailureProfile 0 T ∧
      (isVertexConnected 0 S = true ↔ 0 < Fintype.card V) := by
  refine ⟨vertexFailureProfile_zero S T, ?_⟩
  rw [isVertexConnected_eq_true_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun X hX => absurd hX (Nat.not_lt_zero _)⟩⟩

end Sanity

end MonoidProduct.Graph
