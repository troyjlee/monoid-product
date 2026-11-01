import MonoidProduct.Graph.FailureLower
import MonoidProduct.Graph.VertexReadouts
set_option linter.style.header false

/-!
# Query bounds for vertex-failure profiles

`monoid.tex`, section `sec:failure-profiles`: the vertex-failure half of
`eq:failure-profile-queries`, the upper bound of `prop:failure-profile-complexity` for `Σ^V_k`
(which, with the lower bound of `Graph/FailureLower.lean`, gives both halves), and the query
bounds of the articulation-point and `k`-vertex-connectivity readouts.  Write `v = #V` and
`N = C(v, 2)`.  Error `1/3` throughout, and every constant is explicit.

* `vertexFailureProfile_qList_le` (`eq:failure-profile-queries`):
  `Q_list(Σ^V_k; n) ≤ min{n, 2^18·√(n·2kv)}`.  With the edge half, `failureProfiles_qList_le`
  bounds the larger of the two by the same quantity, the paper's `O(min{n, √(nkv)})`.
* `vertexFailureProfile_qMatrix_le_min` (`prop:failure-profile-complexity`, upper bound):
  `Q_matrix(Σ^V_k) ≤ 2^18·min{v², v·√(v·k)}` for every `v` and `k`.
  `vertexFailureProfile_qMatrix_theta` adds the lower bound `(1/10000)·min{v², v·√(v·k)}` for
  `v ≥ 2`: `Θ(min{v², v^{3/2}·√k})`, as for edge failures (`failureProfiles_qMatrix_theta`).
* The articulation points, and the articulation points with the partitions after their
  deletion, from the profile for `k = 2`: `Q_list ≤ min{n, 2^18·√(n·4v)}` and
  `Q_matrix ≤ 2^19·v·√v`, the paper's `O(min{n, √(nv)})` and `O(v^{3/2})`.
* `k`-vertex-connectivity: the bounds of the profile.

All of them follow from the certificate sizes of `Graph/VertexCertificate.lean` and
`Graph/VertexReadouts.lean` through `eq:graph-certificate-list` and
`eq:graph-certificate-matrix` (`Graph/Quantum.lean`).  Since `2·C(v, 2) ≤ v²`, the certificate
bound `2kv` keeps the constant `2^18` of the edge half.  Each output also has an adjacency-list
bound.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

variable {V O : Type} [Fintype V] [DecidableEq V] [DecidableEq O]

/-! ## Two matrix forms -/

omit [DecidableEq V] in
/-- `2·C(v, 2) ≤ v²`. -/
theorem two_mul_choose_two_le_sq :
    2 * ((Fintype.card V).choose 2 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have h : 2 * (Fintype.card V).choose 2 ≤ Fintype.card V ^ 2 := by
    rw [Nat.choose_two_right, sq]
    exact (Nat.mul_div_le _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  exact_mod_cast h

/-- **Certificates of at most `2kv` edges give `Q_matrix ≤ 2^18·min{v², v·√(v·k)}`.** -/
theorem qMatrix_le_mul_min_of_le_two_mul {f : Finset (Edge V) → O} {k : ℕ}
    (h : strongCertificateSize f ≤ 2 * k * Fintype.card V) :
    (qMatrix f : ℝ) ≤ 2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2)
      (Fintype.card V * Real.sqrt (Fintype.card V * k)) := by
  refine (qMatrix_le_min_sqrt_of_le h).trans ?_
  rw [mul_min_of_nonneg _ _ (by positivity)]
  have hv : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hN2 := two_mul_choose_two_le_sq (V := V)
  refine min_le_min (by nlinarith) ?_
  gcongr
  calc Real.sqrt ((Fintype.card V).choose 2 * (2 * k * Fintype.card V : ℕ))
      ≤ Real.sqrt ((Fintype.card V : ℝ) ^ 2 * (Fintype.card V * k)) := by
        apply Real.sqrt_le_sqrt
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right hN2 (mul_nonneg hk hv)]
    _ = Fintype.card V * Real.sqrt (Fintype.card V * k) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hv]

/-- **Certificates of at most `4v` edges give `Q_matrix ≤ 2^19·v·√v`.** -/
theorem qMatrix_le_two_pow_mul_sqrt_of_le_four {f : Finset (Edge V) → O}
    (h : strongCertificateSize f ≤ 4 * Fintype.card V) :
    (qMatrix f : ℝ) ≤ 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) := by
  refine (qMatrix_le_mul_sqrt_of_le h).trans (le_of_eq ?_)
  have h4 : Real.sqrt ((4 * Fintype.card V : ℕ) : ℝ) = 2 * Real.sqrt (Fintype.card V) := by
    push_cast
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [h4]
  ring

/-! ## The profile -/

/-- **`eq:failure-profile-queries`, vertex failures**: from an edge list of length `n`,
`Q_list(Σ^V_k; n) ≤ min{n, 2^18·√(n·2kv)}`, the paper's `O(min{n, √(nkv)})`. -/
theorem vertexFailureProfile_qList_le (k n : ℕ) :
    (qList (vertexFailureProfile (V := V) k) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * k * Fintype.card V : ℕ))) :=
  qList_le_min_sqrt_of_le ((vertexFailureProfile_strongCertificateSize_le k).trans
    (min_le_right _ _)) n

/-- **`eq:failure-profile-queries`**: both profiles from an edge list of length `n`,
`max{Q_list(Σ^E_k; n), Q_list(Σ^V_k; n)} ≤ min{n, 2^18·√(n·2kv)}`. -/
theorem failureProfiles_qList_le (k n : ℕ) :
    max (qList (edgeFailureProfile (V := V) k) n : ℝ) (qList (vertexFailureProfile (V := V) k) n)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * k * Fintype.card V : ℕ))) := by
  have hkv : k * (Fintype.card V - 1) ≤ 2 * k * Fintype.card V :=
    calc k * (Fintype.card V - 1) ≤ k * Fintype.card V := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ 2 * k * Fintype.card V := Nat.mul_le_mul_right _ (by omega)
  exact max_le (qList_le_min_sqrt_of_le (((edgeFailureProfile_strongCertificateSize_le k).trans
    (min_le_right _ _)).trans hkv) n) (vertexFailureProfile_qList_le k n)

/-- **The vertex-failure profile from an adjacency matrix**:
`Q_matrix(Σ^V_k) ≤ min{N, 2^18·√(N·2kv)}`. -/
theorem vertexFailureProfile_qMatrix_le (k : ℕ) :
    (qMatrix (vertexFailureProfile (V := V) k) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (2 * k * Fintype.card V : ℕ))) :=
  qMatrix_le_min_sqrt_of_le ((vertexFailureProfile_strongCertificateSize_le k).trans
    (min_le_right _ _))

/-- **`prop:failure-profile-complexity`, upper bound for vertex failures**:
`Q_matrix(Σ^V_k) ≤ 2^18·min{v², v·√(v·k)}`, that is `O(min{v², v^{3/2}·√k})`, for every `v` and
`k`. -/
theorem vertexFailureProfile_qMatrix_le_min (k : ℕ) :
    (qMatrix (vertexFailureProfile (V := V) k) : ℝ)
      ≤ 2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2) (Fintype.card V * Real.sqrt (Fintype.card V * k)) :=
  qMatrix_le_mul_min_of_le_two_mul ((vertexFailureProfile_strongCertificateSize_le k).trans
    (min_le_right _ _))

/-- **`prop:failure-profile-complexity` for vertex failures**: for every `v ≥ 2` and every `k`,
`(1/10000)·min{v², v·√(v·k)} ≤ Q_matrix(Σ^V_k) ≤ 2^18·min{v², v·√(v·k)}`, that is
`Θ(min{v², v^{3/2}·√k})`. -/
theorem vertexFailureProfile_qMatrix_theta (hv : 2 ≤ Fintype.card V) (k : ℕ) :
    (1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (vertexFailureProfile (V := V) k) ∧
    (qMatrix (vertexFailureProfile (V := V) k) : ℝ) ≤
      2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) :=
  ⟨vertexFailureProfile_qMatrix_ge hv k, vertexFailureProfile_qMatrix_le_min k⟩

/-- **`prop:failure-profile-complexity`**: for every `v ≥ 2` and every `k`, both profiles have
`(1/10000)·min{v², v·√(v·k)} ≤ Q_matrix ≤ 2^18·min{v², v·√(v·k)}`. -/
theorem failureProfiles_qMatrix_theta (hv : 2 ≤ Fintype.card V) (k : ℕ) :
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
  ⟨edgeFailureProfile_qMatrix_theta hv k, vertexFailureProfile_qMatrix_theta hv k⟩

/-- **The vertex-failure profile from adjacency lists**:
`Q_adj(Σ^V_k; m) ≤ min{2m, 2^19·√(m·2kv)}`. -/
theorem vertexFailureProfile_qAdjEdges_le (k m : ℕ) :
    (qAdjEdges (vertexFailureProfile (V := V) k) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (2 * k * Fintype.card V : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le ((vertexFailureProfile_strongCertificateSize_le k).trans
    (min_le_right _ _)) m

/-! ## Articulation points -/

/-- **The articulation points from an edge list** (`sec:failure-profiles`):
`Q_list(articulation points; n) ≤ min{n, 2^18·√(n·4v)}`, the paper's `O(min{n, √(nv)})`. -/
theorem articulationPoints_qList_le (n : ℕ) :
    (qList (articulationPoints (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (4 * Fintype.card V : ℕ))) :=
  qList_le_min_sqrt_of_le (articulationPoints_strongCertificateSize_le.trans (min_le_right _ _)) n

/-- **The articulation points from an adjacency matrix**:
`Q_matrix ≤ min{N, 2^18·√(N·4v)}`. -/
theorem articulationPoints_qMatrix_le :
    (qMatrix (articulationPoints (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (4 * Fintype.card V : ℕ))) :=
  qMatrix_le_min_sqrt_of_le (articulationPoints_strongCertificateSize_le.trans (min_le_right _ _))

/-- **The articulation points from an adjacency matrix** (`sec:failure-profiles`):
`Q_matrix ≤ 2^19·v·√v`, the paper's `O(v^{3/2})`. -/
theorem articulationPoints_qMatrix_le_mul_sqrt :
    (qMatrix (articulationPoints (V := V)) : ℝ) ≤
      2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_two_pow_mul_sqrt_of_le_four
    (articulationPoints_strongCertificateSize_le.trans (min_le_right _ _))

/-- **The articulation points from adjacency lists**: `Q_adj ≤ min{2m, 2^19·√(m·4v)}`. -/
theorem articulationPoints_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (articulationPoints (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (4 * Fintype.card V : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le
    (articulationPoints_strongCertificateSize_le.trans (min_le_right _ _)) m

/-- **The articulation points and the partitions after their deletion from an edge list**:
`Q_list ≤ min{n, 2^18·√(n·4v)}`. -/
theorem articulationPartitions_qList_le (n : ℕ) :
    (qList (articulationPartitions (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (4 * Fintype.card V : ℕ))) :=
  qList_le_min_sqrt_of_le
    (articulationPartitions_strongCertificateSize_le.trans (min_le_right _ _)) n

/-- **The articulation points and the partitions after their deletion from an adjacency
matrix**: `Q_matrix ≤ min{N, 2^18·√(N·4v)}`. -/
theorem articulationPartitions_qMatrix_le :
    (qMatrix (articulationPartitions (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (4 * Fintype.card V : ℕ))) :=
  qMatrix_le_min_sqrt_of_le
    (articulationPartitions_strongCertificateSize_le.trans (min_le_right _ _))

/-- **The articulation points and the partitions after their deletion from an adjacency
matrix**: `Q_matrix ≤ 2^19·v·√v`. -/
theorem articulationPartitions_qMatrix_le_mul_sqrt :
    (qMatrix (articulationPartitions (V := V)) : ℝ) ≤
      2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_two_pow_mul_sqrt_of_le_four
    (articulationPartitions_strongCertificateSize_le.trans (min_le_right _ _))

/-- **The articulation points and the partitions after their deletion from adjacency lists**:
`Q_adj ≤ min{2m, 2^19·√(m·4v)}`. -/
theorem articulationPartitions_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (articulationPartitions (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (4 * Fintype.card V : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le
    (articulationPartitions_strongCertificateSize_le.trans (min_le_right _ _)) m

/-! ## `k`-vertex-connectivity -/

/-- **`k`-vertex-connectivity from an edge list**: `Q_list ≤ min{n, 2^18·√(n·2kv)}`. -/
theorem vertexConnectivity_qList_le (k n : ℕ) :
    (qList (isVertexConnected (V := V) k) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * k * Fintype.card V : ℕ))) :=
  qList_le_min_sqrt_of_le ((vertexConnectivity_strongCertificateSize_le k).trans
    (min_le_right _ _)) n

/-- **`k`-vertex-connectivity from an adjacency matrix**:
`Q_matrix ≤ min{N, 2^18·√(N·2kv)}`. -/
theorem vertexConnectivity_qMatrix_le (k : ℕ) :
    (qMatrix (isVertexConnected (V := V) k) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (2 * k * Fintype.card V : ℕ))) :=
  qMatrix_le_min_sqrt_of_le ((vertexConnectivity_strongCertificateSize_le k).trans
    (min_le_right _ _))

/-- **`k`-vertex-connectivity from an adjacency matrix**:
`Q_matrix ≤ 2^18·min{v², v·√(v·k)}`. -/
theorem vertexConnectivity_qMatrix_le_min (k : ℕ) :
    (qMatrix (isVertexConnected (V := V) k) : ℝ)
      ≤ 2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2) (Fintype.card V * Real.sqrt (Fintype.card V * k)) :=
  qMatrix_le_mul_min_of_le_two_mul ((vertexConnectivity_strongCertificateSize_le k).trans
    (min_le_right _ _))

/-- **`k`-vertex-connectivity from adjacency lists**: `Q_adj ≤ min{2m, 2^19·√(m·2kv)}`. -/
theorem vertexConnectivity_qAdjEdges_le (k m : ℕ) :
    (qAdjEdges (isVertexConnected (V := V) k) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (2 * k * Fintype.card V : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le ((vertexConnectivity_strongCertificateSize_le k).trans
    (min_le_right _ _)) m

end MonoidProduct.Graph
