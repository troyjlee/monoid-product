import MonoidProduct.Graph.EdgeFaults
import MonoidProduct.Graph.Quantum
set_option linter.style.header false

/-!
# Query bounds for edge-failure profiles

`monoid.tex`, section `sec:failure-profiles`: the edge-failure half of
`eq:failure-profile-queries`, the upper bound of `prop:failure-profile-complexity` for `Σ^E_k`,
and the query bounds of the bridge and `k`-edge-connectivity readouts.  Write `v = #V` and
`N = C(v, 2)`.  Error `1/3` throughout, and every constant is explicit.

* `edgeFailureProfile_qList_le` (`eq:failure-profile-queries`):
  `Q_list(Σ^E_k; n) ≤ min{n, 2^18·√(n·k(v - 1))}`.
* `edgeFailureProfile_qMatrix_le_min` (`prop:failure-profile-complexity`, upper bound):
  `Q_matrix(Σ^E_k) ≤ 2^18·min{v², v·√(v·k)}`, the paper's `O(min{v², v^{3/2}·√k})`, for every
  `v` and `k`.
* The bridges, and the bridges with the partitions after their deletion, from the profile for
  `k = 2`: `Q_list ≤ min{n, 2^18·√(n·2(v - 1))}` and `Q_matrix ≤ 2^19·v·√v`.
* `k`-edge-connectivity: the bounds of the profile.

All of them follow from the certificate sizes of `Graph/EdgeFaults.lean` through
`eq:graph-certificate-list` and `eq:graph-certificate-matrix` (`Graph/Quantum.lean`).  The
matrix bounds use the direct encoded form, so they keep the constant `2^18` rather than paying
the factor two of `eq:graph-model-comparison`.  Each output also has an adjacency-list bound.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

variable {V O : Type} [Fintype V] [DecidableEq V] [DecidableEq O]

/-! ## Two matrix forms -/

/-- **Certificates of at most `k(v - 1)` edges give `Q_matrix ≤ 2^18·min{v², v·√(v·k)}`.** -/
theorem qMatrix_le_mul_min_of_le {f : Finset (Edge V) → O} {k : ℕ}
    (h : strongCertificateSize f ≤ k * (Fintype.card V - 1)) :
    (qMatrix f : ℝ) ≤ 2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2)
      (Fintype.card V * Real.sqrt (Fintype.card V * k)) := by
  refine (qMatrix_le_min_sqrt_of_le h).trans ?_
  rw [mul_min_of_nonneg _ _ (by positivity)]
  have hv : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hN : ((Fintype.card V).choose 2 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow _ _
  have hkv : ((k * (Fintype.card V - 1) : ℕ) : ℝ) ≤ Fintype.card V * k := by
    have : k * (Fintype.card V - 1) ≤ Fintype.card V * k := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right k (Nat.sub_le _ _)
    exact_mod_cast this
  refine min_le_min (by nlinarith) ?_
  gcongr
  calc Real.sqrt ((Fintype.card V).choose 2 * (k * (Fintype.card V - 1) : ℕ))
      ≤ Real.sqrt ((Fintype.card V : ℝ) ^ 2 * (Fintype.card V * k)) := by
        gcongr
    _ = Fintype.card V * Real.sqrt (Fintype.card V * k) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hv]

/-- **Certificates of at most `2(v - 1)` edges give `Q_matrix ≤ 2^19·v·√v`.** -/
theorem qMatrix_le_two_pow_mul_sqrt_of_le {f : Finset (Edge V) → O}
    (h : strongCertificateSize f ≤ 2 * (Fintype.card V - 1)) :
    (qMatrix f : ℝ) ≤ 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) := by
  refine (qMatrix_le_mul_sqrt_of_le h).trans ?_
  have hv : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hb : ((2 * (Fintype.card V - 1) : ℕ) : ℝ) ≤ 2 * Fintype.card V := by
    have : 2 * (Fintype.card V - 1) ≤ 2 * Fintype.card V := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
    exact_mod_cast this
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  calc 2 ^ 18 * (Fintype.card V : ℝ) * Real.sqrt ((2 * (Fintype.card V - 1) : ℕ) : ℝ)
      ≤ 2 ^ 18 * Fintype.card V * (Real.sqrt 2 * Real.sqrt (Fintype.card V)) := by
        rw [← Real.sqrt_mul (by norm_num)]
        gcongr
    _ ≤ 2 ^ 18 * Fintype.card V * (2 * Real.sqrt (Fintype.card V)) := by
        gcongr
    _ = 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) := by ring

/-! ## The profile -/

/-- **`eq:failure-profile-queries`, edge failures**: from an edge list of length `n`,
`Q_list(Σ^E_k; n) ≤ min{n, 2^18·√(n·k(v - 1))}`, the paper's `O(min{n, √(nkv)})`. -/
theorem edgeFailureProfile_qList_le (k n : ℕ) :
    (qList (edgeFailureProfile (V := V) k) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (k * (Fintype.card V - 1) : ℕ))) :=
  qList_le_min_sqrt_of_le ((edgeFailureProfile_strongCertificateSize_le k).trans
    (min_le_right _ _)) n

/-- **The edge-failure profile from an adjacency matrix**:
`Q_matrix(Σ^E_k) ≤ min{N, 2^18·√(N·k(v - 1))}`. -/
theorem edgeFailureProfile_qMatrix_le (k : ℕ) :
    (qMatrix (edgeFailureProfile (V := V) k) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (k * (Fintype.card V - 1) : ℕ))) :=
  qMatrix_le_min_sqrt_of_le ((edgeFailureProfile_strongCertificateSize_le k).trans
    (min_le_right _ _))

/-- **`prop:failure-profile-complexity`, upper bound for edge failures**:
`Q_matrix(Σ^E_k) ≤ 2^18·min{v², v·√(v·k)}`, that is `O(min{v², v^{3/2}·√k})`, for every `v` and
`k`. -/
theorem edgeFailureProfile_qMatrix_le_min (k : ℕ) :
    (qMatrix (edgeFailureProfile (V := V) k) : ℝ)
      ≤ 2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2) (Fintype.card V * Real.sqrt (Fintype.card V * k)) :=
  qMatrix_le_mul_min_of_le ((edgeFailureProfile_strongCertificateSize_le k).trans
    (min_le_right _ _))

/-- **The edge-failure profile from adjacency lists**:
`Q_adj(Σ^E_k; m) ≤ min{2m, 2^19·√(m·k(v - 1))}`. -/
theorem edgeFailureProfile_qAdjEdges_le (k m : ℕ) :
    (qAdjEdges (edgeFailureProfile (V := V) k) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (k * (Fintype.card V - 1) : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le ((edgeFailureProfile_strongCertificateSize_le k).trans
    (min_le_right _ _)) m

/-! ## Bridges -/

/-- **The bridges from an edge list** (`sec:failure-profiles`):
`Q_list(bridges; n) ≤ min{n, 2^18·√(n·2(v - 1))}`, the paper's `O(min{n, √(nv)})`. -/
theorem bridges_qList_le (n : ℕ) :
    (qList (bridges (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * (Fintype.card V - 1) : ℕ))) :=
  qList_le_min_sqrt_of_le (bridges_strongCertificateSize_le.trans (min_le_right _ _)) n

/-- **The bridges from an adjacency matrix**:
`Q_matrix(bridges) ≤ min{N, 2^18·√(N·2(v - 1))}`. -/
theorem bridges_qMatrix_le :
    (qMatrix (bridges (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (2 * (Fintype.card V - 1) : ℕ))) :=
  qMatrix_le_min_sqrt_of_le (bridges_strongCertificateSize_le.trans (min_le_right _ _))

/-- **The bridges from an adjacency matrix** (`sec:failure-profiles`):
`Q_matrix(bridges) ≤ 2^19·v·√v`, the paper's `O(v^{3/2})`. -/
theorem bridges_qMatrix_le_mul_sqrt :
    (qMatrix (bridges (V := V)) : ℝ) ≤ 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_two_pow_mul_sqrt_of_le (bridges_strongCertificateSize_le.trans (min_le_right _ _))

/-- **The bridges from adjacency lists**: `Q_adj(bridges; m) ≤ min{2m, 2^19·√(m·2(v - 1))}`. -/
theorem bridges_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (bridges (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (2 * (Fintype.card V - 1) : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le (bridges_strongCertificateSize_le.trans (min_le_right _ _)) m

/-- **The bridges and the partitions after their deletion from an edge list**:
`Q_list ≤ min{n, 2^18·√(n·2(v - 1))}`. -/
theorem bridgePartitions_qList_le (n : ℕ) :
    (qList (bridgePartitions (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * (Fintype.card V - 1) : ℕ))) :=
  qList_le_min_sqrt_of_le (bridgePartitions_strongCertificateSize_le.trans (min_le_right _ _)) n

/-- **The bridges and the partitions after their deletion from an adjacency matrix**:
`Q_matrix ≤ min{N, 2^18·√(N·2(v - 1))}`. -/
theorem bridgePartitions_qMatrix_le :
    (qMatrix (bridgePartitions (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (2 * (Fintype.card V - 1) : ℕ))) :=
  qMatrix_le_min_sqrt_of_le (bridgePartitions_strongCertificateSize_le.trans (min_le_right _ _))

/-- **The bridges and the partitions after their deletion from an adjacency matrix**:
`Q_matrix ≤ 2^19·v·√v`. -/
theorem bridgePartitions_qMatrix_le_mul_sqrt :
    (qMatrix (bridgePartitions (V := V)) : ℝ)
      ≤ 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_two_pow_mul_sqrt_of_le
    (bridgePartitions_strongCertificateSize_le.trans (min_le_right _ _))

/-- **The bridges and the partitions after their deletion from adjacency lists**:
`Q_adj ≤ min{2m, 2^19·√(m·2(v - 1))}`. -/
theorem bridgePartitions_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (bridgePartitions (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (2 * (Fintype.card V - 1) : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le
    (bridgePartitions_strongCertificateSize_le.trans (min_le_right _ _)) m

/-! ## `k`-edge-connectivity -/

/-- **`k`-edge-connectivity from an edge list**: `Q_list ≤ min{n, 2^18·√(n·k(v - 1))}`. -/
theorem edgeConnectivity_qList_le (k n : ℕ) :
    (qList (isEdgeConnected (V := V) k) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (k * (Fintype.card V - 1) : ℕ))) :=
  qList_le_min_sqrt_of_le ((edgeConnectivity_strongCertificateSize_le k).trans
    (min_le_right _ _)) n

/-- **`k`-edge-connectivity from an adjacency matrix**:
`Q_matrix ≤ min{N, 2^18·√(N·k(v - 1))}`. -/
theorem edgeConnectivity_qMatrix_le (k : ℕ) :
    (qMatrix (isEdgeConnected (V := V) k) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (k * (Fintype.card V - 1) : ℕ))) :=
  qMatrix_le_min_sqrt_of_le ((edgeConnectivity_strongCertificateSize_le k).trans
    (min_le_right _ _))

/-- **`k`-edge-connectivity from an adjacency matrix**: `Q_matrix ≤ 2^18·min{v², v·√(v·k)}`. -/
theorem edgeConnectivity_qMatrix_le_min (k : ℕ) :
    (qMatrix (isEdgeConnected (V := V) k) : ℝ)
      ≤ 2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2) (Fintype.card V * Real.sqrt (Fintype.card V * k)) :=
  qMatrix_le_mul_min_of_le ((edgeConnectivity_strongCertificateSize_le k).trans
    (min_le_right _ _))

/-- **`k`-edge-connectivity from adjacency lists**: `Q_adj ≤ min{2m, 2^19·√(m·k(v - 1))}`. -/
theorem edgeConnectivity_qAdjEdges_le (k m : ℕ) :
    (qAdjEdges (isEdgeConnected (V := V) k) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (k * (Fintype.card V - 1) : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le ((edgeConnectivity_strongCertificateSize_le k).trans
    (min_le_right _ _)) m

end MonoidProduct.Graph
