import MonoidProduct.Graph.QueryModels
import MonoidProduct.Graph.Components
import MonoidProduct.Graph.TwoColorings
import MonoidProduct.Graph.Sparse
set_option linter.style.header false

/-!
# Query bounds from strong certificates for graphs

`monoid.tex`, section `sec:graph-certificates`: `eq:graph-certificate-list`,
`eq:graph-certificate-matrix`, the query bounds of the application paragraphs, and the
adjacency-matrix column of `tab:graph-certificates` for its first three rows.  Write `v = #V`,
`N = C(v, 2)` and `b_f` for `strongCertificateSize f`.  Error `1/3` throughout, and every
constant is explicit.

* `qList_le_min_sqrt` (`eq:graph-certificate-list`): `Q_list(f; n) ≤ min{n, 2^18·√(n·b_f)}`.
  This is `cor:certificate-queries` with the universe `Edge V`.
* `qMatrix_le_min_sqrt`, `qMatrix_le_mul_sqrt` (`eq:graph-certificate-matrix`, first line):
  `Q_matrix(f) ≤ min{N, 2^18·√(N·b_f)} ≤ 2^18·v·√b_f`.
* `qAdj_le_min_sqrt`, `qAdjEdges_le_min_sqrt` (`eq:graph-certificate-matrix`, second line):
  `qAdj f deg ≤ min{∑ deg, 2^18·√((∑ deg)·b_f)}`, so `Q_adj(f; m) ≤ min{2m, 2^19·√(m·b_f)}`,
  and `Q_adj(f; m) ≤ 2^19·min{m, √(m·b_f)}` in the paper's form (`qAdjEdges_le_mul_min`).

The matrix and adjacency bounds apply the encoded form of `cor:certificate-queries`
(`encodedCertificate_qQuery_le_min_sqrt`) to the virtual edge lists `matrixEntry` and `adjEdge`
directly, so they keep the constant `2^18` instead of paying the factor two of
`eq:graph-model-comparison`.  The adjacency bound is proved for all arrays, valid or not, and
restricted to the valid ones.

The `_of_le` forms take any certificate bound `b_f ≤ b`.  Each certificate endpoint of the
section then has named list, matrix and adjacency-list corollaries, with its own bound:
* `v - 1`: the component partition, connectivity, `s`–`t` connectivity;
* `v`: all proper two-colourings, bipartiteness, a canonical colouring, cycle detection;
* `L + 1`: `prop:sparse-certificates`, a property whose yes-instances have at most `L` edges.

The `_qMatrix_le_mul_sqrt` corollaries are the `O(v^{3/2})` entries of `tab:graph-certificates`,
as `2^18·v·√v`.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

variable {V O : Type} [Fintype V] [DecidableEq V] [DecidableEq O]

/-! ## The three models -/

/-- **`eq:graph-certificate-list`**: from an edge list of length `n`,
`Q_list(f; n) ≤ min{n, 2^18·√(n·b_f)}`, for every `n` and every `f`. -/
theorem qList_le_min_sqrt (f : Finset (Edge V) → O) (n : ℕ) :
    (qList f n : ℝ) ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * strongCertificateSize f)) :=
  strongCertificate_qQuery_le_min_sqrt f n

/-- **`eq:graph-certificate-matrix`, adjacency matrices**:
`Q_matrix(f) ≤ min{N, 2^18·√(N·b_f)}`, `N = C(v, 2)`. -/
theorem qMatrix_le_min_sqrt (f : Finset (Edge V) → O) :
    (qMatrix f : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * strongCertificateSize f)) := by
  have h := encodedCertificate_qQuery_le_min_sqrt (ι := Edge V) (A := Bool) matrixEntry f
  rw [card_edge] at h
  have heq : (fun a : Edge V → Bool => f (encodedSet matrixEntry a))
      = fun a => f (matrixGraph a) := by
    funext a
    rw [matrixGraph_eq_recordSet]
    rfl
  rw [heq] at h
  exact h

/-- **`eq:graph-certificate-matrix`, adjacency matrices**: `Q_matrix(f) ≤ 2^18·v·√b_f`, since
`C(v, 2) ≤ v²`. -/
theorem qMatrix_le_mul_sqrt (f : Finset (Edge V) → O) :
    (qMatrix f : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (strongCertificateSize f) := by
  refine (qMatrix_le_min_sqrt f).trans ((min_le_right _ _).trans ?_)
  rw [mul_assoc]
  gcongr
  rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  gcongr
  calc Real.sqrt ((Fintype.card V).choose 2 : ℝ)
      ≤ Real.sqrt ((Fintype.card V : ℝ) ^ 2) := by
        gcongr
        exact_mod_cast Nat.choose_le_pow _ _
    _ = Fintype.card V := Real.sqrt_sq (Nat.cast_nonneg _)

/-- **`eq:graph-certificate-matrix`, adjacency lists**, for the degree vector `deg`:
`Q_adj ≤ min{∑ u, deg u, 2^18·√((∑ u, deg u)·b_f)}`. -/
theorem qAdj_le_min_sqrt (f : Finset (Edge V) → O) (deg : V → ℕ) :
    (qAdj f deg : ℝ) ≤ min ((∑ u, deg u : ℕ) : ℝ)
      (2 ^ 18 * Real.sqrt ((∑ u, deg u : ℕ) * strongCertificateSize f)) := by
  have : Nonempty O := ⟨f ∅⟩
  have := Fintype.ofFinite (AdjArray deg)
  have h := encodedCertificate_qQuery_le_min_sqrt (ι := AdjPos deg) (A := V)
    (fun p w => adjEdge p.1 w) f
  rw [card_adjPos] at h
  have hres := qQueryOn_comp_read_le_qQuery (fun a : AdjArray deg => a.1)
    (fun nbr : AdjPos deg → V => f (encodedSet (fun p w => adjEdge p.1 w) nbr)) (ε := 1 / 3)
    (queryCounts_nonempty (fun x y h => by rw [show x = y from h]) (by norm_num))
  have heq : qAdj f deg = qQueryOn (fun a : AdjArray deg => a.1)
      (fun a => f (encodedSet (fun p w => adjEdge p.1 w) a.1)) (1 / 3) := rfl
  rw [heq]
  exact le_trans (by exact_mod_cast hres) h

/-- **`eq:graph-certificate-matrix`, adjacency lists for graphs with `m` edges**:
`Q_adj(f; m) ≤ min{2m, 2^19·√(m·b_f)}`. -/
theorem qAdjEdges_le_min_sqrt (f : Finset (Edge V) → O) (m : ℕ) :
    (qAdjEdges f m : ℝ) ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * strongCertificateSize f)) := by
  refine qAdjEdges_le_of_forall (by positivity) fun deg hdeg => ?_
  refine (qAdj_le_min_sqrt f deg).trans (min_le_min (by rw [hdeg]; push_cast; rfl) ?_)
  rw [hdeg, show ((2 * m : ℕ) : ℝ) * strongCertificateSize f
      = 2 * ((m : ℝ) * strongCertificateSize f) by push_cast; ring,
    Real.sqrt_mul (by norm_num)]
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs := Real.sqrt_nonneg ((m : ℝ) * strongCertificateSize f)
  nlinarith

/-- **`eq:graph-certificate-matrix`, adjacency lists, in the paper's form**:
`Q_adj(f; m) ≤ 2^19·min{m, √(m·b_f)}`. -/
theorem qAdjEdges_le_mul_min (f : Finset (Edge V) → O) (m : ℕ) :
    (qAdjEdges f m : ℝ) ≤ 2 ^ 19 * min (m : ℝ) (Real.sqrt (m * strongCertificateSize f)) := by
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine (qAdjEdges_le_min_sqrt f m).trans (min_le_min ?_ le_rfl)
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-! ## Against a certificate bound -/

section Bound

variable {f : Finset (Edge V) → O} {b : ℕ}

/-- `eq:graph-certificate-list` for any certificate bound `b_f ≤ b`. -/
theorem qList_le_min_sqrt_of_le (h : strongCertificateSize f ≤ b) (n : ℕ) :
    (qList f n : ℝ) ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * b)) := by
  refine (qList_le_min_sqrt f n).trans (min_le_min_left _ ?_)
  gcongr

/-- `eq:graph-certificate-matrix` for adjacency matrices and any certificate bound `b_f ≤ b`. -/
theorem qMatrix_le_min_sqrt_of_le (h : strongCertificateSize f ≤ b) :
    (qMatrix f : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * b)) := by
  refine (qMatrix_le_min_sqrt f).trans (min_le_min_left _ ?_)
  gcongr

/-- `Q_matrix(f) ≤ 2^18·v·√b` for any certificate bound `b_f ≤ b`. -/
theorem qMatrix_le_mul_sqrt_of_le (h : strongCertificateSize f ≤ b) :
    (qMatrix f : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt b := by
  refine (qMatrix_le_mul_sqrt f).trans ?_
  gcongr

/-- `eq:graph-certificate-matrix` for adjacency lists, the degree vector `deg` and any
certificate bound `b_f ≤ b`. -/
theorem qAdj_le_min_sqrt_of_le (h : strongCertificateSize f ≤ b) (deg : V → ℕ) :
    (qAdj f deg : ℝ) ≤ min ((∑ u, deg u : ℕ) : ℝ) (2 ^ 18 * Real.sqrt ((∑ u, deg u : ℕ) * b)) := by
  refine (qAdj_le_min_sqrt f deg).trans (min_le_min_left _ ?_)
  gcongr

/-- `Q_adj(f; m) ≤ min{2m, 2^19·√(m·b)}` for any certificate bound `b_f ≤ b`. -/
theorem qAdjEdges_le_min_sqrt_of_le (h : strongCertificateSize f ≤ b) (m : ℕ) :
    (qAdjEdges f m : ℝ) ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * b)) := by
  refine (qAdjEdges_le_min_sqrt f m).trans (min_le_min_left _ ?_)
  gcongr

end Bound

/-! ## The component partition, connectivity and `s`–`t` connectivity: `b ≤ v - 1` -/

/-- **The component partition from an edge list** (`sec:graph-certificates`):
`Q_list(π; n) ≤ min{n, 2^18·√(n·(v - 1))}`. -/
theorem connectedComponents_qList_le (n : ℕ) :
    (qList (connectedComponents (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (Fintype.card V - 1 : ℕ))) :=
  qList_le_min_sqrt_of_le connectedComponents_strongCertificateSize_le n

/-- **The component partition from an adjacency matrix**:
`Q_matrix(π) ≤ min{N, 2^18·√(N·(v - 1))}`. -/
theorem connectedComponents_qMatrix_le :
    (qMatrix (connectedComponents (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (Fintype.card V - 1 : ℕ))) :=
  qMatrix_le_min_sqrt_of_le connectedComponents_strongCertificateSize_le

/-- **`tab:graph-certificates`, connected components**: `Q_matrix(π) ≤ 2^18·v^{3/2}`. -/
theorem connectedComponents_qMatrix_le_mul_sqrt :
    (qMatrix (connectedComponents (V := V)) : ℝ)
      ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_mul_sqrt_of_le (connectedComponents_strongCertificateSize_le.trans (Nat.sub_le _ _))

/-- **The component partition from adjacency lists**:
`Q_adj(π; m) ≤ min{2m, 2^19·√(m·(v - 1))}`. -/
theorem connectedComponents_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (connectedComponents (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (Fintype.card V - 1 : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le connectedComponents_strongCertificateSize_le m

/-- **Connectivity from an edge list**: `Q_list(conn; n) ≤ min{n, 2^18·√(n·(v - 1))}`. -/
theorem connectivity_qList_le (n : ℕ) :
    (qList (isConnected (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (Fintype.card V - 1 : ℕ))) :=
  qList_le_min_sqrt_of_le connectivity_strongCertificateSize_le n

/-- **Connectivity from an adjacency matrix**: `Q_matrix(conn) ≤ min{N, 2^18·√(N·(v - 1))}`. -/
theorem connectivity_qMatrix_le :
    (qMatrix (isConnected (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (Fintype.card V - 1 : ℕ))) :=
  qMatrix_le_min_sqrt_of_le connectivity_strongCertificateSize_le

/-- **Connectivity from an adjacency matrix**: `Q_matrix(conn) ≤ 2^18·v^{3/2}`. -/
theorem connectivity_qMatrix_le_mul_sqrt :
    (qMatrix (isConnected (V := V)) : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_mul_sqrt_of_le (connectivity_strongCertificateSize_le.trans (Nat.sub_le _ _))

/-- **Connectivity from adjacency lists**: `Q_adj(conn; m) ≤ min{2m, 2^19·√(m·(v - 1))}`. -/
theorem connectivity_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (isConnected (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (Fintype.card V - 1 : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le connectivity_strongCertificateSize_le m

/-- **`s`–`t` connectivity from an edge list**:
`Q_list(s-t conn; n) ≤ min{n, 2^18·√(n·(v - 1))}`. -/
theorem stConnectivity_qList_le (s t : V) (n : ℕ) :
    (qList (isSTConnected s t) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (Fintype.card V - 1 : ℕ))) :=
  qList_le_min_sqrt_of_le (stConnectivity_strongCertificateSize_le s t) n

/-- **`s`–`t` connectivity from an adjacency matrix**:
`Q_matrix(s-t conn) ≤ min{N, 2^18·√(N·(v - 1))}`. -/
theorem stConnectivity_qMatrix_le (s t : V) :
    (qMatrix (isSTConnected s t) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (Fintype.card V - 1 : ℕ))) :=
  qMatrix_le_min_sqrt_of_le (stConnectivity_strongCertificateSize_le s t)

/-- **`s`–`t` connectivity from an adjacency matrix**: `Q_matrix(s-t conn) ≤ 2^18·v^{3/2}`. -/
theorem stConnectivity_qMatrix_le_mul_sqrt (s t : V) :
    (qMatrix (isSTConnected s t) : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_mul_sqrt_of_le ((stConnectivity_strongCertificateSize_le s t).trans (Nat.sub_le _ _))

/-- **`s`–`t` connectivity from adjacency lists**:
`Q_adj(s-t conn; m) ≤ min{2m, 2^19·√(m·(v - 1))}`. -/
theorem stConnectivity_qAdjEdges_le (s t : V) (m : ℕ) :
    (qAdjEdges (isSTConnected s t) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (Fintype.card V - 1 : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le (stConnectivity_strongCertificateSize_le s t) m

/-! ## Two-colourings, bipartiteness and a canonical colouring: `b ≤ v` -/

/-- **All proper two-colourings from an edge list** (`sec:graph-certificates`):
`Q_list(𝒞; n) ≤ min{n, 2^18·√(n·v)}`. -/
theorem twoColorings_qList_le (n : ℕ) :
    (qList (twoColorings (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * Fintype.card V)) :=
  qList_le_min_sqrt_of_le twoColorings_strongCertificateSize_le n

/-- **All proper two-colourings from an adjacency matrix**:
`Q_matrix(𝒞) ≤ min{N, 2^18·√(N·v)}`. -/
theorem twoColorings_qMatrix_le :
    (qMatrix (twoColorings (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * Fintype.card V)) :=
  qMatrix_le_min_sqrt_of_le twoColorings_strongCertificateSize_le

/-- **`tab:graph-certificates`, bipartiteness and proper two-colourings**: the set of all proper
two-colourings costs `Q_matrix(𝒞) ≤ 2^18·v^{3/2}`. -/
theorem twoColorings_qMatrix_le_mul_sqrt :
    (qMatrix (twoColorings (V := V)) : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_mul_sqrt_of_le twoColorings_strongCertificateSize_le

/-- **All proper two-colourings from adjacency lists**:
`Q_adj(𝒞; m) ≤ min{2m, 2^19·√(m·v)}`. -/
theorem twoColorings_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (twoColorings (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * Fintype.card V)) :=
  qAdjEdges_le_min_sqrt_of_le twoColorings_strongCertificateSize_le m

/-- **Bipartiteness from an edge list**: `Q_list(bip; n) ≤ min{n, 2^18·√(n·v)}`. -/
theorem bipartite_qList_le (n : ℕ) :
    (qList (isBipartite (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * Fintype.card V)) :=
  qList_le_min_sqrt_of_le bipartite_strongCertificateSize_le n

/-- **Bipartiteness from an adjacency matrix**: `Q_matrix(bip) ≤ min{N, 2^18·√(N·v)}`. -/
theorem bipartite_qMatrix_le :
    (qMatrix (isBipartite (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * Fintype.card V)) :=
  qMatrix_le_min_sqrt_of_le bipartite_strongCertificateSize_le

/-- **Bipartiteness from an adjacency matrix**: `Q_matrix(bip) ≤ 2^18·v^{3/2}`. -/
theorem bipartite_qMatrix_le_mul_sqrt :
    (qMatrix (isBipartite (V := V)) : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_mul_sqrt_of_le bipartite_strongCertificateSize_le

/-- **Bipartiteness from adjacency lists**: `Q_adj(bip; m) ≤ min{2m, 2^19·√(m·v)}`. -/
theorem bipartite_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (isBipartite (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * Fintype.card V)) :=
  qAdjEdges_le_min_sqrt_of_le bipartite_strongCertificateSize_le m

/-- **A canonical proper two-colouring, or failure, from an edge list**:
`Q_list ≤ min{n, 2^18·√(n·v)}`. -/
theorem properTwoColoring_qList_le (n : ℕ) :
    (qList (properTwoColoring (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * Fintype.card V)) :=
  qList_le_min_sqrt_of_le properTwoColoring_strongCertificateSize_le n

/-- **A canonical proper two-colouring, or failure, from an adjacency matrix**:
`Q_matrix ≤ min{N, 2^18·√(N·v)}`. -/
theorem properTwoColoring_qMatrix_le :
    (qMatrix (properTwoColoring (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * Fintype.card V)) :=
  qMatrix_le_min_sqrt_of_le properTwoColoring_strongCertificateSize_le

/-- **A canonical proper two-colouring, or failure, from an adjacency matrix**:
`Q_matrix ≤ 2^18·v^{3/2}`. -/
theorem properTwoColoring_qMatrix_le_mul_sqrt :
    (qMatrix (properTwoColoring (V := V)) : ℝ)
      ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_mul_sqrt_of_le properTwoColoring_strongCertificateSize_le

/-- **A canonical proper two-colouring, or failure, from adjacency lists**:
`Q_adj ≤ min{2m, 2^19·√(m·v)}`. -/
theorem properTwoColoring_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (properTwoColoring (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * Fintype.card V)) :=
  qAdjEdges_le_min_sqrt_of_le properTwoColoring_strongCertificateSize_le m

/-! ## Cycle detection: `b ≤ v` -/

/-- **Cycle detection from an edge list** (`sec:graph-certificates`):
`Q_list(cycle; n) ≤ min{n, 2^18·√(n·v)}`. -/
theorem cycle_qList_le (n : ℕ) :
    (qList (hasCycle (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * Fintype.card V)) :=
  qList_le_min_sqrt_of_le cycle_strongCertificateSize_le n

/-- **Cycle detection from an adjacency matrix**: `Q_matrix(cycle) ≤ min{N, 2^18·√(N·v)}`. -/
theorem cycle_qMatrix_le :
    (qMatrix (hasCycle (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * Fintype.card V)) :=
  qMatrix_le_min_sqrt_of_le cycle_strongCertificateSize_le

/-- **`tab:graph-certificates`, cycle detection**: `Q_matrix(cycle) ≤ 2^18·v^{3/2}`. -/
theorem cycle_qMatrix_le_mul_sqrt :
    (qMatrix (hasCycle (V := V)) : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  qMatrix_le_mul_sqrt_of_le cycle_strongCertificateSize_le

/-- **Cycle detection from adjacency lists**: `Q_adj(cycle; m) ≤ min{2m, 2^19·√(m·v)}`. -/
theorem cycle_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (hasCycle (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * Fintype.card V)) :=
  qAdjEdges_le_min_sqrt_of_le cycle_strongCertificateSize_le m

/-! ## Sparse yes-instances: `b ≤ L + 1` -/

section Sparse

variable (P : SimpleGraph V → Prop) [DecidablePred P] {L : ℕ}

/-- **`prop:sparse-certificates` from an edge list**: if every graph satisfying `P` has at most
`L` edges, `Q_list(P; n) ≤ min{n, 2^18·√(n·(L + 1))}`. -/
theorem sparseYes_qList_le (hP : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ L) (n : ℕ) :
    (qList (fun S : Finset (Edge V) => decide (P (toGraph S))) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (L + 1 : ℕ))) :=
  qList_le_min_sqrt_of_le ((sparseYes_strongCertificateSize_le P hP).trans (min_le_right _ _)) n

/-- **`prop:sparse-certificates` from an adjacency matrix**:
`Q_matrix(P) ≤ min{N, 2^18·√(N·(L + 1))}`. -/
theorem sparseYes_qMatrix_le (hP : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ L) :
    (qMatrix (fun S : Finset (Edge V) => decide (P (toGraph S))) : ℝ)
      ≤ min ((Fintype.card V).choose 2 : ℝ)
        (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (L + 1 : ℕ))) :=
  qMatrix_le_min_sqrt_of_le ((sparseYes_strongCertificateSize_le P hP).trans (min_le_right _ _))

/-- **`prop:sparse-certificates` from an adjacency matrix**:
`Q_matrix(P) ≤ 2^18·v·√(L + 1)`. -/
theorem sparseYes_qMatrix_le_mul_sqrt (hP : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ L) :
    (qMatrix (fun S : Finset (Edge V) => decide (P (toGraph S))) : ℝ)
      ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (L + 1 : ℕ) :=
  qMatrix_le_mul_sqrt_of_le ((sparseYes_strongCertificateSize_le P hP).trans (min_le_right _ _))

/-- **`prop:sparse-certificates` from adjacency lists**:
`Q_adj(P; m) ≤ min{2m, 2^19·√(m·(L + 1))}`. -/
theorem sparseYes_qAdjEdges_le (hP : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ L) (m : ℕ) :
    (qAdjEdges (fun S : Finset (Edge V) => decide (P (toGraph S))) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (L + 1 : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le ((sparseYes_strongCertificateSize_le P hP).trans (min_le_right _ _)) m

end Sparse

end MonoidProduct.Graph
