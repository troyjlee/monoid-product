import MonoidProduct.Graph.Quantum
set_option linter.style.header false

/-!
# Acceptance statements for the graph query models

The paper-facing statements of `monoid.tex`, section `sec:graph-certificates`, paragraphs
"Query models" and "Comparison of the models", `eq:graph-model-comparison`,
`eq:graph-certificate-list`, `eq:graph-certificate-matrix` and the application paragraphs.
They are restated with the definitions unfolded where that makes their meaning visible,
followed by small sanity checks.  Lean checks every `example` here against the library's
statement.

* The three models: edge lists of any length with nulls and repetitions, one bit per pair of
  distinct vertices, and valid adjacency arrays with public degrees.  Every graph is
  represented in the last two, and a valid array has `∑ u, deg u = 2m`.
* `eq:graph-model-comparison`, in `ℕ`, for every `f`.
* `eq:graph-certificate-list` and `eq:graph-certificate-matrix` with explicit constants, for
  every `f` and every `n`, `deg` and `m`.
* The list, matrix and adjacency-list bounds of every certificate endpoint of the section, and
  the `O(v^{3/2})` matrix column of `tab:graph-certificates`.

The sanity checks cover:
* a list with a null entry and a repeated edge;
* an adjacency array with an isolated vertex, and an array that the promise excludes;
* empty lists, the empty degree vector, and vertex sets with no pairs;
* constant functions, which need no query in any model.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

/-! ## The models -/

section Statements

variable {V O : Type} [Fintype V] [DecidableEq V] [DecidableEq O]

/-- **Edge lists**: `Q_list(f; n)` is the complexity of computing `f` of the set of nonnull
entries of a list `x : Fin n → Option (Edge V)`. -/
example (f : Finset (Edge V) → O) (n : ℕ) :
    qList f n = qQuery (fun x : Fin n → Option (Edge V) => f (recordSet x)) (1 / 3) ∧
      ∀ (x : Fin n → Option (Edge V)) (e : Edge V), e ∈ recordSet x ↔ ∃ i, x i = some e :=
  ⟨rfl, fun _ _ => mem_recordSet⟩

/-- **Adjacency matrices**: `Q_matrix(f)` is the complexity of computing `f` from one bit per pair
of distinct vertices, the edges being the pairs whose bit is set.  Every graph has exactly one
matrix. -/
example (f : Finset (Edge V) → O) (S : Finset (Edge V)) :
    qMatrix f = qQuery (fun a : Edge V → Bool => f (matrixGraph a)) (1 / 3) ∧
      (∀ (a : Edge V → Bool) (e : Edge V), e ∈ matrixGraph a ↔ a e = true) ∧
      matrixGraph (fun e => decide (e ∈ S)) = S ∧ Function.Injective (matrixGraph (V := V)) :=
  ⟨rfl, fun _ _ => mem_matrixGraph, matrixGraph_indicator S, matrixGraph_injective⟩

/-- **Adjacency arrays**: the promise.  A valid array has no loops, no repeated neighbour in a
row, and symmetric adjacency; the rows may be in any order. -/
example (deg : V → ℕ) (nbr : ((u : V) × Fin (deg u)) → V) :
    IsAdjArray deg nbr ↔ (∀ u j, nbr ⟨u, j⟩ ≠ u) ∧
      (∀ u, Function.Injective fun j : Fin (deg u) => nbr ⟨u, j⟩) ∧
      (∀ u w, (∃ j, nbr ⟨u, j⟩ = w) → ∃ j, nbr ⟨w, j⟩ = u) :=
  ⟨fun h => ⟨h.ne_self, h.row_injective, h.symm⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- **Adjacency arrays**: `qAdj f deg` is the complexity of computing `f` of the represented
graph over the valid arrays with the public degree vector `deg`, a query to `(u, j)` returning
the `j`th neighbour of `u`.  The represented graph has row `u` as the neighbourhood of `u`, and
`∑ u, deg u` is twice its number of edges.  Every graph has an array. -/
example (f : Finset (Edge V) → O) (deg : V → ℕ) (nbr : AdjPos deg → V) (h : IsAdjArray deg nbr)
    (S : Finset (Edge V)) (u w : V) :
    qAdj f deg = qQueryOn (fun a : {nbr : AdjPos deg → V // IsAdjArray deg nbr} => a.1)
        (fun a => f (adjGraph deg a.1)) (1 / 3) ∧
      ((toGraph (adjGraph deg nbr)).Adj u w ↔ ∃ j, nbr ⟨u, j⟩ = w) ∧
      ∑ u, deg u = 2 * (adjGraph deg nbr).card ∧
      ∃ (deg' : V → ℕ) (nbr' : AdjPos deg' → V), IsAdjArray deg' nbr' ∧ adjGraph deg' nbr' = S :=
  ⟨rfl, adjGraph_adj h, sum_deg_eq_two_mul_card_adjGraph h, exists_adjArray S⟩

/-- **`Q_adj(f; m)`** is the worst case over the degree vectors with `∑ u, deg u = 2m`. -/
example (f : Finset (Edge V) → O) (m : ℕ) (deg : V → ℕ) (hdeg : ∑ u, deg u = 2 * m) :
    qAdjEdges f m = ⨆ d : {deg : V → ℕ // ∑ u, deg u = 2 * m}, qAdj f d.1 ∧
      qAdj f deg ≤ qAdjEdges f m :=
  ⟨rfl, qAdj_le_qAdjEdges f hdeg⟩

/-! ## `eq:graph-model-comparison` -/

/-- **`eq:graph-model-comparison`**: `Q_matrix(f) ≤ 2·Q_list(f; C(v, 2))` and
`Q_adj(f; m) ≤ 2·Q_list(f; 2m)`, with the factor two of the reversible simulation. -/
example (f : Finset (Edge V) → O) (deg : V → ℕ) (m : ℕ) :
    qMatrix f ≤ 2 * qList f ((Fintype.card V).choose 2) ∧
      qAdj f deg ≤ 2 * qList f (∑ u, deg u) ∧ qAdjEdges f m ≤ 2 * qList f (2 * m) :=
  ⟨qMatrix_le_two_mul_qList f, qAdj_le_two_mul_qList f deg, qAdjEdges_le_two_mul_qList f m⟩

/-- The two simulations behind it, for any finite positions, alphabets and promise: renaming the
positions is free, and a position-dependent map of the answers costs a factor two. -/
example {ι ι' σ τ X : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [Finite X]
    (e : ι ≃ ι') (lift : ι → σ → τ) (read : X → ι → σ) (g : X → O) (ε : ℝ)
    (hne : (QueryCounts (fun x i => lift i (read x i)) g ε).Nonempty) :
    qQueryOn (fun x i' => read x (e.symm i')) g ε = qQueryOn read g ε ∧
      qQueryOn read g ε ≤ 2 * qQueryOn (fun x i => lift i (read x i)) g ε :=
  ⟨qQueryOn_reindex e read g ε, qQueryOn_positionAlphabetMap_le lift read g hne⟩

/-! ## `eq:graph-certificate-list` and `eq:graph-certificate-matrix` -/

/-- **`eq:graph-certificate-list`** and **`eq:graph-certificate-matrix`**, with
`b_f = strongCertificateSize f`:
`Q_list(f; n) ≤ min{n, 2^18·√(n·b_f)}`, `Q_matrix(f) ≤ min{N, 2^18·√(N·b_f)} ≤ 2^18·v·√b_f`,
`Q_adj ≤ min{∑ deg, 2^18·√((∑ deg)·b_f)}` and
`Q_adj(f; m) ≤ min{2m, 2^19·√(m·b_f)} ≤ 2^19·min{m, √(m·b_f)}`. -/
example (f : Finset (Edge V) → O) (n m : ℕ) (deg : V → ℕ) :
    (qList f n : ℝ) ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * strongCertificateSize f)) ∧
      (qMatrix f : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
        (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * strongCertificateSize f)) ∧
      (qMatrix f : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (strongCertificateSize f) ∧
      (qAdj f deg : ℝ) ≤ min ((∑ u, deg u : ℕ) : ℝ)
        (2 ^ 18 * Real.sqrt ((∑ u, deg u : ℕ) * strongCertificateSize f)) ∧
      (qAdjEdges f m : ℝ) ≤ min (2 * m : ℝ)
        (2 ^ 19 * Real.sqrt (m * strongCertificateSize f)) ∧
      (qAdjEdges f m : ℝ) ≤ 2 ^ 19 * min (m : ℝ) (Real.sqrt (m * strongCertificateSize f)) :=
  ⟨qList_le_min_sqrt f n, qMatrix_le_min_sqrt f, qMatrix_le_mul_sqrt f, qAdj_le_min_sqrt f deg,
    qAdjEdges_le_min_sqrt f m, qAdjEdges_le_mul_min f m⟩

/-- **A certificate bound `b_f = O(v)` gives `O(v^{3/2})` matrix queries and
`O(min{m, √(m·v)})` adjacency-list queries.** -/
example (f : Finset (Edge V) → O) (m : ℕ) (h : strongCertificateSize f ≤ Fintype.card V) :
    (qMatrix f : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges f m : ℝ) ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * Fintype.card V)) :=
  ⟨qMatrix_le_mul_sqrt_of_le h, qAdjEdges_le_min_sqrt_of_le h m⟩

/-! ## The applications -/

/-- **Connected components** (`v - 1`), with connectivity and `s`–`t` connectivity: list,
matrix and adjacency-list bounds, and the `O(v^{3/2})` matrix entry of
`tab:graph-certificates`. -/
example (s t : V) (n m : ℕ) :
    (qList (connectedComponents (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (Fintype.card V - 1 : ℕ))) ∧
      (qMatrix (connectedComponents (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
        (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (Fintype.card V - 1 : ℕ))) ∧
      (qMatrix (connectedComponents (V := V)) : ℝ)
        ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (connectedComponents (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (Fintype.card V - 1 : ℕ))) ∧
      (qList (isConnected (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (Fintype.card V - 1 : ℕ))) ∧
      (qMatrix (isConnected (V := V)) : ℝ)
        ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (isConnected (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (Fintype.card V - 1 : ℕ))) ∧
      (qList (isSTConnected s t) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (Fintype.card V - 1 : ℕ))) ∧
      (qMatrix (isSTConnected s t) : ℝ)
        ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (isSTConnected s t) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (Fintype.card V - 1 : ℕ))) :=
  ⟨connectedComponents_qList_le n, connectedComponents_qMatrix_le,
    connectedComponents_qMatrix_le_mul_sqrt, connectedComponents_qAdjEdges_le m,
    connectivity_qList_le n, connectivity_qMatrix_le_mul_sqrt, connectivity_qAdjEdges_le m,
    stConnectivity_qList_le s t n, stConnectivity_qMatrix_le_mul_sqrt s t,
    stConnectivity_qAdjEdges_le s t m⟩

/-- **Bipartiteness** (`v`): all proper two-colourings, the decision and a canonical colouring,
and the `O(v^{3/2})` matrix entry of `tab:graph-certificates`. -/
example (n m : ℕ) :
    (qList (twoColorings (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * Fintype.card V)) ∧
      (qMatrix (twoColorings (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
        (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * Fintype.card V)) ∧
      (qMatrix (twoColorings (V := V)) : ℝ)
        ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (twoColorings (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * Fintype.card V)) ∧
      (qList (isBipartite (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * Fintype.card V)) ∧
      (qMatrix (isBipartite (V := V)) : ℝ)
        ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (isBipartite (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * Fintype.card V)) ∧
      (qList (properTwoColoring (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * Fintype.card V)) ∧
      (qMatrix (properTwoColoring (V := V)) : ℝ)
        ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (properTwoColoring (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * Fintype.card V)) :=
  ⟨twoColorings_qList_le n, twoColorings_qMatrix_le, twoColorings_qMatrix_le_mul_sqrt,
    twoColorings_qAdjEdges_le m, bipartite_qList_le n, bipartite_qMatrix_le_mul_sqrt,
    bipartite_qAdjEdges_le m, properTwoColoring_qList_le n,
    properTwoColoring_qMatrix_le_mul_sqrt, properTwoColoring_qAdjEdges_le m⟩

/-- **Cycle detection** (`v`), with the `O(v^{3/2})` matrix entry of
`tab:graph-certificates`. -/
example (n m : ℕ) :
    (qList (hasCycle (V := V)) n : ℝ) ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * Fintype.card V)) ∧
      (qMatrix (hasCycle (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
        (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * Fintype.card V)) ∧
      (qMatrix (hasCycle (V := V)) : ℝ) ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (hasCycle (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * Fintype.card V)) :=
  ⟨cycle_qList_le n, cycle_qMatrix_le, cycle_qMatrix_le_mul_sqrt, cycle_qAdjEdges_le m⟩

/-- **`prop:sparse-certificates`** (`L + 1`): a property whose yes-instances have at most `L`
edges, in all three models. -/
example (P : SimpleGraph V → Prop) [DecidablePred P] (L n m : ℕ)
    (hP : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ L) :
    (qList (fun S : Finset (Edge V) => decide (P (toGraph S))) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (L + 1 : ℕ))) ∧
      (qMatrix (fun S : Finset (Edge V) => decide (P (toGraph S))) : ℝ)
        ≤ min ((Fintype.card V).choose 2 : ℝ)
          (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (L + 1 : ℕ))) ∧
      (qMatrix (fun S : Finset (Edge V) => decide (P (toGraph S))) : ℝ)
        ≤ 2 ^ 18 * Fintype.card V * Real.sqrt (L + 1 : ℕ) ∧
      (qAdjEdges (fun S : Finset (Edge V) => decide (P (toGraph S))) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (L + 1 : ℕ))) :=
  ⟨sparseYes_qList_le P hP n, sparseYes_qMatrix_le P hP, sparseYes_qMatrix_le_mul_sqrt P hP,
    sparseYes_qAdjEdges_le P hP m⟩

end Statements

/-! ## Sanity checks -/

section Sanity

/-- The edges `{0, 1}` and `{1, 2}` on three vertices. -/
private def e01 : Edge (Fin 3) := ⟨s(0, 1), by decide⟩
private def e12 : Edge (Fin 3) := ⟨s(1, 2), by decide⟩

/-- **A list with a null entry and a repeated edge** represents the set of its edges. -/
example : recordSet ![some e01, none, some e12, some e01] = {e01, e12} := by decide

/-- The degree vector `(1, 1, 0)` on three vertices. -/
private def deg110 : Fin 3 → ℕ := ![1, 1, 0]

/-- The array listing `1` as the neighbour of `0` and `0` as the neighbour of `1`; vertex `2` has
no neighbour. -/
private def nbr110 : AdjPos deg110 → Fin 3 := fun p => if p.1 = 0 then 1 else 0

private theorem isAdjArray_nbr110 : IsAdjArray deg110 nbr110 :=
  ⟨by decide, by decide, by decide⟩

/-- **An adjacency array with an isolated vertex**: the single edge `{0, 1}` on three vertices.
Vertex `2` has degree `0` and no neighbour, and `∑ u, deg u = 2 = 2·1`. -/
example : adjGraph deg110 nbr110 = {e01} ∧
    (∀ w, ¬(toGraph (adjGraph deg110 nbr110)).Adj 2 w) ∧ ∑ u, deg110 u = 2 * 1 := by
  refine ⟨by decide, fun w h => ?_, by decide⟩
  obtain ⟨j, -⟩ := (adjGraph_adj isAdjArray_nbr110).mp h
  exact absurd j.2 (by simp [deg110])

/-- **The promise excludes asymmetric arrays**: listing `1` in row `0` with an empty row `1` is
not a valid array. -/
example : ¬IsAdjArray (![1, 0] : Fin 2 → ℕ) (fun _ => 1) := fun h => by
  obtain ⟨j, -⟩ := h.symm 0 1 ⟨⟨0, by decide⟩, rfl⟩
  exact absurd j.2 (by simp)

variable {V O : Type} [Fintype V] [DecidableEq V] [DecidableEq O]

/-- **No positions, no query**: the empty list, the empty degree vector, and `Q_adj(f; 0)`. -/
example (f : Finset (Edge V) → O) :
    qList f 0 = 0 ∧ qAdj f (fun _ => 0) = 0 ∧ qAdjEdges f 0 = 0 := by
  refine ⟨Nat.le_zero.mp (qList_le f 0), Nat.le_zero.mp ((qAdj_le f _).trans (by simp)), ?_⟩
  have h := qAdjEdges_le_min_sqrt f 0
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.sqrt_zero, min_self] at h
  exact_mod_cast le_antisymm h (Nat.cast_nonneg _)

/-- **A vertex set with no pairs**: with one vertex there are no pairs to query, so every `f`
costs no matrix query. -/
example (f : Finset (Edge (Fin 1)) → O) : qMatrix f = 0 := by
  have h := qMatrix_le_two_mul_qList f
  rw [show (Fintype.card (Fin 1)).choose 2 = 0 by decide] at h
  have h0 := qList_le f 0
  omega

/-- **Constant functions need no query** in any model: their certificate size is zero. -/
example (c : O) (n m : ℕ) :
    qList (fun _ : Finset (Edge V) => c) n = 0 ∧ qMatrix (fun _ : Finset (Edge V) => c) = 0 ∧
      qAdjEdges (fun _ : Finset (Edge V) => c) m = 0 := by
  have h0 : strongCertificateSize (fun _ : Finset (Edge V) => c) = 0 :=
    strongCertificateSize_eq_zero_iff.mpr fun _ _ => rfl
  have hl := qList_le_min_sqrt (fun _ : Finset (Edge V) => c) n
  have hm := qMatrix_le_min_sqrt (fun _ : Finset (Edge V) => c)
  have ha := qAdjEdges_le_min_sqrt (fun _ : Finset (Edge V) => c) m
  rw [h0] at hl hm ha
  simp only [Nat.cast_zero, mul_zero, Real.sqrt_zero] at hl hm ha
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast le_antisymm (hl.trans (min_le_right _ _)) (Nat.cast_nonneg _)
  · exact_mod_cast le_antisymm (hm.trans (min_le_right _ _)) (Nat.cast_nonneg _)
  · exact_mod_cast le_antisymm (ha.trans (min_le_right _ _)) (Nat.cast_nonneg _)

end Sanity

end MonoidProduct.Graph
