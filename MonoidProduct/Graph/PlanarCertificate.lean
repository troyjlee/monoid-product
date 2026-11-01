import MonoidProduct.Graph.Planar
import MonoidProduct.Graph.Quantum
import MonoidProduct.Graph.Sparse
set_option linter.style.header false

/-!
# Planarity: certificate size and query bounds

`monoid.tex`, section `sec:graph-certificates`, paragraph "Planarity and minor-closed
properties", and the planarity row of `tab:graph-certificates`.  Write `v = #V` and
`N = C(v, 2)`.

* `isPlanar S`: whether `toGraph S` is planar, for the planarity `IsPlanar` of
  `Graph/Planar.lean` (a spherical rotation system).
* `planarity_strongCertificateSize_le`: `b_planar ≤ min{N, 3v - 5}`.  For `v ≥ 3` this is
  `prop:sparse-certificates` with the planar edge bound `3v - 6` (`IsPlanar.ncard_edgeSet_le`);
  for `v ≤ 2` it is the cap `N`, which then equals `3v - 5` in `ℕ`.  So the paper's hypothesis
  `v ≥ 3` is not needed.
* The query bounds: `Q_list(planar; n) ≤ min{n, 2^18·√(n(3v - 5))}`, the paper's
  `O(min{n, √(nv)})`; `Q_matrix ≤ 2^19·v·√v`, the `O(v^{3/2})` of `tab:graph-certificates`; and
  the adjacency-list form.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

section Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Planarity** of `toGraph S`. -/
noncomputable def isPlanar (S : Finset (Edge V)) : Bool := by
  classical exact decide (IsPlanar (toGraph S))

omit [Fintype V] [DecidableEq V] in
theorem isPlanar_eq_true_iff {S : Finset (Edge V)} :
    isPlanar S = true ↔ IsPlanar (toGraph S) := by
  simp [isPlanar]

omit [DecidableEq V] in
/-- Planar edge sets on `v ≥ 3` vertices have at most `3v - 6` edges. -/
theorem card_le_of_isPlanar {S : Finset (Edge V)} (h : isPlanar S = true)
    (hv : 3 ≤ Fintype.card V) : S.card ≤ 3 * Fintype.card V - 6 := by
  rw [← ncard_edgeSet_toGraph]
  exact (isPlanar_eq_true_iff.mp h).ncard_edgeSet_le hv

/-- **Planarity** (`sec:graph-certificates`): `b_planar ≤ min{C(v, 2), 3v - 5}`, for every `v`;
the paper states it for `v ≥ 3`. -/
theorem planarity_strongCertificateSize_le :
    strongCertificateSize (isPlanar (V := V)) ≤
      min ((Fintype.card V).choose 2) (3 * Fintype.card V - 5) := by
  classical
  by_cases hv : 3 ≤ Fintype.card V
  · have h := sparseYes_strongCertificateSize_le (V := V) IsPlanar
      (L := 3 * Fintype.card V - 6) fun G hG => hG.ncard_edgeSet_le hv
    have heq : (fun S : Finset (Edge V) => decide (IsPlanar (toGraph S))) = isPlanar :=
      funext fun S => Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff, isPlanar_eq_true_iff])
    rw [heq, show 3 * Fintype.card V - 6 + 1 = 3 * Fintype.card V - 5 by omega] at h
    exact h
  · have hcap : strongCertificateSize (isPlanar (V := V)) ≤ (Fintype.card V).choose 2 := by
      rw [← card_edge]
      exact strongCertificateSize_le_card _
    refine hcap.trans (le_min le_rfl ?_)
    rcases (show Fintype.card V = 0 ∨ Fintype.card V = 1 ∨ Fintype.card V = 2 by omega)
      with h | h | h <;> rw [h] <;> decide

/-- **Certificates for planarity within `min{C(v, 2), 3v - 5}` edges.** -/
theorem hasStrongCertificateBound_isPlanar :
    HasStrongCertificateBound (isPlanar (V := V))
      (min ((Fintype.card V).choose 2) (3 * Fintype.card V - 5)) :=
  hasStrongCertificateBound_iff_size_le.mpr planarity_strongCertificateSize_le

end Certificate

section Queries

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Planarity from an edge list** (`sec:graph-certificates`):
`Q_list(planar; n) ≤ min{n, 2^18·√(n(3v - 5))}`, the paper's `O(min{n, √(nv)})`. -/
theorem planarity_qList_le (n : ℕ) :
    (qList (isPlanar (V := V)) n : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (3 * Fintype.card V - 5 : ℕ))) :=
  qList_le_min_sqrt_of_le (planarity_strongCertificateSize_le.trans (min_le_right _ _)) n

/-- **Planarity from an adjacency matrix**: `Q_matrix ≤ min{N, 2^18·√(N(3v - 5))}`. -/
theorem planarity_qMatrix_le :
    (qMatrix (isPlanar (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
      (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (3 * Fintype.card V - 5 : ℕ))) :=
  qMatrix_le_min_sqrt_of_le (planarity_strongCertificateSize_le.trans (min_le_right _ _))

/-- **Planarity from an adjacency matrix** (`tab:graph-certificates`): `Q_matrix ≤ 2^19·v·√v`,
the paper's `O(v^{3/2})`. -/
theorem planarity_qMatrix_le_mul_sqrt :
    (qMatrix (isPlanar (V := V)) : ℝ) ≤ 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) := by
  refine (qMatrix_le_mul_sqrt_of_le
    (planarity_strongCertificateSize_le.trans (min_le_right _ _))).trans ?_
  have hb : ((3 * Fintype.card V - 5 : ℕ) : ℝ) ≤ 2 ^ 2 * Fintype.card V := by
    exact_mod_cast (show 3 * Fintype.card V - 5 ≤ 2 ^ 2 * Fintype.card V by omega)
  have h4 : Real.sqrt ((3 * Fintype.card V - 5 : ℕ) : ℝ) ≤ 2 * Real.sqrt (Fintype.card V) :=
    calc Real.sqrt ((3 * Fintype.card V - 5 : ℕ) : ℝ)
        ≤ Real.sqrt (2 ^ 2 * Fintype.card V) := Real.sqrt_le_sqrt hb
      _ = 2 * Real.sqrt (Fintype.card V) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  calc 2 ^ 18 * (Fintype.card V : ℝ) * Real.sqrt ((3 * Fintype.card V - 5 : ℕ) : ℝ)
      ≤ 2 ^ 18 * Fintype.card V * (2 * Real.sqrt (Fintype.card V)) := by gcongr
    _ = 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) := by ring

/-- **Planarity from adjacency lists**: `Q_adj ≤ min{2m, 2^19·√(m(3v - 5))}`. -/
theorem planarity_qAdjEdges_le (m : ℕ) :
    (qAdjEdges (isPlanar (V := V)) m : ℝ)
      ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (3 * Fintype.card V - 5 : ℕ))) :=
  qAdjEdges_le_min_sqrt_of_le (planarity_strongCertificateSize_le.trans (min_le_right _ _)) m

end Queries

end MonoidProduct.Graph
