import MonoidProduct.Matroid.Width
import MonoidProduct.Quantum.WidthApplications
set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# Quantum query complexity of minimum-weight matroid bases

This file proves the operational upper bound of `thm:matroid-basis-query` in `monoid.tex`
(section `sec:matroid-bases`).  The input is `x : Fin n → Option (E × W)`: one query
returns a whole weighted element or a null record.  For a public matroid `M` on a finite
linearly ordered type `E` with `M.eRank ≤ r` and a finite linearly ordered weight type `W`,

  `Q_{1/3} ≤ min{n, 2^18·√(n·r)}`

for computing the canonical minimum-weight basis, both as its labelled records
(`matroidBasisRecords_qQuery_le_min_sqrt`) and as its set of input positions
(`matroidBasisIndices_qQuery_le_min_sqrt`).  The bound is uniform in `E`, in `W` and in the
values of the weights, and it has the exact read-all cap `n`.  At `r = 0` no query is needed
(`matroidBasisRecords_qQuery_eq_zero`).

The proof applies the essential-width theorem `thm:essential-width` to the incremental
summary `matroidBasisSummary` over the physical alphabet `Option (E × W)`, whose essential
width is at most `r` (`card_essentialSet_matroidBasisSummary_le`).  The case `n = 0` is
split off first: there the input space is a single point.

`matroidBasis_minWeight_and_qQuery` pairs the query bound with the correctness statement
`basisRecords_isMinimumWeightBasis`.
-/

namespace MonoidProduct.Matroid
open Set QuantumQueryComplexity

variable {E W : Type} [Fintype E] [LinearOrder E] [Fintype W] [LinearOrder W]
variable {M : _root_.Matroid E}

/-- **The essential-width bound for any readout of the canonical basis records**
(`thm:matroid-basis-query`): `Q_{1/3} ≤ min{n, 2^18·√(n·r)}`. -/
theorem matroidBasisReadout_qQuery_le_min_sqrt {O : Type} [Fintype O] [DecidableEq O]
    [Nonempty O] (hM : M.E = univ) {r : ℕ} (hr : M.eRank ≤ r) (n : ℕ)
    (g : Finset (WeightedRecord (Fin n) E W) → O) :
    (qQuery (fun x : Fin n → Option (E × W) => g (basisRecords M x Finset.univ)) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * r)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : qQuery (fun x : Fin 0 → Option (E × W) => g (basisRecords M x Finset.univ))
        (1 / 3) = 0 :=
      qQueryOn_const_eq_zero id (c := g (basisRecords M (fun i => i.elim0) Finset.univ))
        (fun x => by rw [Subsingleton.elim x (fun i => i.elim0)]) (by norm_num)
    rw [h0]
    simp
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have h := summary_qQuery_le_min_sqrt (matroidBasisSummary hM g)
      (card_essentialSet_matroidBasisSummary_le hM hr g)
    rw [Fintype.card_fin] at h
    exact h

/-- **Rank zero: no query is needed** for any readout of the canonical basis records. -/
theorem matroidBasisReadout_qQuery_eq_zero {O : Type} [Fintype O] [DecidableEq O]
    [Nonempty O] (hM : M.E = univ) (hr : M.eRank = 0) (n : ℕ)
    (g : Finset (WeightedRecord (Fin n) E W) → O) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → Option (E × W) => g (basisRecords M x Finset.univ)) ε = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact qQueryOn_const_eq_zero id (c := g (basisRecords M (fun i => i.elim0) Finset.univ))
      (fun x => by rw [Subsingleton.elim x (fun i => i.elim0)]) hε
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact summary_qQuery_eq_zero_of_width_zero (matroidBasisSummary hM g)
      (card_essentialSet_matroidBasisSummary_le hM (r := 0) (by rw [hr]; rfl) g) hε

/-- **Minimum-weight basis records, operational** (`thm:matroid-basis-query`): computing the
canonical basis records `basisRecords M x univ` of `x : Fin n → Option (E × W)` costs
`Q_{1/3} ≤ min{n, 2^18·√(n·r)}` whenever `M.eRank ≤ r`. -/
theorem matroidBasisRecords_qQuery_le_min_sqrt (hM : M.E = univ) {r : ℕ}
    (hr : M.eRank ≤ r) (n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) => basisRecords M x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * r)) :=
  matroidBasisReadout_qQuery_le_min_sqrt hM hr n id

/-- **Minimum-weight basis positions, operational** (`thm:matroid-basis-query`): computing
the positions `basisIndices M x univ` of the canonical minimum-weight basis of
`x : Fin n → Option (E × W)` costs `Q_{1/3} ≤ min{n, 2^18·√(n·r)}` whenever
`M.eRank ≤ r`. -/
theorem matroidBasisIndices_qQuery_le_min_sqrt (hM : M.E = univ) {r : ℕ}
    (hr : M.eRank ≤ r) (n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) => basisIndices M x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * r)) :=
  matroidBasisReadout_qQuery_le_min_sqrt hM hr n (Finset.image WeightedRecord.index)

/-- At rank zero the canonical basis records need no query. -/
theorem matroidBasisRecords_qQuery_eq_zero (hM : M.E = univ) (hr : M.eRank = 0) (n : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → Option (E × W) => basisRecords M x Finset.univ) ε = 0 :=
  matroidBasisReadout_qQuery_eq_zero hM hr n id hε

/-- At rank zero the canonical basis positions need no query. -/
theorem matroidBasisIndices_qQuery_eq_zero (hM : M.E = univ) (hr : M.eRank = 0) (n : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → Option (E × W) => basisIndices M x Finset.univ) ε = 0 :=
  matroidBasisReadout_qQuery_eq_zero hM hr n (Finset.image WeightedRecord.index) hε

/-- **`thm:matroid-basis-query`**: for a matroid `M` on a finite linearly ordered type with
`M.eRank ≤ r`, and weights in a finite linearly ordered type embedded in `ℝ`,

1. for every input `x : Fin n → Option (E × W)`, the returned records are truthful records
   of `x`, they are exactly the input records at the returned positions, the returned
   positions form a basis of the input in the parallel-copy model, and their total weight is
   at most that of every such basis;
2. computing the returned records costs `Q_{1/3} ≤ min{n, 2^18·√(n·r)}`;
3. computing the returned positions costs `Q_{1/3} ≤ min{n, 2^18·√(n·r)}`. -/
theorem matroidBasis_minWeight_and_qQuery (hM : M.E = univ) (weight : W ↪o ℝ) {r : ℕ}
    (hr : M.eRank ≤ r) (n : ℕ) :
    (∀ x : Fin n → Option (E × W),
      (∀ s ∈ basisRecords M x Finset.univ, x s.index = some (s.element, s.weight)) ∧
      records x (basisIndices M x Finset.univ) = basisRecords M x Finset.univ ∧
      IsParallelBasis M x Finset.univ (basisIndices M x Finset.univ) ∧
      ∀ J : Finset (Fin n), IsParallelBasis M x Finset.univ J →
        ∑ i ∈ basisIndices M x Finset.univ, inputWeight weight x i ≤
          ∑ i ∈ J, inputWeight weight x i) ∧
    (qQuery (fun x : Fin n → Option (E × W) => basisRecords M x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * r)) ∧
    (qQuery (fun x : Fin n → Option (E × W) => basisIndices M x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * r)) := by
  refine ⟨fun x => ?_, matroidBasisRecords_qQuery_le_min_sqrt hM hr n,
    matroidBasisIndices_qQuery_le_min_sqrt hM hr n⟩
  obtain ⟨h1, h2, h3, h4⟩ := basisRecords_isMinimumWeightBasis hM weight x Finset.univ
  exact ⟨fun s hs => (h1 s hs).2, h2, h3, h4⟩

end MonoidProduct.Matroid
