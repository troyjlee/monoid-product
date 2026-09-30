import MonoidProduct.Stock.Strict
import MonoidProduct.Quantum.OrderedVerified

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The strict stock problem (`prop:stock-beta` + `thm:ordered-beta-product`)

The strict stock-summary monoid of `Stock/Strict.lean` has breadth at most `4` and a stable
order, so the linear-exponent theorem gives `O(√n·log¹⁰(n+2))` queries for the complete
strict summary (`strict_qQuery_le_five_halves`), hence for the strict best profit
`max_{i<j}(x_j − x_i)` itself (`strictProfit_qQuery_le`, free postprocessing), in both error
conventions; and the certified core algorithm with `4` verification queries
(`strict_exists_verified_core_alg`).

Semantic checks (kernel-evaluated): the empty and singleton words have profit `⊥`;
`(5, 2) ↦ −3`; `(2, 2) ↦ 0` (attained at two distinct indices); `(2, 5) ↦ 3`; and the
complete summary of `(10, 2, 5, 0)` needs all four positions, so the breadth bound `4` is
sharp.
-/

namespace MonoidProduct
namespace StrictStock

open QuantumQueryComplexity

/-! ## Query bounds -/

/-- **The strict stock summary** in `O(√n·log¹⁰(n+2))` quantum queries (`b = 4`). -/
theorem strict_qQuery_le_five_halves {σ : Type} [Fintype σ] [DecidableEq σ] (pr : σ → ℤ) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd (letter pr) x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 29 : ℝ) ^ 4 * Real.sqrt n * (logLen n : ℝ) ^ 10) := by
  have h := ordered_qQuery_le_five_halves (letter pr) isStableOrder_summaries
    (isBreadthBound_strict pr) n
  convert h using 2
  rw [orderedLogFactor_pow_four]
  norm_num

/-- The exponent-`3b` form, `O(√n·log¹²(n+2))`. -/
theorem strict_qQuery_le {σ : Type} [Fintype σ] [DecidableEq σ] (pr : σ → ℤ) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd (letter pr) x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 29 : ℝ) ^ 4 * Real.sqrt n * (logLen n : ℝ) ^ 12) := by
  have h := ordered_qQuery_le (letter pr) isStableOrder_summaries (isBreadthBound_strict pr) n
  convert h using 3
  norm_num

/-- The strict profit is free postprocessing of the summary. -/
theorem strictProfit_qQuery_le_wordProd {σ : Type} [Fintype σ] [DecidableEq σ] (pr : σ → ℤ)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → σ => strictProfit pr x) ε
      ≤ qQuery (fun x : Fin n → σ => wordProd (letter pr) x) ε := by
  have hne : (QueryCounts (X := Fin n → σ) id (fun x => wordProd (letter pr) x) ε).Nonempty :=
    queryCounts_nonempty (fun x y h => congrArg (fun z => wordProd (letter pr) z) h) hε
  have h := qQueryOn_postcomp_le (read := (id : (Fin n → σ) → Fin n → σ))
    (f := fun x => wordProd (letter pr) x) (ε := ε) profitOf hne
  simp only [profitOf_wordProd_eq_strictProfit] at h
  exact h

/-- **The strict stock problem** `max_{i<j}(x_j − x_i)` in `O(√n·log¹⁰(n+2))` quantum
queries. -/
theorem strictProfit_qQuery_le {σ : Type} [Fintype σ] [DecidableEq σ] (pr : σ → ℤ) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => strictProfit pr x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 29 : ℝ) ^ 4 * Real.sqrt n * (logLen n : ℝ) ^ 10) :=
  le_trans (by exact_mod_cast strictProfit_qQuery_le_wordProd pr n (by norm_num))
    (strict_qQuery_le_five_halves pr n)

/-- The bounded-error convention `ε = 1/3`. -/
theorem strictProfit_qQuery_third_le {σ : Type} [Fintype σ] [DecidableEq σ] (pr : σ → ℤ)
    (n : ℕ) :
    (qQuery (fun x : Fin n → σ => strictProfit pr x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 29 : ℝ) ^ 4 * Real.sqrt n * (logLen n : ℝ) ^ 10) :=
  le_trans (by exact_mod_cast strictProfit_qQuery_le_wordProd pr n (by norm_num))
    (ordered_qQuery_third_le_of (letter pr) (strict_qQuery_le_five_halves pr n))

open Classical in
/-- **The certified core algorithm for the strict stock summary**: at most
`min {n, (2^29)^4·√n·L_n^{10}} + 4` queries, every output a truthful record of at most `4`
original positions, and the summary-preserving record with probability at least `9/10`. -/
theorem strict_exists_verified_core_alg {σ : Type} [Fintype σ] [DecidableEq σ] (pr : σ → ℤ)
    (n : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ min (n : ℝ) ((2 ^ 29 : ℝ) ^ 4 * Real.sqrt n * (logLen n : ℝ) ^ 10) + 4
      ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x Q K →
          K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ 4 ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec (letter pr) 4 x), B.prob x Q K := by
  obtain ⟨W, hW, hW', B, Q, hQ, hall, hgood⟩ := ordered_exists_verified_core_alg_five_halves
    (letter pr) isStableOrder_summaries (isBreadthBound_strict pr) n
  refine ⟨W, hW, hW', B, Q, ?_, hall, hgood⟩
  convert hQ using 3
  all_goals (try rw [orderedLogFactor_pow_four])
  all_goals norm_num

/-! ## Semantic checks -/

/-- The empty word: no transaction. -/
example : strictProfit (id : ℤ → ℤ) (fun i : Fin 0 => i.elim0) = ⊥ := by
  rw [← profitOf_wordProd_eq_strictProfit]; rfl

/-- A singleton: no transaction, profit `⊥` (not `0`). -/
example : strictProfit (id : ℤ → ℤ) ![7] = ⊥ := by
  rw [← profitOf_wordProd_eq_strictProfit]; decide

/-- Falling prices `(5, 2)`: profit `−3`, no clipping at zero. -/
example : strictProfit (id : ℤ → ℤ) ![5, 2] = ((-3 : ℤ) : WithBot ℤ) := by
  rw [← profitOf_wordProd_eq_strictProfit]; decide

/-- Flat prices `(2, 2)`: profit `0`, attained at two distinct indices. -/
example : strictProfit (id : ℤ → ℤ) ![2, 2] = ((0 : ℤ) : WithBot ℤ) := by
  rw [← profitOf_wordProd_eq_strictProfit]; decide

/-- Rising prices `(2, 5)`: profit `3`. -/
example : strictProfit (id : ℤ → ℤ) ![2, 5] = ((3 : ℤ) : WithBot ℤ) := by
  rw [← profitOf_wordProd_eq_strictProfit]; decide

/-- The complete summary of `(10, 2, 5, 0)`: minimum `0`, maximum `10`, profit `3`. -/
example : wordProd (letter (id : ℤ → ℤ)) ![10, 2, 5, 0] = ((⟨0, 10, ((3 : ℤ) : WithBot ℤ)⟩ : SSumm) : Summaries) := by
  decide

/-- **Sharpness of the breadth bound**: no three positions of `(10, 2, 5, 0)` carry its
complete summary. -/
example : ∀ u : Finset (Fin 4), u.card ≤ 3 →
    subwordProd (letter (id : ℤ → ℤ)) ![10, 2, 5, 0] u ≠ wordProd (letter id) ![10, 2, 5, 0] := by
  decide

end StrictStock
end MonoidProduct
