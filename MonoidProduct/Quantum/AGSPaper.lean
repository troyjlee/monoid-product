import MonoidProduct.Quantum.AGSApplications
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `thm:main-ags` in the paper's displayed form

The paper states the AGS bound as

    Q_{1/3}(Prod_{M,n}) ≤ min{n, √n·((|M|+1)·log(n+2))^{O(D_J(M)+1)}}

with an absolute constant in the exponent.  The explicit forms of
`Quantum/AGSApplications.lean` give it with exponent constant `69` and the
natural logarithm (the smallest of the usual logarithms, so the bound holds for
every base `≤ e`, in particular base `2`):
the base `2^55·(|M|+1)^6·(log₂(n+1)+3)^2` is at most `((|M|+1)·ln(n+2))^69`
(`ags_base_le_pow`), since `(|M|+1)·ln(n+2) ≥ 2·ln 3 ≥ 2` for `n ≥ 1`
(for `n = 0` both sides are `0`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-- `ln 3 > 1`. -/
lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_d9.trans (by norm_num)

/-- The explicit AGS base is at most the 69th power of `(q+1)·ln(n+2)` for `q ≥ 1`. -/
theorem ags_base_le_pow {q : ℝ} (hq : 1 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    2 ^ 55 * (q + 1) ^ 6 * (Real.logb 2 ((n : ℝ) + 1) + 3) ^ 2
      ≤ ((q + 1) * Real.log ((n : ℝ) + 2)) ^ 69 := by
  set L := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := by
    have h3 : Real.log 3 ≤ L :=
      Real.log_le_log (by norm_num) (by have : (1 : ℝ) ≤ n := (by exact_mod_cast hn); linarith)
    linarith [one_lt_log_three]
  set x := (q + 1) * L with hx
  have hy : 2 ≤ q + 1 := by linarith
  have hx2 : 2 ≤ x := by nlinarith
  have hyx : q + 1 ≤ x := by nlinarith
  have hLx : L ≤ x := by nlinarith
  -- `log₂(n+1) + 3 ≤ 8·L`
  have hlog2 : Real.logb 2 ((n : ℝ) + 1) ≤ 2 * L := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have h1 : Real.log ((n : ℝ) + 1) ≤ L :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have hlogpos : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hA : Real.logb 2 ((n : ℝ) + 1) + 3 ≤ x ^ 4 := by
    have h8 : (8 : ℝ) ≤ x ^ 3 := by
      have : (2 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx2 3
      norm_num at this; linarith
    have : Real.logb 2 ((n : ℝ) + 1) + 3 ≤ 8 * L := by linarith
    calc _ ≤ 8 * L := this
      _ ≤ x ^ 3 * x := mul_le_mul h8 hLx (by linarith) (by positivity)
      _ = x ^ 4 := by ring
  have h55 : (2 : ℝ) ^ 55 ≤ x ^ 55 := pow_le_pow_left₀ (by norm_num) hx2 55
  have h6 : (q + 1) ^ 6 ≤ x ^ 6 := pow_le_pow_left₀ (by linarith) hyx 6
  have h2 : (Real.logb 2 ((n : ℝ) + 1) + 3) ^ 2 ≤ (x ^ 4) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hA 2
  calc 2 ^ 55 * (q + 1) ^ 6 * (Real.logb 2 ((n : ℝ) + 1) + 3) ^ 2
      ≤ x ^ 55 * x ^ 6 * (x ^ 4) ^ 2 := by gcongr
    _ = x ^ 69 := by ring

section
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

lemma one_le_card_real : (1 : ℝ) ≤ (Fintype.card M : ℝ) := by
  have : 0 < Fintype.card M := Fintype.card_pos_iff.2 ⟨1⟩
  exact_mod_cast this

/-- **`thm:main-ags`, as displayed** (one-hot model), with exponent constant `69`:

    Q_{1/3}(Prod_{M,n}) ≤ min{n, √n·((|M|+1)·ln(n+2))^{69·(D_J(M)+1)}}. -/
theorem ags_oneHotQQuery_le_paper (n : ℕ) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * (((Fintype.card M : ℝ) + 1) * Real.log ((n : ℝ) + 2))
              ^ (69 * (jDepth M + 1))) := by
  refine le_min (by exact_mod_cast ags_oneHotQQuery_upper_length) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := ags_oneHotQQuery_upper_length (M := M) (n := 0)
    have h0 : oneHotQQuery (fun w : Fin 0 → M => wordProd id w) (1 / 3) = 0 := by omega
    rw [h0]; simp
  refine ags_oneHotQQuery_le_display_logb.trans ?_
  rw [pow_mul]
  gcongr
  exact ags_base_le_pow one_le_card_real hn

/-- **`thm:main-ags`, as displayed** (native model), with exponent constant `69`. -/
theorem ags_qQuery_le_paper (n : ℕ) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * (((Fintype.card M : ℝ) + 1) * Real.log ((n : ℝ) + 2))
              ^ (69 * (jDepth M + 1))) := by
  refine le_min (by exact_mod_cast ags_qQuery_upper_length) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := ags_qQuery_upper_length (M := M) (n := 0)
    have h0 : qQuery (fun w : Fin 0 → M => wordProd id w) (1 / 3) = 0 := by omega
    rw [h0]; simp
  refine ags_qQuery_le_display_logb.trans ?_
  rw [pow_mul]
  gcongr
  refine le_trans ?_ (ags_base_le_pow one_le_card_real hn)
  gcongr
  all_goals norm_num

end

end MonoidProduct
