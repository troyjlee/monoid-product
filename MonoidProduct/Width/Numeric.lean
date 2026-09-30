import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The numeric endgame of the index-two width bound

From the ball inequality `2^B ≤ m·∑_{j≤ℓ} C(B,j)` with `ℓ = ⌊log₂ m⌋`, deduce
`B < 5·log₂ m` (final paragraph of the proof of `thm:index-two-width`).  Two departures
from the paper's write-up make the formal proof shorter:

* **The Hamming-ball estimate is proved at the real exponent `L = log₂ m`
  directly**, by the generating-function trick with parameter `L/B`:

    `∑_{j≤ℓ} C(B,j) ≤ (B/L)^L · ∑_j C(B,j)(L/B)^j ≤ (B/L)^L (1+L/B)^B ≤ (eB/L)^L`.

  The paper instead proves it at `ℓ` and transfers along the monotonicity of
  `u ↦ u·log(eB/u)` — a calculus lemma the formal proof never needs.

* **The exclusion of `t = B/L ≥ 5` is an affine comparison, not a derivative
  argument**: `log₂ t ≤ log₂ 5 + (t/5 - 1)/log 2` by the tangent bound
  `log u ≤ u - 1`, and the resulting affine inequality has slope
  `1/(5 log 2) < 1`, so failing at `t = 5` (because `5e < 16`) means failing
  everywhere beyond.

The numeric inputs are `Real.exp_one_lt_d9` and `Real.log_two_gt_d9`.
-/

namespace MonoidProduct

open Real Finset

/-- **The Hamming-ball estimate at a real radius**: for `0 < L ≤ B` and
`ℓ ≤ L`, the ball of radius `ℓ` has at most `(eB/L)^L` points. -/
lemma sum_choose_le_rpow {B ℓ : ℕ} {L : ℝ} (hL0 : 0 < L) (hLB : L ≤ B)
    (hlL : (ℓ : ℝ) ≤ L) :
    (∑ j ∈ range (ℓ + 1), (B.choose j : ℝ))
      ≤ (Real.exp 1 * B / L) ^ (L : ℝ) := by
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le hL0 hLB
  have hBn0 : B ≠ 0 := by
    exact_mod_cast hB0.ne'
  have hq0 : (0 : ℝ) < B / L := div_pos hB0 hL0
  have hq1 : (1 : ℝ) ≤ B / L := (one_le_div hL0).mpr hLB
  -- each term picks up a factor `(L/B)^j (B/L)^L ≥ 1`
  have hterm : ∀ j ∈ range (ℓ + 1), (B.choose j : ℝ)
      ≤ (B / L) ^ (L : ℝ) * ((B.choose j : ℝ) * (L / B) ^ j) := by
    intro j hj
    have hjL : (j : ℝ) ≤ L := by
      have : (j : ℝ) ≤ ℓ := by
        exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hj)
      linarith
    have hfac : (1 : ℝ) ≤ (B / L) ^ (L : ℝ) * (L / B) ^ j := by
      have h1 : (1 : ℝ) ≤ (B / L) ^ (L - (j : ℝ)) :=
        Real.one_le_rpow hq1 (by linarith)
      have h2 : (B / L) ^ (L - (j : ℝ))
          = (B / L) ^ (L : ℝ) * (L / B) ^ j := by
        rw [sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_neg hq0.le,
          Real.rpow_natCast, ← inv_pow, inv_div]
      rwa [h2] at h1
    calc (B.choose j : ℝ) = (B.choose j : ℝ) * 1 := by ring
      _ ≤ (B.choose j : ℝ) * ((B / L) ^ (L : ℝ) * (L / B) ^ j) :=
          mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg _)
      _ = (B / L) ^ (L : ℝ) * ((B.choose j : ℝ) * (L / B) ^ j) := by ring
  -- the generating function is the binomial expansion of `(1 + L/B)^B`
  have hgen : (∑ j ∈ range (ℓ + 1), (B.choose j : ℝ) * (L / B) ^ j)
      ≤ (1 + L / B) ^ B := by
    have hℓB : ℓ ≤ B := by
      have h := le_trans hlL hLB
      exact_mod_cast h
    have hsub : range (ℓ + 1) ⊆ range (B + 1) := by
      intro j hj
      rw [Finset.mem_range] at hj ⊢
      omega
    have hfull : (∑ j ∈ range (B + 1), (B.choose j : ℝ) * (L / B) ^ j)
        = (1 + L / B) ^ B := by
      rw [add_comm (1 : ℝ), add_pow]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← hfull]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => ?_
    have hLB' : (0 : ℝ) ≤ L / B := le_of_lt (div_pos hL0 hB0)
    positivity
  -- `(1 + L/B)^B ≤ exp L`
  have hexp : ((1 : ℝ) + L / B) ^ B ≤ Real.exp L := by
    have h1 : (1 : ℝ) + L / B ≤ Real.exp (L / B) := by
      have := Real.add_one_le_exp (L / B)
      linarith
    have h2 : ((1 : ℝ) + L / B) ^ B ≤ Real.exp (L / B) ^ B := by
      have hnn : (0 : ℝ) ≤ 1 + L / B := by
        have : (0 : ℝ) ≤ L / B := le_of_lt (div_pos hL0 hB0)
        linarith
      gcongr
    have h3 : Real.exp (L / B) ^ B = Real.exp L := by
      rw [← Real.rpow_natCast (Real.exp (L / B)) B, ← Real.exp_mul,
        div_mul_cancel₀ _ (by exact_mod_cast hBn0 : (B : ℝ) ≠ 0)]
    rwa [h3] at h2
  -- assemble
  calc (∑ j ∈ range (ℓ + 1), (B.choose j : ℝ))
      ≤ ∑ j ∈ range (ℓ + 1),
          (B / L) ^ (L : ℝ) * ((B.choose j : ℝ) * (L / B) ^ j) :=
        Finset.sum_le_sum hterm
    _ = (B / L) ^ (L : ℝ)
          * ∑ j ∈ range (ℓ + 1), (B.choose j : ℝ) * (L / B) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ (B / L) ^ (L : ℝ) * Real.exp L := by
        refine mul_le_mul_of_nonneg_left (le_trans hgen hexp) ?_
        exact Real.rpow_nonneg (le_of_lt hq0) _
    _ = (Real.exp 1 * B / L) ^ (L : ℝ) := by
        rw [← Real.exp_one_rpow L, mul_div_assoc,
          Real.mul_rpow (le_of_lt (Real.exp_pos 1)) (le_of_lt hq0), mul_comm]

/-- **The affine exclusion of `t ≥ 5`**: `t ≤ 1 + log₂(e·t)` fails for
`t ≥ 5`, because it fails at `5` (`5e < 16`) and the right side has slope
`1/(5·log 2) < 1` past that point. -/
lemma lt_five_of_le_one_add_logb {t : ℝ} (ht : 5 ≤ t)
    (h : t ≤ 1 + Real.logb 2 (Real.exp 1 * t)) : False := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  -- the tangent bound at `t = 5`
  have htan : Real.logb 2 t ≤ Real.logb 2 5 + (t / 5 - 1) / Real.log 2 := by
    have h1 : Real.log (t / 5) ≤ t / 5 - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    have h2 : Real.log (t / 5) = Real.log t - Real.log 5 :=
      Real.log_div (by linarith) (by norm_num)
    rw [Real.logb, Real.logb, ← add_div, div_le_div_iff_of_pos_right
      (by linarith : (0 : ℝ) < Real.log 2)]
    linarith
  -- split the logarithm of the product
  have hsplit : Real.logb 2 (Real.exp 1 * t)
      = Real.logb 2 (Real.exp 1) + Real.logb 2 t :=
    Real.logb_mul (ne_of_gt he0) (ne_of_gt ht0)
  -- `log₂(5e) < 4`, because `5e < 16`
  have hfive : Real.logb 2 (Real.exp 1) + Real.logb 2 5 < 4 := by
    have h5e : Real.exp 1 * 5 < 16 := by nlinarith
    have h1 : Real.logb 2 (Real.exp 1) + Real.logb 2 5
        = Real.logb 2 (Real.exp 1 * 5) :=
      (Real.logb_mul (ne_of_gt he0) (by norm_num)).symm
    have h2 : Real.logb 2 (Real.exp 1 * 5) < Real.logb 2 16 := by
      refine (Real.logb_lt_logb_iff (by norm_num) ?_ (by norm_num)).mpr h5e
      positivity
    have h3 : Real.logb 2 (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [h1]
    linarith
  -- assemble the affine contradiction
  have hmain : t ≤ 1 + Real.logb 2 (Real.exp 1) + Real.logb 2 5
      + (t / 5 - 1) / Real.log 2 := by
    rw [hsplit] at h
    linarith
  -- clear the division by `log 2`
  have hdiv : (t / 5 - 1) / Real.log 2 * Real.log 2 = t / 5 - 1 :=
    div_mul_cancel₀ _ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hmain (by linarith : (0 : ℝ) ≤ Real.log 2),
    mul_lt_mul_of_pos_right hfive (by linarith : (0 : ℝ) < Real.log 2),
    mul_nonneg (by linarith : (0 : ℝ) ≤ t - 5)
      (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 5)]

/-- **The endgame** (final paragraph of the proof of `thm:index-two-width`): the ball
inequality `2^B ≤ m·∑_{j≤⌊log₂ m⌋} C(B,j)` forces `B < 5·log₂ m`. -/
theorem lt_five_logb_of_ball {m B : ℕ} (hm : 2 ≤ m)
    (hball : 2 ^ B ≤ m * ∑ j ∈ range (Nat.log 2 m + 1), B.choose j) :
    (B : ℝ) < 5 * Real.logb 2 m := by
  set L : ℝ := Real.logb 2 m with hLdef
  have hm0 : (0 : ℝ) < m := by positivity
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) hm0, Real.rpow_one]
    exact hm2
  have hL0 : (0 : ℝ) < L := by linarith
  -- if the budget is below `L` there is nothing to prove
  rcases lt_or_ge (B : ℝ) L with hBL | hLB
  · nlinarith
  -- the floor is below the real logarithm
  have hlL : ((Nat.log 2 m : ℕ) : ℝ) ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) hm0]
    have h1 : ((2 : ℕ) ^ Nat.log 2 m : ℕ) ≤ m := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 : ℝ)) ^ ((Nat.log 2 m : ℕ) : ℝ)
        = (((2 : ℕ) ^ Nat.log 2 m : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      ring
    rw [h2]
    exact_mod_cast h1
  -- the ball bound, over the reals
  have hcast : ((2 : ℝ)) ^ B ≤ (m : ℝ)
      * ∑ j ∈ range (Nat.log 2 m + 1), (B.choose j : ℝ) := by
    exact_mod_cast hball
  have hham := sum_choose_le_rpow (B := B) (ℓ := Nat.log 2 m) hL0 hLB hlL
  have hX0 : (0 : ℝ) < Real.exp 1 * B / L := by
    have hB0 : (0 : ℝ) < B := lt_of_lt_of_le hL0 hLB
    positivity
  have hchain : ((2 : ℝ)) ^ B ≤ (m : ℝ) * (Real.exp 1 * B / L) ^ (L : ℝ) := by
    refine le_trans hcast ?_
    refine mul_le_mul_of_nonneg_left hham (le_of_lt hm0)
  -- take base-two logarithms
  have hB' : (B : ℝ) ≤ L + L * Real.logb 2 (Real.exp 1 * B / L) := by
    have h1 : Real.logb 2 ((2 : ℝ) ^ B) = B := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    have h2 : Real.logb 2 ((m : ℝ) * (Real.exp 1 * B / L) ^ (L : ℝ))
        = L + L * Real.logb 2 (Real.exp 1 * B / L) := by
      rw [Real.logb_mul (ne_of_gt hm0)
          (ne_of_gt (Real.rpow_pos_of_pos hX0 _)),
        Real.logb_rpow_eq_mul_logb_of_pos hX0, ← hLdef, mul_comm]
    have h3 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hchain
    rw [h1, h2] at h3
    exact h3
  -- the exclusion
  by_contra hge
  push_neg at hge
  have ht5 : 5 ≤ (B : ℝ) / L := by
    rw [le_div_iff₀ hL0]
    linarith
  refine lt_five_of_le_one_add_logb ht5 ?_
  have harg : Real.exp 1 * ((B : ℝ) / L) = Real.exp 1 * B / L := by
    ring
  rw [harg, div_le_iff₀ hL0,
    show (1 + Real.logb 2 (Real.exp 1 * B / L)) * L
      = L + L * Real.logb 2 (Real.exp 1 * B / L) from by ring]
  exact hB'

end MonoidProduct
