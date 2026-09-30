import MonoidProduct.Ordered.LogRank

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The cost recurrence of the stages, solved

`costB_le`: if the stage-`0` costs are at most `K·√2^j`, the copy count is at most `2L`, the
thinning rounds at most `5L` and `1600·b·L^4 ≤ K`, then `costB s j ≤ K^{s+1}·√2^j` for every
`j ≤ L`.  The step is the computation

    (j+3)·Vc + Pc ≤ 4(j+1)(j+5)·K^{s+1}√2^j ≤ 20L²·K^{s+1}√2^j,

with `Vc ≤ 4(j+1)K^{s+1}√2^j` because `√2^{j-d}·√2^d = √2^j`, and
`Pc ≤ 8(j+1)K^{s+1}√2^j` because `√2^{j-d} ≤ √2^j`.
-/

namespace MonoidProduct

open Finset

lemma sqrt_two_pow (j : ℕ) : Real.sqrt ((2 : ℝ) ^ j) = Real.sqrt 2 ^ j := by
  rw [show ((2 : ℝ) ^ j) = (Real.sqrt 2 ^ j) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
  exact Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg 2) j)

lemma one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)

section Cost

variable (b : ℕ) (P : MParams) (c R : ℕ)

lemma VcOf_nonneg {A : ℕ → ℝ} (hA : ∀ d, 0 ≤ A d) (j : ℕ) : 0 ≤ VcOf A j := by
  unfold VcOf
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => ?_)
  have := hA (j - d); positivity

lemma PcOf_nonneg {A : ℕ → ℝ} (hA : ∀ d, 0 ≤ A d) (j : ℕ) : 0 ≤ PcOf A j := by
  unfold PcOf
  exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => hA _))

/-- **The recurrence solved.** -/
theorem costB_le {L : ℕ} (hL1 : 1 ≤ L) {K : ℝ} (hK2 : 2 ≤ K)
    (hKb : 1600 * (b : ℝ) * (L : ℝ) ^ 4 ≤ K) (hc : (c : ℝ) ≤ 2 * L) (hR : (R : ℝ) ≤ 5 * L)
    (hbase : ∀ j, j ≤ L → costB b P c R 0 j ≤ K * Real.sqrt 2 ^ j) :
    ∀ s j, j ≤ L → costB b P c R s j ≤ K ^ (s + 1) * Real.sqrt 2 ^ j
  | 0, j, hj => by simpa using hbase j hj
  | s + 1, 0, _ => by
    unfold costB
    have h1 : (1 : ℝ) ≤ K := by linarith
    calc (2 : ℝ) ≤ K := hK2
      _ ≤ K ^ (s + 1 + 1) := le_self_pow₀ h1 (by omega)
      _ = K ^ (s + 1 + 1) * Real.sqrt 2 ^ 0 := by rw [pow_zero, mul_one]
  | s + 1, j + 1, hj => by
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    have hjL : ((j : ℝ) + 1) ≤ L := by exact_mod_cast hj
    have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := one_le_sqrt_two
    have hK0 : 0 ≤ K := by linarith
    have hKs : 0 ≤ K ^ (s + 1) := by positivity
    set X := K ^ (s + 1) * Real.sqrt 2 ^ j with hX
    have hX0 : 0 ≤ X := by positivity
    have hterm : ∀ d ∈ Finset.range (j + 1),
        costB b P c R s (j - d) * Real.sqrt 2 ^ d ≤ X := by
      intro d hd
      rw [Finset.mem_range] at hd
      calc costB b P c R s (j - d) * Real.sqrt 2 ^ d
          ≤ K ^ (s + 1) * Real.sqrt 2 ^ (j - d) * Real.sqrt 2 ^ d :=
            mul_le_mul_of_nonneg_right (costB_le hL1 hK2 hKb hc hR hbase s (j - d) (by omega))
              (by positivity)
        _ = X := by rw [hX, mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
    have hterm' : ∀ d ∈ Finset.range (j + 1), costB b P c R s (j - d) ≤ X := by
      intro d hd
      rw [Finset.mem_range] at hd
      calc costB b P c R s (j - d) ≤ K ^ (s + 1) * Real.sqrt 2 ^ (j - d) :=
            costB_le hL1 hK2 hKb hc hR hbase s (j - d) (by omega)
        _ ≤ X := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs2 (by omega)) hKs
    have hV : VcOf (costB b P c R s) j ≤ 4 * (((j : ℝ) + 1) * X) := by
      unfold VcOf
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc ∑ d ∈ Finset.range (j + 1), costB b P c R s (j - d) * Real.sqrt 2 ^ d
          ≤ ∑ d ∈ Finset.range (j + 1), X := Finset.sum_le_sum hterm
        _ = ((j : ℝ) + 1) * X := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have hP : PcOf (costB b P c R s) j ≤ 8 * (((j : ℝ) + 1) * X) := by
      unfold PcOf
      calc 2 * (4 * ∑ d ∈ Finset.range (j + 1), costB b P c R s (j - d))
          ≤ 2 * (4 * ∑ d ∈ Finset.range (j + 1), X) := by
            gcongr with d hd
            exact hterm' d hd
        _ = 8 * (((j : ℝ) + 1) * X) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have hV0 : 0 ≤ VcOf (costB b P c R s) j := VcOf_nonneg (costB_nonneg b P c R s) j
    have hP0 : 0 ≤ PcOf (costB b P c R s) j := PcOf_nonneg (costB_nonneg b P c R s) j
    have hM0 : 0 ≤ ((j : ℝ) + 3) * VcOf (costB b P c R s) j + PcOf (costB b P c R s) j := by
      positivity
    have hM : ((j : ℝ) + 3) * VcOf (costB b P c R s) j + PcOf (costB b P c R s) j
        ≤ 20 * (L : ℝ) ^ 2 * X := by
      have h1 : ((j : ℝ) + 3) * VcOf (costB b P c R s) j
          ≤ ((j : ℝ) + 3) * (4 * (((j : ℝ) + 1) * X)) :=
        mul_le_mul_of_nonneg_left hV (by positivity)
      have h2 : ((j : ℝ) + 1) * ((j : ℝ) + 5) ≤ (L : ℝ) * (L + 4) :=
        mul_le_mul hjL (by linarith) (by positivity) (by positivity)
      have h3 : (L : ℝ) * (L + 4) ≤ 5 * (L : ℝ) ^ 2 := by nlinarith
      have h4 : 4 * (((j : ℝ) + 1) * ((j : ℝ) + 5)) * X ≤ 4 * (5 * (L : ℝ) ^ 2) * X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h2.trans h3) (by norm_num)) hX0
      nlinarith
    have hcRM : (c : ℝ) * R
          * (((j : ℝ) + 3) * VcOf (costB b P c R s) j + PcOf (costB b P c R s) j)
        ≤ (2 * L) * (5 * L) * (20 * (L : ℝ) ^ 2 * X) :=
      mul_le_mul (mul_le_mul hc hR (by positivity) (by positivity)) hM hM0 (by positivity)
    unfold costB
    calc 2 * ((c : ℝ) * (2 * ((R : ℝ) * (((2 * b : ℕ) : ℝ)
            * (((j : ℝ) + 3) * VcOf (costB b P c R s) j + PcOf (costB b P c R s) j)))))
        = 4 * ((2 * b : ℕ) : ℝ) * ((c : ℝ) * R
            * (((j : ℝ) + 3) * VcOf (costB b P c R s) j + PcOf (costB b P c R s) j)) := by ring
      _ ≤ 4 * ((2 * b : ℕ) : ℝ) * ((2 * L) * (5 * L) * (20 * (L : ℝ) ^ 2 * X)) :=
          mul_le_mul_of_nonneg_left hcRM (by positivity)
      _ = (1600 * (b : ℝ) * (L : ℝ) ^ 4) * X := by push_cast; ring
      _ ≤ K * X := mul_le_mul_of_nonneg_right hKb hX0
      _ = K ^ (s + 1 + 1) * Real.sqrt 2 ^ j := by rw [hX]; ring
      _ ≤ K ^ (s + 1 + 1) * Real.sqrt 2 ^ (j + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs2 (by omega)) (by positivity)

end Cost

end MonoidProduct
