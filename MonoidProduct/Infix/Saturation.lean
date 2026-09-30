import MonoidProduct.Infix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Ring.GeomSum

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The saturated distance kernel

For `1 ≤ G ≤ m` and `1 ≤ D ≤ m` (or `D = ∞`) there are vectors `satA m G`,
`satB m D` (`satBInf m`) with

  `⟨satA m G, satB m D⟩ = min {1, D/G}`,  `⟨satA m G, satBInf m⟩ = 1`,

and squared norms `O(λ(m))`, `λ(m) = 1 + log₂ log₂ (m + 4)`.  Three orthogonal
parts, indexed by the dyadic bin `i(t) = ⌊log₂ t⌋` with `U_i = 2^{i+1} − 1`:

* the bin part gives `D/G` when `i(D) ≤ i(G)`;
* the correction part, on pairs `(bin, t)`, subtracts `(D − G)₊/G` when the
  bins agree;
* the order kernel `[i(G) < i(D)]` gives `1` when `D`'s bin is higher (with an
  extra leaf `B + 1` for `∞`).
-/

namespace MonoidProduct.Infix

open Finset

/-- `λ(m) = 1 + log₂ log₂ (m + 4)`. -/
noncomputable def lam (m : ℕ) : ℝ := 1 + Real.logb 2 (Real.logb 2 ((m : ℝ) + 4))

lemma two_le_logb_m_add_four (m : ℕ) : 2 ≤ Real.logb 2 ((m : ℝ) + 4) := by
  have h4 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]; simp
  calc (2 : ℝ) = Real.logb 2 4 := h4.symm
    _ ≤ Real.logb 2 ((m : ℝ) + 4) :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) (by linarith)

lemma two_le_lam (m : ℕ) : 2 ≤ lam m := by
  unfold lam
  have h := two_le_logb_m_add_four m
  have h1 : (1 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((m : ℝ) + 4)) := by
    have : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    calc (1 : ℝ) = Real.logb 2 2 := this.symm
      _ ≤ _ := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h
  linarith

/-- The number of dyadic bins below `m`, minus one. -/
def B (m : ℕ) : ℕ := Nat.log 2 m

/-- The bit length for the order kernel on the bins and the extra leaf. -/
def kk (m : ℕ) : ℕ := Nat.log 2 (B m + 1) + 1

lemma B_add_one_lt (m : ℕ) : B m + 1 < 2 ^ kk m := Nat.lt_pow_succ_log_self (by norm_num) _

lemma kk_add_one_le (m : ℕ) : (kk m : ℝ) + 1 ≤ 2 + lam m := by
  have h1 : (Nat.log 2 (B m + 1) : ℝ) ≤ Real.logb 2 ((B m : ℝ) + 1) := by
    have := Real.natLog_le_logb (B m + 1) 2
    rwa [Nat.cast_add, Nat.cast_one] at this
  have h2 : (B m : ℝ) ≤ Real.logb 2 ((m : ℝ) + 4) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp [B]
      have := two_le_logb_m_add_four 0; simp at this; linarith
    · have := Real.natLog_le_logb m 2
      refine this.trans
        (Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hm) (by linarith))
  have h3 : Real.logb 2 ((B m : ℝ) + 1)
      ≤ Real.logb 2 (2 * Real.logb 2 ((m : ℝ) + 4)) := by
    have h := two_le_logb_m_add_four m
    exact Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) (by linarith)
  have h4 : Real.logb 2 (2 * Real.logb 2 ((m : ℝ) + 4))
      = 1 + Real.logb 2 (Real.logb 2 ((m : ℝ) + 4)) := by
    have h := two_le_logb_m_add_four m
    rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)]
  unfold kk lam
  push_cast
  linarith

/-- `U_i = 2^{i+1} − 1`, the top of the `i`th dyadic bin. -/
def U (i : ℕ) : ℕ := 2 ^ (i + 1) - 1

lemma U_pos (i : ℕ) : 0 < U i := by
  unfold U; have := Nat.one_lt_two_pow (n := i + 1) (by omega); omega

lemma le_U_of_log_le {t i : ℕ} (h : Nat.log 2 t ≤ i) : t ≤ U i := by
  unfold U
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) t
  have h2 : 2 ^ (Nat.log 2 t).succ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma U_lt_two_mul {G : ℕ} (hG : 0 < G) : U (Nat.log 2 G) < 2 * G := by
  unfold U
  have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 hG)
  rw [Nat.pow_succ]
  omega

lemma pow_log_le {G : ℕ} (hG : 0 < G) : 2 ^ Nat.log 2 G ≤ G :=
  Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 hG)

lemma lt_pow_log_succ (t : ℕ) : t < 2 ^ (Nat.log 2 t + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) t

/-- The coordinates: bins, (bin, position) pairs, and the order kernel. -/
abbrev SatIdx (m : ℕ) := Fin (B m + 1) ⊕ (Fin (B m + 1) × Fin (2 * m + 2)) ⊕ OrdIdx (kk m)

/-- The vector of the gap length `G`. -/
noncomputable def satA (m G : ℕ) : SatIdx m → ℝ
  | Sum.inl i => if (i : ℕ) ≤ Nat.log 2 G then (U i : ℝ) / G else 0
  | Sum.inr (Sum.inl (i, t)) =>
      if (i : ℕ) = Nat.log 2 G ∧ G < (t : ℕ) ∧ (t : ℕ) ≤ U i then Real.sqrt (U i) / G else 0
  | Sum.inr (Sum.inr o) => ordB (kk m) (Nat.log 2 G + 1) o

/-- The vector of the distance `D`. -/
noncomputable def satB (m D : ℕ) : SatIdx m → ℝ
  | Sum.inl i => if (i : ℕ) = Nat.log 2 D then (D : ℝ) / U i else 0
  | Sum.inr (Sum.inl (i, t)) =>
      if (i : ℕ) = Nat.log 2 D ∧ 1 ≤ (t : ℕ) ∧ (t : ℕ) ≤ D then -(1 / Real.sqrt (U i)) else 0
  | Sum.inr (Sum.inr o) => ordA (kk m) (Nat.log 2 D) o

/-- The vector of the distance `∞`. -/
noncomputable def satBInf (m : ℕ) : SatIdx m → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr o) => ordA (kk m) (B m + 1) o

variable {m : ℕ}

/-- A count of positions in a window, as a sum over the coordinate range. -/
lemma sum_ite_Ioc (N a b : ℕ) (hb : b < N) :
    ∑ t : Fin N, (if a < (t : ℕ) ∧ (t : ℕ) ≤ b then (1 : ℝ) else 0) = ((b - a : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if a < t ∧ t ≤ b then (1 : ℝ) else 0) N,
    Finset.sum_boole]
  congr 1
  rw [← Nat.card_Ioc a b]
  congr 1
  ext t
  simp only [mem_filter, mem_range, mem_Ioc]
  omega

/-! ## The inner products -/

/-- The bin part: `[i(D) ≤ i(G)]·D/G`. -/
lemma satA_satB_bins {G D : ℕ} (hG : 0 < G) (hDm : D ≤ m) (_hD : 0 < D) :
    ∑ i : Fin (B m + 1), satA m G (Sum.inl i) * satB m D (Sum.inl i)
      = if Nat.log 2 D ≤ Nat.log 2 G then (D : ℝ) / G else 0 := by
  classical
  have hDB : Nat.log 2 D < B m + 1 := by
    have := Nat.log_mono_right (b := 2) hDm; unfold B; omega
  simp only [satA, satB]
  rw [Finset.sum_eq_single ⟨Nat.log 2 D, hDB⟩]
  · simp only [if_true]
    split_ifs with h
    · have hU : (U (Nat.log 2 D) : ℝ) ≠ 0 := by exact_mod_cast (U_pos _).ne'
      field_simp
    · simp
  · intro i _ hi
    rw [if_neg (fun h => hi (Fin.ext h))]; ring
  · intro h; exact absurd (mem_univ _) h

/-- The correction part: `−[i(D) = i(G)]·(D − G)₊/G`. -/
lemma satA_satB_corr {G D : ℕ} (hG : 0 < G) (hDm : D ≤ m) (_hD : 0 < D) :
    ∑ p : Fin (B m + 1) × Fin (2 * m + 2),
        satA m G (Sum.inr (Sum.inl p)) * satB m D (Sum.inr (Sum.inl p))
      = if Nat.log 2 D = Nat.log 2 G then -(((D - G : ℕ) : ℝ) / G) else 0 := by
  classical
  have hDB : Nat.log 2 D < B m + 1 := by
    have := Nat.log_mono_right (b := 2) hDm; unfold B; omega
  rw [Fintype.sum_prod_type]
  simp only [satA, satB]
  rw [Finset.sum_eq_single ⟨Nat.log 2 D, hDB⟩]
  · by_cases h : Nat.log 2 D = Nat.log 2 G
    · rw [if_pos h]
      have hU : (0 : ℝ) < U (Nat.log 2 D) := by exact_mod_cast U_pos _
      have hDU : D ≤ U (Nat.log 2 D) := le_U_of_log_le le_rfl
      have hcount : ∀ t : Fin (2 * m + 2),
          (if (Nat.log 2 D) = Nat.log 2 G ∧ G < (t : ℕ) ∧ (t : ℕ) ≤ U (Nat.log 2 D)
            then Real.sqrt (U (Nat.log 2 D)) / G else 0)
          * (if (Nat.log 2 D) = Nat.log 2 D ∧ 1 ≤ (t : ℕ) ∧ (t : ℕ) ≤ D
            then -(1 / Real.sqrt (U (Nat.log 2 D))) else 0)
          = -(1 / G) * (if G < (t : ℕ) ∧ (t : ℕ) ≤ D then (1 : ℝ) else 0) := by
        intro t
        by_cases ht : G < (t : ℕ) ∧ (t : ℕ) ≤ D
        · rw [if_pos ⟨h, ht.1, ht.2.trans hDU⟩, if_pos ⟨rfl, by omega, ht.2⟩, if_pos ht]
          have hs : Real.sqrt (U (Nat.log 2 D)) ≠ 0 := (Real.sqrt_pos.2 hU).ne'
          field_simp
        · rw [if_neg ht]
          by_cases h1 : G < (t : ℕ)
          · rw [if_neg (show ¬ (Nat.log 2 D = Nat.log 2 D ∧ 1 ≤ (t : ℕ) ∧ (t : ℕ) ≤ D) from
              fun h' => ht ⟨h1, h'.2.2⟩)]
            ring
          · rw [if_neg (show ¬ (Nat.log 2 D = Nat.log 2 G ∧ G < (t : ℕ)
              ∧ (t : ℕ) ≤ U (Nat.log 2 D)) from fun h' => h1 h'.2.1)]
            ring
      rw [Finset.sum_congr rfl (fun t _ => hcount t)]
      rw [← Finset.mul_sum, sum_ite_Ioc _ _ _ (by omega)]
      ring
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [if_neg (fun h' => h h'.1)]; ring
  · intro i _ hi
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg (show ¬ ((i : ℕ) = Nat.log 2 D ∧ 1 ≤ (t : ℕ) ∧ (t : ℕ) ≤ D) from
      fun h' => hi (Fin.ext h'.1))]
    ring
  · intro h; exact absurd (mem_univ _) h

/-- The order part: `[i(G) < i(D)]`. -/
lemma satA_satB_ord {G D : ℕ} (hGm : G ≤ m) (hDm : D ≤ m) :
    ∑ o : OrdIdx (kk m), satA m G (Sum.inr (Sum.inr o)) * satB m D (Sum.inr (Sum.inr o))
      = if Nat.log 2 G < Nat.log 2 D then 1 else 0 := by
  simp only [satA, satB]
  have hk := B_add_one_lt m
  have hG' : Nat.log 2 G + 1 < 2 ^ kk m := by
    have := Nat.log_mono_right (b := 2) hGm; unfold B at hk; omega
  have hD' : Nat.log 2 D < 2 ^ kk m := by
    have := Nat.log_mono_right (b := 2) hDm; unfold B at hk; omega
  rw [show (∑ o : OrdIdx (kk m), ordB (kk m) (Nat.log 2 G + 1) o * ordA (kk m) (Nat.log 2 D) o)
      = ∑ o : OrdIdx (kk m), ordA (kk m) (Nat.log 2 D) o * ordB (kk m) (Nat.log 2 G + 1) o from
    Finset.sum_congr rfl fun o _ => mul_comm _ _, ordA_mul_ordB hD' hG']
  simp only [Nat.succ_le_iff]

/-- **The saturated distance kernel.** -/
theorem satA_mul_satB {G D : ℕ} (hG : 1 ≤ G) (hGm : G ≤ m) (hD : 1 ≤ D) (hDm : D ≤ m) :
    ∑ i, satA m G i * satB m D i = min 1 ((D : ℝ) / G) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, satA_satB_bins hG hDm hD,
    satA_satB_corr hG hDm hD, satA_satB_ord hGm hDm]
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  rcases lt_trichotomy (Nat.log 2 D) (Nat.log 2 G) with hlt | heq | hgt
  · rw [if_pos hlt.le, if_neg hlt.ne, if_neg (not_lt.2 hlt.le)]
    -- `D < 2^{i(D)+1} ≤ 2^{i(G)} ≤ G`
    have hDG : D < G := by
      have h1 := lt_pow_log_succ D
      have h2 : 2 ^ (Nat.log 2 D + 1) ≤ 2 ^ Nat.log 2 G := Nat.pow_le_pow_right (by norm_num) hlt
      have h3 := pow_log_le hG
      omega
    rw [min_eq_right (by rw [div_le_one hGr]; exact_mod_cast hDG.le)]
    ring
  · rw [if_pos heq.le, if_pos heq, if_neg (by omega)]
    rcases le_or_gt D G with hDG | hDG
    · rw [Nat.sub_eq_zero_of_le hDG, min_eq_right (by rw [div_le_one hGr]; exact_mod_cast hDG)]
      simp
    · rw [min_eq_left (by rw [le_div_iff₀ hGr]; norm_num; exact_mod_cast hDG.le)]
      rw [Nat.cast_sub hDG.le]
      field_simp
      ring
  · rw [if_neg (not_le.2 hgt), if_neg hgt.ne', if_pos hgt]
    -- `G < 2^{i(G)+1} ≤ 2^{i(D)} ≤ D`
    have hDG : G < D := by
      have h1 := lt_pow_log_succ G
      have h2 : 2 ^ (Nat.log 2 G + 1) ≤ 2 ^ Nat.log 2 D := Nat.pow_le_pow_right (by norm_num) hgt
      have h3 := pow_log_le hD
      omega
    rw [min_eq_left (by rw [le_div_iff₀ hGr]; norm_num; exact_mod_cast hDG.le)]
    ring

/-- **The value at `∞` is one.** -/
theorem satA_mul_satBInf {G : ℕ} (hGm : G ≤ m) :
    ∑ i, satA m G i * satBInf m i = 1 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [satA, satBInf, mul_zero, Finset.sum_const_zero, zero_add]
  have hk := B_add_one_lt m
  have hG' : Nat.log 2 G + 1 < 2 ^ kk m := by
    have := Nat.log_mono_right (b := 2) hGm; unfold B at hk; omega
  rw [show (∑ o : OrdIdx (kk m), ordB (kk m) (Nat.log 2 G + 1) o * ordA (kk m) (B m + 1) o)
      = ∑ o : OrdIdx (kk m), ordA (kk m) (B m + 1) o * ordB (kk m) (Nat.log 2 G + 1) o from
    Finset.sum_congr rfl fun o _ => mul_comm _ _, ordA_mul_ordB hk hG']
  have := Nat.log_mono_right (b := 2) hGm
  unfold B
  rw [if_pos (by omega)]

/-! ## The norms -/

lemma geom_two_sq_bound (n : ℕ) :
    ∑ i ∈ range (n + 1), ((2 : ℝ) ^ (i + 1)) ^ 2 ≤ 16 / 3 * ((2 : ℝ) ^ n) ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ((2 : ℝ) ^ (n + 1 + 1)) ^ 2 = 16 * ((2 : ℝ) ^ n) ^ 2 := by ring
      have h2 : ((2 : ℝ) ^ (n + 1)) ^ 2 = 4 * ((2 : ℝ) ^ n) ^ 2 := by ring
      rw [h1, h2]
      linarith

lemma U_le_two_mul_m {i : ℕ} (hi : i ≤ B m) (hm : 0 < m) : U i < 2 * m + 2 := by
  unfold U
  have h1 : 2 ^ (i + 1) ≤ 2 ^ (B m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ B m ≤ m := Nat.pow_log_le_self 2 (by omega)
  rw [Nat.pow_succ] at h1
  omega

lemma satA_bins_sq_le {G : ℕ} (hG : 0 < G) (hGm : G ≤ m) :
    ∑ i : Fin (B m + 1), satA m G (Sum.inl i) * satA m G (Sum.inl i) ≤ 16 / 3 := by
  classical
  have hlog : Nat.log 2 G ≤ B m := Nat.log_mono_right hGm
  have hG2 : (2 : ℝ) ^ Nat.log 2 G ≤ G := by exact_mod_cast pow_log_le hG
  have hpos : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 G := by positivity
  have hterm : ∀ i : Fin (B m + 1), satA m G (Sum.inl i) * satA m G (Sum.inl i)
      ≤ if (i : ℕ) ≤ Nat.log 2 G
        then ((2 : ℝ) ^ ((i : ℕ) + 1)) ^ 2 / ((2 : ℝ) ^ Nat.log 2 G) ^ 2 else 0 := by
    intro i
    simp only [satA]
    split_ifs with h
    · have hU : (U i : ℝ) ≤ 2 ^ ((i : ℕ) + 1) := by
        have : U i ≤ 2 ^ ((i : ℕ) + 1) := Nat.sub_le _ _
        exact_mod_cast this
      have hU0 : (0 : ℝ) ≤ U i := by positivity
      rw [← sq, div_pow]
      have hGr : (0 : ℝ) < G := by exact_mod_cast hG
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hU0 hU 2) (by positivity)
      exact pow_le_pow_left₀ hpos.le hG2 2
    · simp
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ Nat.log 2 G
    then ((2 : ℝ) ^ (i + 1)) ^ 2 / ((2 : ℝ) ^ Nat.log 2 G) ^ 2 else 0) (B m + 1),
    ← Finset.sum_filter]
  have hfilt : (range (B m + 1)).filter (fun i => i ≤ Nat.log 2 G) = range (Nat.log 2 G + 1) := by
    ext i; simp only [mem_filter, mem_range]; omega
  rw [hfilt, ← Finset.sum_div, div_le_iff₀ (by positivity)]
  have := geom_two_sq_bound (Nat.log 2 G)
  linarith

lemma satA_corr_sq_le {G : ℕ} (hG : 0 < G) (hGm : G ≤ m) :
    ∑ p : Fin (B m + 1) × Fin (2 * m + 2),
        satA m G (Sum.inr (Sum.inl p)) * satA m G (Sum.inr (Sum.inl p)) ≤ 4 := by
  classical
  have hlog : Nat.log 2 G < B m + 1 := by have := Nat.log_mono_right (b := 2) hGm; unfold B; omega
  rw [Fintype.sum_prod_type]
  simp only [satA]
  rw [Finset.sum_eq_single ⟨Nat.log 2 G, hlog⟩]
  · have hU0 : (0 : ℝ) < U (Nat.log 2 G) := by exact_mod_cast U_pos _
    have hGr : (0 : ℝ) < G := by exact_mod_cast hG
    have hterm : ∀ t : Fin (2 * m + 2),
        (if (Nat.log 2 G) = Nat.log 2 G ∧ G < (t : ℕ) ∧ (t : ℕ) ≤ U (Nat.log 2 G)
          then Real.sqrt (U (Nat.log 2 G)) / G else 0)
        * (if (Nat.log 2 G) = Nat.log 2 G ∧ G < (t : ℕ) ∧ (t : ℕ) ≤ U (Nat.log 2 G)
          then Real.sqrt (U (Nat.log 2 G)) / G else 0)
        = (U (Nat.log 2 G) : ℝ) / (G * G)
          * (if G < (t : ℕ) ∧ (t : ℕ) ≤ U (Nat.log 2 G) then (1 : ℝ) else 0) := by
      intro t
      by_cases ht : G < (t : ℕ) ∧ (t : ℕ) ≤ U (Nat.log 2 G)
      · rw [if_pos ⟨rfl, ht⟩, if_pos ht, div_mul_div_comm, Real.mul_self_sqrt hU0.le, mul_one]
      · rw [if_neg (fun h => ht h.2), if_neg ht]; ring
    rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Finset.mul_sum,
      sum_ite_Ioc _ _ _ (U_le_two_mul_m (i := Nat.log 2 G) (by omega) (by omega))]
    have hU2 : (U (Nat.log 2 G) : ℝ) ≤ 2 * G := by
      have := U_lt_two_mul hG; exact_mod_cast this.le
    have hsub : (((U (Nat.log 2 G) - G : ℕ) : ℝ)) ≤ U (Nat.log 2 G) := by
      exact_mod_cast Nat.sub_le _ _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hU0, hGr, hU2, hsub]
  · intro i _ hi
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg (fun h => hi (Fin.ext h.1))]; ring
  · intro h; exact absurd (mem_univ _) h

/-- **The norm of `satA`.** -/
theorem satA_sq_le {G : ℕ} (hG : 1 ≤ G) (hGm : G ≤ m) :
    ∑ i, satA m G i * satA m G i ≤ 7 * lam m := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 := satA_bins_sq_le (m := m) hG hGm
  have h2 := satA_corr_sq_le (m := m) hG hGm
  have h3 : ∑ o : OrdIdx (kk m), satA m G (Sum.inr (Sum.inr o)) * satA m G (Sum.inr (Sum.inr o))
      ≤ kk m + 1 := ordB_sq_le _ _
  have h4 := kk_add_one_le m
  have h5 := two_le_lam m
  linarith

lemma satB_bins_sq_le {D : ℕ} (hD : 0 < D) (hDm : D ≤ m) :
    ∑ i : Fin (B m + 1), satB m D (Sum.inl i) * satB m D (Sum.inl i) ≤ 1 := by
  classical
  have hlog : Nat.log 2 D < B m + 1 := by have := Nat.log_mono_right (b := 2) hDm; unfold B; omega
  simp only [satB]
  rw [Finset.sum_eq_single ⟨Nat.log 2 D, hlog⟩]
  · rw [if_pos rfl]
    have hU0 : (0 : ℝ) < U (Nat.log 2 D) := by exact_mod_cast U_pos _
    have hDU : (D : ℝ) ≤ U (Nat.log 2 D) := by exact_mod_cast le_U_of_log_le le_rfl
    have : (D : ℝ) / U (Nat.log 2 D) ≤ 1 := by rw [div_le_one hU0]; exact hDU
    nlinarith [this, show (0 : ℝ) ≤ (D : ℝ) / U (Nat.log 2 D) by positivity]
  · intro i _ hi
    rw [if_neg (fun h => hi (Fin.ext h))]; ring
  · intro h; exact absurd (mem_univ _) h

lemma satB_corr_sq_le {D : ℕ} (_hD : 0 < D) (hDm : D ≤ m) :
    ∑ p : Fin (B m + 1) × Fin (2 * m + 2),
        satB m D (Sum.inr (Sum.inl p)) * satB m D (Sum.inr (Sum.inl p)) ≤ 1 := by
  classical
  have hlog : Nat.log 2 D < B m + 1 := by have := Nat.log_mono_right (b := 2) hDm; unfold B; omega
  rw [Fintype.sum_prod_type]
  simp only [satB]
  rw [Finset.sum_eq_single ⟨Nat.log 2 D, hlog⟩]
  · have hU0 : (0 : ℝ) < U (Nat.log 2 D) := by exact_mod_cast U_pos _
    have hterm : ∀ t : Fin (2 * m + 2),
        (if (Nat.log 2 D) = Nat.log 2 D ∧ 1 ≤ (t : ℕ) ∧ (t : ℕ) ≤ D
          then -(1 / Real.sqrt (U (Nat.log 2 D))) else 0)
        * (if (Nat.log 2 D) = Nat.log 2 D ∧ 1 ≤ (t : ℕ) ∧ (t : ℕ) ≤ D
          then -(1 / Real.sqrt (U (Nat.log 2 D))) else 0)
        = 1 / (U (Nat.log 2 D) : ℝ) * (if 0 < (t : ℕ) ∧ (t : ℕ) ≤ D then (1 : ℝ) else 0) := by
      intro t
      by_cases ht : 1 ≤ (t : ℕ) ∧ (t : ℕ) ≤ D
      · rw [if_pos ⟨rfl, ht⟩, if_pos ⟨ht.1, ht.2⟩, neg_mul_neg, div_mul_div_comm,
          Real.mul_self_sqrt hU0.le, mul_one, mul_one]
      · rw [if_neg (fun h => ht h.2), if_neg (fun h => ht ⟨h.1, h.2⟩)]; ring
    rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Finset.mul_sum,
      sum_ite_Ioc _ _ _ (by omega)]
    have hDU : ((D - 0 : ℕ) : ℝ) ≤ U (Nat.log 2 D) := by
      rw [Nat.sub_zero]; exact_mod_cast le_U_of_log_le le_rfl
    rw [one_div_mul_eq_div, div_le_one hU0]
    exact hDU
  · intro i _ hi
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg (fun h => hi (Fin.ext h.1))]; ring
  · intro h; exact absurd (mem_univ _) h

/-- **The norm of `satB`.** -/
theorem satB_sq_le {D : ℕ} (hD : 1 ≤ D) (hDm : D ≤ m) :
    ∑ i, satB m D i * satB m D i ≤ 3 * lam m := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 := satB_bins_sq_le (m := m) hD hDm
  have h2 := satB_corr_sq_le (m := m) hD hDm
  have h3 : ∑ o : OrdIdx (kk m), satB m D (Sum.inr (Sum.inr o)) * satB m D (Sum.inr (Sum.inr o))
      ≤ kk m + 1 := ordA_sq_le _ _
  have h4 := kk_add_one_le m
  have h5 := two_le_lam m
  linarith

/-- **The norm of `satBInf`.** -/
theorem satBInf_sq_le : ∑ i, satBInf m i * satBInf m i ≤ 3 * lam m := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [satBInf, mul_zero, Finset.sum_const_zero, zero_add]
  have h3 : ∑ o : OrdIdx (kk m), ordA (kk m) (B m + 1) o * ordA (kk m) (B m + 1) o
      ≤ kk m + 1 := ordA_sq_le _ _
  have h4 := kk_add_one_le m
  have h5 := two_le_lam m
  linarith

end MonoidProduct.Infix
