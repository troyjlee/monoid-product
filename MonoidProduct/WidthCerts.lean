import QuantumQueryComplexity.HasDual
import MonoidProduct.Width.Main
import MonoidProduct.Width.Product
import MonoidProduct.Width.IndexTwo
import MonoidProduct.Width.IndexK
import MonoidProduct.Capped.Width
set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Essential-width certificates, bundled

The essential-width development (`Width/*`, `Capped/Width.lean`) exposes
its dual as a bare existential (`exists_summary_dual_isCostLe`) and its
endpoints through `advPM`; this file bundles the same certificates as
`HasDual` — what the operational extraction
(`Quantum/WidthApplications.lean`) consumes:

* `hasDual_of_summary` — any order-independent incremental summary of
  essential width `≤ B`, at `16·√(n·B)`;
* `hasDual_prodFun_of_width` — the commutative-monoid product from any
  width bound;
* `hasDual_prodFun_card_monoid` — the aperiodic fallback `B = |M| - 1`
  (the elementary ideal-chain fallback);
* `hasDual_prodFun_capped` — the capped counter, `B = min{n, r·k}`
  (`thm:capped-counter-product`, upper half);
* `hasDual_prodFun_five_logb` — index two, `B < 5·log₂|M|` (`thm:index-two-width`);
* `hasDual_prodFun_bcw` — index `k`, `B ≤ 2⁶²(k+1)·t·log₂ t` at
  `t = max 2 ⌈log₂|M|⌉` (`thm:index-k-width`).

The `advPM` endpoints in `Width/*` and `Capped/*` are retained there
unchanged; each is weak duality on the corresponding certificate below.
The file lives downstream of both the width development and
`HasDual.lean`; no quantum import appears anywhere in this hierarchy.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Summary

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {O : Type} [Fintype O] [DecidableEq O]
variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- **The essential-width certificate, bundled**: any order-independent
incremental summary of essential width at most `B ≥ 1` has a dual of cost
`16·√(n·B)`. -/
theorem hasDual_of_summary (S : IncrementalSummary ι σ O Q)
    {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    HasDual S.out (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) := by
  obtain ⟨P, hP⟩ := exists_summary_dual_isCostLe S hB hwidth
  exact ⟨_, inferInstance, P, hP⟩

/-- **The essential-width certificate for every budget `B ≥ 0`**: width zero gives the zero
certificate at cost `0 ≤ 16·√(n·B)`; positive budgets use the scan engine. -/
theorem hasDual_of_summary_nonneg (S : IncrementalSummary ι σ O Q) {B : ℕ}
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    HasDual S.out (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · exact (hasDual_const (S.out_const_of_width_zero hwidth)).mono (by positivity)
  · exact hasDual_of_summary S hB hwidth

/-- **The weighted essential-width certificate for every budget `B ≥ 0`**: with positive
coordinate costs `c`, a weighted dual of cost `16·√B·‖c‖`.  At `B = 0` the budget is `0` and
the certificate is the zero pair; no `1/√B` is formed there. -/
theorem hasWeightedDual_of_summary_nonneg (S : IncrementalSummary ι σ O Q) {B : ℕ}
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    HasWeightedDual S.out c (16 * (Real.sqrt B * costNorm c)) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, mul_zero]
    exact hasWeightedDual_const (S.out_const_of_width_zero hwidth)
  · obtain ⟨P, hP⟩ := exists_summary_dual_isWeightedCostLe S hB hwidth c hc
    exact hasWeightedDual_of_dualPair P hP

/-- The weighted certificate at width zero, stated with the budget `0`. -/
theorem hasWeightedDual_of_summary_zero (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0) (c : ι → ℝ) :
    HasWeightedDual S.out c 0 :=
  hasWeightedDual_const (S.out_const_of_width_zero hwidth)

end Summary

section Product

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- **The width-transfer certificate** (`eq:comm-width`): any bound `B` on the
essential width of the subset product gives a dual at `16·√(n·B)`. -/
theorem hasDual_prodFun_of_width (m : σ → M) {B : ℕ} (hB : 0 < B)
    (hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ B) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) :=
  hasDual_of_summary (prodSummary (ι := ι) (σ := σ) m) hB hw

/-- The width-transfer certificate for every budget `B ≥ 0`. -/
theorem hasDual_prodFun_of_width_nonneg (m : σ → M) {B : ℕ}
    (hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ B) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) :=
  hasDual_of_summary_nonneg (prodSummary (ι := ι) (σ := σ) m) hw

/-- The adversary form of the width transfer for every budget `B ≥ 0`. -/
theorem advPM_prodFun_le_of_width_nonneg (m : σ → M) {B : ℕ}
    (hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ B) :
    advPM (fun x : ι → σ => ∏ i, m (x i)) ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) :=
  advPM_le_of_summary_nonneg (prodSummary (ι := ι) (σ := σ) m) hw

/-- **The aperiodic fallback certificate**: `B = |M| - 1`. -/
theorem hasDual_prodFun_card_monoid [IsAperiodicMonoid M]
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * ((Fintype.card M : ℝ) - 1))) := by
  have h := hasDual_prodFun_of_width (ι := ι) (σ := σ) m
    (B := Fintype.card M - 1) (by omega)
    (fun x T => card_prodEss_le_card_monoid m x T)
  have hcast : ((Fintype.card M - 1 : ℕ) : ℝ) = (Fintype.card M : ℝ) - 1 := by
    have : 1 ≤ Fintype.card M := by omega
    push_cast [Nat.cast_sub this]
    ring
  rwa [hcast] at h

/-- **The index-two certificate** (`thm:index-two-width`): `x³ = x²` puts the width
below `5·log₂|M|`. -/
theorem hasDual_prodFun_five_logb (hx3 : ∀ z : M, z ^ 3 = z ^ 2)
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (5 * Real.logb 2 (Fintype.card M)))) := by
  set L : ℝ := Real.logb 2 (Fintype.card M) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) (by positivity),
      Real.rpow_one]
    exact_mod_cast hM
  set B₀ : ℕ := Nat.floor (5 * L) with hB₀
  have hB₀pos : 0 < B₀ := by
    have h5 : (5 : ℕ) ≤ B₀ := Nat.le_floor (by push_cast; linarith)
    omega
  have hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ B₀ := by
    intro x T
    exact Nat.le_floor (le_of_lt (card_prodEss_lt_five_logb hx3 m x T hM))
  refine (hasDual_prodFun_of_width (ι := ι) (σ := σ) m hB₀pos hw).mono ?_
  have hmono : (Fintype.card ι : ℝ) * B₀ ≤ (Fintype.card ι : ℝ) * (5 * L) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact Nat.floor_le (by linarith)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)

/-- **The index-k certificate** (`thm:index-k-width`): `w^{k+1} = w^k` puts the
width below `2⁶²(k+1)·t·log₂ t` at `t = max 2 ⌈log₂|M|⌉`. -/
theorem hasDual_prodFun_bcw {k : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (m : σ → M) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M)))) := by
  have hc : (1 : ℝ) ≤ 2 ^ 62 * ((k : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have ht1 : (1 : ℝ) ≤ (bcwT M : ℝ) := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2).trans (two_le_bcwT M)
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 (bcwT M) := one_le_logb_bcwT M
  have hR1 : (1 : ℝ)
      ≤ 2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M) := by
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ 2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M) := by
          gcongr
  set B₀ : ℕ := Nat.floor
    (2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M)) with hB₀
  have hB₀pos : 0 < B₀ := by
    have h1 : (1 : ℕ) ≤ B₀ := Nat.le_floor (by exact_mod_cast hR1)
    omega
  have hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ B₀ :=
    fun x T => Nat.le_floor (card_prodEss_le_bcw hxk hk m x T)
  refine (hasDual_prodFun_of_width (ι := ι) (σ := σ) m hB₀pos hw).mono ?_
  have hmono : (Fintype.card ι : ℝ) * B₀
      ≤ (Fintype.card ι : ℝ)
          * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact Nat.floor_le (by linarith)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)

end Product

section Capped

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- **The capped-counter certificate** (`thm:capped-counter-product`, upper half):
`B = min{n, r·k}` where `r = |ρ|`. -/
theorem hasDual_prodFun_capped {k : ℕ} (hk : 0 < k) [Nonempty ρ]
    (m : σ → ρ → Capped k) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (min (Fintype.card ι) (Fintype.card ρ * k) : ℕ))) := by
  refine hasDual_prodFun_of_width m ?_ ?_
  · exact lt_min_iff.mpr ⟨Fintype.card_pos, Nat.mul_pos Fintype.card_pos hk⟩
  · intro x T
    exact le_min (Finset.card_le_univ _) (card_prodEss_le_capped m x T)

end Capped

end MonoidProduct
