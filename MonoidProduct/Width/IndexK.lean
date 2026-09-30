import MonoidProduct.Width.RaoBCW
/-!
# The index-`k` width bound (`thm:index-k-width`)

The numeric endgame on top of the BCW fiber-partition bound
`C(B, t) ≤ |M| · (2⁶¹·(k+1)·log₂ t)^t` (`Width/RaoBCW.lean`):

* `pow_le_pow_mul_choose` — the binomial lower bound `(B/t)^t ≤ C(B,t)` in
  the root-free product form `B^t ≤ t^t · C(B,t)`, by the term-by-term
  comparison `B·(t-i) ≤ t·(B-i)`;
* evaluating at the scale `t = bcwT M = max 2 ⌈log₂|M|⌉` makes
  `|M| ≤ 2^t`, so both sides of the fiber-partition bound become `t`-th
  powers and the `t`-th root is `le_of_pow_le_pow_left₀` — no `rpow`;
* the headline `card_prodEss_le_bcw` :
  `κ ≤ 2⁶²·(k+1)·⌈log₂|M|⌉·log₂⌈log₂|M|⌉ = O(k·log|M|·loglog|M|)`,
  and the transfer `advPM_prodFun_le_bcw : ADV± ≤ 16·√(n·κ-bound)` via
  `eq:comm-width`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open Finset
open scoped Nat

/-! ## The binomial lower bound -/

/-- **`B^t ≤ t^t · C(B,t)`** — the standard `(B/t)^t ≤ C(B,t)` with the
division cleared.  Pairing the factorizations
`B^t · t ! = ∏ᵢ B·(t-i)` and `t^t · B·(B-1)⋯(B-t+1) = ∏ᵢ t·(B-i)`,
the factors compare term by term since `t ≤ B`. -/
lemma pow_le_pow_mul_choose {B t : ℕ} (h : t ≤ B) :
    B ^ t ≤ t ^ t * B.choose t := by
  have hdesc : B.choose t * t ! = B.descFactorial t := by
    rw [Nat.choose_eq_descFactorial_div_factorial,
      Nat.div_mul_cancel (Nat.factorial_dvd_descFactorial B t)]
  have hfac : t ! = ∏ i ∈ Finset.range t, (t - i) := by
    calc t ! = ∏ i ∈ Finset.range t, (i + 1) :=
          Nat.factorial_eq_prod_range_add_one t
      _ = ∏ i ∈ Finset.range t, (t - 1 - i + 1) :=
          (Finset.prod_range_reflect (fun i => i + 1) t).symm
      _ = ∏ i ∈ Finset.range t, (t - i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have := Finset.mem_range.mp hi
          omega
  have key : B ^ t * t ! ≤ t ^ t * B.descFactorial t := by
    have hBt : B ^ t = ∏ _i ∈ Finset.range t, B := by
      rw [Finset.prod_const, Finset.card_range]
    have htt : t ^ t = ∏ _i ∈ Finset.range t, t := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hBt, htt, hfac, Nat.descFactorial_eq_prod_range,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun i hi => ?_
    have hit : i < t := Finset.mem_range.mp hi
    have h1 : B * (t - i) + B * i = B * t := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hit.le]
    have h2 : t * (B - i) + t * i = t * B := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (hit.le.trans h)]
    have h3 : t * i ≤ B * i := Nat.mul_le_mul_right i h
    have h4 : B * t = t * B := Nat.mul_comm B t
    omega
  have hchain : B ^ t * t ! ≤ (t ^ t * B.choose t) * t ! := by
    calc B ^ t * t ! ≤ t ^ t * B.descFactorial t := key
      _ = t ^ t * (B.choose t * t !) := by rw [hdesc]
      _ = (t ^ t * B.choose t) * t ! := by ring
  exact Nat.le_of_mul_le_mul_right hchain (Nat.factorial_pos t)

/-! ## The evaluation scale -/

/-- The scale at which the BCW fiber bound is evaluated:
`max 2 ⌈log₂|M|⌉`.  The `max` handles tiny monoids and supplies the
`2 ≤ t` the sunflower theorem needs. -/
def bcwT (M : Type*) [Fintype M] : ℕ := max 2 (Nat.clog 2 (Fintype.card M))

lemma two_le_bcwT (M : Type*) [Fintype M] : 2 ≤ bcwT M := le_max_left _ _

lemma card_le_two_pow_bcwT (M : Type*) [Fintype M] :
    Fintype.card M ≤ 2 ^ bcwT M :=
  (Nat.le_pow_clog (by norm_num) _).trans
    (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

lemma one_le_logb_bcwT (M : Type*) [Fintype M] :
    (1 : ℝ) ≤ Real.logb 2 (bcwT M) := by
  calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
    _ ≤ Real.logb 2 (bcwT M) :=
        Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num)
          (by exact_mod_cast two_le_bcwT M)

/-! ## The index-`k` width bound -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {M : Type*} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- **The index-`k` width bound** (`thm:index-k-width`, BCW form):
for a commutative monoid of index `k`, the essential set of the subset
product has size `κ ≤ 2⁶²·(k+1)·t·log₂ t` at `t = max 2 ⌈log₂|M|⌉`, i.e.
`κ = O(k·log|M|·loglog|M|)`. -/
theorem card_prodEss_le_bcw {k : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k)
    (m : σ → M) (x : ι → σ) (T : Finset ι) :
    ((prodEss m x T).card : ℝ)
      ≤ 2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M) := by
  have ht2 : 2 ≤ bcwT M := two_le_bcwT M
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 (bcwT M) := one_le_logb_bcwT M
  have hlog0 : (0 : ℝ) ≤ Real.logb 2 (bcwT M) := zero_le_one.trans hlog1
  have hc : (1 : ℝ) ≤ 2 ^ 62 * ((k : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have ht0 : (0 : ℝ) ≤ (bcwT M : ℝ) := Nat.cast_nonneg _
  rcases lt_or_ge (prodEss m x T).card (bcwT M) with hBt | htB
  · calc ((prodEss m x T).card : ℝ)
        ≤ (bcwT M : ℝ) := by exact_mod_cast hBt.le
      _ = 1 * (bcwT M : ℝ) * 1 := by ring
      _ ≤ 2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M) := by
          gcongr
  · have hchoose : ((prodEss m x T).card : ℝ) ^ bcwT M
        ≤ (bcwT M : ℝ) ^ bcwT M
            * ((prodEss m x T).card.choose (bcwT M) : ℝ) := by
      exact_mod_cast pow_le_pow_mul_choose htB
    have hfiber := choose_le_card_mul_pow_logb m x T hxk hk ht2
    have hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ bcwT M := by
      exact_mod_cast card_le_two_pow_bcwT M
    have hchain : ((prodEss m x T).card : ℝ) ^ bcwT M
        ≤ (2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M))
            ^ bcwT M := by
      calc ((prodEss m x T).card : ℝ) ^ bcwT M
          ≤ (bcwT M : ℝ) ^ bcwT M
              * ((prodEss m x T).card.choose (bcwT M) : ℝ) := hchoose
        _ ≤ (bcwT M : ℝ) ^ bcwT M
              * ((Fintype.card M : ℝ)
                  * ((2 : ℝ) ^ 61 * ((k : ℝ) + 1)
                      * Real.logb 2 (bcwT M)) ^ bcwT M) := by
            gcongr
        _ ≤ (bcwT M : ℝ) ^ bcwT M
              * ((2 : ℝ) ^ bcwT M
                  * ((2 : ℝ) ^ 61 * ((k : ℝ) + 1)
                      * Real.logb 2 (bcwT M)) ^ bcwT M) := by
            have hbase : (0 : ℝ)
                ≤ (2 : ℝ) ^ 61 * ((k : ℝ) + 1) * Real.logb 2 (bcwT M) :=
              mul_nonneg (by positivity) hlog0
            gcongr
        _ = ((bcwT M : ℝ)
              * ((2 : ℝ)
                  * ((2 : ℝ) ^ 61 * ((k : ℝ) + 1)
                      * Real.logb 2 (bcwT M)))) ^ bcwT M := by
            rw [← mul_pow, ← mul_pow]
        _ = (2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M))
              ^ bcwT M := by
            congr 1
            ring
    refine le_of_pow_le_pow_left₀ (by omega) ?_ hchain
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (by positivity)) ht0) hlog0

/-- **`ADV±(∏ᵢ m(xᵢ)) ≤ 16·√(n · 2⁶²(k+1)·t·log₂ t)`** at
`t = max 2 ⌈log₂|M|⌉` — `thm:index-k-width` transferred through the essential-width
theorem (`eq:comm-width`). -/
theorem advPM_prodFun_le_bcw {k : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (m : σ → M) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M))) := by
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
  have h := advPM_prodFun_le_of_width (ι := ι) (σ := σ) m hB₀pos hw
  refine le_trans h ?_
  have hmono : (Fintype.card ι : ℝ) * B₀
      ≤ (Fintype.card ι : ℝ)
          * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact Nat.floor_le (by linarith)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)

end MonoidProduct
