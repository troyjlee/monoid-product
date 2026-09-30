import MonoidProduct.Width.ProductSunflower
import Sunflower.RaoBCW

/-!
# The BCW fiber bound for product fibers

The adapter between `MonoidProduct.Width.ProductSunflower` and the
`tcs-formalizations-public` sunflower library:

* the local sunflower vocabulary is a verbatim mirror of `Sunflower.Defs`,
  so the bridge is definitional (`hasSunflower_iff`);
* the contrapositive of `Sunflower.rao_bcw_uniform` turns "product fibers
  contain no `(k+1)`-sunflower" (`lem:no-product-sunflower`) into the fiber
  cardinality bound `|fiber| < (2⁶⁰·(k+1)·lg t)^t`;
* combined with the fiber partition this bounds the binomial coefficient
  `C(B, t)` — the analytic input to `thm:index-k-width`;
* `lg` is `Real.logb 1.9` (the ALWZ convention); `lg_le_two_logb` converts
  the threshold into the base-2 convention of `monoid.tex` at the price of
  one factor `2`, i.e. `2⁶⁰ ↦ 2⁶¹`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open Finset

/-! ## The definitional bridge -/

/-- The local sunflower predicate is FAMOUS's, definitionally. -/
lemma hasSunflower_iff {α : Type*} [DecidableEq α] {r : ℕ}
    {𝓕 : Finset (Finset α)} :
    Sunflower.HasSunflower r 𝓕 ↔ HasSunflower r 𝓕 := Iff.rfl

/-! ## The fiber bound -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {M : Type*} [Fintype M] [DecidableEq M] [CommMonoid M]
variable (m : σ → M) (x : ι → σ) (T : Finset ι)

/-- Product fibers are `t`-uniform families. -/
lemma isUniform_prodFiber (z : M) (t : ℕ) :
    Sunflower.IsUniform t (prodFiber m x T z t) :=
  fun _ hS => ((mem_prodFiber m x T).mp hS).1.2

/-- **The BCW fiber-cardinality bound**: since a product fiber of an
index-`k` monoid contains no `(k+1)`-sunflower, `rao_bcw_uniform` caps its
size below `raoBound (2⁶⁰) (k+1) t = (2⁶⁰·(k+1)·lg t)^t`. -/
theorem card_prodFiber_lt_raoBound {k t : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (ht : 2 ≤ t) (z : M) :
    ((prodFiber m x T z t).card : ℝ)
      < Sunflower.raoBound (2 ^ 60) (k + 1) t := by
  by_contra hle
  push_neg at hle
  exact not_hasSunflower_prodFiber m x T hxk hk z t
    (hasSunflower_iff.mp
      (Sunflower.rao_bcw_uniform (by omega) ht
        (isUniform_prodFiber m x T z t) hle))

/-- **`C(B, t) ≤ |M| · (2⁶⁰·(k+1)·lg t)^t`** — the fiber partition times the
BCW fiber bound. -/
theorem choose_le_card_mul_raoBound {k t : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (ht : 2 ≤ t) :
    ((prodEss m x T).card.choose t : ℝ)
      ≤ (Fintype.card M : ℝ) * Sunflower.raoBound (2 ^ 60) (k + 1) t := by
  have h0 : (0 : ℝ) ≤ Sunflower.raoBound (2 ^ 60) (k + 1) t :=
    le_of_lt ((Nat.cast_nonneg _).trans_lt
      (card_prodFiber_lt_raoBound m x T hxk hk ht 1))
  have hF : ∀ z : M, (prodFiber m x T z t).card
      ≤ Nat.floor (Sunflower.raoBound (2 ^ 60) (k + 1) t) := fun z =>
    Nat.le_floor (le_of_lt (card_prodFiber_lt_raoBound m x T hxk hk ht z))
  calc ((prodEss m x T).card.choose t : ℝ)
      ≤ ((Fintype.card M
            * Nat.floor (Sunflower.raoBound (2 ^ 60) (k + 1) t) : ℕ) : ℝ) :=
        Nat.cast_le.mpr (choose_le_card_mul_of_fiber_card_le m x T hF)
    _ = (Fintype.card M : ℝ)
          * (Nat.floor (Sunflower.raoBound (2 ^ 60) (k + 1) t) : ℝ) := by
        push_cast; ring
    _ ≤ (Fintype.card M : ℝ) * Sunflower.raoBound (2 ^ 60) (k + 1) t := by
        have := Nat.floor_le h0
        gcongr

/-! ## Translation to the base-2 convention -/

/-- The ALWZ base-1.9 logarithm is within a factor `2` of `log₂` (because
`√2 ≤ 1.9`). -/
lemma lg_le_two_logb {x : ℝ} (hx : 1 ≤ x) :
    Sunflower.lg x ≤ 2 * Real.logb 2 x := by
  have hx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have h19 : (0 : ℝ) < Real.log 1.9 := Real.log_pos (by norm_num)
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have key : Real.log 2 ≤ 2 * Real.log 1.9 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≤ 1.9 ^ 2)
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  calc Sunflower.lg x = Real.log x / Real.log 1.9 := rfl
    _ ≤ Real.log x / (Real.log 2 / 2) := by
        apply div_le_div_of_nonneg_left hx0 (by linarith) (by linarith)
    _ = 2 * (Real.log x / Real.log 2) := by ring
    _ = 2 * Real.logb 2 x := rfl

/-- **The BCW threshold in the `monoid.tex` log convention**:
`(2⁶⁰·r·lg t)^t ≤ (2⁶¹·r·log₂ t)^t`. -/
lemma raoBound_le_pow_logb {r t : ℕ} (ht : 2 ≤ t) :
    Sunflower.raoBound (2 ^ 60) r t
      ≤ ((2 : ℝ) ^ 61 * r * Real.logb 2 t) ^ t := by
  have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
  have hlg0 : (0 : ℝ) ≤ Sunflower.lg t :=
    Real.logb_nonneg (by norm_num) h1
  have hlg := lg_le_two_logb h1
  calc Sunflower.raoBound (2 ^ 60) r t
      = ((2 : ℝ) ^ 60 * r * Sunflower.lg t) ^ t := rfl
    _ ≤ ((2 : ℝ) ^ 61 * r * Real.logb 2 t) ^ t := by
        refine pow_le_pow_left₀
          (mul_nonneg (by positivity) hlg0) ?_ t
        have h := mul_le_mul_of_nonneg_left hlg
          (mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 60)
            (Nat.cast_nonneg r))
        calc (2 : ℝ) ^ 60 * r * Sunflower.lg t
            ≤ (2 : ℝ) ^ 60 * r * (2 * Real.logb 2 t) := h
          _ = (2 : ℝ) ^ 61 * r * Real.logb 2 t := by ring

/-- **`C(B, t) ≤ |M| · (2⁶¹·(k+1)·log₂ t)^t`** — the fiber-partition bound in
the `monoid.tex` convention, ready for the `thm:index-k-width` endgame. -/
theorem choose_le_card_mul_pow_logb {k t : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (ht : 2 ≤ t) :
    ((prodEss m x T).card.choose t : ℝ)
      ≤ (Fintype.card M : ℝ)
          * ((2 : ℝ) ^ 61 * ((k : ℝ) + 1) * Real.logb 2 t) ^ t := by
  refine (choose_le_card_mul_raoBound m x T hxk hk ht).trans ?_
  have h := raoBound_le_pow_logb (r := k + 1) (t := t) ht
  push_cast at h
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

end MonoidProduct
