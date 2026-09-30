import MonoidProduct.Aperiodic.Induction
import QuantumQueryComplexity.Quantum.UniformHasDual
import MonoidProduct.Quantum.OneHotApplications
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The AGS theorem, operationally (`thm:main-ags`)

`monoid.tex`, `thm:main-ags`: for a finite aperiodic monoid `M`, the product
`x₁ ⋯ xₙ` can be computed with `√n·(c·|M|^6·log^6(n|M|))^{D_J(M)}` quantum
queries (up to the `|M|·λ` product-assembly factor).  This file makes that
statement operational, in both oracle models, from the exact dual certificate
`hasDual_wordProd` (`Aperiodic/Induction.lean`) through the cardinality-free
uniform extraction `qQueryOn_third_le_of_hasDualOn_uniform`:

* **native** (transposition oracle), for `n ≤ N`:
  `Q_{1/3}(Prod_{M,n}) ≤ min{n, 8192·(1 + 2·|M|·agsStep N M^(D_J(M)+1)·√n)}`;
* **one-hot**: the same at `16384`, with the exact read-all cap `n`;
* **the paper's quasi-polynomial shape**, at `N = n`, with every constant
  explicit (`agsStep n M = 2^40·(|M|+1)^5·(⌈log₂(n+1)⌉+2)^2`):

      Q_{1/3}(Prod_{M,n}) ≤ √n·(2^54·(|M|+1)^6·(⌈log₂(n+1)⌉+2)^2)^(D_J(M)+1),

  and the same over the real logarithm with `(log₂(n+1)+3)^2`; one-hot at
  `2^55`.

Relative to the manuscript's display, the formal exponent is `D_J(M) + 1`
rather than `D_J(M)` (the manuscript absorbs the base case's `C₁ log n` into
the `D_J`-th power "for any nontrivial monoid"; here the base case is charged
one honest level), while the per-level base is *better*: `|M|^6·log^2` in
place of `|M|^6·log^6(n|M|)` — no amplification factor `λ` appears, every
test being an exact dual solution, and the `|M|·λ` assembly factor of the
manuscript is already absorbed.

This file sits outside the `QuantumQueryComplexity.Quantum` aggregate: it is an
application layer importing both the quantum model and the classical AGS
induction.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## The native model -/

section Native

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
variable {N n : ℕ}

lemma ags_cost_nonneg (N n : ℕ) :
    (0 : ℝ) ≤ 2 * ((Fintype.card M : ℝ)
      * (agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ))) := by
  have h1 : (1 : ℝ) ≤ agsStep N M := one_le_agsStep N M
  have h2 : (0 : ℝ) ≤ agsStep N M ^ (jDepth M + 1) := by positivity
  positivity

/-- **The AGS upper bound, operationally**: for `n ≤ N`,
`Q_{1/3}(Prod_{M,n}) ≤ 8192·(1 + 2·|M|·agsStep N M^(D_J(M)+1)·√n)`. -/
theorem ags_qQuery_upper (hn : n ≤ N) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 2 * ((Fintype.card M : ℝ)
            * (agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ)))) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_wordProd (id : M → M) N hn).hasDualOn (ags_cost_nonneg N n)

/-- **Reading every letter**: `Q_{1/3}(Prod_{M,n}) ≤ n`. -/
theorem ags_qQuery_upper_length :
    qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) ≤ n := by
  have h := qQueryOn_le_card
    (read := (id : (Fin n → M) → Fin n → M))
    (f := fun w => wordProd (id : M → M) w)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **`thm:main-ags`, operationally** (native model): for `n ≤ N`,

    Q_{1/3}(Prod_{M,n}) ≤ min{n, 8192·(1 + 2·|M|·agsStep N M^(D_J(M)+1)·√n)}. -/
theorem ags_qQuery_le_min (hn : n ≤ N) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (uniformExtractionConstant
          * (1 + 2 * ((Fintype.card M : ℝ)
            * (agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ))))) :=
  le_min (by exact_mod_cast ags_qQuery_upper_length) (ags_qQuery_upper hn)

end Native

/-! ## The one-hot model -/

section OneHot

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
variable {N n : ℕ}

/-- **The AGS upper bound in the one-hot model**, at a direct factor two. -/
theorem ags_oneHotQQuery_upper (hn : n ≤ N) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ 16384 * (1 + 2 * ((Fintype.card M : ℝ)
          * (agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ)))) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
    (ags_qQuery_upper (M := M) hn)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every letter, one-hot**: the exact cap `n`. -/
theorem ags_oneHotQQuery_upper_length :
    oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) ≤ n := by
  have h := oneHotQQuery_le_card (fun w : Fin n → M => wordProd id w)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **`thm:main-ags` in the one-hot model** — the paper's whole-element
value-oracle convention. -/
theorem ags_oneHotQQuery_le_min (hn : n ≤ N) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (16384 * (1 + 2 * ((Fintype.card M : ℝ)
          * (agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ))))) :=
  le_min (by exact_mod_cast ags_oneHotQQuery_upper_length)
    (ags_oneHotQQuery_upper hn)

end OneHot

/-! ## The paper's quasi-polynomial shape

Take `N = n`.  With `r = √n`, the read-all cap `Q ≤ r²` handles `r < 1`
(then `Q ≤ r`), and for `r ≥ 1` the additive `1` is absorbed into `r`; the
remaining prefactor `2·A·(|M|+1)` is then absorbed into the `(D_J+1)`-th
power of the per-level base. -/

section Presentation

/-- The pure absorption step. -/
lemma ags_absorb {A m S r Q : ℝ} (d : ℕ) (hA : 1 ≤ A) (hm : 0 ≤ m) (hS : 1 ≤ S)
    (hr : 0 ≤ r) (hQn : Q ≤ r ^ 2) (hQ : Q ≤ A * (1 + 2 * (m * (S ^ (d + 1) * r)))) :
    Q ≤ r * (2 * A * (m + 1) * S) ^ (d + 1) := by
  have hB1 : 1 ≤ 2 * A * (m + 1) := by nlinarith
  have hSd : 1 ≤ S ^ (d + 1) := one_le_pow₀ hS
  have hBd : 2 * A * (m + 1) ≤ (2 * A * (m + 1)) ^ (d + 1) :=
    le_self_pow₀ hB1 (by omega)
  have hpow : (2 * A * (m + 1) * S) ^ (d + 1)
      = (2 * A * (m + 1)) ^ (d + 1) * S ^ (d + 1) := mul_pow _ _ _
  have hge : 1 ≤ (2 * A * (m + 1) * S) ^ (d + 1) := by
    rw [hpow]; nlinarith
  rcases lt_or_ge r 1 with hr1 | hr1
  · calc Q ≤ r ^ 2 := hQn
      _ ≤ r := by nlinarith
      _ ≤ r * (2 * A * (m + 1) * S) ^ (d + 1) := by nlinarith
  · have h1 : A * (1 + 2 * (m * (S ^ (d + 1) * r)))
        ≤ r * (2 * A * (m + 1) * S ^ (d + 1)) := by
      have : 1 ≤ r * S ^ (d + 1) := by nlinarith
      nlinarith [mul_nonneg hm (mul_nonneg (by linarith : (0 : ℝ) ≤ S ^ (d + 1)) hr)]
    have h2 : 2 * A * (m + 1) * S ^ (d + 1) ≤ (2 * A * (m + 1) * S) ^ (d + 1) := by
      rw [hpow]; nlinarith
    calc Q ≤ _ := hQ
      _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hr

/-- The per-level base with the extraction prefactor absorbed:
`2·A·(|M|+1)·agsStep n M` for `A = 2^13` is `2^54·(|M|+1)^6·(⌈log₂(n+1)⌉+2)^2`. -/
lemma ags_base_eq (a : ℕ) (n : ℕ) (M : Type) [Fintype M] :
    2 * (2 : ℝ) ^ a * ((Fintype.card M : ℝ) + 1) * agsStep n M
      = 2 ^ (a + 41) * ((Fintype.card M : ℝ) + 1) ^ 6
          * ((Nat.clog 2 (n + 1) : ℝ) + 2) ^ 2 := by
  rw [agsStep, pow_add]; ring

/-- The ceiling logarithm against the real one. -/
lemma ags_clog_le_logb (n : ℕ) :
    (Nat.clog 2 (n + 1) : ℝ) ≤ Real.logb 2 ((n : ℝ) + 1) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hclog1 : 1 ≤ Nat.clog 2 (n + 1) := Nat.clog_pos (by norm_num) (by omega)
  have hlt : 2 ^ (Nat.clog 2 (n + 1) - 1) < n + 1 :=
    Nat.pow_pred_clog_lt_self (b := 2) (x := n + 1) (by norm_num) (by omega)
  have hlogb : ((Nat.clog 2 (n + 1) - 1 : ℕ) : ℝ) ≤ Real.logb 2 ((n : ℝ) + 1) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    have : ((2 : ℕ) ^ (Nat.clog 2 (n + 1) - 1) : ℝ) ≤ ((n : ℝ) + 1) := by
      exact_mod_cast hlt.le
    exact_mod_cast this
  have hcast : ((Nat.clog 2 (n + 1) - 1 : ℕ) : ℝ) = (Nat.clog 2 (n + 1) : ℝ) - 1 := by
    push_cast [Nat.cast_sub hclog1]; ring
  rw [hcast] at hlogb
  linarith

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
variable {n : ℕ}

/-- The generic presentation step: a min-bound with prefactor `2^a` gives the
quasi-polynomial shape with base `2^(a+41)·(|M|+1)^6·(⌈log₂(n+1)⌉+2)^2`. -/
lemma ags_display_of_le_min {Q : ℝ} (a : ℕ)
    (hQ : Q ≤ min (n : ℝ) ((2 : ℝ) ^ a * (1 + 2 * ((Fintype.card M : ℝ)
      * (agsStep n M ^ (jDepth M + 1) * Real.sqrt (n : ℝ)))))) :
    Q ≤ Real.sqrt (n : ℝ) * (2 ^ (a + 41) * ((Fintype.card M : ℝ) + 1) ^ 6
      * ((Nat.clog 2 (n + 1) : ℝ) + 2) ^ 2) ^ (jDepth M + 1) := by
  rw [← ags_base_eq]
  refine ags_absorb (jDepth M) (one_le_pow₀ (by norm_num)) (Nat.cast_nonneg _)
    (one_le_agsStep n M) (Real.sqrt_nonneg _) ?_ (hQ.trans (min_le_right _ _))
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  exact hQ.trans (min_le_left _ _)

/-- **`thm:main-ags` in the paper's quasi-polynomial shape** (native model,
every constant explicit):

    Q_{1/3}(Prod_{M,n}) ≤ √n·(2^54·(|M|+1)^6·(⌈log₂(n+1)⌉+2)^2)^(D_J(M)+1). -/
theorem ags_qQuery_le_display :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (2 ^ 54 * ((Fintype.card M : ℝ) + 1) ^ 6
          * ((Nat.clog 2 (n + 1) : ℝ) + 2) ^ 2) ^ (jDepth M + 1) := by
  have h := ags_qQuery_le_min (M := M) (N := n) le_rfl
  rw [show uniformExtractionConstant = (2 : ℝ) ^ 13 by
    norm_num [uniformExtractionConstant]] at h
  exact ags_display_of_le_min 13 h

/-- **`thm:main-ags` in the one-hot model**, quasi-polynomial shape:

    Q^{1-hot}_{1/3}(Prod_{M,n}) ≤ √n·(2^55·(|M|+1)^6·(⌈log₂(n+1)⌉+2)^2)^(D_J(M)+1). -/
theorem ags_oneHotQQuery_le_display :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (2 ^ 55 * ((Fintype.card M : ℝ) + 1) ^ 6
          * ((Nat.clog 2 (n + 1) : ℝ) + 2) ^ 2) ^ (jDepth M + 1) := by
  have h := ags_oneHotQQuery_le_min (M := M) (N := n) le_rfl
  rw [show (16384 : ℝ) = (2 : ℝ) ^ 14 by norm_num] at h
  exact ags_display_of_le_min 14 h

/-- Replacing the ceiling logarithm by the real one inside the base. -/
lemma ags_base_mono_logb (c : ℝ) (hc : 0 ≤ c) (n d : ℕ) (K : ℝ) :
    Real.sqrt (n : ℝ) * (c * K ^ 6 * ((Nat.clog 2 (n + 1) : ℝ) + 2) ^ 2) ^ d
      ≤ Real.sqrt (n : ℝ) * (c * K ^ 6 * (Real.logb 2 ((n : ℝ) + 1) + 3) ^ 2) ^ d := by
  have hL0 : (0 : ℝ) ≤ (Nat.clog 2 (n + 1) : ℝ) + 2 := by positivity
  have hL : (Nat.clog 2 (n + 1) : ℝ) + 2 ≤ Real.logb 2 ((n : ℝ) + 1) + 3 := by
    linarith [ags_clog_le_logb n]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ d)
    (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL 2) (by positivity)

/-- **`thm:main-ags` over the real logarithm** (native model):

    Q_{1/3}(Prod_{M,n}) ≤ √n·(2^54·(|M|+1)^6·(log₂(n+1)+3)^2)^(D_J(M)+1). -/
theorem ags_qQuery_le_display_logb :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (2 ^ 54 * ((Fintype.card M : ℝ) + 1) ^ 6
          * (Real.logb 2 ((n : ℝ) + 1) + 3) ^ 2) ^ (jDepth M + 1) :=
  ags_qQuery_le_display.trans (ags_base_mono_logb _ (by positivity) _ _ _)

/-- **`thm:main-ags` over the real logarithm, one-hot**:

    Q^{1-hot}_{1/3}(Prod_{M,n}) ≤ √n·(2^55·(|M|+1)^6·(log₂(n+1)+3)^2)^(D_J(M)+1). -/
theorem ags_oneHotQQuery_le_display_logb :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (2 ^ 55 * ((Fintype.card M : ℝ) + 1) ^ 6
          * (Real.logb 2 ((n : ℝ) + 1) + 3) ^ 2) ^ (jDepth M + 1) :=
  ags_oneHotQQuery_le_display.trans (ags_base_mono_logb _ (by positivity) _ _ _)

end Presentation

end MonoidProduct
