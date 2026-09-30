import MonoidProduct.Capped.LengthBreadth
import MonoidProduct.Quantum.AGSApplications
import QuantumQueryComplexity.Duality.Main
import QuantumQueryComplexity.Quantum.LowerBound.MainBool

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Quantum statements of the paper in their displayed forms

Two displayed statements, assembled from the library's bounds.

* `eq:capped-counter-size`, the size form of `eq:capped-counter-theta`.  The paper uses
  `k·r = (k/log₂(k+1))·log₂|M_{k,r}|` (`capped_mul_eq_size`) and restricts to the
  nonsaturated regime `k·r ≤ n`, where `min{n, k·r} = k·r`.  There

      √(n·(k/log₂(k+1))·log₂|M_{k,r}|)/72 ≤ Q_{1/3}(Prod_{M_{k,r},n})
        ≤ 139264·√(n·(k/log₂(k+1))·log₂|M_{k,r}|)

  (`cappedLen_qQuery_size`); `139264 = 17·8192` absorbs the additive `1` of
  `cappedLen_qQuery_theta`.
* `lem:ags-local-step`, both clauses.
  * The dual clause in one statement, with the paper's range `1 ≤ ℓ ≤ n₀` of recursive
    lengths and its constant `A_{n₀} = 2^40·(q+1)^5·(⌈log₂(n₀+1)⌉+2)^2 = agsStep n₀ M`:
    `hasDual_eqProd_localStep`.
  * The query clause: `qQuery_eqProd_localStep` with explicit constant
    `294912·A_{n₀}·(B+1)·√n`, and `qQuery_eqProd_localStep_paper` in the paper's shape
    `q^{c₀}·L(n₀)^{c₀}·(B+1)·√n`, `L(u) = 2 + log₂(u+2)`, at `c₀ = 37`.

**The query clause, operationally.**  A query hypothesis `Q_{1/3} ≤ B√ℓ` gives
`ADV± ≤ 36·B√ℓ` by the Boolean-output lower bound (`mul_advPMOn_le_qQueryOn_of_error_third`),
hence, by strong duality (`exists_dualPair_of_advPM_lt`), a dual solution of cost
`(36B+1)·√ℓ` for every `ℓ ≥ 1` (`hasDual_of_qQuery_third_lt`).  The dual clause then gives a
dual of cost `A_{n₀}·(36B+1)·√n` for the target, and uniform extraction
(`qQueryOn_third_le_of_hasDualOn_uniform`) returns
`Q_{1/3} ≤ 8192·(1 + A_{n₀}(36B+1)√n) ≤ 294912·A_{n₀}·(B+1)·√n`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## `eq:capped-counter-size` -/

section CappedSize

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ] {k : ℕ}

/-- `|M_{k,r}| = (k+1)^r`. -/
lemma card_cappedPow (k : ℕ) :
    Fintype.card (ρ → Capped k) = (k + 1) ^ Fintype.card ρ := by
  rw [Fintype.card_fun, show Fintype.card (Capped k) = k + 1 from Fintype.card_fin _]

/-- **The size identity** behind `eq:capped-counter-size`:
`k·r = (k/log₂(k+1))·log₂|M_{k,r}|`. -/
lemma capped_mul_eq_size (hk : 0 < k) :
    ((k * Fintype.card ρ : ℕ) : ℝ)
      = (k : ℝ) / Real.logb 2 ((k : ℝ) + 1)
          * Real.logb 2 (Fintype.card (ρ → Capped k) : ℝ) := by
  have hl : 0 < Real.logb 2 ((k : ℝ) + 1) :=
    Real.logb_pos (by norm_num) (by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith)
  rw [card_cappedPow, Nat.cast_pow, Real.logb_pow]
  push_cast
  field_simp

/-- **`eq:capped-counter-size`**: in the nonsaturated regime `k·r ≤ n`,

    √(n·(k/log₂(k+1))·log₂|M_{k,r}|)/72 ≤ Q_{1/3}(Prod_{M_{k,r},n})
      ≤ 139264·√(n·(k/log₂(k+1))·log₂|M_{k,r}|),

with `|M_{k,r}| = (k+1)^r` the cardinality of the monoid `ρ → Capped k`. -/
theorem cappedLen_qQuery_size (hk : 0 < k) [Nonempty ρ] {n : ℕ}
    (hkr : k * Fintype.card ρ ≤ n) :
    Real.sqrt ((n : ℝ) * ((k : ℝ) / Real.logb 2 ((k : ℝ) + 1)
          * Real.logb 2 (Fintype.card (ρ → Capped k) : ℝ))) / 72
        ≤ (qQuery (fun x : Fin n → (ρ → Capped k) => ∏ i, x i) (1 / 3) : ℝ)
      ∧ (qQuery (fun x : Fin n → (ρ → Capped k) => ∏ i, x i) (1 / 3) : ℝ)
        ≤ 139264 * Real.sqrt ((n : ℝ) * ((k : ℝ) / Real.logb 2 ((k : ℝ) + 1)
          * Real.logb 2 (Fintype.card (ρ → Capped k) : ℝ))) := by
  have hr : 1 ≤ Fintype.card ρ := Fintype.card_pos
  have hkr1 : 1 ≤ k * Fintype.card ρ := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  have hn : 1 ≤ n := hkr1.trans hkr
  have hmin : min n (Fintype.card ρ * k) = k * Fintype.card ρ := by
    rw [Nat.mul_comm]; exact min_eq_right hkr
  have hX : (((n * min n (Fintype.card ρ * k)) : ℕ) : ℝ)
      = (n : ℝ) * ((k : ℝ) / Real.logb 2 ((k : ℝ) + 1)
          * Real.logb 2 (Fintype.card (ρ → Capped k) : ℝ)) := by
    rw [hmin, ← capped_mul_eq_size hk]; push_cast; ring
  have hX' : (n : ℝ) * ((min n (Fintype.card ρ * k) : ℕ) : ℝ)
      = (n : ℝ) * ((k : ℝ) / Real.logb 2 ((k : ℝ) + 1)
          * Real.logb 2 (Fintype.card (ρ → Capped k) : ℝ)) := by
    rw [← hX]; push_cast; ring
  obtain ⟨hlo, hup⟩ := cappedLen_qQuery_theta (ρ := ρ) hk hn
  rw [hX] at hlo
  rw [hX'] at hup
  refine ⟨hlo, ?_⟩
  set S := Real.sqrt ((n : ℝ) * ((k : ℝ) / Real.logb 2 ((k : ℝ) + 1)
          * Real.logb 2 (Fintype.card (ρ → Capped k) : ℝ))) with hS
  have hS1 : 1 ≤ S := by
    rw [hS, ← hX]
    have h1 : (1 : ℝ) ≤ (((n * min n (Fintype.card ρ * k)) : ℕ) : ℝ) := by
      rw [hmin]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at this
  have h := hup.trans (min_le_right _ _)
  rw [show uniformExtractionConstant = 8192 from rfl] at h
  linarith

end CappedSize

/-! ## `lem:ags-local-step` -/

section LocalStep

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **From a query bound to a dual solution**: `Q_{1/3}(g) ≤ T` and `36·T < c` give a
dual solution of cost `c` for a Boolean `g` (the Boolean-output lower bound
`ADV± ≤ 36·Q_{1/3}`, then strong duality). -/
theorem hasDual_of_qQuery_third_lt {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty σ]
    {g : (ι → σ) → Bool} {T c : ℝ} (hQ : (qQuery g (1 / 3) : ℝ) ≤ T) (hc : 36 * T < c) :
    HasDual g c := by
  have h := mul_advPMOn_le_qQueryOn_of_error_third
    (read := (id : (ι → σ) → ι → σ)) (f := g)
    (fun x y hxy => by rw [show x = y from hxy])
  replace h : (1 / 36 : ℝ) * advPM g ≤ (qQuery g (1 / 3) : ℝ) := h
  obtain ⟨m, P, hP⟩ := exists_dualPair_of_advPM_lt (g := g) (c := c) (by linarith)
  exact ⟨Fin m, inferInstance, P, hP⟩

/-- **`lem:ags-local-step`, dual clause**, as displayed: let `m ≠ 1`, `n₀ ≥ 1`, `B ≥ 1`,
and suppose that for every strict two-sided parent `s` (`MmM ⊊ MsM`) and every
`1 ≤ ℓ ≤ n₀` the test `P_s ∩ M^ℓ` has a dual of cost `B·√ℓ`.  Then for every
`1 ≤ n ≤ n₀`, the test `P_m ∩ M^n` has a dual of cost `A_{n₀}·B·√n`, where
`A_{n₀} = agsStep n₀ M = 2^40·(|M|+1)^5·(⌈log₂(n₀+1)⌉+2)^2`.  The letters are read through
an arbitrary map `letter : σ → M`; the paper's case is `letter = id`. -/
theorem hasDual_eqProd_localStep (letter : σ → M) {m : M} (hm : m ≠ 1) {n₀ : ℕ} {B : ℝ}
    (hB : 1 ≤ B)
    (hIH : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ n₀ →
      HasDual (eqProd (n := ℓ) letter s) (B * Real.sqrt (ℓ : ℝ)))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ n₀) :
    HasDual (eqProd (n := n) letter m) (agsStep n₀ M * B * Real.sqrt (n : ℝ)) := by
  have : Nonempty M := ⟨1⟩
  have hIH' : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ)) := by
    intro s hs len hlen
    rcases Nat.eq_zero_or_pos len with rfl | hpos
    · refine (hasDual_const fun x y => ?_).mono (by simp)
      rw [Subsingleton.elim x y]
    · exact hIH s hs len hpos (hlen.trans hn)
  refine (hasDual_eqProd_step_strict letter hm (by linarith) hIH').mono ?_
  have h := stepBound_le M hn1 hn hB
  linarith [show B * agsStep n₀ M * Real.sqrt (n : ℝ)
    = agsStep n₀ M * B * Real.sqrt (n : ℝ) by ring]

/-- **`lem:ags-local-step`, query clause, explicit constant**: let `m ≠ 1`, `n₀ ≥ 1`,
`B ≥ 0`, and suppose that for every strict two-sided parent `s` (`MmM ⊊ MsM`) and every
`1 ≤ ℓ ≤ n₀`, `Q_{1/3}(P_s ∩ M^ℓ) ≤ B·√ℓ`.  Then for every `1 ≤ n ≤ n₀`,

    Q_{1/3}(P_m ∩ M^n) ≤ 294912·A_{n₀}·(B+1)·√n,

`A_{n₀} = agsStep n₀ M = 2^40·(|M|+1)^5·(⌈log₂(n₀+1)⌉+2)^2`, `294912 = 36·8192`.  The
hypotheses are converted to duals of cost `(36B+1)·√ℓ`, and the conclusion extracted
uniformly (see the module docstring). -/
theorem qQuery_eqProd_localStep [Nonempty σ] (letter : σ → M) {m : M} (hm : m ≠ 1)
    {n₀ : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ n₀ →
      (qQuery (fun x : Fin ℓ → σ => eqProd letter s x) (1 / 3) : ℝ)
        ≤ B * Real.sqrt (ℓ : ℝ))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ n₀) :
    (qQuery (fun x : Fin n → σ => eqProd letter m x) (1 / 3) : ℝ)
      ≤ 294912 * agsStep n₀ M * (B + 1) * Real.sqrt (n : ℝ) := by
  have hD : HasDual (eqProd (n := n) letter m)
      (agsStep n₀ M * (36 * B + 1) * Real.sqrt (n : ℝ)) := by
    refine hasDual_eqProd_localStep letter hm (by linarith) ?_ hn1 hn
    intro s hs ℓ hℓ1 hℓ
    have hsq : 0 < Real.sqrt (ℓ : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hℓ1)
    exact hasDual_of_qQuery_third_lt (hQ s hs ℓ hℓ1 hℓ) (by nlinarith)
  have hA : 1 ≤ agsStep n₀ M := one_le_agsStep n₀ M
  have hR : 1 ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn1)
    rwa [Real.sqrt_one] at h
  have hAR : 1 ≤ agsStep n₀ M * Real.sqrt (n : ℝ) := by nlinarith
  have hu := qQueryOn_third_le_of_hasDualOn_uniform hD.hasDualOn (by positivity)
  change (qQuery (fun x : Fin n → σ => eqProd letter m x) (1 / 3) : ℝ) ≤ _ at hu
  rw [show uniformExtractionConstant = 8192 from rfl] at hu
  have e : 294912 * agsStep n₀ M * (B + 1) * Real.sqrt (n : ℝ)
      = 8192 * (agsStep n₀ M * Real.sqrt (n : ℝ)) * (36 * B + 36) := by ring
  have e' : 8192 * (1 + agsStep n₀ M * (36 * B + 1) * Real.sqrt (n : ℝ))
      = 8192 * (1 + (agsStep n₀ M * Real.sqrt (n : ℝ)) * (36 * B + 1)) := by ring
  rw [e]
  rw [e'] at hu
  nlinarith

/-- The constant chase for the paper's shape: for `q ≥ 2` and `L ≥ 2`,
`294912·2^40·(q+1)^5·H^2 ≤ q^37·L^37` whenever `0 ≤ H ≤ 2L`. -/
lemma localStep_const_le {q L H : ℝ} (hq : 2 ≤ q) (hL : 2 ≤ L) (hH0 : 0 ≤ H)
    (hH : H ≤ 2 * L) :
    294912 * (2 ^ 40 * (q + 1) ^ 5 * H ^ 2) ≤ q ^ 37 * L ^ 37 := by
  have hq0 : 0 ≤ q := by linarith
  have hL0 : 0 ≤ L := by linarith
  have h1 : (q + 1) ^ 5 ≤ (2 * q) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
  have h2 : H ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hH0 hH 2
  have h3 : (2 : ℝ) ^ 32 ≤ q ^ 32 := pow_le_pow_left₀ (by norm_num) hq 32
  have h4 : (2 : ℝ) ^ 35 ≤ L ^ 35 := pow_le_pow_left₀ (by norm_num) hL 35
  have hq5 : 0 ≤ q ^ 5 := by positivity
  have hL2 : 0 ≤ L ^ 2 := by positivity
  calc 294912 * (2 ^ 40 * (q + 1) ^ 5 * H ^ 2)
      ≤ 294912 * (2 ^ 40 * (2 * q) ^ 5 * (2 * L) ^ 2) := by gcongr
    _ = 9 * 2 ^ 62 * (q ^ 5 * L ^ 2) := by ring
    _ ≤ (2 ^ 32 * 2 ^ 35) * (q ^ 5 * L ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); norm_num
    _ ≤ (q ^ 32 * L ^ 35) * (q ^ 5 * L ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = q ^ 37 * L ^ 37 := by ring

/-- **`lem:ags-local-step`, query clause, in the paper's shape** with `c₀ = 37`: under the
hypotheses of `qQuery_eqProd_localStep`, for every `1 ≤ n ≤ n₀`,

    Q_{1/3}(P_m ∩ M^n) ≤ q^37·L(n₀)^37·(B+1)·√n,   q = |M|,  L(u) = 2 + log₂(u+2). -/
theorem qQuery_eqProd_localStep_paper [Nonempty σ] (letter : σ → M) {m : M} (hm : m ≠ 1)
    {n₀ : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ n₀ →
      (qQuery (fun x : Fin ℓ → σ => eqProd letter s x) (1 / 3) : ℝ)
        ≤ B * Real.sqrt (ℓ : ℝ))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ n₀) :
    (qQuery (fun x : Fin n → σ => eqProd letter m x) (1 / 3) : ℝ)
      ≤ (Fintype.card M : ℝ) ^ 37 * (2 + Real.logb 2 ((n₀ : ℝ) + 2)) ^ 37
          * (B + 1) * Real.sqrt (n : ℝ) := by
  refine (qQuery_eqProd_localStep letter hm hB hQ hn1 hn).trans ?_
  have : Nontrivial M := ⟨⟨m, 1, hm⟩⟩
  have hq : (2 : ℝ) ≤ (Fintype.card M : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card M)
  have hlog1 : Real.logb 2 ((n₀ : ℝ) + 1) ≤ Real.logb 2 ((n₀ : ℝ) + 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.logb 2 ((n₀ : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)])
  have hH : (Nat.clog 2 (n₀ + 1) : ℝ) + 2 ≤ 2 * (2 + Real.logb 2 ((n₀ : ℝ) + 2)) := by
    linarith [ags_clog_le_logb n₀]
  have hc := localStep_const_le hq (L := 2 + Real.logb 2 ((n₀ : ℝ) + 2)) (by linarith)
    (by positivity) hH
  have hBR : 0 ≤ (B + 1) * Real.sqrt (n : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_right hc hBR
  rw [agsStep]
  linarith [show 294912 * (2 ^ 40 * ((Fintype.card M : ℝ) + 1) ^ 5
      * ((Nat.clog 2 (n₀ + 1) : ℝ) + 2) ^ 2) * (B + 1) * Real.sqrt (n : ℝ)
    = 294912 * (2 ^ 40 * ((Fintype.card M : ℝ) + 1) ^ 5
      * ((Nat.clog 2 (n₀ + 1) : ℝ) + 2) ^ 2) * ((B + 1) * Real.sqrt (n : ℝ)) by ring,
    show (Fintype.card M : ℝ) ^ 37 * (2 + Real.logb 2 ((n₀ : ℝ) + 2)) ^ 37
      * (B + 1) * Real.sqrt (n : ℝ)
    = (Fintype.card M : ℝ) ^ 37 * (2 + Real.logb 2 ((n₀ : ℝ) + 2)) ^ 37
      * ((B + 1) * Real.sqrt (n : ℝ)) by ring]

end LocalStep

end MonoidProduct
