import MonoidProduct.Aperiodic.CubeRoot.Exports
import QuantumQueryComplexity.Quantum.UniformHasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The carrier recurrence solved at every threshold `t ≥ 2`
(`monoid.tex`, `prop:ags-cuberoot-recurrence`, `eq:ags-cuberoot-recurrence-solved`)

The manuscript's proposition asserts, for **every** integer `t ≥ 2`,

  `C_N ≤ (N·L)^{O(t + (N/t² + 1)·log N)}`,

where `C_s` is the largest normalized cost `Q_{1/3}(Prod_{H,ℓ})/√ℓ` over aperiodic `H`
with `|H| ≤ s` and `1 ≤ ℓ ≤ n₀`, and `L = L(n₀)`.  `Main.lean`'s
`hasWordProdDualPoly_rec` solves the recurrence only at `t = cubeThreshold s`, the value
the proof of `thm:ags-cuberoot-size` then chooses.  The descent there never uses the
choice of `t` beyond `2 ≤ t`: the step `hasWordProdDualPoly_step` and the majorant
`step_cost_le_pow` are already stated for any `t ≥ 2`.  This file reruns the strong
induction with `t` free.

* `solvRec_hasWordProdDualPoly` — for every `t ≥ 2`, every finite aperiodic `M'` with
  `|M'| ≤ s` and `|M'| ≤ m` satisfies the alphabet-uniform contract at
  `(B^256)^(t + (m/t² + 1)·⌈log₂(s+2)⌉)`, `B = s·L(n₀)`;
* `solvRec_hasWordProdDualPoly_top` — the solved form at `m = s`;
* `solvRec_qQuery_le` — the quantum reading, i.e. the bound on `C_s` itself:
  for `1 ≤ ℓ ≤ n₀`,
  `Q_{1/3}(Prod_{H,ℓ}) ≤ 16384·(s·L(n₀))^{256·(t + (s/t² + 1)·⌈log₂(s+2)⌉)}·√ℓ`.

The exponent `t + (s/t² + 1)·⌈log₂(s+2)⌉` is the manuscript's
`t + (N/t² + 1)·log N` (floor division, and `⌈log₂(s+2)⌉ ≥ 1` in place of `log N`,
which vanishes at `N = 1`); the constant `O(·)` is `256`, and the `16384` is the
extraction constant `8192` doubled to absorb the additive `1`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open LocallyThin ApexAdapter

/-- **`prop:ags-cuberoot-recurrence`, solved, at every threshold `t ≥ 2`**: every finite
aperiodic monoid `M'` with `|M'| ≤ s` and `|M'| ≤ m` satisfies the alphabet-uniform
word-product contract at `(B^256)^(t + (m/t² + 1)·⌈log₂(s+2)⌉)`, `B = s·L(n₀)`.  This is
`hasWordProdDualPoly_rec` with `cubeThreshold s` replaced by an arbitrary `t ≥ 2`. -/
theorem solvRec_hasWordProdDualPoly (s n₀ t : ℕ) (hs : 1 ≤ s) (ht2 : 2 ≤ t) (m : ℕ) :
    ∀ (M' : Type) [Monoid M'] [Fintype M'] [DecidableEq M'] [IsAperiodicMonoid M'],
      Fintype.card M' ≤ s → Fintype.card M' ≤ m →
      HasWordProdDualPoly M' n₀
        ((assemblyBase s n₀ ^ 256) ^ (t + (m / t ^ 2 + 1) * Nat.clog 2 (s + 2))) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro M' _ _ _ _ hcs hcm
    have htsq : 4 ≤ t ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ t ^ 2 := Nat.pow_le_pow_left ht2 2
    by_cases hm : t ^ 2 ≤ m
    · -- the descent
      have hD1 : (1 : ℝ) ≤ (assemblyBase s n₀ ^ 256)
          ^ (t + ((m - t ^ 2) / t ^ 2 + 1) * Nat.clog 2 (s + 2)) :=
        one_le_pow₀ (one_le_assemblyBase_pow hs 256)
      have hDt : assemblyBase s n₀ ^ (130 * t)
          ≤ (assemblyBase s n₀ ^ 256)
            ^ (t + ((m - t ^ 2) / t ^ 2 + 1) * Nat.clog 2 (s + 2)) := by
        rw [← pow_mul]
        refine assemblyBase_pow_le_pow hs ?_
        refine le_trans (Nat.mul_le_mul_right _ (by norm_num : 130 ≤ 256)) ?_
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      have hquot : ∀ (k : Fin (PrincipalFactor.munnPackage M').count)
          (hc : ((PrincipalFactor.munnPackage M').coord k).IsProper),
          t < ((PrincipalFactor.munnPackage M').coord k).degree →
          HasWordProdDualPoly
            (ReesQuot (ReesQuot.apexIdeal
              ((PrincipalFactor.munnPackage M').coord k) hc)) n₀
            ((assemblyBase s n₀ ^ 256)
              ^ (t + ((m - t ^ 2) / t ^ 2 + 1) * Nat.clog 2 (s + 2))) := by
        intro k hc hdeg
        have hdrop := ReesQuot.card_reesQuot_add_sq_le
          ((PrincipalFactor.munnPackage M').coord k) hc hdeg
        have hcard0 : Fintype.card (ReesQuot (ReesQuot.apexIdeal
              ((PrincipalFactor.munnPackage M').coord k) hc))
            ≤ Fintype.card M' :=
          le_trans (Nat.le_add_right _ _) hdrop
        have hlt : m - t ^ 2 < m := Nat.sub_lt (by omega) (by omega)
        refine ih (m - t ^ 2) hlt _ (le_trans hcard0 hcs) ?_
        exact Nat.le_sub_of_add_le (le_trans hdrop hcm)
      have hstep := (PrincipalFactor.munnPackage M').hasWordProdDualPoly_step
        n₀ t ht2 hD1 hquot
      refine hstep.mono_cost (le_trans (step_cost_le_pow hs hcs ht2 hD1 hDt) ?_)
      rw [← pow_mul, ← pow_add, ← pow_mul]
      refine assemblyBase_pow_le_pow hs ?_
      have hexp : Nat.clog 2 (s + 2)
            + (t + ((m - t ^ 2) / t ^ 2 + 1) * Nat.clog 2 (s + 2))
          ≤ t + (m / t ^ 2 + 1) * Nat.clog 2 (s + 2) :=
        exponent_step (by omega) (le_of_eq (Nat.sub_add_cancel hm))
      calc 100 * Nat.clog 2 (s + 2)
            + 256 * (t + ((m - t ^ 2) / t ^ 2 + 1) * Nat.clog 2 (s + 2))
          ≤ 256 * Nat.clog 2 (s + 2)
            + 256 * (t + ((m - t ^ 2) / t ^ 2 + 1) * Nat.clog 2 (s + 2)) :=
            Nat.add_le_add_right (Nat.mul_le_mul_right _ (by norm_num)) _
        _ = 256 * (Nat.clog 2 (s + 2)
              + (t + ((m - t ^ 2) / t ^ 2 + 1) * Nat.clog 2 (s + 2))) := by ring
        _ ≤ 256 * (t + (m / t ^ 2 + 1) * Nat.clog 2 (s + 2)) :=
            Nat.mul_le_mul_left _ hexp
    · -- the base: a degree above the threshold would charge more than `m`
      have hD1 : (1 : ℝ) ≤ assemblyBase s n₀ ^ (256 * t) :=
        one_le_assemblyBase_pow hs _
      have hDt : assemblyBase s n₀ ^ (130 * t) ≤ assemblyBase s n₀ ^ (256 * t) :=
        assemblyBase_pow_le_pow hs (Nat.mul_le_mul_right _ (by norm_num))
      have hquot : ∀ (k : Fin (PrincipalFactor.munnPackage M').count)
          (hc : ((PrincipalFactor.munnPackage M').coord k).IsProper),
          t < ((PrincipalFactor.munnPackage M').coord k).degree →
          HasWordProdDualPoly
            (ReesQuot (ReesQuot.apexIdeal
              ((PrincipalFactor.munnPackage M').coord k) hc)) n₀
            (assemblyBase s n₀ ^ (256 * t)) := by
        intro k hc hdeg
        exfalso
        have hsq := ((PrincipalFactor.munnPackage M').coord k).degree_sq_le
        have hjc : (jClass M' ((PrincipalFactor.munnPackage M').coord k).apex).card
            ≤ Fintype.card M' := by
          calc (jClass M' ((PrincipalFactor.munnPackage M').coord k).apex).card
              ≤ Finset.univ.card := Finset.card_le_univ _
            _ = Fintype.card M' := Finset.card_univ
        have hlt : t ^ 2 < ((PrincipalFactor.munnPackage M').coord k).degree ^ 2 :=
          Nat.pow_lt_pow_left hdeg (by norm_num)
        exact hm (le_trans hlt.le (le_trans hsq (le_trans hjc hcm)))
      have hstep := (PrincipalFactor.munnPackage M').hasWordProdDualPoly_step
        n₀ t ht2 hD1 hquot
      refine hstep.mono_cost (le_trans (step_cost_le_pow hs hcs ht2 hD1 hDt) ?_)
      rw [← pow_add, ← pow_mul]
      refine assemblyBase_pow_le_pow hs ?_
      have h1 : Nat.clog 2 (s + 2) ≤ (m / t ^ 2 + 1) * Nat.clog 2 (s + 2) :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      calc 100 * Nat.clog 2 (s + 2) + 256 * t
          ≤ 256 * ((m / t ^ 2 + 1) * Nat.clog 2 (s + 2)) + 256 * t :=
            Nat.add_le_add_right
              (le_trans (Nat.mul_le_mul_right _ (by norm_num))
                (Nat.mul_le_mul_left _ h1)) _
        _ = 256 * (t + (m / t ^ 2 + 1) * Nat.clog 2 (s + 2)) := by ring

/-- **`eq:ags-cuberoot-recurrence-solved`, contract form, at every `t ≥ 2`**: every
finite aperiodic monoid of order at most `s` satisfies the alphabet-uniform contract at
`(s·L(n₀))^{256·(t + (s/t² + 1)·⌈log₂(s+2)⌉)}`. -/
theorem solvRec_hasWordProdDualPoly_top (s n₀ t : ℕ) (hs : 1 ≤ s) (ht : 2 ≤ t)
    (M' : Type) [Monoid M'] [Fintype M'] [DecidableEq M'] [IsAperiodicMonoid M']
    (hcs : Fintype.card M' ≤ s) :
    HasWordProdDualPoly M' n₀
      (assemblyBase s n₀ ^ (256 * (t + (s / t ^ 2 + 1) * Nat.clog 2 (s + 2)))) := by
  rw [pow_mul]
  exact solvRec_hasWordProdDualPoly s n₀ t hs ht s M' hcs hcs

/-- **`eq:ags-cuberoot-recurrence-solved`, the bound on `C_s`, at every `t ≥ 2`**: for
every finite aperiodic `H` with `|H| ≤ s`, every horizon `n₀` and every length
`1 ≤ ℓ ≤ n₀`,

  `Q_{1/3}(Prod_{H,ℓ}) ≤ 16384·(s·L(n₀))^{256·(t + (s/t² + 1)·⌈log₂(s+2)⌉)}·√ℓ`,

with `L = cubeLog` (`2 + ⌈log₂(n₀+2)⌉`).  Dividing by `√ℓ` and maximizing over `H` and
`ℓ` is the manuscript's `C_s ≤ (s·L)^{O(t + (s/t² + 1) log s)}`. -/
theorem solvRec_qQuery_le {s n₀ t ℓ : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t)
    (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ n₀)
    {H : Type} [Monoid H] [Fintype H] [DecidableEq H] [IsAperiodicMonoid H]
    (hcs : Fintype.card H ≤ s) :
    (qQuery (fun w : Fin ℓ → H => wordProd (id : H → H) w) (1 / 3) : ℝ)
      ≤ 16384 * ((s : ℝ) * cubeLog n₀)
          ^ (256 * (t + (s / t ^ 2 + 1) * Nat.clog 2 (s + 2))) * Real.sqrt ℓ := by
  have hne : Nonempty H := ⟨1⟩
  set D : ℝ := assemblyBase s n₀ ^ (256 * (t + (s / t ^ 2 + 1) * Nat.clog 2 (s + 2)))
    with hD
  have hcon := solvRec_hasWordProdDualPoly_top s n₀ t hs ht H hcs
  have hdual : HasDual (fun w : Fin ℓ → H => wordProd (id : H → H) w)
      (D * Real.sqrt (ℓ : ℝ)) := hcon.2 H id ℓ hℓ
  have hD1 : (1 : ℝ) ≤ D := one_le_assemblyBase_pow hs _
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (ℓ : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hℓ1)
  have hc0 : (0 : ℝ) ≤ D * Real.sqrt (ℓ : ℝ) := by positivity
  have hQ := qQueryOn_third_le_of_hasDualOn_uniform hdual.hasDualOn hc0
  have hprod : (1 : ℝ) ≤ D * Real.sqrt (ℓ : ℝ) := by nlinarith
  have hB : assemblyBase s n₀ = (s : ℝ) * cubeLog n₀ := rfl
  rw [← hB]
  calc (qQuery (fun w : Fin ℓ → H => wordProd (id : H → H) w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + D * Real.sqrt (ℓ : ℝ)) := hQ
    _ ≤ 8192 * (D * Real.sqrt (ℓ : ℝ) + D * Real.sqrt (ℓ : ℝ)) := by
        rw [uniformExtractionConstant]
        nlinarith
    _ = 16384 * D * Real.sqrt ℓ := by ring

end MonoidProduct
