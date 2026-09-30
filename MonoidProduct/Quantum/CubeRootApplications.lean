import MonoidProduct.Aperiodic.CubeRoot.Exports
import QuantumQueryComplexity.Quantum.UniformHasDual
import MonoidProduct.Quantum.OneHotApplications
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The cube-root theorem, operationally

The quantum endpoints of the cube-root development, in both oracle models:

* **native** (transposition oracle): for every finite aperiodic monoid,
  `Q_{1/3}(Prod_{M,n}) ≤ min{n, 8192·(1 + cubeRootDualCost 256 |M| n)}` —
  the cardinality-free uniform extraction on the cube-root dual, capped by
  exact read-all;
* **one-hot** (the canonical one-hot XOR oracle model, the paper's
  whole-element value-oracle convention): the same at `16384` and the same
  exact cap, a direct factor two;
* **semigroups**: the `WithOne` forms, visibly at length `n + 1`, cap
  `n + 1`, and carrier `|S| + 1`.  These carry `[Nonempty S]` — a semigroup
  need not be inhabited, and the extraction and read-all need a nonempty
  answer alphabet; the paper's semigroup convention is nonempty, so this is
  the clean public hypothesis.

Every `Q` is the native transposition-oracle complexity except in the
one-hot statements, which are the conventional-model exports.

This file is an application layer importing both the quantum model and the
classical cube-root development.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## The native model: finite aperiodic monoids -/

section Monoid

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
variable {n : ℕ}

/-- **The cube-root upper bound, operationally**:
`Q_{1/3}(Prod_{M,n}) ≤ 8192·(1 + cubeRootDualCost 256 |M| n)`. -/
theorem aperiodic_qQuery_upper :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + cubeRootDualCost 256 (Fintype.card M) n) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_wordProd_cubeRoot (id : M → M) n).hasDualOn
    (cubeRootDualCost_nonneg _ _ _)

/-- **Reading every letter**: `Q_{1/3}(Prod_{M,n}) ≤ n`. -/
theorem aperiodic_qQuery_upper_length :
    qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) ≤ n := by
  have h := qQueryOn_le_card
    (read := (id : (Fin n → M) → Fin n → M))
    (f := fun w => wordProd (id : M → M) w)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The cube-root theorem for finite aperiodic monoids, operationally**
(`thm:ags-cuberoot-size` in the paper, the aperiodic clause of the trichotomy
at cube-root precision):

    Q_{1/3}(Prod_{M,n}) ≤ min{n, 8192·(1 + √n·(|M|·L(n))^(256·cubeExponent |M|))}. -/
theorem aperiodic_qQuery_le_min :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (uniformExtractionConstant
          * (1 + cubeRootDualCost 256 (Fintype.card M) n)) :=
  le_min (by exact_mod_cast aperiodic_qQuery_upper_length) aperiodic_qQuery_upper

end Monoid

/-! ## The one-hot model: finite aperiodic monoids -/

section MonoidOneHot

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
variable {n : ℕ}

/-- **The cube-root upper bound in the one-hot model**, at a direct factor
two: `Q^{1-hot}_{1/3}(Prod_{M,n}) ≤ 16384·(1 + cubeRootDualCost 256 |M| n)`. -/
theorem aperiodic_oneHotQQuery_upper :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ 16384 * (1 + cubeRootDualCost 256 (Fintype.card M) n) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
    (aperiodic_qQuery_upper (M := M) (n := n))
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every letter, one-hot**: the exact cap `n`. -/
theorem aperiodic_oneHotQQuery_upper_length :
    oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) ≤ n := by
  have h := oneHotQQuery_le_card (fun w : Fin n → M => wordProd id w)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The cube-root theorem in the one-hot model** — the paper's
whole-element value-oracle convention. -/
theorem aperiodic_oneHotQQuery_le_min :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
          (16384 * (1 + cubeRootDualCost 256 (Fintype.card M) n)) :=
  le_min (by exact_mod_cast aperiodic_oneHotQQuery_upper_length)
    aperiodic_oneHotQQuery_upper

end MonoidOneHot

/-! ## Finite aperiodic semigroups: length `n + 1`, carrier `|S| + 1` -/

section Semigroup

variable {S : Type} [Semigroup S] [Fintype S] [DecidableEq S]
  [IsAperiodicSemigroup S] [Nonempty S]
variable {n : ℕ}

/-- **The cube-root upper bound for a finite aperiodic semigroup**:
`Q_{1/3}(semigroupProd n) ≤ 8192·(1 + cubeRootDualCost 256 (|S|+1) (n+1))`. -/
theorem aperiodic_semigroup_qQuery_upper :
    (qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + cubeRootDualCost 256 (Fintype.card S + 1) (n + 1)) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_semigroupProd_cubeRoot (id : S → S) n).hasDualOn
    (cubeRootDualCost_nonneg _ _ _)

/-- **Reading every letter**: the exact cap `n + 1`. -/
theorem aperiodic_semigroup_qQuery_upper_length :
    qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) ≤ n + 1 := by
  have h := qQueryOn_le_card
    (read := (id : (Fin (n + 1) → S) → Fin (n + 1) → S))
    (f := fun w => semigroupProd n w)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The cube-root theorem for finite aperiodic semigroups**, native model:
length `n + 1`, cap `n + 1`, carrier `|S| + 1`. -/
theorem aperiodic_semigroup_qQuery_le_min :
    (qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (uniformExtractionConstant
          * (1 + cubeRootDualCost 256 (Fintype.card S + 1) (n + 1))) :=
  le_min (by exact_mod_cast aperiodic_semigroup_qQuery_upper_length)
    aperiodic_semigroup_qQuery_upper

/-- **The one-hot semigroup upper bound**, at a direct factor two. -/
theorem aperiodic_semigroup_oneHotQQuery_upper :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ 16384 * (1 + cubeRootDualCost 256 (Fintype.card S + 1) (n + 1)) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
    (aperiodic_semigroup_qQuery_upper (S := S) (n := n))
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every letter, one-hot**: the exact cap `n + 1`. -/
theorem aperiodic_semigroup_oneHotQQuery_upper_length :
    oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3)
      ≤ n + 1 := by
  have h := oneHotQQuery_le_card (fun w : Fin (n + 1) → S => semigroupProd n w)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The cube-root theorem for finite aperiodic semigroups, one-hot** — the
paper-facing model and conventions. -/
theorem aperiodic_semigroup_oneHotQQuery_le_min :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ)
          (16384 * (1 + cubeRootDualCost 256 (Fintype.card S + 1) (n + 1))) :=
  le_min (by exact_mod_cast aperiodic_semigroup_oneHotQQuery_upper_length)
    aperiodic_semigroup_oneHotQQuery_upper

end Semigroup

/-! ## The paper-facing display

The paper's asymptotic form, at positive length (the exact and
min-with-read-all theorems above cover `n = 0`; the display below assumes
`1 ≤ n`, which its absorption uses):

    Q ≤ √n · (N·L(n))^(4096·(N·L(N))^(1/3)),

with `L = cubeLog` and one universal constant `4096`.  The real cube root
enters only here — the algebraic development is integer-exponent
throughout — and only through the two contained lemmas below. -/

section Presentation

/-- Cube roots without naming them: `x³ ≤ y` gives `x ≤ y^(1/3)`. -/
lemma le_rpow_inv_three_of_pow_le {x y : ℝ} (hx : 0 ≤ x)
    (h : x ^ (3 : ℕ) ≤ y) : x ≤ y ^ ((3 : ℝ)⁻¹) := by
  have h1 : (x ^ (3 : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) ≤ y ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) h (by norm_num)
  calc x = (x ^ (3 : ℕ)) ^ ((3 : ℝ)⁻¹) := by
        rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx,
          show ((3 : ℕ) : ℝ) * (3 : ℝ)⁻¹ = 1 by norm_num, Real.rpow_one]
    _ ≤ y ^ ((3 : ℝ)⁻¹) := h1

lemma rpow_inv_three_512 : ((512 : ℝ)) ^ ((3 : ℝ)⁻¹) = 8 := by
  rw [show (512 : ℝ) = 8 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast 8 3,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8),
    show ((3 : ℕ) : ℝ) * (3 : ℝ)⁻¹ = 1 by norm_num, Real.rpow_one]

/-- The layer count under the cube root: `cubeExponent N ≤ 8·(N·L(N))^(1/3)`. -/
lemma cubeExponent_le_rpow {N : ℕ} (hN : 1 ≤ N) :
    ((cubeExponent N : ℕ) : ℝ)
      ≤ 8 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) := by
  have hcube := cubeExponent_pow_le hN
  have hreal : ((cubeExponent N : ℕ) : ℝ) ^ (3 : ℕ)
      ≤ 512 * ((N * cubeLog N : ℕ) : ℝ) := by exact_mod_cast hcube
  have h1 := le_rpow_inv_three_of_pow_le (Nat.cast_nonneg _) hreal
  rwa [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _), rpow_inv_three_512] at h1

/-- **The absorption**: any `16384·(1 + cubeRootDualCost)` bound becomes the
paper's display at positive length. -/
theorem paper_display_of_le {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) {Q : ℝ}
    (hQ : Q ≤ 16384 * (1 + cubeRootDualCost 256 N n)) :
    Q ≤ Real.sqrt (n : ℝ) * (((N * cubeLog n : ℕ) : ℝ)
        ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
  have hBcast : ((N * cubeLog n : ℕ) : ℝ) = assemblyBase N n := by
    unfold assemblyBase
    push_cast
    ring
  have hB1 : (1 : ℝ) ≤ assemblyBase N n := one_le_assemblyBase hN
  have hsq : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hcost : cubeRootDualCost 256 N n
      = Real.sqrt (n : ℝ) * assemblyBase N n ^ (256 * cubeExponent N) :=
    cubeRootDualCost_eq 256 N n
  have hpow1 : (1 : ℝ) ≤ assemblyBase N n ^ (256 * cubeExponent N) :=
    one_le_assemblyBase_pow hN _
  have habs : 16384 * (1 + cubeRootDualCost 256 N n)
      ≤ Real.sqrt (n : ℝ) * assemblyBase N n ^ (256 * cubeExponent N + 15) := by
    rw [hcost]
    have h1 : (1 : ℝ)
        ≤ Real.sqrt (n : ℝ) * assemblyBase N n ^ (256 * cubeExponent N) := by
      nlinarith
    have h3 : (32768 : ℝ) ≤ assemblyBase N n ^ 15 :=
      numeral_le_assemblyBase_pow hN (by norm_num)
    have hnn : (0 : ℝ)
        ≤ Real.sqrt (n : ℝ) * assemblyBase N n ^ (256 * cubeExponent N) := by
      linarith
    calc 16384 * (1 + Real.sqrt (n : ℝ)
            * assemblyBase N n ^ (256 * cubeExponent N))
        ≤ 32768 * (Real.sqrt (n : ℝ)
            * assemblyBase N n ^ (256 * cubeExponent N)) := by nlinarith
      _ ≤ assemblyBase N n ^ 15 * (Real.sqrt (n : ℝ)
            * assemblyBase N n ^ (256 * cubeExponent N)) :=
          mul_le_mul_of_nonneg_right h3 hnn
      _ = Real.sqrt (n : ℝ)
            * assemblyBase N n ^ (256 * cubeExponent N + 15) := by
          rw [pow_add]
          ring
  have hy1 : (1 : ℝ) ≤ ((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) := by
    have hy : (1 : ℝ) ≤ ((N * cubeLog N : ℕ) : ℝ) := by
      have h3 := three_le_cubeLog N
      have : 1 * 1 ≤ N * cubeLog N := Nat.mul_le_mul hN (by omega)
      exact_mod_cast le_trans (by norm_num) this
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ)⁻¹) := (Real.one_rpow _).symm
      _ ≤ ((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by norm_num) hy (by norm_num)
  have hexp : ((256 * cubeExponent N + 15 : ℕ) : ℝ)
      ≤ 4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) := by
    have hce := cubeExponent_le_rpow hN
    have h2e : (2 : ℕ) ≤ cubeExponent N := two_le_cubeExponent N
    have h2e' : (2 : ℝ) ≤ ((cubeExponent N : ℕ) : ℝ) := by exact_mod_cast h2e
    have hE15 : ((256 * cubeExponent N + 15 : ℕ) : ℝ)
        ≤ 264 * ((cubeExponent N : ℕ) : ℝ) := by
      push_cast
      linarith
    calc ((256 * cubeExponent N + 15 : ℕ) : ℝ)
        ≤ 264 * ((cubeExponent N : ℕ) : ℝ) := hE15
      _ ≤ 264 * (8 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))) :=
          mul_le_mul_of_nonneg_left hce (by norm_num)
      _ = 2112 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) := by ring
      _ ≤ 4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) := by nlinarith
  have hrpow : assemblyBase N n ^ (256 * cubeExponent N + 15)
      ≤ assemblyBase N n
          ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))) := by
    rw [← Real.rpow_natCast (assemblyBase N n) (256 * cubeExponent N + 15)]
    exact Real.rpow_le_rpow_of_exponent_le hB1 hexp
  refine le_trans hQ (le_trans habs ?_)
  rw [hBcast]
  exact mul_le_mul_of_nonneg_left hrpow (Real.sqrt_nonneg _)

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **The paper display, native model** (`1 ≤ n`):
`Q_{1/3}(Prod_{M,n}) ≤ √n·(|M|·L(n))^(4096·(|M|·L(|M|))^(1/3))`. -/
theorem aperiodic_qQuery_paper {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (((Fintype.card M * cubeLog n : ℕ) : ℝ)
          ^ (4096 * (((Fintype.card M * cubeLog (Fintype.card M) : ℕ) : ℝ)
              ^ ((3 : ℝ)⁻¹)))) := by
  have hne : Nonempty M := ⟨1⟩
  refine paper_display_of_le Fintype.card_pos hn
    (le_trans aperiodic_qQuery_upper ?_)
  have hc := cubeRootDualCost_nonneg 256 (Fintype.card M) n
  have h16 : uniformExtractionConstant ≤ (16384 : ℝ) := by
    norm_num [uniformExtractionConstant]
  nlinarith

/-- **The paper display, one-hot model** — the paper's oracle convention. -/
theorem aperiodic_oneHotQQuery_paper {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (((Fintype.card M * cubeLog n : ℕ) : ℝ)
          ^ (4096 * (((Fintype.card M * cubeLog (Fintype.card M) : ℕ) : ℝ)
              ^ ((3 : ℝ)⁻¹)))) := by
  have hne : Nonempty M := ⟨1⟩
  exact paper_display_of_le Fintype.card_pos hn aperiodic_oneHotQQuery_upper

variable {S : Type} [Semigroup S] [Fintype S] [DecidableEq S]
  [IsAperiodicSemigroup S] [Nonempty S]

/-- **The paper display for finite aperiodic semigroups, one-hot** — the
paper's statement and model; positive length is automatic in the semigroup
convention. -/
theorem aperiodic_semigroup_oneHotQQuery_paper (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ Real.sqrt ((n + 1 : ℕ) : ℝ)
          * ((((Fintype.card S + 1) * cubeLog (n + 1) : ℕ) : ℝ)
          ^ (4096 * ((((Fintype.card S + 1) * cubeLog (Fintype.card S + 1) : ℕ) : ℝ)
              ^ ((3 : ℝ)⁻¹)))) :=
  paper_display_of_le (Nat.le_add_left 1 _) (Nat.le_add_left 1 n)
    aperiodic_semigroup_oneHotQQuery_upper

/-! ### The final display: separating the fixed exponential

The first step toward the paper's displayed bound `eq:ags-cuberoot-final`,
from the unabsorbed form by the paper's own case split: if `L(n)³ ≤ N` the
input is short and read-all gives `n ≤ √n·2^(N^(1/3))`; otherwise `N ≤ L(n)³` and the `N`-power
of the base is absorbed into the `L(n)`-power. -/

/-- **The read-all absorption**: the final display, with the fixed
exponential still separated, from the unabsorbed one. -/
theorem paper_display_final_of_le {N n : ℕ} (hN : 1 ≤ N) (_hn : 1 ≤ n) {Q : ℝ}
    (hQn : Q ≤ (n : ℝ))
    (hQ1 : Q ≤ Real.sqrt (n : ℝ) * (((N * cubeLog n : ℕ) : ℝ)
        ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))))) :
    Q ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
        * ((2 : ℝ) ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)))
          * ((cubeLog n : ℕ) : ℝ)
            ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
                * ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
  have hLn3 : (3 : ℝ) ≤ ((cubeLog n : ℕ) : ℝ) := by
    exact_mod_cast three_le_cubeLog n
  have hLn1 : (1 : ℝ) ≤ ((cubeLog n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN13 : (1 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ)⁻¹) := (Real.one_rpow _).symm
      _ ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by norm_num) hN1 (by norm_num)
  have hLN13 : (1 : ℝ) ≤ ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) := by
    have h3 : (1 : ℝ) ≤ ((cubeLog N : ℕ) : ℝ) := by
      have := three_le_cubeLog N
      exact_mod_cast by omega
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ)⁻¹) := (Real.one_rpow _).symm
      _ ≤ ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by norm_num) h3 (by norm_num)
  have hbig0 : (0 : ℝ) ≤ 16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
      * ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) := by linarith
    have h2 : (0 : ℝ) ≤ ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) := by linarith
    positivity
  have hLnPow1 : (1 : ℝ) ≤ ((cubeLog n : ℕ) : ℝ)
      ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
          * ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
          * ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) := (Real.one_rpow _).symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hLn1 hbig0
  have h2Pow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))) := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  refine le_min hQn ?_
  by_cases hcase : (cubeLog n) ^ 3 ≤ N
  · -- short input: read-all
    have hcLn13 : ((cubeLog n : ℕ) : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) := by
      refine le_rpow_inv_three_of_pow_le (Nat.cast_nonneg _) ?_
      exact_mod_cast hcase
    have hn2 : (n : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) ^ ((3 : ℝ)⁻¹)) := by
      have hnat : n ≤ 2 ^ cubeLog n := by
        have h1 : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by norm_num) _
        have h2 : (2 : ℕ) ^ Nat.clog 2 (n + 2) ≤ 2 ^ cubeLog n :=
          Nat.pow_le_pow_right (by norm_num) (by unfold cubeLog; omega)
        omega
      have hreal : (n : ℝ) ≤ (2 : ℝ) ^ (((cubeLog n : ℕ)) : ℝ) := by
        rw [Real.rpow_natCast]
        exact_mod_cast hnat
      exact le_trans hreal
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hcLn13)
    have hsqrtn : Real.sqrt (n : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) ^ ((3 : ℝ)⁻¹)) := by
      refine le_trans (Real.sqrt_le_sqrt hn2) ?_
      refine Real.sqrt_le_self_iff.2 (Or.inr ?_)
      calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
        _ ≤ (2 : ℝ) ^ ((N : ℝ) ^ ((3 : ℝ)⁻¹)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hQn' : Q ≤ Real.sqrt (n : ℝ) * ((2 : ℝ) ^ ((N : ℝ) ^ ((3 : ℝ)⁻¹))) := by
      calc Q ≤ (n : ℝ) := hQn
        _ = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
            (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
        _ ≤ Real.sqrt (n : ℝ) * ((2 : ℝ) ^ ((N : ℝ) ^ ((3 : ℝ)⁻¹))) :=
            mul_le_mul_of_nonneg_left hsqrtn (Real.sqrt_nonneg _)
    refine le_trans hQn' ?_
    have h2mono : (2 : ℝ) ^ ((N : ℝ) ^ ((3 : ℝ)⁻¹))
        ≤ (2 : ℝ) ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc (2 : ℝ) ^ ((N : ℝ) ^ ((3 : ℝ)⁻¹))
        ≤ (2 : ℝ) ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))) := h2mono
      _ ≤ (2 : ℝ) ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog n : ℕ) : ℝ)
              ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
                  * ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) :=
          le_mul_of_one_le_right (by linarith) hLnPow1
  · -- long input: absorb the `N`-power into the `L(n)`-power
    rw [not_le] at hcase
    have hNle : (N : ℝ) ≤ ((cubeLog n : ℕ) : ℝ) ^ (3 : ℕ) := by
      exact_mod_cast hcase.le
    have he0 : (0 : ℝ) ≤ 4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) := by
      have := Real.rpow_nonneg (Nat.cast_nonneg (N * cubeLog N)) ((3 : ℝ)⁻¹)
      positivity
    have hbase : (((N * cubeLog n : ℕ) : ℝ))
          ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
        ≤ ((cubeLog n : ℕ) : ℝ)
          ^ ((4 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
      have hsplit : (((N * cubeLog n : ℕ) : ℝ))
          = (N : ℝ) * ((cubeLog n : ℕ) : ℝ) := by push_cast; ring
      rw [hsplit, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      have h1 : (N : ℝ) ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
          ≤ (((cubeLog n : ℕ) : ℝ) ^ (3 : ℕ))
            ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hNle he0
      have h2 : (((cubeLog n : ℕ) : ℝ) ^ (3 : ℕ))
            ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
          = ((cubeLog n : ℕ) : ℝ)
            ^ ((3 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
        rw [← Real.rpow_natCast ((cubeLog n : ℕ) : ℝ) 3,
          ← Real.rpow_mul (Nat.cast_nonneg _)]
        norm_num
      have h3 : ((cubeLog n : ℕ) : ℝ)
            ^ ((3 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))))
            * ((cubeLog n : ℕ) : ℝ)
            ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
          = ((cubeLog n : ℕ) : ℝ)
            ^ ((4 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
        rw [← Real.rpow_add (by linarith : (0 : ℝ) < ((cubeLog n : ℕ) : ℝ))]
        ring_nf
      calc (N : ℝ) ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog n : ℕ) : ℝ)
              ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
          ≤ (((cubeLog n : ℕ) : ℝ) ^ (3 : ℕ))
              ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog n : ℕ) : ℝ)
              ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))) := by
            refine mul_le_mul_of_nonneg_right h1 ?_
            exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        _ = ((cubeLog n : ℕ) : ℝ)
              ^ ((4 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
            rw [h2, h3]
    have hexp : (4 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
        = 16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
            * ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) := by
      have hysplit : (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))
          = ((N : ℝ) ^ ((3 : ℝ)⁻¹))
              * (((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) := by
        rw [show ((N * cubeLog N : ℕ) : ℝ)
            = (N : ℝ) * ((cubeLog N : ℕ) : ℝ) by push_cast; ring,
          Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      rw [hysplit]
      ring
    calc Q ≤ Real.sqrt (n : ℝ) * (((N * cubeLog n : ℕ) : ℝ)
          ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := hQ1
      _ ≤ Real.sqrt (n : ℝ) * (((cubeLog n : ℕ) : ℝ)
            ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
                * ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          rw [← hexp]
          exact hbase
      _ ≤ Real.sqrt (n : ℝ) * ((2 : ℝ) ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog n : ℕ) : ℝ)
              ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
                  * ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          exact le_mul_of_one_le_left (by linarith) h2Pow1

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **The final display, separated form (`cubeLog`), native model**:
`Q_{1/3}(Prod_{M,n}) ≤ min{n, √n·2^(C·N^(1/3))·L(n)^(C·N^(1/3)·L(N)^(1/3))}`
at `C = 16384`, `N = |M|`, `1 ≤ n`. -/
theorem aperiodic_qQuery_final {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * ((2 : ℝ) ^ (16384 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog n : ℕ) : ℝ)
              ^ (16384 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹))
                  * ((cubeLog (Fintype.card M) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
  have hne : Nonempty M := ⟨1⟩
  exact paper_display_final_of_le Fintype.card_pos hn
    (by exact_mod_cast aperiodic_qQuery_upper_length)
    (aperiodic_qQuery_paper hn)

/-- **The final display, separated form (`cubeLog`), one-hot model** — the
paper's oracle convention. -/
theorem aperiodic_oneHotQQuery_final {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * ((2 : ℝ) ^ (16384 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog n : ℕ) : ℝ)
              ^ (16384 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹))
                  * ((cubeLog (Fintype.card M) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
  have hne : Nonempty M := ⟨1⟩
  exact paper_display_final_of_le Fintype.card_pos hn
    (by exact_mod_cast aperiodic_oneHotQQuery_upper_length)
    (aperiodic_oneHotQQuery_paper hn)

variable {S : Type} [Semigroup S] [Fintype S] [DecidableEq S]
  [IsAperiodicSemigroup S] [Nonempty S]

/-- **The final display for semigroups, separated form, one-hot** — `N = |S| + 1`,
as the paper's own remark takes it; positive length is automatic. -/
theorem aperiodic_semigroup_oneHotQQuery_final (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (Real.sqrt ((n + 1 : ℕ) : ℝ)
          * ((2 : ℝ) ^ (16384 * (((Fintype.card S + 1 : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog (n + 1) : ℕ) : ℝ)
              ^ (16384 * (((Fintype.card S + 1 : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))
                  * ((cubeLog (Fintype.card S + 1) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) :=
  paper_display_final_of_le (Nat.le_add_left 1 _) (Nat.le_add_left 1 n)
    (by exact_mod_cast aperiodic_semigroup_oneHotQQuery_upper_length)
    (aperiodic_semigroup_oneHotQQuery_paper n)

/-! ### The paper's logarithm, literally

The paper defines `L(n) = 2 + log₂(n+2)` with the *real* logarithm; the
endpoints above use `cubeLog n = 2 + ⌈log₂(n+2)⌉`.  The two are within a
factor two (`cubeLog_le_two_mul_paperLog`, from
`Nat.pow_pred_clog_lt_self`), so both displays transport to the
paper's `L` — the unabsorbed one verbatim at constant `16384`, the final
one in its separated form at `65536` (the paper's exact final form is the
next subsection). -/

/-- The paper's logarithmic factor, `L(n) = 2 + log₂(n + 2)` with the
real logarithm. -/
noncomputable def paperLog (n : ℕ) : ℝ := 2 + Real.logb 2 ((n : ℝ) + 2)

lemma three_le_paperLog (n : ℕ) : (3 : ℝ) ≤ paperLog n := by
  have h1 : (1 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    rw [Real.rpow_one]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  unfold paperLog
  linarith

/-- **The ceiling logarithm is within a factor two of the paper's**. -/
lemma cubeLog_le_two_mul_paperLog (n : ℕ) :
    ((cubeLog n : ℕ) : ℝ) ≤ 2 * paperLog n := by
  have hclog1 : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by norm_num) (by omega)
  have hlt : 2 ^ (Nat.clog 2 (n + 2) - 1) < n + 2 :=
    Nat.pow_pred_clog_lt_self (b := 2) (x := n + 2) (by norm_num) (by omega)
  have hlogb : ((Nat.clog 2 (n + 2) - 1 : ℕ) : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity),
      Real.rpow_natCast]
    have : ((2 : ℕ) ^ (Nat.clog 2 (n + 2) - 1) : ℝ) ≤ ((n : ℝ) + 2) := by
      exact_mod_cast hlt.le
    exact_mod_cast this
  have hcast : ((Nat.clog 2 (n + 2) - 1 : ℕ) : ℝ)
      = ((Nat.clog 2 (n + 2) : ℕ) : ℝ) - 1 := by
    push_cast [Nat.cast_sub hclog1]
    ring
  have hclogR : ((Nat.clog 2 (n + 2) : ℕ) : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) + 1 := by
    rw [hcast] at hlogb
    linarith
  have hL := three_le_paperLog n
  have hcube : ((cubeLog n : ℕ) : ℝ) = ((Nat.clog 2 (n + 2) : ℕ) : ℝ) + 2 := by
    unfold cubeLog
    push_cast
    ring
  -- cubeLog n ≤ logb + 3 = paperLog + 1 ≤ 2·paperLog since paperLog ≥ 1
  have : ((cubeLog n : ℕ) : ℝ) ≤ paperLog n + 1 := by
    rw [hcube]
    unfold paperLog
    linarith
  linarith

/-- **The unabsorbed display over the paper's real logarithm**
(`eq:ags-cuberoot-unabsorbed`, literally):
`Q ≤ √n·(N·L(n))^(16384·(N·L(N))^(1/3))`, `L(n) = 2 + log₂(n+2)`. -/
theorem paper_display_real_of_le {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) {Q : ℝ}
    (hQ : Q ≤ 16384 * (1 + cubeRootDualCost 256 N n)) :
    Q ≤ Real.sqrt (n : ℝ) * (((N : ℝ) * paperLog n)
        ^ (16384 * (((N : ℝ) * paperLog N) ^ ((3 : ℝ)⁻¹)))) := by
  have hbase := paper_display_of_le hN hn hQ
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpLn := three_le_paperLog n
  have hpLN := three_le_paperLog N
  have hbridge_n := cubeLog_le_two_mul_paperLog n
  have hbridge_N := cubeLog_le_two_mul_paperLog N
  -- the ℕ-cast bases and exponent arguments, in real form
  have hBn : ((N * cubeLog n : ℕ) : ℝ) ≤ ((N : ℝ) * paperLog n) ^ (2 : ℕ) := by
    have h1 : ((N * cubeLog n : ℕ) : ℝ) = (N : ℝ) * ((cubeLog n : ℕ) : ℝ) := by
      push_cast
      ring
    have h2 : (N : ℝ) * ((cubeLog n : ℕ) : ℝ) ≤ 2 * ((N : ℝ) * paperLog n) := by
      have := mul_le_mul_of_nonneg_left hbridge_n hN0
      nlinarith
    have h3 : (2 : ℝ) ≤ (N : ℝ) * paperLog n := by nlinarith
    have h4 : 2 * ((N : ℝ) * paperLog n) ≤ ((N : ℝ) * paperLog n) ^ (2 : ℕ) := by
      nlinarith
    linarith [h1 ▸ h2]
  have hexp0 : (0 : ℝ) ≤ 4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg (N * cubeLog N)) ((3 : ℝ)⁻¹)
    positivity
  -- swap the base, paying a factor two in the exponent
  have hswap : (((N * cubeLog n : ℕ) : ℝ))
        ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
      ≤ ((N : ℝ) * paperLog n)
        ^ ((2 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
    have h1 : (((N * cubeLog n : ℕ) : ℝ))
          ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
        ≤ (((N : ℝ) * paperLog n) ^ (2 : ℕ))
          ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hBn hexp0
    have h2 : (((N : ℝ) * paperLog n) ^ (2 : ℕ))
          ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
        = ((N : ℝ) * paperLog n)
          ^ ((2 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) := by
      rw [← Real.rpow_natCast ((N : ℝ) * paperLog n) 2,
        ← Real.rpow_mul (by nlinarith : (0 : ℝ) ≤ (N : ℝ) * paperLog n)]
      norm_num
    rw [← h2]
    exact h1
  -- enlarge the exponent argument to the real logarithm
  have hexparg : ((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)
      ≤ 2 * (((N : ℝ) * paperLog N) ^ ((3 : ℝ)⁻¹)) := by
    have h1 : ((N * cubeLog N : ℕ) : ℝ) ≤ 2 * ((N : ℝ) * paperLog N) := by
      have h2 : ((N * cubeLog N : ℕ) : ℝ) = (N : ℝ) * ((cubeLog N : ℕ) : ℝ) := by
        push_cast
        ring
      have := mul_le_mul_of_nonneg_left hbridge_N hN0
      nlinarith [h2]
    calc ((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)
        ≤ (2 * ((N : ℝ) * paperLog N)) ^ ((3 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by norm_num)
      _ = (2 : ℝ) ^ ((3 : ℝ)⁻¹) * (((N : ℝ) * paperLog N) ^ ((3 : ℝ)⁻¹)) :=
          Real.mul_rpow (by norm_num) (by nlinarith)
      _ ≤ 2 * (((N : ℝ) * paperLog N) ^ ((3 : ℝ)⁻¹)) := by
          have h2r : (2 : ℝ) ^ ((3 : ℝ)⁻¹) ≤ 2 := by
            calc (2 : ℝ) ^ ((3 : ℝ)⁻¹) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          have hnn : (0 : ℝ) ≤ ((N : ℝ) * paperLog N) ^ ((3 : ℝ)⁻¹) :=
            Real.rpow_nonneg (by nlinarith) _
          nlinarith
  have hexp : (2 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
      ≤ 16384 * (((N : ℝ) * paperLog N) ^ ((3 : ℝ)⁻¹)) := by nlinarith
  have hfinal : ((N : ℝ) * paperLog n)
        ^ ((2 : ℝ) * (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))))
      ≤ ((N : ℝ) * paperLog n)
        ^ (16384 * (((N : ℝ) * paperLog N) ^ ((3 : ℝ)⁻¹))) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith) hexp
  refine le_trans hbase ?_
  refine mul_le_mul_of_nonneg_left (le_trans hswap hfinal) (Real.sqrt_nonneg _)

/-- **The final display over the paper's real logarithm**, in the
separated form (the fixed exponential kept apart; `eq:ags-cuberoot-final`
itself is `paper_display_exact_of_final_real` below):
`Q ≤ min{n, √n·2^(65536·N^(1/3))·L(n)^(65536·N^(1/3)·L(N)^(1/3))}`. -/
theorem paper_display_final_real_of_le {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n)
    {Q : ℝ} (hQn : Q ≤ (n : ℝ))
    (hQ1 : Q ≤ Real.sqrt (n : ℝ) * (((N * cubeLog n : ℕ) : ℝ)
        ^ (4096 * (((N * cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))))) :
    Q ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
        * ((2 : ℝ) ^ (65536 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)))
          * paperLog n
            ^ (65536 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
                * paperLog N ^ ((3 : ℝ)⁻¹)))) := by
  have hclog := paper_display_final_of_le hN hn hQn hQ1
  refine le_min hQn ?_
  have h2 := le_trans hclog (min_le_right _ _)
  have hN13 : (1 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ)⁻¹) := (Real.one_rpow _).symm
      _ ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) (by norm_num)
  have hpLn := three_le_paperLog n
  have hpLN := three_le_paperLog N
  have hbridge_n := cubeLog_le_two_mul_paperLog n
  have hbridge_N := cubeLog_le_two_mul_paperLog N
  have hLn3 : (3 : ℝ) ≤ ((cubeLog n : ℕ) : ℝ) := by
    exact_mod_cast three_le_cubeLog n
  -- the old L(n)-power under paperLog, paying a factor two in the exponent
  set Eold : ℝ := 16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
      * ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) with hEold
  have hEold0 : (0 : ℝ) ≤ Eold := by
    have h1 : (0 : ℝ) ≤ ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [hEold]
    positivity
  have hLnP : ((cubeLog n : ℕ) : ℝ) ^ Eold ≤ paperLog n ^ (2 * Eold) := by
    have h1 : ((cubeLog n : ℕ) : ℝ) ≤ paperLog n ^ (2 : ℕ) := by nlinarith
    calc ((cubeLog n : ℕ) : ℝ) ^ Eold ≤ (paperLog n ^ (2 : ℕ)) ^ Eold :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 hEold0
      _ = paperLog n ^ (2 * Eold) := by
          rw [← Real.rpow_natCast (paperLog n) 2,
            ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ paperLog n)]
          norm_num
  -- the exponent under the real logarithm
  have hexparg : ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)
      ≤ 2 * (paperLog N ^ ((3 : ℝ)⁻¹)) := by
    calc ((cubeLog N : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)
        ≤ (2 * paperLog N) ^ ((3 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hbridge_N (by norm_num)
      _ = (2 : ℝ) ^ ((3 : ℝ)⁻¹) * (paperLog N ^ ((3 : ℝ)⁻¹)) :=
          Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 * (paperLog N ^ ((3 : ℝ)⁻¹)) := by
          have h2r : (2 : ℝ) ^ ((3 : ℝ)⁻¹) ≤ 2 := by
            calc (2 : ℝ) ^ ((3 : ℝ)⁻¹) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          have hnn : (0 : ℝ) ≤ paperLog N ^ ((3 : ℝ)⁻¹) :=
            Real.rpow_nonneg (by linarith) _
          nlinarith
  have hexp : 2 * Eold ≤ 65536 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
      * paperLog N ^ ((3 : ℝ)⁻¹) := by
    rw [hEold]
    nlinarith [hN13, Real.rpow_nonneg (Nat.cast_nonneg (cubeLog N)) ((3 : ℝ)⁻¹),
      Real.rpow_nonneg (show (0:ℝ) ≤ paperLog N by linarith) ((3 : ℝ)⁻¹)]
  have hLnfinal : ((cubeLog n : ℕ) : ℝ) ^ Eold
      ≤ paperLog n ^ (65536 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
          * paperLog N ^ ((3 : ℝ)⁻¹)) :=
    le_trans hLnP (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp)
  have h2pow : (2 : ℝ) ^ (16384 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)))
      ≤ (2 : ℝ) ^ (65536 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  refine le_trans h2 ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul h2pow hLnfinal
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_
  have := Real.rpow_nonneg (show (0:ℝ) ≤ (2:ℝ) by norm_num)
    (65536 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)))
  linarith

variable {M' : Type} [Monoid M'] [Fintype M'] [DecidableEq M']
  [IsAperiodicMonoid M']

/-- **`eq:ags-cuberoot-unabsorbed`, verbatim** — the paper's real
logarithm, native model, `1 ≤ n`, universal constant `16384`. -/
theorem aperiodic_qQuery_paper_real {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M' => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (((Fintype.card M' : ℝ) * paperLog n)
          ^ (16384 * (((Fintype.card M' : ℝ) * paperLog (Fintype.card M'))
              ^ ((3 : ℝ)⁻¹)))) := by
  have hne : Nonempty M' := ⟨1⟩
  refine paper_display_real_of_le Fintype.card_pos hn
    (le_trans aperiodic_qQuery_upper ?_)
  have hc := cubeRootDualCost_nonneg 256 (Fintype.card M') n
  have h16 : uniformExtractionConstant ≤ (16384 : ℝ) := by
    norm_num [uniformExtractionConstant]
  nlinarith

/-- **The final display, separated form** — the paper's real logarithm,
one-hot model (the paper's oracle convention), `1 ≤ n`, universal constant
`65536`; the paper's exact form is `aperiodic_oneHotQQuery_final_exact`. -/
theorem aperiodic_oneHotQQuery_final_real {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M' => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * ((2 : ℝ) ^ (65536 * ((Fintype.card M' : ℝ) ^ ((3 : ℝ)⁻¹)))
            * paperLog n
              ^ (65536 * ((Fintype.card M' : ℝ) ^ ((3 : ℝ)⁻¹))
                  * paperLog (Fintype.card M') ^ ((3 : ℝ)⁻¹)))) := by
  have hne : Nonempty M' := ⟨1⟩
  exact paper_display_final_real_of_le Fintype.card_pos hn
    (by exact_mod_cast aperiodic_oneHotQQuery_upper_length)
    (aperiodic_oneHotQQuery_paper hn)

variable {S' : Type} [Semigroup S'] [Fintype S'] [DecidableEq S']
  [IsAperiodicSemigroup S'] [Nonempty S']

/-- **The paper's semigroup remark, separated form**: the final display
with `N = |S| + 1`, one-hot, positive length automatic; the paper's exact form
is `aperiodic_semigroup_oneHotQQuery_final_exact`. -/
theorem aperiodic_semigroup_oneHotQQuery_final_real (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S' => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (Real.sqrt ((n + 1 : ℕ) : ℝ)
          * ((2 : ℝ) ^ (65536 * (((Fintype.card S' + 1 : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
            * paperLog (n + 1)
              ^ (65536 * (((Fintype.card S' + 1 : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))
                  * paperLog (Fintype.card S' + 1) ^ ((3 : ℝ)⁻¹)))) :=
  paper_display_final_real_of_le (Nat.le_add_left 1 _) (Nat.le_add_left 1 n)
    (by exact_mod_cast aperiodic_semigroup_oneHotQQuery_upper_length)
    (aperiodic_semigroup_oneHotQQuery_paper n)

/-! ### The paper's displays, exactly

The final display above still carries the fixed exponential `2^(C·N^(1/3))`
and the factor `L(N)^(1/3)` in the exponent.  The paper states

* `eq:ags-cuberoot-final`: `Q ≤ min{n, √n·L(n)^(C·(N·log(N+2))^(1/3))}`, and
* `res:aperiodic-size` (introduction): `Q ≤ min{n, √n·log^(C·(N·log(N+2))^(1/3))(n+2)}`,

with the natural logarithm.  Both follow by elementary absorption:
`2 ≤ L(n)` swallows the fixed exponential, `L(N) ≤ 8·ln(N+2)` gives
`L(N)^(1/3) ≤ 2·ln(N+2)^(1/3)` (constant `2^18`), and for the introduction's
base `L(n) ≤ ln(n+2)³` once `n ≥ 6`, while for `1 ≤ n ≤ 5` the read-all branch
already lies below the display (constant `2^20`). -/


lemma rpow_inv_three_eight : ((8 : ℝ)) ^ ((3 : ℝ)⁻¹) = 2 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast 2 3,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show ((3 : ℕ) : ℝ) * (3 : ℝ)⁻¹ = 1 by norm_num, Real.rpow_one]

/-- `L(N) ≤ 8·ln(N+2)` at every `N`: the paper's `L` against the natural
logarithm of the cube-root exponent. -/
lemma paperLog_le_eight_log (N : ℕ) :
    paperLog N ≤ 8 * Real.log ((N : ℝ) + 2) := by
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hmono : Real.log 2 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hdiv : Real.logb 2 ((N : ℝ) + 2) ≤ (3 / 2) * Real.log ((N : ℝ) + 2) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  unfold paperLog
  linarith

/-- `ln 3 ≥ 51/50`, from `ln 3 = ln 2 + ln(3/2)` and `ln(3/2) ≥ 1 − 2/3`. -/
lemma fiftyone_div_fifty_le_log_three : (51 / 50 : ℝ) ≤ Real.log 3 := by
  have hl2 := Real.log_two_gt_d9
  have h32 : 1 - (3 / 2 : ℝ)⁻¹ ≤ Real.log (3 / 2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hsplit : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [hsplit]
  norm_num at h32
  linarith

lemma fiftyone_div_fifty_le_log_add_two {n : ℕ} (hn : 1 ≤ n) :
    (51 / 50 : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact le_trans fiftyone_div_fifty_le_log_three
    (Real.log_le_log (by norm_num) (by linarith))

/-- For `n ≥ 6`, `L(n) ≤ ln(n+2)³`. -/
lemma paperLog_le_log_cube {n : ℕ} (hn : 6 ≤ n) :
    paperLog n ≤ Real.log ((n : ℝ) + 2) ^ (3 : ℕ) := by
  have hl2 := Real.log_two_gt_d9
  have hn' : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h8 : Real.log 8 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  set t := Real.log ((n : ℝ) + 2) with ht
  have ht2 : 2 ≤ t := by linarith
  have hdiv : Real.logb 2 ((n : ℝ) + 2) ≤ (3 / 2) * t := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have hcube : 4 * t ≤ t ^ (3 : ℕ) := by
    have : t ^ (3 : ℕ) = t * t * t := by ring
    nlinarith
  unfold paperLog
  linarith

/-- **The final display, absorbed**: the `2^(C·N^(1/3))` factor goes into the
`L(n)`-power (`2 ≤ L(n)`), and `L(N)^(1/3) ≤ 2·ln(N+2)^(1/3)`. -/
theorem paper_display_exact_of_final_real {N n : ℕ} {Q : ℝ}
    (hQ : Q ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
        * ((2 : ℝ) ^ (65536 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)))
          * paperLog n
            ^ (65536 * ((N : ℝ) ^ ((3 : ℝ)⁻¹))
                * paperLog N ^ ((3 : ℝ)⁻¹))))) :
    Q ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
        * paperLog n
          ^ (262144 * (((N : ℝ) * Real.log ((N : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) := by
  refine le_trans hQ (min_le_min le_rfl
    (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)))
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hP := three_le_paperLog n
  have hPN := three_le_paperLog N
  have hlog0 : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
  set a : ℝ := 65536 * ((N : ℝ) ^ ((3 : ℝ)⁻¹)) with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set ℓ : ℝ := paperLog N ^ ((3 : ℝ)⁻¹) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ]
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ)⁻¹) := (Real.one_rpow _).symm
      _ ≤ paperLog N ^ ((3 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have hℓ2 : ℓ ≤ 2 * Real.log ((N : ℝ) + 2) ^ ((3 : ℝ)⁻¹) := by
    calc ℓ ≤ (8 * Real.log ((N : ℝ) + 2)) ^ ((3 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by linarith) (paperLog_le_eight_log N) (by norm_num)
      _ = 2 * Real.log ((N : ℝ) + 2) ^ ((3 : ℝ)⁻¹) := by
          rw [Real.mul_rpow (by norm_num) hlog0, rpow_inv_three_eight]
  -- the fixed exponential joins the `L(n)`-power
  have h2P : (2 : ℝ) ^ a ≤ paperLog n ^ a :=
    Real.rpow_le_rpow (by norm_num) (by linarith) ha0
  have hmerge : paperLog n ^ a * paperLog n ^ (a * ℓ)
      = paperLog n ^ (a + a * ℓ) :=
    (Real.rpow_add (by linarith) a (a * ℓ)).symm
  have hexp : a + a * ℓ
      ≤ 262144 * (((N : ℝ) * Real.log ((N : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)) := by
    rw [Real.mul_rpow hN0 hlog0, ha]
    have hN13 : (0 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) := Real.rpow_nonneg hN0 _
    nlinarith
  calc (2 : ℝ) ^ a * paperLog n ^ (a * ℓ)
      ≤ paperLog n ^ a * paperLog n ^ (a * ℓ) :=
        mul_le_mul_of_nonneg_right h2P (Real.rpow_nonneg (by linarith) _)
    _ = paperLog n ^ (a + a * ℓ) := hmerge
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp

/-- **The introduction's form**: base `ln(n+2)` instead of `L(n)`.  For
`n ≥ 6`, `L(n) ≤ ln(n+2)³`; for `1 ≤ n ≤ 5` the read-all branch already lies
below `√n·ln(n+2)^E`, since `ln(n+2) ≥ ln 3 > 1` and `E` is large. -/
theorem intro_display_of_paper_display {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n)
    {Q : ℝ}
    (hQ : Q ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
        * paperLog n
          ^ (262144 * (((N : ℝ) * Real.log ((N : ℝ) + 2)) ^ ((3 : ℝ)⁻¹))))) :
    Q ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
        * Real.log ((n : ℝ) + 2)
          ^ (1048576 * (((N : ℝ) * Real.log ((N : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) := by
  have hQn : Q ≤ (n : ℝ) := hQ.trans (min_le_left _ _)
  refine le_min hQn ?_
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 1 ≤ Real.log ((N : ℝ) + 2) := by
    have := fiftyone_div_fifty_le_log_add_two hN
    linarith
  set y : ℝ := ((N : ℝ) * Real.log ((N : ℝ) + 2)) ^ ((3 : ℝ)⁻¹) with hy
  have hy1 : 1 ≤ y := by
    rw [hy]
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ)⁻¹) := (Real.one_rpow _).symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) (by nlinarith) (by norm_num)
  set t : ℝ := Real.log ((n : ℝ) + 2) with ht
  have ht1 : (51 / 50 : ℝ) ≤ t := fiftyone_div_fifty_le_log_add_two hn
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  by_cases h6 : 6 ≤ n
  · -- `L(n) ≤ t³`, so `L(n)^E ≤ t^(3E) ≤ t^(4E)`
    have hL := paperLog_le_log_cube h6
    have hP := three_le_paperLog n
    have hE0 : (0 : ℝ) ≤ 262144 * y := by linarith
    have h1 : paperLog n ^ (262144 * y) ≤ (t ^ (3 : ℕ)) ^ (262144 * y) :=
      Real.rpow_le_rpow (by linarith) hL hE0
    have h2 : (t ^ (3 : ℕ)) ^ (262144 * y) = t ^ (3 * (262144 * y)) := by
      rw [← Real.rpow_natCast t 3, ← Real.rpow_mul (by linarith)]
      norm_num
    have h3 : t ^ (3 * (262144 * y)) ≤ t ^ (1048576 * y) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
    refine le_trans (hQ.trans (min_le_right _ _)) ?_
    exact mul_le_mul_of_nonneg_left (h1.trans (h2 ▸ h3)) hsqrt0
  · -- short inputs: `n ≤ √n·3 ≤ √n·t^(4E)`
    have hn5 : (n : ℝ) ≤ 5 := by
      have : n ≤ 5 := by omega
      exact_mod_cast this
    have hsq3 : Real.sqrt (n : ℝ) ≤ 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hbern : (21 : ℝ) ≤ t ^ (1000 : ℕ) := by
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ t - 1 by linarith) 1000
      have : (1 : ℝ) + t - 1 = t := by ring
      rw [add_sub_cancel] at hb
      push_cast at hb
      nlinarith
    have hbig : (3 : ℝ) ≤ t ^ (1048576 * y) := by
      have h1000 : t ^ ((1000 : ℕ) : ℝ) ≤ t ^ (1048576 * y) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; nlinarith)
      rw [Real.rpow_natCast] at h1000
      linarith
    have hnn : (n : ℝ) = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
      (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
    calc Q ≤ (n : ℝ) := hQn
      _ = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := hnn
      _ ≤ Real.sqrt (n : ℝ) * 3 := mul_le_mul_of_nonneg_left hsq3 hsqrt0
      _ ≤ _ := mul_le_mul_of_nonneg_left hbig hsqrt0

/-- **`eq:ags-cuberoot-final`, native model**, in the paper's form:
`Q_{1/3}(Prod_{M,n}) ≤ min{n, √n·L(n)^(C·(N·ln(N+2))^(1/3))}`, `C = 2^18`. -/
theorem aperiodic_qQuery_final_exact {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M' => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * paperLog n
            ^ (262144 * (((Fintype.card M' : ℝ)
                * Real.log ((Fintype.card M' : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) := by
  have hne : Nonempty M' := ⟨1⟩
  exact paper_display_exact_of_final_real
    (paper_display_final_real_of_le Fintype.card_pos hn
      (by exact_mod_cast aperiodic_qQuery_upper_length)
      (aperiodic_qQuery_paper hn))

/-- **`eq:ags-cuberoot-final`, one-hot model** (the paper's oracle convention). -/
theorem aperiodic_oneHotQQuery_final_exact {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M' => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * paperLog n
            ^ (262144 * (((Fintype.card M' : ℝ)
                * Real.log ((Fintype.card M' : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  paper_display_exact_of_final_real (aperiodic_oneHotQQuery_final_real hn)

/-- **The introduction's display (`res:aperiodic-size`), native model**:
`Q_{1/3}(Prod_{M,n}) ≤ min{n, √n·ln(n+2)^(C·(N·ln(N+2))^(1/3))}`, `C = 2^20`. -/
theorem aperiodic_qQuery_intro {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M' => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * Real.log ((n : ℝ) + 2)
            ^ (1048576 * (((Fintype.card M' : ℝ)
                * Real.log ((Fintype.card M' : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  intro_display_of_paper_display Fintype.card_pos hn (aperiodic_qQuery_final_exact hn)

/-- **The introduction's display, one-hot model**. -/
theorem aperiodic_oneHotQQuery_intro {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M' => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * Real.log ((n : ℝ) + 2)
            ^ (1048576 * (((Fintype.card M' : ℝ)
                * Real.log ((Fintype.card M' : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  intro_display_of_paper_display Fintype.card_pos hn
    (aperiodic_oneHotQQuery_final_exact hn)

/-- **`eq:ags-cuberoot-final` for semigroups, one-hot**: `N = |S| + 1`. -/
theorem aperiodic_semigroup_oneHotQQuery_final_exact (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S' => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (Real.sqrt ((n + 1 : ℕ) : ℝ)
          * paperLog (n + 1)
            ^ (262144 * ((((Fintype.card S' + 1 : ℕ) : ℝ)
                * Real.log (((Fintype.card S' + 1 : ℕ) : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  paper_display_exact_of_final_real (aperiodic_semigroup_oneHotQQuery_final_real n)

/-- **The introduction's display for semigroups, one-hot**: `N = |S| + 1`. -/
theorem aperiodic_semigroup_oneHotQQuery_intro (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S' => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (Real.sqrt ((n + 1 : ℕ) : ℝ)
          * Real.log (((n + 1 : ℕ) : ℝ) + 2)
            ^ (1048576 * ((((Fintype.card S' + 1 : ℕ) : ℝ)
                * Real.log (((Fintype.card S' + 1 : ℕ) : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  intro_display_of_paper_display (Nat.le_add_left 1 _) (Nat.le_add_left 1 n)
    (aperiodic_semigroup_oneHotQQuery_final_exact n)

end Presentation

end MonoidProduct
