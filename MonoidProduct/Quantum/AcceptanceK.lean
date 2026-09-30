import MonoidProduct.Quantum.CubeRootApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance test: the cube-root AGS theorem

The statement pins for the **cube-root AGS theorem** (`thm:ags-cuberoot-size`
in the paper, the aperiodic clause at cube-root precision) and its operational
exports.  Like the other acceptance files, this file exists to be broken: any
change to a pinned statement fails the build.

Pinned:

1. **The classical cube-root theorem** — every finite aperiodic monoid
   satisfies the alphabet-uniform word-product contract at
   `cubeRootFactor 256 |M| n₀`; the universal exponent multiplier is
   `K = 256`.
2. **The exact certificates** — `HasDual` and `advPM ≤ cubeRootDualCost`
   at every alphabet and length, monoid and `WithOne` semigroup forms
   (length `n + 1`, carrier `|S| + 1`).
3. **The operational forms** — `Q_{1/3}(Prod_{M,n}) ≤ min{n,
   8192(1 + cubeRootDualCost 256 |M| n)}` natively, `16384` in the
   canonical one-hot XOR model, and the semigroup versions at cap `n + 1`
   with `[Nonempty S]`.
4. **The paper displays** (`1 ≤ n`) —
   `Q ≤ √n·(N·L(n))^(4096·(N·L(N))^(1/3))` with `L = cubeLog`, in both
   models, and the semigroup one-hot form at `N = |S| + 1` where positive
   length is automatic.
5. **The final displays, separated form** (`cubeLog`, fixed exponential
   `2^(C·N^(1/3))` kept apart).
6. **The paper's `L`** — `eq:ags-cuberoot-unabsorbed` verbatim, and the
   final display in separated form.
7. **The paper's exact displays** — `eq:ags-cuberoot-final`,
   `Q ≤ min{n, √n·L(n)^(2^18·(N·ln(N+2))^(1/3))}`, and the introduction's
   `res:aperiodic-size`, `Q ≤ min{n, √n·ln(n+2)^(2^20·(N·ln(N+2))^(1/3))}`,
   native and one-hot, and the semigroup one-hot forms at `N = |S| + 1`.

    #print axioms MonoidProduct.hasWordProdDualPoly_cubeRootFactor
      → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
open QuantumQueryComplexity
namespace AcceptanceK

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
variable {S : Type} [Semigroup S] [Fintype S] [DecidableEq S]
  [IsAperiodicSemigroup S]

/-! ## 1. The classical cube-root theorem -/

theorem cube_root_pinned (n₀ : ℕ) :
    HasWordProdDualPoly M n₀ (cubeRootFactor 256 (Fintype.card M) n₀) :=
  hasWordProdDualPoly_cubeRootFactor M n₀

/-! ## 2. The exact certificates -/

theorem dual_pinned (letter : σ → M) (n : ℕ) :
    HasDual (fun x : Fin n → σ => wordProd letter x)
      (cubeRootDualCost 256 (Fintype.card M) n) :=
  hasDual_wordProd_cubeRoot letter n

theorem advPM_pinned (letter : σ → M) (n : ℕ) :
    advPM (fun x : Fin n → σ => wordProd letter x)
      ≤ cubeRootDualCost 256 (Fintype.card M) n :=
  advPM_wordProd_cubeRoot letter n

theorem semigroup_dual_pinned (sletter : σ → S) (n : ℕ) :
    HasDual (fun x : Fin (n + 1) → σ => semigroupProd n fun i => sletter (x i))
      (cubeRootDualCost 256 (Fintype.card S + 1) (n + 1)) :=
  hasDual_semigroupProd_cubeRoot sletter n

theorem semigroup_advPM_pinned (sletter : σ → S) (n : ℕ) :
    advPM (fun x : Fin (n + 1) → σ => semigroupProd n fun i => sletter (x i))
      ≤ cubeRootDualCost 256 (Fintype.card S + 1) (n + 1) :=
  advPM_semigroupProd_cubeRoot sletter n

/-! ## 3. The operational forms -/

theorem operational_pinned (n : ℕ) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (uniformExtractionConstant
          * (1 + cubeRootDualCost 256 (Fintype.card M) n)) :=
  aperiodic_qQuery_le_min

theorem oneHot_pinned (n : ℕ) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
          (16384 * (1 + cubeRootDualCost 256 (Fintype.card M) n)) :=
  aperiodic_oneHotQQuery_le_min

theorem semigroup_operational_pinned [Nonempty S] (n : ℕ) :
    (qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (uniformExtractionConstant
          * (1 + cubeRootDualCost 256 (Fintype.card S + 1) (n + 1))) :=
  aperiodic_semigroup_qQuery_le_min

theorem semigroup_oneHot_pinned [Nonempty S] (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ)
          (16384 * (1 + cubeRootDualCost 256 (Fintype.card S + 1) (n + 1))) :=
  aperiodic_semigroup_oneHotQQuery_le_min

/-! ## 4. The paper displays -/

theorem paper_pinned {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (((Fintype.card M * cubeLog n : ℕ) : ℝ)
          ^ (4096 * (((Fintype.card M * cubeLog (Fintype.card M) : ℕ) : ℝ)
              ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_qQuery_paper hn

theorem paper_oneHot_pinned {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (((Fintype.card M * cubeLog n : ℕ) : ℝ)
          ^ (4096 * (((Fintype.card M * cubeLog (Fintype.card M) : ℕ) : ℝ)
              ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_oneHotQQuery_paper hn

theorem semigroup_paper_oneHot_pinned [Nonempty S] (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ Real.sqrt ((n + 1 : ℕ) : ℝ)
          * ((((Fintype.card S + 1) * cubeLog (n + 1) : ℕ) : ℝ)
          ^ (4096 * ((((Fintype.card S + 1)
              * cubeLog (Fintype.card S + 1) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_semigroup_oneHotQQuery_paper n

/-! ## 5. The final displays (`eq:ags-cuberoot-final`) -/

theorem final_pinned {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * ((2 : ℝ) ^ (16384 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog n : ℕ) : ℝ)
              ^ (16384 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹))
                  * ((cubeLog (Fintype.card M) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_qQuery_final hn

theorem final_oneHot_pinned {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * ((2 : ℝ) ^ (16384 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog n : ℕ) : ℝ)
              ^ (16384 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹))
                  * ((cubeLog (Fintype.card M) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_oneHotQQuery_final hn

theorem semigroup_final_oneHot_pinned [Nonempty S] (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (Real.sqrt ((n + 1 : ℕ) : ℝ)
          * ((2 : ℝ) ^ (16384 * (((Fintype.card S + 1 : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
            * ((cubeLog (n + 1) : ℕ) : ℝ)
              ^ (16384 * (((Fintype.card S + 1 : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))
                  * ((cubeLog (Fintype.card S + 1) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_semigroup_oneHotQQuery_final n

/-! ## 6. The paper's logarithm, verbatim

The paper states its displays with the *real* `L(n) = 2 + log₂(n+2)`
(`paperLog`); the endpoints above use the `Nat.clog` variant `cubeLog`.
`cubeLog_le_two_mul_paperLog` bridges them at a factor two, and these pins
give `eq:ags-cuberoot-unabsorbed` **verbatim** at constant `16384`, and the
final display at constant `65536` in its separated form (the fixed
exponential `2^(C·N^(1/3))` and `L(N)^(1/3)` still explicit; part 7 below has
the paper's exact form). -/

theorem paper_real_pinned {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ Real.sqrt (n : ℝ) * (((Fintype.card M : ℝ) * paperLog n)
          ^ (16384 * (((Fintype.card M : ℝ) * paperLog (Fintype.card M))
              ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_qQuery_paper_real hn

theorem final_real_oneHot_pinned {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * ((2 : ℝ) ^ (65536 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹)))
            * paperLog n
              ^ (65536 * ((Fintype.card M : ℝ) ^ ((3 : ℝ)⁻¹))
                  * paperLog (Fintype.card M) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_oneHotQQuery_final_real hn

theorem semigroup_final_real_oneHot_pinned [Nonempty S] (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (Real.sqrt ((n + 1 : ℕ) : ℝ)
          * ((2 : ℝ) ^ (65536 * (((Fintype.card S + 1 : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)))
            * paperLog (n + 1)
              ^ (65536 * (((Fintype.card S + 1 : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹))
                  * paperLog (Fintype.card S + 1) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_semigroup_oneHotQQuery_final_real n

/-! ## 7. The paper's exact displays

`eq:ags-cuberoot-final` (`L(n) = 2 + log₂(n+2)`, natural `log` in the exponent,
constant `2^18`) and the introduction's `res:aperiodic-size` (base `ln(n+2)`,
constant `2^20`), both at `1 ≤ n`. -/

theorem final_exact_pinned {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * paperLog n
            ^ (262144 * (((Fintype.card M : ℝ)
                * Real.log ((Fintype.card M : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_qQuery_final_exact hn

theorem final_exact_oneHot_pinned {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * paperLog n
            ^ (262144 * (((Fintype.card M : ℝ)
                * Real.log ((Fintype.card M : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_oneHotQQuery_final_exact hn

theorem intro_pinned {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * Real.log ((n : ℝ) + 2)
            ^ (1048576 * (((Fintype.card M : ℝ)
                * Real.log ((Fintype.card M : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_qQuery_intro hn

theorem intro_oneHot_pinned {n : ℕ} (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * Real.log ((n : ℝ) + 2)
            ^ (1048576 * (((Fintype.card M : ℝ)
                * Real.log ((Fintype.card M : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_oneHotQQuery_intro hn

theorem semigroup_final_exact_oneHot_pinned [Nonempty S] (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (Real.sqrt ((n + 1 : ℕ) : ℝ)
          * paperLog (n + 1)
            ^ (262144 * ((((Fintype.card S + 1 : ℕ) : ℝ)
                * Real.log (((Fintype.card S + 1 : ℕ) : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_semigroup_oneHotQQuery_final_exact n

theorem semigroup_intro_oneHot_pinned [Nonempty S] (n : ℕ) :
    (oneHotQQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ)
      ≤ min ((n + 1 : ℕ) : ℝ) (Real.sqrt ((n + 1 : ℕ) : ℝ)
          * Real.log (((n + 1 : ℕ) : ℝ) + 2)
            ^ (1048576 * ((((Fintype.card S + 1 : ℕ) : ℝ)
                * Real.log (((Fintype.card S + 1 : ℕ) : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) :=
  aperiodic_semigroup_oneHotQQuery_intro n

end AcceptanceK

end MonoidProduct
