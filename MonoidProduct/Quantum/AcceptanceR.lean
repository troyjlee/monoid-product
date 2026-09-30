import MonoidProduct.Quantum.WidthApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Essential width, capped, index-two, index-k: acceptance test

The statement pins for the operational essential-width endpoints.  Like the
other pins, this file exists to be broken: a refactor that changes a
statement fails here.

Pinned, with every convention literal:

1. **the classical certificates** — `HasDual` at `16·√(n·B)` for any
   incremental summary of essential width `≤ B`, and at the width bounds
   of the four instantiations (aperiodic fallback `|M|-1`, capped
   `min{n, r·k}`, index-two `5·log₂|M|`, index-k `2⁶²(k+1)·t·log₂ t`),
   split out of the `advPM` endpoints (retained in `Width/*` and
   `Capped/*` unchanged), no quantum import in their proofs;
2. **the native unabsorbed minimums** at the literal `8192`, error
   exactly `1/3`, exact read-all cap `n`;
3. **the one-hot unabsorbed minimums** of the three manuscript theorems
   at `16384` with the same exact cap.

The capped family's matching operational lower bound is
`capped_qQuery_lower` (`Quantum/Applications.lean`).

Manual axiom checks:

    #print axioms MonoidProduct.capped_qQuery_le_min
      → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.indexK_qQuery_le_min
      → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.hasDual_of_summary
      → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
open QuantumQueryComplexity
namespace AcceptanceR

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {O : Type} [Fintype O] [DecidableEq O]
variable {Q : Type} [Fintype Q] [DecidableEq Q]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M]
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-! ## 1. The classical certificates -/

theorem dual_summary_pinned (S : IncrementalSummary ι σ O Q)
    {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    HasDual S.out (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) :=
  hasDual_of_summary S hB hwidth

theorem dual_cardMonoid_pinned [IsAperiodicMonoid M]
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * ((Fintype.card M : ℝ) - 1))) :=
  hasDual_prodFun_card_monoid hM m

theorem dual_capped_pinned {k : ℕ} (hk : 0 < k) [Nonempty ρ]
    (m : σ → ρ → Capped k) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (min (Fintype.card ι) (Fintype.card ρ * k) : ℕ))) :=
  hasDual_prodFun_capped hk m

theorem dual_indexTwo_pinned (hx3 : ∀ z : M, z ^ 3 = z ^ 2)
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (5 * Real.logb 2 (Fintype.card M)))) :=
  hasDual_prodFun_five_logb hx3 hM m

theorem dual_indexK_pinned {k : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (m : σ → M) :
    HasDual (fun x : ι → σ => ∏ i, m (x i))
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M)))) :=
  hasDual_prodFun_bcw hxk hk m

/-! ## 2. The native unabsorbed minimums -/

theorem summary_min_pinned [Nonempty O] (S : IncrementalSummary ι σ O Q)
    {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (8192 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * B))) := by
  have h := summary_qQuery_le_min S hB hwidth
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

theorem capped_min_pinned {k : ℕ} (hk : 0 < k) [Nonempty ρ]
    (m : σ → ρ → Capped k) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (8192 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (min (Fintype.card ι) (Fintype.card ρ * k) : ℕ)))) := by
  have h := capped_qQuery_le_min (ι := ι) hk m
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

theorem indexTwo_min_pinned (hx3 : ∀ z : M, z ^ 3 = z ^ 2)
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (8192 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (5 * Real.logb 2 (Fintype.card M))))) := by
  have h := indexTwo_qQuery_le_min (ι := ι) hx3 hM m
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

theorem indexK_min_pinned {k : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (8192 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M
              * Real.logb 2 (bcwT M))))) := by
  have h := indexK_qQuery_le_min (ι := ι) hxk hk m
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

/-! ## 3. The one-hot unabsorbed minimums -/

theorem capped_oneHot_min_pinned {k : ℕ} (hk : 0 < k) [Nonempty ρ]
    (m : σ → ρ → Capped k) :
    (oneHotQQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (min (Fintype.card ι) (Fintype.card ρ * k) : ℕ)))) :=
  capped_oneHotQQuery_le_min hk m

theorem indexTwo_oneHot_min_pinned (hx3 : ∀ z : M, z ^ 3 = z ^ 2)
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    (oneHotQQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (5 * Real.logb 2 (Fintype.card M))))) :=
  indexTwo_oneHotQQuery_le_min hx3 hM m

theorem indexK_oneHot_min_pinned {k : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (m : σ → M) :
    (oneHotQQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M
              * Real.logb 2 (bcwT M))))) :=
  indexK_oneHotQQuery_le_min hxk hk m

/-! ## Every budget `B ≥ 0` (`thm:essential-width`)

The positive-budget pins above are regression checks for the scan engine; the pins below
cover the public statements including width zero: no positivity argument, no assumed
constancy certificate, zero queries from a genuine constant algorithm. -/

/-- The adversary bound for every `B : ℕ`. -/
theorem adv_nonneg_pinned (S : IncrementalSummary ι σ O Q) (B : ℕ)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    advPM S.out ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) :=
  advPM_le_of_summary_nonneg S hwidth

/-- The bundled dual for every `B : ℕ`. -/
theorem dual_nonneg_pinned (S : IncrementalSummary ι σ O Q) (B : ℕ)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    HasDual S.out (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) :=
  hasDual_of_summary_nonneg S hwidth

/-- The weighted certificate for every `B : ℕ` and positive costs. -/
theorem weighted_nonneg_pinned (S : IncrementalSummary ι σ O Q) (B : ℕ)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    HasWeightedDual S.out c (16 * (Real.sqrt B * costNorm c)) :=
  hasWeightedDual_of_summary_nonneg S hwidth c hc

/-- The weighted certificate at `B = 0`: cost `16·(√0·‖c‖) = 0`. -/
theorem weighted_zero_pinned (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    HasWeightedDual S.out c (16 * (Real.sqrt ((0 : ℕ) : ℝ) * costNorm c)) :=
  hasWeightedDual_of_summary_nonneg S hwidth c hc

/-- Width zero: pairwise equal outputs. -/
theorem width_zero_const_pinned (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0) (x y : ι → σ) :
    S.out x = S.out y :=
  S.out_const_of_width_zero hwidth x y

/-- Width zero: adversary value zero. -/
theorem width_zero_adv_pinned (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0) :
    advPM S.out = 0 :=
  advPM_eq_zero_of_width_zero S hwidth

/-- Width zero: zero queries at error `1/3`. -/
theorem width_zero_qQuery_pinned [Nonempty O] (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0) :
    qQuery S.out (1 / 3) = 0 :=
  summary_qQuery_eq_zero_of_width_zero S hwidth (by norm_num)

/-- The uniform operational bound `min{n, 2^18·√(nB)}` for every `B : ℕ`. -/
theorem qQuery_min_sqrt_pinned [Nonempty O] (S : IncrementalSummary ι σ O Q) (B : ℕ)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * B)) :=
  summary_qQuery_le_min_sqrt S hwidth

/-- Specialisation `B = 0`: the bound reads `min{n, 0}`. -/
theorem qQuery_min_sqrt_zero_pinned [Nonempty O] (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * ((0 : ℕ) : ℝ))) :=
  summary_qQuery_le_min_sqrt S hwidth

/-- Specialisation `B = 1`: `min{n, 2^18·√n}`. -/
theorem qQuery_min_sqrt_one_pinned [Nonempty O] (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 1) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * ((1 : ℕ) : ℝ))) :=
  summary_qQuery_le_min_sqrt S hwidth

/-- Specialisation `n = 1`: `min{1, 2^18·√B}`. -/
theorem qQuery_min_sqrt_len_one_pinned [Nonempty O] (S : IncrementalSummary (Fin 1) σ O Q)
    (B : ℕ) (hwidth : ∀ (x : Fin 1 → σ) (T : Finset (Fin 1)), (S.essentialSet x T).card ≤ B) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ min (Fintype.card (Fin 1) : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card (Fin 1) : ℝ) * B)) :=
  summary_qQuery_le_min_sqrt S hwidth

/-- The real-budget forms. -/
theorem adv_real_pinned (S : IncrementalSummary ι σ O Q) {b : ℝ} (hb : 0 ≤ b)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), ((S.essentialSet x T).card : ℝ) ≤ b) :
    advPM S.out ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * b) :=
  advPM_le_of_summary_real S hb hwidth

theorem qQuery_real_pinned [Nonempty O] (S : IncrementalSummary ι σ O Q) {b : ℝ} (hb : 0 ≤ b)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), ((S.essentialSet x T).card : ℝ) ≤ b) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * b)) :=
  summary_qQuery_le_min_sqrt_real S hb hwidth

/-- The empty alphabet: the wrappers carry no `Nonempty σ` hypothesis. -/
theorem adv_nonneg_empty_alphabet_pinned (S : IncrementalSummary ι Empty O Q) (B : ℕ)
    (hwidth : ∀ (x : ι → Empty) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    advPM S.out ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) :=
  advPM_le_of_summary_nonneg S hwidth

/-- The width-transfer certificate for the commutative product at every budget. -/
theorem dual_prodFun_nonneg_pinned (m : σ → M) (B : ℕ)
    (hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ B) :
    HasDual (fun x : ι → σ => ∏ i, m (x i)) (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) :=
  hasDual_prodFun_of_width_nonneg m hw

end AcceptanceR

end MonoidProduct
