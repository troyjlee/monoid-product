import MonoidProduct.WidthCerts
import QuantumQueryComplexity.Quantum.UniformHasDual
import MonoidProduct.Quantum.OneHotApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Essential width, capped, index-two, and index-k products: the
operational quantum-query endpoints

The bounded-error quantum query complexity of the essential-width family
(`monoid.tex` Theorems 8, 14, 16, 18), as named theorems:

* **the general engine**: `Q_{1/3}(S.out) ≤ min{n, 8192·(1 + 16·√(n·B))}`
  for any incremental summary of essential width `≤ B`, and the
  commutative-monoid product from any width bound;
* **the aperiodic fallback**: `B = |M| - 1`;
* **the capped counter** (`Θ` family): `B = min{n, r·k}`, with the
  matching operational lower bound already in
  `Quantum/Applications.lean` (`capped_qQuery_lower`);
* **index two**: `B = 5·log₂|M|` under `x³ = x²`;
* **index k**: `B = 2⁶²(k+1)·t·log₂ t` at `t = max 2 ⌈log₂|M|⌉` under
  `w^{k+1} = w^k`;
* **one-hot** forms of the three manuscript theorems (capped, index-two,
  index-k) at a direct factor two (`16384`), with the **exact** read-all
  cap `n`.

The upper route preserves the essential-width scan certificate:
`hasDual_of_summary`/`hasDual_prodFun_*` (`WidthCerts.lean`, split out of
the `advPM` endpoints, which are retained in `Width/*` and `Capped/*` as
weak-duality corollaries) `→ qQueryOn_third_le_of_hasDualOn_uniform` —
the cardinality-free extraction, so every bound is **uniform in the
letter alphabet**.

This file sits outside the `QuantumQueryComplexity.Quantum` aggregate: it is an
application layer importing both the classical width development and the
quantum model, built by CI as an explicit cross-stream target.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Summary

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {O : Type} [Fintype O] [DecidableEq O]
variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- **The general engine, operational**: any incremental summary of
essential width `≤ B` has `Q_{1/3}(S.out) ≤ 8192·(1 + 16·√(n·B))`. -/
theorem summary_qQuery_upper [Nonempty O] (S : IncrementalSummary ι σ O Q)
    {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_of_summary S hB hwidth).hasDualOn (by positivity)

/-- **Reading every position**: the exact cap `Q_{1/3}(S.out) ≤ n`. -/
theorem summary_qQuery_upper_length [Nonempty O]
    (S : IncrementalSummary ι σ O Q) :
    qQuery S.out (1 / 3) ≤ Fintype.card ι :=
  qQueryOn_le_card (read := (id : (ι → σ) → ι → σ)) (f := S.out)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form**:
`Q_{1/3}(S.out) ≤ min{n, 8192·(1 + 16·√(n·B))}`. -/
theorem summary_qQuery_le_min [Nonempty O] (S : IncrementalSummary ι σ O Q)
    {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * B))) :=
  le_min (by exact_mod_cast summary_qQuery_upper_length S)
    (summary_qQuery_upper S hB hwidth)

/-- **Width zero: exactly zero queries**, from a genuine zero-query constant algorithm.  If
the input space is empty the statement is vacuous and the constant is any output. -/
theorem summary_qQuery_eq_zero_of_width_zero [Nonempty O] (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0)
    {ε : ℝ} (hε : 0 ≤ ε) : qQuery S.out ε = 0 := by
  have hconst := S.out_const_of_width_zero hwidth
  by_cases h : Nonempty (ι → σ)
  · obtain ⟨x₀⟩ := h
    exact qQueryOn_const_eq_zero id (c := S.out x₀) (fun x => hconst x x₀) hε
  · exact qQueryOn_const_eq_zero id (c := Classical.arbitrary O) (fun x => absurd ⟨x⟩ h) hε

/-- **`thm:essential-width`, operational, for every budget `B ≥ 0`**:
`Q_{1/3}(S.out) ≤ min{n, 2^18·√(n·B)}`; at `B = 0` the right side is `0` and the algorithm
is the constant one, for `B ≥ 1` the unabsorbed `8192·(1 + 16√(nB))` is at most `2^18·√(nB)`
because `√(nB) ≥ 1`. -/
theorem summary_qQuery_le_min_sqrt [Nonempty O] (S : IncrementalSummary ι σ O Q) {B : ℕ}
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * B)) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · rw [summary_qQuery_eq_zero_of_width_zero S hwidth (by norm_num)]
    simp only [Nat.cast_zero]
    exact le_min (by positivity) (by positivity)
  · refine le_min (by exact_mod_cast summary_qQuery_upper_length S) ?_
    have h := summary_qQuery_upper S hB hwidth
    have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hs : (1 : ℝ) ≤ Real.sqrt ((Fintype.card ι : ℝ) * B) :=
      Real.one_le_sqrt.2 (by nlinarith)
    refine h.trans ?_
    rw [uniformExtractionConstant]
    nlinarith

/-- The real-budget form of the operational bound. -/
theorem summary_qQuery_le_min_sqrt_real [Nonempty O] (S : IncrementalSummary ι σ O Q) {b : ℝ}
    (hb : 0 ≤ b)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), ((S.essentialSet x T).card : ℝ) ≤ b) :
    (qQuery S.out (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * b)) := by
  have h := summary_qQuery_le_min_sqrt S (B := ⌊b⌋₊) fun x T => Nat.le_floor (hwidth x T)
  refine h.trans (min_le_min_left _ (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
    (by norm_num)))
  exact mul_le_mul_of_nonneg_left (Nat.floor_le hb) (Nat.cast_nonneg _)

end Summary

section Product

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- **The width transfer, operational**: any width bound `B` gives
`Q_{1/3}(∏ᵢ m(xᵢ)) ≤ 8192·(1 + 16·√(n·B))`. -/
theorem width_qQuery_upper (m : σ → M) {B : ℕ} (hB : 0 < B)
    (hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ B) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_prodFun_of_width m hB hw).hasDualOn (by positivity)

/-- **Reading every position**: the exact cap `n` for any monoid
product. -/
theorem prodFun_qQuery_upper_length (m : σ → M) :
    qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) ≤ Fintype.card ι :=
  qQueryOn_le_card (read := (id : (ι → σ) → ι → σ))
    (f := fun x : ι → σ => ∏ i, m (x i))
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The aperiodic fallback, operational**:
`Q_{1/3}(∏ᵢ m(xᵢ)) ≤ min{n, 8192·(1 + 16·√(n·(|M|-1)))}`. -/
theorem cardMonoid_qQuery_le_min [IsAperiodicMonoid M]
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * ((Fintype.card M : ℝ) - 1)))) := by
  refine le_min (by exact_mod_cast prodFun_qQuery_upper_length m) ?_
  refine qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_prodFun_card_monoid hM m).hasDualOn ?_
  have h1 : (1 : ℝ) ≤ (Fintype.card M : ℝ) := by
    have : (1 : ℕ) ≤ Fintype.card M := by omega
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) * ((Fintype.card M : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  positivity

/-- **Index two, operational** (`thm:index-two-width`): under `x³ = x²`,
`Q_{1/3}(∏ᵢ m(xᵢ)) ≤ 8192·(1 + 16·√(n·5·log₂|M|))`. -/
theorem indexTwo_qQuery_upper (hx3 : ∀ z : M, z ^ 3 = z ^ 2)
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (5 * Real.logb 2 (Fintype.card M)))) := by
  refine qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_prodFun_five_logb hx3 hM m).hasDualOn ?_
  have hL : (0 : ℝ) ≤ Real.logb 2 (Fintype.card M) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hM.trans' (by norm_num))
  positivity

/-- **The index-two unabsorbed minimum**. -/
theorem indexTwo_qQuery_le_min (hx3 : ∀ z : M, z ^ 3 = z ^ 2)
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (5 * Real.logb 2 (Fintype.card M))))) :=
  le_min (by exact_mod_cast prodFun_qQuery_upper_length m)
    (indexTwo_qQuery_upper hx3 hM m)

/-- **Index k, operational** (`thm:index-k-width`): under `w^{k+1} = w^k`,
`Q_{1/3}(∏ᵢ m(xᵢ)) ≤ 8192·(1 + 16·√(n·2⁶²(k+1)·t·log₂ t))` at
`t = max 2 ⌈log₂|M|⌉`. -/
theorem indexK_qQuery_upper {k : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M
              * Real.logb 2 (bcwT M)))) := by
  refine qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_prodFun_bcw hxk hk m).hasDualOn ?_
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 (bcwT M) := one_le_logb_bcwT M
  have h0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ)
      * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M)) := by
    have : (0 : ℝ) ≤ 2 ^ 62 * ((k : ℝ) + 1) * bcwT M := by positivity
    exact mul_nonneg (Nat.cast_nonneg _) (by nlinarith)
  positivity

/-- **The index-k unabsorbed minimum**. -/
theorem indexK_qQuery_le_min {k : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M
              * Real.logb 2 (bcwT M))))) :=
  le_min (by exact_mod_cast prodFun_qQuery_upper_length m)
    (indexK_qQuery_upper hxk hk m)

/-- **Index two, one-hot**, at a direct factor two. -/
theorem indexTwo_oneHotQQuery_le_min (hx3 : ∀ z : M, z ^ 3 = z ^ 2)
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    (oneHotQQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (5 * Real.logb 2 (Fintype.card M))))) := by
  have hcap : oneHotQQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3)
      ≤ Fintype.card ι :=
    oneHotQQuery_le_card _ (by norm_num : (0 : ℝ) ≤ 1 / 3)
  refine le_min (by exact_mod_cast hcap) ?_
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (fun x : ι → σ => ∏ i, m (x i))) (by norm_num)
    (indexTwo_qQuery_upper hx3 hM m)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Index k, one-hot**, at a direct factor two. -/
theorem indexK_oneHotQQuery_le_min {k : ℕ}
    (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (m : σ → M) :
    (oneHotQQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (2 ^ 62 * ((k : ℝ) + 1) * bcwT M
              * Real.logb 2 (bcwT M))))) := by
  have hcap : oneHotQQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3)
      ≤ Fintype.card ι :=
    oneHotQQuery_le_card _ (by norm_num : (0 : ℝ) ≤ 1 / 3)
  refine le_min (by exact_mod_cast hcap) ?_
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (fun x : ι → σ => ∏ i, m (x i))) (by norm_num)
    (indexK_qQuery_upper hxk hk m)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

end Product

section Capped

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- **The capped counter, operational** (`thm:capped-counter-product`, upper half):
`Q_{1/3}(∏ᵢ m(xᵢ)) ≤ 8192·(1 + 16·√(n·min{n, r·k}))`; the matching lower
bound is `capped_qQuery_lower` (`Quantum/Applications.lean`). -/
theorem capped_qQuery_upper {k : ℕ} (hk : 0 < k) [Nonempty ρ]
    (m : σ → ρ → Capped k) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (min (Fintype.card ι) (Fintype.card ρ * k) : ℕ))) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_prodFun_capped hk m).hasDualOn (by positivity)

/-- **The capped unabsorbed minimum**. -/
theorem capped_qQuery_le_min {k : ℕ} (hk : 0 < k) [Nonempty ρ]
    (m : σ → ρ → Capped k) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (min (Fintype.card ι) (Fintype.card ρ * k) : ℕ)))) :=
  le_min (by exact_mod_cast prodFun_qQuery_upper_length m)
    (capped_qQuery_upper hk m)

/-- **The capped counter, one-hot**, at a direct factor two. -/
theorem capped_oneHotQQuery_le_min {k : ℕ} (hk : 0 < k) [Nonempty ρ]
    (m : σ → ρ → Capped k) :
    (oneHotQQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (min (Fintype.card ι) (Fintype.card ρ * k) : ℕ)))) := by
  have hcap : oneHotQQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3)
      ≤ Fintype.card ι :=
    oneHotQQuery_le_card _ (by norm_num : (0 : ℝ) ≤ 1 / 3)
  refine le_min (by exact_mod_cast hcap) ?_
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (fun x : ι → σ => ∏ i, m (x i))) (by norm_num)
    (capped_qQuery_upper hk m)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

end Capped

end MonoidProduct
