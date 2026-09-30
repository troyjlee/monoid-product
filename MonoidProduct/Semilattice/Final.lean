import MonoidProduct.Semilattice.Record
import QuantumQueryComplexity.Scan.Final
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# `ADV±(⋁ᵢ m (xᵢ)) ≤ 16 √(n B)`

The product of the letters read at `n` query positions, in a commutative
idempotent semigroup — equivalently the join in a finite semilattice — has a
direct adversary dual of cost `16 √(n B)`, where `B` is any uniform bound on the
number of critical positions of a set.  Taking `B = ⌊log₂(|A|+1)⌋`
(`MonoidProduct/Semilattice/Critical.lean`) gives

  `ADV±(joinMap m) ≤ 16 √(n ⌊log₂(|A|+1)⌋)`,

which is `O(√(n log|L|))`, the bound of the paper's `thm:semilattice-product`,
proved here without a quantum algorithm, amplification, or the characterisation
of quantum query complexity by the adversary bound.

The weights are the maximum scan's, rescaled by the budget: at the one-indexed
time `k`,

  `W(i, black) = √k/√B`,   `W(i, red) = √B/√k`,

so both masses are bounded by `√(B/k) + [red] √(k/B)`.  The record count
`k · |{red at time k}| ≤ B · |Order ι|` turns the second term into another
`√(B/k)`, and `∑_k 1/√k ≤ 2√n` finishes.  At `B = 1` these are exactly the
maximum scan's weights, which is the right sanity check: a chain has at most one
critical position per prefix.

No harmonic number appears, unlike in the algorithmic proof, which counts an
expected number of update rounds.  The dual instead balances the red
contribution at each depth against the reciprocal black one.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [SemilatticeSup A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The weights -/

/-- The join scan's weights for a record budget `B`.  At `B = 1` they are the
maximum scan's `√(t+1)` and `1/√(t+1)`. -/
noncomputable def joinWeight (B : ℕ) (e : Order ι) (i : ι) (col : Bool) : ℝ :=
  if col then Real.sqrt B / Real.sqrt (((e i : ℕ) : ℝ) + 1)
  else Real.sqrt (((e i : ℕ) : ℝ) + 1) / Real.sqrt B

variable {B : ℕ}

lemma sqrt_time_pos (t : ℕ) : (0 : ℝ) < Real.sqrt ((t : ℝ) + 1) :=
  Real.sqrt_pos.mpr (by positivity)

lemma sqrt_budget_pos (hB : 0 < B) : (0 : ℝ) < Real.sqrt B :=
  Real.sqrt_pos.mpr (by exact_mod_cast hB)

lemma joinWeight_true (B : ℕ) (e : Order ι) (i : ι) :
    joinWeight B e i true = Real.sqrt B / Real.sqrt (((e i : ℕ) : ℝ) + 1) := by
  simp [joinWeight]

lemma joinWeight_false (B : ℕ) (e : Order ι) (i : ι) :
    joinWeight B e i false = Real.sqrt (((e i : ℕ) : ℝ) + 1) / Real.sqrt B := by
  simp [joinWeight]

lemma joinWeight_pos (hB : 0 < B) (e : Order ι) (i : ι) (col : Bool) :
    0 < joinWeight B e i col := by
  cases col
  · rw [joinWeight_false]
    exact div_pos (sqrt_time_pos _) (sqrt_budget_pos hB)
  · rw [joinWeight_true]
    exact div_pos (sqrt_budget_pos hB) (sqrt_time_pos _)

/-- The common upper envelope of the two weighted masses at one coordinate. -/
noncomputable def joinTerm (B : ℕ) (t : ℕ) (rec : Bool) : ℝ :=
  Real.sqrt B / Real.sqrt ((t : ℝ) + 1)
    + if rec then Real.sqrt ((t : ℝ) + 1) / Real.sqrt B else 0

lemma joinTerm_false (B : ℕ) (t : ℕ) :
    joinTerm B t false = Real.sqrt B / Real.sqrt ((t : ℝ) + 1) := by simp [joinTerm]

lemma joinTerm_true (B : ℕ) (t : ℕ) :
    joinTerm B t true = Real.sqrt B / Real.sqrt ((t : ℝ) + 1)
      + Real.sqrt ((t : ℝ) + 1) / Real.sqrt B := by simp [joinTerm]

/-- The `u`-side mass at a coordinate is bounded by the envelope. -/
lemma joinWeight_inv_le (hB : 0 < B) (e : Order ι) (col : Bool) (i : ι) :
    (joinWeight B e i col)⁻¹ ≤ joinTerm B ((e i : ℕ)) col := by
  have ht := sqrt_time_pos ((e i : ℕ))
  have hb := sqrt_budget_pos hB
  cases col
  · rw [joinWeight_false, joinTerm_false, inv_div]
  · rw [joinWeight_true, joinTerm_true, inv_div]
    have h : (0 : ℝ) ≤ Real.sqrt B / Real.sqrt (((e i : ℕ) : ℝ) + 1) :=
      le_of_lt (div_pos hb ht)
    linarith

/-- The `v`-side mass at a coordinate is exactly the envelope. -/
lemma joinWeight_sum_eq (hB : 0 < B) (e : Order ι) (col : Bool) (i : ι) :
    joinWeight B e i true + (if col then joinWeight B e i false else 0)
      = joinTerm B ((e i : ℕ)) col := by
  cases col
  · have h0 : (if (false : Bool) then joinWeight B e i false else (0 : ℝ)) = 0 := by
      simp
    rw [h0, add_zero, joinWeight_true, joinTerm_false]
  · have h1 : (if (true : Bool) then joinWeight B e i false else (0 : ℝ))
        = joinWeight B e i false := by simp
    rw [h1, joinWeight_true, joinWeight_false, joinTerm_true]

/-! ## Averaging over scan orders -/

/-- **The per-time estimate.**  The record count turns the red contribution into
a second copy of the black one. -/
lemma sum_orders_joinTerm_le (hB : 0 < B) (m : σ → A) (x : ι → σ)
    (hcrit : ∀ T : Finset ι, (criticalSet (fun j => m (x j)) T).card ≤ B)
    (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, joinTerm B ((t : ℕ))
        (isJoinRecord (⇑e) (fun j => m (x j)) (e.symm t)))
      ≤ (Fintype.card (Order ι) : ℝ)
          * (2 * (Real.sqrt B / Real.sqrt (((t : ℕ) : ℝ) + 1))) := by
  classical
  have ht := sqrt_time_pos ((t : ℕ))
  have hb := sqrt_budget_pos hB
  have htt : Real.sqrt (((t : ℕ) : ℝ) + 1) * Real.sqrt (((t : ℕ) : ℝ) + 1)
      = ((t : ℕ) : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  have hbb : Real.sqrt B * Real.sqrt B = (B : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  set R := (Finset.univ.filter fun e : Order ι =>
    isJoinRecord (⇑e) (fun j => m (x j)) (e.symm t) = true).card with hRdef
  -- split the envelope into its constant and record parts
  have hsplit : (∑ e : Order ι, joinTerm B ((t : ℕ))
        (isJoinRecord (⇑e) (fun j => m (x j)) (e.symm t)))
      = (Fintype.card (Order ι) : ℝ)
          * (Real.sqrt B / Real.sqrt (((t : ℕ) : ℝ) + 1))
        + (R : ℝ) * (Real.sqrt (((t : ℕ) : ℝ) + 1) / Real.sqrt B) := by
    simp only [joinTerm]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul,
      add_zero, hRdef]
  have hcount : (((t : ℕ) : ℝ) + 1) * (R : ℝ)
      ≤ (B : ℝ) * (Fintype.card (Order ι) : ℝ) := by
    exact_mod_cast card_joinRecord_mul_le_of_bound (fun j => m (x j)) hcrit t
  have hkey : (R : ℝ) * (Real.sqrt (((t : ℕ) : ℝ) + 1) / Real.sqrt B)
      ≤ (Fintype.card (Order ι) : ℝ)
        * (Real.sqrt B / Real.sqrt (((t : ℕ) : ℝ) + 1)) := by
    -- clear the denominators by hand: both sides over `√B √(t+1)`
    have h1 : (R : ℝ) * (Real.sqrt (((t : ℕ) : ℝ) + 1) / Real.sqrt B)
        = ((R : ℝ) * (Real.sqrt (((t : ℕ) : ℝ) + 1)
              * Real.sqrt (((t : ℕ) : ℝ) + 1)))
          / (Real.sqrt B * Real.sqrt (((t : ℕ) : ℝ) + 1)) := by
      field_simp
    have h2 : (Fintype.card (Order ι) : ℝ)
          * (Real.sqrt B / Real.sqrt (((t : ℕ) : ℝ) + 1))
        = ((Fintype.card (Order ι) : ℝ) * (Real.sqrt B * Real.sqrt B))
          / (Real.sqrt B * Real.sqrt (((t : ℕ) : ℝ) + 1)) := by
      field_simp
    rw [h1, h2, htt, hbb, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith [hcount]) (by positivity)
  rw [hsplit]
  linarith

/-- `∑_t √B/√(t+1) ≤ 2 √(n B)`. -/
lemma sum_sqrt_budget_le (hB : 0 < B) :
    (∑ t : Fin (Fintype.card ι),
        Real.sqrt B / Real.sqrt (((t : ℕ) : ℝ) + 1))
      ≤ 2 * (Real.sqrt (Fintype.card ι) * Real.sqrt B) := by
  have hstep : (∑ t : Fin (Fintype.card ι),
        Real.sqrt B / Real.sqrt (((t : ℕ) : ℝ) + 1))
      = Real.sqrt B * ∑ t : Fin (Fintype.card ι),
          (Real.sqrt (((t : ℕ) : ℝ) + 1))⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [div_eq_mul_inv]
  rw [hstep]
  refine le_trans (mul_le_mul_of_nonneg_left
    (sum_inv_sqrt_fin_le (Fintype.card ι)) (Real.sqrt_nonneg _)) (le_of_eq ?_)
  ring

/-! ## The dual -/

set_option maxHeartbeats 1000000 in
/-- **A dual for the product whose cost is controlled input by input.**

The budget hypothesis is *per input*: at `x` the mass is `16 √(n B)` as soon as
the prefixes of `x` have at most `B` critical positions.  Nothing about other
inputs is used, which is what lets the same solution serve a **promise** domain,
where the budget is only assumed on the promise. -/
theorem exists_joinMap_dual_pointwise (m : σ → A) (hB : 0 < B) :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A))
      (joinMap m : (ι → σ) → A),
      ∀ x : ι → σ, (∀ T : Finset ι, (criticalSet (fun j => m (x j)) T).card ≤ B) →
        (∑ i : ι, ∑ k : Order ι × ScanDim ι A (WithBot A),
            P.u x i k * P.u x i k)
          ≤ 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)
        ∧ (∑ i : ι, ∑ k : Order ι × ScanDim ι A (WithBot A),
            P.v x i k * P.v x i k)
          ≤ 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B) := by
  classical
  haveI : Nonempty (Order ι) := ⟨Fintype.equivFin ι⟩
  set N : ℝ := (Fintype.card (Order ι) : ℝ) with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef, Nat.cast_pos]; exact Fintype.card_pos
  have hN' : N ≠ 0 := ne_of_gt hNpos
  set P : Order ι → DualPair (ScanDim ι A (WithBot A)) (joinMap m : (ι → σ) → A) :=
    fun e => (joinScanMap m (⇑e) e.injective).dual (joinWeight B e)
      (joinWeight_pos hB e) with hPdef
  -- the total, over all orders, of the envelope, for one input
  have hmaster : ∀ x : ι → σ,
      (∀ T : Finset ι, (criticalSet (fun j => m (x j)) T).card ≤ B) →
      (∑ e : Order ι, ∑ i : ι,
          joinTerm B ((e i : ℕ)) (isJoinRecord (⇑e) (fun j => m (x j)) i))
        ≤ N * (4 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)) := by
    intro x hcrit
    have hswap : ∀ e : Order ι,
        (∑ i : ι, joinTerm B ((e i : ℕ))
            (isJoinRecord (⇑e) (fun j => m (x j)) i))
          = ∑ t : Fin (Fintype.card ι), joinTerm B ((t : ℕ))
              (isJoinRecord (⇑e) (fun j => m (x j)) (e.symm t)) := by
      intro e
      refine Fintype.sum_equiv e _ _ fun i => ?_
      rw [Equiv.symm_apply_apply]
    rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hswap e, Finset.sum_comm]
    calc (∑ t : Fin (Fintype.card ι), ∑ e : Order ι, joinTerm B ((t : ℕ))
          (isJoinRecord (⇑e) (fun j => m (x j)) (e.symm t)))
        ≤ ∑ t : Fin (Fintype.card ι), N
            * (2 * (Real.sqrt B / Real.sqrt (((t : ℕ) : ℝ) + 1))) :=
          Finset.sum_le_sum fun t _ => sum_orders_joinTerm_le hB m x hcrit t
      _ = N * 2 * ∑ t : Fin (Fintype.card ι),
            Real.sqrt B / Real.sqrt (((t : ℕ) : ℝ) + 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ ≤ N * 2 * (2 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)) :=
          mul_le_mul_of_nonneg_left (sum_sqrt_budget_le hB) (by positivity)
      _ = N * (4 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)) := by ring
  refine ⟨DualPair.averageUnif P, fun x hcrit => ⟨?_, ?_⟩⟩
  · -- the `u` side
    rw [DualPair.sum_averageUnif_u_sq P x]
    have hmass : ∀ e : Order ι,
        (∑ i : ι, ∑ k : ScanDim ι A (WithBot A), (P e).u x i k * (P e).u x i k)
          ≤ 4 * ∑ i : ι, joinTerm B ((e i : ℕ))
              (isJoinRecord (⇑e) (fun j => m (x j)) i) := by
      intro e
      rw [hPdef, Scan.sum_dual_u_sq]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
      exact joinWeight_inv_le hB e _ i
    calc N⁻¹ * ∑ e : Order ι,
          (∑ i : ι, ∑ k : ScanDim ι A (WithBot A), (P e).u x i k * (P e).u x i k)
        ≤ N⁻¹ * ∑ e : Order ι, 4 * ∑ i : ι, joinTerm B ((e i : ℕ))
            (isJoinRecord (⇑e) (fun j => m (x j)) i) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => hmass e) ?_
          positivity
      _ = N⁻¹ * (4 * ∑ e : Order ι, ∑ i : ι, joinTerm B ((e i : ℕ))
            (isJoinRecord (⇑e) (fun j => m (x j)) i)) := by rw [← Finset.mul_sum]
      _ ≤ N⁻¹ * (4 * (N * (4 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmaster x hcrit) (by norm_num)
      _ = 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B) := by
          rw [show N⁻¹ * (4 * (N * (4 * (Real.sqrt (Fintype.card ι) * Real.sqrt B))))
              = (N⁻¹ * N) * (16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B))
            from by ring, inv_mul_cancel₀ hN', one_mul]
  · -- the `v` side
    rw [DualPair.sum_averageUnif_v_sq P x]
    have hmass : ∀ e : Order ι,
        (∑ i : ι, ∑ k : ScanDim ι A (WithBot A), (P e).v x i k * (P e).v x i k)
          = 4 * ∑ i : ι, joinTerm B ((e i : ℕ))
              (isJoinRecord (⇑e) (fun j => m (x j)) i) := by
      intro e
      rw [hPdef, Scan.sum_dual_v_sq,
        Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
          joinWeight_sum_eq hB e _ i]
      rfl
    calc N⁻¹ * ∑ e : Order ι,
          (∑ i : ι, ∑ k : ScanDim ι A (WithBot A), (P e).v x i k * (P e).v x i k)
        = N⁻¹ * ∑ e : Order ι, 4 * ∑ i : ι, joinTerm B ((e i : ℕ))
            (isJoinRecord (⇑e) (fun j => m (x j)) i) := by
          rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hmass e]
      _ = N⁻¹ * (4 * ∑ e : Order ι, ∑ i : ι, joinTerm B ((e i : ℕ))
            (isJoinRecord (⇑e) (fun j => m (x j)) i)) := by rw [← Finset.mul_sum]
      _ ≤ N⁻¹ * (4 * (N * (4 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmaster x hcrit) (by norm_num)
      _ = 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B) := by
          rw [show N⁻¹ * (4 * (N * (4 * (Real.sqrt (Fintype.card ι) * Real.sqrt B))))
              = (N⁻¹ * N) * (16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B))
            from by ring, inv_mul_cancel₀ hN', one_mul]

/-- **A dual for the product, from any critical budget.** -/
theorem exists_joinMap_dual_isCostLe_of_bound (m : σ → A) (hB : 0 < B)
    (hcrit : ∀ (y : ι → A) (T : Finset ι), (criticalSet y T).card ≤ B) :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A))
      (joinMap m : (ι → σ) → A),
      P.IsCostLe (16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)) := by
  obtain ⟨P, hP⟩ := exists_joinMap_dual_pointwise (ι := ι) m hB
  exact ⟨P, fun x => (hP x (fun T => hcrit _ T)).1,
    fun y => (hP y (fun T => hcrit _ T)).2⟩

/-- **The semilattice product bound.**  `B = ⌊log₂(|A|+1)⌋`. -/
theorem exists_joinMap_dual_isCostLe [Nonempty A] (m : σ → A) :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A))
      (joinMap m : (ι → σ) → A),
      P.IsCostLe (16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ))) := by
  obtain ⟨P, hP⟩ := exists_joinMap_dual_isCostLe_of_bound (ι := ι) (σ := σ) m
    (joinBits_pos (A := A)) (fun y T => card_criticalSet_le y T)
  refine ⟨P, ?_⟩
  rwa [Real.sqrt_mul (Nat.cast_nonneg _)]

/-- **`ADV±(⋁ᵢ m (xᵢ)) ≤ 16 √(n ⌊log₂(|A|+1)⌋)`.**

The paper's `thm:semilattice-product` for a finite join-semilattice, proved as a
direct adversary construction.  The bound sees neither the size of the letter
type `σ` nor anything about `A` beyond the number of its elements. -/
theorem advPM_joinMap_le [Nonempty A] (m : σ → A) :
    advPM (joinMap m : (ι → σ) → A)
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ)) := by
  obtain ⟨P, hP⟩ := exists_joinMap_dual_isCostLe (ι := ι) (σ := σ) (A := A) m
  exact advPM_le_of_dualPair P (by positivity) hP

end MonoidProduct
