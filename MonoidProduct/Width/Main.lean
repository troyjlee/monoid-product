import MonoidProduct.Width.Incidence
import QuantumQueryComplexity.Scan.Uniform
import QuantumQueryComplexity.Scan.Average
import QuantumQueryComplexity.Scan.Weighted
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The essential-width theorem: `ADV±_c(f) ≤ 16 √B (∑ᵢ cᵢ²)^{1/2}`

The paper's `thm:essential-width`, with the weighted costs of
`eq:weighted-width`: if `f` has an order-independent incremental
summary of essential width at most `B ≥ 1`, then for any positive coordinate
costs the scan dual has weighted cost at most `16 √B (∑ᵢ cᵢ²)^{1/2}`; unit
costs give the boxed `ADV±(f) ≤ 16 √(nB)`.

This file is `QuantumQueryComplexity/Scan/Weighted.lean` with the maximum scan abstracted
away.  The scale gains a `√B`:

  `q_t = C √(t+1) / (√n √B)`,   `W(i, black) = q_t / cᵢ`,   `W(i, red) = cᵢ / q_t`,

so both weighted masses at a coordinate are bounded by
`cᵢ²/q_t + [red] · q_t` (∗), and the two averages balance at
`C √B / (√n √(t+1))` each: the coordinate term because the coordinate at a
fixed time is uniform (`sum_orders_coord`), the record term because at most a
`B/(t+1)` fraction of orders are red at time `t`
(`card_red_mul_le_of_bound`).  Then `∑_t 1/√(t+1) ≤ 2√n` and the gadget factor
`4` give `16 √B C`.  At `B = 1` this is exactly the weighted maximum theorem.

The **only** hypothesis about the function is the essential-width bound; all
the adversary algebra lives in the general `Scan.dual`.  Instantiations are in
`MonoidProduct/Width/Instances.lean`.

The scan engine needs a positive budget (`0 < B`: the scale `1/√B` is used).  The public
statement of `thm:essential-width` covers every `B ≥ 0`: `advPM_le_of_summary_nonneg`
(width zero gives a constant output, `out_const_of_width_zero`, hence adversary value `0`),
and its real-budget form `advPM_le_of_summary_real`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## The budgeted cost scale -/

/-- The scale at scan time `t` with red budget `B`.  At `B = 1` this is
`Scan/Weighted.lean`'s `costScale`. -/
noncomputable def bScale (c : ι → ℝ) (B : ℕ) (t : ℕ) : ℝ :=
  costNorm c * Real.sqrt ((t : ℝ) + 1)
    / (Real.sqrt (Fintype.card ι) * Real.sqrt B)

/-- The common value of the two averaged terms at time `t`. -/
noncomputable def bBase (c : ι → ℝ) (B : ℕ) (t : ℕ) : ℝ :=
  costNorm c * Real.sqrt B
    / (Real.sqrt (Fintype.card ι) * Real.sqrt ((t : ℝ) + 1))

variable (c : ι → ℝ) (B : ℕ)

lemma sqrt_budget_pos (hB : 0 < B) : (0 : ℝ) < Real.sqrt B :=
  Real.sqrt_pos.mpr (by exact_mod_cast hB)

lemma bScale_pos (hc : ∀ i, 0 < c i) (hB : 0 < B) (t : ℕ) : 0 < bScale c B t :=
  div_pos (mul_pos (costNorm_pos c hc) (Real.sqrt_pos.mpr (by positivity)))
    (mul_pos sqrt_card_pos (sqrt_budget_pos B hB))

lemma bBase_nonneg (hc : ∀ i, 0 < c i) (t : ℕ) : 0 ≤ bBase c B t :=
  div_nonneg (mul_nonneg (le_of_lt (costNorm_pos c hc)) (Real.sqrt_nonneg _))
    (by positivity)

/-- `B · q_t = (t+1) · bBase t`: after the incidence count pays `B/(t+1)`, the
record term lands on the same average as the coordinate term. -/
lemma bScale_mul_budget (hB : 0 < B) (t : ℕ) :
    (B : ℝ) * bScale c B t = ((t : ℝ) + 1) * bBase c B t := by
  have ht : (0 : ℝ) < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have htt : Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) = (t : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hBB : Real.sqrt B * Real.sqrt B = (B : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hn' : Real.sqrt (Fintype.card ι) ≠ 0 := ne_of_gt sqrt_card_pos
  have ht' : Real.sqrt ((t : ℝ) + 1) ≠ 0 := ne_of_gt ht
  have hB' : Real.sqrt B ≠ 0 := ne_of_gt (sqrt_budget_pos B hB)
  rw [bScale, bBase, ← mul_div_assoc, ← mul_div_assoc,
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination
    ((B : ℝ) * costNorm c * Real.sqrt (Fintype.card ι)) * htt
      - (((t : ℝ) + 1) * costNorm c * Real.sqrt (Fintype.card ι)) * hBB

/-! ## The weights -/

/-- The scan weights with red budget `B`: black is `q/cᵢ`, red is `cᵢ/q`. -/
noncomputable def bWeight (c : ι → ℝ) (B : ℕ) (e : Order ι) (i : ι)
    (col : Bool) : ℝ :=
  if col then c i / bScale c B ((e i : ℕ)) else bScale c B ((e i : ℕ)) / c i

lemma bWeight_true (e : Order ι) (i : ι) :
    bWeight c B e i true = c i / bScale c B ((e i : ℕ)) := by simp [bWeight]

lemma bWeight_false (e : Order ι) (i : ι) :
    bWeight c B e i false = bScale c B ((e i : ℕ)) / c i := by simp [bWeight]

lemma bWeight_pos (hc : ∀ i, 0 < c i) (hB : 0 < B) (e : Order ι) (i : ι)
    (col : Bool) : 0 < bWeight c B e i col := by
  have h1 := hc i
  have h2 := bScale_pos c B hc hB ((e i : ℕ))
  cases col
  · rw [bWeight_false]
    exact div_pos h2 h1
  · rw [bWeight_true]
    exact div_pos h1 h2

/-- The bound (∗) on both weighted masses at one coordinate. -/
noncomputable def bTerm (c : ι → ℝ) (B : ℕ) (i : ι) (t : ℕ) (rec : Bool) : ℝ :=
  c i * c i / bScale c B t + if rec then bScale c B t else 0

lemma bTerm_false (i : ι) (t : ℕ) :
    bTerm c B i t false = c i * c i / bScale c B t := by simp [bTerm]

lemma bTerm_true (i : ι) (t : ℕ) :
    bTerm c B i t true = c i * c i / bScale c B t + bScale c B t := by
  simp [bTerm]

/-- The `u`-side weighted mass at a coordinate is bounded by (∗). -/
lemma bTerm_u_le (hc : ∀ i, 0 < c i) (hB : 0 < B) (e : Order ι) (col : Bool)
    (i : ι) : c i * (bWeight c B e i col)⁻¹ ≤ bTerm c B i ((e i : ℕ)) col := by
  have hci : (0 : ℝ) < c i := hc i
  have hq : (0 : ℝ) < bScale c B ((e i : ℕ)) := bScale_pos c B hc hB ((e i : ℕ))
  have hci' : c i ≠ 0 := ne_of_gt hci
  have hq' : bScale c B ((e i : ℕ)) ≠ 0 := ne_of_gt hq
  cases col
  · rw [bWeight_false, bTerm_false, inv_div]
    apply le_of_eq
    field_simp
  · rw [bWeight_true, bTerm_true, inv_div]
    have hstep : c i * (bScale c B ((e i : ℕ)) / c i) = bScale c B ((e i : ℕ)) := by
      field_simp
    rw [hstep]
    have hpos : (0 : ℝ) ≤ c i * c i / bScale c B ((e i : ℕ)) :=
      div_nonneg (mul_self_nonneg _) hq.le
    linarith

/-- The `v`-side weighted mass at a coordinate is exactly (∗). -/
lemma bTerm_v_eq (hc : ∀ i, 0 < c i) (hB : 0 < B) (e : Order ι) (col : Bool)
    (i : ι) :
    c i * (bWeight c B e i true + if col then bWeight c B e i false else 0)
      = bTerm c B i ((e i : ℕ)) col := by
  have hci' : c i ≠ 0 := ne_of_gt (hc i)
  have hq' : bScale c B ((e i : ℕ)) ≠ 0 :=
    ne_of_gt (bScale_pos c B hc hB ((e i : ℕ)))
  cases col
  · have h0 : (if (false : Bool) then bWeight c B e i false else (0 : ℝ)) = 0 := by
      simp
    rw [h0, add_zero, bWeight_true, bTerm_false]
    field_simp
  · have h1 : (if (true : Bool) then bWeight c B e i false else (0 : ℝ))
        = bWeight c B e i false := by simp
    rw [h1, bWeight_true, bWeight_false, bTerm_true]
    field_simp

/-! ## Averaging over scan orders -/

/-- **The coordinate term averages to `bBase`**: the coordinate at a fixed time
is uniform, and no red event is involved. -/
lemma sum_orders_bCoordTerm (hc : ∀ i, 0 < c i) (hB : 0 < B)
    (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, c (e.symm t) * c (e.symm t) / bScale c B ((t : ℕ)))
      = (Fintype.card (Order ι) : ℝ) * bBase c B ((t : ℕ)) := by
  have hn := sqrt_card_pos (ι := ι)
  have hnn := sqrt_card_sq (ι := ι)
  have hC := costNorm_pos c hc
  have hCC := costNorm_sq c hc
  have ht : (0 : ℝ) < Real.sqrt (((t : ℕ) : ℝ) + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  have hBB : Real.sqrt B * Real.sqrt B = (B : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hn' : Real.sqrt (Fintype.card ι) ≠ 0 := ne_of_gt hn
  have ht' : Real.sqrt (((t : ℕ) : ℝ) + 1) ≠ 0 := ne_of_gt ht
  have hB' : Real.sqrt B ≠ 0 := ne_of_gt (sqrt_budget_pos B hB)
  have hC' : costNorm c ≠ 0 := ne_of_gt hC
  have hnc : (Fintype.card ι : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    exact ne_of_gt h
  have huni := sum_orders_coord t (fun i => c i * c i)
  have hsum : (∑ e : Order ι, c (e.symm t) * c (e.symm t))
      = (Fintype.card (Order ι) : ℝ) * (costNorm c * costNorm c)
        / (Real.sqrt (Fintype.card ι) * Real.sqrt (Fintype.card ι)) := by
    rw [hnn, hCC, eq_div_iff hnc]
    linarith [huni]
  rw [← Finset.sum_div, hsum, bScale, bBase]
  field_simp

/-- **The record term averages to at most `bBase`**: at most a `B/(t+1)`
fraction of orders are red at time `t`, by the incidence count. -/
lemma sum_orders_bRecTerm_le (S : IncrementalSummary ι σ O Q)
    (hc : ∀ i, 0 < c i) (hB : 0 < B) (x : ι → σ)
    (hwidth : ∀ T : Finset ι, (S.essentialSet x T).card ≤ B)
    (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, if (S.toScan ⇑e e.injective).col x (e.symm t) then
        bScale c B ((t : ℕ)) else 0)
      ≤ (Fintype.card (Order ι) : ℝ) * bBase c B ((t : ℕ)) := by
  classical
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  set R := (Finset.univ.filter fun e : Order ι =>
    (S.toScan ⇑e e.injective).col x (e.symm t) = true).card with hRdef
  have hsplit : (∑ e : Order ι, if (S.toScan ⇑e e.injective).col x (e.symm t) then
      bScale c B ((t : ℕ)) else 0) = (R : ℝ) * bScale c B ((t : ℕ)) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul,
      add_zero, hRdef]
  have hcount : (((t : ℕ) : ℝ) + 1) * (R : ℝ)
      ≤ (B : ℝ) * (Fintype.card (Order ι) : ℝ) := by
    exact_mod_cast S.card_red_mul_le_of_bound x hwidth t
  -- multiply the target by `B > 0` and use `B·q_t = (t+1)·bBase`
  rw [hsplit]
  refine le_of_mul_le_mul_left ?_ hBpos
  calc (B : ℝ) * ((R : ℝ) * bScale c B ((t : ℕ)))
      = (R : ℝ) * ((B : ℝ) * bScale c B ((t : ℕ))) := by ring
    _ = (R : ℝ) * ((((t : ℕ) : ℝ) + 1) * bBase c B ((t : ℕ))) := by
        rw [bScale_mul_budget c B hB]
    _ = ((((t : ℕ) : ℝ) + 1) * (R : ℝ)) * bBase c B ((t : ℕ)) := by ring
    _ ≤ ((B : ℝ) * (Fintype.card (Order ι) : ℝ)) * bBase c B ((t : ℕ)) :=
        mul_le_mul_of_nonneg_right hcount (bBase_nonneg c B hc _)
    _ = (B : ℝ) * ((Fintype.card (Order ι) : ℝ) * bBase c B ((t : ℕ))) := by ring

/-- `∑_t C√B/(√n √(t+1)) ≤ 2 √B C`. -/
lemma sum_bBase_le (hc : ∀ i, 0 < c i) :
    (∑ t : Fin (Fintype.card ι), bBase c B ((t : ℕ)))
      ≤ 2 * (Real.sqrt B * costNorm c) := by
  have hn := sqrt_card_pos (ι := ι)
  have hn' : Real.sqrt (Fintype.card ι) ≠ 0 := ne_of_gt hn
  have hCnn : 0 ≤ costNorm c := le_of_lt (costNorm_pos c hc)
  have hstep : (∑ t : Fin (Fintype.card ι), bBase c B ((t : ℕ)))
      = costNorm c * Real.sqrt B / Real.sqrt (Fintype.card ι)
        * ∑ t : Fin (Fintype.card ι), (Real.sqrt (((t : ℕ) : ℝ) + 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [bBase]
    have ht' : Real.sqrt (((t : ℕ) : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  rw [hstep]
  have hsum := sum_inv_sqrt_fin_le (Fintype.card ι)
  refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) (le_of_eq ?_)
  field_simp

/-! ## The essential-width theorem -/

set_option maxHeartbeats 1000000 in
/-- **The essential-width theorem, weighted** (`thm:essential-width` with
`eq:weighted-width`): a summary of essential width at most `B ≥ 1` gives a dual of
`c`-weighted cost at most `16 √B (∑ᵢ cᵢ²)^{1/2}`. -/
theorem exists_summary_dual_isWeightedCostLe (S : IncrementalSummary ι σ O Q)
    {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ P : DualPair (Order ι × ScanDim ι O Q) S.out,
      P.IsWeightedCostLe c (16 * (Real.sqrt B * costNorm c)) := by
  classical
  haveI : Nonempty (Order ι) := ⟨Fintype.equivFin ι⟩
  set N : ℝ := (Fintype.card (Order ι) : ℝ) with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef, Nat.cast_pos]; exact Fintype.card_pos
  have hN' : N ≠ 0 := ne_of_gt hNpos
  set P : Order ι → DualPair (ScanDim ι O Q) S.out :=
    fun e => (S.toScan ⇑e e.injective).dual (bWeight c B e)
      (bWeight_pos c B hc hB e) with hPdef
  -- the total, over all orders, of the bound (∗)
  have hmaster : ∀ x : ι → σ,
      (∑ e : Order ι, ∑ i : ι,
          bTerm c B i ((e i : ℕ)) ((S.toScan ⇑e e.injective).col x i))
        ≤ N * (4 * (Real.sqrt B * costNorm c)) := by
    intro x
    have hswap : ∀ e : Order ι,
        (∑ i : ι, bTerm c B i ((e i : ℕ)) ((S.toScan ⇑e e.injective).col x i))
          = ∑ t : Fin (Fintype.card ι), bTerm c B (e.symm t) ((t : ℕ))
              ((S.toScan ⇑e e.injective).col x (e.symm t)) := by
      intro e
      refine Fintype.sum_equiv e _ _ fun i => ?_
      rw [Equiv.symm_apply_apply]
    rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hswap e, Finset.sum_comm]
    have hper : ∀ t : Fin (Fintype.card ι),
        (∑ e : Order ι, bTerm c B (e.symm t) ((t : ℕ))
            ((S.toScan ⇑e e.injective).col x (e.symm t)))
          ≤ N * (2 * bBase c B ((t : ℕ))) := by
      intro t
      simp only [bTerm]
      rw [Finset.sum_add_distrib, sum_orders_bCoordTerm c B hc hB t]
      have := sum_orders_bRecTerm_le c B S hc hB x (hwidth x) t
      rw [hNdef]
      linarith
    calc (∑ t : Fin (Fintype.card ι), ∑ e : Order ι,
          bTerm c B (e.symm t) ((t : ℕ))
            ((S.toScan ⇑e e.injective).col x (e.symm t)))
        ≤ ∑ t : Fin (Fintype.card ι), N * (2 * bBase c B ((t : ℕ))) :=
          Finset.sum_le_sum fun t _ => hper t
      _ = N * 2 * ∑ t : Fin (Fintype.card ι), bBase c B ((t : ℕ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ ≤ N * 2 * (2 * (Real.sqrt B * costNorm c)) :=
          mul_le_mul_of_nonneg_left (sum_bBase_le c B hc) (by positivity)
      _ = N * (4 * (Real.sqrt B * costNorm c)) := by ring
  refine ⟨DualPair.averageUnif P, ?_⟩
  refine DualPair.averageUnif_isWeightedCostLe P (fun x => ?_) (fun y => ?_)
  · -- the `u` side
    have hmass : ∀ e : Order ι,
        (∑ i : ι, c i * ∑ k : ScanDim ι O Q, (P e).u x i k * (P e).u x i k)
          ≤ 4 * ∑ i : ι,
              bTerm c B i ((e i : ℕ)) ((S.toScan ⇑e e.injective).col x i) := by
      intro e
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hPdef, Scan.sum_dual_u_sq_coord]
      rw [show c i * (4 * (bWeight c B e i
            ((S.toScan ⇑e e.injective).col x i))⁻¹)
          = 4 * (c i * (bWeight c B e i
            ((S.toScan ⇑e e.injective).col x i))⁻¹) from by ring]
      exact mul_le_mul_of_nonneg_left (bTerm_u_le c B hc hB e _ i) (by norm_num)
    calc N⁻¹ * ∑ e : Order ι,
          (∑ i : ι, c i * ∑ k : ScanDim ι O Q, (P e).u x i k * (P e).u x i k)
        ≤ N⁻¹ * ∑ e : Order ι, 4 * ∑ i : ι,
            bTerm c B i ((e i : ℕ)) ((S.toScan ⇑e e.injective).col x i) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => hmass e) ?_
          positivity
      _ = N⁻¹ * (4 * ∑ e : Order ι, ∑ i : ι,
            bTerm c B i ((e i : ℕ)) ((S.toScan ⇑e e.injective).col x i)) := by
          rw [← Finset.mul_sum]
      _ ≤ N⁻¹ * (4 * (N * (4 * (Real.sqrt B * costNorm c)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmaster x) (by norm_num)
      _ = 16 * (Real.sqrt B * costNorm c) := by
          rw [show N⁻¹ * (4 * (N * (4 * (Real.sqrt B * costNorm c))))
              = (N⁻¹ * N) * (16 * (Real.sqrt B * costNorm c)) from by ring,
            inv_mul_cancel₀ hN', one_mul]
  · -- the `v` side
    have hmass : ∀ e : Order ι,
        (∑ i : ι, c i * ∑ k : ScanDim ι O Q, (P e).v y i k * (P e).v y i k)
          = 4 * ∑ i : ι,
              bTerm c B i ((e i : ℕ)) ((S.toScan ⇑e e.injective).col y i) := by
      intro e
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hPdef, Scan.sum_dual_v_sq_coord]
      rw [show c i * (4 * (bWeight c B e i true
            + if (S.toScan ⇑e e.injective).col y i then
                bWeight c B e i false else 0))
          = 4 * (c i * (bWeight c B e i true
            + if (S.toScan ⇑e e.injective).col y i then
                bWeight c B e i false else 0)) from by ring]
      rw [bTerm_v_eq c B hc hB e _ i]
    calc N⁻¹ * ∑ e : Order ι,
          (∑ i : ι, c i * ∑ k : ScanDim ι O Q, (P e).v y i k * (P e).v y i k)
        = N⁻¹ * ∑ e : Order ι, 4 * ∑ i : ι,
            bTerm c B i ((e i : ℕ)) ((S.toScan ⇑e e.injective).col y i) := by
          rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hmass e]
      _ = N⁻¹ * (4 * ∑ e : Order ι, ∑ i : ι,
            bTerm c B i ((e i : ℕ)) ((S.toScan ⇑e e.injective).col y i)) := by
          rw [← Finset.mul_sum]
      _ ≤ N⁻¹ * (4 * (N * (4 * (Real.sqrt B * costNorm c)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmaster y) (by norm_num)
      _ = 16 * (Real.sqrt B * costNorm c) := by
          rw [show N⁻¹ * (4 * (N * (4 * (Real.sqrt B * costNorm c))))
              = (N⁻¹ * N) * (16 * (Real.sqrt B * costNorm c)) from by ring,
            inv_mul_cancel₀ hN', one_mul]

/-- **The essential-width theorem, unit costs**: `16 √(nB)`. -/
theorem exists_summary_dual_isCostLe (S : IncrementalSummary ι σ O Q)
    {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    ∃ P : DualPair (Order ι × ScanDim ι O Q) S.out,
      P.IsCostLe (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) := by
  obtain ⟨P, hP⟩ := exists_summary_dual_isWeightedCostLe S hB hwidth
    (fun _ => 1) (fun _ => one_pos)
  have hnorm : costNorm (fun _ : ι => (1 : ℝ)) = Real.sqrt (Fintype.card ι) := by
    rw [costNorm]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hval : 16 * (Real.sqrt B * costNorm (fun _ : ι => (1 : ℝ)))
      = 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) := by
    rw [hnorm, Real.sqrt_mul (Nat.cast_nonneg _)]
    ring
  rw [hval] at hP
  exact ⟨P, fun x => by simpa using hP.1 x, fun y => by simpa using hP.2 y⟩

/-- **`ADV±(f) ≤ 16 √(nB)`** for any function with an order-independent
incremental summary of essential width at most `B ≥ 1` — the boxed statement of
`thm:essential-width`. -/
theorem advPM_le_of_summary (S : IncrementalSummary ι σ O Q)
    {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    advPM S.out ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) := by
  obtain ⟨P, hP⟩ := exists_summary_dual_isCostLe S hB hwidth
  exact advPM_le_of_dualPair P (by positivity) hP

/-- **`thm:essential-width` for every budget `B ≥ 0`**: `ADV±(S.out) ≤ 16·√(n·B)`.  At `B = 0`
the output is constant and the adversary value is `0`; for `B ≥ 1` this is the scan engine
`advPM_le_of_summary`. -/
theorem advPM_le_of_summary_nonneg (S : IncrementalSummary ι σ O Q) {B : ℕ}
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    advPM S.out ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · rw [advPM_eq_zero_of_forall_eq (S.out_const_of_width_zero hwidth)]
    positivity
  · exact advPM_le_of_summary S hB hwidth

/-- The real-budget form: a bound `b ≥ 0` on the essential width (as a real) gives
`ADV±(S.out) ≤ 16·√(n·b)`; budgets `0 ≤ b < 1` fall into the zero case. -/
theorem advPM_le_of_summary_real (S : IncrementalSummary ι σ O Q) {b : ℝ} (hb : 0 ≤ b)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), ((S.essentialSet x T).card : ℝ) ≤ b) :
    advPM S.out ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * b) := by
  have h := advPM_le_of_summary_nonneg S (B := ⌊b⌋₊) fun x T => Nat.le_floor (hwidth x T)
  refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
  exact mul_le_mul_of_nonneg_left (Nat.floor_le hb) (Nat.cast_nonneg _)

/-- Width zero: the adversary value is exactly zero, with no assumption on the alphabet. -/
theorem advPM_eq_zero_of_width_zero (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0) :
    advPM S.out = 0 :=
  advPM_eq_zero_of_forall_eq (S.out_const_of_width_zero hwidth)

/-- **Width zero means the adversary bound is zero**: the function is constant. -/
theorem advPM_eq_zero_of_essentialSet_eq_empty [Nonempty σ]
    (S : IncrementalSummary ι σ O Q)
    (h : ∀ (x : ι → σ) (T : Finset ι), S.essentialSet x T = ∅) :
    advPM S.out = 0 :=
  advPM_eq_zero_of_forall_eq fun x y =>
    S.out_const_of_essentialSet_eq_empty h x y

end MonoidProduct
