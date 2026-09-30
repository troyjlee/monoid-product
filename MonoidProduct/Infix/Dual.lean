import MonoidProduct.Infix.Negative
import MonoidProduct.Infix.Saturation
import QuantumQueryComplexity.Quantum.UniformHasDual

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The clean-witness adversary

An oriented dual for clean infix.  A positive word `x` with chosen witness
`[l, r]`, `G = r − l`, carries
* interior vectors `G⁻¹·χ_{[l,r)}` at every position strictly inside the witness,
* the saturation vector `satA m G` at `l` (left copy) and at `r` (right copy).
A negative word `y` carries
* at every `1` inside a gap `[a, b)` the vector `h⁻¹·χ_{[a,b)}`, `h` the number
  of `1`s in the gap,
* the boundary corrections `alpha y q · satB m (D_L q)` and
  `beta y q · satB m (D_R q)`, or `satBInf` everywhere when `y` has no `2`.

The filtered inner product of a positive and a negative word is exactly `1`
(`filteredSum_eq_one`): the interior part is `(1/G)·∑_{t ∈ [l,r)} phi t` after
exchanging the two sums, and `completion` finishes.  The loads are
`O(λ(m))` and `O(m·λ(m))`, so `hasDual_of_oriented` gives
`ADV±(Inf_m) ≤ 11·√m·λ(m)` (`hasDual_inf`).
-/

namespace MonoidProduct.Infix

open Finset QuantumQueryComplexity

variable {m : ℕ}

/-- The coordinates: positions, and two copies of the saturation kernel. -/
abbrev DIdx (m : ℕ) := Fin m ⊕ SatIdx m ⊕ SatIdx m

/-- The left end of the chosen witness (`0` for a negative word). -/
noncomputable def wl (x : Word m) : ℕ := if h : inf m x = true then (witness h).1 else 0

/-- The right end of the chosen witness. -/
noncomputable def wr (x : Word m) : ℕ := if h : inf m x = true then (witness h).2 else 0

lemma wl_lt_wr {x : Word m} (h : inf m x = true) : wl x < wr x := by
  unfold wl wr; rw [dif_pos h, dif_pos h]; exact (witness_spec h).1

lemma wr_lt {x : Word m} (h : inf m x = true) : wr x < m := by
  unfold wr; rw [dif_pos h]; exact (witness h).2.isLt

lemma wl_eq {x : Word m} (h : inf m x = true) : wl x = (witness h).1 := by
  unfold wl; rw [dif_pos h]

lemma wr_eq {x : Word m} (h : inf m x = true) : wr x = (witness h).2 := by
  unfold wr; rw [dif_pos h]

lemma x_wl {x : Word m} (h : inf m x = true) : x ⟨wl x, (wl_lt_wr h).trans (wr_lt h)⟩ = 2 := by
  have := (witness_spec h).2.1
  rw [show (⟨wl x, (wl_lt_wr h).trans (wr_lt h)⟩ : Fin m) = (witness h).1 from
    Fin.ext (wl_eq h)]
  exact this

lemma x_wr {x : Word m} (h : inf m x = true) : x ⟨wr x, wr_lt h⟩ = 2 := by
  have := (witness_spec h).2.2.1
  rw [show (⟨wr x, wr_lt h⟩ : Fin m) = (witness h).2 from Fin.ext (wr_eq h)]
  exact this

lemma x_mid {x : Word m} (h : inf m x = true) (q : Fin m) (h1 : wl x < q) (h2 : (q : ℕ) < wr x) :
    x q = 0 := by
  have := (witness_spec h).2.2.2 q
  exact this (Fin.lt_def.2 (by rw [← wl_eq h]; exact h1))
    (Fin.lt_def.2 (by rw [← wr_eq h]; exact h2))

/-- `y` has some `2`. -/
def HasTwo (y : Word m) : Prop := ∃ p : Fin m, y p = 2

instance (y : Word m) : Decidable (HasTwo y) := by unfold HasTwo; infer_instance

lemma hasTwo_iff {y : Word m} : HasTwo y ↔ ∃ p, isTwo y p :=
  ⟨fun ⟨p, hp⟩ => ⟨p, p.isLt, hp⟩, fun ⟨p, hp, h2⟩ => ⟨⟨p, hp⟩, h2⟩⟩

lemma not_hasTwoLE_of_not_hasTwo {y : Word m} (h : ¬ HasTwo y) (t : ℕ) : ¬ HasTwoLE y t :=
  fun ⟨p, _, h2⟩ => h (hasTwo_iff.2 ⟨p, h2⟩)

lemma not_isTwo_of_not_hasTwo {y : Word m} (h : ¬ HasTwo y) (t : ℕ) : ¬ isTwo y t :=
  fun h2 => h (hasTwo_iff.2 ⟨t, h2⟩)

/-- The positive vectors. -/
noncomputable def uVec (x : Word m) (q : Fin m) : DIdx m → ℝ
  | Sum.inl t =>
      if wl x < q ∧ (q : ℕ) < wr x ∧ wl x ≤ t ∧ (t : ℕ) < wr x
      then 1 / ((wr x - wl x : ℕ) : ℝ) else 0
  | Sum.inr (Sum.inl s) => if (q : ℕ) = wl x then satA m (wr x - wl x) s else 0
  | Sum.inr (Sum.inr s) => if (q : ℕ) = wr x then satA m (wr x - wl x) s else 0

/-- A position of `y` carrying a `1` inside a gap. -/
def InGap (y : Word m) (q : ℕ) : Prop := isOne y q ∧ HasTwoLE y q ∧ HasTwoGT y q

instance (y : Word m) (q : ℕ) : Decidable (InGap y q) := by unfold InGap; infer_instance

/-- The negative vectors. -/
noncomputable def vVec (y : Word m) (q : Fin m) : DIdx m → ℝ
  | Sum.inl t =>
      if InGap y q ∧ lastTwoLE y q ≤ t ∧ (t : ℕ) < firstTwoGT y q
      then 1 / (ones y (lastTwoLE y q) (firstTwoGT y q) : ℝ) else 0
  | Sum.inr (Sum.inl s) =>
      if HasTwo y then alpha y q * satB m (max 1 (DL y q)) s else satBInf m s
  | Sum.inr (Sum.inr s) => if HasTwo y then beta y q * satB m (max 1 (DR y q)) s else 0

/-! ## Counting the `1`s of a gap through the position they sit at -/

/-- The positions of `y` in `t`'s gap: a `1` in a gap whose interval contains `t`
is a `1` strictly inside `(lastTwoLE t, firstTwoGT t)`, and conversely. -/
lemma inGap_and_mem_iff {y : Word m} {q : Fin m} {t : ℕ} :
    (InGap y q ∧ lastTwoLE y q ≤ t ∧ t < firstTwoGT y q)
      ↔ (isOne y q ∧ HasTwoLE y t ∧ HasTwoGT y t
          ∧ lastTwoLE y t < q ∧ (q : ℕ) < firstTwoGT y t) := by
  constructor
  · rintro ⟨⟨h1, hL, hG⟩, hat, htb⟩
    have hq2 : ¬ isTwo y q := not_isTwo_of_isOne h1
    have hlt : lastTwoLE y q < q := lastTwoLE_lt_of_not_isTwo hL hq2
    have hgt : (q : ℕ) < firstTwoGT y q := lt_firstTwoGT y q q.isLt
    have hno : ∀ p, lastTwoLE y q < p → p < firstTwoGT y q → ¬ isTwo y p :=
      fun p h1 h2 => not_isTwo_of_mem_gap h1 h2
    -- `t` lies in `[a, b)`, so its gap data is `(a, b)`
    have hA : isTwo y (lastTwoLE y q) := isTwo_lastTwoLE hL
    have hLt : HasTwoLE y t := ⟨_, hat, hA⟩
    have hGt : HasTwoGT y t := ⟨_, htb, isTwo_firstTwoGT hG⟩
    obtain ⟨-, eA⟩ := lastTwoLE_eq_of_no_two (y := y) hat (fun p h1 h2 => hno p h1 (by omega))
    obtain ⟨-, eB⟩ := firstTwoGT_eq_of_no_two (y := y) hat (fun p h1 h2 => hno p h1 (by omega))
    have hAA : lastTwoLE y (lastTwoLE y q) = lastTwoLE y q :=
      le_antisymm (lastTwoLE_le _ _) (le_lastTwoLE le_rfl hA)
    obtain ⟨-, eBq⟩ := firstTwoGT_eq_of_no_two (y := y) hlt.le
      (fun p h1 h2 => hno p h1 (by omega))
    refine ⟨h1, hLt, hGt, ?_, ?_⟩
    · rw [eA, hAA]; exact hlt
    · rw [eB, ← eBq]; exact hgt
  · rintro ⟨h1, hL, hG, hq1, hq2⟩
    obtain ⟨hLq, hGq, eA, eB⟩ := gap_eq_of_mem hL hG hq1 hq2
    refine ⟨⟨h1, hLq, hGq⟩, ?_, ?_⟩
    · rw [eA]; exact lastTwoLE_le y t
    · rw [eB]; exact lt_firstTwoGT y t (lt_m_of_hasTwoGT hG)

/-- The number of `1`s of `y` in `t`'s gap satisfying a position predicate. -/
lemma card_inGap {y : Word m} {t : ℕ} (hL : HasTwoLE y t) (hG : HasTwoGT y t)
    (P : ℕ → Prop) [DecidablePred P] :
    ((univ : Finset (Fin m)).filter (fun q : Fin m => (InGap y q ∧ lastTwoLE y q ≤ t
        ∧ t < firstTwoGT y q) ∧ P (q : ℕ))).card
      = ((Ioo (lastTwoLE y t) (firstTwoGT y t)).filter (fun p => isOne y p ∧ P p)).card := by
  classical
  rw [← Finset.card_map (Fin.valEmbedding)]
  congr 1
  ext p
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ioo]
  constructor
  · rintro ⟨q, ⟨hq, hP⟩, rfl⟩
    obtain ⟨h1, -, -, hq1, hq2⟩ := inGap_and_mem_iff.1 hq
    exact ⟨⟨hq1, hq2⟩, h1, hP⟩
  · rintro ⟨⟨hq1, hq2⟩, h1, hP⟩
    refine ⟨⟨p, isOne_lt h1⟩, ⟨inGap_and_mem_iff.2 ⟨h1, hL, hG, hq1, hq2⟩, hP⟩, rfl⟩

/-- No `1` sits in a gap containing `t` unless `t` has a gap. -/
lemma not_inGap_of_no_gap {y : Word m} {t : ℕ} (h : ¬ (HasTwoLE y t ∧ HasTwoGT y t)) (q : Fin m) :
    ¬ (InGap y q ∧ lastTwoLE y q ≤ t ∧ t < firstTwoGT y q) := fun hq =>
  h ⟨(inGap_and_mem_iff.1 hq).2.1, (inGap_and_mem_iff.1 hq).2.2.1⟩

/-! ## The constraint -/

section Constraint

variable {x y : Word m}

lemma interior_term (q t : Fin m) :
    uVec x q (Sum.inl t) * vVec y q (Sum.inl t)
      = if (wl x < q ∧ (q : ℕ) < wr x ∧ wl x ≤ t ∧ (t : ℕ) < wr x)
          ∧ (InGap y q ∧ lastTwoLE y q ≤ t ∧ (t : ℕ) < firstTwoGT y q)
        then 1 / ((wr x - wl x : ℕ) : ℝ) * (1 / (ones y (lastTwoLE y q) (firstTwoGT y q) : ℝ))
        else 0 := by
  simp only [uVec, vVec]
  by_cases h1 : wl x < q ∧ (q : ℕ) < wr x ∧ wl x ≤ t ∧ (t : ℕ) < wr x <;>
    by_cases h2 : InGap y q ∧ lastTwoLE y q ≤ t ∧ (t : ℕ) < firstTwoGT y q
  · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
  · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2), mul_zero]
  · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1), zero_mul]
  · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1), zero_mul]

lemma interior_zero_of_eq (hx : inf m x = true) {q : Fin m} (hq : x q = y q) :
    ∑ t : Fin m, uVec x q (Sum.inl t) * vVec y q (Sum.inl t) = 0 := by
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [interior_term, if_neg]
  rintro ⟨⟨h1, h2, -, -⟩, ⟨⟨hone, -, -⟩, -, -⟩⟩
  have h0 := x_mid hx q h1 h2
  obtain ⟨_, h1'⟩ := hone
  simp only [Fin.eta] at h1'
  rw [h0, h1'] at hq
  exact absurd hq (by decide)

/-- The interior contribution at a fixed position `t`. -/
lemma interior_at (_hx : inf m x = true) (_hy : inf m y = false) (t : Fin m) :
    ∑ q : Fin m, uVec x q (Sum.inl t) * vVec y q (Sum.inl t)
      = if wl x ≤ t ∧ (t : ℕ) < wr x
        then 1 / ((wr x - wl x : ℕ) : ℝ) * phi y (wl x) (wr x) t else 0 := by
  classical
  simp only [interior_term]
  by_cases ht : wl x ≤ t ∧ (t : ℕ) < wr x
  · rw [if_pos ht]
    by_cases hgap : HasTwoLE y t ∧ HasTwoGT y t
    · -- every contributing `q` has `t`'s gap
      have hterm : ∀ q : Fin m,
          (if (wl x < q ∧ (q : ℕ) < wr x ∧ wl x ≤ t ∧ (t : ℕ) < wr x)
              ∧ (InGap y q ∧ lastTwoLE y q ≤ t ∧ (t : ℕ) < firstTwoGT y q)
            then 1 / ((wr x - wl x : ℕ) : ℝ) * (1 / (ones y (lastTwoLE y q) (firstTwoGT y q) : ℝ))
            else 0)
          = if (InGap y q ∧ lastTwoLE y q ≤ t ∧ (t : ℕ) < firstTwoGT y q)
              ∧ (wl x < q ∧ (q : ℕ) < wr x)
            then 1 / ((wr x - wl x : ℕ) : ℝ) * (1 / (ones y (lastTwoLE y t) (firstTwoGT y t) : ℝ))
            else 0 := by
        intro q
        by_cases hc : (InGap y q ∧ lastTwoLE y q ≤ t ∧ (t : ℕ) < firstTwoGT y q)
            ∧ (wl x < q ∧ (q : ℕ) < wr x)
        · rw [if_pos hc, if_pos ⟨⟨hc.2.1, hc.2.2, ht.1, ht.2⟩, hc.1⟩]
          obtain ⟨h1, hL, hG, hq1, hq2⟩ := inGap_and_mem_iff.1 hc.1
          obtain ⟨-, -, eA, eB⟩ := gap_eq_of_mem hL hG hq1 hq2
          rw [eA, eB]
        · rw [if_neg hc, if_neg]
          rintro ⟨⟨a1, a2, -, -⟩, b⟩
          exact hc ⟨b, a1, a2⟩
      rw [Finset.sum_congr rfl fun q _ => hterm q, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, card_inGap hgap.1 hgap.2 (fun p => wl x < p ∧ p < wr x)]
      unfold phi
      rw [if_pos hgap]
      have hfilt : (Ioo (lastTwoLE y t) (firstTwoGT y t)).filter
            (fun p => isOne y p ∧ (wl x < p ∧ p < wr x))
          = (Ioo (max (wl x) (lastTwoLE y t)) (min (wr x) (firstTwoGT y t))).filter (isOne y) := by
        ext p
        simp only [mem_filter, mem_Ioo]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega⟩, h3, by omega, by omega⟩
      rw [hfilt]
      unfold ones
      ring
    · rw [Finset.sum_eq_zero fun q _ => ?_]
      · unfold phi; rw [if_neg hgap]; ring
      · rw [if_neg]
        rintro ⟨-, hq⟩
        exact not_inGap_of_no_gap hgap q hq
  · rw [if_neg ht]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    rintro ⟨⟨-, -, h3, h4⟩, -⟩
    exact ht ⟨h3, h4⟩

/-- **The interior part** is `(1/G)·∑_{t ∈ [l,r)} phi t`. -/
lemma interior_sum (hx : inf m x = true) (hy : inf m y = false) :
    ∑ q : Fin m, ∑ t : Fin m, uVec x q (Sum.inl t) * vVec y q (Sum.inl t)
      = (∑ t ∈ Ico (wl x) (wr x), phi y (wl x) (wr x) t) / ((wr x - wl x : ℕ) : ℝ) := by
  classical
  rw [Finset.sum_comm]
  simp only [interior_at hx hy]
  rw [Fin.sum_univ_eq_sum_range (fun t => if wl x ≤ t ∧ t < wr x
    then 1 / ((wr x - wl x : ℕ) : ℝ) * phi y (wl x) (wr x) t else 0) m, ← Finset.sum_filter]
  have hfilt : (range m).filter (fun t => wl x ≤ t ∧ t < wr x) = Ico (wl x) (wr x) := by
    ext t
    simp only [mem_filter, mem_range, mem_Ico]
    have := wr_lt hx
    omega
  rw [hfilt, ← Finset.mul_sum]
  ring

/-- **The left part**. -/
lemma left_sum (hx : inf m x = true) (_hy : inf m y = false) :
    (∑ q : Fin m, if x q = y q then 0
        else ∑ s, uVec x q (Sum.inr (Sum.inl s)) * vVec y q (Sum.inr (Sum.inl s)))
      = if HasTwo y then alpha y (wl x) * min 1 ((DL y (wl x) : ℝ) / ((wr x - wl x : ℕ) : ℝ))
        else 1 := by
  classical
  have hl : wl x < m := (wl_lt_wr hx).trans (wr_lt hx)
  have hG1 : 1 ≤ wr x - wl x := by have := wl_lt_wr hx; omega
  have hGm : wr x - wl x ≤ m := by have := wr_lt hx; omega
  rw [Finset.sum_eq_single ⟨wl x, hl⟩]
  · simp only [uVec, if_true]
    by_cases h2 : HasTwo y
    · rw [if_pos h2]
      simp only [vVec, h2, if_true]
      by_cases hl2 : isTwo y (wl x)
      · -- both letters are `2`: the filter kills the term, and `alpha = 0`
        have hy2 : y ⟨wl x, hl⟩ = 2 := hl2.2
        rw [if_pos (by rw [x_wl hx, hy2]), alpha, if_pos (Or.inl hl2), zero_mul]
      · have hne : x ⟨wl x, hl⟩ ≠ y ⟨wl x, hl⟩ := by
          rw [x_wl hx]; intro h; exact hl2 ⟨hl, h.symm⟩
        rw [if_neg hne]
        rw [show (∑ s, satA m (wr x - wl x) s * (alpha y (wl x) * satB m (max 1 (DL y (wl x))) s))
            = alpha y (wl x) * ∑ s, satA m (wr x - wl x) s * satB m (max 1 (DL y (wl x))) s by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring]
        by_cases hG : HasTwoGT y (wl x)
        · have hDL1 : 1 ≤ DL y (wl x) := by
            unfold DL; have := lt_firstTwoGT y (wl x) hl; omega
          have hDLm : DL y (wl x) ≤ m := by unfold DL; have := firstTwoGT_le_m y (wl x); omega
          rw [max_eq_right hDL1, satA_mul_satB hG1 hGm hDL1 hDLm]
        · rw [alpha, if_pos (Or.inr hG), zero_mul, zero_mul]
    · rw [if_neg h2]
      simp only [vVec, h2, if_false]
      have hne : x ⟨wl x, hl⟩ ≠ y ⟨wl x, hl⟩ := by
        rw [x_wl hx]; intro h; exact h2 ⟨_, h.symm⟩
      rw [if_neg hne]
      exact satA_mul_satBInf hGm
  · intro q _ hq
    split_ifs
    · rfl
    · refine Finset.sum_eq_zero fun s _ => ?_
      simp only [uVec]
      rw [if_neg (fun h => hq (Fin.ext h)), zero_mul]
  · intro h; exact absurd (mem_univ _) h

/-- **The right part**. -/
lemma right_sum (hx : inf m x = true) (_hy : inf m y = false) :
    (∑ q : Fin m, if x q = y q then 0
        else ∑ s, uVec x q (Sum.inr (Sum.inr s)) * vVec y q (Sum.inr (Sum.inr s)))
      = if HasTwo y then beta y (wr x) * min 1 ((DR y (wr x) : ℝ) / ((wr x - wl x : ℕ) : ℝ))
        else 0 := by
  classical
  have hr : wr x < m := wr_lt hx
  have hG1 : 1 ≤ wr x - wl x := by have := wl_lt_wr hx; omega
  have hGm : wr x - wl x ≤ m := by omega
  rw [Finset.sum_eq_single ⟨wr x, hr⟩]
  · simp only [uVec, if_true]
    by_cases h2 : HasTwo y
    · rw [if_pos h2]
      simp only [vVec, h2, if_true]
      by_cases hr2 : isTwo y (wr x)
      · have hy2 : y ⟨wr x, hr⟩ = 2 := hr2.2
        rw [if_pos (by rw [x_wr hx, hy2]), beta, if_pos (Or.inl hr2), zero_mul]
      · have hne : x ⟨wr x, hr⟩ ≠ y ⟨wr x, hr⟩ := by
          rw [x_wr hx]; intro h; exact hr2 ⟨hr, h.symm⟩
        rw [if_neg hne]
        rw [show (∑ s, satA m (wr x - wl x) s * (beta y (wr x) * satB m (max 1 (DR y (wr x))) s))
            = beta y (wr x) * ∑ s, satA m (wr x - wl x) s * satB m (max 1 (DR y (wr x))) s by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring]
        by_cases hL : HasTwoLE y (wr x)
        · have hDR1 : 1 ≤ DR y (wr x) := by
            unfold DR; have := lastTwoLE_lt_of_not_isTwo hL hr2; omega
          have hDRm : DR y (wr x) ≤ m := by unfold DR; omega
          rw [max_eq_right hDR1, satA_mul_satB hG1 hGm hDR1 hDRm]
        · rw [beta, if_pos (Or.inr hL), zero_mul, zero_mul]
    · rw [if_neg h2]
      simp only [vVec, h2, if_false, mul_zero, Finset.sum_const_zero, ite_self]
  · intro q _ hq
    split_ifs
    · rfl
    · refine Finset.sum_eq_zero fun s _ => ?_
      simp only [uVec]
      rw [if_neg (fun h => hq (Fin.ext h)), zero_mul]
  · intro h; exact absurd (mem_univ _) h

/-- **The oriented constraint**: every positive–negative pair has filtered
inner product one. -/
theorem filteredSum_eq_one (hx : inf m x = true) (hy : inf m y = false) :
    filteredSum (uVec (m := m)) (vVec (m := m)) x y = 1 := by
  classical
  unfold filteredSum
  have hsplit : ∀ q : Fin m, (if x q = y q then (0 : ℝ) else ∑ k, uVec x q k * vVec y q k)
      = (∑ t : Fin m, uVec x q (Sum.inl t) * vVec y q (Sum.inl t))
        + (if x q = y q then 0
            else ∑ s, uVec x q (Sum.inr (Sum.inl s)) * vVec y q (Sum.inr (Sum.inl s)))
        + (if x q = y q then 0
            else ∑ s, uVec x q (Sum.inr (Sum.inr s)) * vVec y q (Sum.inr (Sum.inr s))) := by
    intro q
    by_cases hq : x q = y q
    · rw [if_pos hq, if_pos hq, if_pos hq, interior_zero_of_eq hx hq]; ring
    · rw [if_neg hq, if_neg hq, if_neg hq, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [interior_sum hx hy, left_sum hx hy, right_sum hx hy]
  by_cases h2 : HasTwo y
  · rw [if_pos h2, if_pos h2]
    exact completion hy (hasTwo_iff.1 h2) (wl_lt_wr hx) (wr_lt hx)
  · rw [if_neg h2, if_neg h2]
    have hzero : ∀ t ∈ Ico (wl x) (wr x), phi y (wl x) (wr x) t = 0 := fun t _ => by
      unfold phi
      rw [if_neg (fun h => not_hasTwoLE_of_not_hasTwo h2 t h.1)]
    rw [Finset.sum_eq_zero hzero, zero_div]
    ring

end Constraint

/-! ## The loads -/

section Loads

/-- A count of positions in a half-open window, as a sum over the coordinates. -/
lemma sum_ite_Ico (N a b : ℕ) (hb : b ≤ N) :
    ∑ t : Fin N, (if a ≤ (t : ℕ) ∧ (t : ℕ) < b then (1 : ℝ) else 0) = ((b - a : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if a ≤ t ∧ t < b then (1 : ℝ) else 0) N,
    Finset.sum_boole]
  congr 1
  rw [← Nat.card_Ico a b]
  congr 1
  ext t
  simp only [mem_filter, mem_range, mem_Ico]
  omega

lemma sum_ite_Ioo (N a b : ℕ) (hb : b ≤ N) :
    ∑ t : Fin N, (if a < (t : ℕ) ∧ (t : ℕ) < b then (1 : ℝ) else 0) = ((b - a - 1 : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if a < t ∧ t < b then (1 : ℝ) else 0) N,
    Finset.sum_boole]
  congr 1
  rw [← Nat.card_Ioo a b]
  congr 1
  ext t
  simp only [mem_filter, mem_range, mem_Ioo]
  omega

variable {x y : Word m}

/-- **The positive load** is at most `15·λ(m)`. -/
theorem uVec_load (hx : inf m x = true) :
    ∑ q : Fin m, ∑ k, uVec x q k * uVec x q k ≤ 15 * lam m := by
  classical
  have hG1 : 1 ≤ wr x - wl x := by have := wl_lt_wr hx; omega
  have hGm : wr x - wl x ≤ m := by have := wr_lt hx; omega
  have hGr : (0 : ℝ) < ((wr x - wl x : ℕ) : ℝ) := by exact_mod_cast hG1
  have hsplit : ∀ q : Fin m, ∑ k, uVec x q k * uVec x q k
      = (∑ t : Fin m, uVec x q (Sum.inl t) * uVec x q (Sum.inl t))
        + (∑ s, uVec x q (Sum.inr (Sum.inl s)) * uVec x q (Sum.inr (Sum.inl s)))
        + (∑ s, uVec x q (Sum.inr (Sum.inr s)) * uVec x q (Sum.inr (Sum.inr s))) := fun q => by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  simp only [hsplit, Finset.sum_add_distrib]
  -- interior
  have hint : ∑ q : Fin m, ∑ t : Fin m, uVec x q (Sum.inl t) * uVec x q (Sum.inl t) ≤ 1 := by
    have hq : ∀ q : Fin m, ∑ t : Fin m, uVec x q (Sum.inl t) * uVec x q (Sum.inl t)
        = if wl x < q ∧ (q : ℕ) < wr x then 1 / ((wr x - wl x : ℕ) : ℝ) else 0 := by
      intro q
      simp only [uVec]
      by_cases hq : wl x < q ∧ (q : ℕ) < wr x
      · rw [if_pos hq]
        have : ∀ t : Fin m, (if wl x < q ∧ (q : ℕ) < wr x ∧ wl x ≤ t ∧ (t : ℕ) < wr x
              then 1 / ((wr x - wl x : ℕ) : ℝ) else 0)
            * (if wl x < q ∧ (q : ℕ) < wr x ∧ wl x ≤ t ∧ (t : ℕ) < wr x
              then 1 / ((wr x - wl x : ℕ) : ℝ) else 0)
            = 1 / ((wr x - wl x : ℕ) : ℝ) ^ 2
              * (if wl x ≤ (t : ℕ) ∧ (t : ℕ) < wr x then (1 : ℝ) else 0) := by
          intro t
          by_cases ht : wl x ≤ (t : ℕ) ∧ (t : ℕ) < wr x
          · rw [if_pos ⟨hq.1, hq.2, ht⟩, if_pos ht]; ring
          · rw [if_neg (fun h => ht ⟨h.2.2.1, h.2.2.2⟩), if_neg ht]; ring
        rw [Finset.sum_congr rfl fun t _ => this t, ← Finset.mul_sum,
          sum_ite_Ico _ _ _ (wr_lt hx).le]
        field_simp
      · rw [if_neg hq]
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [if_neg (fun h => hq ⟨h.1, h.2.1⟩), zero_mul]
    rw [Finset.sum_congr rfl fun q _ => hq q, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    have hcard : (((univ : Finset (Fin m)).filter fun q : Fin m => wl x < q ∧ (q : ℕ) < wr x).card
        : ℝ) = ((wr x - wl x - 1 : ℕ) : ℝ) := by
      rw [← sum_ite_Ioo m (wl x) (wr x) (wr_lt hx).le, Finset.sum_boole]
    rw [hcard, div_eq_mul_inv, one_mul, ← div_eq_mul_inv, div_le_one hGr]
    exact_mod_cast Nat.sub_le _ _
  -- the two boundary copies
  have hleft : ∑ q : Fin m, ∑ s, uVec x q (Sum.inr (Sum.inl s)) * uVec x q (Sum.inr (Sum.inl s))
      ≤ 7 * lam m := by
    rw [Finset.sum_eq_single ⟨wl x, (wl_lt_wr hx).trans (wr_lt hx)⟩]
    · simp only [uVec, if_true]
      exact satA_sq_le hG1 hGm
    · intro q _ hq
      refine Finset.sum_eq_zero fun s _ => ?_
      simp only [uVec]
      rw [if_neg (fun h => hq (Fin.ext h)), zero_mul]
    · intro h; exact absurd (mem_univ _) h
  have hright : ∑ q : Fin m, ∑ s, uVec x q (Sum.inr (Sum.inr s)) * uVec x q (Sum.inr (Sum.inr s))
      ≤ 7 * lam m := by
    rw [Finset.sum_eq_single ⟨wr x, wr_lt hx⟩]
    · simp only [uVec, if_true]
      exact satA_sq_le hG1 hGm
    · intro q _ hq
      refine Finset.sum_eq_zero fun s _ => ?_
      simp only [uVec]
      rw [if_neg (fun h => hq (Fin.ext h)), zero_mul]
    · intro h; exact absurd (mem_univ _) h
  have := two_le_lam m
  linarith

/-- The interior load of a negative word at one position `t`. -/
lemma vVec_interior_at (hy : inf m y = false) (t : Fin m) :
    ∑ q : Fin m, vVec y q (Sum.inl t) * vVec y q (Sum.inl t) ≤ 1 := by
  classical
  by_cases hgap : HasTwoLE y t ∧ HasTwoGT y t
  · have hpos : 0 < ones y (lastTwoLE y t) (firstTwoGT y t) := ones_gap_pos hy hgap.1 hgap.2
    have hposr : (0 : ℝ) < ones y (lastTwoLE y t) (firstTwoGT y t) := by exact_mod_cast hpos
    have hterm : ∀ q : Fin m, vVec y q (Sum.inl t) * vVec y q (Sum.inl t)
        ≤ if (InGap y q ∧ lastTwoLE y q ≤ t ∧ (t : ℕ) < firstTwoGT y q) ∧ True
          then 1 / (ones y (lastTwoLE y t) (firstTwoGT y t) : ℝ) else 0 := by
      intro q
      simp only [vVec, and_true]
      by_cases hc : InGap y q ∧ lastTwoLE y q ≤ t ∧ (t : ℕ) < firstTwoGT y q
      · rw [if_pos hc, if_pos hc]
        obtain ⟨h1, hL, hG, hq1, hq2⟩ := inGap_and_mem_iff.1 hc
        obtain ⟨-, -, eA, eB⟩ := gap_eq_of_mem hL hG hq1 hq2
        rw [eA, eB]
        have h1' : (1 : ℝ) ≤ ones y (lastTwoLE y t) (firstTwoGT y t) := by exact_mod_cast hpos
        rw [← sq, div_pow, one_pow]
        exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by nlinarith)
      · rw [if_neg hc, if_neg hc]; norm_num
    refine (Finset.sum_le_sum fun q _ => hterm q).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_inGap hgap.1 hgap.2 (fun _ => True)]
    simp only [and_true]
    rw [div_eq_mul_inv, one_mul, ← div_eq_mul_inv, div_le_one hposr]
    rfl
  · rw [Finset.sum_eq_zero]
    · norm_num
    intro q _
    simp only [vVec]
    rw [if_neg (not_inGap_of_no_gap hgap q)]; norm_num

/-- **The negative load** is at most `7·m·λ(m)`. -/
theorem vVec_load (hy : inf m y = false) :
    ∑ q : Fin m, ∑ k, vVec y q k * vVec y q k ≤ 7 * m * lam m := by
  classical
  have hsplit : ∀ q : Fin m, ∑ k, vVec y q k * vVec y q k
      = (∑ t : Fin m, vVec y q (Sum.inl t) * vVec y q (Sum.inl t))
        + (∑ s, vVec y q (Sum.inr (Sum.inl s)) * vVec y q (Sum.inr (Sum.inl s)))
        + (∑ s, vVec y q (Sum.inr (Sum.inr s)) * vVec y q (Sum.inr (Sum.inr s))) := fun q => by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  simp only [hsplit, Finset.sum_add_distrib]
  have hint : ∑ q : Fin m, ∑ t : Fin m, vVec y q (Sum.inl t) * vVec y q (Sum.inl t) ≤ m := by
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun t _ => vVec_interior_at hy t).trans ?_
    rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hDL : ∀ q : Fin m, 1 ≤ max 1 (DL y q) ∧ max 1 (DL y q) ≤ m := fun q =>
    ⟨le_max_left _ _, max_le q.pos (by unfold DL; have := firstTwoGT_le_m y q; omega)⟩
  have hDR : ∀ q : Fin m, 1 ≤ max 1 (DR y q) ∧ max 1 (DR y q) ≤ m := fun q =>
    ⟨le_max_left _ _, max_le q.pos (by unfold DR; have := q.isLt; omega)⟩
  have hleft : ∑ q : Fin m, ∑ s, vVec y q (Sum.inr (Sum.inl s)) * vVec y q (Sum.inr (Sum.inl s))
      ≤ m * (3 * lam m) := by
    refine (Finset.sum_le_sum (g := fun _ => 3 * lam m) fun q _ => ?_).trans
      (le_of_eq (by rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]))
    · exact (show ∑ s, vVec y q (Sum.inr (Sum.inl s)) * vVec y q (Sum.inr (Sum.inl s))
          ≤ 3 * lam m from by
        simp only [vVec]
        by_cases h2 : HasTwo y
        · simp only [h2, if_true]
          have : ∑ s, alpha y q * satB m (max 1 (DL y q)) s
                * (alpha y q * satB m (max 1 (DL y q)) s)
              = alpha y q * alpha y q
                * ∑ s, satB m (max 1 (DL y q)) s * satB m (max 1 (DL y q)) s := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
          rw [this]
          have ha0 := alpha_nonneg y q
          have ha1 := alpha_le_one hy q
          have hs := satB_sq_le (m := m) (hDL q).1 (hDL q).2
          have hs0 : 0 ≤ ∑ s, satB m (max 1 (DL y q)) s * satB m (max 1 (DL y q)) s :=
            Finset.sum_nonneg fun s _ => mul_self_nonneg _
          calc alpha y q * alpha y q * ∑ s, satB m (max 1 (DL y q)) s * satB m (max 1 (DL y q)) s
              ≤ 1 * ∑ s, satB m (max 1 (DL y q)) s * satB m (max 1 (DL y q)) s :=
                mul_le_mul_of_nonneg_right (by nlinarith) hs0
            _ ≤ 3 * lam m := by rw [one_mul]; exact hs
        · simp only [h2, if_false]
          exact satBInf_sq_le)
  have hright : ∑ q : Fin m, ∑ s, vVec y q (Sum.inr (Sum.inr s)) * vVec y q (Sum.inr (Sum.inr s))
      ≤ m * (3 * lam m) := by
    refine (Finset.sum_le_sum (g := fun _ => 3 * lam m) fun q _ => ?_).trans
      (le_of_eq (by rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]))
    · exact (show ∑ s, vVec y q (Sum.inr (Sum.inr s)) * vVec y q (Sum.inr (Sum.inr s))
          ≤ 3 * lam m from by
        simp only [vVec]
        by_cases h2 : HasTwo y
        · simp only [h2, if_true]
          have : ∑ s, beta y q * satB m (max 1 (DR y q)) s * (beta y q * satB m (max 1 (DR y q)) s)
              = beta y q * beta y q
                * ∑ s, satB m (max 1 (DR y q)) s * satB m (max 1 (DR y q)) s := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
          rw [this]
          have ha0 := beta_nonneg y q
          have ha1 := beta_le_one hy q
          have hs := satB_sq_le (m := m) (hDR q).1 (hDR q).2
          have hs0 : 0 ≤ ∑ s, satB m (max 1 (DR y q)) s * satB m (max 1 (DR y q)) s :=
            Finset.sum_nonneg fun s _ => mul_self_nonneg _
          calc beta y q * beta y q * ∑ s, satB m (max 1 (DR y q)) s * satB m (max 1 (DR y q)) s
              ≤ 1 * ∑ s, satB m (max 1 (DR y q)) s * satB m (max 1 (DR y q)) s :=
                mul_le_mul_of_nonneg_right (by nlinarith) hs0
            _ ≤ 3 * lam m := by rw [one_mul]; exact hs
        · simp only [h2, if_false, mul_zero, Finset.sum_const_zero]
          have := two_le_lam m; linarith)
  have := two_le_lam m
  have hm : (0 : ℝ) ≤ m := by positivity
  nlinarith

end Loads

/-! ## The theorem -/

/-- **Clean infix, dual form**: `ADV±(Inf_m) ≤ 11·√m·λ(m)`. -/
theorem hasDual_inf (m : ℕ) : HasDual (inf m) (11 * Real.sqrt m * lam m) := by
  have h := hasDual_of_oriented (inf m) (uVec (m := m)) (vVec (m := m))
    (fun x y hx hy => filteredSum_eq_one hx hy) (P := 15 * lam m) (N := 7 * m * lam m)
    (by have := two_le_lam m; positivity) (by have := two_le_lam m; positivity)
    (fun x hx => uVec_load hx) (fun y hy => vVec_load hy)
  refine h.mono ?_
  have hl := two_le_lam m
  have hm : (0 : ℝ) ≤ m := by positivity
  rw [show 15 * lam m * (7 * m * lam m) = (Real.sqrt m * lam m) ^ 2 * 105 by
    rw [mul_pow, Real.sq_sqrt hm]; ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]
  have h105 : Real.sqrt 105 ≤ 11 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc Real.sqrt m * lam m * Real.sqrt 105 ≤ Real.sqrt m * lam m * 11 :=
        mul_le_mul_of_nonneg_left h105 (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
    _ = 11 * Real.sqrt m * lam m := by ring

/-- **Clean infix, query bound**: `Q_{1/3}(Inf_m) ≤ 8192·(1 + 11·√m·λ(m))`. -/
theorem inf_qQuery_upper (m : ℕ) :
    (qQuery (inf m) (1 / 3) : ℝ) ≤ uniformExtractionConstant * (1 + 11 * Real.sqrt m * lam m) :=
  qQueryOn_third_le_of_hasDualOn_uniform (hasDual_inf m).hasDualOn
    (by have := two_le_lam m; positivity)

end MonoidProduct.Infix
