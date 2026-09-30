import MonoidProduct.Infix.Defs

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The gap structure of a negative word

A position `t` of a word `y` lies in the **gap** `[lastTwoLE y t, firstTwoGT y t)`
when a `2` occurs at or before it and another after it.  All positions of one
gap share the same endpoints (`gap_eq_of_mem`), and the gap's `1`s are counted
by `ones`.  The boundary corrections of the clean-witness adversary, `alpha` and `beta`, are the
fractions of the gap's `1`s at or before, respectively at or after, a position.

`completion` is the completion identity of that adversary in per-position form: for a clean
witness `[l, r]` of the positive word and a negative word `y` with some `2`,

  `(1/G)·∑_{t ∈ [l,r)} phi t + alpha l·min{1, D_L(l)/G} + beta r·min{1, D_R(r)/G} = 1`,

where `phi t` is the fraction of the `1`s of `t`'s gap that lie strictly inside
`(l, r)`.  Split `[l, r)` at the first `2` at or after `l` and the last `2` at
or before `r`: the middle positions have `phi = 1`, and each boundary piece
combines with its correction to its length over `G`.
-/

namespace MonoidProduct.Infix

open Finset

variable {m : ℕ}

/-! ## Same-gap lemmas -/

lemma hasTwoLE_of_le {y : Word m} {s t : ℕ} (h : HasTwoLE y s) (hst : s ≤ t) : HasTwoLE y t := by
  obtain ⟨p, hp, h2⟩ := h; exact ⟨p, hp.trans hst, h2⟩

lemma hasTwoGT_of_le {y : Word m} {s t : ℕ} (h : HasTwoGT y t) (hst : s ≤ t) : HasTwoGT y s := by
  obtain ⟨p, hp, h2⟩ := h; exact ⟨p, by omega, h2⟩

lemma lastTwoLE_lt_of_not_isTwo {y : Word m} {t : ℕ} (h : HasTwoLE y t) (h2 : ¬ isTwo y t) :
    lastTwoLE y t < t := by
  rcases lt_or_eq_of_le (lastTwoLE_le y t) with hlt | heq
  · exact hlt
  · exact absurd (heq ▸ isTwo_lastTwoLE h) h2

/-- No `2` strictly between the gap endpoints. -/
lemma not_isTwo_of_mem_gap {y : Word m} {t p : ℕ} (h1 : lastTwoLE y t < p)
    (h2 : p < firstTwoGT y t) :
    ¬ isTwo y p := by
  intro hp
  by_cases hpt : p ≤ t
  · exact not_isTwo_of_lastTwoLE_lt h1 hpt hp
  · exact not_isTwo_of_lt_firstTwoGT (by omega) h2 hp

lemma lt_m_of_hasTwoGT {y : Word m} {t : ℕ} (h : HasTwoGT y t) : t < m := by
  obtain ⟨p, hp, h2⟩ := h; have := isTwo_lt h2; omega

/-- Positions strictly inside the gap of `t` have the same gap. -/
lemma gap_eq_of_mem {y : Word m} {t q : ℕ} (hL : HasTwoLE y t) (hG : HasTwoGT y t)
    (h1 : lastTwoLE y t < q) (h2 : q < firstTwoGT y t) :
    HasTwoLE y q ∧ HasTwoGT y q ∧ lastTwoLE y q = lastTwoLE y t
      ∧ firstTwoGT y q = firstTwoGT y t := by
  have hA := isTwo_lastTwoLE hL
  have hB := isTwo_firstTwoGT hG
  have hLq : HasTwoLE y q := ⟨_, h1.le, hA⟩
  have hGq : HasTwoGT y q := ⟨_, h2, hB⟩
  refine ⟨hLq, hGq, le_antisymm ?_ (le_lastTwoLE h1.le hA), le_antisymm (firstTwoGT_le h2 hB) ?_⟩
  · by_contra hcon
    push Not at hcon
    exact not_isTwo_of_mem_gap hcon (lt_of_le_of_lt (lastTwoLE_le y q) h2) (isTwo_lastTwoLE hLq)
  · by_contra hcon
    push Not at hcon
    have hq : q < firstTwoGT y q := lt_firstTwoGT y q (lt_m_of_hasTwoGT hGq)
    exact not_isTwo_of_mem_gap (by omega : lastTwoLE y t < firstTwoGT y q) hcon
      (isTwo_firstTwoGT hGq)

/-- Positions at the end of a `2`-free stretch from `s` share `s`'s gap data. -/
lemma gap_eq_of_no_two {y : Word m} {s t : ℕ} (hst : s ≤ t)
    (hno : ∀ p, s ≤ p → p ≤ t → ¬ isTwo y p) :
    (HasTwoLE y t ↔ HasTwoLE y s) ∧ (HasTwoGT y t ↔ HasTwoGT y s)
      ∧ (HasTwoLE y s → lastTwoLE y t = lastTwoLE y s)
      ∧ (HasTwoGT y s → firstTwoGT y t = firstTwoGT y s) := by
  have hGT : HasTwoGT y s → t < firstTwoGT y s := by
    intro hG
    by_contra hle
    push Not at hle
    exact hno _ (lt_firstTwoGT y s (lt_m_of_hasTwoGT hG)).le hle (isTwo_firstTwoGT hG)
  refine ⟨⟨fun ⟨p, hp, h2⟩ => ⟨p, ?_, h2⟩, fun h => hasTwoLE_of_le h hst⟩,
    ⟨fun h => hasTwoGT_of_le h hst, fun hG => ⟨_, hGT hG, isTwo_firstTwoGT hG⟩⟩,
    fun hL => ?_, fun hG => ?_⟩
  · by_contra hcon; exact hno p (by omega) hp h2
  · apply le_antisymm
    · by_contra hcon
      push Not at hcon
      by_cases hs : s ≤ lastTwoLE y t
      · exact hno _ hs (lastTwoLE_le y t) (isTwo_lastTwoLE (hasTwoLE_of_le hL hst))
      · exact absurd (le_lastTwoLE (by omega) (isTwo_lastTwoLE (hasTwoLE_of_le hL hst)))
          (not_le.2 hcon)
    · exact le_lastTwoLE ((lastTwoLE_le y s).trans hst) (isTwo_lastTwoLE hL)
  · apply le_antisymm
    · exact firstTwoGT_le (hGT hG) (isTwo_firstTwoGT hG)
    · have hGt : HasTwoGT y t := ⟨_, hGT hG, isTwo_firstTwoGT hG⟩
      exact firstTwoGT_le (lt_of_le_of_lt hst (lt_firstTwoGT y t (lt_m_of_hasTwoGT hGt)))
        (isTwo_firstTwoGT hGt)

/-- After a `2`-free stretch `(s, t]` the next-`2` data of `t` is that of `s`. -/
lemma firstTwoGT_eq_of_no_two {y : Word m} {s t : ℕ} (hst : s ≤ t)
    (hno : ∀ p, s < p → p ≤ t → ¬ isTwo y p) :
    (HasTwoGT y t ↔ HasTwoGT y s) ∧ firstTwoGT y t = firstTwoGT y s := by
  have hGT : HasTwoGT y s → t < firstTwoGT y s := by
    intro hG
    by_contra hle
    push Not at hle
    exact hno _ (lt_firstTwoGT y s (lt_m_of_hasTwoGT hG)) hle (isTwo_firstTwoGT hG)
  have hiff : HasTwoGT y t ↔ HasTwoGT y s :=
    ⟨fun h => hasTwoGT_of_le h hst, fun hG => ⟨_, hGT hG, isTwo_firstTwoGT hG⟩⟩
  refine ⟨hiff, ?_⟩
  by_cases hG : HasTwoGT y s
  · apply le_antisymm
    · exact firstTwoGT_le (hGT hG) (isTwo_firstTwoGT hG)
    · have hGt : HasTwoGT y t := hiff.2 hG
      exact firstTwoGT_le (lt_of_le_of_lt hst (lt_firstTwoGT y t (lt_m_of_hasTwoGT hGt)))
        (isTwo_firstTwoGT hGt)
  · have hGt : ¬ HasTwoGT y t := fun h => hG (hiff.1 h)
    unfold firstTwoGT
    rw [dif_neg hGt, dif_neg hG]

/-- After a `2`-free stretch `(s, t]` the last-`2` data of `t` is that of `s`. -/
lemma lastTwoLE_eq_of_no_two {y : Word m} {s t : ℕ} (hst : s ≤ t)
    (hno : ∀ p, s < p → p ≤ t → ¬ isTwo y p) :
    (HasTwoLE y t ↔ HasTwoLE y s) ∧ lastTwoLE y t = lastTwoLE y s := by
  have hiff : HasTwoLE y t ↔ HasTwoLE y s := by
    refine ⟨fun ⟨p, hp, h2⟩ => ⟨p, ?_, h2⟩, fun h => hasTwoLE_of_le h hst⟩
    by_contra hcon; exact hno p (by omega) hp h2
  refine ⟨hiff, ?_⟩
  by_cases hL : HasTwoLE y s
  · apply le_antisymm
    · by_contra hcon
      push Not at hcon
      have hLt := hiff.2 hL
      by_cases hs : s < lastTwoLE y t
      · exact hno _ hs (lastTwoLE_le y t) (isTwo_lastTwoLE hLt)
      · exact absurd (le_lastTwoLE (by omega) (isTwo_lastTwoLE hLt)) (not_le.2 hcon)
    · exact le_lastTwoLE ((lastTwoLE_le y s).trans hst) (isTwo_lastTwoLE hL)
  · have hLt : ¬ HasTwoLE y t := fun h => hL (hiff.1 h)
    have h1 : lastTwoLE y t = 0 := Nat.findGreatest_eq_zero_iff.2 fun p _ hp h2 =>
      hLt ⟨p, hp, h2⟩
    have h2 : lastTwoLE y s = 0 := Nat.findGreatest_eq_zero_iff.2 fun p _ hp h2 =>
      hL ⟨p, hp, h2⟩
    rw [h1, h2]

/-! ## Splitting the `1`-counts -/

lemma ones_split {y : Word m} {a c b : ℕ} (h1 : a < c) (h2 : c < b) :
    ones y a b = ones y a (c + 1) + ones y c b := by
  unfold ones
  rw [← card_union_of_disjoint]
  · congr 1
    ext p
    simp only [mem_filter, mem_union, mem_Ioo]
    by_cases hone : isOne y p
    · simp only [hone, and_true]; omega
    · simp only [hone, and_false, or_self]
  · rw [disjoint_left]
    intro p hp hp'
    obtain ⟨hp, -⟩ := mem_filter.1 hp
    obtain ⟨hp', -⟩ := mem_filter.1 hp'
    rw [mem_Ioo] at hp hp'
    omega

/-- The `1`s in `[c, b)`. -/
def onesFrom (y : Word m) (c b : ℕ) : ℕ := ((Ico c b).filter (isOne y)).card

lemma ones_split_from {y : Word m} {a c b : ℕ} (h1 : a < c) (h2 : c < b) :
    ones y a b = ones y a c + onesFrom y c b := by
  unfold ones onesFrom
  rw [← card_union_of_disjoint]
  · congr 1
    ext p
    simp only [mem_filter, mem_union, mem_Ioo, mem_Ico]
    by_cases hone : isOne y p
    · simp only [hone, and_true]; omega
    · simp only [hone, and_false, or_self]
  · rw [disjoint_left]
    intro p hp hp'
    obtain ⟨hp, -⟩ := mem_filter.1 hp
    obtain ⟨hp', -⟩ := mem_filter.1 hp'
    rw [mem_Ioo] at hp
    rw [mem_Ico] at hp'
    omega

lemma ones_mono {y : Word m} {a a' b' b : ℕ} (h1 : a ≤ a') (h2 : b' ≤ b) :
    ones y a' b' ≤ ones y a b := by
  unfold ones
  apply card_le_card
  intro p hp
  obtain ⟨hp, hone⟩ := mem_filter.1 hp
  rw [mem_Ioo] at hp
  exact mem_filter.2 ⟨mem_Ioo.2 ⟨by omega, by omega⟩, hone⟩

lemma ones_eq_zero_of_le {y : Word m} {a b : ℕ} (h : b ≤ a + 1) : ones y a b = 0 := by
  unfold ones
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p hp
  rw [mem_Ioo] at hp
  omega

/-- The gap of a negative word has a `1`. -/
lemma ones_gap_pos {y : Word m} (hy : inf m y = false) {t : ℕ} (hL : HasTwoLE y t)
    (hG : HasTwoGT y t) :
    0 < ones y (lastTwoLE y t) (firstTwoGT y t) :=
  ones_pos_of_neg hy (isTwo_lastTwoLE hL) (isTwo_firstTwoGT hG)
    (lt_of_le_of_lt (lastTwoLE_le y t) (lt_firstTwoGT y t (lt_m_of_hasTwoGT hG)))
    fun _ h1 h2 => not_isTwo_of_mem_gap h1 h2

/-! ## The boundary corrections and the completion identity -/

/-- The fraction of the `1`s of `t`'s gap lying strictly inside `(l, r)`. -/
noncomputable def phi (y : Word m) (l r t : ℕ) : ℝ :=
  if HasTwoLE y t ∧ HasTwoGT y t then
    (ones y (max l (lastTwoLE y t)) (min r (firstTwoGT y t)) : ℝ)
      / ones y (lastTwoLE y t) (firstTwoGT y t)
  else 0

/-- The left correction `α_q`. -/
noncomputable def alpha (y : Word m) (q : ℕ) : ℝ :=
  if isTwo y q ∨ ¬ HasTwoGT y q then 0
  else if HasTwoLE y q then
    (ones y (lastTwoLE y q) (q + 1) : ℝ) / ones y (lastTwoLE y q) (firstTwoGT y q)
  else 1

/-- The right correction `β_q`. -/
noncomputable def beta (y : Word m) (q : ℕ) : ℝ :=
  if isTwo y q ∨ ¬ HasTwoLE y q then 0
  else if HasTwoGT y q then
    (onesFrom y q (firstTwoGT y q) : ℝ) / ones y (lastTwoLE y q) (firstTwoGT y q)
  else 1

/-- The distance to the next `2`. -/
noncomputable def DL (y : Word m) (q : ℕ) : ℕ := firstTwoGT y q - q

/-- The distance to the previous `2`. -/
noncomputable def DR (y : Word m) (q : ℕ) : ℕ := q - lastTwoLE y q

lemma alpha_nonneg (y : Word m) (q : ℕ) : 0 ≤ alpha y q := by
  unfold alpha; split_ifs <;> positivity

lemma beta_nonneg (y : Word m) (q : ℕ) : 0 ≤ beta y q := by
  unfold beta; split_ifs <;> positivity

lemma alpha_le_one {y : Word m} (hy : inf m y = false) (q : ℕ) : alpha y q ≤ 1 := by
  unfold alpha
  split_ifs with h1 h2
  · norm_num
  · push Not at h1
    have hpos := ones_gap_pos hy h2 h1.2
    rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast ones_mono le_rfl (Nat.succ_le_of_lt (lt_firstTwoGT y q (lt_m_of_hasTwoGT h1.2)))
  · exact le_rfl

lemma beta_le_one {y : Word m} (hy : inf m y = false) (q : ℕ) : beta y q ≤ 1 := by
  unfold beta
  split_ifs with h1 h2
  · norm_num
  · push Not at h1
    have hpos := ones_gap_pos hy h1.2 h2
    rw [div_le_one (by exact_mod_cast hpos)]
    have hlt := lastTwoLE_lt_of_not_isTwo h1.2 h1.1
    have := ones_split_from (y := y) hlt (lt_firstTwoGT y q (lt_m_of_hasTwoGT h2))
    exact_mod_cast (by omega : onesFrom y q (firstTwoGT y q)
      ≤ ones y (lastTwoLE y q) (firstTwoGT y q))
  · exact le_rfl

/-- **The completion identity** (per-position form). -/
theorem completion {y : Word m} (hy : inf m y = false) (hsome : ∃ p, isTwo y p) {l r : ℕ}
    (hlr : l < r) (hr : r < m) :
    (∑ t ∈ Ico l r, phi y l r t) / ((r - l : ℕ) : ℝ)
      + alpha y l * min 1 ((DL y l : ℝ) / ((r - l : ℕ) : ℝ))
      + beta y r * min 1 ((DR y r : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
  have hG : (0 : ℝ) < ((r - l : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - l)
  have hrl : ((r - l : ℕ) : ℝ) = (r : ℝ) - l := by rw [Nat.cast_sub hlr.le]
  by_cases hin : ∃ p, l ≤ p ∧ p ≤ r ∧ isTwo y p
  · -- Case A: a `2` in `[l, r]`
    obtain ⟨p₀, hp₀l, hp₀r, hp₀⟩ := hin
    have hLr : HasTwoLE y r := ⟨p₀, hp₀r, hp₀⟩
    set a' := lastTwoLE y r with ha'
    have ha'2 : isTwo y a' := isTwo_lastTwoLE hLr
    have hla' : l ≤ a' := hp₀l.trans (le_lastTwoLE hp₀r hp₀)
    have ha'r : a' ≤ r := lastTwoLE_le y r
    -- the first `2` at or after `l`
    set b := if isTwo y l then l else firstTwoGT y l with hb
    have hb2 : isTwo y b := by
      rw [hb]; split_ifs with h
      · exact h
      · exact isTwo_firstTwoGT ⟨p₀, lt_of_le_of_ne hp₀l (fun e => h (e ▸ hp₀)), hp₀⟩
    have hlb : l ≤ b := by
      rw [hb]; split_ifs with h
      · exact le_rfl
      · exact (lt_firstTwoGT y l (by omega)).le
    have hba' : b ≤ a' := by
      rw [hb]; split_ifs with h
      · exact hla'
      · exact (firstTwoGT_le (lt_of_le_of_ne hp₀l (fun e => h (e ▸ hp₀))) hp₀).trans
          (le_lastTwoLE hp₀r hp₀)
    have hnob : ∀ p, l ≤ p → p < b → ¬ isTwo y p := by
      intro p h1 h2 hp
      rw [hb] at h2
      split_ifs at h2 with h
      · omega
      · exact not_isTwo_of_lt_firstTwoGT (lt_of_le_of_ne h1 (fun e => h (e ▸ hp))) h2 hp
    have hnoa' : ∀ p, a' < p → p ≤ r → ¬ isTwo y p := fun p h1 h2 =>
      not_isTwo_of_lastTwoLE_lt h1 h2
    -- split the sum
    rw [← Finset.sum_Ico_consecutive _ hlb (hba'.trans ha'r),
      ← Finset.sum_Ico_consecutive _ hba' ha'r]
    -- the middle piece: `phi = 1`
    have hmid : ∑ t ∈ Ico b a', phi y l r t = ((a' - b : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)), Finset.sum_const, Nat.card_Ico,
        nsmul_eq_mul, mul_one]
      intro t ht
      rw [mem_Ico] at ht
      have hLt : HasTwoLE y t := ⟨b, ht.1, hb2⟩
      have hGt : HasTwoGT y t := ⟨a', ht.2, ha'2⟩
      have h1 : l ≤ lastTwoLE y t := hlb.trans (le_lastTwoLE ht.1 hb2)
      have h2 : firstTwoGT y t ≤ r := (firstTwoGT_le ht.2 ha'2).trans ha'r
      unfold phi
      rw [if_pos ⟨hLt, hGt⟩, max_eq_right h1, min_eq_right h2]
      exact div_self (by exact_mod_cast (ones_gap_pos hy hLt hGt).ne')
    -- the left piece
    have hleft : (∑ t ∈ Ico l b, phi y l r t) / ((r - l : ℕ) : ℝ)
        + alpha y l * min 1 ((DL y l : ℝ) / ((r - l : ℕ) : ℝ))
        = ((b - l : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) := by
      by_cases hl2 : isTwo y l
      · have hbl : b = l := by rw [hb, if_pos hl2]
        rw [hbl, Finset.Ico_self, Finset.sum_empty, zero_div, Nat.sub_self, Nat.cast_zero,
          zero_div]
        unfold alpha
        rw [if_pos (Or.inl hl2)]
        ring
      · have hbl : b = firstTwoGT y l := by rw [hb, if_neg hl2]
        have hGl : HasTwoGT y l := ⟨p₀, lt_of_le_of_ne hp₀l (fun e => hl2 (e ▸ hp₀)), hp₀⟩
        have hDL : (DL y l : ℝ) = ((b - l : ℕ) : ℝ) := by rw [DL, hbl]
        have hbr : b ≤ r := hba'.trans ha'r
        have hmin : min 1 ((DL y l : ℝ) / ((r - l : ℕ) : ℝ))
            = ((b - l : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) := by
          rw [hDL, min_eq_right]
          rw [div_le_one hG]
          exact_mod_cast (by omega : b - l ≤ r - l)
        rw [hmin]
        -- `phi` is constant on `[l, b)`
        have hconst : ∀ t ∈ Ico l b, phi y l r t = phi y l r l := by
          intro t ht
          rw [mem_Ico] at ht
          obtain ⟨e1, e2, e3, e4⟩ := gap_eq_of_no_two (y := y) ht.1
            (fun p h1 h2 => hnob p h1 (by omega))
          unfold phi
          by_cases hL : HasTwoLE y l
          · rw [if_pos ⟨e1.2 hL, e2.2 hGl⟩, if_pos ⟨hL, hGl⟩, e3 hL, e4 hGl]
          · rw [if_neg (fun h => hL (e1.1 h.1)), if_neg (fun h => hL h.1)]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        unfold alpha
        rw [if_neg (fun h => h.elim hl2 (fun h' => h' hGl))]
        by_cases hL : HasTwoLE y l
        · rw [if_pos hL]
          have hA : lastTwoLE y l < l := lastTwoLE_lt_of_not_isTwo hL hl2
          have hlb' : l < b := by rw [hbl]; exact lt_firstTwoGT y l (by omega)
          unfold phi
          rw [if_pos ⟨hL, hGl⟩, ← hbl, max_eq_left hA.le, min_eq_right hbr]
          have hpos : (0 : ℝ) < ones y (lastTwoLE y l) b := by
            have := ones_gap_pos hy hL hGl; rw [← hbl] at this; exact_mod_cast this
          have hsplit : (ones y (lastTwoLE y l) b : ℝ)
              = ones y (lastTwoLE y l) (l + 1) + ones y l b := by
            exact_mod_cast ones_split hA hlb'
          field_simp
          rw [hsplit]; ring
        · rw [if_neg hL]
          unfold phi
          rw [if_neg (fun h => hL h.1)]
          ring
    -- the right piece
    have hright : (∑ t ∈ Ico a' r, phi y l r t) / ((r - l : ℕ) : ℝ)
        + beta y r * min 1 ((DR y r : ℝ) / ((r - l : ℕ) : ℝ))
        = ((r - a' : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) := by
      by_cases hr2 : isTwo y r
      · have ha'r' : a' = r := le_antisymm ha'r (le_lastTwoLE le_rfl hr2)
        rw [ha'r', Finset.Ico_self, Finset.sum_empty, zero_div, Nat.sub_self, Nat.cast_zero,
          zero_div]
        unfold beta
        rw [if_pos (Or.inl hr2)]
        ring
      · have ha'lt : a' < r := lastTwoLE_lt_of_not_isTwo hLr hr2
        have hDR : (DR y r : ℝ) = ((r - a' : ℕ) : ℝ) := by rw [DR]
        have hmin : min 1 ((DR y r : ℝ) / ((r - l : ℕ) : ℝ))
            = ((r - a' : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) := by
          rw [hDR, min_eq_right]
          rw [div_le_one hG]
          exact_mod_cast (by omega : r - a' ≤ r - l)
        rw [hmin]
        obtain ⟨eG, eB⟩ := firstTwoGT_eq_of_no_two (y := y) ha'r hnoa'
        -- `phi` is constant on `[a', r)`
        have hconst : ∀ t ∈ Ico a' r, phi y l r t
            = if HasTwoGT y r then (ones y a' r : ℝ) / ones y a' (firstTwoGT y r) else 0 := by
          intro t ht
          rw [mem_Ico] at ht
          obtain ⟨eGt, eBt⟩ := firstTwoGT_eq_of_no_two (y := y) ht.1
            (fun p h1 h2 => hnoa' p h1 (by omega))
          obtain ⟨eLt, eAt⟩ := lastTwoLE_eq_of_no_two (y := y) ht.1
            (fun p h1 h2 => hnoa' p h1 (by omega))
          have hAa' : lastTwoLE y a' = a' :=
            le_antisymm (lastTwoLE_le y a') (le_lastTwoLE le_rfl ha'2)
          have hLt : HasTwoLE y t := ⟨a', ht.1, ha'2⟩
          unfold phi
          by_cases hGr : HasTwoGT y r
          · rw [if_pos ⟨hLt, eGt.2 (eG.1 hGr)⟩, if_pos hGr, eAt, hAa', eBt, ← eB,
              max_eq_right hla', min_eq_left]
            exact (lt_firstTwoGT y r hr).le
          · rw [if_neg (fun h => hGr (eG.2 (eGt.1 h.2))), if_neg hGr]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        unfold beta
        rw [if_neg (show ¬ (isTwo y r ∨ ¬ HasTwoLE y r) from
          fun h => h.elim hr2 (fun h' => h' hLr))]
        by_cases hGr : HasTwoGT y r
        · rw [if_pos hGr, if_pos hGr, ← ha']
          have hB : r < firstTwoGT y r := lt_firstTwoGT y r hr
          have hpos : (0 : ℝ) < ones y a' (firstTwoGT y r) := by
            have := ones_gap_pos hy hLr hGr; rw [← ha'] at this; exact_mod_cast this
          have hsplit : (ones y a' (firstTwoGT y r) : ℝ)
              = ones y a' r + onesFrom y r (firstTwoGT y r) := by
            exact_mod_cast ones_split_from ha'lt hB
          field_simp
          rw [hsplit]
        · rw [if_neg hGr, if_neg hGr]
          ring
    -- assemble
    rw [hmid]
    have e3 : ((b - l : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) + ((a' - b : ℕ) : ℝ) / ((r - l : ℕ) : ℝ)
        + ((r - a' : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) = 1 := by
      rw [← add_div, ← add_div, ← Nat.cast_add, ← Nat.cast_add,
        show (b - l) + (a' - b) + (r - a') = r - l by omega]
      exact div_self hG.ne'
    linear_combination hleft + hright + e3
  · -- Case B: no `2` in `[l, r]`
    push Not at hin
    have hno : ∀ p, l ≤ p → p ≤ r → ¬ isTwo y p := fun p h1 h2 h => hin p h1 h2 h
    have hl2 : ¬ isTwo y l := hno l le_rfl hlr.le
    have hr2 : ¬ isTwo y r := hno r hlr.le le_rfl
    obtain ⟨e1, e2, e3, e4⟩ := gap_eq_of_no_two (y := y) hlr.le hno
    have hconst : ∀ t ∈ Ico l r, phi y l r t = phi y l r l := by
      intro t ht
      rw [mem_Ico] at ht
      obtain ⟨f1, f2, f3, f4⟩ := gap_eq_of_no_two (y := y) ht.1
        (fun p h1 h2 => hno p h1 (by omega))
      unfold phi
      by_cases hL : HasTwoLE y l <;> by_cases hGl : HasTwoGT y l
      · rw [if_pos ⟨f1.2 hL, f2.2 hGl⟩, if_pos ⟨hL, hGl⟩, f3 hL, f4 hGl]
      · rw [if_neg (fun h => hGl (f2.1 h.2)), if_neg (fun h => hGl h.2)]
      · rw [if_neg (fun h => hL (f1.1 h.1)), if_neg (fun h => hL h.1)]
      · rw [if_neg (fun h => hL (f1.1 h.1)), if_neg (fun h => hL h.1)]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      mul_div_cancel_left₀ _ hG.ne']
    by_cases hL : HasTwoLE y l <;> by_cases hGl : HasTwoGT y l
    · -- both sides: a full gap around `[l, r]`
      have hA : lastTwoLE y l < l := lastTwoLE_lt_of_not_isTwo hL hl2
      have hB : r < firstTwoGT y l := by
        by_contra hle
        push Not at hle
        exact hno _ (lt_firstTwoGT y l (by omega)).le hle (isTwo_firstTwoGT hGl)
      have hpos : (0 : ℝ) < ones y (lastTwoLE y l) (firstTwoGT y l) := by
        exact_mod_cast ones_gap_pos hy hL hGl
      have hDLmin : min 1 ((DL y l : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
        rw [min_eq_left]
        rw [le_div_iff₀ hG, one_mul, DL]
        exact_mod_cast (by omega : r - l ≤ firstTwoGT y l - l)
      have hDRmin : min 1 ((DR y r : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
        rw [min_eq_left]
        rw [le_div_iff₀ hG, one_mul, DR, e3 hL]
        exact_mod_cast (by omega : r - l ≤ r - lastTwoLE y l)
      rw [hDLmin, hDRmin, mul_one, mul_one]
      unfold phi alpha beta
      rw [if_pos ⟨hL, hGl⟩, if_neg (fun h => h.elim hl2 (fun h' => h' hGl)), if_pos hL,
        if_neg (fun h => h.elim hr2 (fun h' => h' (e1.2 hL))), if_pos (e2.2 hGl), e3 hL, e4 hGl,
        max_eq_left hA.le, min_eq_left hB.le]
      have hs1 : (ones y (lastTwoLE y l) (firstTwoGT y l) : ℝ)
          = ones y (lastTwoLE y l) (l + 1) + ones y l (firstTwoGT y l) := by
        exact_mod_cast ones_split hA (hlr.trans hB)
      have hs2 : (ones y l (firstTwoGT y l) : ℝ) = ones y l r + onesFrom y r (firstTwoGT y l) := by
        exact_mod_cast ones_split_from hlr hB
      field_simp
      rw [hs1, hs2]; ring
    · -- a `2` before, none after
      have hA : lastTwoLE y l < l := lastTwoLE_lt_of_not_isTwo hL hl2
      have hDRmin : min 1 ((DR y r : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
        rw [min_eq_left]
        rw [le_div_iff₀ hG, one_mul, DR, e3 hL]
        exact_mod_cast (by omega : r - l ≤ r - lastTwoLE y l)
      rw [hDRmin, mul_one]
      unfold phi alpha beta
      rw [if_neg (fun h => hGl h.2), if_pos (Or.inr hGl),
        if_neg (fun h => h.elim hr2 (fun h' => h' (e1.2 hL))), if_neg (fun h => hGl (e2.1 h))]
      ring
    · -- a `2` after, none before
      have hB : r < firstTwoGT y l := by
        by_contra hle
        push Not at hle
        exact hno _ (lt_firstTwoGT y l (by omega)).le hle (isTwo_firstTwoGT hGl)
      have hDLmin : min 1 ((DL y l : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
        rw [min_eq_left]
        rw [le_div_iff₀ hG, one_mul, DL]
        exact_mod_cast (by omega : r - l ≤ firstTwoGT y l - l)
      rw [hDLmin, mul_one]
      unfold phi alpha beta
      rw [if_neg (fun h => hL h.1), if_neg (fun h => h.elim hl2 (fun h' => h' hGl)), if_neg hL,
        if_pos (Or.inr (fun h => hL (e1.1 h)))]
      ring
    · -- no `2` at all: excluded
      exfalso
      obtain ⟨p, hp⟩ := hsome
      by_cases hpl : p ≤ l
      · exact hL ⟨p, hpl, hp⟩
      · exact hGl ⟨p, by omega, hp⟩

end MonoidProduct.Infix
