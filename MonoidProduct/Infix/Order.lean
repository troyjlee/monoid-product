import QuantumQueryComplexity.Oriented
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The order kernel

For `d, e < 2^k` there are vectors `ordA k d`, `ordB k e` with
`⟨ordA k d, ordB k e⟩ = [e ≤ d]` and squared norms `≤ k + 1`.  One coordinate
per (bit position `j`, prefix above bit `j`): `d` writes it when its bit `j`
is `1`, `e` when its bit `j` is `0`; they meet exactly at the highest bit where
`d` and `e` differ, and there `d > e`.  One more coordinate per value gives
equality.
-/

namespace MonoidProduct.Infix

open Finset

/-- The coordinates: a bit position with the prefix above it, or a value. -/
abbrev OrdIdx (k : ℕ) := (Fin k × Fin (2 ^ k)) ⊕ Fin (2 ^ k)

/-- The prefix of `d` above bit `j`, as an index (clipped for safety). -/
def prefixAbove (k : ℕ) (d : ℕ) (j : Fin k) : Fin (2 ^ k) :=
  ⟨(d / 2 ^ ((j : ℕ) + 1)) % 2 ^ k, Nat.mod_lt _ (by positivity)⟩

/-- The value `d` as an index (clipped for safety). -/
def valIdx (k : ℕ) (d : ℕ) : Fin (2 ^ k) := ⟨d % 2 ^ k, Nat.mod_lt _ (by positivity)⟩

/-- The vector of `d`. -/
def ordA (k : ℕ) (d : ℕ) : OrdIdx k → ℝ
  | Sum.inl (j, p) => if d.testBit j = true ∧ prefixAbove k d j = p then 1 else 0
  | Sum.inr p => if valIdx k d = p then 1 else 0

/-- The vector of `e`. -/
def ordB (k : ℕ) (e : ℕ) : OrdIdx k → ℝ
  | Sum.inl (j, p) => if e.testBit j = false ∧ prefixAbove k e j = p then 1 else 0
  | Sum.inr p => if valIdx k e = p then 1 else 0

lemma ordA_sq_le (k d : ℕ) : ∑ i, ordA k d i * ordA k d i ≤ k + 1 := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1 : ∀ j : Fin k, ∑ p : Fin (2 ^ k), ordA k d (Sum.inl (j, p)) * ordA k d (Sum.inl (j, p))
      ≤ 1 := by
    intro j
    simp only [ordA]
    rw [Finset.sum_eq_single (prefixAbove k d j)]
    · split_ifs <;> norm_num
    · intro p _ hp; rw [if_neg (fun h => hp h.2.symm)]; norm_num
    · intro h; exact absurd (mem_univ _) h
  have h2 : ∑ p : Fin (2 ^ k), ordA k d (Sum.inr p) * ordA k d (Sum.inr p) = 1 := by
    simp only [ordA]
    rw [Finset.sum_eq_single (valIdx k d)]
    · rw [if_pos rfl]; norm_num
    · intro p _ hp; rw [if_neg (Ne.symm hp)]; norm_num
    · intro h; exact absurd (mem_univ _) h
  rw [h2]
  have := Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin k))) => h1 j
  rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
  linarith

lemma ordB_sq_le (k e : ℕ) : ∑ i, ordB k e i * ordB k e i ≤ k + 1 := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1 : ∀ j : Fin k, ∑ p : Fin (2 ^ k), ordB k e (Sum.inl (j, p)) * ordB k e (Sum.inl (j, p))
      ≤ 1 := by
    intro j
    simp only [ordB]
    rw [Finset.sum_eq_single (prefixAbove k e j)]
    · split_ifs <;> norm_num
    · intro p _ hp; rw [if_neg (fun h => hp h.2.symm)]; norm_num
    · intro h; exact absurd (mem_univ _) h
  have h2 : ∑ p : Fin (2 ^ k), ordB k e (Sum.inr p) * ordB k e (Sum.inr p) = 1 := by
    simp only [ordB]
    rw [Finset.sum_eq_single (valIdx k e)]
    · rw [if_pos rfl]; norm_num
    · intro p _ hp; rw [if_neg (Ne.symm hp)]; norm_num
    · intro h; exact absurd (mem_univ _) h
  rw [h2]
  have := Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin k))) => h1 j
  rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
  linarith

/-- The bit-level contribution: `1` exactly when `d` and `e` agree above bit `j`,
`d` has bit `j` set and `e` does not. -/
lemma ordA_mul_ordB_inl (k d e : ℕ) (j : Fin k) :
    ∑ p : Fin (2 ^ k), ordA k d (Sum.inl (j, p)) * ordB k e (Sum.inl (j, p))
      = if d.testBit j = true ∧ e.testBit j = false ∧ prefixAbove k d j = prefixAbove k e j
        then 1 else 0 := by
  classical
  simp only [ordA, ordB]
  rw [Finset.sum_eq_single (prefixAbove k d j)]
  · by_cases h : d.testBit j = true ∧ e.testBit j = false ∧ prefixAbove k d j = prefixAbove k e j
    · rw [if_pos h, if_pos ⟨h.1, rfl⟩, if_pos ⟨h.2.1, h.2.2.symm⟩]; norm_num
    · rw [if_neg h]
      by_cases h1 : d.testBit j = true ∧ prefixAbove k d j = prefixAbove k d j
      · rw [if_pos h1, if_neg]; · norm_num
        rintro ⟨h2, h3⟩; exact h ⟨h1.1, h2, h3.symm⟩
      · rw [if_neg h1]; norm_num
  · intro p _ hp; rw [if_neg (fun h => hp h.2.symm)]; norm_num
  · intro h; exact absurd (mem_univ _) h

/-- **Prefixes above bit `j` agree exactly when all higher bits agree.** -/
lemma prefixAbove_eq_iff {k d e : ℕ} (hd : d < 2 ^ k) (he : e < 2 ^ k) (j : Fin k) :
    prefixAbove k d j = prefixAbove k e j ↔ ∀ i, (j : ℕ) < i → d.testBit i = e.testBit i := by
  have hd' : d / 2 ^ ((j : ℕ) + 1) < 2 ^ k :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hd
  have he' : e / 2 ^ ((j : ℕ) + 1) < 2 ^ k :=
    lt_of_le_of_lt (Nat.div_le_self _ _) he
  simp only [prefixAbove, Fin.mk.injEq, Nat.mod_eq_of_lt hd', Nat.mod_eq_of_lt he']
  constructor
  · intro h i hi
    have := congrArg (fun n => n.testBit (i - ((j : ℕ) + 1))) h
    simp only [Nat.testBit_div_two_pow] at this
    rwa [Nat.sub_add_cancel (by omega : (j : ℕ) + 1 ≤ i)] at this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact h _ (by omega)

/-- For `e < d` there is a highest differing bit, where `d` has the `1`. -/
lemma exists_highest_diff {k d e : ℕ} (hd : d < 2 ^ k) (he : e < 2 ^ k) (hne : e < d) :
    ∃ j : Fin k, d.testBit j = true ∧ e.testBit j = false
      ∧ prefixAbove k d j = prefixAbove k e j := by
  classical
  have hdiff : ∃ j, j < k ∧ d.testBit j ≠ e.testBit j := by
    by_contra h
    push Not at h
    have : d = e := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < k
      · exact h j hj
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hd
          (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hj))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le he
          (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hj)))]
    omega
  obtain ⟨j₀, hj₀k, hj₀⟩ := hdiff
  let j := Nat.findGreatest (fun j => d.testBit j ≠ e.testBit j) (k - 1)
  have hjk : j < k := by
    have := Nat.findGreatest_le (P := fun j => d.testBit j ≠ e.testBit j) (k - 1)
    omega
  have hjspec : d.testBit j ≠ e.testBit j :=
    Nat.findGreatest_spec (P := fun j => d.testBit j ≠ e.testBit j) (by omega : j₀ ≤ k - 1) hj₀
  have hjmax : ∀ j', j < j' → d.testBit j' = e.testBit j' := fun j' h1 => by
    by_cases h2 : j' < k
    · exact not_not.1 (Nat.findGreatest_is_greatest h1 (by omega))
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hd
        (Nat.pow_le_pow_right (by norm_num) (not_lt.1 h2))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le he
        (Nat.pow_le_pow_right (by norm_num) (not_lt.1 h2)))]
  have hbit : d.testBit j = true ∧ e.testBit j = false := by
    by_contra hcon
    have hd' : d.testBit j = false := by
      cases hdt : d.testBit j
      · rfl
      · cases het : e.testBit j
        · exact absurd ⟨hdt, het⟩ hcon
        · exact absurd (hdt.trans het.symm) hjspec
    have he' : e.testBit j = true := by
      cases het : e.testBit j
      · rw [hd', het] at hjspec; exact absurd rfl hjspec
      · rfl
    have hlt : d < e := Nat.lt_of_testBit j hd' he' fun j' hj' => hjmax j' hj'
    omega
  exact ⟨⟨j, hjk⟩, hbit.1, hbit.2, (prefixAbove_eq_iff hd he ⟨j, hjk⟩).2 hjmax⟩

/-- **The order kernel**: `⟨ordA k d, ordB k e⟩ = [e ≤ d]` for `d, e < 2^k`. -/
theorem ordA_mul_ordB {k d e : ℕ} (hd : d < 2 ^ k) (he : e < 2 ^ k) :
    ∑ i, ordA k d i * ordB k e i = if e ≤ d then 1 else 0 := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [ordA_mul_ordB_inl]
  have hval : ∑ p : Fin (2 ^ k), ordA k d (Sum.inr p) * ordB k e (Sum.inr p)
      = if d = e then 1 else 0 := by
    simp only [ordA, ordB]
    rw [Finset.sum_eq_single (valIdx k d)]
    · rw [if_pos rfl]
      by_cases hde : d = e
      · rw [if_pos hde, if_pos (by rw [hde])]; norm_num
      · rw [if_neg hde, if_neg]
        · norm_num
        intro h
        apply hde
        have := congrArg Fin.val h
        simp only [valIdx] at this
        rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at this
        exact this.symm
    · intro p _ hp; rw [if_neg (Ne.symm hp)]; norm_num
    · intro h; exact absurd (mem_univ _) h
  rw [hval]
  -- a bit contributes only if it is the highest differing bit and `d` has the `1` there
  have hcontrib : ∀ j : Fin k, (d.testBit j = true ∧ e.testBit j = false
      ∧ prefixAbove k d j = prefixAbove k e j) → e < d := by
    rintro j ⟨a, b, c⟩
    exact Nat.lt_of_testBit j b a fun j' hj' => ((prefixAbove_eq_iff hd he j).1 c j' hj').symm
  rcases lt_trichotomy e d with hlt | heq | hgt
  · obtain ⟨j, h1, h2, h3⟩ := exists_highest_diff hd he hlt
    rw [if_pos hlt.le, if_neg hlt.ne']
    rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨h1, h2, h3⟩]; norm_num
    · intro j' _ hj'
      rw [if_neg]
      rintro ⟨a, b, c⟩
      rcases lt_or_gt_of_ne (fun h : (j' : ℕ) = j => hj' (Fin.ext h)) with h | h
      · have := (prefixAbove_eq_iff hd he j').1 c j h
        rw [h1, h2] at this
        exact absurd this (by decide)
      · have := (prefixAbove_eq_iff hd he j).1 h3 j' h
        rw [a, b] at this
        exact absurd this (by decide)
    · intro h; exact absurd (mem_univ _) h
  · subst heq
    rw [if_pos le_rfl, if_pos rfl, Finset.sum_eq_zero]
    · norm_num
    intro j _
    rw [if_neg]
    rintro ⟨a, b, _⟩
    rw [a] at b
    exact absurd b (by decide)
  · rw [if_neg (not_le.2 hgt), if_neg hgt.ne, Finset.sum_eq_zero]
    · norm_num
    intro j _
    rw [if_neg]
    intro h
    have := hcontrib j h
    omega

end MonoidProduct.Infix
