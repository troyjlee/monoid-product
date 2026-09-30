import QuantumQueryComplexity.Oriented
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Clean infix

Over the alphabet `{0, 1, 2}` (`Fin 3`), `inf m x = true` when two `2`s of `x`
have only `0`s strictly between them; such a pair `[l, r]` is a **clean
witness** (`IsWitness`).

For the clean-witness adversary (`Infix/Dual.lean`) a negative word is organized by its `2`s:
`isTwo`, `lastTwoLE y t` (the last `2` at or before `t`), `firstTwoGT y t`
(the first `2` after `t`), and `ones y a b`, the number of `1`s strictly
between `a` and `b`.  A negative word has a `1` in every gap between
consecutive `2`s (`ones_pos_of_neg`).
-/

namespace MonoidProduct.Infix

open Finset

/-- A word over `{0, 1, 2}`. -/
abbrev Word (m : ℕ) := Fin m → Fin 3

variable {m : ℕ}

/-- `[l, r]` is a clean witness: two `2`s with only `0`s strictly between. -/
def IsWitness (x : Word m) (l r : Fin m) : Prop :=
  l < r ∧ x l = 2 ∧ x r = 2 ∧ ∀ q, l < q → q < r → x q = 0

instance (x : Word m) (l r : Fin m) : Decidable (IsWitness x l r) := by
  unfold IsWitness; infer_instance

/-- **Clean infix.** -/
def inf (m : ℕ) (x : Word m) : Bool := decide (∃ l r : Fin m, IsWitness x l r)

lemma inf_eq_true_iff {x : Word m} : inf m x = true ↔ ∃ l r : Fin m, IsWitness x l r := by
  simp [inf]

lemma inf_eq_false_iff {x : Word m} : inf m x = false ↔ ∀ l r : Fin m, ¬ IsWitness x l r := by
  simp [inf]

/-- A chosen witness of a positive word. -/
noncomputable def witness {x : Word m} (h : inf m x = true) : Fin m × Fin m :=
  let h' := inf_eq_true_iff.1 h
  (h'.choose, h'.choose_spec.choose)

lemma witness_spec {x : Word m} (h : inf m x = true) :
    IsWitness x (witness h).1 (witness h).2 :=
  (inf_eq_true_iff.1 h).choose_spec.choose_spec

/-! ## The `2`s of a word -/

/-- Position `p` carries a `2`. -/
def isTwo (y : Word m) (p : ℕ) : Prop := ∃ h : p < m, y ⟨p, h⟩ = 2

/-- Position `p` carries a `1`. -/
def isOne (y : Word m) (p : ℕ) : Prop := ∃ h : p < m, y ⟨p, h⟩ = 1

instance (y : Word m) (p : ℕ) : Decidable (isTwo y p) := by unfold isTwo; infer_instance
instance (y : Word m) (p : ℕ) : Decidable (isOne y p) := by unfold isOne; infer_instance

lemma isTwo_lt {y : Word m} {p : ℕ} (h : isTwo y p) : p < m := h.1
lemma isOne_lt {y : Word m} {p : ℕ} (h : isOne y p) : p < m := h.1

lemma not_isTwo_of_isOne {y : Word m} {p : ℕ} (h : isOne y p) : ¬ isTwo y p := by
  rintro ⟨_, h2⟩
  obtain ⟨_, h1⟩ := h
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- The number of `1`s strictly between `a` and `b`. -/
def ones (y : Word m) (a b : ℕ) : ℕ := ((Ioo a b).filter (isOne y)).card

/-- There is a `2` at or before `t`. -/
def HasTwoLE (y : Word m) (t : ℕ) : Prop := ∃ p ≤ t, isTwo y p

/-- There is a `2` strictly after `t`. -/
def HasTwoGT (y : Word m) (t : ℕ) : Prop := ∃ p, t < p ∧ isTwo y p

instance (y : Word m) (t : ℕ) : Decidable (HasTwoLE y t) := by unfold HasTwoLE; infer_instance
instance (y : Word m) (t : ℕ) : Decidable (HasTwoGT y t) := by
  unfold HasTwoGT
  exact decidable_of_iff (∃ p ∈ Finset.Ioo t m, isTwo y p)
    ⟨fun ⟨p, hp, h⟩ => ⟨p, (Finset.mem_Ioo.1 hp).1, h⟩,
     fun ⟨p, hp, h⟩ => ⟨p, Finset.mem_Ioo.2 ⟨hp, h.1⟩, h⟩⟩

/-- The last `2` at or before `t` (`0` if there is none). -/
noncomputable def lastTwoLE (y : Word m) (t : ℕ) : ℕ := Nat.findGreatest (isTwo y) t

/-- The first `2` strictly after `t` (`m` if there is none). -/
noncomputable def firstTwoGT (y : Word m) (t : ℕ) : ℕ :=
  if h : HasTwoGT y t then Nat.find h else m

lemma lastTwoLE_le (y : Word m) (t : ℕ) : lastTwoLE y t ≤ t := Nat.findGreatest_le t

lemma isTwo_lastTwoLE {y : Word m} {t : ℕ} (h : HasTwoLE y t) : isTwo y (lastTwoLE y t) := by
  obtain ⟨p, hp, h2⟩ := h
  exact Nat.findGreatest_spec hp h2

lemma le_lastTwoLE {y : Word m} {t p : ℕ} (hp : p ≤ t) (h2 : isTwo y p) : p ≤ lastTwoLE y t :=
  Nat.le_findGreatest hp h2

lemma not_isTwo_of_lastTwoLE_lt {y : Word m} {t p : ℕ} (h1 : lastTwoLE y t < p) (h2 : p ≤ t) :
    ¬ isTwo y p :=
  Nat.findGreatest_is_greatest h1 h2

lemma lt_firstTwoGT (y : Word m) (t : ℕ) (ht : t < m) : t < firstTwoGT y t := by
  unfold firstTwoGT
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact ht

lemma isTwo_firstTwoGT {y : Word m} {t : ℕ} (h : HasTwoGT y t) : isTwo y (firstTwoGT y t) := by
  unfold firstTwoGT; rw [dif_pos h]; exact (Nat.find_spec h).2

lemma firstTwoGT_le {y : Word m} {t p : ℕ} (hp : t < p) (h2 : isTwo y p) : firstTwoGT y t ≤ p := by
  unfold firstTwoGT
  rw [dif_pos ⟨p, hp, h2⟩]
  exact Nat.find_min' _ ⟨hp, h2⟩

lemma firstTwoGT_le_m (y : Word m) (t : ℕ) : firstTwoGT y t ≤ m := by
  unfold firstTwoGT
  split_ifs with h
  · exact (Nat.find_spec h).2.1.le
  · exact le_rfl

lemma not_isTwo_of_lt_firstTwoGT {y : Word m} {t p : ℕ} (h1 : t < p) (h2 : p < firstTwoGT y t) :
    ¬ isTwo y p := by
  intro h
  exact absurd (firstTwoGT_le h1 h) (not_le.2 h2)

/-- **Negative words have a `1` in every gap between consecutive `2`s.** -/
lemma ones_pos_of_neg {y : Word m} (hy : inf m y = false) {a b : ℕ} (ha : isTwo y a)
    (hb : isTwo y b) (hab : a < b) (hgap : ∀ p, a < p → p < b → ¬ isTwo y p) :
    0 < ones y a b := by
  rw [inf_eq_false_iff] at hy
  by_contra h0
  push Not at h0
  have hempty : ∀ p, a < p → p < b → ¬ isOne y p := by
    intro p hap hpb hone
    have hmem : p ∈ (Ioo a b).filter (isOne y) := by
      rw [mem_filter, mem_Ioo]; exact ⟨⟨hap, hpb⟩, hone⟩
    have := card_pos.2 ⟨p, hmem⟩
    unfold ones at h0; omega
  obtain ⟨ha', ha2⟩ := ha
  obtain ⟨hb', hb2⟩ := hb
  refine hy ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨hab, ha2, hb2, fun q hq1 hq2 => ?_⟩
  have h1 : ¬ isTwo y q := hgap q hq1 hq2
  have h2 : ¬ isOne y q := hempty q hq1 hq2
  simp only [isTwo, isOne, not_exists] at h1 h2
  have h1' := h1 q.isLt
  have h2' := h2 q.isLt
  simp only [Fin.eta] at h1' h2'
  revert h1' h2'
  generalize y q = c
  revert c; decide

end MonoidProduct.Infix
