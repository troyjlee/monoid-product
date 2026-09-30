import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The capped counter monoid

`Capped k` is `{0, …, k}` with `a ⊕ b = min (a + b) k`, written
multiplicatively to fit the product-problem framework (the capped counters of
the paper, `thm:capped-counter-product`).  Iterated products compute the capped sum
(`val_prod : (∏ f).val = min (∑ (f ·).val) k`), every element satisfies
`x^(k+1) = x^k` (`pow_index`), and `k` is the least uniform such exponent.

The combinatorial heart of the width upper bound lives here too:
`card_filter_capped_ne_le` — in any multiset of capped values, at most `k`
positions change the product by their deletion.  The charging
argument: with uncapped total `S`, either `S < k` and only the ≤ `S` positive
positions can matter, or `S ≥ k` and every deletion that uncaps the sum
removes at least `S - k + 1`, so there are at most
`S / (S - k + 1) ≤ k` of them.

The carrier is a `def` (not `abbrev`) wrapping `Fin (k + 1)`: `Fin (k + 1)`
carries Mathlib's mod-`(k+1)` ring structure, which must not leak.
-/

namespace MonoidProduct

/-- The capped counter: `{0, …, k}` with `a * b = min (a + b) k`. -/
def Capped (k : ℕ) : Type := Fin (k + 1)

namespace Capped

variable {k : ℕ}

instance : DecidableEq (Capped k) := inferInstanceAs (DecidableEq (Fin (k + 1)))
instance : Fintype (Capped k) := inferInstanceAs (Fintype (Fin (k + 1)))

/-- The counter value, in `{0, …, k}`. -/
def val (a : Capped k) : ℕ := Fin.val a

lemma val_le (a : Capped k) : a.val ≤ k := Nat.lt_succ_iff.mp (Fin.isLt a)

lemma ext {a b : Capped k} (h : a.val = b.val) : a = b := Fin.ext h

lemma val_inj {a b : Capped k} : a.val = b.val ↔ a = b :=
  ⟨ext, fun h => h ▸ rfl⟩

instance : Mul (Capped k) := ⟨fun a b => ⟨min (a.val + b.val) k, by omega⟩⟩
instance : One (Capped k) := ⟨⟨0, by omega⟩⟩

@[simp] lemma mul_val (a b : Capped k) :
    (a * b).val = min (a.val + b.val) k := rfl

@[simp] lemma one_val : (1 : Capped k).val = 0 := rfl

instance : CommMonoid (Capped k) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := ext (by simp only [mul_val]; omega)
  one_mul a := ext (by simp only [mul_val, one_val]; have := a.val_le; omega)
  mul_one a := ext (by simp only [mul_val, one_val]; have := a.val_le; omega)
  mul_comm a b := ext (by simp only [mul_val]; omega)

/-- **Products are capped sums.** -/
lemma val_prod {α : Type*} (s : Finset α) (f : α → Capped k) :
    (∏ j ∈ s, f j).val = min (∑ j ∈ s, (f j).val) k := by
  induction s using Finset.cons_induction with
  | empty => show (1 : Capped k).val = min 0 k; rw [one_val]; omega
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons, mul_val, ih]
      omega

lemma pow_val (a : Capped k) (j : ℕ) : (a ^ j).val = min (j * a.val) k := by
  induction j with
  | zero => rw [pow_zero, one_val]; omega
  | succ j ih =>
      rw [pow_succ, mul_val, ih]
      have h : (j + 1) * a.val = j * a.val + a.val := by ring
      omega

/-- The aperiodicity index of `Capped k` is `k`: `x^(k+1) = x^k`. -/
lemma pow_index (a : Capped k) : a ^ (k + 1) = a ^ k := by
  apply ext
  rw [pow_val, pow_val]
  rcases Nat.eq_zero_or_pos a.val with h0 | h1
  · simp [h0]
  · have h2 : k ≤ k * a.val := Nat.le_mul_of_pos_right k h1
    have h3 : (k + 1) * a.val = k * a.val + a.val := by ring
    omega

/-- The generator witnessing that `k` is least: `1̂ = 1` capped. -/
def gen : Capped k := ⟨min 1 k, by omega⟩

/-! ## The charging bound -/

/-- **At most `k` positions of `T` change the capped product by their
deletion** — the per-coordinate charging argument for capped counters
(`thm:capped-counter-product`). -/
lemma card_filter_capped_ne_le {α : Type*} [DecidableEq α]
    (T : Finset α) (f : α → Capped k) :
    (T.filter fun i => ∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j).card ≤ k := by
  classical
  have herase : ∀ i ∈ T, (∏ j ∈ T.erase i, f j).val
      = min ((∑ j ∈ T, (f j).val) - (f i).val) k := by
    intro i hi
    rw [val_prod]
    have h := Finset.sum_erase_add T (fun j => (f j).val) hi
    congr 1
    omega
  have hmem : ∀ i ∈ T,
      (∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j
        ↔ min (∑ j ∈ T, (f j).val) k
            ≠ min ((∑ j ∈ T, (f j).val) - (f i).val) k) := by
    intro i hi
    rw [← val_prod, ← herase i hi]
    exact (not_congr val_inj).symm
  by_cases hSk : (∑ j ∈ T, (f j).val) < k
  · have hsub1 : (T.filter fun i => ∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j)
        ⊆ T.filter fun i => 1 ≤ (f i).val := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      have hval := (hmem i hi.1).mp hi.2
      omega
    calc (T.filter fun i => ∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j).card
        ≤ (T.filter fun i => 1 ≤ (f i).val).card := Finset.card_le_card hsub1
      _ ≤ ∑ i ∈ T.filter fun i => 1 ≤ (f i).val, (f i).val := by
          have h := Finset.card_nsmul_le_sum
            (T.filter fun i => 1 ≤ (f i).val) (fun i => (f i).val) 1
            (fun i hi => (Finset.mem_filter.mp hi).2)
          simpa using h
      _ ≤ ∑ i ∈ T, (f i).val :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ k := hSk.le
  · push_neg at hSk
    have hlow : ∀ i ∈ T.filter fun i => ∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j,
        (∑ j ∈ T, (f j).val) - k + 1 ≤ (f i).val := by
      intro i hi
      rw [Finset.mem_filter] at hi
      have hval := (hmem i hi.1).mp hi.2
      have hvS : (f i).val ≤ ∑ j ∈ T, (f j).val :=
        Finset.single_le_sum (f := fun j => (f j).val)
          (fun j _ => Nat.zero_le _) hi.1
      omega
    have hsum :
        (T.filter fun i => ∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j).card
          * ((∑ j ∈ T, (f j).val) - k + 1) ≤ ∑ j ∈ T, (f j).val := by
      have h := Finset.card_nsmul_le_sum
        (T.filter fun i => ∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j)
        (fun i => (f i).val) ((∑ j ∈ T, (f j).val) - k + 1) hlow
      calc (T.filter fun i => ∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j).card
            * ((∑ j ∈ T, (f j).val) - k + 1)
          ≤ ∑ i ∈ T.filter fun i => ∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j,
              (f i).val := by simpa using h
        _ ≤ ∑ i ∈ T, (f i).val :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    by_contra hcard
    push_neg at hcard
    have h2 : (k + 1) * ((∑ j ∈ T, (f j).val) - k + 1)
        ≤ (T.filter fun i => ∏ j ∈ T, f j ≠ ∏ j ∈ T.erase i, f j).card
          * ((∑ j ∈ T, (f j).val) - k + 1) :=
      Nat.mul_le_mul_right _ hcard
    have hexp : (k + 1) * ((∑ j ∈ T, (f j).val) - k + 1)
        = k * ((∑ j ∈ T, (f j).val) - k) + k
          + ((∑ j ∈ T, (f j).val) - k) + 1 := by ring
    omega

end Capped

end MonoidProduct
