import MonoidProduct.Width.EssentialWord
import MonoidProduct.Capped.Embed
import QuantumQueryComplexity.Spectral
import QuantumQueryComplexity.Promise.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The permutation-and-deletion promise and its adversary certificate

Fix a padding symbol `s0` and a core word `a : Fin r → σ` with no letter equal to `s0`.  A
**high** word of length `n ≥ r` has the multiset of letters `bag a + (n−r)·{s0}`; a **low**
word is a high word with one core letter replaced by `s0`, i.e. `bag y + {c} = bag a +
(n−r+1)·{s0}` for some `c ∈ bag a` (its **missing symbol**, unique by cancellation of
multisets).  Words are represented by their actual entries, so repeated core letters are
never distinguishable query answers.

* Deletion at a nonpadding coordinate of a high word gives a low word with missing symbol
  the deleted letter (`isLow_update`); restoring the missing symbol at a padding coordinate
  of a low word gives a high word (`isHigh_update`); the two are inverse (`adj_iff`).
* Degrees: a high word has `r` low neighbours (`card_nbr_high`), a low word `n−r+1` high
  neighbours (`card_nbr_low`) — distinct coordinates give distinct words.
* The zero-one adjacency matrix `delΓ` on `High ⊕ Low` has the eigenvector `(r, θ)` with
  eigenvalue `θ = √(r(n−r+1))` (`delΓ_mulVec_delVec`), so `θ ≤ ‖Γ‖`; every query mask is
  supported on the graph of the involution `delFlip i` (delete/restore at `i`), so the masked
  norms are at most one; hence `θ ≤ advPMOn delRead delOut` (`sqrt_le_advPMOn_coreDeletion`).
* Products (`prod_isHigh`, `prod_isLow_ne`): every high word has the product of `a`, and
  when every position of `a` is essential every low word has a different product.

Nothing here needs aperiodicity; the all-essential core word is supplied by
`Width/EssentialWord.lean`.
-/

namespace MonoidProduct

open Finset QuantumQueryComplexity
open scoped Matrix Matrix.Norms.L2Operator

/-! ## Bags of letters -/

section Bag

variable {σ : Type} [DecidableEq σ]

/-- The multiset of entries of a word. -/
def bag {k : ℕ} (x : Fin k → σ) : Multiset σ := Finset.univ.val.map x

lemma univ_val_eq_cons {k : ℕ} (i : Fin k) :
    (Finset.univ : Finset (Fin k)).val = i ::ₘ (Finset.univ.erase i).val := by
  rw [← Finset.insert_val_of_notMem (Finset.notMem_erase i Finset.univ),
    Finset.insert_erase (Finset.mem_univ i)]

lemma bag_eq_cons {k : ℕ} (x : Fin k → σ) (i : Fin k) :
    bag x = x i ::ₘ (Finset.univ.erase i).val.map x := by
  rw [bag, univ_val_eq_cons i, Multiset.map_cons]

/-- Updating one coordinate replaces one occurrence of its letter. -/
lemma bag_update {k : ℕ} (x : Fin k → σ) (i : Fin k) (c : σ) :
    bag (Function.update x i c) = c ::ₘ (bag x).erase (x i) := by
  rw [bag_eq_cons (Function.update x i c) i, Function.update_self, bag_eq_cons x i,
    Multiset.erase_cons_head]
  congr 1
  exact Multiset.map_congr rfl fun j hj =>
    Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_def.2 hj)) _ _

lemma mem_bag {k : ℕ} (x : Fin k → σ) (i : Fin k) : x i ∈ bag x :=
  Multiset.mem_map.2 ⟨i, Finset.mem_def.1 (Finset.mem_univ i), rfl⟩

lemma mem_bag_iff {k : ℕ} {x : Fin k → σ} {c : σ} : c ∈ bag x ↔ ∃ i, x i = c := by
  rw [bag, Multiset.mem_map]
  simp

lemma count_bag {k : ℕ} (x : Fin k → σ) (c : σ) :
    (bag x).count c = (Finset.univ.filter fun i => x i = c).card := by
  rw [bag, Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun i _ => eq_comm

lemma prod_bag {M : Type} [CommMonoid M] (m : σ → M) {k : ℕ} (x : Fin k → σ) :
    ∏ i, m (x i) = ((bag x).map m).prod := by
  rw [Finset.prod_eq_multiset_prod, bag, Multiset.map_map]
  rfl

end Bag

/-! ## The promise -/

section Promise

variable {σ : Type} [Fintype σ] [DecidableEq σ] (s0 : σ) {r n : ℕ} (a : Fin r → σ)

/-- High words: the core letters plus `n − r` padding symbols. -/
def IsHigh (x : Fin n → σ) : Prop := bag x = bag a + Multiset.replicate (n - r) s0

/-- Low words: one core letter missing, one more padding symbol. -/
def IsLow (y : Fin n → σ) : Prop :=
  ∃ c ∈ bag a, bag y + {c} = bag a + Multiset.replicate (n - r + 1) s0

lemma s0_notMem_bag (ha : ∀ j, a j ≠ s0) : s0 ∉ bag a := fun h => by
  obtain ⟨j, hj⟩ := mem_bag_iff.1 h
  exact ha j hj

lemma isHigh_count (ha : ∀ j, a j ≠ s0) {x : Fin n → σ} (hx : IsHigh s0 a x) :
    (bag x).count s0 = n - r := by
  rw [hx, Multiset.count_add, Multiset.count_eq_zero.2 (s0_notMem_bag s0 a ha),
    Multiset.count_replicate, if_pos rfl, zero_add]

lemma isHigh_card_ne (ha : ∀ j, a j ≠ s0) (hrn : r ≤ n) {x : Fin n → σ} (hx : IsHigh s0 a x) :
    (Finset.univ.filter fun i => x i ≠ s0).card = r := by
  have h1 := isHigh_count s0 a ha hx
  rw [count_bag] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => x i = s0)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : (Finset.univ.filter fun i : Fin n => ¬ x i = s0)
      = Finset.univ.filter fun i => x i ≠ s0 := rfl
  rw [h3] at h2
  omega

lemma isLow_count (ha : ∀ j, a j ≠ s0) {y : Fin n → σ} (hy : IsLow s0 a y) :
    (bag y).count s0 = n - r + 1 := by
  obtain ⟨c, hc, hyc⟩ := hy
  have hcs : c ≠ s0 := fun h => s0_notMem_bag s0 a ha (h ▸ hc)
  have := congrArg (Multiset.count s0) hyc
  rw [Multiset.count_add, Multiset.count_add, Multiset.count_singleton, if_neg (Ne.symm hcs),
    Multiset.count_eq_zero.2 (s0_notMem_bag s0 a ha), Multiset.count_replicate, if_pos rfl]
    at this
  omega

lemma isLow_card_pad (ha : ∀ j, a j ≠ s0) {y : Fin n → σ} (hy : IsLow s0 a y) :
    (Finset.univ.filter fun i => y i = s0).card = n - r + 1 := by
  rw [← count_bag]
  exact isLow_count s0 a ha hy

/-- The missing symbol of a low word is unique. -/
lemma missing_unique {y : Fin n → σ} {c d : σ}
    (hc : bag y + {c} = bag a + Multiset.replicate (n - r + 1) s0)
    (hd : bag y + {d} = bag a + Multiset.replicate (n - r + 1) s0) : c = d :=
  Multiset.singleton_inj.1 (add_left_cancel (hc.trans hd.symm))

/-- The high words. -/
abbrev High (n : ℕ) : Type := {x : Fin n → σ // IsHigh s0 a x}

/-- The low words. -/
abbrev Low (n : ℕ) : Type := {y : Fin n → σ // IsLow s0 a y}

/-- The missing symbol of a low word. -/
noncomputable def missing (y : Low s0 a n) : σ := y.2.choose

lemma missing_mem (y : Low s0 a n) : missing s0 a y ∈ bag a := y.2.choose_spec.1

lemma missing_spec (y : Low s0 a n) :
    bag y.1 + {missing s0 a y} = bag a + Multiset.replicate (n - r + 1) s0 := y.2.choose_spec.2

lemma missing_ne (ha : ∀ j, a j ≠ s0) (y : Low s0 a n) : missing s0 a y ≠ s0 := fun h =>
  s0_notMem_bag s0 a ha (h ▸ missing_mem s0 a y)

lemma eq_missing {y : Low s0 a n} {c : σ}
    (hc : bag y.1 + {c} = bag a + Multiset.replicate (n - r + 1) s0) : c = missing s0 a y :=
  missing_unique s0 a hc (missing_spec s0 a y)

/-! ## Deletion and restoration -/

lemma mem_bag_of_isHigh {x : Fin n → σ} (hx : IsHigh s0 a x) {i : Fin n} (hi : x i ≠ s0) :
    x i ∈ bag a := by
  have := mem_bag x i
  rw [hx, Multiset.mem_add] at this
  rcases this with h | h
  · exact h
  · exact absurd (Multiset.mem_replicate.1 h).2 hi

lemma isLow_update_eq {x : Fin n → σ} (hx : IsHigh s0 a x) {i : Fin n} (_hi : x i ≠ s0) :
    bag (Function.update x i s0) + {x i} = bag a + Multiset.replicate (n - r + 1) s0 := by
  rw [bag_update, Multiset.cons_add, add_comm ((bag x).erase (x i)) {x i},
    Multiset.singleton_add, Multiset.cons_erase (mem_bag x i), hx, Multiset.replicate_succ,
    Multiset.add_cons]

/-- Deleting a nonpadding letter of a high word gives a low word. -/
lemma isLow_update {x : Fin n → σ} (hx : IsHigh s0 a x) {i : Fin n} (hi : x i ≠ s0) :
    IsLow s0 a (Function.update x i s0) :=
  ⟨x i, mem_bag_of_isHigh s0 a hx hi, isLow_update_eq s0 a hx hi⟩

/-- Restoring the missing symbol at a padding coordinate gives a high word. -/
lemma isHigh_update (ha : ∀ j, a j ≠ s0) (y : Low s0 a n) {i : Fin n} (hi : y.1 i = s0) :
    IsHigh s0 a (Function.update y.1 i (missing s0 a y)) := by
  have hspec := missing_spec s0 a y
  have hc := missing_ne s0 a ha y
  unfold IsHigh
  rw [bag_update, hi]
  have h1 : missing s0 a y ::ₘ bag y.1 = s0 ::ₘ (bag a + Multiset.replicate (n - r) s0) := by
    rw [← Multiset.singleton_add, add_comm, hspec, Multiset.replicate_succ, Multiset.add_cons]
  have h2 := congrArg (fun s => Multiset.erase s s0) h1
  rw [Multiset.erase_cons_tail _ hc, Multiset.erase_cons_head] at h2
  exact h2

/-- Adjacency: `y` is `x` with one nonpadding coordinate deleted. -/
def Adj (x y : Fin n → σ) : Prop := ∃ i, x i ≠ s0 ∧ y = Function.update x i s0

lemma missing_of_adj (x : High s0 a n) (y : Low s0 a n) {i : Fin n} (hi : x.1 i ≠ s0)
    (hy : y.1 = Function.update x.1 i s0) : missing s0 a y = x.1 i :=
  (eq_missing s0 a (by rw [hy]; exact isLow_update_eq s0 a x.2 hi)).symm

/-- Deletion and restoration at the same coordinate are inverse. -/
lemma adj_iff (ha : ∀ j, a j ≠ s0) (x : High s0 a n) (y : Low s0 a n) :
    Adj s0 x.1 y.1 ↔ ∃ i, y.1 i = s0 ∧ x.1 = Function.update y.1 i (missing s0 a y) := by
  constructor
  · rintro ⟨i, hi, hy⟩
    refine ⟨i, by rw [hy, Function.update_self], ?_⟩
    rw [missing_of_adj s0 a x y hi hy, hy, Function.update_idem, Function.update_eq_self]
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, ?_, ?_⟩
    · rw [hx, Function.update_self]
      exact missing_ne s0 a ha y
    · rw [hx, Function.update_idem,
        show Function.update y.1 i s0 = Function.update y.1 i (y.1 i) by rw [hi],
        Function.update_eq_self]

/-! ## Degrees -/

open Classical in
lemma card_nbr_high (ha : ∀ j, a j ≠ s0) (hrn : r ≤ n) (x : High s0 a n) :
    (Finset.univ.filter fun y : Low s0 a n => Adj s0 x.1 y.1).card = r := by
  refine Eq.trans ?_ (isHigh_card_ne s0 a ha hrn x.2)
  symm
  refine Finset.card_bij (fun i hi => ⟨Function.update x.1 i s0,
    isLow_update s0 a x.2 (Finset.mem_filter.1 hi).2⟩) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, i, (Finset.mem_filter.1 hi).2, rfl⟩
  · intro i hi j hj heq
    have h := congrArg (fun z : Low s0 a n => z.1 i) heq
    simp only [Function.update_self] at h
    by_contra hij
    rw [Function.update_of_ne hij] at h
    exact (Finset.mem_filter.1 hi).2 h.symm
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := (Finset.mem_filter.1 hy).2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, Subtype.ext hyi.symm⟩

open Classical in
lemma card_nbr_low (ha : ∀ j, a j ≠ s0) (y : Low s0 a n) :
    (Finset.univ.filter fun x : High s0 a n => Adj s0 x.1 y.1).card = n - r + 1 := by
  refine Eq.trans ?_ (isLow_card_pad s0 a ha y.2)
  symm
  refine Finset.card_bij (fun i hi => ⟨Function.update y.1 i (missing s0 a y),
    isHigh_update s0 a ha y (Finset.mem_filter.1 hi).2⟩) ?_ ?_ ?_
  · intro i hi
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    exact (adj_iff s0 a ha _ y).2 ⟨i, (Finset.mem_filter.1 hi).2, rfl⟩
  · intro i hi j hj heq
    have h := congrArg (fun z : High s0 a n => z.1 i) heq
    simp only [Function.update_self] at h
    by_contra hij
    rw [Function.update_of_ne hij] at h
    exact missing_ne s0 a ha y (h.trans (Finset.mem_filter.1 hi).2)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := (adj_iff s0 a ha x y).1 (Finset.mem_filter.1 hx).2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, Subtype.ext hxi.symm⟩

/-! ## The padded word -/

/-- The core word padded with `s0`. -/
def delPadWord (_hrn : r ≤ n) : Fin n → σ := fun i => if h : (i : ℕ) < r then a ⟨i, h⟩ else s0

lemma filter_lt_eq_map (hrn : r ≤ n) :
    (Finset.univ.filter fun i : Fin n => (i : ℕ) < r)
      = (Finset.univ : Finset (Fin r)).map (Fin.castLEEmb hrn) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro h
    exact ⟨⟨i, h⟩, Fin.ext (by simp)⟩
  · rintro ⟨j, rfl⟩
    show ((Fin.castLE hrn j : Fin n) : ℕ) < r
    rw [Fin.val_castLE]
    exact j.isLt

lemma card_filter_lt (hrn : r ≤ n) : (Finset.univ.filter fun i : Fin n => (i : ℕ) < r).card = r := by
  rw [filter_lt_eq_map hrn, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma isHigh_delPadWord (hrn : r ≤ n) : IsHigh s0 a (delPadWord s0 a hrn) := by
  unfold IsHigh bag
  rw [← Multiset.filter_add_not (fun i : Fin n => (i : ℕ) < r) Finset.univ.val, Multiset.map_add]
  congr 1
  · rw [← Finset.filter_val, filter_lt_eq_map hrn, Finset.map_val, Multiset.map_map]
    exact Multiset.map_congr rfl fun j _ => by
      simp only [Function.comp, delPadWord, Fin.castLEEmb_apply, Fin.val_castLE, j.isLt, dif_pos]
  · rw [Multiset.eq_replicate]
    constructor
    · rw [Multiset.card_map, ← Finset.filter_val, ← Finset.card_def]
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i : Fin n => (i : ℕ) < r)
      rw [card_filter_lt hrn, Finset.card_univ, Fintype.card_fin] at h
      omega
    · intro b hb
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hb
      rw [Multiset.mem_filter] at hi
      simp only [delPadWord, hi.2, dif_neg, not_false_eq_true]

lemma nonempty_high (hrn : r ≤ n) : Nonempty (High s0 a n) := ⟨⟨delPadWord s0 a hrn, isHigh_delPadWord s0 a hrn⟩⟩

/-! ## Products -/

section Products

variable {M : Type} [CommMonoid M] (m : σ → M) (hs0 : m s0 = 1)
include hs0

/-- Every high word has the product of the core. -/
lemma prod_isHigh {x : Fin n → σ} (hx : IsHigh s0 a x) : ∏ i, m (x i) = ∏ j, m (a j) := by
  rw [prod_bag, hx, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
    Multiset.prod_replicate, hs0, one_pow, mul_one, ← prod_bag]

/-- When every core position is essential, every low word has a different product. -/
lemma prod_isLow_ne [DecidableEq M] (hall : prodEss m a Finset.univ = Finset.univ)
    {y : Fin n → σ} (hy : IsLow s0 a y) : ∏ i, m (y i) ≠ ∏ j, m (a j) := by
  obtain ⟨c, hc, hyc⟩ := hy
  obtain ⟨j₀, hj₀⟩ := mem_bag_iff.1 hc
  -- the bag of `y` is the core minus one occurrence of `c`, plus padding
  have hbag : bag y = (bag a).erase c + Multiset.replicate (n - r + 1) s0 := by
    have h : c ::ₘ bag y = c ::ₘ ((bag a).erase c + Multiset.replicate (n - r + 1) s0) := by
      rw [← Multiset.singleton_add, add_comm, hyc, ← Multiset.cons_add, Multiset.cons_erase hc]
    exact (Multiset.cons_inj_right c).1 h
  have hprod : ∏ i, m (y i) = ∏ j ∈ Finset.univ.erase j₀, m (a j) := by
    rw [prod_bag, hbag, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
      Multiset.prod_replicate, hs0, one_pow, mul_one, ← hj₀, bag_eq_cons a j₀,
      Multiset.erase_cons_head, Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  rw [hprod]
  have hj : j₀ ∈ prodEss m a Finset.univ := by rw [hall]; exact Finset.mem_univ _
  exact fun h => (mem_prodEss'.1 hj).2 h.symm

end Products

/-! ## The adversary matrix -/

open Classical

/-- The observations: the word itself. -/
def delRead : High s0 a n ⊕ Low s0 a n → Fin n → σ := Sum.elim Subtype.val Subtype.val

/-- The Boolean promise output: `true` on high words. -/
def delOut : High s0 a n ⊕ Low s0 a n → Bool := Sum.elim (fun _ => true) (fun _ => false)

lemma delRead_injective (ha : ∀ j, a j ≠ s0) :
    Function.Injective (delRead s0 a (n := n)) := by
  intro p q h
  cases p with
  | inl x =>
      cases q with
      | inl x' => exact congrArg Sum.inl (Subtype.ext h)
      | inr y =>
          exfalso
          have h1 := isHigh_count s0 a ha x.2
          have h2 := isLow_count s0 a ha y.2
          rw [show x.1 = y.1 from h] at h1
          omega
  | inr y =>
      cases q with
      | inl x =>
          exfalso
          have h1 := isHigh_count s0 a ha x.2
          have h2 := isLow_count s0 a ha y.2
          rw [show y.1 = x.1 from h] at h2
          omega
      | inr y' => exact congrArg Sum.inr (Subtype.ext h)

/-- The adjacency matrix across the two sides, zero within a side. -/
noncomputable def delΓ : Matrix (High s0 a n ⊕ Low s0 a n) (High s0 a n ⊕ Low s0 a n) ℝ :=
  Matrix.of <| Sum.elim
    (fun x => Sum.elim (fun _ : High s0 a n => (0 : ℝ))
      (fun y : Low s0 a n => if Adj s0 x.1 y.1 then 1 else 0))
    (fun y => Sum.elim (fun x : High s0 a n => if Adj s0 x.1 y.1 then 1 else 0)
      (fun _ : Low s0 a n => (0 : ℝ)))

@[simp] lemma delΓ_inl_inl (x x' : High s0 a n) : delΓ s0 a (Sum.inl x) (Sum.inl x') = 0 := rfl
@[simp] lemma delΓ_inr_inr (y y' : Low s0 a n) : delΓ s0 a (Sum.inr y) (Sum.inr y') = 0 := rfl
@[simp] lemma delΓ_inl_inr (x : High s0 a n) (y : Low s0 a n) :
    delΓ s0 a (Sum.inl x) (Sum.inr y) = if Adj s0 x.1 y.1 then 1 else 0 := rfl
@[simp] lemma delΓ_inr_inl (y : Low s0 a n) (x : High s0 a n) :
    delΓ s0 a (Sum.inr y) (Sum.inl x) = if Adj s0 x.1 y.1 then 1 else 0 := rfl

lemma delΓ_symm (p q : High s0 a n ⊕ Low s0 a n) : delΓ s0 a p q = delΓ s0 a q p := by
  cases p <;> cases q <;> rfl

lemma delΓ_isHermitian : (delΓ s0 a (n := n)).IsHermitian :=
  Matrix.IsHermitian.ext fun p q => by rw [star_trivial, delΓ_symm s0 a q p]

lemma abs_delΓ_le_one (p q : High s0 a n ⊕ Low s0 a n) : |delΓ s0 a p q| ≤ 1 := by
  cases p <;> cases q <;>
    simp only [delΓ_inl_inl, delΓ_inr_inr, delΓ_inl_inr, delΓ_inr_inl] <;>
    [skip; split_ifs; split_ifs; skip] <;> norm_num

lemma delΓ_apply_eq_zero {p q : High s0 a n ⊕ Low s0 a n} (hf : delOut s0 a p = delOut s0 a q) :
    delΓ s0 a p q = 0 := by
  cases p with
  | inl x =>
      cases q with
      | inl x' => rfl
      | inr y => exact absurd hf (by simp [delOut])
  | inr y =>
      cases q with
      | inl x => exact absurd hf (by simp [delOut])
      | inr y' => rfl

/-! ## The eigenvector -/

/-- `θ = √(r(n−r+1))`. -/
noncomputable def delTheta (r n : ℕ) : ℝ := Real.sqrt ((r * (n - r + 1) : ℕ) : ℝ)

lemma delTheta_nonneg : 0 ≤ delTheta r n := Real.sqrt_nonneg _

/-- The eigenvector: `r` on high words, `θ` on low words. -/
noncomputable def delVec : High s0 a n ⊕ Low s0 a n → ℝ :=
  Sum.elim (fun _ => (r : ℝ)) (fun _ => delTheta r n)

@[simp] lemma delVec_inl (x : High s0 a n) : delVec s0 a (Sum.inl x) = (r : ℝ) := rfl
@[simp] lemma delVec_inr (y : Low s0 a n) : delVec s0 a (Sum.inr y) = delTheta r n := rfl

/-- **The eigen equation** `Γ v = θ v`, from the two degrees. -/
lemma delΓ_mulVec_delVec (ha : ∀ j, a j ≠ s0) (hrn : r ≤ n) :
    delΓ s0 a *ᵥ delVec s0 a = delTheta r n • delVec s0 a (n := n) := by
  funext p
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.smul_apply, smul_eq_mul]
  cases p with
  | inl x =>
      have h1 : (∑ x' : High s0 a n, delΓ s0 a (Sum.inl x) (Sum.inl x')
          * delVec s0 a (Sum.inl x')) = 0 :=
        Finset.sum_eq_zero fun x' _ => by rw [delΓ_inl_inl, zero_mul]
      have h2 : (∑ y : Low s0 a n, delΓ s0 a (Sum.inl x) (Sum.inr y) * delVec s0 a (Sum.inr y))
          = (r : ℝ) * delTheta r n := by
        rw [Finset.sum_congr rfl fun y _ => by
          rw [delΓ_inl_inr, delVec_inr, ite_mul, one_mul, zero_mul],
          ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_nbr_high s0 a ha hrn x]
      rw [h1, h2, delVec_inl, zero_add, mul_comm]
  | inr y =>
      have h1 : (∑ x : High s0 a n, delΓ s0 a (Sum.inr y) (Sum.inl x) * delVec s0 a (Sum.inl x))
          = ((n - r + 1 : ℕ) : ℝ) * (r : ℝ) := by
        rw [Finset.sum_congr rfl fun x _ => by
          rw [delΓ_inr_inl, delVec_inl, ite_mul, one_mul, zero_mul],
          ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_nbr_low s0 a ha y]
      have h2 : (∑ y' : Low s0 a n, delΓ s0 a (Sum.inr y) (Sum.inr y')
          * delVec s0 a (Sum.inr y')) = 0 :=
        Finset.sum_eq_zero fun y' _ => by rw [delΓ_inr_inr, zero_mul]
      rw [h1, h2, delVec_inr, add_zero, delTheta, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      push_cast
      ring

lemma delVec_ne_zero (hrn : r ≤ n) (hr1 : 1 ≤ r) : delVec s0 a (n := n) ≠ 0 := by
  intro h0
  obtain ⟨x⟩ := nonempty_high s0 a hrn
  have h := congrFun h0 (Sum.inl x)
  rw [delVec_inl, Pi.zero_apply] at h
  have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  linarith

lemma delTheta_le_norm (ha : ∀ j, a j ≠ s0) (hrn : r ≤ n) (hr1 : 1 ≤ r) :
    delTheta r n ≤ ‖delΓ s0 a (n := n)‖ :=
  (le_abs_self _).trans
    (abs_eigenvalue_le_norm (delΓ_mulVec_delVec s0 a ha hrn) (delVec_ne_zero s0 a hrn hr1))

/-! ## The query masks -/

/-- The flip at `i`: delete a nonpadding letter of a high word, restore the missing symbol at
a padding coordinate of a low word, stand still otherwise. -/
noncomputable def delFlip (ha : ∀ j, a j ≠ s0) (i : Fin n) :
    High s0 a n ⊕ Low s0 a n → High s0 a n ⊕ Low s0 a n
  | Sum.inl x =>
      if h : x.1 i ≠ s0 then Sum.inr ⟨Function.update x.1 i s0, isLow_update s0 a x.2 h⟩
      else Sum.inl x
  | Sum.inr y =>
      if h : y.1 i = s0 then
        Sum.inl ⟨Function.update y.1 i (missing s0 a y), isHigh_update s0 a ha y h⟩
      else Sum.inr y

lemma delFlip_involutive (ha : ∀ j, a j ≠ s0) (i : Fin n) :
    Function.Involutive (delFlip s0 a ha i) := by
  intro p
  cases p with
  | inl x =>
      by_cases h : x.1 i ≠ s0
      · have hyi : (Function.update x.1 i s0) i = s0 := Function.update_self _ _ _
        simp only [delFlip, dif_pos h, dif_pos hyi]
        refine congrArg Sum.inl (Subtype.ext ?_)
        show Function.update (Function.update x.1 i s0) i (missing s0 a ⟨_, _⟩) = x.1
        rw [missing_of_adj s0 a x ⟨_, isLow_update s0 a x.2 h⟩ h rfl, Function.update_idem,
          Function.update_eq_self]
      · simp only [delFlip, dif_neg h]
  | inr y =>
      by_cases h : y.1 i = s0
      · have hxi : ¬ (Function.update y.1 i (missing s0 a y)) i = s0 := by
          rw [Function.update_self]; exact missing_ne s0 a ha y
        simp only [delFlip, dif_pos h, dif_pos hxi]
        refine congrArg Sum.inr (Subtype.ext ?_)
        show Function.update (Function.update y.1 i (missing s0 a y)) i s0 = y.1
        rw [Function.update_idem,
          show Function.update y.1 i s0 = Function.update y.1 i (y.1 i) by rw [h],
          Function.update_eq_self]
      · simp only [delFlip, dif_neg h]

/-- The support of a masked entry: the unique incident flip. -/
lemma delMask_support (ha : ∀ j, a j ≠ s0) {i : Fin n} {p q : High s0 a n ⊕ Low s0 a n}
    (hΓ : delΓ s0 a p q ≠ 0) (hmask : delRead s0 a p i ≠ delRead s0 a q i) :
    q = delFlip s0 a ha i p := by
  cases p with
  | inl x =>
      cases q with
      | inl x' => exact absurd (delΓ_inl_inl s0 a x x') hΓ
      | inr y =>
          have hadj : Adj s0 x.1 y.1 := by
            by_contra hn
            rw [delΓ_inl_inr, if_neg hn] at hΓ
            exact hΓ rfl
          obtain ⟨j, hj, hy⟩ := hadj
          have hij : i = j := by
            by_contra hij
            apply hmask
            show x.1 i = y.1 i
            rw [hy, Function.update_of_ne hij]
          subst hij
          simp only [delFlip, dif_pos hj]
          exact congrArg Sum.inr (Subtype.ext hy)
  | inr y =>
      cases q with
      | inr y' => exact absurd (delΓ_inr_inr s0 a y y') hΓ
      | inl x =>
          have hadj : Adj s0 x.1 y.1 := by
            by_contra hn
            rw [delΓ_inr_inl, if_neg hn] at hΓ
            exact hΓ rfl
          obtain ⟨j, hj, hy⟩ := hadj
          have hij : i = j := by
            by_contra hij
            apply hmask
            show y.1 i = x.1 i
            rw [hy, Function.update_of_ne hij]
          subst hij
          have hyi : y.1 i = s0 := by rw [hy, Function.update_self]
          simp only [delFlip, dif_pos hyi]
          refine congrArg Sum.inl (Subtype.ext ?_)
          show x.1 = Function.update y.1 i (missing s0 a y)
          rw [missing_of_adj s0 a x y hj hy, hy, Function.update_idem, Function.update_eq_self]

/-- **The mask bound**: every query filter leaves norm at most one. -/
lemma delΓ_hadamard_le_one (ha : ∀ j, a j ≠ s0) (i : Fin n) :
    ‖delΓ s0 a ⊙ advDOn (delRead s0 a (n := n)) i‖ ≤ 1 := by
  refine l2_opNorm_le_one_of_equiv_support _ (delFlip_involutive s0 a ha i).toPerm ?_ ?_
  · intro p q hne
    rw [Matrix.hadamard_apply, advDOn_apply]
    by_cases hmask : delRead s0 a p i = delRead s0 a q i
    · rw [if_pos hmask, mul_zero]
    · rw [if_neg hmask]
      by_cases hΓ : delΓ s0 a p q = 0
      · rw [hΓ, zero_mul]
      · exact absurd (delMask_support s0 a ha hΓ hmask) hne
  · intro p q
    rw [Matrix.hadamard_apply, advDOn_apply]
    split_ifs with hm
    · rw [mul_zero, abs_zero]
      norm_num
    · rw [mul_one]
      exact abs_delΓ_le_one s0 a p q

/-! ## The certificate -/

/-- **The deletion adversary bound**: telling the high words from the low words needs
adversary value `√(r(n−r+1))`. -/
theorem sqrt_le_advPMOn_coreDeletion (ha : ∀ j, a j ≠ s0) (hrn : r ≤ n) (hr1 : 1 ≤ r) :
    delTheta r n ≤ advPMOn (delRead s0 a (n := n)) (delOut s0 a (n := n)) := by
  have hdet := separates_of_injective (delRead_injective s0 a ha) (delOut s0 a (n := n))
  have h1 : IsAdvMatrixOn (delOut s0 a (n := n)) (delΓ s0 a) :=
    ⟨delΓ_isHermitian s0 a, fun p q hf => delΓ_apply_eq_zero s0 a hf⟩
  exact (delTheta_le_norm s0 a ha hrn hr1).trans
    (le_advPMOn hdet h1 (delΓ_hadamard_le_one s0 a ha))

end Promise

end MonoidProduct
