import MonoidProduct.Simon.Blue
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Red positions: the suffix-product mirror of `Blue.lean`

For a word `v` the **suffix products** `sⱼ = (v.drop j).prod`; position
`j` is **red** when `sⱼ ≠ sⱼ₊₁`.  Everything mirrors the blue side, proved
directly on suffix products (no opposite monoid, no reversal):

* absorption — deleting non-red positions keeps the product
  (`prod_subAt_eq_of_red_subset`); here the head recursion needs no
  context at all, since suffix products are intrinsic to the suffix;
* domination from above — the red positions are the **rightmost**
  occurrence of the red subword: at or after every occurrence of every
  suffix of it (`le_redList_of_isOcc`);
* the count — at most `|M| − 1` red positions in a 𝓙-trivial monoid
  (`length_redList_le`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

open List

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

attribute [local instance] monoidInhabited

/-! ## Suffix products and red positions -/

/-- Position `j` is red when dropping its letter changes the suffix
product. -/
def IsRed (v : List M) (j : ℕ) : Prop :=
  (v.drop j).prod ≠ (v.drop (j + 1)).prod

instance (v : List M) (j : ℕ) : Decidable (IsRed v j) := by
  unfold IsRed; infer_instance

/-- The red positions, in increasing order. -/
def redList (v : List M) : List ℕ :=
  (List.range v.length).filter fun j => decide (IsRed v j)

/-- The red subword: the letters at the red positions. -/
def redWord (v : List M) : List M := readAt v (redList v)

lemma mem_redList {v : List M} {j : ℕ} :
    j ∈ redList v ↔ j < v.length ∧ IsRed v j := by
  simp [redList]

lemma redList_pairwise (v : List M) : (redList v).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

lemma redList_lt {v : List M} {j : ℕ} (h : j ∈ redList v) : j < v.length :=
  (mem_redList.mp h).1

lemma isOcc_redList (v : List M) : IsOcc (redWord v) v (redList v) :=
  ⟨redList_pairwise v, fun j hj => redList_lt hj, rfl⟩

lemma redWord_sublist (v : List M) : List.Sublist (redWord v) v :=
  (sublist_iff_exists_isOcc _ _).mpr ⟨_, isOcc_redList v⟩

/-- The suffix product peels its first letter. -/
lemma drop_prod_succ (v : List M) {j : ℕ} (hj : j < v.length) :
    (v.drop j).prod = v[j] * (v.drop (j + 1)).prod := by
  rw [List.drop_eq_getElem_cons hj, List.prod_cons]

/-- Along a red-free stretch the suffix product is constant. -/
lemma drop_prod_eq_of_no_red (v : List M) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ j, a ≤ j → j < b → ¬ IsRed v j) :
    (v.drop a).prod = (v.drop b).prod := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => rfl
  | succ d ih =>
      have hnr := h (a + d) (by omega) (by omega)
      rw [IsRed, not_not] at hnr
      rw [show a + (d + 1) = a + d + 1 from by omega, ← hnr]
      exact ih (by omega) fun j hj hj' => h j hj (by omega)

/-! ## Absorption -/

/-- **Deleting non-red positions does not change the product.** -/
lemma prod_subAtFrom_eq_red (w : List M) (o : ℕ) (S : Finset ℕ)
    (h : ∀ j, j < w.length → o + j ∉ S →
      (w.drop j).prod = (w.drop (j + 1)).prod) :
    (subAtFrom w o S).prod = w.prod := by
  induction w generalizing o with
  | nil => rfl
  | cons a w ih =>
      rw [subAtFrom_cons]
      have htail : ∀ j, j < w.length → o + 1 + j ∉ S →
          (w.drop j).prod = (w.drop (j + 1)).prod := by
        intro j hj hS
        have := h (j + 1) (by simp; omega)
          (by rw [show o + (j + 1) = o + 1 + j from by omega]; exact hS)
        simpa [List.drop_succ_cons] using this
      by_cases hS : o ∈ S
      · rw [if_pos hS, List.prod_cons, List.prod_cons, ih (o + 1) htail]
      · rw [if_neg hS, ih (o + 1) htail]
        have h0 := h 0 (by simp) (by simpa using hS)
        simpa [List.prod_cons] using h0.symm

/-- **Absorption**: a position set containing every red position reads a
subword with the same product. -/
theorem prod_subAt_eq_of_red_subset (v : List M) {S : Finset ℕ}
    (hS : ∀ j, IsRed v j → j < v.length → j ∈ S) :
    (subAt v S).prod = v.prod :=
  prod_subAtFrom_eq_red v 0 S fun j hj hS' => by
    by_contra hne
    exact hS' (by simpa using hS j hne hj)

/-! ## Domination from above: the red positions form the rightmost occurrence -/

/-- A position above the `s`-th red position and below the next is not
red. -/
lemma not_isRed_of_gt_of_next {v : List M} {s j : ℕ} (hs : s < (redList v).length)
    (hj : (redList v)[s] < j)
    (hnext : ∀ (hs' : s + 1 < (redList v).length), j < (redList v)[s + 1]) :
    ¬ IsRed v j := by
  intro hr
  by_cases hjv : j < v.length
  · have hmem : j ∈ redList v := mem_redList.mpr ⟨hjv, hr⟩
    obtain ⟨s', hs', rfl⟩ := List.mem_iff_getElem.mp hmem
    have hp := List.pairwise_iff_getElem.mp (redList_pairwise v)
    rcases lt_or_ge s s' with hlt | hge
    · rcases eq_or_lt_of_le (show s + 1 ≤ s' by omega) with heq | hlt'
      · subst heq
        have := hnext hs'
        omega
      · have h1 := hnext (by omega)
        have h2 := hp (s + 1) s' (by omega) hs' hlt'
        omega
    · rcases eq_or_lt_of_le hge with rfl | hlt
      · omega
      · have := hp s' s hs' hs hlt
        omega
  · apply hr
    rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]

/-- The letter at an occurrence position of a suffix of the red subword is
the letter at the corresponding red position. -/
lemma getElem_eq_of_isOcc_redWord_drop (v : List M) {s' : ℕ} {ℓ : List ℕ}
    (hℓ : IsOcc ((redWord v).drop s') v ℓ) {t : ℕ} (ht' : t < ℓ.length)
    (htR : s' + t < (redList v).length) :
    v[ℓ[t]]'(hℓ.getElem_lt ht')
      = v[(redList v)[s' + t]]'(redList_lt (List.getElem_mem htR)) := by
  rw [hℓ.getElem_read ht', List.getElem_drop, ← (isOcc_redList v).getElem_read htR]

/-- **The contradiction**: an occurrence position of a suffix of the red
subword strictly after the corresponding red position, and before the next
one, would freeze the suffix product across that red position. -/
lemma redList_key (v : List M) {s' : ℕ} {ℓ : List ℕ}
    (hℓ : IsOcc ((redWord v).drop s') v ℓ) {t : ℕ} (ht' : t < ℓ.length)
    (htR : s' + t < (redList v).length) (hgt : (redList v)[s' + t] < ℓ[t])
    (hnext : ∀ (hs' : s' + t + 1 < (redList v).length),
      ℓ[t] < (redList v)[s' + t + 1]) : False := by
  have hR := redList_lt (List.getElem_mem htR)
  have hj := hℓ.getElem_lt ht'
  have hnr : ∀ j', (redList v)[s' + t] < j' → j' ≤ ℓ[t] → ¬ IsRed v j' :=
    fun j' h1 h2 => not_isRed_of_gt_of_next htR h1 fun hs'' => by
      have := hnext hs''; omega
  have hconst : (v.drop ((redList v)[s' + t] + 1)).prod = (v.drop (ℓ[t] + 1)).prod :=
    drop_prod_eq_of_no_red v (by omega) fun j' h1 h2 => hnr j' (by omega) (by omega)
  have hletter := getElem_eq_of_isOcc_redWord_drop v hℓ ht' htR
  have hnrj : ¬ IsRed v ℓ[t] := hnr _ hgt le_rfl
  rw [IsRed, not_not, drop_prod_succ v hj] at hnrj
  have hred := (mem_redList.mp (List.getElem_mem htR)).2
  apply hred
  rw [drop_prod_succ v hR, ← hletter, hconst, hnrj]

/-- **The red positions dominate from above every occurrence of every
suffix of the red subword.** -/
theorem le_redList_of_isOcc (v : List M) {s' : ℕ} {ℓ : List ℕ}
    (hℓ : IsOcc ((redWord v).drop s') v ℓ) {t : ℕ} (ht' : t < ℓ.length)
    (htR : s' + t < (redList v).length) :
    ℓ[t] ≤ (redList v)[s' + t] := by
  have hlen : ℓ.length = (redList v).length - s' := by
    rw [hℓ.length, List.length_drop]
    simp [redWord]
  -- downward induction: `k` counts the positions after `t`; the red index is
  -- carried as an explicit variable so that no `getElem` index is rewritten
  suffices h : ∀ k t i, (hi : i = s' + t) → (ht : t + k + 1 = ℓ.length) →
      ∀ (hiR : i < (redList v).length), ℓ[t]'(by omega) ≤ (redList v)[i] from
    h (ℓ.length - 1 - t) t (s' + t) rfl (by omega) htR
  intro k
  induction k with
  | zero =>
      intro t i hi ht hiR
      subst hi
      by_contra hgt
      exact redList_key v hℓ (by omega) hiR (not_le.mp hgt) fun hs'' => by omega
  | succ k ih =>
      intro t i hi ht hiR
      subst hi
      by_contra hgt
      refine redList_key v hℓ (by omega) hiR (not_le.mp hgt) fun hs'' => ?_
      have h1 := ih (t + 1) (s' + t + 1) (by omega) (by omega) hs''
      have h2 : ℓ[t]'(by omega) < ℓ[t + 1]'(by omega) :=
        hℓ.getElem_lt_getElem (by omega) (by omega)
      omega

/-! ## The count, in a 𝓙-trivial monoid -/

/-- A repeated suffix value freezes the stretch in between. -/
lemma drop_prod_eq_of_eq (hJ : IsJTrivialMonoid M) (v : List M) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (h : (v.drop a).prod = (v.drop c).prod) :
    (v.drop b).prod = (v.drop c).prod := by
  have hsplit : ∀ {x y : ℕ}, x ≤ y → JLe (v.drop x).prod (v.drop y).prod := by
    intro x y hxy
    rw [show v.drop x = (v.drop x).take (y - x) ++ v.drop y from by
      conv_lhs => rw [← List.take_append_drop (y - x) (v.drop x)]
      rw [List.drop_drop, Nat.add_sub_cancel' hxy], List.prod_append]
    exact jLe_mul_right _ _
  have h1 := hsplit hab
  have h2 := hsplit hbc
  rw [h] at h1
  exact hJ.eq_of_jLe_jLe h2 h1

lemma redList_nodup (v : List M) : (redList v).Nodup :=
  (redList_pairwise v).imp ne_of_lt

/-- **At most `|M| − 1` red positions** in a 𝓙-trivial monoid. -/
theorem length_redList_le (hJ : IsJTrivialMonoid M) (v : List M) :
    (redList v).length ≤ Fintype.card M - 1 := by
  classical
  rw [← List.toFinset_card_of_nodup (redList_nodup v)]
  have h := Finset.card_le_card_of_injOn (fun j : ℕ => (v.drop j).prod)
    (s := (redList v).toFinset) (t := Finset.univ.erase 1) ?_ ?_
  · rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h
  · intro j hj
    rw [Finset.mem_coe, List.mem_toFinset, mem_redList] at hj
    rw [Finset.mem_coe, Finset.mem_erase]
    refine ⟨fun h1 => hj.2 ?_, Finset.mem_univ _⟩
    have h1' : (v.drop j).prod = 1 := h1
    have := drop_prod_eq_of_eq hJ v (Nat.le_add_right j 1) (show j + 1 ≤ v.length by omega)
      (by rw [h1', List.drop_length]; rfl)
    rw [this, h1', List.drop_length]
    rfl
  · intro j hj j' hj' hjj'
    rw [Finset.mem_coe, List.mem_toFinset, mem_redList] at hj hj'
    have hjj'' : (v.drop j).prod = (v.drop j').prod := hjj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · apply hj.2
      have := drop_prod_eq_of_eq hJ v (Nat.le_add_right j 1) (show j + 1 ≤ j' by omega) hjj''
      exact hjj''.trans this.symm
    · apply hj'.2
      have := drop_prod_eq_of_eq hJ v (Nat.le_add_right j' 1) (show j' + 1 ≤ j by omega)
        hjj''.symm
      exact hjj''.symm.trans this.symm

end MonoidProduct
