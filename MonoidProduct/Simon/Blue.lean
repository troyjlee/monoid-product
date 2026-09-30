import MonoidProduct.Simon.Defs
import MonoidProduct.Simon.Words
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Blue and red positions: prefix and suffix products of a word

Klíma's proof, the monoid-side layer.  For a word `u` over a monoid `M`
the **prefix products** `pᵢ = (u.take i).prod` descend; position `i` is
**blue** when `pᵢ₊₁ ≠ pᵢ`.  Dually the **suffix products**
`sⱼ = (v.drop j).prod` and the **red** positions `sⱼ ≠ sⱼ₊₁`.

Three facts on each side:

* **absorption** — deleting non-blue positions does not change the
  product (`prod_subAt_eq_of_blue_subset`): a one-line head recursion, no
  algebra at all;
* **domination** — the blue positions are the leftmost occurrence of the
  blue subword: they lie componentwise at or before every occurrence of
  every prefix of it (`blueList_le_of_isOcc`), again with no algebra;
* **the count** — in a 𝓙-trivial monoid there are at most `|M| − 1` blue
  positions (`length_blueList_le`): the prefix products at the blue
  positions are pairwise distinct and never `1`, because in a 𝓙-trivial
  monoid a repeated prefix value freezes the whole stretch in between
  (`take_prod_eq_of_eq`).

The red side is the mirror image, proved directly on suffix products.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open List

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- The default letter is the identity; `readAt` reads it off the word's
end, where it is never used. -/
def monoidInhabited (M : Type) [Monoid M] : Inhabited M := ⟨1⟩

attribute [local instance] monoidInhabited

/-! ## Prefix products and blue positions -/

/-- Position `i` is blue when appending its letter changes the prefix
product. -/
def IsBlue (u : List M) (i : ℕ) : Prop :=
  (u.take (i + 1)).prod ≠ (u.take i).prod

instance (u : List M) (i : ℕ) : Decidable (IsBlue u i) := by
  unfold IsBlue; infer_instance

/-- The blue positions, in increasing order. -/
def blueList (u : List M) : List ℕ :=
  (List.range u.length).filter fun i => decide (IsBlue u i)

/-- The blue subword: the letters at the blue positions. -/
def blueWord (u : List M) : List M := readAt u (blueList u)

lemma mem_blueList {u : List M} {i : ℕ} :
    i ∈ blueList u ↔ i < u.length ∧ IsBlue u i := by
  simp [blueList]

lemma blueList_pairwise (u : List M) : (blueList u).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

lemma blueList_lt {u : List M} {i : ℕ} (h : i ∈ blueList u) : i < u.length :=
  (mem_blueList.mp h).1

/-- The blue positions are an occurrence of the blue subword. -/
lemma isOcc_blueList (u : List M) : IsOcc (blueWord u) u (blueList u) :=
  ⟨blueList_pairwise u, fun i hi => blueList_lt hi, rfl⟩

/-- The blue subword is a subword. -/
lemma blueWord_sublist (u : List M) : List.Sublist (blueWord u) u :=
  (sublist_iff_exists_isOcc _ _).mpr ⟨_, isOcc_blueList u⟩

/-- Along a blue-free stretch the prefix product is constant. -/
lemma take_prod_eq_of_no_blue (u : List M) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ j, a ≤ j → j < b → ¬ IsBlue u j) :
    (u.take b).prod = (u.take a).prod := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => rfl
  | succ d ih =>
      have hnb := h (a + d) (by omega) (by omega)
      rw [IsBlue, not_not] at hnb
      rw [show a + (d + 1) = a + d + 1 from by omega, hnb]
      exact ih (by omega) fun j hj hj' => h j hj (by omega)

/-! ## Absorption -/

/-- **Deleting non-blue positions does not change the product** — stated
for a suffix starting at position `o` with the left context `c`. -/
lemma prod_subAtFrom_eq (w : List M) (o : ℕ) (S : Finset ℕ) (c : M)
    (h : ∀ j, j < w.length → o + j ∉ S →
      c * (w.take (j + 1)).prod = c * (w.take j).prod) :
    c * (subAtFrom w o S).prod = c * w.prod := by
  induction w generalizing o c with
  | nil => rfl
  | cons a w ih =>
      rw [subAtFrom_cons]
      have htail : ∀ j, j < w.length → o + 1 + j ∉ S →
          (c * a) * (w.take (j + 1)).prod = (c * a) * (w.take j).prod := by
        intro j hj hS
        have := h (j + 1) (by simp; omega) (by rw [show o + (j + 1) = o + 1 + j from by omega]; exact hS)
        simpa [List.take_succ_cons, List.prod_cons, mul_assoc] using this
      by_cases hS : o ∈ S
      · rw [if_pos hS]
        have := ih (o + 1) (c * a) htail
        simpa [List.prod_cons, mul_assoc] using this
      · rw [if_neg hS]
        have h0 := h 0 (by simp) (by simpa using hS)
        simp only [List.take_succ_cons, List.take_zero, List.prod_cons, List.prod_nil,
          mul_one] at h0
        have := ih (o + 1) (c * a) htail
        rw [h0] at this
        rw [this, List.prod_cons, ← mul_assoc, h0]

/-- **Absorption**: a position set containing every blue position reads a
subword with the same product. -/
theorem prod_subAt_eq_of_blue_subset (u : List M) {S : Finset ℕ}
    (hS : ∀ i, IsBlue u i → i < u.length → i ∈ S) :
    (subAt u S).prod = u.prod := by
  have := prod_subAtFrom_eq u 0 S 1 fun j hj hS' => by
    rw [one_mul, one_mul]
    by_contra hne
    exact hS' (by simpa using hS j hne (by simpa using hj))
  simpa [subAt] using this

/-! ## Domination: the blue positions form the leftmost occurrence -/

/-- A position below the `t`-th blue position and above the `(t−1)`-st is
not blue. -/
lemma not_isBlue_of_lt_of_prev {u : List M} {t j : ℕ} (ht : t < (blueList u).length)
    (hj : j < (blueList u)[t]) (hprev : ∀ s, (hs : s + 1 = t) → (blueList u)[s]'(by omega) < j) :
    ¬ IsBlue u j := by
  intro hb
  have hmem : j ∈ blueList u :=
    mem_blueList.mpr ⟨by have := blueList_lt (List.getElem_mem ht); omega, hb⟩
  obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hmem
  have hp := List.pairwise_iff_getElem.mp (blueList_pairwise u)
  rcases lt_or_ge s t with hst | hst
  · obtain ⟨s', rfl⟩ : ∃ s', t = s' + 1 := ⟨t - 1, by omega⟩
    have h1 := hprev s' rfl
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hst) with rfl | hlt
    · omega
    · have := hp s s' hs (by omega) hlt
      omega
  · rcases eq_or_lt_of_le hst with rfl | hlt
    · omega
    · have := hp t s ht hs hlt
      omega

/-- The letter at an occurrence position of a prefix of the blue subword is
the letter at the corresponding blue position. -/
lemma getElem_eq_of_isOcc_blueWord_take (u : List M) {r : ℕ} {ℓ : List ℕ}
    (hℓ : IsOcc ((blueWord u).take r) u ℓ) {t : ℕ} (ht' : t < ℓ.length)
    (htB : t < (blueList u).length) :
    u[ℓ[t]]'(hℓ.getElem_lt ht')
      = u[(blueList u)[t]]'(blueList_lt (List.getElem_mem htB)) := by
  rw [hℓ.getElem_read ht', List.getElem_take, ← (isOcc_blueList u).getElem_read htB]

/-- **The contradiction**: an occurrence position of the blue subword's
prefix strictly before the corresponding blue position, and after the
previous one, would freeze the prefix product across that blue position. -/
lemma blueList_key (u : List M) {r : ℕ} {ℓ : List ℕ}
    (hℓ : IsOcc ((blueWord u).take r) u ℓ) {t : ℕ} (ht' : t < ℓ.length)
    (htB : t < (blueList u).length) (hlt : ℓ[t] < (blueList u)[t])
    (hprev : ∀ s, (hs : s + 1 = t) → (blueList u)[s]'(by omega) < ℓ[t]) : False := by
  have hB := blueList_lt (List.getElem_mem htB)
  have hj := hℓ.getElem_lt ht'
  -- no blue position in `[ℓ[t], B[t])`
  have hnb : ∀ j', ℓ[t] ≤ j' → j' < (blueList u)[t] → ¬ IsBlue u j' := fun j' h1 h2 =>
    not_isBlue_of_lt_of_prev htB h2 fun s hs => by have := hprev s hs; omega
  have hconst : (u.take (blueList u)[t]).prod = (u.take ℓ[t]).prod :=
    take_prod_eq_of_no_blue u hlt.le hnb
  have hletter := getElem_eq_of_isOcc_blueWord_take u hℓ ht' htB
  have hnbj : ¬ IsBlue u ℓ[t] := hnb _ le_rfl hlt
  rw [IsBlue, not_not, List.prod_take_succ _ _ hj] at hnbj
  have hblue := (mem_blueList.mp (List.getElem_mem htB)).2
  apply hblue
  rw [List.prod_take_succ _ _ hB, ← hletter, hconst, hnbj]

/-- **The blue positions dominate every occurrence of every prefix of the
blue subword.** -/
theorem blueList_le_of_isOcc (u : List M) {r : ℕ} {ℓ : List ℕ}
    (hℓ : IsOcc ((blueWord u).take r) u ℓ) {t : ℕ} (ht' : t < ℓ.length)
    (htB : t < (blueList u).length) :
    (blueList u)[t] ≤ ℓ[t] := by
  induction t with
  | zero =>
      by_contra hlt
      push_neg at hlt
      exact absurd (blueList_key u hℓ ht' htB hlt fun s hs => by omega) id
  | succ t ih =>
      by_contra hlt
      push_neg at hlt
      have hprev : (blueList u)[t] < ℓ[t + 1] := by
        have h1 := ih (by omega) (by omega)
        have h2 : ℓ[t] < ℓ[t + 1] := hℓ.getElem_lt_getElem (by omega) ht'
        omega
      exact absurd (blueList_key u hℓ ht' htB hlt fun s hs => by
        have : s = t := by omega
        subst this
        exact hprev) id

/-! ## The count, in a 𝓙-trivial monoid -/

/-- **A repeated prefix value freezes the stretch in between**: this is
where 𝓙-triviality enters. -/
lemma take_prod_eq_of_eq (hJ : IsJTrivialMonoid M) (u : List M) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (h : (u.take c).prod = (u.take a).prod) :
    (u.take b).prod = (u.take a).prod := by
  have hsplit : ∀ {x y : ℕ}, x ≤ y → JLe (u.take y).prod (u.take x).prod := by
    intro x y hxy
    rw [show u.take y = u.take x ++ (u.drop x).take (y - x) from by
      rw [← List.take_add, Nat.add_sub_cancel' hxy], List.prod_append]
    exact jLe_mul_left _ _
  have h1 := hsplit hab
  have h2 := hsplit hbc
  rw [h] at h2
  exact hJ.eq_of_jLe_jLe h1 h2

/-- The blue positions are pairwise distinct. -/
lemma blueList_nodup (u : List M) : (blueList u).Nodup :=
  (blueList_pairwise u).imp ne_of_lt

/-- **At most `|M| − 1` blue positions** in a 𝓙-trivial monoid: the prefix
products just after the blue positions are pairwise distinct and never
`1`. -/
theorem length_blueList_le (hJ : IsJTrivialMonoid M) (u : List M) :
    (blueList u).length ≤ Fintype.card M - 1 := by
  classical
  rw [← List.toFinset_card_of_nodup (blueList_nodup u)]
  have h := Finset.card_le_card_of_injOn (fun i : ℕ => (u.take (i + 1)).prod)
    (s := (blueList u).toFinset) (t := Finset.univ.erase 1) ?_ ?_
  · rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h
  · intro i hi
    rw [Finset.mem_coe, List.mem_toFinset, mem_blueList] at hi
    rw [Finset.mem_coe, Finset.mem_erase]
    refine ⟨fun h1 => hi.2 ?_, Finset.mem_univ _⟩
    have h1' : (u.take (i + 1)).prod = 1 := h1
    have := take_prod_eq_of_eq hJ u (Nat.zero_le i) (Nat.le_add_right i 1)
      (by rw [h1']; simp)
    rw [h1', this]
    simp
  · intro i hi i' hi' hii'
    rw [Finset.mem_coe, List.mem_toFinset, mem_blueList] at hi hi'
    have hii'' : (u.take (i + 1)).prod = (u.take (i' + 1)).prod := hii'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · apply hi'.2
      have := take_prod_eq_of_eq hJ u (show i + 1 ≤ i' by omega)
        (Nat.le_add_right i' 1) hii''.symm
      exact hii''.symm.trans this.symm
    · apply hi.2
      have := take_prod_eq_of_eq hJ u (show i' + 1 ≤ i by omega)
        (Nat.le_add_right i 1) hii''
      exact hii''.trans this.symm

end MonoidProduct
