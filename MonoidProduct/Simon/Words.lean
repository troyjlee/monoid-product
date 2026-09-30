import Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Words: subwords at position sets, occurrences, greedy embeddings

The combinatorics-on-words layer of the Simon formalization, following Klíma's
proof (*Piecewise testable languages via combinatorics on words*, Discrete
Math. 2011).  Positions are `0`-based naturals.

* `subAtFrom w o S` — the letters of `w` at the positions of `S`, when `w`
  starts at position `o`; `subAt w S := subAtFrom w 0 S`.  The recursion on
  the word is what the prefix-product induction (`Blue.lean`) consumes.
* `readAt w ℓ` — the letters of `w` at a list of positions; an
  **occurrence** of `p` in `w` is a strictly increasing position list inside
  `w` reading `p` (`IsOcc`).  `Sublist` is exactly "some occurrence exists".
* `leftmost p w` — the greedy leftmost occurrence, which **dominates**
  every occurrence of every prefix of `p` componentwise
  (`leftmost_le_of_isOcc`); `rightmost` is its mirror image, obtained by
  reversing the words.
-/

namespace MonoidProduct

open List

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## Subwords at position sets -/

/-- The letters of `w` at the positions in `S`, `w` starting at position
`o`. -/
def subAtFrom : List α → ℕ → Finset ℕ → List α
  | [], _, _ => []
  | a :: w, o, S =>
      if o ∈ S then a :: subAtFrom w (o + 1) S else subAtFrom w (o + 1) S

/-- The subword of `w` at the positions in `S`. -/
def subAt (w : List α) (S : Finset ℕ) : List α := subAtFrom w 0 S

@[simp] lemma subAtFrom_nil (o : ℕ) (S : Finset ℕ) :
    subAtFrom ([] : List α) o S = [] := rfl

lemma subAtFrom_cons (a : α) (w : List α) (o : ℕ) (S : Finset ℕ) :
    subAtFrom (a :: w) o S
      = if o ∈ S then a :: subAtFrom w (o + 1) S else subAtFrom w (o + 1) S :=
  rfl

lemma subAtFrom_sublist (w : List α) (o : ℕ) (S : Finset ℕ) :
    subAtFrom w o S <+ w := by
  induction w generalizing o with
  | nil => exact Sublist.refl _
  | cons a w ih =>
      rw [subAtFrom_cons]
      split_ifs
      · exact (ih (o + 1)).cons₂ a
      · exact (ih (o + 1)).cons a

lemma subAt_sublist (w : List α) (S : Finset ℕ) : subAt w S <+ w :=
  subAtFrom_sublist w 0 S

/-- Only the positions inside the word matter. -/
lemma subAtFrom_congr (w : List α) (o : ℕ) {S T : Finset ℕ}
    (h : ∀ i, o ≤ i → i < o + w.length → (i ∈ S ↔ i ∈ T)) :
    subAtFrom w o S = subAtFrom w o T := by
  induction w generalizing o with
  | nil => rfl
  | cons a w ih =>
      rw [subAtFrom_cons, subAtFrom_cons]
      have h0 : o ∈ S ↔ o ∈ T := h o le_rfl (by simp)
      have ih' := ih (o + 1) fun i hi hi' => h i (by omega)
        (by simp only [length_cons] at *; omega)
      by_cases hS : o ∈ S
      · rw [if_pos hS, if_pos (h0.mp hS), ih']
      · rw [if_neg hS, if_neg (fun hT => hS (h0.mpr hT)), ih']

/-! ## Reading a word at a list of positions -/

/-- The letters of `w` at a list of positions. -/
def readAt (w : List α) (ℓ : List ℕ) : List α := ℓ.map fun i => w.getD i default

@[simp] lemma readAt_nil (w : List α) : readAt w [] = [] := rfl

@[simp] lemma readAt_cons (w : List α) (i : ℕ) (ℓ : List ℕ) :
    readAt w (i :: ℓ) = w.getD i default :: readAt w ℓ := rfl

@[simp] lemma length_readAt (w : List α) (ℓ : List ℕ) :
    (readAt w ℓ).length = ℓ.length := by simp [readAt]

/-- Reading a shifted position list in a longer word. -/
lemma readAt_cons_map_succ (a : α) (w : List α) (ℓ : List ℕ) :
    readAt (a :: w) (ℓ.map (· + 1)) = readAt w ℓ := by
  simp [readAt, List.map_map, Function.comp_def, List.getD_cons_succ]

lemma readAt_reverse (w : List α) (ℓ : List ℕ) (h : ∀ i ∈ ℓ, i < w.length) :
    readAt w.reverse (ℓ.map fun i => w.length - 1 - i) = readAt w ℓ := by
  simp only [readAt, List.map_map, Function.comp_def]
  refine List.map_congr_left fun i hi => ?_
  have hi' := h i hi
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi',
    List.getElem_reverse]
  congr 1
  omega

/-! ## Occurrences -/

/-- `ℓ` is an occurrence of `p` in `w`: a strictly increasing list of
positions inside `w` at which `w` reads `p`. -/
structure IsOcc (p w : List α) (ℓ : List ℕ) : Prop where
  sorted : ℓ.Pairwise (· < ·)
  bounded : ∀ i ∈ ℓ, i < w.length
  read : readAt w ℓ = p

lemma IsOcc.length {p w : List α} {ℓ : List ℕ} (h : IsOcc p w ℓ) :
    ℓ.length = p.length := by
  rw [← h.read, length_readAt]

lemma isOcc_nil (w : List α) : IsOcc [] w [] :=
  ⟨List.Pairwise.nil, by simp, rfl⟩

/-- Shifting an occurrence into a longer word. -/
lemma IsOcc.cons_shift {p w : List α} {ℓ : List ℕ} (a : α)
    (h : IsOcc p w ℓ) : IsOcc p (a :: w) (ℓ.map (· + 1)) where
  sorted := List.pairwise_map.mpr (h.sorted.imp fun hlt => by omega)
  bounded := by
    intro i hi
    rw [List.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have := h.bounded j hj
    simp only [length_cons]
    omega
  read := by rw [readAt_cons_map_succ, h.read]

/-- Extending an occurrence at the front by a match at position `0`. -/
lemma IsOcc.cons_zero {p w : List α} {ℓ : List ℕ} (a : α)
    (h : IsOcc p w ℓ) : IsOcc (a :: p) (a :: w) (0 :: ℓ.map (· + 1)) where
  sorted := by
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, (h.cons_shift a).sorted⟩
    rw [List.mem_map] at hb
    obtain ⟨c, -, rfl⟩ := hb
    omega
  bounded := by
    intro i hi
    rw [List.mem_cons] at hi
    rcases hi with rfl | hi
    · simp
    · exact (h.cons_shift a).bounded i hi
  read := by rw [readAt_cons, readAt_cons_map_succ, h.read]; rfl

/-- Unshifting: an occurrence in `a :: w` avoiding position `0` is a shifted
occurrence in `w`. -/
lemma IsOcc.of_cons_shift {p w : List α} {ℓ : List ℕ} {a : α}
    (h : IsOcc p (a :: w) (ℓ.map (· + 1))) : IsOcc p w ℓ where
  sorted := (List.pairwise_map.mp h.sorted).imp fun hlt => by omega
  bounded := by
    intro i hi
    have := h.bounded (i + 1) (List.mem_map.mpr ⟨i, hi, rfl⟩)
    simp only [length_cons] at this
    omega
  read := by rw [← readAt_cons_map_succ a, h.read]

/-- A position list avoiding `0` is a shifted list. -/
lemma exists_map_succ_of_zero_notMem {ℓ : List ℕ} (h : ∀ i ∈ ℓ, i ≠ 0) :
    ∃ ℓ₀ : List ℕ, ℓ = ℓ₀.map (· + 1) := by
  refine ⟨ℓ.map (· - 1), ?_⟩
  rw [List.map_map]
  conv_lhs => rw [← List.map_id ℓ]
  refine List.map_congr_left fun i hi => ?_
  have := h i hi
  simp only [Function.comp_apply, id_eq]
  omega

/-- **Sublists are exactly the patterns with an occurrence.** -/
theorem sublist_iff_exists_isOcc (p w : List α) :
    p <+ w ↔ ∃ ℓ, IsOcc p w ℓ := by
  constructor
  · intro h
    induction h with
    | slnil => exact ⟨[], isOcc_nil []⟩
    | cons a _ ih =>
        obtain ⟨ℓ, hℓ⟩ := ih
        exact ⟨_, hℓ.cons_shift a⟩
    | cons_cons a _ ih =>
        obtain ⟨ℓ, hℓ⟩ := ih
        exact ⟨_, hℓ.cons_zero a⟩
  · rintro ⟨ℓ, hℓ⟩
    induction w generalizing p ℓ with
    | nil =>
        cases ℓ with
        | nil => rw [← hℓ.read]; exact Sublist.refl _
        | cons i ℓ => have := hℓ.bounded i (by simp); simp at this
    | cons a w ih =>
        cases ℓ with
        | nil => rw [← hℓ.read]; exact nil_sublist _
        | cons i ℓ =>
            by_cases hi : i = 0
            · subst hi
              have hpos : ∀ j ∈ ℓ, j ≠ 0 := by
                intro j hj
                have := List.rel_of_pairwise_cons hℓ.sorted hj
                omega
              obtain ⟨ℓ₀, rfl⟩ := exists_map_succ_of_zero_notMem hpos
              have htail : IsOcc (readAt w ℓ₀) w ℓ₀ :=
                ⟨(List.pairwise_map.mp (List.pairwise_cons.mp hℓ.sorted).2).imp
                    fun hlt => by omega,
                  fun j hj => by
                    have := hℓ.bounded (j + 1)
                      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
                    simp only [length_cons] at this; omega,
                  rfl⟩
              have hp : p = a :: readAt w ℓ₀ := by
                rw [← hℓ.read, readAt_cons, readAt_cons_map_succ]; rfl
              rw [hp]
              exact (ih _ _ htail).cons₂ a
            · have hpos : ∀ j ∈ i :: ℓ, j ≠ 0 := by
                intro j hj
                rw [List.mem_cons] at hj
                rcases hj with rfl | hj
                · exact hi
                · have := List.rel_of_pairwise_cons hℓ.sorted hj; omega
              obtain ⟨ℓ₀, hℓ₀⟩ := exists_map_succ_of_zero_notMem hpos
              rw [hℓ₀] at hℓ
              exact (ih p ℓ₀ hℓ.of_cons_shift).cons a

/-! ## Indexing occurrences -/

/-- The `t`-th position of an occurrence lies inside the word. -/
lemma IsOcc.getElem_lt {p w : List α} {ℓ : List ℕ} (h : IsOcc p w ℓ) {t : ℕ}
    (ht : t < ℓ.length) : ℓ[t] < w.length :=
  h.bounded _ (List.getElem_mem ht)

/-- The letter read at the `t`-th position of an occurrence. -/
lemma IsOcc.getElem_read {p w : List α} {ℓ : List ℕ} (h : IsOcc p w ℓ) {t : ℕ}
    (ht : t < ℓ.length) :
    w[ℓ[t]]'(h.getElem_lt ht) = p[t]'(by rw [← h.length]; exact ht) := by
  have hr := h.read
  subst hr
  simp [readAt, List.getElem?_eq_getElem (h.getElem_lt ht)]

/-- Positions of an occurrence are strictly increasing. -/
lemma IsOcc.getElem_lt_getElem {p w : List α} {ℓ : List ℕ} (h : IsOcc p w ℓ)
    {s t : ℕ} (hs : s < t) (ht : t < ℓ.length) : ℓ[s] < ℓ[t] :=
  List.pairwise_iff_getElem.mp h.sorted s t (by omega) ht hs

/-- Occurrences of a prefix of the pattern: truncation. -/
lemma IsOcc.take {p w : List α} {ℓ : List ℕ} (h : IsOcc p w ℓ) (r : ℕ) :
    IsOcc (p.take r) w (ℓ.take r) where
  sorted := h.sorted.sublist (List.take_sublist r ℓ)
  bounded := fun i hi => h.bounded i (List.mem_of_mem_take hi)
  read := by rw [← h.read, readAt, readAt, List.map_take]

/-! ## The greedy leftmost occurrence -/

/-- The greedy leftmost occurrence of `p` in `w`, if any. -/
def leftmost : List α → List α → Option (List ℕ)
  | [], _ => some []
  | _ :: _, [] => none
  | b :: p, a :: w =>
      if a = b then (leftmost p w).map fun ℓ => 0 :: ℓ.map (· + 1)
      else (leftmost (b :: p) w).map fun ℓ => ℓ.map (· + 1)

@[simp] lemma leftmost_nil (w : List α) : leftmost ([] : List α) w = some [] := by
  cases w <;> rfl

lemma leftmost_cons_nil (b : α) (p : List α) : leftmost (b :: p) [] = none := rfl

lemma leftmost_cons_cons (b : α) (p : List α) (a : α) (w : List α) :
    leftmost (b :: p) (a :: w)
      = if a = b then (leftmost p w).map fun ℓ => 0 :: ℓ.map (· + 1)
        else (leftmost (b :: p) w).map fun ℓ => ℓ.map (· + 1) := rfl

/-- The greedy occurrence is an occurrence. -/
theorem isOcc_of_leftmost {p w : List α} {ℓ : List ℕ}
    (h : leftmost p w = some ℓ) : IsOcc p w ℓ := by
  induction w generalizing p ℓ with
  | nil =>
      cases p with
      | nil => simp at h; subst h; exact isOcc_nil []
      | cons b p => simp [leftmost_cons_nil] at h
  | cons a w ih =>
      cases p with
      | nil => simp at h; subst h; exact isOcc_nil _
      | cons b p =>
          rw [leftmost_cons_cons] at h
          split_ifs at h with hab
          · subst hab
            rw [Option.map_eq_some_iff] at h
            obtain ⟨ℓ₀, h₀, rfl⟩ := h
            exact (ih h₀).cons_zero a
          · rw [Option.map_eq_some_iff] at h
            obtain ⟨ℓ₀, h₀, rfl⟩ := h
            exact (ih h₀).cons_shift a

/-- The greedy occurrence exists exactly for sublists. -/
theorem leftmost_isSome_iff (p w : List α) :
    (leftmost p w).isSome ↔ p <+ w := by
  constructor
  · intro h
    obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp h
    exact (sublist_iff_exists_isOcc p w).mpr ⟨ℓ, isOcc_of_leftmost hℓ⟩
  · intro h
    induction w generalizing p with
    | nil =>
        rw [List.sublist_nil] at h
        subst h
        simp
    | cons a w ih =>
        cases p with
        | nil => simp
        | cons b p =>
            rw [leftmost_cons_cons]
            split_ifs with hab
            · subst hab
              obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp
                (ih p (List.Sublist.of_cons_cons h))
              simp [hℓ]
            · have h' : b :: p <+ w := by
                rcases List.sublist_cons_iff.mp h with h' | ⟨r, hr, -⟩
                · exact h'
                · exact absurd (List.head_eq_of_cons_eq hr).symm hab
              obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp (ih (b :: p) h')
              simp [hℓ]

/-- **Domination**: the greedy leftmost occurrence of `p` is componentwise at
most every occurrence of every prefix of `p`. -/
theorem leftmost_le_of_isOcc {p w : List α} {ℓ : List ℕ}
    (h : leftmost p w = some ℓ) {r : ℕ} {ℓ' : List ℕ}
    (h' : IsOcc (p.take r) w ℓ') {t : ℕ} (ht : t < r) (ht' : t < ℓ'.length) :
    ℓ[t]'(by
      have h1 := (isOcc_of_leftmost h).length
      have h2 := h'.length
      rw [List.length_take] at h2
      omega) ≤ ℓ'[t] := by
  induction w generalizing p ℓ r ℓ' t with
  | nil =>
      cases p with
      | nil =>
          have := h'.length
          simp only [List.take_nil, List.length_nil] at this
          omega
      | cons b p => simp [leftmost_cons_nil] at h
  | cons a w ih =>
      cases p with
      | nil =>
          have := h'.length
          simp only [List.take_nil, List.length_nil] at this
          omega
      | cons b p =>
          cases r with
          | zero => omega
          | succ r =>
              rw [List.take_succ_cons] at h'
              rw [leftmost_cons_cons] at h
              split_ifs at h with hab
              · rw [Option.map_eq_some_iff] at h
                obtain ⟨ℓ₀, h₀, rfl⟩ := h
                cases ℓ' with
                | nil => simp at ht'
                | cons i ℓ' =>
                    cases t with
                    | zero => simp
                    | succ t =>
                        have hpos : ∀ j ∈ ℓ', j ≠ 0 := by
                          intro j hj
                          have := List.rel_of_pairwise_cons h'.sorted hj
                          omega
                        obtain ⟨ℓ₁, rfl⟩ := exists_map_succ_of_zero_notMem hpos
                        have h₁ : IsOcc (p.take r) w ℓ₁ := by
                          refine IsOcc.of_cons_shift (a := a) ?_
                          refine ⟨(List.pairwise_cons.mp h'.sorted).2,
                            fun j hj => h'.bounded j (List.mem_cons_of_mem _ hj), ?_⟩
                          have := h'.read
                          rw [readAt_cons] at this
                          exact List.tail_eq_of_cons_eq this
                        simp only [List.getElem_cons_succ, List.getElem_map]
                        have := ih (r := r) (t := t) h₀ h₁ (by omega)
                          (by simpa using ht')
                        omega
              · rw [Option.map_eq_some_iff] at h
                obtain ⟨ℓ₀, h₀, rfl⟩ := h
                have hpos : ∀ j ∈ ℓ', j ≠ 0 := by
                  intro j hj
                  rintro rfl
                  cases ℓ' with
                  | nil => simp at hj
                  | cons i ℓ' =>
                      have hi0 : i = 0 := by
                        rw [List.mem_cons] at hj
                        rcases hj with h | h
                        · exact h.symm
                        · have := List.rel_of_pairwise_cons h'.sorted h; omega
                      subst hi0
                      have := h'.read
                      rw [readAt_cons] at this
                      have hb : a = b := by
                        have := List.head_eq_of_cons_eq this
                        simpa using this
                      exact hab hb
                obtain ⟨ℓ₁, rfl⟩ := exists_map_succ_of_zero_notMem hpos
                have h₁ : IsOcc ((b :: p).take (r + 1)) w ℓ₁ :=
                  IsOcc.of_cons_shift (by rw [List.take_succ_cons]; exact h')
                simp only [List.getElem_map]
                have := ih (r := r + 1) (t := t) h₀ h₁ ht (by simpa using ht')
                omega

/-! ## The greedy rightmost occurrence, by reversal -/

/-- Reversing an occurrence. -/
lemma IsOcc.reverse {p w : List α} {ℓ : List ℕ} (h : IsOcc p w ℓ) :
    IsOcc p.reverse w.reverse ((ℓ.map fun i => w.length - 1 - i).reverse) where
  sorted := by
    rw [List.pairwise_reverse, List.pairwise_map]
    refine h.sorted.imp_of_mem fun {i j} hi hj hij => ?_
    have := h.bounded j hj
    omega
  bounded := by
    intro i hi
    rw [List.mem_reverse, List.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have := h.bounded j hj
    rw [List.length_reverse]
    omega
  read := by
    rw [readAt, List.map_reverse, ← readAt, readAt_reverse w ℓ h.bounded, h.read]

/-- The greedy rightmost occurrence: the leftmost occurrence in the reversed
words, read back through `i ↦ |w| − 1 − i`. -/
def rightmost (p w : List α) : Option (List ℕ) :=
  (leftmost p.reverse w.reverse).map fun ℓ =>
    (ℓ.map fun i => w.length - 1 - i).reverse

/-- Un-reversing an occurrence. -/
lemma IsOcc.of_reverse {p w : List α} {ℓ : List ℕ}
    (h : IsOcc p.reverse w.reverse ℓ) :
    IsOcc p w ((ℓ.map fun i => w.length - 1 - i).reverse) := by
  have h' := h.reverse
  rw [List.reverse_reverse, List.reverse_reverse, List.length_reverse] at h'
  exact h'

theorem isOcc_of_rightmost {p w : List α} {ρ : List ℕ}
    (h : rightmost p w = some ρ) : IsOcc p w ρ := by
  rw [rightmost, Option.map_eq_some_iff] at h
  obtain ⟨ℓ, hℓ, rfl⟩ := h
  exact (isOcc_of_leftmost hℓ).of_reverse

theorem rightmost_isSome_iff (p w : List α) :
    (rightmost p w).isSome ↔ p <+ w := by
  rw [rightmost, Option.isSome_map, leftmost_isSome_iff, List.reverse_sublist]

/-- The reversal of a suffix of `p` is a prefix of the reversal of `p`. -/
lemma reverse_drop_eq_take_reverse (p : List α) (s : ℕ) :
    (p.drop s).reverse = p.reverse.take (p.length - s) := by
  rw [List.take_reverse]
  by_cases hs : s ≤ p.length
  · rw [show p.length - (p.length - s) = s from by omega]
  · rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]

/-- Indexing a reversed, mapped position list. -/
lemma getElem_reverse_map (f : ℕ → ℕ) (ℓ : List ℕ) {i : ℕ} (hi : i < ℓ.length) :
    ((ℓ.map f).reverse)[i]'(by simp; omega) = f (ℓ[ℓ.length - 1 - i]'(by omega)) := by
  simp [List.getElem_reverse]

/-- **Domination from above**: the greedy rightmost occurrence of `p` is
componentwise at least every occurrence of every suffix of `p`. -/
theorem le_rightmost_of_isOcc {p w : List α} {ρ : List ℕ}
    (h : rightmost p w = some ρ) {s : ℕ} {ℓ' : List ℕ}
    (h' : IsOcc (p.drop s) w ℓ') {t : ℕ} (ht' : t < ℓ'.length) :
    ℓ'[t] ≤ ρ[s + t]'(by
      have h1 := (isOcc_of_rightmost h).length
      have h2 := h'.length
      rw [List.length_drop] at h2
      omega) := by
  rw [rightmost, Option.map_eq_some_iff] at h
  obtain ⟨ℓ, hℓ, rfl⟩ := h
  have hℓocc := isOcc_of_leftmost hℓ
  have hℓlen := hℓocc.length
  rw [List.length_reverse] at hℓlen
  have h'len := h'.length
  rw [List.length_drop] at h'len
  -- the reversed occurrence of the reversed suffix, a prefix of `p.reverse`
  have h'' := h'.reverse
  rw [reverse_drop_eq_take_reverse] at h''
  have hdom := leftmost_le_of_isOcc hℓ h'' (r := p.length - s)
    (t := ℓ'.length - 1 - t) (by omega) (by simp; omega)
  -- unfold the two reversed indexings
  have hb := h'.getElem_lt ht'
  rw [getElem_reverse_map _ _ (by omega)] at hdom
  have e1 : ℓ'[ℓ'.length - 1 - (ℓ'.length - 1 - t)]'(by omega) = ℓ'[t] := by
    congr 1
    omega
  rw [e1] at hdom
  rw [getElem_reverse_map _ _ (by omega)]
  have e2 : ℓ[ℓ.length - 1 - (s + t)]'(by omega) = ℓ[ℓ'.length - 1 - t]'(by omega) := by
    congr 1
    omega
  rw [e2]
  omega

/-! ## Subwords at position sets, as filtered readings -/

/-- `subAtFrom` reads the word at the in-range positions of `S`, in
order. -/
lemma subAtFrom_eq_readAt (w : List α) (o : ℕ) (S : Finset ℕ) :
    subAtFrom w o S
      = readAt w ((List.range w.length).filter fun i => decide (o + i ∈ S)) := by
  induction w generalizing o with
  | nil => rfl
  | cons a w ih =>
      rw [subAtFrom_cons, ih (o + 1), List.length_cons, List.range_succ_eq_map,
        List.filter_cons, List.filter_map]
      have hpred : ((fun i => decide (o + i ∈ S)) ∘ Nat.succ)
          = fun i => decide (o + 1 + i ∈ S) := by
        funext i
        simp only [Function.comp_apply, Nat.succ_eq_add_one]
        congr 1
        exact propext ⟨fun h => by rwa [Nat.add_right_comm], fun h => by rwa [Nat.add_right_comm] at h⟩
      rw [hpred]
      have hmap : ∀ L : List ℕ, readAt (a :: w) (L.map Nat.succ) = readAt w L := fun L =>
        readAt_cons_map_succ a w L
      by_cases hS : o ∈ S
      · rw [if_pos hS, if_pos (by simpa using hS), readAt_cons, hmap]
        rfl
      · rw [if_neg hS, if_neg (by simpa using hS), hmap]

lemma subAt_eq_readAt (w : List α) (S : Finset ℕ) :
    subAt w S = readAt w ((List.range w.length).filter fun i => decide (i ∈ S)) := by
  rw [subAt, subAtFrom_eq_readAt]
  simp

/-! ## Concatenating and splitting occurrences -/

lemma IsOcc.append {p q w : List α} {ℓ₁ ℓ₂ : List ℕ} (h₁ : IsOcc p w ℓ₁)
    (h₂ : IsOcc q w ℓ₂) (hlt : ∀ i ∈ ℓ₁, ∀ j ∈ ℓ₂, i < j) :
    IsOcc (p ++ q) w (ℓ₁ ++ ℓ₂) where
  sorted := List.pairwise_append.mpr ⟨h₁.sorted, h₂.sorted, hlt⟩
  bounded := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact h₁.bounded i hi
    · exact h₂.bounded i hi
  read := by rw [readAt, List.map_append, ← readAt, ← readAt, h₁.read, h₂.read]

lemma IsOcc.split {p q w : List α} {ℓ : List ℕ} (h : IsOcc (p ++ q) w ℓ) :
    IsOcc p w (ℓ.take p.length) ∧ IsOcc q w (ℓ.drop p.length) := by
  have hlen : ℓ.length = p.length + q.length := by rw [h.length, List.length_append]
  refine ⟨⟨h.sorted.sublist (List.take_sublist _ _),
      fun i hi => h.bounded i (List.mem_of_mem_take hi), ?_⟩,
    ⟨h.sorted.sublist (List.drop_sublist _ _),
      fun i hi => h.bounded i (List.mem_of_mem_drop hi), ?_⟩⟩
  · rw [readAt, List.map_take, ← readAt, h.read, List.take_left]
  · rw [readAt, List.map_drop, ← readAt, h.read, List.drop_left]

/-! ## Strictly increasing lists are determined by their members -/

lemma eq_of_pairwise_lt_of_mem_iff {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· < ·))
    (h₂ : l₂.Pairwise (· < ·)) (h : ∀ i, i ∈ l₁ ↔ i ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons b l₂ => exact absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | cons a l₁ ih =>
      cases l₂ with
      | nil => exact absurd ((h a).mp (List.mem_cons_self ..)) (by simp)
      | cons b l₂ =>
          have hab : a = b := by
            have ha := (h a).mp (List.mem_cons_self ..)
            have hb := (h b).mpr (List.mem_cons_self ..)
            rw [List.mem_cons] at ha hb
            rcases ha with ha | ha
            · exact ha
            · rcases hb with hb | hb
              · exact hb.symm
              · have := List.rel_of_pairwise_cons h₂ ha
                have := List.rel_of_pairwise_cons h₁ hb
                omega
          subst hab
          congr 1
          refine ih (List.pairwise_cons.mp h₁).2 (List.pairwise_cons.mp h₂).2 fun i => ?_
          constructor
          · intro hi
            have := (h i).mp (List.mem_cons_of_mem _ hi)
            rw [List.mem_cons] at this
            rcases this with rfl | this
            · have := List.rel_of_pairwise_cons h₁ hi; omega
            · exact this
          · intro hi
            have := (h i).mpr (List.mem_cons_of_mem _ hi)
            rw [List.mem_cons] at this
            rcases this with rfl | this
            · have := List.rel_of_pairwise_cons h₂ hi; omega
            · exact this

/-- **Reading through an order isomorphism of position lists**: a strictly
monotone map between two increasing position lists that preserves the
letters read gives the same reading. -/
lemma readAt_eq_of_orderIso {u v : List α} {Lu Lv : List ℕ} (f : ℕ → ℕ)
    (hLu : Lu.Pairwise (· < ·)) (hLv : Lv.Pairwise (· < ·))
    (hmono : ∀ i ∈ Lu, ∀ i' ∈ Lu, i < i' → f i < f i')
    (himage : ∀ j, j ∈ Lv ↔ ∃ i ∈ Lu, f i = j)
    (hletter : ∀ i ∈ Lu, u.getD i default = v.getD (f i) default) :
    readAt u Lu = readAt v Lv := by
  have hLv' : Lv = Lu.map f := by
    refine eq_of_pairwise_lt_of_mem_iff hLv ?_ fun j => ?_
    · exact List.pairwise_map.mpr (hLu.imp_of_mem fun {i i'} hi hi' hii' =>
        hmono i hi i' hi' hii')
    · rw [himage, List.mem_map]
  rw [hLv', readAt, readAt, List.map_map]
  exact (List.map_congr_left fun i hi => (hletter i hi).symm).symm

end MonoidProduct
