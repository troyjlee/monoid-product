import MonoidProduct.Simon.Red
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Simon's kernel: short subwords determine the product

`monoid.tex`'s Simon transfer needs the **bounded short-subword kernel**: in
a finite 𝓙-trivial monoid `M` with `m = |M|`, two words with the same
subwords of length `≤ 2m − 2` have the same product.  This is the
monoid-morphism form of the `2m − 2` short-subword estimate proved in
Klíma's Lemma 3 (*Piecewise testable languages via combinatorics on
words*, Discrete Math. 311, 2011), which is stated at the level of a
𝓙-trivial congruence of index `m`; the constant improves Simon's `2m − 1`,
as Klíma notes.  The proof architecture below follows Klíma's.

The argument.  Let `a` be the blue subword of `u` (at most `m − 1`
letters), `b` the red subword of `v`.  Both are short, so `a` occurs in `v`
and `b` in `u`; take the leftmost occurrence `I` of `a` in `v` and the
rightmost occurrence `J` of `b` in `u`.  The blue positions `B` of `u` and
`I` are both **left-dominating** occurrences of `a` (at or before every
occurrence of every prefix), the red positions `R` of `v` and `J` are
**right-dominating** occurrences of `b`.  For such pairs the relative order
of the `t`-th left position and the `s`-th right position is decided by
two subword tests of length `≤ 2m − 2` — the pattern
`a.take (t+1) ++ b.drop s` decides `<`, and with the shared letter dropped
it decides `≤` when the letters agree — so the interleavings of `B, J` in
`u` and of `I, R` in `v` coincide.  Reading `u` at `B ∪ J` and `v` at
`I ∪ R` therefore gives the same word, and both readings keep the product
by absorption (`B ⊆ B ∪ J` contains the blue positions, `R ⊆ I ∪ R` the red
ones).
-/

namespace MonoidProduct
open QuantumQueryComplexity

open List

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

attribute [local instance] monoidInhabited

/-! ## Occurrences of suffixes -/

lemma IsOcc.drop {p w : List M} {ℓ : List ℕ} (h : IsOcc p w ℓ) (s : ℕ) :
    IsOcc (p.drop s) w (ℓ.drop s) where
  sorted := h.sorted.sublist (List.drop_sublist s ℓ)
  bounded := fun i hi => h.bounded i (List.mem_of_mem_drop hi)
  read := by rw [readAt, List.map_drop, ← readAt, h.read]

/-! ## Dominating occurrences -/

/-- A **left-dominating** occurrence of `a`: at or before every occurrence
of every prefix of `a`, componentwise. -/
structure LeftDom (a w : List M) (P : List ℕ) : Prop where
  occ : IsOcc a w P
  dom : ∀ {r : ℕ} {ℓ : List ℕ}, IsOcc (a.take r) w ℓ →
    ∀ {t : ℕ} (ht : t < ℓ.length) (htP : t < P.length), P[t] ≤ ℓ[t]

/-- A **right-dominating** occurrence of `b`: at or after every occurrence
of every suffix of `b`, componentwise. -/
structure RightDom (b w : List M) (Q : List ℕ) : Prop where
  occ : IsOcc b w Q
  dom : ∀ {s : ℕ} {ℓ : List ℕ}, IsOcc (b.drop s) w ℓ →
    ∀ {t : ℕ} (ht : t < ℓ.length) (hs : s + t < Q.length), ℓ[t] ≤ Q[s + t]

lemma leftDom_blue (u : List M) : LeftDom (blueWord u) u (blueList u) :=
  ⟨isOcc_blueList u, fun {r ℓ} h {t} ht htB => blueList_le_of_isOcc u h ht htB⟩

lemma rightDom_red (v : List M) : RightDom (redWord v) v (redList v) :=
  ⟨isOcc_redList v, fun {s ℓ} h {t} ht hs => le_redList_of_isOcc v h ht hs⟩

lemma leftDom_leftmost {a w : List M} {P : List ℕ} (h : leftmost a w = some P) :
    LeftDom a w P :=
  ⟨isOcc_of_leftmost h, fun {r ℓ} h' {t} ht htP => by
    have hlen := h'.length
    rw [List.length_take] at hlen
    exact leftmost_le_of_isOcc h h' (r := r) (by omega) ht⟩

lemma rightDom_rightmost {b w : List M} {Q : List ℕ} (h : rightmost b w = some Q) :
    RightDom b w Q :=
  ⟨isOcc_of_rightmost h, fun {s ℓ} h' {t} ht _ => le_rightmost_of_isOcc h h' ht⟩

lemma LeftDom.length {a w : List M} {P : List ℕ} (hP : LeftDom a w P) :
    P.length = a.length := hP.occ.length

lemma RightDom.length {b w : List M} {Q : List ℕ} (hQ : RightDom b w Q) :
    Q.length = b.length := hQ.occ.length

/-! ## The comparison lemmas -/

section Compare

variable {a b w : List M} {P Q : List ℕ} (hP : LeftDom a w P) (hQ : RightDom b w Q)
  {t s : ℕ} (ht : t < a.length) (hs : s < b.length)

include hP hQ ht hs

/-- The `<` test pattern: `a.take (t+1) ++ b.drop s`. -/
lemma lt_of_sublist (h : List.Sublist (a.take (t + 1) ++ b.drop s) w) :
    P[t]'(by rw [hP.length]; exact ht) < Q[s]'(by rw [hQ.length]; exact hs) := by
  have hPl := hP.length
  have hQl := hQ.length
  obtain ⟨ℓ, hℓ⟩ := (sublist_iff_exists_isOcc _ _).mp h
  obtain ⟨h₁, h₂⟩ := hℓ.split
  have hlen := hℓ.length
  rw [List.length_append, List.length_take, List.length_drop] at hlen
  have hta : (a.take (t + 1)).length = t + 1 := by rw [List.length_take]; omega
  have h₁len : (ℓ.take (a.take (t + 1)).length).length = t + 1 := by
    rw [List.length_take, hta]; omega
  have h₂len : (ℓ.drop (a.take (t + 1)).length).length = b.length - s := by
    rw [List.length_drop, hta]; omega
  have hd1 := hP.dom h₁ (t := t) (by omega) (by omega)
  have hd2 := hQ.dom h₂ (t := 0) (by omega) (by omega)
  simp only [List.getElem_take, List.getElem_drop, Nat.add_zero] at hd1 hd2
  have hlt : ℓ[t]'(by omega) < ℓ[(a.take (t + 1)).length]'(by omega) :=
    hℓ.getElem_lt_getElem (by omega) (by omega)
  omega

/-- The `<` test pattern occurs when the positions are ordered. -/
lemma sublist_of_lt (h : P[t]'(by rw [hP.length]; exact ht)
    < Q[s]'(by rw [hQ.length]; exact hs)) :
    List.Sublist (a.take (t + 1) ++ b.drop s) w := by
  have hPl := hP.length
  have hQl := hQ.length
  refine (sublist_iff_exists_isOcc _ _).mpr ⟨_, (hP.occ.take (t + 1)).append (hQ.occ.drop s) ?_⟩
  intro i hi j hj
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hi
  obtain ⟨n', hn', rfl⟩ := List.getElem_of_mem hj
  rw [List.length_take] at hn
  rw [List.length_drop] at hn'
  simp only [List.getElem_take, List.getElem_drop]
  have h1 : P[n]'(by omega) ≤ P[t]'(by omega) := by
    rcases eq_or_lt_of_le (show n ≤ t by omega) with rfl | hlt
    · exact le_rfl
    · exact (List.pairwise_iff_getElem.mp hP.occ.sorted n t (by omega) (by omega) hlt).le
  have h2 : Q[s]'(by omega) ≤ Q[s + n']'(by omega) := by
    rcases Nat.eq_zero_or_pos n' with rfl | hpos
    · exact le_rfl
    · exact (List.pairwise_iff_getElem.mp hQ.occ.sorted s (s + n') (by omega) (by omega)
        (by omega)).le
  omega

lemma lt_iff_sublist :
    P[t]'(by rw [hP.length]; exact ht) < Q[s]'(by rw [hQ.length]; exact hs)
      ↔ List.Sublist (a.take (t + 1) ++ b.drop s) w :=
  ⟨sublist_of_lt hP hQ ht hs, lt_of_sublist hP hQ ht hs⟩

/-- The `≤` test pattern, for a shared letter: `a.take (t+1) ++ b.drop (s+1)`. -/
lemma le_iff_sublist (hc : a[t] = b[s]) :
    P[t]'(by rw [hP.length]; exact ht) ≤ Q[s]'(by rw [hQ.length]; exact hs)
      ↔ List.Sublist (a.take (t + 1) ++ b.drop (s + 1)) w := by
  have hPl := hP.length
  have hQl := hQ.length
  constructor
  · intro hle
    refine (sublist_iff_exists_isOcc _ _).mpr
      ⟨_, (hP.occ.take (t + 1)).append (hQ.occ.drop (s + 1)) ?_⟩
    intro i hi j hj
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hi
    obtain ⟨n', hn', rfl⟩ := List.getElem_of_mem hj
    rw [List.length_take] at hn
    rw [List.length_drop] at hn'
    simp only [List.getElem_take, List.getElem_drop]
    have h1 : P[n]'(by omega) ≤ P[t]'(by omega) := by
      rcases eq_or_lt_of_le (show n ≤ t by omega) with rfl | hlt
      · exact le_rfl
      · exact (List.pairwise_iff_getElem.mp hP.occ.sorted n t (by omega) (by omega) hlt).le
    have h2 : Q[s]'(by omega) < Q[s + 1 + n']'(by omega) :=
      List.pairwise_iff_getElem.mp hQ.occ.sorted s (s + 1 + n') (by omega) (by omega)
        (by omega)
    omega
  · intro h
    -- every position of the rightmost tail lies after `P[t]`
    have htail : ∀ j ∈ Q.drop (s + 1), P[t]'(by omega) < j := by
      intro j hj
      obtain ⟨n', hn', rfl⟩ := List.getElem_of_mem hj
      rw [List.length_drop] at hn'
      simp only [List.getElem_drop]
      obtain ⟨ℓ, hℓ⟩ := (sublist_iff_exists_isOcc _ _).mp h
      obtain ⟨h₁, h₂⟩ := hℓ.split
      have hlen := hℓ.length
      rw [List.length_append, List.length_take, List.length_drop] at hlen
      have hta : (a.take (t + 1)).length = t + 1 := by rw [List.length_take]; omega
      have hd1 := hP.dom h₁ (t := t) (by rw [List.length_take, hta]; omega) (by omega)
      have hd2 := hQ.dom h₂ (t := 0) (by rw [List.length_drop, hta]; omega) (by omega)
      simp only [List.getElem_take, List.getElem_drop, Nat.add_zero] at hd1 hd2
      have hlt : ℓ[t]'(by omega) < ℓ[(a.take (t + 1)).length]'(by omega) :=
        hℓ.getElem_lt_getElem (by omega) (by omega)
      have h3 : Q[s + 1]'(by omega) ≤ Q[s + 1 + n']'(by omega) := by
        rcases Nat.eq_zero_or_pos n' with rfl | hpos
        · exact le_rfl
        · exact (List.pairwise_iff_getElem.mp hQ.occ.sorted _ _ (by omega) (by omega)
            (by omega)).le
      omega
    -- `P[t] :: Q.drop (s+1)` is an occurrence of `b.drop s`
    have hocc : IsOcc (b.drop s) w (P[t]'(by omega) :: Q.drop (s + 1)) := by
      refine ⟨List.pairwise_cons.mpr ⟨htail, (hQ.occ.drop (s + 1)).sorted⟩, ?_, ?_⟩
      · intro i hi
        rw [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact hP.occ.getElem_lt _
        · exact (hQ.occ.drop (s + 1)).bounded i hi
      · rw [readAt_cons, (hQ.occ.drop (s + 1)).read, List.drop_eq_getElem_cons hs,
          List.getD_eq_getElem _ _ (hP.occ.getElem_lt _), hP.occ.getElem_read, hc]
    have := hQ.dom hocc (t := 0) (by simp) (by omega)
    simpa using this

/-- Positions with different letters differ. -/
lemma ne_of_letter_ne (hc : a[t] ≠ b[s]) :
    P[t]'(by rw [hP.length]; exact ht) ≠ Q[s]'(by rw [hQ.length]; exact hs) := by
  intro heq
  apply hc
  rw [← hP.occ.getElem_read (t := t) (by rw [hP.length]; exact ht),
    ← hQ.occ.getElem_read (t := s) (by rw [hQ.length]; exact hs)]
  simp only [heq]

end Compare

/-! ## Transfer between the two words -/

section Transfer

variable {a b u v : List M} {B J I R : List ℕ}
  (hB : LeftDom a u B) (hJ : RightDom b u J) (hI : LeftDom a v I) (hR : RightDom b v R)
  (htest : ∀ p : List M, p.length ≤ a.length + b.length →
    (List.Sublist p u ↔ List.Sublist p v))
  {t s : ℕ} (ht : t < a.length) (hs : s < b.length)

include hB hJ hI hR htest ht hs

lemma lt_iff_lt :
    B[t]'(by rw [hB.length]; exact ht) < J[s]'(by rw [hJ.length]; exact hs)
      ↔ I[t]'(by rw [hI.length]; exact ht) < R[s]'(by rw [hR.length]; exact hs) := by
  rw [lt_iff_sublist hB hJ ht hs, lt_iff_sublist hI hR ht hs]
  exact htest _ (by rw [List.length_append, List.length_take, List.length_drop]; omega)

lemma le_iff_le (hc : a[t] = b[s]) :
    B[t]'(by rw [hB.length]; exact ht) ≤ J[s]'(by rw [hJ.length]; exact hs)
      ↔ I[t]'(by rw [hI.length]; exact ht) ≤ R[s]'(by rw [hR.length]; exact hs) := by
  rw [le_iff_sublist hB hJ ht hs hc, le_iff_sublist hI hR ht hs hc]
  exact htest _ (by rw [List.length_append, List.length_take, List.length_drop]; omega)

lemma eq_iff_eq :
    B[t]'(by rw [hB.length]; exact ht) = J[s]'(by rw [hJ.length]; exact hs)
      ↔ I[t]'(by rw [hI.length]; exact ht) = R[s]'(by rw [hR.length]; exact hs) := by
  by_cases hc : a[t] = b[s]
  · have h1 := le_iff_le hB hJ hI hR htest ht hs hc
    have h2 := lt_iff_lt hB hJ hI hR htest ht hs
    constructor
    · intro h
      have := h1.mp h.le
      have := fun h' => (h2.mpr h').ne h
      omega
    · intro h
      have := h1.mpr h.le
      have := fun h' => (h2.mp h').ne h
      omega
  · exact ⟨fun h => absurd h (ne_of_letter_ne hB hJ ht hs hc),
      fun h => absurd h (ne_of_letter_ne hI hR ht hs hc)⟩

lemma gt_iff_gt :
    J[s]'(by rw [hJ.length]; exact hs) < B[t]'(by rw [hB.length]; exact ht)
      ↔ R[s]'(by rw [hR.length]; exact hs) < I[t]'(by rw [hI.length]; exact ht) := by
  have h1 := lt_iff_lt hB hJ hI hR htest ht hs
  have h2 := eq_iff_eq hB hJ hI hR htest ht hs
  constructor
  · intro h
    have h1' : ¬ (I[t]'(by rw [hI.length]; exact ht) < R[s]'(by rw [hR.length]; exact hs)) :=
      fun h' => absurd (h1.mpr h') (by omega)
    have h2' : ¬ (I[t]'(by rw [hI.length]; exact ht) = R[s]'(by rw [hR.length]; exact hs)) :=
      fun h' => absurd (h2.mpr h') (by omega)
    omega
  · intro h
    have h1' : ¬ (B[t]'(by rw [hB.length]; exact ht) < J[s]'(by rw [hJ.length]; exact hs)) :=
      fun h' => absurd (h1.mp h') (by omega)
    have h2' : ¬ (B[t]'(by rw [hB.length]; exact ht) = J[s]'(by rw [hJ.length]; exact hs)) :=
      fun h' => absurd (h2.mp h') (by omega)
    omega

end Transfer

/-! ## The theorem -/

/-- `idxOf` inverts `getElem` on a list without duplicates. -/
lemma idxOf_getElem_of_nodup {L : List ℕ} (hL : L.Nodup) {t : ℕ} (ht : t < L.length) :
    L.idxOf L[t] = t := by
  have hlt : L.idxOf L[t] < L.length :=
    List.idxOf_lt_length_iff.mpr (List.getElem_mem ht)
  exact hL.getElem_inj_iff.mp (List.getElem_idxOf hlt)

/-- In a strictly increasing list, the position order is the index order. -/
lemma index_lt_of_getElem_lt {L : List ℕ} (hL : L.Pairwise (· < ·)) {t t' : ℕ}
    (ht : t < L.length) (ht' : t' < L.length) (h : L[t] < L[t']) : t < t' := by
  by_contra hle
  rcases eq_or_lt_of_le (not_lt.mp hle) with rfl | hlt
  · exact lt_irrefl _ h
  · have := List.pairwise_iff_getElem.mp hL t' t ht' ht hlt
    omega

/-- **Simon's kernel** (Klíma's Lemma 3): in a finite 𝓙-trivial monoid with
`m` elements, two words with the same subwords of length `≤ 2m − 2` have
the same product. -/
theorem prod_eq_of_sublist_iff (hJ : IsJTrivialMonoid M) (u v : List M)
    (hsub : ∀ p : List M, p.length ≤ 2 * Fintype.card M - 2 →
      (List.Sublist p u ↔ List.Sublist p v)) :
    u.prod = v.prod := by
  classical
  -- the four dominating occurrences
  have hm : 1 ≤ Fintype.card M := Fintype.card_pos
  have hBlen := length_blueList_le hJ u
  have hRlen := length_redList_le hJ v
  have halen : (blueWord u).length = (blueList u).length := by simp [blueWord]
  have hblen : (redWord v).length = (redList v).length := by simp [redWord]
  have htest : ∀ p : List M, p.length ≤ (blueWord u).length + (redWord v).length →
      (List.Sublist p u ↔ List.Sublist p v) := fun p hp => hsub p (by omega)
  have haV : List.Sublist (blueWord u) v := (htest _ (by omega)).mp (blueWord_sublist u)
  have hbU : List.Sublist (redWord v) u := (htest _ (by omega)).mpr (redWord_sublist v)
  obtain ⟨Iv, hIv⟩ := Option.isSome_iff_exists.mp ((leftmost_isSome_iff _ v).mpr haV)
  obtain ⟨Ju, hJu⟩ := Option.isSome_iff_exists.mp ((rightmost_isSome_iff _ u).mpr hbU)
  have hBd : LeftDom (blueWord u) u (blueList u) := leftDom_blue u
  have hRd : RightDom (redWord v) v (redList v) := rightDom_red v
  have hId : LeftDom (blueWord u) v Iv := leftDom_leftmost hIv
  have hJd : RightDom (redWord v) u Ju := rightDom_rightmost hJu
  have hIlen := hId.length
  have hJlen := hJd.length
  set Bu := blueList u with hBu
  set Rv := redList v with hRv
  have hBnd : Bu.Nodup := blueList_nodup u
  have hJnd : Ju.Nodup := hJd.occ.sorted.imp ne_of_lt
  -- the position sets and the map between them
  set Su : Finset ℕ := Bu.toFinset ∪ Ju.toFinset with hSu
  set Sv : Finset ℕ := Iv.toFinset ∪ Rv.toFinset with hSv
  set f : ℕ → ℕ := fun i => if i ∈ Bu then Iv.getD (Bu.idxOf i) 0 else Rv.getD (Ju.idxOf i) 0
    with hf
  have fB : ∀ t (ht : t < Bu.length), f Bu[t] = Iv[t]'(by omega) := by
    intro t ht
    simp only [hf, if_pos (List.getElem_mem ht), idxOf_getElem_of_nodup hBnd ht]
    exact List.getD_eq_getElem _ _ (by omega)
  have fJ : ∀ s (hs : s < Ju.length), f Ju[s] = Rv[s]'(by omega) := by
    intro s hs
    by_cases hmem : Ju[s] ∈ Bu
    · obtain ⟨t, ht, hts⟩ := List.getElem_of_mem hmem
      rw [← hts, fB t ht]
      have := (eq_iff_eq hBd hJd hId hRd htest (by omega) (by omega)).mp hts
      exact this
    · simp only [hf, if_neg hmem, idxOf_getElem_of_nodup hJnd hs]
      exact List.getD_eq_getElem _ _ (by omega)
  -- membership in the merged position lists
  set Lu := (List.range u.length).filter fun i => decide (i ∈ Su) with hLu
  set Lv := (List.range v.length).filter fun i => decide (i ∈ Sv) with hLv
  have hmemLu : ∀ i, i ∈ Lu ↔ i ∈ Bu ∨ i ∈ Ju := by
    intro i
    rw [hLu, List.mem_filter, List.mem_range, decide_eq_true_eq, hSu, Finset.mem_union,
      List.mem_toFinset, List.mem_toFinset]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rcases h with h | h
      · exact blueList_lt h
      · exact hJd.occ.bounded i h
  have hmemLv : ∀ j, j ∈ Lv ↔ j ∈ Iv ∨ j ∈ Rv := by
    intro j
    rw [hLv, List.mem_filter, List.mem_range, decide_eq_true_eq, hSv, Finset.mem_union,
      List.mem_toFinset, List.mem_toFinset]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rcases h with h | h
      · exact hId.occ.bounded j h
      · exact redList_lt h
  -- the readings agree
  have hread : readAt u Lu = readAt v Lv := by
    refine readAt_eq_of_orderIso f (List.pairwise_lt_range.filter _)
      (List.pairwise_lt_range.filter _) ?_ ?_ ?_
    · -- monotone
      intro i hi i' hi' hii'
      rcases (hmemLu i).mp hi with hB | hJ' <;> rcases (hmemLu i').mp hi' with hB' | hJ''
      · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hB
        obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hB'
        rw [fB t ht, fB t' ht']
        exact List.pairwise_iff_getElem.mp hId.occ.sorted t t' (by omega) (by omega)
          (index_lt_of_getElem_lt hBd.occ.sorted ht ht' hii')
      · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hB
        obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hJ''
        rw [fB t ht, fJ s hs]
        exact (lt_iff_lt hBd hJd hId hRd htest (by omega) (by omega)).mp hii'
      · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hJ'
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hB'
        rw [fJ s hs, fB t ht]
        exact (gt_iff_gt hBd hJd hId hRd htest (by omega) (by omega)).mp hii'
      · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hJ'
        obtain ⟨s', hs', rfl⟩ := List.getElem_of_mem hJ''
        rw [fJ s hs, fJ s' hs']
        exact List.pairwise_iff_getElem.mp hRd.occ.sorted s s' (by omega) (by omega)
          (index_lt_of_getElem_lt hJd.occ.sorted hs hs' hii')
    · -- image
      intro j
      rw [hmemLv]
      constructor
      · rintro (hI | hR)
        · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hI
          exact ⟨Bu[t]'(by omega), (hmemLu _).mpr (Or.inl (List.getElem_mem _)), fB t (by omega)⟩
        · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hR
          exact ⟨Ju[s]'(by omega), (hmemLu _).mpr (Or.inr (List.getElem_mem _)), fJ s (by omega)⟩
      · rintro ⟨i, hi, rfl⟩
        rcases (hmemLu i).mp hi with hB | hJ'
        · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hB
          rw [fB t ht]
          exact Or.inl (List.getElem_mem _)
        · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hJ'
          rw [fJ s hs]
          exact Or.inr (List.getElem_mem _)
    · -- letters
      intro i hi
      rcases (hmemLu i).mp hi with hB | hJ'
      · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hB
        rw [fB t ht, List.getD_eq_getElem _ _ (hBd.occ.getElem_lt ht),
          List.getD_eq_getElem _ _ (hId.occ.getElem_lt (by omega)),
          hBd.occ.getElem_read, hId.occ.getElem_read]
      · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hJ'
        rw [fJ s hs, List.getD_eq_getElem _ _ (hJd.occ.getElem_lt hs),
          List.getD_eq_getElem _ _ (hRd.occ.getElem_lt (by omega)),
          hJd.occ.getElem_read, hRd.occ.getElem_read]
  -- absorption on both sides
  have hu : (subAt u Su).prod = u.prod :=
    prod_subAt_eq_of_blue_subset u fun i hi hi' =>
      Finset.mem_union_left _ (List.mem_toFinset.mpr (mem_blueList.mpr ⟨hi', hi⟩))
  have hv : (subAt v Sv).prod = v.prod :=
    prod_subAt_eq_of_red_subset v fun j hj hj' =>
      Finset.mem_union_right _ (List.mem_toFinset.mpr (mem_redList.mpr ⟨hj', hj⟩))
  rw [← hu, ← hv, subAt_eq_readAt, subAt_eq_readAt]
  exact congrArg List.prod hread

end MonoidProduct
