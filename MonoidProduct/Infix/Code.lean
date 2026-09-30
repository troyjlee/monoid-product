import MonoidProduct.Infix.Rees
import MonoidProduct.Infix.Defs

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The two-letter code

`A2 = R(P_A)¹` with `P_A = [[0,1],[1,1]]`: the product `(i, l)(i', m)` is zero
exactly when `l = 0` and `i' = 0`.  The code `codeA` sends
`1 ↦ 00`, `0 ↦ 22`, `m₀₀ ↦ 20`, `m₀₁ ↦ 21`, `m₁₀ ↦ 12`, `m₁₁ ↦ 10`, and a word
is bad exactly when its coded word has a clean witness (`bad_iff_inf_flat`).

For a general sandwich `P` and a zero entry `P l₀ j₀ = false`, the letter map
`psi l₀ j₀` sends the cell `(i, l)` to `([i ≠ j₀], [l ≠ l₀])`; a word over
`R(P)¹` is bad exactly when one of its images is bad in `A2`
(`bad_iff_exists_psi`).
-/

namespace MonoidProduct.Infix

open Finset

/-- The sandwich matrix of `A₂¹`. -/
def PA : Fin 2 → Fin 2 → Bool := fun l i => !(decide (l = 0 ∧ i = 0))

/-- **`A₂¹`.** -/
abbrev A2 := Rees1 PA

lemma PA_eq_false_iff (l i : Fin 2) : PA l i = false ↔ l = 0 ∧ i = 0 := by
  simp [PA]

/-- The code of a cell. -/
def codeCell (i l : Fin 2) : Fin 2 → Fin 3 := fun b =>
  if b = 0 then (if i = 0 then 2 else 1)
  else (if i = 1 ∧ l = 0 then 2 else if i = 0 ∧ l = 1 then 1 else 0)

/-- **The two-letter code.** -/
def codeA (a : A2) : Fin 2 → Fin 3 :=
  Option.elim (α := ReesZero PA) a (fun _ => 0)
    (fun x => Option.elim x.toOpt (fun _ => 2) (fun p => codeCell p.1 p.2))

@[simp] lemma codeA_one : codeA (1 : A2) = fun _ => 0 := rfl
@[simp] lemma codeA_zero : codeA (↑(ReesZero.zero PA) : A2) = fun _ => 2 := rfl
@[simp] lemma codeA_cell (i l : Fin 2) : codeA (↑(ReesZero.cell PA i l) : A2) = codeCell i l := rfl

/-- The letters whose code has a `2` in the second position: zero and `m₁₀`. -/
lemma of_codeA_one_eq_two {a : A2} (h : codeA a 1 = 2) :
    a = ↑(ReesZero.zero PA) ∨ a = ↑(ReesZero.cell PA 1 0) := by
  rcases Rees1.cases PA a with ha | ha | ⟨i, l, ha⟩ <;> subst ha
  · simp at h
  · exact Or.inl rfl
  · fin_cases i <;> fin_cases l <;> simp [codeCell] at h ⊢

/-- The letters whose code has a `2` in the first position: zero, `m₀₀`, `m₀₁`. -/
lemma of_codeA_zero_eq_two {a : A2} (h : codeA a 0 = 2) :
    a = ↑(ReesZero.zero PA) ∨ a = ↑(ReesZero.cell PA 0 0) ∨ a = ↑(ReesZero.cell PA 0 1) := by
  rcases Rees1.cases PA a with ha | ha | ⟨i, l, ha⟩ <;> subst ha
  · simp at h
  · exact Or.inl rfl
  · fin_cases i <;> fin_cases l <;> simp [codeCell] at h ⊢

lemma eq_one_of_codeA {a : A2} (h0 : codeA a 0 = 0) (h1 : codeA a 1 = 0) : a = 1 := by
  rcases Rees1.cases PA a with ha | ha | ⟨i, l, ha⟩ <;> subst ha
  · rfl
  · simp at h0
  · fin_cases i <;> fin_cases l <;> simp [codeCell] at h0 h1

lemma eq_cell00_of_codeA {a : A2} (h0 : codeA a 0 = 2) (h1 : codeA a 1 = 0) :
    a = ↑(ReesZero.cell PA 0 0) := by
  rcases Rees1.cases PA a with ha | ha | ⟨i, l, ha⟩ <;> subst ha
  · simp at h0
  · simp at h1
  · fin_cases i <;> fin_cases l <;> simp [codeCell] at h0 h1 ⊢

lemma eq_zero_of_codeA {a : A2} (h0 : codeA a 0 = 2) (h1 : codeA a 1 = 2) :
    a = ↑(ReesZero.zero PA) := by
  rcases Rees1.cases PA a with ha | ha | ⟨i, l, ha⟩ <;> subst ha
  · simp at h0
  · rfl
  · fin_cases i <;> fin_cases l <;> simp [codeCell] at h0 h1

lemma not_codeA_zero_two {a : A2} (h0 : codeA a 0 = 0) (h1 : codeA a 1 = 2) : False := by
  rcases Rees1.cases PA a with ha | ha | ⟨i, l, ha⟩ <;> subst ha
  · simp at h1
  · simp at h0
  · fin_cases i <;> fin_cases l <;> simp [codeCell] at h0 h1

/-- The flattened coded word: position `2i + b` carries `codeA (w i) b`. -/
def flatA {n : ℕ} (w : Fin n → A2) : Fin (2 * n) → Fin 3 := fun k =>
  codeA (w ⟨k / 2, by have := k.isLt; omega⟩) ⟨k % 2, Nat.mod_lt _ (by norm_num)⟩

lemma flatA_apply {n : ℕ} (w : Fin n → A2) (i : Fin n) (b : Fin 2) :
    flatA w ⟨2 * i + b, by have := i.isLt; have := b.isLt; omega⟩ = codeA (w i) b := by
  unfold flatA
  congr 1
  · congr 1; ext; simp; omega
  · ext; simp; omega

/-- **The correspondence for `A₂¹`**: a word over `A₂¹` is bad exactly when
its coded word has a clean witness. -/
theorem bad_iff_inf_flatA {n : ℕ} (w : Fin n → A2) : Bad w n ↔ inf (2 * n) (flatA w) = true := by
  rw [inf_eq_true_iff]
  constructor
  · rintro (⟨s, hs, h⟩ | ⟨s, s', h1, h2, h3, i, l, i', m, h4, h5, h6⟩)
    · -- an explicit zero at `s`: the witness `(2s, 2s+1)`
      rw [padAt_of_lt _ hs] at h
      refine ⟨⟨2 * s, by omega⟩, ⟨2 * s + 1, by omega⟩, Fin.lt_def.2 (by simp), ?_, ?_, ?_⟩
      · have := flatA_apply w ⟨s, hs⟩ 0
        simp only [Fin.val_zero, add_zero] at this
        rw [this, h, codeA_zero]
      · have := flatA_apply w ⟨s, hs⟩ 1
        simp only [Fin.val_one] at this
        rw [this, h, codeA_zero]
      · intro q hq1 hq2
        rw [Fin.lt_def] at hq1 hq2
        simp at hq1 hq2
        omega
    · -- a forbidden pair `(s, s')`
      have hs' : s' < n := by
        by_contra hcon; rw [padAt_of_le _ (not_lt.1 hcon)] at h5; exact WithOne.one_ne_coe h5
      have hs : s < n := by omega
      rw [padAt_of_lt _ hs] at h4
      rw [padAt_of_lt _ hs'] at h5
      rw [PA_eq_false_iff] at h6
      obtain ⟨hl, hi'⟩ := h6
      subst hl hi'
      -- the right end: the first code letter of `w s'`
      have hr : flatA w ⟨2 * s', by omega⟩ = 2 := by
        have := flatA_apply w ⟨s', hs'⟩ 0
        simp only [Fin.val_zero, add_zero] at this
        rw [this, h5, codeA_cell]
        simp [codeCell]
      have hmid : ∀ q : Fin (2 * n), 2 * s + 2 ≤ (q : ℕ) → (q : ℕ) < 2 * s' → flatA w q = 0 := by
        intro q hq1 hq2
        have hq : s < q / 2 ∧ q / 2 < s' := by omega
        have := h3 (q / 2) hq.1 hq.2
        rw [padAt_of_lt _ (by omega)] at this
        unfold flatA
        rw [this, codeA_one]
      fin_cases i
      · -- `w s = m₀₀`, code `20`: the witness starts at `2s`
        refine ⟨⟨2 * s, by omega⟩, ⟨2 * s', by omega⟩, Fin.lt_def.2 (by simp; omega), ?_, hr, ?_⟩
        · have := flatA_apply w ⟨s, hs⟩ 0
          simp only [Fin.val_zero, add_zero] at this
          rw [this, h4, codeA_cell]; simp [codeCell]
        · intro q hq1 hq2
          simp only [Fin.lt_def] at hq1 hq2
          rcases Nat.lt_or_ge (q : ℕ) (2 * s + 2) with hq | hq
          · have hq' : (q : ℕ) = 2 * s + 1 := by omega
            have := flatA_apply w ⟨s, hs⟩ 1
            simp only [Fin.val_one] at this
            rw [show q = ⟨2 * s + 1, by omega⟩ from Fin.ext hq', this, h4, codeA_cell]
            simp [codeCell]
          · exact hmid q hq hq2
      · -- `w s = m₁₀`, code `12`: the witness starts at `2s + 1`
        refine ⟨⟨2 * s + 1, by omega⟩, ⟨2 * s', by omega⟩, Fin.lt_def.2 (by simp; omega), ?_, hr,
          ?_⟩
        · have := flatA_apply w ⟨s, hs⟩ 1
          simp only [Fin.val_one] at this
          rw [this, h4, codeA_cell]; simp [codeCell]
        · intro q hq1 hq2
          simp only [Fin.lt_def] at hq1 hq2
          exact hmid q (by omega) hq2
  · rintro ⟨l, r, hlr, hl, hr, hmid⟩
    -- decode the two endpoints
    set i := (l : ℕ) / 2 with hi
    set b := (l : ℕ) % 2 with hb
    set i' := (r : ℕ) / 2 with hi'
    set b' := (r : ℕ) % 2 with hb'
    have hlv : (l : ℕ) = 2 * i + b := by omega
    have hrv : (r : ℕ) = 2 * i' + b' := by omega
    have hin : i < n := by have := l.isLt; omega
    have hin' : i' < n := by have := r.isLt; omega
    have hl2 : codeA (w ⟨i, hin⟩) ⟨b, by omega⟩ = 2 := by
      have := flatA_apply w ⟨i, hin⟩ ⟨b, by omega⟩
      rw [← this, ← hl]; congr 1; ext; simp [hlv]
    have hr2 : codeA (w ⟨i', hin'⟩) ⟨b', by omega⟩ = 2 := by
      have := flatA_apply w ⟨i', hin'⟩ ⟨b', by omega⟩
      rw [← this, ← hr]; congr 1; ext; simp [hrv]
    have hmid' : ∀ q (hq : q < n) (c : Fin 2), (l : ℕ) < 2 * q + c → 2 * q + c < (r : ℕ)
        → codeA (w ⟨q, hq⟩) c = 0 := by
      intro q hq c hq1 hq2
      have := hmid ⟨2 * q + c, by have := c.isLt; omega⟩ (Fin.lt_def.2 hq1) (Fin.lt_def.2 hq2)
      rw [← flatA_apply]; exact this
    have hlr' : (l : ℕ) < r := Fin.lt_def.1 hlr
    rcases lt_trichotomy i i' with hii | hii | hii
    · -- distinct blocks
      have hids : ∀ q, i < q → q < i' → padAt w q = 1 := by
        intro q hq1 hq2
        rw [padAt_of_lt _ (by omega)]
        apply eq_one_of_codeA
        · exact hmid' q (by omega) 0 (by simp; omega) (by simp; omega)
        · exact hmid' q (by omega) 1 (by simp; omega) (by simp; omega)
      -- the right end has `b' = 0`
      have hb'0 : b' = 0 := by
        by_contra hne
        have hb'1 : b' = 1 := by omega
        have h0 : codeA (w ⟨i', hin'⟩) 0 = 0 := hmid' i' hin' 0 (by simp; omega) (by simp; omega)
        have h1 : codeA (w ⟨i', hin'⟩) 1 = 2 := by
          rw [← hr2]; congr 1; ext; simp [hb'1]
        exact not_codeA_zero_two h0 h1
      have hr2' : codeA (w ⟨i', hin'⟩) 0 = 2 := by rw [← hr2]; congr 1; ext; simp [hb'0]
      -- the left end is a column-zero letter or zero
      have hleft : w ⟨i, hin⟩ = ↑(ReesZero.zero PA) ∨ w ⟨i, hin⟩ = ↑(ReesZero.cell PA 0 0)
          ∨ w ⟨i, hin⟩ = ↑(ReesZero.cell PA 1 0) := by
        rcases Nat.eq_zero_or_pos b with hb0 | hbpos
        · have h0 : codeA (w ⟨i, hin⟩) 0 = 2 := by rw [← hl2]; congr 1; ext; simp [hb0]
          have h1 : codeA (w ⟨i, hin⟩) 1 = 0 := hmid' i hin 1 (by simp; omega) (by simp; omega)
          exact Or.inr (Or.inl (eq_cell00_of_codeA h0 h1))
        · have hb1 : b = 1 := by omega
          have h1 : codeA (w ⟨i, hin⟩) 1 = 2 := by rw [← hl2]; congr 1; ext; simp [hb1]
          rcases of_codeA_one_eq_two h1 with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      rcases of_codeA_zero_eq_two hr2' with hz' | hc'
      · exact Or.inl ⟨i', hin', by rw [padAt_of_lt _ hin']; exact hz'⟩
      rcases hleft with hz | hc
      · exact Or.inl ⟨i, hin, by rw [padAt_of_lt _ hin]; exact hz⟩
      · refine Or.inr ⟨i, i', hii, hin', hids, ?_⟩
        rcases hc with hc | hc <;> rcases hc' with hc' | hc'
        · exact ⟨0, 0, 0, 0, by rw [padAt_of_lt _ hin]; exact hc,
            by rw [padAt_of_lt _ hin']; exact hc', by decide⟩
        · exact ⟨0, 0, 0, 1, by rw [padAt_of_lt _ hin]; exact hc,
            by rw [padAt_of_lt _ hin']; exact hc', by decide⟩
        · exact ⟨1, 0, 0, 0, by rw [padAt_of_lt _ hin]; exact hc,
            by rw [padAt_of_lt _ hin']; exact hc', by decide⟩
        · exact ⟨1, 0, 0, 1, by rw [padAt_of_lt _ hin]; exact hc,
            by rw [padAt_of_lt _ hin']; exact hc', by decide⟩
    · -- the same block: it must be the zero letter
      have hb0 : b = 0 := by omega
      have hb'1 : b' = 1 := by omega
      have h0 : codeA (w ⟨i, hin⟩) 0 = 2 := by rw [← hl2]; congr 1; ext; simp [hb0]
      have h1 : codeA (w ⟨i, hin⟩) 1 = 2 := by
        rw [show (⟨i, hin⟩ : Fin n) = ⟨i', hin'⟩ from Fin.ext hii, ← hr2]
        congr 1; ext; simp [hb'1]
      exact Or.inl ⟨i, hin, by rw [padAt_of_lt _ hin]; exact eq_zero_of_codeA h0 h1⟩
    · omega

/-! ## Maps into `A₂¹` -/

variable {I Λ : Type} [Fintype I] [DecidableEq I] [Fintype Λ] [DecidableEq Λ]

/-- The letter map for the zero entry `(l₀, j₀)` of `P`. -/
def psi (P : Λ → I → Bool) (l₀ : Λ) (j₀ : I) (a : Rees1 P) : A2 :=
  Option.elim (α := ReesZero P) a 1
    (fun x => Option.elim x.toOpt (↑(ReesZero.zero PA))
      (fun p => ↑(ReesZero.cell PA (if p.1 = j₀ then 0 else 1) (if p.2 = l₀ then 0 else 1))))

variable {P : Λ → I → Bool} {l₀ : Λ} {j₀ : I}

@[simp] lemma psi_one : psi P l₀ j₀ 1 = 1 := rfl
@[simp] lemma psi_zero : psi P l₀ j₀ ↑(ReesZero.zero P) = ↑(ReesZero.zero PA) := rfl
@[simp] lemma psi_cell (i : I) (l : Λ) :
    psi P l₀ j₀ ↑(ReesZero.cell P i l)
      = ↑(ReesZero.cell PA (if i = j₀ then 0 else 1) (if l = l₀ then 0 else 1)) := rfl

lemma psi_eq_one_iff {a : Rees1 P} : psi P l₀ j₀ a = 1 ↔ a = 1 := by
  rcases Rees1.cases P a with ha | ha | ⟨i, l, ha⟩ <;> subst ha <;> simp

lemma psi_eq_zero_iff {a : Rees1 P} :
    psi P l₀ j₀ a = ↑(ReesZero.zero PA) ↔ a = ↑(ReesZero.zero P) := by
  rcases Rees1.cases P a with ha | ha | ⟨i, l, ha⟩ <;> subst ha
  · simp
  · simp
  · simp only [psi_cell]
    constructor
    · intro h; exact absurd h (Rees1.cell_ne_zero PA _ _)
    · intro h; exact absurd h (Rees1.cell_ne_zero P _ _)

lemma psi_eq_cell_iff {a : Rees1 P} {i' l' : Fin 2} :
    psi P l₀ j₀ a = ↑(ReesZero.cell PA i' l')
      ↔ ∃ i l, a = ↑(ReesZero.cell P i l) ∧ i' = (if i = j₀ then 0 else 1)
          ∧ l' = (if l = l₀ then 0 else 1) := by
  rcases Rees1.cases P a with ha | ha | ⟨i, l, ha⟩ <;> subst ha
  · simp only [psi_one]
    constructor
    · intro h; exact absurd h.symm WithOne.coe_ne_one
    · rintro ⟨i, l, h, -⟩; exact absurd h.symm WithOne.coe_ne_one
  · simp only [psi_zero]
    constructor
    · intro h; exact absurd h.symm (Rees1.cell_ne_zero PA _ _)
    · rintro ⟨i, l, h, -⟩; exact absurd h.symm (Rees1.cell_ne_zero P _ _)
  · simp only [psi_cell]
    constructor
    · intro h; obtain ⟨h1, h2⟩ := Rees1.cell_inj PA h; exact ⟨i, l, rfl, h1.symm, h2.symm⟩
    · rintro ⟨i₁, l₁, h, h1, h2⟩
      obtain ⟨e1, e2⟩ := Rees1.cell_inj P h
      subst e1 e2; rw [h1, h2]

lemma padAt_psi {n : ℕ} (w : Fin n → Rees1 P) (q : ℕ) :
    padAt (fun k => psi P l₀ j₀ (w k)) q = psi P l₀ j₀ (padAt w q) := by
  unfold padAt; split_ifs <;> simp

/-- **The correspondence for `R(P)¹`**: a word over `R(P)¹` is bad exactly when
it has an explicit zero, or its image under some zero-entry map is bad in
`A₂¹`. -/
theorem bad_iff_exists_psi {n : ℕ} (w : Fin n → Rees1 P) :
    Bad w n ↔ (∃ s, s < n ∧ padAt w s = ↑(ReesZero.zero P))
      ∨ ∃ l₀ j₀, P l₀ j₀ = false ∧ Bad (fun k => psi P l₀ j₀ (w k)) n := by
  constructor
  · rintro (⟨s, hs, h⟩ | ⟨s, s', h1, h2, h3, i, l, i', m, h4, h5, h6⟩)
    · exact Or.inl ⟨s, hs, h⟩
    · refine Or.inr ⟨l, i', h6, Or.inr ⟨s, s', h1, h2, fun q hq1 hq2 => ?_,
        if i = i' then 0 else 1, 0, 0, if m = l then 0 else 1, ?_, ?_, by decide⟩⟩
      · rw [padAt_psi, h3 q hq1 hq2, psi_one]
      · rw [padAt_psi, h4, psi_cell, if_pos rfl]
      · rw [padAt_psi, h5, psi_cell, if_pos rfl]
  · rintro (⟨s, hs, h⟩ | ⟨l₀, j₀, hP, ⟨s, hs, h⟩
      | ⟨s, s', h1, h2, h3, i₁, l₁, i₁', m₁, h4, h5, h6⟩⟩)
    · exact Or.inl ⟨s, hs, h⟩
    · rw [padAt_psi, psi_eq_zero_iff] at h
      exact Or.inl ⟨s, hs, h⟩
    · rw [padAt_psi, psi_eq_cell_iff] at h4 h5
      obtain ⟨i, l, h4, -, hl₁⟩ := h4
      obtain ⟨i', m, h5, hi₁', -⟩ := h5
      rw [PA_eq_false_iff] at h6
      obtain ⟨e1, e2⟩ := h6
      rw [e1] at hl₁; rw [e2] at hi₁'
      have hl : l = l₀ := by
        by_contra hne; rw [if_neg hne] at hl₁; exact absurd hl₁ (by decide)
      have hi' : i' = j₀ := by
        by_contra hne; rw [if_neg hne] at hi₁'; exact absurd hi₁' (by decide)
      refine Or.inr ⟨s, s', h1, h2, fun q hq1 hq2 => ?_, i, l, i', m, h4, h5, ?_⟩
      · have := h3 q hq1 hq2; rwa [padAt_psi, psi_eq_one_iff] at this
      · rw [hl, hi']; exact hP

end MonoidProduct.Infix
