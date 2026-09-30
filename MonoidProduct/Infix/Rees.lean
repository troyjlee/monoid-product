import MonoidProduct.Aperiodic.CubeRoot.ReesBlock
import MonoidProduct.Aperiodic.EqProd
import Mathlib.Algebra.Group.WithOne.Defs

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Words over a Rees zero-matrix monoid `R(P)¹`

`Rees1 P = WithOne (ReesZero P)`: the Rees zero-matrix semigroup over the
trivial group with sandwich `P : Λ → I → Bool`, with an adjoined identity.

A word is **bad** (`Bad P w t`, on its prefix of length `t`) when it has an
explicit zero, or two cells `(i, l)`, `(i', m)` with only identities between
them and `P l i' = false`.  `prefix_spec` is the normal form of a prefix
product: it is zero exactly when the prefix is bad; otherwise it is `1` when
every letter is the identity, and the cell `(row of the first non-identity
letter, column of the last)` otherwise.
-/

namespace MonoidProduct.Infix

open Finset

variable {I Λ : Type} [Fintype I] [DecidableEq I] [Fintype Λ] [DecidableEq Λ]

/-- The cells-or-zero as an option. -/
def ReesZero.equivOpt (P : Λ → I → Bool) : ReesZero P ≃ Option (I × Λ) where
  toFun := ReesZero.toOpt
  invFun := ReesZero.mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

instance (P : Λ → I → Bool) : Fintype (ReesZero P) :=
  Fintype.ofEquiv _ (ReesZero.equivOpt P).symm

instance (P : Λ → I → Bool) : DecidableEq (ReesZero P) :=
  (ReesZero.equivOpt P).injective.decidableEq

/-- **`R(P)¹`**: the Rees zero-matrix monoid with an adjoined identity. -/
abbrev Rees1 (P : Λ → I → Bool) := WithOne (ReesZero P)

instance (P : Λ → I → Bool) : Fintype (Rees1 P) := inferInstanceAs (Fintype (Option (ReesZero P)))
instance (P : Λ → I → Bool) : DecidableEq (Rees1 P) :=
  inferInstanceAs (DecidableEq (Option (ReesZero P)))

variable (P : Λ → I → Bool)

/-- Every element is the identity, the zero, or a cell. -/
lemma Rees1.cases (a : Rees1 P) :
    a = 1 ∨ a = ↑(ReesZero.zero P) ∨ ∃ i l, a = ↑(ReesZero.cell P i l) := by
  rcases a with _ | ⟨_ | ⟨i, l⟩⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨i, l, rfl⟩)

lemma Rees1.cell_ne_zero (i : I) (l : Λ) :
    (↑(ReesZero.cell P i l) : Rees1 P) ≠ ↑(ReesZero.zero P) := by
  intro h
  have := WithOne.coe_inj.1 h
  simp [ReesZero.cell, ReesZero.zero] at this

lemma Rees1.cell_inj {i i' : I} {l l' : Λ}
    (h : (↑(ReesZero.cell P i l) : Rees1 P) = ↑(ReesZero.cell P i' l')) : i = i' ∧ l = l' := by
  have := WithOne.coe_inj.1 h
  simp only [ReesZero.cell, ReesZero.mk.injEq, Option.some.injEq, Prod.mk.injEq] at this
  exact this

lemma Rees1.mul_zero (a : Rees1 P) : a * ↑(ReesZero.zero P) = ↑(ReesZero.zero P) := by
  rcases Rees1.cases P a with h | h | ⟨i, l, h⟩ <;> subst h
  · exact one_mul _
  · rw [← WithOne.coe_mul]; rfl
  · rw [← WithOne.coe_mul]; rfl

lemma Rees1.zero_mul (a : Rees1 P) : (↑(ReesZero.zero P) : Rees1 P) * a = ↑(ReesZero.zero P) := by
  rcases Rees1.cases P a with h | h | ⟨i, l, h⟩ <;> subst h
  · exact mul_one _
  · rw [← WithOne.coe_mul]; rfl
  · rw [← WithOne.coe_mul]; rfl

lemma Rees1.cell_mul_cell (i : I) (l : Λ) (j : I) (m : Λ) :
    (↑(ReesZero.cell P i l) : Rees1 P) * ↑(ReesZero.cell P j m)
      = if P l j then ↑(ReesZero.cell P i m) else ↑(ReesZero.zero P) := by
  rw [← WithOne.coe_mul, ReesZero.cell_mul_cell]
  split_ifs <;> rfl

/-! ## Bad words -/

variable {P}

/-- A prefix of length `t` is bad: an explicit zero, or a forbidden transition
between two cells with only identities between them. -/
def Bad {n : ℕ} (w : Fin n → Rees1 P) (t : ℕ) : Prop :=
  (∃ s, s < t ∧ padAt w s = ↑(ReesZero.zero P)) ∨
  ∃ s s', s < s' ∧ s' < t ∧ (∀ q, s < q → q < s' → padAt w q = 1) ∧
    ∃ i l i' m, padAt w s = ↑(ReesZero.cell P i l) ∧ padAt w s' = ↑(ReesZero.cell P i' m)
      ∧ P l i' = false

lemma Bad.mono {n : ℕ} {w : Fin n → Rees1 P} {t t' : ℕ} (h : Bad w t) (htt : t ≤ t') :
    Bad w t' := by
  rcases h with ⟨s, hs, h⟩ | ⟨s, s', h1, h2, h3, h4⟩
  · exact Or.inl ⟨s, by omega, h⟩
  · exact Or.inr ⟨s, s', h1, by omega, h3, h4⟩

/-- The normal form of a non-bad prefix. -/
def NormalForm {n : ℕ} (w : Fin n → Rees1 P) (t : ℕ) : Prop :=
  ((∀ s, s < t → padAt w s = 1) ∧ rangeProd w 0 t = 1) ∨
  ∃ s₁ s₂ i l i' m, s₁ ≤ s₂ ∧ s₂ < t ∧ (∀ q, q < s₁ → padAt w q = 1)
    ∧ (∀ q, s₂ < q → q < t → padAt w q = 1)
    ∧ padAt w s₁ = ↑(ReesZero.cell P i l) ∧ padAt w s₂ = ↑(ReesZero.cell P i' m)
    ∧ rangeProd w 0 t = ↑(ReesZero.cell P i m)

/-- **The prefix-product invariant.** -/
theorem prefix_spec {n : ℕ} (w : Fin n → Rees1 P) (t : ℕ) :
    (rangeProd w 0 t = ↑(ReesZero.zero P) ↔ Bad w t) ∧ (¬ Bad w t → NormalForm w t) := by
  induction t with
  | zero =>
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun _ => Or.inl ⟨fun s hs => absurd hs (by omega), ?_⟩⟩
      · rw [rangeProd_self] at h; exact absurd h.symm (WithOne.coe_ne_one)
      · rcases h with ⟨s, hs, -⟩ | ⟨s, s', -, hs', -⟩ <;> omega
      · exact rangeProd_self _ _
  | succ t ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rw [rangeProd_succ_right _ (Nat.zero_le t)]
      rcases Rees1.cases P (padAt w t) with ha | ha | ⟨i', m', ha⟩
      · -- an identity letter
        rw [ha, mul_one]
        have hiff : Bad w (t + 1) ↔ Bad w t := by
          constructor
          · rintro (⟨s, hs, h⟩ | ⟨s, s', h1, h2, h3, i, l, i'', m, h4, h5, h6⟩)
            · refine Or.inl ⟨s, ?_, h⟩
              rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hs) with h' | h'
              · exact h'
              · subst h'; rw [ha] at h; exact absurd h.symm (WithOne.coe_ne_one)
            · refine Or.inr ⟨s, s', h1, ?_, h3, i, l, i'', m, h4, h5, h6⟩
              rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 h2) with h' | h'
              · exact h'
              · subst h'; rw [ha] at h5; exact absurd h5.symm (WithOne.coe_ne_one)
          · exact fun h => h.mono (Nat.le_succ t)
        refine ⟨ih1.trans hiff.symm, fun hb => ?_⟩
        rcases ih2 (fun h => hb (hiff.2 h)) with ⟨h1, h2⟩
          | ⟨s₁, s₂, i, l, i'', m, h1, h2, h3, h4, h5, h6, h7⟩
        · refine Or.inl ⟨fun s hs => ?_,
            by rw [rangeProd_succ_right _ (Nat.zero_le t), h2, ha, mul_one]⟩
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hs) with h' | h'
          · exact h1 s h'
          · subst h'; exact ha
        · refine Or.inr ⟨s₁, s₂, i, l, i'', m, h1, by omega, h3, fun q hq1 hq2 => ?_, h5, h6,
            by rw [rangeProd_succ_right _ (Nat.zero_le t), h7, ha, mul_one]⟩
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hq2) with h' | h'
          · exact h4 q hq1 h'
          · subst h'; exact ha
      · -- an explicit zero
        rw [ha, Rees1.mul_zero]
        have hb : Bad w (t + 1) := Or.inl ⟨t, Nat.lt_succ_self t, ha⟩
        exact ⟨⟨fun _ => hb, fun _ => rfl⟩, fun h => absurd hb h⟩
      · -- a cell
        rw [ha]
        by_cases hbt : Bad w t
        · rw [ih1.2 hbt, Rees1.zero_mul]
          exact ⟨⟨fun _ => hbt.mono (Nat.le_succ t), fun _ => rfl⟩,
            fun h => absurd (hbt.mono (Nat.le_succ t)) h⟩
        · rcases ih2 hbt with ⟨h1, h2⟩ | ⟨s₁, s₂, i, l, i'', m, h1, h2, h3, h4, h5, h6, h7⟩
          · -- all identities so far
            rw [h2, one_mul]
            have hnb : ¬ Bad w (t + 1) := by
              rintro (⟨s, hs, h⟩ | ⟨s, s', hs1, hs2, -, i, l, -, -, h4, -, -⟩)
              · rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hs) with h' | h'
                · rw [h1 s h'] at h; exact absurd h WithOne.one_ne_coe
                · subst h'; rw [ha] at h; exact Rees1.cell_ne_zero P _ _ h
              · rw [h1 s (by omega)] at h4; exact absurd h4 WithOne.one_ne_coe
            refine ⟨⟨fun h => absurd h (Rees1.cell_ne_zero P _ _), fun h => absurd h hnb⟩,
              fun _ => ?_⟩
            exact Or.inr ⟨t, t, i', m', i', m', le_rfl, Nat.lt_succ_self t, h1,
              fun q hq1 hq2 => absurd hq1 (by omega), ha, ha,
              by rw [rangeProd_succ_right _ (Nat.zero_le t), h2, ha, one_mul]⟩
          · -- a cell product so far
            rw [h7, Rees1.cell_mul_cell]
            by_cases hP : P m i' = true
            · rw [if_pos hP]
              have hnb : ¬ Bad w (t + 1) := by
                rintro (⟨s, hs, h⟩ | ⟨s, s', hs1, hs2, hmid, j, l', j', m'', h4', h5', h6'⟩)
                · rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hs) with h' | h'
                  · exact hbt (Or.inl ⟨s, h', h⟩)
                  · subst h'; rw [ha] at h; exact Rees1.cell_ne_zero P _ _ h
                · rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hs2) with h' | h'
                  · exact hbt (Or.inr ⟨s, s', hs1, h', hmid, j, l', j', m'', h4', h5', h6'⟩)
                  · subst h'
                    -- the left cell must be the last one, at `s₂`
                    have hss : s = s₂ := by
                      rcases lt_trichotomy s s₂ with hlt | heq | hgt
                      · have := hmid s₂ hlt h2
                        rw [h6] at this; exact absurd this WithOne.coe_ne_one
                      · exact heq
                      · have := h4 s hgt hs1
                        rw [h4'] at this; exact absurd this WithOne.coe_ne_one
                    subst hss
                    rw [h6] at h4'
                    obtain ⟨-, hl⟩ := Rees1.cell_inj P h4'
                    rw [ha] at h5'
                    obtain ⟨hj, -⟩ := Rees1.cell_inj P h5'
                    rw [← hl, ← hj] at h6'
                    rw [hP] at h6'
                    exact absurd h6' (by decide)
              refine ⟨⟨fun h => absurd h (Rees1.cell_ne_zero P _ _), fun h => absurd h hnb⟩,
                fun _ => ?_⟩
              exact Or.inr ⟨s₁, t, i, l, i', m', by omega, Nat.lt_succ_self t, h3,
                fun q hq1 hq2 => absurd hq1 (by omega), h5, ha,
                by rw [rangeProd_succ_right _ (Nat.zero_le t), h7, ha, Rees1.cell_mul_cell,
                  if_pos hP]⟩
            · rw [if_neg hP]
              have hb : Bad w (t + 1) := Or.inr ⟨s₂, t, h2, Nat.lt_succ_self t, h4, i'', m, i', m',
                h6, ha, by simpa using hP⟩
              exact ⟨⟨fun _ => hb, fun _ => rfl⟩, fun h => absurd hb h⟩

/-- **The word product is zero exactly for bad words.** -/
theorem wordProd_eq_zero_iff {n : ℕ} (w : Fin n → Rees1 P) :
    wordProd (id : Rees1 P → Rees1 P) w = ↑(ReesZero.zero P) ↔ Bad w n := by
  have := (prefix_spec w n).1
  rw [wordProd, orderedProd_eq_rangeProd]
  exact this

end MonoidProduct.Infix
