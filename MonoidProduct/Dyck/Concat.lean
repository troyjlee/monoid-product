import MonoidProduct.Dyck.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Concatenating equal-width words (supporting layer for the block encoding)

The successor step of the block encoder is

  `B' = B₁ B₂ ⋯ B_{2m} d^{2m}`,

so it needs an `n`-fold concatenation of words of a common width `w`, together
with balance bookkeeping for it and for a run of closing parentheses.

**No `i * w + s` arithmetic appears anywhere.**  `concatW` is defined by
recursion through `wordAppend`, and every lemma is an induction on the number of
blocks:

* the two prefix bounds the block invariant needs are proved without locating `t` inside a
  block — at a split point the left part contributes its whole total balance and
  the right part is handled by the induction hypothesis;
* the block encoding's query locality needs only *existence* statements — `concatW_local`
  ("each position is one fixed block-and-offset, uniformly in the word family")
  and `concatW_locate` ("each block-and-offset is realised at some position").
  Neither names the position numerically, so neither needs `Nat` division.

Width casts, a common source of dependent-type friction, are confined to
`wcast`, whose lemmas are all `subst`-then-`rfl`.
-/

namespace MonoidProduct

/-! ## Transporting a word along an equality of widths -/

/-- Reindex a word along an equality of widths. -/
def wcast {a b : ℕ} (h : a = b) (x : Fin a → Bool) : Fin b → Bool :=
  fun i => x (Fin.cast h.symm i)

@[simp] lemma stepAt_wcast {a b : ℕ} (h : a = b) (x : Fin a → Bool) (i : ℕ) :
    stepAt (wcast h x) i = stepAt x i := by
  subst h
  rfl

@[simp] lemma prefixBalance_wcast {a b : ℕ} (h : a = b) (x : Fin a → Bool)
    (t : ℕ) : prefixBalance (wcast h x) t = prefixBalance x t := by
  subst h
  rfl

@[simp] lemma totalBalance_wcast {a b : ℕ} (h : a = b) (x : Fin a → Bool) :
    totalBalance (wcast h x) = totalBalance x := by
  subst h
  rfl

lemma wcast_apply {a b : ℕ} (h : a = b) (x : Fin a → Bool) (i : Fin b) :
    wcast h x i = x (Fin.cast h.symm i) := rfl

/-! ## Pointwise values of a concatenation of two words -/

lemma wordAppend_apply_left {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool)
    (k : Fin (a + b)) (h : (k : ℕ) < a) : wordAppend x y k = x ⟨(k : ℕ), h⟩ :=
  dif_pos h

lemma wordAppend_apply_right {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool)
    (k : Fin (a + b)) (h : ¬ (k : ℕ) < a) :
    wordAppend x y k = y ⟨(k : ℕ) - a, by omega⟩ :=
  dif_neg h

/-- Value in the left factor, addressed by an offset rather than a bound. -/
lemma wordAppend_apply_left' {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool)
    (s : Fin a) (k : Fin (a + b)) (hk : (k : ℕ) = (s : ℕ)) :
    wordAppend x y k = x s := by
  have hs := s.isLt
  rw [wordAppend_apply_left x y k (by omega)]
  congr 1
  exact Fin.ext (by omega)

/-- Value in the right factor, addressed by an offset rather than a bound. -/
lemma wordAppend_apply_right' {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool)
    (s : Fin b) (k : Fin (a + b)) (hk : (k : ℕ) = a + (s : ℕ)) :
    wordAppend x y k = y s := by
  rw [wordAppend_apply_right x y k (by omega)]
  congr 1
  exact Fin.ext (show (k : ℕ) - a = (s : ℕ) from by omega)

/-! ## A run of closing parentheses -/

/-- `r` closing parentheses. -/
def dRun (r : ℕ) : Fin r → Bool := fun _ => true

@[simp] lemma stepAt_dRun (r i : ℕ) :
    stepAt (dRun r) i = if i < r then -1 else 0 := by
  by_cases h : i < r
  · rw [if_pos h, stepAt_of_lt _ h]
    rfl
  · rw [if_neg h, stepAt_of_ge _ (by omega)]

lemma prefixBalance_dRun (r t : ℕ) :
    prefixBalance (dRun r) t = -((min t r : ℕ) : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [prefixBalance_succ, ih, stepAt_dRun]
      by_cases h : t < r
      · rw [if_pos h, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
        push_cast
        ring
      · rw [if_neg h, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
        ring

@[simp] lemma totalBalance_dRun (r : ℕ) :
    totalBalance (dRun r) = -((r : ℕ) : ℤ) := by
  rw [totalBalance, prefixBalance_dRun, Nat.min_self]

/-! ## `n`-fold concatenation -/

/-- Concatenation of `n` words of common width `w`. -/
def concatW (w : ℕ) : (n : ℕ) → (Fin n → Fin w → Bool) → Fin (n * w) → Bool
  | 0, _ => fun k => Fin.elim0 (Fin.cast (Nat.zero_mul w) k)
  | n + 1, B =>
      wcast (by ring) (wordAppend (B 0) (concatW w n fun i => B i.succ))

lemma concatW_succ (w n : ℕ) (B : Fin (n + 1) → Fin w → Bool) :
    concatW w (n + 1) B
      = wcast (by ring) (wordAppend (B 0) (concatW w n fun i => B i.succ)) :=
  rfl

/-- The successor of a concatenation, addressed through the width cast. -/
lemma concatW_succ_apply (w n : ℕ) (B : Fin (n + 1) → Fin w → Bool)
    (p : Fin (w + n * w)) :
    concatW w (n + 1) B (Fin.cast (by ring) p)
      = wordAppend (B 0) (concatW w n fun i => B i.succ) p := rfl

lemma prefixBalance_concatW_zero (w : ℕ) (B : Fin 0 → Fin w → Bool) (t : ℕ) :
    prefixBalance (concatW w 0 B) t = 0 :=
  Finset.sum_eq_zero fun i _ => stepAt_of_ge _ (by omega)

@[simp] lemma totalBalance_concatW (w : ℕ) :
    ∀ (n : ℕ) (B : Fin n → Fin w → Bool),
      totalBalance (concatW w n B) = ∑ i, totalBalance (B i)
  | 0, B => by
      rw [totalBalance, prefixBalance_concatW_zero]
      simp
  | n + 1, B => by
      rw [concatW_succ, totalBalance_wcast, totalBalance_wordAppend,
        totalBalance_concatW w n, Fin.sum_univ_succ]

/-- **The two prefix bounds needed by the block invariant.**  No position is ever located
inside a particular block. -/
lemma prefixBalance_concatW_bounds (w : ℕ) {h : ℤ} (hh : 0 ≤ h) :
    ∀ (n : ℕ) (B : Fin n → Fin w → Bool),
      (∀ i t, 0 ≤ prefixBalance (B i) t) →
      (∀ i t, prefixBalance (B i) t ≤ h) →
      ∀ t, 0 ≤ prefixBalance (concatW w n B) t ∧
        prefixBalance (concatW w n B) t ≤ (∑ i, totalBalance (B i)) + h
  | 0, B, _, _, t => by
      rw [prefixBalance_concatW_zero]
      refine ⟨le_refl 0, ?_⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
      exact hh
  | n + 1, B, hnn, hle, t => by
      have htb0 : 0 ≤ totalBalance (B 0) := hnn 0 w
      have hrest := prefixBalance_concatW_bounds w hh n (fun i => B i.succ)
        (fun i => hnn i.succ) (fun i => hle i.succ)
      have hsum : (∑ i, totalBalance (B i))
          = totalBalance (B 0) + ∑ i : Fin n, totalBalance (B i.succ) :=
        Fin.sum_univ_succ _
      have hrestnn : 0 ≤ ∑ i : Fin n, totalBalance (B i.succ) :=
        Finset.sum_nonneg fun i _ => hnn i.succ w
      rw [concatW_succ, prefixBalance_wcast]
      rcases Nat.lt_or_ge t w with ht | ht
      · rw [prefixBalance_wordAppend_left _ _ (le_of_lt ht)]
        refine ⟨hnn 0 t, ?_⟩
        rw [hsum]
        have := hle 0 t
        linarith
      · obtain ⟨s, rfl⟩ : ∃ s, t = w + s := ⟨t - w, by omega⟩
        rw [prefixBalance_wordAppend_right]
        obtain ⟨h1, h2⟩ := hrest s
        rw [hsum]
        constructor
        · linarith
        · linarith

lemma prefixBalance_concatW_nonneg (w n : ℕ) {h : ℤ} (hh : 0 ≤ h)
    (B : Fin n → Fin w → Bool)
    (hnn : ∀ i t, 0 ≤ prefixBalance (B i) t)
    (hle : ∀ i t, prefixBalance (B i) t ≤ h) (t : ℕ) :
    0 ≤ prefixBalance (concatW w n B) t :=
  (prefixBalance_concatW_bounds w hh n B hnn hle t).1

lemma prefixBalance_concatW_le (w n : ℕ) {h : ℤ} (hh : 0 ≤ h)
    (B : Fin n → Fin w → Bool)
    (hnn : ∀ i t, 0 ≤ prefixBalance (B i) t)
    (hle : ∀ i t, prefixBalance (B i) t ≤ h) (t : ℕ) :
    prefixBalance (concatW w n B) t ≤ (∑ i, totalBalance (B i)) + h :=
  (prefixBalance_concatW_bounds w hh n B hnn hle t).2

/-! ## Query locality

Both statements are existential: they say *that* a position corresponds to a
block-and-offset, never *which* number it is. -/

/-- Every position of a concatenation is one fixed block-and-offset, uniformly
in the family of words. -/
lemma concatW_local {w : ℕ} :
    ∀ (n : ℕ) (k : Fin (n * w)),
      ∃ (i : Fin n) (s : Fin w),
        ∀ B : Fin n → Fin w → Bool, concatW w n B k = B i s
  | 0, k => absurd k.isLt (by omega)
  | n + 1, k => by
      obtain ⟨p, rfl⟩ : ∃ p : Fin (w + n * w), k = Fin.cast (by ring) p :=
        ⟨Fin.cast (by ring) k, Fin.ext (by simp)⟩
      by_cases hlt : (p : ℕ) < w
      · exact ⟨0, ⟨(p : ℕ), hlt⟩, fun B => by
          rw [concatW_succ_apply]
          exact wordAppend_apply_left' _ _ _ _ rfl⟩
      · obtain ⟨i, s, hs⟩ := concatW_local (w := w) n
          ⟨(p : ℕ) - w, by have := p.isLt; omega⟩
        refine ⟨i.succ, s, fun B => ?_⟩
        rw [concatW_succ_apply,
          wordAppend_apply_right' _ _ ⟨(p : ℕ) - w, by have := p.isLt; omega⟩ p
            (by simp; omega)]
        exact hs (fun j => B j.succ)

/-- Every block-and-offset is realised at some position. -/
lemma concatW_locate {w : ℕ} :
    ∀ (n : ℕ) (i : Fin n) (s : Fin w),
      ∃ k : Fin (n * w), ∀ B : Fin n → Fin w → Bool, concatW w n B k = B i s
  | 0, i, _ => absurd i.isLt (by omega)
  | n + 1, i, s => by
      refine Fin.cases (motive := fun i =>
        ∃ k : Fin ((n + 1) * w),
          ∀ B : Fin (n + 1) → Fin w → Bool, concatW w (n + 1) B k = B i s)
        ?_ ?_ i
      · refine ⟨Fin.cast (by ring)
          (⟨(s : ℕ), by have := s.isLt; omega⟩ : Fin (w + n * w)), fun B => ?_⟩
        rw [concatW_succ_apply]
        exact wordAppend_apply_left' _ _ s _ rfl
      · intro j
        obtain ⟨k, hk⟩ := concatW_locate (w := w) n j s
        refine ⟨Fin.cast (by ring)
          (⟨w + (k : ℕ), by have := k.isLt; omega⟩ : Fin (w + n * w)),
          fun B => ?_⟩
        rw [concatW_succ_apply, wordAppend_apply_right' _ _ k _ rfl]
        exact hk (fun j => B j.succ)

end MonoidProduct
