import MonoidProduct.Aperiodic.Defs
import Mathlib.Data.Fin.VecNotation

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.show false

/-!
# The counter states and their sequential endomorphism monoid

Setup for the Dyck transition monoid of `prop:dyck-monoid`.

`DyckState k` is the height counter of the depth-`k` Dyck automaton: the live
heights `0, …, k` plus a dead state.  `ThenEnd S` wraps `S → S` with the
**sequential** multiplication `(x * y).run s = y.run (x.run s)` — "apply `x`,
then `y`" — so that `orderedProd` of letter actions reads a word from left to
right exactly as the paper does (this is the most dangerous convention
error; the `example`s at the bottom pin it).

`upE`/`downE` are the two letter actions: stepping outside `[0, k]` is death,
and dead stays dead.  Following the parenthesis convention of `Dyck/Defs.lean`
(`parenStep false = +1`), the letter `false` is `upE` and `true` is `downE`.

The power-evaluation lemmas (`upE_pow_run_of_le` etc.) are what the
realization of a normal form by the word `d^a u^(a+b) d^(b-e)` consumes.
-/

namespace MonoidProduct

/-! ## The sequential endomorphism monoid -/

/-- An endofunction under **sequential** composition: `x * y` is "apply `x`,
then `y`". -/
structure ThenEnd (S : Type*) where
  /-- Apply the transformation. -/
  run : S → S

namespace ThenEnd

variable {S : Type*}

@[ext] lemma ext {x y : ThenEnd S} (h : ∀ s, x.run s = y.run s) : x = y := by
  cases x
  cases y
  simp only [mk.injEq]
  exact funext h

instance : Mul (ThenEnd S) := ⟨fun x y => ⟨fun s => y.run (x.run s)⟩⟩

instance : One (ThenEnd S) := ⟨⟨fun s => s⟩⟩

@[simp] lemma mul_run (x y : ThenEnd S) (s : S) :
    (x * y).run s = y.run (x.run s) := rfl

@[simp] lemma one_run (s : S) : (1 : ThenEnd S).run s = s := rfl

instance : Monoid (ThenEnd S) where
  mul_assoc x y z := ext fun s => rfl
  one_mul x := ext fun s => rfl
  mul_one x := ext fun s => rfl

/-- Powers evaluate front-first: the `n` remaining copies run after the first.
(This is `pow_succ'`, whose orientation matches sequential composition.) -/
lemma pow_succ_run (x : ThenEnd S) (n : ℕ) (s : S) :
    (x ^ (n + 1)).run s = (x ^ n).run (x.run s) := by
  rw [pow_succ']
  rfl

@[simp] lemma pow_zero_run (x : ThenEnd S) (s : S) : (x ^ 0).run s = s := by
  rw [pow_zero]
  rfl

/-- A transformation that preserves a distinguished point does so in every
power. -/
lemma pow_run_fixed {x : ThenEnd S} {s : S} (hx : x.run s = s) (j : ℕ) :
    (x ^ j).run s = s := by
  induction j with
  | zero => rw [pow_zero_run]
  | succ j ih => rw [pow_succ_run, hx, ih]

end ThenEnd

/-! ## The counter states and letter actions -/

/-- The states of the depth-`k` counter: live heights `0, …, k`, or dead. -/
abbrev DyckState (k : ℕ) := Option (Fin (k + 1))

/-- The action of an opening parenthesis: step up, die above `k`. -/
def upE (k : ℕ) : ThenEnd (DyckState k) :=
  ⟨fun s => s.bind fun h =>
    if hk : (h : ℕ) + 1 ≤ k then some ⟨(h : ℕ) + 1, by omega⟩ else none⟩

/-- The action of a closing parenthesis: step down, die below `0`. -/
def downE (k : ℕ) : ThenEnd (DyckState k) :=
  ⟨fun s => s.bind fun h =>
    if 1 ≤ (h : ℕ) then some ⟨(h : ℕ) - 1, by have := h.isLt; omega⟩
    else none⟩

/-- The letter action, following `parenStep`: `false` opens, `true` closes. -/
def letterE (k : ℕ) : Bool → ThenEnd (DyckState k)
  | false => upE k
  | true => downE k

@[simp] lemma upE_run_none (k : ℕ) : (upE k).run none = none := rfl

@[simp] lemma downE_run_none (k : ℕ) : (downE k).run none = none := rfl

lemma upE_run_some (k : ℕ) (h : Fin (k + 1)) :
    (upE k).run (some h)
      = if hk : (h : ℕ) + 1 ≤ k then some ⟨(h : ℕ) + 1, by omega⟩
        else none := rfl

lemma downE_run_some (k : ℕ) (h : Fin (k + 1)) :
    (downE k).run (some h)
      = if 1 ≤ (h : ℕ) then some ⟨(h : ℕ) - 1, by have := h.isLt; omega⟩
        else none := rfl

lemma upE_run_some_of_le {k : ℕ} {h : Fin (k + 1)} (hk : (h : ℕ) + 1 ≤ k) :
    (upE k).run (some h) = some ⟨(h : ℕ) + 1, by omega⟩ := by
  rw [upE_run_some, dif_pos hk]

lemma upE_run_some_of_gt {k : ℕ} {h : Fin (k + 1)} (hk : k < (h : ℕ) + 1) :
    (upE k).run (some h) = none := by
  rw [upE_run_some, dif_neg (by omega)]

lemma downE_run_some_of_le {k : ℕ} {h : Fin (k + 1)} (hk : 1 ≤ (h : ℕ)) :
    (downE k).run (some h)
      = some ⟨(h : ℕ) - 1, by have := h.isLt; omega⟩ := by
  rw [downE_run_some, if_pos hk]

lemma downE_run_some_of_lt {k : ℕ} {h : Fin (k + 1)} (hk : (h : ℕ) < 1) :
    (downE k).run (some h) = none := by
  rw [downE_run_some, if_neg (by omega)]

/-! ## Power evaluation -/

lemma upE_pow_run_of_le {k : ℕ} {h : Fin (k + 1)} {j : ℕ}
    (hj : (h : ℕ) + j ≤ k) :
    (upE k ^ j).run (some h) = some ⟨(h : ℕ) + j, by omega⟩ := by
  induction j generalizing h with
  | zero =>
      rw [ThenEnd.pow_zero_run]
      exact congrArg some (Fin.ext (Nat.add_zero _).symm)
  | succ j ih =>
      rw [ThenEnd.pow_succ_run, upE_run_some_of_le (by omega),
        ih (h := ⟨(h : ℕ) + 1, by omega⟩) (by show (h : ℕ) + 1 + j ≤ k; omega)]
      exact congrArg some (Fin.ext (by show (h : ℕ) + 1 + j = (h : ℕ) + (j + 1); omega))

lemma upE_pow_run_of_gt {k : ℕ} {h : Fin (k + 1)} {j : ℕ}
    (hj : k < (h : ℕ) + j) :
    (upE k ^ j).run (some h) = none := by
  induction j generalizing h with
  | zero => exact absurd h.isLt (by omega)
  | succ j ih =>
      rw [ThenEnd.pow_succ_run]
      by_cases hk : (h : ℕ) + 1 ≤ k
      · rw [upE_run_some_of_le hk]
        exact ih (h := ⟨(h : ℕ) + 1, by omega⟩) (by show k < (h : ℕ) + 1 + j; omega)
      · rw [upE_run_some_of_gt (by omega)]
        exact ThenEnd.pow_run_fixed (upE_run_none k) j

lemma downE_pow_run_of_le {k : ℕ} {h : Fin (k + 1)} {j : ℕ}
    (hj : j ≤ (h : ℕ)) :
    (downE k ^ j).run (some h)
      = some ⟨(h : ℕ) - j, by have := h.isLt; omega⟩ := by
  induction j generalizing h with
  | zero =>
      rw [ThenEnd.pow_zero_run]
      exact congrArg some (Fin.ext (Nat.sub_zero _).symm)
  | succ j ih =>
      rw [ThenEnd.pow_succ_run, downE_run_some_of_le (by omega),
        ih (h := ⟨(h : ℕ) - 1, by have := h.isLt; omega⟩)
          (by show j ≤ (h : ℕ) - 1; omega)]
      exact congrArg some (Fin.ext
        (by show (h : ℕ) - 1 - j = (h : ℕ) - (j + 1); omega))

lemma downE_pow_run_of_gt {k : ℕ} {h : Fin (k + 1)} {j : ℕ}
    (hj : (h : ℕ) < j) :
    (downE k ^ j).run (some h) = none := by
  induction j generalizing h with
  | zero => exact absurd hj (by omega)
  | succ j ih =>
      rw [ThenEnd.pow_succ_run]
      by_cases hk : 1 ≤ (h : ℕ)
      · rw [downE_run_some_of_le hk]
        exact ih (h := ⟨(h : ℕ) - 1, by have := h.isLt; omega⟩)
          (by show (h : ℕ) - 1 < j; omega)
      · rw [downE_run_some_of_lt (by omega)]
        exact ThenEnd.pow_run_fixed (downE_run_none k) j

/-! ## Orientation checks

`orderedProd ![u, d]` must mean "up, then down": from height `0` at `k = 1` it
returns to `0`, while "down, then up" would die immediately. -/

example : (orderedProd fun i => letterE 1 (![false, true] i)).run
    (some 0) = some 0 := by decide

example : (orderedProd fun i => letterE 1 (![true, false] i)).run
    (some 0) = none := by decide

example : (orderedProd fun i => letterE 1 (![false, false] i)).run
    (some 0) = none := by decide

end MonoidProduct
