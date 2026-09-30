import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation

set_option linter.style.header false

/-!
# Depth-bounded Dyck recognition

A word over `Bool` is read as a
parenthesis string — `false` opens, `true` closes — and `IsDyck k x` says its
running balance stays in `[0, k]` and returns to `0`.

Two conventions, both chosen to keep later proofs free of coercion noise:

* the prefix length is a plain `ℕ`, with positions past the end contributing
  `0` (`stepAt`), exactly as `padAt` does for interval products in
  `MonoidProduct/Aperiodic/Defs.lean`.  Raw `Fin` casts
  swamp the prefix arithmetic, and this is the same fix that worked there;
* `IsDyck` quantifies over `Finset.range (n+1)` so that it is decidable
  without instance gymnastics, and `isDyck_iff` recovers the unbounded reading.

The **odd-length fact** is proved here rather than left to prose: at odd `n` no
word is balanced, so exact-length Dyck recognition is constant and its adversary
bound is `0`.  A literal "for every `n`" statement
of the Dyck lower bound (the paper's `thm:dyck-lb`) is false without this, so it is worth having as a standing guard.
-/

namespace MonoidProduct

/-! ## Balance -/

/-- `false` opens a parenthesis, `true` closes one. -/
def parenStep : Bool → ℤ
  | false => 1
  | true => -1

@[simp] lemma parenStep_false : parenStep false = 1 := rfl
@[simp] lemma parenStep_true : parenStep true = -1 := rfl

lemma parenStep_eq_one_or (b : Bool) : parenStep b = 1 ∨ parenStep b = -1 := by
  cases b <;> simp

/-- The contribution of position `i`, or `0` past the end of the word. -/
def stepAt {n : ℕ} (x : Fin n → Bool) (i : ℕ) : ℤ :=
  if h : i < n then parenStep (x ⟨i, h⟩) else 0

@[simp] lemma stepAt_of_lt {n : ℕ} (x : Fin n → Bool) {i : ℕ} (h : i < n) :
    stepAt x i = parenStep (x ⟨i, h⟩) := dif_pos h

@[simp] lemma stepAt_of_ge {n : ℕ} (x : Fin n → Bool) {i : ℕ} (h : n ≤ i) :
    stepAt x i = 0 := dif_neg (by omega)

/-- The balance of the first `t` symbols. -/
def prefixBalance {n : ℕ} (x : Fin n → Bool) (t : ℕ) : ℤ :=
  ∑ i ∈ Finset.range t, stepAt x i

/-- The balance of the whole word. -/
def totalBalance {n : ℕ} (x : Fin n → Bool) : ℤ := prefixBalance x n

@[simp] lemma prefixBalance_zero {n : ℕ} (x : Fin n → Bool) :
    prefixBalance x 0 = 0 := by simp [prefixBalance]

lemma prefixBalance_succ {n : ℕ} (x : Fin n → Bool) (t : ℕ) :
    prefixBalance x (t + 1) = prefixBalance x t + stepAt x t := by
  simp [prefixBalance, Finset.sum_range_succ]

/-- Past the end of the word the balance no longer moves. -/
lemma prefixBalance_of_ge {n : ℕ} (x : Fin n → Bool) {t : ℕ} (h : n ≤ t) :
    prefixBalance x t = totalBalance x := by
  obtain ⟨d, rfl⟩ : ∃ d, t = n + d := ⟨t - n, by omega⟩
  clear h
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [show n + (d + 1) = n + d + 1 from rfl, prefixBalance_succ,
        stepAt_of_ge x (by omega), add_zero, ih]

lemma prefixBalance_step_le {n : ℕ} (x : Fin n → Bool) (t : ℕ) :
    prefixBalance x (t + 1) ≤ prefixBalance x t + 1 := by
  rw [prefixBalance_succ]
  rcases Nat.lt_or_ge t n with h | h
  · rcases parenStep_eq_one_or (x ⟨t, h⟩) with hs | hs <;>
      rw [stepAt_of_lt x h, hs] <;> linarith
  · rw [stepAt_of_ge x h]; linarith

/-! ## The predicate -/

/-- `x` is a Dyck word of depth at most `k`. -/
def IsDyck (k : ℕ) {n : ℕ} (x : Fin n → Bool) : Prop :=
  totalBalance x = 0 ∧ ∀ t ∈ Finset.range (n + 1),
    0 ≤ prefixBalance x t ∧ prefixBalance x t ≤ (k : ℤ)

instance {k n : ℕ} (x : Fin n → Bool) : Decidable (IsDyck k x) := by
  unfold IsDyck; infer_instance

/-- The unbounded reading: past the end the balance is the total, so the two
agree. -/
lemma isDyck_iff {k n : ℕ} (x : Fin n → Bool) :
    IsDyck k x ↔ totalBalance x = 0 ∧
      ∀ t : ℕ, 0 ≤ prefixBalance x t ∧ prefixBalance x t ≤ (k : ℤ) := by
  constructor
  · rintro ⟨htot, hb⟩
    refine ⟨htot, fun t => ?_⟩
    rcases Nat.lt_or_ge t (n + 1) with h | h
    · exact hb t (Finset.mem_range.2 h)
    · rw [prefixBalance_of_ge x (by omega), htot]
      exact ⟨le_refl 0, Int.natCast_nonneg k⟩
  · rintro ⟨htot, hb⟩
    exact ⟨htot, fun t _ => hb t⟩

/-- The `Bool`-valued wrapper the adversary bound consumes. -/
def dyck (k n : ℕ) : (Fin n → Bool) → Bool := fun x => decide (IsDyck k x)

@[simp] lemma dyck_eq_true {k n : ℕ} {x : Fin n → Bool} :
    dyck k n x = true ↔ IsDyck k x := by simp [dyck]

/-- Deeper words are still accepted at a larger depth bound. -/
lemma IsDyck.mono {k k' n : ℕ} (hkk : k ≤ k') {x : Fin n → Bool}
    (h : IsDyck k x) : IsDyck k' x := by
  refine ⟨h.1, fun t ht => ⟨(h.2 t ht).1, le_trans (h.2 t ht).2 ?_⟩⟩
  exact_mod_cast hkk

/-! ## Parity: odd-length exact Dyck is constant

This is why the headline theorems must be stated at even
length. -/

lemma even_prefixBalance_sub {n : ℕ} (x : Fin n → Bool) {t : ℕ} (ht : t ≤ n) :
    Even (prefixBalance x t - (t : ℤ)) := by
  induction t with
  | zero => simpa using even_zero
  | succ t ih =>
      obtain ⟨j, hj⟩ := ih (by omega)
      rw [prefixBalance_succ, stepAt_of_lt x (by omega)]
      rcases parenStep_eq_one_or (x ⟨t, by omega⟩) with hs | hs <;> rw [hs]
      · exact ⟨j, by push_cast; linarith⟩
      · exact ⟨j - 1, by push_cast; linarith⟩

/-- **No word of odd length is balanced.** -/
theorem not_isDyck_of_odd {k n : ℕ} (hn : ¬ Even n) (x : Fin n → Bool) :
    ¬ IsDyck k x := by
  rintro ⟨htot, -⟩
  obtain ⟨j, hj⟩ := even_prefixBalance_sub x (le_refl n)
  rw [← totalBalance, htot] at hj
  exact hn ⟨(-j).toNat, by omega⟩

/-- Exact-length Dyck recognition is the constant `false` at odd length, so its
adversary bound is `0`. -/
theorem dyck_eq_false_of_odd {k n : ℕ} (hn : ¬ Even n) (x : Fin n → Bool) :
    dyck k n x = false := by
  simp only [dyck, decide_eq_false_iff_not]
  exact not_isDyck_of_odd hn x

/-! ## Concatenation

A single `wordAppend` with its indexing lemmas proved once — the
recursive block encoder must never be proved by repeated casts
between raw natural indices. -/

/-- Concatenation of two words. -/
def wordAppend {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    Fin (a + b) → Bool :=
  fun i => if h : (i : ℕ) < a then x ⟨i, h⟩ else y ⟨(i : ℕ) - a, by omega⟩

@[simp] lemma stepAt_wordAppend {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool)
    (i : ℕ) : stepAt (wordAppend x y) i
      = if i < a then stepAt x i else stepAt y (i - a) := by
  by_cases hi : i < a
  · rw [if_pos hi, stepAt_of_lt _ (by omega), stepAt_of_lt x hi]
    simp [wordAppend, hi]
  · rw [if_neg hi]
    by_cases hb : i < a + b
    · rw [stepAt_of_lt _ hb, stepAt_of_lt y (by omega)]
      simp [wordAppend, hi]
    · rw [stepAt_of_ge _ (by omega), stepAt_of_ge y (by omega)]

lemma prefixBalance_wordAppend_left {a b : ℕ} (x : Fin a → Bool)
    (y : Fin b → Bool) {t : ℕ} (ht : t ≤ a) :
    prefixBalance (wordAppend x y) t = prefixBalance x t := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [stepAt_wordAppend, if_pos (by omega)]

lemma prefixBalance_wordAppend_right {a b : ℕ} (x : Fin a → Bool)
    (y : Fin b → Bool) (s : ℕ) :
    prefixBalance (wordAppend x y) (a + s)
      = totalBalance x + prefixBalance y s := by
  rw [prefixBalance, Finset.sum_range_add, ← prefixBalance,
    prefixBalance_wordAppend_left x y (le_refl a), ← totalBalance]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [stepAt_wordAppend, if_neg (by omega)]
  congr 1
  omega

@[simp] lemma totalBalance_wordAppend {a b : ℕ} (x : Fin a → Bool)
    (y : Fin b → Bool) :
    totalBalance (wordAppend x y) = totalBalance x + totalBalance y :=
  prefixBalance_wordAppend_right x y b

/-- **Dyck words of the same depth concatenate.** -/
theorem IsDyck.append {k a b : ℕ} {x : Fin a → Bool} {y : Fin b → Bool}
    (hx : IsDyck k x) (hy : IsDyck k y) : IsDyck k (wordAppend x y) := by
  rw [isDyck_iff] at hx hy ⊢
  refine ⟨by rw [totalBalance_wordAppend, hx.1, hy.1, add_zero], fun t => ?_⟩
  rcases Nat.lt_or_ge t a with h | h
  · rw [prefixBalance_wordAppend_left x y (le_of_lt h)]
    exact hx.2 t
  · obtain ⟨s, rfl⟩ : ∃ s, t = a + s := ⟨t - a, by omega⟩
    rw [prefixBalance_wordAppend_right, hx.1, zero_add]
    exact hy.2 s

/-! ### Balanced padding -/

/-- The two-symbol word `ud`. -/
def ud : Fin 2 → Bool := fun i => decide ((i : ℕ) = 1)

lemma stepAt_ud_zero : stepAt ud 0 = 1 := by
  rw [stepAt_of_lt ud (by norm_num : (0 : ℕ) < 2)]
  rfl

lemma stepAt_ud_one : stepAt ud 1 = -1 := by
  rw [stepAt_of_lt ud (by norm_num : (1 : ℕ) < 2)]
  rfl

lemma prefixBalance_ud_one : prefixBalance ud 1 = 1 := by
  have h : prefixBalance ud 1 = prefixBalance ud 0 + stepAt ud 0 :=
    prefixBalance_succ ud 0
  rw [h, prefixBalance_zero, zero_add, stepAt_ud_zero]

@[simp] lemma totalBalance_ud : totalBalance ud = 0 := by
  have h : prefixBalance ud 2 = prefixBalance ud 1 + stepAt ud 1 :=
    prefixBalance_succ ud 1
  rw [totalBalance, h, prefixBalance_ud_one, stepAt_ud_one]
  ring

lemma isDyck_ud {k : ℕ} (hk : 1 ≤ k) : IsDyck k ud := by
  rw [isDyck_iff]
  refine ⟨totalBalance_ud, fun t => ?_⟩
  match t with
  | 0 => simpa using Int.natCast_nonneg k
  | 1 =>
      rw [prefixBalance_ud_one]
      exact ⟨by norm_num, by exact_mod_cast hk⟩
  | (s + 2) =>
      rw [prefixBalance_of_ge ud (by omega), totalBalance_ud]
      exact ⟨le_refl 0, Int.natCast_nonneg k⟩

/-- Appending `ud` preserves acceptance, which is how an even-length statement
is obtained from the exact block lengths of the reduction. -/
theorem IsDyck.appendUd {k n : ℕ} (hk : 1 ≤ k) {x : Fin n → Bool}
    (h : IsDyck k x) : IsDyck k (wordAppend x ud) :=
  h.append (isDyck_ud hk)


/-! ## Exit criterion: agreement with a stack counter

The definition is checked by exhaustive agreement with a direct simulation.
The reference below is written independently of the balance arithmetic: it
carries a height, fails on underflow or on exceeding the depth, and accepts when
the final height is `0`. -/

/-- One step of a direct stack simulation; `none` is failure. -/
def stackStep (k : ℕ) : Option ℕ → Bool → Option ℕ
  | none, _ => none
  | some h, true => if h = 0 then none else some (h - 1)
  | some h, false => if h = k then none else some (h + 1)

/-- A direct stack simulation, independent of `prefixBalance`. -/
def stackAccept (k : ℕ) {n : ℕ} (x : Fin n → Bool) : Bool :=
  ((List.ofFn x).foldl (stackStep k) (some 0)) == some 0

section Checks

example : ∀ x : Fin 0 → Bool, dyck 2 0 x = stackAccept 2 x := by decide
example : ∀ x : Fin 1 → Bool, dyck 2 1 x = stackAccept 2 x := by decide
example : ∀ x : Fin 2 → Bool, dyck 1 2 x = stackAccept 1 x := by decide
example : ∀ x : Fin 3 → Bool, dyck 2 3 x = stackAccept 2 x := by decide
example : ∀ x : Fin 4 → Bool, dyck 1 4 x = stackAccept 1 x := by decide
example : ∀ x : Fin 4 → Bool, dyck 2 4 x = stackAccept 2 x := by decide
example : ∀ x : Fin 4 → Bool, dyck 3 4 x = stackAccept 3 x := by decide
example : ∀ x : Fin 5 → Bool, dyck 2 5 x = stackAccept 2 x := by decide
example : ∀ x : Fin 6 → Bool, dyck 2 6 x = stackAccept 2 x := by decide
example : ∀ x : Fin 6 → Bool, dyck 3 6 x = stackAccept 3 x := by decide

/-- The depth bound really bites: `uuudd d` is Dyck at depth `3` but not at
depth `2`. -/
example : dyck 3 6 ![false, false, false, true, true, true] = true := by decide
example : dyck 2 6 ![false, false, false, true, true, true] = false := by decide

/-- Odd lengths are constant. -/
example : ∀ x : Fin 5 → Bool, dyck 3 5 x = false := by decide

end Checks

end MonoidProduct
