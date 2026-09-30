import MonoidProduct.Aperiodic.Decomposition
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Pi

set_option linter.style.header false

/-!
# Two tiny aperiodic monoids, and the decomposition checked by brute force

The decomposition theorem (the paper's `thm:decomp`) is proved in `MonoidProduct/Aperiodic/Decomposition.lean`, so evaluating
it is no test of the *mathematics*.  What the checks below test is that the
four conditions, as formalised, are the ones the paper means: that each of
`(U)`, `(V)`, `(C)`, `(W)` actually has content, and that the half-open index
conventions line up.  A misplaced `+1` would show up here as a condition that is
vacuously true, or as an independence witness that fails to exist.

* `U₂` — the identity together with two right zeros.  Non-commutative; the
  ordered product of a word is its last non-identity letter.  Here `(C)` and
  `(W)` are vacuous and `(U)`, `(V)` carry everything.
* `N₂` — the identity, a nilpotent `a` with `a² = 0`, and an absorbing `0`.
  Commutative; here all four conditions bite.
-/

namespace MonoidProduct

/-! ## `U₂`: an identity and two right zeros -/

/-- The three-element monoid `{1, e₁, e₂}` with `e_i · e_j = e_j`. -/
inductive U2 | one | e1 | e2
  deriving DecidableEq, Repr

instance : Fintype U2 :=
  ⟨{U2.one, U2.e1, U2.e2}, fun x => by cases x <;> decide⟩

namespace U2

instance : Mul U2 := ⟨fun a b => match b with | .one => a | b => b⟩
instance : One U2 := ⟨.one⟩

instance : Monoid U2 where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide

instance : IsAperiodicMonoid U2 where
  stabilizes a := ⟨1, Nat.one_pos, by revert a; decide⟩

end U2

/-! ## `N₂`: a nilpotent of index two -/

/-- The three-element monoid `{1, a, 0}` with `a² = 0`. -/
inductive N2 | one | a | zero
  deriving DecidableEq, Repr

instance : Fintype N2 :=
  ⟨{N2.one, N2.a, N2.zero}, fun x => by cases x <;> decide⟩

namespace N2

instance : Mul N2 := ⟨fun p q => match p, q with
  | .one, q => q
  | p, .one => p
  | .a, .a => .zero
  | _, _ => .zero⟩
instance : One N2 := ⟨.one⟩

instance : Monoid N2 where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide

instance : CommMonoid N2 where
  mul_comm := by decide

instance : IsAperiodicMonoid N2 where
  stabilizes p := ⟨2, by norm_num, by revert p; decide⟩

end N2

/-! ## `C₂`: a non-example -/

/-- The two-element *group*.  Aperiodicity is a real hypothesis, and this is
what it excludes. -/
inductive C2 | one | g
  deriving DecidableEq, Repr

instance : Fintype C2 :=
  ⟨{C2.one, C2.g}, fun x => by cases x <;> decide⟩

namespace C2

instance : Mul C2 := ⟨fun p q => match p, q with
  | .one, q => q
  | p, .one => p
  | .g, .g => .one⟩
instance : One C2 := ⟨.one⟩

instance : Monoid C2 where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide

end C2

/-! ## Sanity checks

Everything below is settled by kernel evaluation. -/

section Checks

/-- The two monoids really are what they claim to be. -/
example : ∀ p q : U2, p * q = if q = 1 then p else q := by decide

/-! ### A fixed left context does not present strict parents

`CubeRoot/StrictParent.lean` keeps `hasDual_eqProdLeft_of_strictFibre` only as
an auxiliary result, because its premise — every `v` with `a · v = m` is a
strict two-sided parent of `m` — already fails at a nonidentity idempotent,
which is exactly the apex representative a killed axis runs at.  `e₂` is one:
`e₂ · e₂ = e₂`, so `v = m = a = e₂` sits in the fibre with equal, not strictly
larger, two-sided ideal.  (The manuscript prepends the context as a known
coordinate instead; that is `hasDual_eqProdLeft_of_prepend`.) -/
example : U2.e2 * U2.e2 = U2.e2 ∧ U2.e2 ≠ 1 := by decide

example : ¬ ∀ v : U2, U2.e2 * v = U2.e2 → twoIdeal U2.e2 ⊂ twoIdeal v := by decide
example : N2.a * N2.a = N2.zero := by decide
example : ∀ p : N2, N2.zero * p = N2.zero := by decide

/-- `U₂` is not commutative, so the decomposition is being exercised on a
genuinely non-commutative example. -/
example : ¬ ∀ p q : U2, p * q = q * p := by decide

/-- Aperiodicity is a real hypothesis: `C₂` is a finite monoid that fails it.
The generator's powers alternate, so no `N` can stabilise them — take the two
exponents `2N` and `2N+1`, both past `N`. -/
example : ¬ ∀ p : C2, ∃ N, 0 < N ∧ p ^ N = p ^ (N + 1) := by
  intro h
  obtain ⟨N, -, hp⟩ := h C2.g
  have hsq : C2.g ^ 2 = 1 := by decide
  -- multiplying `g ^ N = g ^ (N+1)` by `g ^ (N+1)` lands on adjacent parities
  have hadd : C2.g ^ N * C2.g ^ (N + 1) = C2.g ^ (2 * N + 1) := by
    rw [← pow_add, show N + (N + 1) = 2 * N + 1 from by ring]
  have hadd2 : C2.g ^ (N + 1) * C2.g ^ (N + 1) = C2.g ^ (2 * N + 2) := by
    rw [← pow_add, show N + 1 + (N + 1) = 2 * N + 2 from by ring]
  have key : C2.g ^ (2 * N + 1) = C2.g ^ (2 * N + 2) := by
    rw [← hadd, ← hadd2, hp]
  rw [show C2.g ^ (2 * N + 1) = C2.g from by
        rw [pow_succ, pow_mul, hsq, one_pow, one_mul],
    show C2.g ^ (2 * N + 2) = 1 from by
        rw [show 2 * N + 2 = 2 * (N + 1) from by ring, pow_mul, hsq, one_pow]] at key
  exact absurd key (by decide)

/-! ### The decomposition itself -/

/-- The decomposition theorem (`thm:decomp`) on `U₂`, for every target and every word of length three. -/
example : ∀ (m : U2) (x : Fin 3 → U2), m ≠ 1 →
    (orderedProd x = m ↔
      UEvent m x ∧ VEvent m x ∧ ¬ badLetter m x ∧ ¬ badInfix m x) := by
  decide

/-- The decomposition theorem (`thm:decomp`) on `N₂`, for every target and every word of length three. -/
example : ∀ (m : N2) (x : Fin 3 → N2), m ≠ 1 →
    (orderedProd x = m ↔
      UEvent m x ∧ VEvent m x ∧ ¬ badLetter m x ∧ ¬ badInfix m x) := by
  decide

/-! ### The index sets are not degenerate -/

/-- On `U₂` the last two conditions are vacuous: the product of a word is its
last non-identity letter, which no local test can rule out. -/
example : setC U2.e2 = ∅ ∧ setG U2.e2 = ∅ := by decide

/-- On `N₂`, by contrast, all four index sets are inhabited for the target
`a`. -/
example : (setE N2.a).Nonempty ∧ (setF N2.a).Nonempty ∧
    (setC N2.a).Nonempty ∧ (setG N2.a).Nonempty := by decide

/-- The letter `0` is forbidden, and two `a`s cannot both occur — the two
non-trivial local tests for the target `a`. -/
example : setC N2.a = {N2.zero} := by decide
example : (N2.a, 1, N2.a) ∈ setG N2.a := by decide

/-! ### `(C)` and `(W)` are each needed

There is a length-three word over `N₂` satisfying the other three conditions
whose ordered product is nevertheless not `a`.  Since `thm:decomp` is an iff, that
is exactly the statement that the dropped condition is not implied by the rest;
the witnesses are `x = (0,1,1)` and `x = (a,1,a)`. -/

example : ∃ x : Fin 3 → N2, orderedProd x ≠ N2.a ∧
    UEvent N2.a x ∧ VEvent N2.a x ∧ ¬ badInfix N2.a x := by decide

example : ∃ x : Fin 3 → N2, orderedProd x ≠ N2.a ∧
    UEvent N2.a x ∧ VEvent N2.a x ∧ ¬ badLetter N2.a x := by decide

/-- `(U)` and `(V)`, on the other hand, are *not* independent here: on `N₂` each
follows from the other three.  That is a fact about `N₂`, not about the theorem —
`N₂` is commutative, and once `(C)` and `(W)` hold the word has at most one
non-identity letter, so "the first one is `a`" and "the last one is `a`" say the
same thing.  The same collapse happens on `U₂`, where `(C)` and `(W)` are
vacuous and `(V)` alone already implies `(U)`. -/
example : ∀ x : Fin 3 → N2, ¬ badLetter N2.a x → ¬ badInfix N2.a x →
    (UEvent N2.a x ↔ VEvent N2.a x) := by decide

example : ∀ x : Fin 3 → U2, VEvent U2.e2 x → UEvent U2.e2 x := by decide

/-! ### Ideal ascent has content

The recursion of the AGS bound (Section `sec:ags-local` of the paper) needs `MmM ⊊ MrM` for the `r` of each index set;
on `N₂` with target `a` these are genuine strict inclusions, not equalities. -/

example : ∀ p : N2 × N2, p ∈ setE N2.a → twoIdeal N2.a ⊂ twoIdeal p.1 := by
  decide

example : ∀ p : N2 × N2, p ∈ setF N2.a → twoIdeal N2.a ⊂ twoIdeal p.2 := by
  decide

example : ∀ p : N2 × N2 × N2, p ∈ setG N2.a →
    twoIdeal N2.a ⊂ twoIdeal p.2.1 := by
  decide

/-- And the ascent is strict in the level, so the recursion terminates.  `jLevel`
is defined by well-founded recursion and does not reduce in the kernel, so this
one goes through the lemma rather than by `decide`. -/
example : ∀ p : N2 × N2 × N2, p ∈ setG N2.a → jLevel p.2.1 < jLevel N2.a :=
  fun _ hp => jLevel_lt_of_mem_setG hp

end Checks

end MonoidProduct
