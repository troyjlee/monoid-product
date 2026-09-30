import MonoidProduct.Aperiodic.CubeRoot.Green
import MonoidProduct.Aperiodic.Examples
set_option linter.style.header false

/-!
# Calibration of the Green layer on the two tiny monoids

Kept out of `Green.lean` so that the algebra module depends only on the
principal ideals and Mathlib's idempotents.

* `U₂ = {1, e₁, e₂}` with `e_i · e_j = e_j`: both right zeros are idempotent,
  hence regular, and their `J`-class is regular.
* `N₂ = {1, a, 0}` with `a² = 0`: `a` is **not** regular, since `a · x · a`
  is `0` for every `x`.  Its `J`-class is a singleton, so the class is not
  regular either — proved here directly from the singleton fact rather than
  from stability, to keep the two claims independent.
-/

namespace MonoidProduct

example : U2.e2 * U2.e2 = U2.e2 ∧ U2.e1 * U2.e1 = U2.e1 := by decide

example : IsIdempotentElem U2.e2 := by
  change U2.e2 * U2.e2 = U2.e2
  decide

example : IsVonNeumannRegular U2.e2 := ⟨U2.e2, by decide⟩

example : IsRegularClass U2.e2 := ⟨U2.e2, rfl, U2.e2, by decide⟩

/-- `a` is not regular in `N₂`. -/
theorem n2_a_not_isRegular : ¬ IsVonNeumannRegular N2.a := by
  rintro ⟨x, hx⟩
  exact absurd ⟨x, hx⟩ (by decide : ¬ ∃ x : N2, N2.a * x * N2.a = N2.a)

/-- The `J`-class of `a` in `N₂` is the singleton `{a}`. -/
theorem n2_jClass_a_singleton : ∀ b : N2, twoIdeal b = twoIdeal N2.a → b = N2.a := by
  decide

/-- Hence the class is not regular — argued from the singleton fact, not from
stability. -/
theorem n2_a_not_isRegularClass : ¬ IsRegularClass N2.a := by
  rintro ⟨b, hb, hreg⟩
  rw [n2_jClass_a_singleton b hb] at hreg
  exact n2_a_not_isRegular hreg

/-! ### Regular height at the base

`regHeight` is a well-founded recursion, so it does not reduce by `decide`;
these check the base API instead. -/

example : regHeight (1 : U2) = 0 := regHeight_one

example : regHeight U2.e2 ≠ 0 := fun h => by
  have : U2.e2 = 1 := regHeight_eq_zero_iff.1 h
  exact absurd this (by decide)

example : regHeight N2.a ≠ 0 := fun h => by
  have : N2.a = 1 := regHeight_eq_zero_iff.1 h
  exact absurd this (by decide)

end MonoidProduct
