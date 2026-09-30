import MonoidProduct.Stock.Strict
import MonoidProduct.Aperiodic.Defs

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The BTBS monoid is aperiodic and noncommutative (`ex:btbs-breadth`)

`ex:btbs-breadth` of `monoid.tex` asserts that the BTBS monoid (summaries
`(min, max, best profit)` with `⊗`, the singleton `(p, p, −∞)`, and an adjoined identity) is
noncommutative and satisfies `s² = s³` for every `s`, hence is aperiodic.

For a nonempty summary `s = (a, b, c)` one has `s * s = (a, b, max c (b − a))`, and multiplying
by `s` once more changes nothing: the new cross term is again `b − a`.  The identity is
idempotent.

* `strictStock_sq_eq_cube` / `strictStock_pow_two_eq_pow_three`: `s * s = s * s * s` and
  `s ^ 2 = s ^ 3` in `StrictStock.Summaries` (the paper's monoid, profit in `WithBot ℤ`);
* `strictStock_isAperiodicMonoid`: the `IsAperiodicMonoid` instance (stabilisation at `N = 2`);
* `strictStock_not_commutative`: `price 0 * price 1 ≠ price 1 * price 0`;

The identity holds on all summaries, not only the reachable ones.  (The same facts for the
optional-trade monoid of `Stock/Beta.lean` live in that file.)
-/

namespace MonoidProduct

/-! ## The strict (paper) monoid -/

namespace StrictStock

/-- On nonempty strict summaries, `s * s = s * s * s`. -/
lemma strictStock_ssumm_sq_eq_cube (s : SSumm) : s * s = s * s * s := by
  ext
  · simp only [mul_lo]; omega
  · simp only [mul_hi]; omega
  · simp only [mul_profit, mul_lo, min_self]
    apply le_antisymm <;> simp

/-- **`ex:btbs-breadth`**: the BTBS monoid satisfies `s² = s³`, product form. -/
theorem strictStock_sq_eq_cube (s : Summaries) : s * s = s * s * s := by
  induction s using WithOne.recOneCoe with
  | one => simp
  | coe t =>
      simp only [← WithOne.coe_mul]
      exact congrArg _ (strictStock_ssumm_sq_eq_cube t)

/-- **`ex:btbs-breadth`**: the BTBS monoid satisfies `s ^ 2 = s ^ 3`. -/
theorem strictStock_pow_two_eq_pow_three (s : Summaries) : s ^ 2 = s ^ 3 := by
  rw [sq, pow_three, ← mul_assoc]
  exact strictStock_sq_eq_cube s

/-- **`ex:btbs-breadth`**: the BTBS monoid is aperiodic. -/
instance strictStock_isAperiodicMonoid : IsAperiodicMonoid Summaries where
  stabilizes s := ⟨2, by norm_num, strictStock_pow_two_eq_pow_three s⟩

/-- **`ex:btbs-breadth`**: the BTBS monoid is noncommutative. -/
theorem strictStock_not_commutative :
    (price 0 : Summaries) * (price 1 : Summaries)
      ≠ (price 1 : Summaries) * (price 0 : Summaries) := by
  rw [← WithOne.coe_mul, ← WithOne.coe_mul, Ne, WithOne.coe_inj]
  intro h
  have := congrArg SSumm.profit h
  simp only [mul_profit, price] at this
  norm_num at this

end StrictStock

end MonoidProduct
