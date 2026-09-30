import MonoidProduct.Simon.Defs
import MonoidProduct.Width.Product
set_option linter.style.header false

/-!
# Commutative aperiodic monoids are 𝓙-trivial

`monoid.tex` Proposition `prop:comm-jtrivial`.  In a commutative monoid the
three Green relations coincide; if `a` and `b` generate the same ideal then
`a = b·u` and `b = a·v`, so `a = a·(v·u)`, and absorption
(`mul_right_absorb`, the aperiodic device of `Width/Product.lean`, in place of
the paper's Sandwich Lemma) gives `a·v = a`, i.e. `b = a`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-- **A finite commutative aperiodic monoid is 𝓙-trivial.** -/
theorem isJTrivialMonoid_of_comm {M : Type} [CommMonoid M] [Fintype M] [DecidableEq M]
    [IsAperiodicMonoid M] : IsJTrivialMonoid M := by
  intro a b hab
  have ha : a ∈ twoIdeal b := hab ▸ self_mem_twoIdeal a
  have hb : b ∈ twoIdeal a := hab.symm ▸ self_mem_twoIdeal b
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.mp ha
  obtain ⟨p', q', hpq'⟩ := mem_twoIdeal.mp hb
  have h1 : a = b * (p * q) := by
    rw [← hpq]
    ac_rfl
  have h2 : b = a * (p' * q') := by
    rw [← hpq']
    ac_rfl
  have h3 : a * ((p' * q') * (p * q)) = a := by
    rw [← mul_assoc, ← h2, ← h1]
  have h4 : a * (p' * q') = a := mul_right_absorb h3
  rw [h2, h4]

end MonoidProduct
