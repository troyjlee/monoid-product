import MonoidProduct.Simon.Chain
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The unitriangular division degree `τ(M)`

For a finite 𝓙-trivial monoid `M`, `monoid.tex` defines
`τ(M) = min {k ≥ 1 : M ≺ UT_k(𝔹)}`; Simon's theorem
(`exists_divides_but_of_isJTrivial`) says the minimum exists.  `tau` is
that least degree, packaged with its two defining facts.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

open Classical in
/-- **The unitriangular division degree**: the least `k ≥ 1` with
`M ≺ UT_k(𝔹)`. -/
noncomputable def tau (M : Type) [Monoid M] [Fintype M] [DecidableEq M]
    (hJ : IsJTrivialMonoid M) : ℕ :=
  Nat.find (exists_divides_but_of_isJTrivial hJ)

open Classical in
lemma tau_spec (hJ : IsJTrivialMonoid M) :
    1 ≤ tau M hJ ∧ SemigroupDivides M (BUT (tau M hJ)) :=
  Nat.find_spec (exists_divides_but_of_isJTrivial hJ)

lemma one_le_tau (hJ : IsJTrivialMonoid M) : 1 ≤ tau M hJ := (tau_spec hJ).1

/-- **Simon's theorem at the least degree**: `M ≺ UT_{τ(M)}(𝔹)`. -/
theorem semigroupDivides_but_tau (hJ : IsJTrivialMonoid M) :
    SemigroupDivides M (BUT (tau M hJ)) := (tau_spec hJ).2

open Classical in
/-- `τ(M)` is least: any positive degree admitting a division dominates it. -/
lemma tau_le (hJ : IsJTrivialMonoid M) {k : ℕ} (hk : 1 ≤ k)
    (h : SemigroupDivides M (BUT k)) : tau M hJ ≤ k :=
  Nat.find_min' (exists_divides_but_of_isJTrivial hJ) ⟨hk, h⟩

end MonoidProduct
