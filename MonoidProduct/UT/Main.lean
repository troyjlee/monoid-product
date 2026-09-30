import MonoidProduct.UT.Upper
import MonoidProduct.UT.Lower
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `UT_k(𝔹)` products: the `ADV±` sandwich

`monoid.tex` Theorem `thm:boolean-unitriangular` at the adversary level:

    √(n·min{n, ⌊k²/4⌋}/2)  ≤  ADV±(Prod_{UT_k(𝔹),n})  ≤  8√(n·min{n, C(k,2)}),

both sides `Θ(min{n, k√n})` for `k ≥ 2`.  The upper bound is the
bounded-change scan on the monotone prefix products, the lower bound the
cross-edge disjoint search; the operational (quantum) forms live in
`Quantum/Applications.lean`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {k n : ℕ}

/-- **The `UT_k(𝔹)` product's adversary bound**: `8√(n·min{n, C(k,2)})`. -/
theorem advPM_wordProd_but_le :
    advPM (fun w : Fin n → BUT k => wordProd id w)
      ≤ 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)) :=
  advPM_le_of_hasDual (by positivity) (hasDual_wordProd_but (id : BUT k → BUT k))

/-- **Theorem `thm:boolean-unitriangular`, at the `ADV±` level**: for
`k ≥ 2` and `n ≥ 1`, with `d = min{n, ⌊k²/4⌋}`,
`√(nd/2) ≤ ADV±(Prod_{UT_k(𝔹),n}) ≤ 8√(n·min{n, C(k,2)})`. -/
theorem advPM_wordProd_but_sandwich (hk : 2 ≤ k) (hn : 0 < n) :
    Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ)
        ≤ advPM (fun w : Fin n → BUT k => wordProd id w)
      ∧ advPM (fun w : Fin n → BUT k => wordProd id w)
        ≤ 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)) :=
  ⟨ut_lower_advPM hk hn rfl, advPM_wordProd_but_le⟩

/-- **`UT_1(𝔹)` is trivial**: the product is constant and its adversary
bound is `0` — the `k = 1` case the sandwich excludes by `2 ≤ k`. -/
theorem advPM_wordProd_but_eq_zero_dim_one (n : ℕ) :
    advPM (fun w : Fin n → BUT 1 => wordProd id w) = 0 :=
  advPM_eq_zero_of_forall_eq fun _ _ => Subsingleton.elim _ _

end MonoidProduct
