import MonoidProduct.Quantum.Applications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance test: Boolean unitriangular products

The statement pin for the Boolean unitriangular products.  Like the other
pins, this file exists to be broken: a refactor that changes a statement
fails here.  It sits outside the `QuantumQueryComplexity.Quantum` aggregate (it imports
`Applications`, which crosses into the tracked development); **CI must
build it explicitly**: `lake build QuantumQueryComplexity.Quantum.AcceptanceE`.

Pinned (the paper's Theorem `thm:boolean-unitriangular` and Corollary
`cor:jtrivial-division`, the latter conditional on a supplied witness):

1. **The adversary sandwich** — `√(n·min{n,⌊k²/4⌋}/2) ≤
   ADV±(Prod_{UT_k(𝔹),n}) ≤ 8√(n·min{n, C(k,2)})` for `k ≥ 2`, `n ≥ 1`.
2. **The operational sandwich** — `1/36·√(n·min{n,⌊k²/4⌋}/2) ≤
   Q_{1/3}(Prod_{UT_k(𝔹),n}) ≤ min{n, 8192(1 + 8√(n·min{n, C(k,2)}))}`,
   i.e. `Θ(min{n, k√n})`, in the native model.
3. **The `k = 1` endpoint** — zero queries at every nonnegative error.
4. **The conditional division theorem** — `M ≺ UT_k(𝔹)` (subsemigroup,
   hom, section) gives `Q_{1/3}(Prod_{M,n}) ≤ 2·8192(1 + 8√(n·min{n,
   C(k,2)}))`.  No 𝓙-triviality is assumed here; the
   𝓙-trivial case goes through Simon's theorem (`Applications.lean`).

    #print axioms MonoidProduct.ut_qQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
open QuantumQueryComplexity
namespace AcceptanceE

/-! ## 1. The adversary sandwich -/

theorem adversary_sandwich_pinned {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ)
        ≤ advPM (fun w : Fin n → BUT k => wordProd id w)
      ∧ advPM (fun w : Fin n → BUT k => wordProd id w)
        ≤ 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)) :=
  advPM_wordProd_but_sandwich hk hn

/-! ## 2. The operational sandwich -/

theorem operational_sandwich_pinned {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    (1 / 36 : ℝ) * Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ)
        ≤ (qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
      ∧ (qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
        ≤ min (n : ℝ) (uniformExtractionConstant
            * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)))) :=
  ut_qQuery_sandwich hk hn

/-! ## 3. The `k = 1` endpoint -/

theorem dim_one_pinned (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun w : Fin n → BUT 1 => wordProd id w) ε = 0 :=
  ut_qQuery_eq_zero_dim_one n hε

/-! ## 4. The conditional division theorem -/

theorem but_division_pinned {k n : ℕ} {M : Type} [Monoid M] [Fintype M]
    [DecidableEq M] (hn : 1 ≤ n) (T : Subsemigroup (BUT k)) (φ : T →ₙ* M)
    (ψ : M → T) (hsec : ∀ m, φ (ψ m) = m) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ 2 * (uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)))) :=
  qQuery_le_of_but_division hn T φ ψ hsec

end AcceptanceE
end MonoidProduct
