import MonoidProduct.Quantum.Applications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance test: Simon's theorem and the 𝓙-trivial bound

The statement pin for Simon's theorem (forward direction) and the
unconditional 𝓙-trivial product bound.  Like the other acceptance files, this
file exists to be broken: any change to a pinned statement fails the build.

Pinned:

1. **Simon's theorem, forward direction** — every finite 𝓙-trivial monoid
   divides some `UT_k(𝔹)`, `k ≥ 1`, in the exact interface
   `SemigroupDivides M S := ∃ T : Subsemigroup S, ∃ φ : T →ₙ* M,
   Function.Surjective φ`.
2. **The least degree** — `τ(M) ≥ 1`, `M ≺ UT_{τ(M)}(𝔹)`, and minimality.
3. **The unconditional 𝓙-trivial theorem, in the paper's shape** —
   `Q_{1/3}(Prod_{M,n}) ≤ min{n, 147456·√(n·min{n, C(τ(M),2)})}` (zero at
   `τ(M) = 1`); the additive `2·8192(1 + 8√(…))` form is kept as the raw
   compiler bound.
4. **The kernel** — words with the same subwords of length `≤ 2|M| − 2`
   have the same product.

Not gated on the reverse direction or on the piecewise-testable-language
theorem.

    #print axioms MonoidProduct.exists_divides_but_of_isJTrivial
      → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
open QuantumQueryComplexity
namespace AcceptanceF

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## 1. Simon's theorem, forward direction -/

theorem simon_forward_pinned (hJ : IsJTrivialMonoid M) :
    ∃ k, 1 ≤ k ∧ SemigroupDivides M (BUT k) :=
  exists_divides_but_of_isJTrivial hJ

/-! ## 2. The least degree -/

theorem tau_pinned (hJ : IsJTrivialMonoid M) :
    1 ≤ tau M hJ ∧ SemigroupDivides M (BUT (tau M hJ))
      ∧ ∀ k, 1 ≤ k → SemigroupDivides M (BUT k) → tau M hJ ≤ k :=
  ⟨one_le_tau hJ, semigroupDivides_but_tau hJ, fun _ hk h => tau_le hJ hk h⟩

/-! ## 3. The unconditional 𝓙-trivial theorem -/

/-- The paper-shaped endpoint, pinned. -/
theorem jtrivial_pinned {n : ℕ} (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
        (147456 * Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))) :=
  jtrivial_qQuery_le_min hJ hn

/-- The raw compiler bound, pinned. -/
theorem jtrivial_raw_pinned {n : ℕ} (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ 2 * (uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ)))) :=
  jtrivial_qQuery_le hJ hn

/-! ## 4. The kernel -/

theorem kernel_pinned (hJ : IsJTrivialMonoid M) (u v : List M)
    (hsub : ∀ p : List M, p.length ≤ 2 * Fintype.card M - 2 →
      (List.Sublist p u ↔ List.Sublist p v)) :
    u.prod = v.prod :=
  prod_eq_of_sublist_iff hJ u v hsub

end AcceptanceF
end MonoidProduct
