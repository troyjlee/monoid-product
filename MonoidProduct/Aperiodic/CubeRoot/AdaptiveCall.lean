import MonoidProduct.Aperiodic.CubeRoot.StrictParent
import QuantumQueryComplexity.Adaptive
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The adaptive killed-axis call, and the prepend integration

The regular-action compiler (`lem:ags-action-compiler`) makes **adaptive
calls**: it computes a descriptor — which
state the action has reached, where the first death occurred — and then runs
a sub-test *whose identity depends on that descriptor value*.  Only the
branch actually taken may be paid for; a tool that pays `∑_d c_d` over all
branches is fatal inside the recursion.

The question is whether `HasDualOn.descriptorCompose`
expresses the calls needed here directly, or whether a separate tree-shaped
adapter is needed.  **It expresses them directly**, once the identity-promise
bridge is available in both directions.  Both halves are generic, so they
live upstream: `HasDual.of_hasDualOn_id` beside its converse in
`Promise/HasDual.lean`, and `HasDual.adaptiveCall` /
`adaptiveCall_const` / `adaptiveTranscript` in `Adaptive.lean`.

What remains here is the AGS-specific integration — an **integration test**
for the localized AGS step of `StrictParent.lean`.  The global AGS solution
supplies `StrictParentIH` over the
*augmented* alphabet `Option σ` at horizon `n + 1`, which is what the
virtual-prepend adapter of `StrictParent.lean` consumes; the two then compose
into the adaptive killed-axis call `x ↦ (D x, [D x · φ(x) = m])`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Integration

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **The AGS solution supplies the localized induction hypothesis**, with the
exponent dropped by one: every strict two-sided parent of `m` has `J`-level
`< jLevel m`, so its own `agsStep ^ (jLevel s + 1)` is at most
`agsStep ^ jLevel m`.  That drop is exactly what localizing buys — the
recursion is only ever asked about strict parents. -/
theorem strictParentIH_of_ags (letter : σ → M) (N : ℕ) (m : M) :
    StrictParentIH letter m N (agsStep N M ^ jLevel m) := by
  intro s hs ℓ hℓ
  refine (hasDual_eqProd' letter N s hℓ).mono ?_
  have hstep1 : (1 : ℝ) ≤ agsStep N M := one_le_agsStep N M
  have hlt : jLevel s < jLevel m := jLevel_lt_of_ssubset hs
  have hpow : agsStep N M ^ (jLevel s + 1) ≤ agsStep N M ^ jLevel m :=
    pow_le_pow_right₀ hstep1 (by omega)
  exact mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)

/-- **The integration test**: the contract the virtual prepend
consumes is satisfiable — at the augmented alphabet `Option σ` and at the
shifted horizon `n + 1`. -/
theorem strictParentIH_prependLetter (letter : σ → M) (a m : M) (n : ℕ) :
    StrictParentIH (prependLetter letter a) m (n + 1)
      (agsStep (n + 1) M ^ jLevel m) :=
  strictParentIH_of_ags (prependLetter letter a) (n + 1) m

/-- **End to end**: the fixed-left-context test, priced with no hypotheses at
all beyond `m ≠ 1`.  The context is prepended as a known coordinate, the
localized step runs over the augmented alphabet at horizon `n + 1`, and the
dual comes back to the original alphabet at length `n`. -/
theorem hasDual_eqProdLeft_ags (letter : σ → M) (a : M) {m : M} (hm : m ≠ 1)
    (n : ℕ) :
    HasDual (fun x : Fin n → σ => eqProdLeft letter a m x)
      (16 * stepBound (n + 1) M (agsStep (n + 1) M ^ jLevel m)) :=
  hasDual_eqProdLeft_of_strictParentIH letter a hm
    (pow_nonneg (le_trans zero_le_one (one_le_agsStep (n + 1) M)) _)
    (strictParentIH_prependLetter letter a m n)

/-- **The adaptive killed-axis call**: run the fixed-context test *for the
state the descriptor reports*.  This is the shape the action compiler
calls, priced additively — the descriptor once, one context test, and no
factor in the number of states. -/
theorem hasDual_adaptive_eqProdLeft (letter : σ → M) {n : ℕ}
    (D : (Fin n → σ) → M) {m : M} (hm : m ≠ 1) {g : ℝ} (hD : HasDual D g) :
    HasDual (fun x => (D x, eqProdLeft letter (D x) m x))
      (g + 16 * stepBound (n + 1) M (agsStep (n + 1) M ^ jLevel m)) :=
  HasDual.adaptiveCall hD fun a => hasDual_eqProdLeft_ags letter a hm n

end Integration

end MonoidProduct
