import MonoidProduct.Quantum.OrderedVerified
import MonoidProduct.Quantum.StrictStockApplications
import MonoidProduct.Quantum.OrderedLogAcceptance

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Acceptance test: certified outputs and the strict stock instance

Statement pins for certified core algorithms and the strict stock instance.  Like the library's other pins, this file
exists to be broken: a refactor that changes a statement fails here.

1. **Certified core algorithms** (`thm:ordered-beta-product`, `thm:ordered-beta-log-product`,
   algorithmic form with all-branch truthfulness): with the constants `2^27` (exponent
   `5b/2`) and `2^17` (paper's form) quantified first, for every `b` and `n` an algorithm
   with at most `min {n, bound} + b` queries whose **every** output of positive probability
   is a truthful record of at most `b` original positions, and which returns a product-
   preserving record with probability at least `9/10`.  The `+ b` is the exact verification
   overhead; the product constants are unchanged.
2. **The strict stock instance** (`prop:stock-beta`): breadth `4` and a stable order for the
   strict summary monoid (singleton profit `⊥`, no clipping at zero); the monoid readout is
   `max_{i<j}(x_j − x_i)`; `O(√n·log¹⁰(n+2))` queries for the strict profit; and the
   kernel-checked examples `(5,2) ↦ −3`, `(2,2) ↦ 0`, `(2,5) ↦ 3`, singleton `↦ ⊥`, and the
   sharpness witness `(10,2,5,0)`.

Axioms:

    #print axioms MonoidProduct.ordered_exists_verified_core_alg_quasipoly → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.StrictStock.strictProfit_qQuery_le           → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
namespace FollowupAcceptance

open QuantumQueryComplexity

/-! ## 1. Certified core algorithms -/

open Classical in
/-- **Exponent `5b/2`, constant `2^27`, every output certified.** -/
theorem acceptance_verified_core_five_halves :
    ∃ C : ℝ, C = OrderedAcceptance.orderedConstant ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → ∀ b : ℕ, IsBreadthBound letter b → ∀ n : ℕ,
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
          (B : QAlg (Fin n) σ (Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)) W) (Q : ℕ),
          (Q : ℝ) ≤ min (n : ℝ) ((C * b) ^ b * Real.sqrt n
              * orderedLogFactor (Nat.clog 2 (n + 1)) ^ b) + b
          ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)),
              0 < B.prob x Q K →
                K.Truthful (pad x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
          ∧ ∀ x : Fin n → σ,
              9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K :=
  ⟨OrderedAcceptance.orderedConstant, rfl,
    fun letter hst _b hb n => ordered_exists_verified_core_alg_five_halves letter hst hb n⟩

open Classical in
/-- **The paper's form, constant `2^17`, every output certified.** -/
theorem acceptance_verified_core_quasipoly :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → ∀ b : ℕ, IsBreadthBound letter b → ∀ n : ℕ,
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
          (B : QAlg (Fin n) σ (Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)) W) (Q : ℕ),
          (Q : ℝ) ≤ min (n : ℝ) (Real.sqrt ((n : ℝ) + 1)
              * (C * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ (C * Real.log ((b : ℝ) + 2))) + b
          ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)),
              0 < B.prob x Q K →
                K.Truthful (pad x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
          ∧ ∀ x : Fin n → σ,
              9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K :=
  ⟨quasipolyConstant, OrderedLogAcceptance.four_le_quasipolyConstant,
    fun letter hst _b hb n => ordered_exists_verified_core_alg_quasipoly letter hst hb n⟩

/-- The certification is a genuine algorithm in the model: the wrapper `QAlg.postQuery` with
`b` slots, whose outcome law is the pushforward of the raw law (pinned). -/
theorem acceptance_postQuery_law {ι σ O O' W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] [Fintype W] [DecidableEq W] [Fintype O] [DecidableEq O] [DecidableEq O']
    {k : ℕ} (A : QAlg ι σ O W) (sel : O → Fin k → Option ι) (Q : ℕ)
    (dec : O → (Fin k → Option σ) → O') (a : ι → σ) (o' : O') :
    (A.postQuery sel Q dec).prob a (Q + k) o'
      = ∑ o ∈ Finset.univ.filter (fun o => dec o (fun m => Option.map a (sel o m)) = o'),
          A.prob a Q o :=
  postQuery_prob_eq_sum A sel Q dec a o'

/-! ## 2. The strict stock instance -/

/-- **`prop:stock-beta`, the strict core**: `β ≤ 4` for every price map. -/
theorem acceptance_strict_breadth {σ : Type} (pr : σ → ℤ) :
    IsBreadthBound (StrictStock.letter pr) 4 :=
  StrictStock.isBreadthBound_strict pr

/-- **`prop:stock-beta`, the order**: stable with least identity. -/
theorem acceptance_strict_stable : IsStableOrder StrictStock.Summaries :=
  StrictStock.isStableOrder_summaries

/-- **The readout is the strict stock problem** `max_{i<j}(x_j − x_i)` (`⊥` if no pair). -/
theorem acceptance_strict_semantics {σ : Type} (pr : σ → ℤ) {n : ℕ} (x : Fin n → σ) :
    StrictStock.profitOf (wordProd (StrictStock.letter pr) x) = StrictStock.strictProfit pr x :=
  StrictStock.profitOf_wordProd_eq_strictProfit pr x

/-- **`O(√n·log¹⁰(n+2))` for the strict profit**, error `1/3`. -/
theorem acceptance_strict_profit {σ : Type} [Fintype σ] [DecidableEq σ] (pr : σ → ℤ) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => StrictStock.strictProfit pr x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 29 : ℝ) ^ 4 * Real.sqrt n * (Nat.clog 2 (n + 1) : ℝ) ^ 10) :=
  StrictStock.strictProfit_qQuery_third_le pr n

/-- The singleton has profit `⊥`, not `0`. -/
theorem acceptance_strict_singleton : StrictStock.strictProfit (id : ℤ → ℤ) ![7] = ⊥ := by
  rw [← StrictStock.profitOf_wordProd_eq_strictProfit]; decide

/-- `(5, 2)`: strict profit `−3`. -/
theorem acceptance_strict_falling :
    StrictStock.strictProfit (id : ℤ → ℤ) ![5, 2] = ((-3 : ℤ) : WithBot ℤ) := by
  rw [← StrictStock.profitOf_wordProd_eq_strictProfit]; decide

/-- `(2, 2)`: strict profit `0`. -/
theorem acceptance_strict_flat :
    StrictStock.strictProfit (id : ℤ → ℤ) ![2, 2] = ((0 : ℤ) : WithBot ℤ) := by
  rw [← StrictStock.profitOf_wordProd_eq_strictProfit]; decide

/-- `(2, 5)`: strict profit `3`. -/
theorem acceptance_strict_rising :
    StrictStock.strictProfit (id : ℤ → ℤ) ![2, 5] = ((3 : ℤ) : WithBot ℤ) := by
  rw [← StrictStock.profitOf_wordProd_eq_strictProfit]; decide

/-- **Sharpness**: the complete summary of `(10, 2, 5, 0)` needs all four positions. -/
theorem acceptance_strict_sharp : ∀ u : Finset (Fin 4), u.card ≤ 3 →
    subwordProd (StrictStock.letter (id : ℤ → ℤ)) ![10, 2, 5, 0] u
      ≠ wordProd (StrictStock.letter id) ![10, 2, 5, 0] := by
  decide

end FollowupAcceptance
end MonoidProduct
