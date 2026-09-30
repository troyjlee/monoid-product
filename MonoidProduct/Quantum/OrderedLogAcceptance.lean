import MonoidProduct.Quantum.OrderedLogApplications
import MonoidProduct.Quantum.OrderedAcceptance

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Acceptance: the quasipolynomial ordered product theorem

Statement pins for the paper's `thm:ordered-beta-log-product` as formalized
through the weighted transcript-tree dual, seeded rank doubling and output amplification.
Like the library's other pins, this file exists to be broken: a refactor that changes a
statement fails here.

Pinned, one theorem each:

1. **A universal constant**, the numeral `2^17`, quantified before the alphabet, the monoid,
   the order, `b` and the input length; natural logarithms and a real exponent, with `4 ≤ C`.
2. **Both error conventions**: `Q_{1/3}` and `Q_{1/10}`.
3. **The product-and-core algorithm**: for `1 ≤ b < n`, success at least `9/10` for a record
   that is a product-preserving set of at most `b` original positions, within the bound.
4. **The `breadth` specialisation.**
5. **The discrete form** `(2^15·(b+2)·L_n^4)^{⌈log₂(b+2)⌉+2}·√n` from which the paper's form
   is derived.
6. **The linear-exponent theorem is retained**: the exponent-`5b/2` pins of `OrderedAcceptance.lean` still hold.

Axioms:

    #print axioms MonoidProduct.ordered_qQuery_third_le_quasipoly  → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.ordered_exists_core_alg_quasipoly  → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
namespace OrderedLogAcceptance

open QuantumQueryComplexity

/-! ## 1. The constant -/

theorem quasipolyConstant_pinned : quasipolyConstant = (2 : ℝ) ^ 17 := rfl

theorem four_le_quasipolyConstant : 4 ≤ quasipolyConstant := by
  unfold quasipolyConstant; norm_num

/-! ## 1–2. The product bound with the constant quantified first -/

/-- **The quasipolynomial product bound**, in the form of `thm:ordered-beta-log-product`: one real
constant `C ≥ 4`, then any finite alphabet, any monoid with a stable partial order, any
breadth bound `b`, any length `n`; error `1/3`. -/
theorem acceptance_quasipoly :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → ∀ b : ℕ, IsBreadthBound letter b → ∀ n : ℕ,
        (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
          ≤ min (n : ℝ)
              (Real.sqrt ((n : ℝ) + 1)
                * (C * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ (C * Real.log ((b : ℝ) + 2))) :=
  ⟨quasipolyConstant, four_le_quasipolyConstant,
    fun letter hst _b hb n => ordered_qQuery_third_le_quasipoly letter hst hb n⟩

/-- The same bound in the error-`1/10` convention. -/
theorem acceptance_quasipoly_tenth :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → ∀ b : ℕ, IsBreadthBound letter b → ∀ n : ℕ,
        (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
          ≤ min (n : ℝ)
              (Real.sqrt ((n : ℝ) + 1)
                * (C * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ (C * Real.log ((b : ℝ) + 2))) :=
  ⟨quasipolyConstant, four_le_quasipolyConstant,
    fun letter hst _b hb n => ordered_qQuery_le_quasipoly letter hst hb n⟩

/-- The constant of the pins is the constant of the theorem. -/
theorem acceptance_constant_is_quasipolyConstant :
    ∀ b n : ℕ, quasipolyBound b n
      = Real.sqrt ((n : ℝ) + 1) * (quasipolyConstant * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2))
          ^ (quasipolyConstant * Real.log ((b : ℝ) + 2)) := fun _ _ => rfl

/-! ## 3. The product-and-core algorithm -/

open Classical in
/-- **The product-and-core algorithm**: for `1 ≤ b < n`, an algorithm within the bound whose
output is, with probability at least `9/10`, a good record: truthful for the padded word, at
most `b` original positions, and the word's product. -/
theorem acceptance_core_quasipoly :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → ∀ b : ℕ, IsBreadthBound letter b → 1 ≤ b →
        ∀ n : ℕ, b < n →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
          (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
          (Q : ℝ) ≤ Real.sqrt ((n : ℝ) + 1)
              * (C * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ (C * Real.log ((b : ℝ) + 2))
          ∧ ∀ x : Fin n → σ,
            9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K :=
  ⟨quasipolyConstant, four_le_quasipolyConstant,
    fun letter hst _b hb hb1 _n hbn => ordered_exists_core_alg_quasipoly letter hst hb hb1 hbn⟩

/-- Every good record's product is the word's product (the definition, pinned). -/
theorem acceptance_goodRec_prod {σ M : Type} [Monoid M] (letter : σ → M) (b : ℕ) {n : ℕ}
    (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)) (hK : GoodRec letter b x K) :
    K.prod (letterOpt letter) = wordProd letter x := hK.2.2

/-! ## 4. The `breadth` specialisation -/

theorem acceptance_breadth_quasipoly :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → (∃ b, IsBreadthBound letter b) → ∀ n : ℕ,
        (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
          ≤ min (n : ℝ)
              (Real.sqrt ((n : ℝ) + 1)
                * (C * ((breadth letter : ℝ) + 2) * Real.log ((n : ℝ) + 2))
                  ^ (C * Real.log ((breadth letter : ℝ) + 2))) :=
  ⟨quasipolyConstant, four_le_quasipolyConstant,
    fun letter hst hex n => ordered_qQuery_le_quasipoly_breadth letter hst hex n⟩

/-! ## 5. The discrete form -/

/-- **The discrete form**: `Q_{1/3} ≤ min { n, (2^15·(b+2)·L_n^4)^{⌈log₂(b+2)⌉+2}·√n }` with
`L_n = ⌈log₂(n+1)⌉`. -/
theorem acceptance_discrete
    {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
    (letter : σ → M) (hst : IsStableOrder M) (b : ℕ) (hb : IsBreadthBound letter b) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
          ((2 ^ 15 * ((b : ℝ) + 2) * (Nat.clog 2 (n + 1) : ℝ) ^ 4) ^ (Nat.clog 2 (b + 2) + 2)
            * Real.sqrt n) :=
  ordered_qQuery_third_le_logrank letter hst hb n

/-! ## 6. The linear-exponent pins retained -/

/-- The linear-exponent pins (`thm:ordered-beta-product`: constant `2^27`, exponents `3b` and `5b/2`) are unchanged. -/
theorem ordered_acceptance_retained : True := by
  have := @OrderedAcceptance.acceptance_product
  have := @OrderedAcceptance.acceptance_product_five_halves
  have := @OrderedAcceptance.acceptance_core_five_halves
  trivial

end OrderedLogAcceptance
end MonoidProduct
