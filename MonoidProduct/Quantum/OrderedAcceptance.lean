import MonoidProduct.Quantum.OrderedApplications

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Acceptance test: the ordered product theorem

Statement pins for `thm:ordered-beta-product` as formalized through seeded rejection duals
and a finite quantum mixture.  Like the library's other
pins, this file exists to be broken: a refactor that changes a statement fails here.

Pinned, one theorem each:

1. **A universal constant**, the numeral `2^27`, quantified before the alphabet, the
   monoid, the order, `b` and the input length; no `|M|`, `|σ|`, output-cardinality or
   seed-count factor anywhere.
2. **Explicit hypotheses**: `IsStableOrder M` and `IsBreadthBound letter b`; no
   commutativity, no total order, no finiteness of `M`.
3. **Success at least `9/10`** for a returned record that is a product-preserving set of at
   most `b` original positions, together with the `Q_{1/10}` product bound.
4. **The exact `n`-query fallback**, and zero queries when `b = 0` or `n = 0`.
5. **The exponent `5b/2`** with the same constant: product, real-power form (checked at an
   odd breadth), core algorithm and both error conventions.

Axioms:

    #print axioms MonoidProduct.ordered_qQuery_le        → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.ordered_exists_core_alg  → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
namespace OrderedAcceptance

open QuantumQueryComplexity

/-! ## 1. The constant -/

/-- **The universal constant, pinned**: the absolute numeral `2^27`. -/
def orderedConstant : ℝ := 2 ^ 27

theorem orderedConstant_pinned : orderedConstant = (2 : ℝ) ^ 27 := rfl

/-! ## 2–3. The product bound with the constant quantified first -/

/-- **The product bound**: one real constant, then any finite alphabet, any monoid with a
stable partial order, any breadth bound `b`, any length `n`. -/
theorem acceptance_product :
    ∃ C : ℝ, C = orderedConstant ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → ∀ b : ℕ, IsBreadthBound letter b → ∀ n : ℕ,
        (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
          ≤ min (n : ℝ) ((C * b) ^ b * Real.sqrt n * (Nat.clog 2 (n + 1) : ℝ) ^ (3 * b)) :=
  ⟨orderedConstant, rfl, fun letter hst _b hb n => ordered_qQuery_le letter hst hb n⟩

open Classical in
/-- **The product-and-core algorithm**: for `1 ≤ b < n`, an algorithm within the bound
whose output is, with probability at least `9/10`, a good record; and every good record is
a product-preserving set of at most `b` original positions. -/
theorem acceptance_core {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M]
    [DecidableEq M] (letter : σ → M) (hst : IsStableOrder M) {b : ℕ}
    (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) {n : ℕ} (hbn : b < n) :
    (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ (orderedConstant * b) ^ b * Real.sqrt n * (Nat.clog 2 (n + 1) : ℝ) ^ (3 * b)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K)
    ∧ ∀ (x : Fin n → σ) (K : Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)), GoodRec letter b x K →
        ∃ D : Finset (Fin n), D.card ≤ b ∧ IsCore letter x D :=
  ⟨ordered_exists_core_alg letter hst hb hb1 hbn,
    fun _ _ hK => GoodRec.exists_core letter (le_two_pow_logLen n) hK⟩

/-! ## 4. The fallback and the zero cases -/

theorem acceptance_read_all {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M]
    [PartialOrder M] [DecidableEq M] (letter : σ → M) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → σ => wordProd letter x) ε ≤ n :=
  qQuery_wordProd_le_length letter n hε

theorem acceptance_zero_length {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M]
    [PartialOrder M] [DecidableEq M] (letter : σ → M) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin 0 → σ => wordProd letter x) ε = 0 :=
  qQuery_wordProd_zero_length letter hε

theorem acceptance_zero_breadth {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M]
    [PartialOrder M] [DecidableEq M] (letter : σ → M) (hb : IsBreadthBound letter 0) (n : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → σ => wordProd letter x) ε = 0 :=
  qQuery_wordProd_zero_breadth letter hb n hε

/-! ## 5. The exponent `5b/2`, same constant -/

/-- **The product bound with exponent `5b/2`**: the same constant `2^27`, quantified first. -/
theorem acceptance_product_five_halves :
    ∃ C : ℝ, C = orderedConstant ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → ∀ b : ℕ, IsBreadthBound letter b → ∀ n : ℕ,
        (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
          ≤ min (n : ℝ) ((C * b) ^ b * Real.sqrt n
              * orderedLogFactor (Nat.clog 2 (n + 1)) ^ b) :=
  ⟨orderedConstant, rfl, fun letter hst _b hb n => ordered_qQuery_le_five_halves letter hst hb n⟩

/-- The real-power form, for `n ≥ 1`; the exponent `5·b/2` is a real number. -/
theorem acceptance_rpow {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M]
    [DecidableEq M] (letter : σ → M) (hst : IsStableOrder M) {b : ℕ}
    (hb : IsBreadthBound letter b) {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) ((orderedConstant * b) ^ b * Real.sqrt n
          * (Nat.clog 2 (n + 1) : ℝ) ^ ((5 : ℝ) * b / 2)) :=
  ordered_qQuery_le_rpow letter hst hb hn

/-- Odd breadth: the exponent is `15/2`, not `7`. -/
example : orderedLogFactor 4 ^ 3 = (4 : ℝ) ^ ((15 : ℝ) / 2) := by
  rw [orderedLogFactor_pow_eq_rpow (by norm_num)]
  norm_num

open Classical in
/-- **The product-and-core algorithm with exponent `5b/2`.** -/
theorem acceptance_core_five_halves {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M]
    [PartialOrder M] [DecidableEq M] (letter : σ → M) (hst : IsStableOrder M) {b : ℕ}
    (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) {n : ℕ} (hbn : b < n) :
    (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ (orderedConstant * b) ^ b * Real.sqrt n
          * orderedLogFactor (Nat.clog 2 (n + 1)) ^ b
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K)
    ∧ ∀ (x : Fin n → σ) (K : Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)), GoodRec letter b x K →
        ∃ D : Finset (Fin n), D.card ≤ b ∧ IsCore letter x D :=
  ⟨ordered_exists_core_alg_five_halves letter hst hb hb1 hbn,
    fun _ _ hK => GoodRec.exists_core letter (le_two_pow_logLen n) hK⟩

/-- Both error conventions with exponent `5b/2`. -/
theorem acceptance_third_five_halves {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M]
    [PartialOrder M] [DecidableEq M] (letter : σ → M) (hst : IsStableOrder M) {b : ℕ}
    (hb : IsBreadthBound letter b) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) ((orderedConstant * b) ^ b * Real.sqrt n
          * orderedLogFactor (Nat.clog 2 (n + 1)) ^ b) :=
  ordered_qQuery_third_le_five_halves letter hst hb n

end OrderedAcceptance
end MonoidProduct
