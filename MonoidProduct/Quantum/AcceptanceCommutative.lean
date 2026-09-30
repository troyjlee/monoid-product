import MonoidProduct.Quantum.CommutativeLower

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Acceptance: the commutative lower bound (`res:commutative`, `thm:commutative-beta`)

Statement pins for the lower half of `res:commutative`.  Like the library's
other pins, this file exists to be broken: a refactor that changes a statement fails here.

Pinned, one theorem each:

1. **The alphabet-relative lower bound**: any finite alphabet `σ`, any letter map `m`, any
   identity symbol `s0` (a noninjective map and repeated core letters are allowed), any
   finite commutative aperiodic monoid, `n ≥ 1`, `β ≥ 1`:
   `√(n·min{n, β})/72 ≤ Q_{1/3}(∏ᵢ m(xᵢ))`.  No distinct-letter assumption, no `|M|` factor,
   no assumed lower-bound certificate.
2. **The full alphabet** `σ = M`, `m = id`, under `Nontrivial M` (which gives `β ≥ 1`), in
   both the `∏` and the `wordProd` form.
3. **The one-hot oracle**, constant `1/144`.
4. **The sandwich**: `√(n·min{n,β})/72 ≤ Q_{1/3} ≤ min{n, 2^18·√(n·min{n,β})}`, i.e.
   `Q_{1/3}(Prod_{M,G,n}) = Θ(min{n, √(nβ)})` with explicit constants.
5. **Boundary regimes**: the statements apply verbatim at `n = 1`, at `β = 1`, and at
   `β ≥ n` (where `min{n, β} = n`); the trivial monoid and breadth `0` are excluded by the
   hypotheses `Nontrivial M` / `1 ≤ β`, as they must be (no queries are needed there).

Axioms:

    #print axioms MonoidProduct.commutative_qQuery_lower        → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.commutative_qQuery_sandwich     → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
namespace CommutativeAcceptance

open QuantumQueryComplexity

/-! ## 1. The alphabet-relative lower bound -/

theorem acceptance_lower_alphabet :
    ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Fintype M] [DecidableEq M] [CommMonoid M]
      [IsAperiodicMonoid M] (m : σ → M) (s0 : σ), m s0 = 1 →
      ∀ {n : ℕ}, 1 ≤ n → 1 ≤ breadth m →
        Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 72
          ≤ (qQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ) :=
  fun m s0 hs0 => fun hn hb => commutative_qQuery_lower m s0 hs0 hn hb

/-! ## 2. The full alphabet -/

theorem acceptance_lower_total :
    ∀ {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M] [IsAperiodicMonoid M]
      [Nontrivial M] {n : ℕ}, 1 ≤ n →
        Real.sqrt ((n * min n (breadth (id : M → M)) : ℕ) : ℝ) / 72
          ≤ (qQuery (fun x : Fin n → M => ∏ i, x i) (1 / 3) : ℝ) :=
  fun hn => commutative_qQuery_lower_total hn

theorem acceptance_lower_wordProd :
    ∀ {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M] [IsAperiodicMonoid M]
      [Nontrivial M] {n : ℕ}, 1 ≤ n →
        Real.sqrt ((n * min n (breadth (id : M → M)) : ℕ) : ℝ) / 72
          ≤ (qQuery (fun x : Fin n → M => wordProd (id : M → M) x) (1 / 3) : ℝ) :=
  fun hn => commutative_qQuery_lower_wordProd hn

/-- A nontrivial monoid has breadth at least one over its full alphabet (the hypothesis of
the total form is genuinely weaker than `1 ≤ β`). -/
theorem acceptance_one_le_breadth :
    ∀ {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M] [IsAperiodicMonoid M]
      [Nontrivial M], 1 ≤ breadth (id : M → M) :=
  one_le_breadth_id

/-! ## 3. The one-hot oracle -/

theorem acceptance_lower_oneHot :
    ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Fintype M] [DecidableEq M] [CommMonoid M]
      [IsAperiodicMonoid M] (m : σ → M) (s0 : σ), m s0 = 1 →
      ∀ {n : ℕ}, 1 ≤ n → 1 ≤ breadth m →
        Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 144
          ≤ (oneHotQQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ) :=
  fun m s0 hs0 => fun hn hb => commutative_oneHotQQuery_lower m s0 hs0 hn hb

/-! ## 4. The sandwich -/

theorem acceptance_sandwich :
    ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Fintype M] [DecidableEq M] [CommMonoid M]
      [IsAperiodicMonoid M] (m : σ → M) (s0 : σ), m s0 = 1 →
      ∀ {n : ℕ}, 1 ≤ n → 1 ≤ breadth m →
        Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 72
            ≤ (qQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
          ∧ (qQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
            ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ)) :=
  fun m s0 hs0 => fun hn hb => commutative_qQuery_sandwich m s0 hs0 hn hb

/-! ## 5. Boundary regimes -/

/-- `n = 1`: the bound reads `1/72 ≤ Q_{1/3}` (one query is needed). -/
example {σ M : Type} [Fintype σ] [DecidableEq σ] [Fintype M] [DecidableEq M] [CommMonoid M]
    [IsAperiodicMonoid M] (m : σ → M) (s0 : σ) (hs0 : m s0 = 1) (hb : 1 ≤ breadth m) :
    (1 : ℝ) / 72 ≤ (qQuery (fun x : Fin 1 → σ => ∏ i, m (x i)) (1 / 3) : ℝ) := by
  have h := commutative_qQuery_lower m s0 hs0 (le_refl 1) hb
  have hmin : min 1 (breadth m) = 1 := min_eq_left hb
  rw [hmin] at h
  simpa using h

/-- `β ≥ n`: the bound is `√(n·n)/72 = n/72`, the linear regime. -/
example {σ M : Type} [Fintype σ] [DecidableEq σ] [Fintype M] [DecidableEq M] [CommMonoid M]
    [IsAperiodicMonoid M] (m : σ → M) (s0 : σ) (hs0 : m s0 = 1) {n : ℕ} (hn : 1 ≤ n)
    (hbn : n ≤ breadth m) :
    (n : ℝ) / 72 ≤ (qQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ) := by
  have h := commutative_qQuery_lower m s0 hs0 hn (le_trans hn hbn)
  rw [min_eq_left hbn] at h
  have hsq : Real.sqrt ((n * n : ℕ) : ℝ) = n := by
    rw [Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg n)]
  rwa [hsq] at h

end CommutativeAcceptance
end MonoidProduct
