import MonoidProduct.Dyck.Monoid.Reduce
import MonoidProduct.Dyck.Monoid.Green
import MonoidProduct.Aperiodic.Induction
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The two-sided theorem: `2^Θ(J-depth)` for ordered products

This file is where the repository's two monoid layers meet.  The AGS **upper**
bound (`Aperiodic/Induction.lean`) says that over any finite aperiodic monoid
`M`, the ordered product of `n ≤ N` letters has

  `ADV± ≤ 2 · |M| · agsStep(N, M)^(jDepth M + 1) · √n`,

an explicit constant to the power of the `J`-depth.  The Dyck **lower** bound
(`Dyck/Monoid/Reduce.lean`) gives a concrete family on which such exponential
dependence on the `J`-depth is unavoidable: `DyckNF k` has

  `|DyckNF k| = (k+1)(k+2)(2k+3)/6 + 1 ≤ (k+2)³`  and  `jDepth = k + 1`,

yet its ordered-product problem has `ADV± ≥ √n · √2^ℓ / (2√2)` whenever
`4 + 10ℓ ≤ k` and `n ≥ 4·8^ℓ` is even.  `advPM_dyckProduct_sandwich` states
the two bounds together: for `ℓ ≈ k/10`,

  `√n · 2^(Ω(jDepth))  ≤  ADV±(dyckProduct k n)  ≤  √n · C(N, k)^(jDepth + 1)`,

with every constant explicit — the content of the paper's `thm:dyck-lb` +
`prop:dyck-monoid` + `cor:dyck` in `advPM` form, and the counterpart of the
paper's `Ω(√n · 2^(Ω(|M|^(1/3))))` reading via the cubic cardinality.

Since the `J`-depth is `k + 1` and the cardinality is cubic in `k`, the same
sandwich also exhibits the gap in monoid-size terms: the upper bound's base
`agsStep` is polynomial in `|M|` and polylogarithmic in `N`, while the lower
bound is exponential in `|M|^(1/3)`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-- **An elementary bound**: the monoid is at most cubic in the
depth. -/
lemma card_dyckNF_le_cube (k : ℕ) :
    Fintype.card (DyckNF k) ≤ (k + 2) ^ 3 := by
  rw [card_dyckNF_closed]
  have h : (k + 1) * (k + 2) * (2 * k + 3) + 1 ≤ 6 * (k + 2) ^ 3 := by
    have e1 : (k + 1) * (k + 2) * (2 * k + 3)
        = 2 * k ^ 3 + 9 * k ^ 2 + 13 * k + 6 := by ring
    have e2 : 6 * (k + 2) ^ 3 = 6 * k ^ 3 + 36 * k ^ 2 + 72 * k + 48 := by
      ring
    rw [e1, e2]
    omega
  omega

/-- **The AGS certificate instantiated at the hard family**: `dyckProduct`
is definitionally `wordProd (dyckLetter k)`, `DyckNF k` is aperiodic, and
its `J`-depth is `k + 1` — so `hasDual_wordProd` bundles a dual at
`2·|M|·agsStep^(k+2)·√n`. -/
theorem hasDual_dyckProduct (k N n : ℕ) (hn : n ≤ N) :
    HasDual (dyckProduct k n)
      (2 * ((Fintype.card (DyckNF k) : ℝ)
        * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n))) := by
  have h := hasDual_wordProd (M := DyckNF k) (dyckLetter k) N hn
  rw [jDepth_dyckNF] at h
  exact h

/-- **The AGS upper bound instantiated at the hard family** — weak duality
on the bundled certificate. -/
theorem advPM_dyckProduct_le (k N n : ℕ) (hn : n ≤ N) :
    advPM (dyckProduct k n)
      ≤ 2 * ((Fintype.card (DyckNF k) : ℝ)
        * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n)) := by
  have h1 : (1 : ℝ) ≤ agsStep N (DyckNF k) := one_le_agsStep N (DyckNF k)
  refine advPM_le_of_hasDual ?_ (hasDual_dyckProduct k N n hn)
  have h2 : (0 : ℝ) ≤ agsStep N (DyckNF k) ^ (k + 2) := by positivity
  positivity

/-- **The `2^Θ(J-depth)` sandwich**: on the explicit
aperiodic family `DyckNF k` — of cardinality `(k+1)(k+2)(2k+3)/6 + 1` and
`J`-depth `k+1` — the ordered-product problem is pinned between
`√n · √2^ℓ / (2√2)` and `2 |M| · agsStep^(k+2) · √n`. -/
theorem advPM_dyckProduct_sandwich (k ℓ n N : ℕ) (heven : Even n)
    (hfit : 4 * 8 ^ ℓ ≤ n) (hk : 4 + 10 * ℓ ≤ k) (hn : n ≤ N) :
    Real.sqrt n * Real.sqrt 2 ^ ℓ
        ≤ 2 * Real.sqrt 2 * advPM (dyckProduct k n)
      ∧ advPM (dyckProduct k n)
        ≤ 2 * ((Fintype.card (DyckNF k) : ℝ)
          * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n)) :=
  ⟨dyckMonoid_product_lower_fixedBase ℓ n k heven hfit hk,
    advPM_dyckProduct_le k N n hn⟩

end MonoidProduct
