import MonoidProduct.Quantum.DyckApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The legacy Dyck sandwich: acceptance test

The statement pins for the operational `2^Θ(J-depth)` Dyck endpoints.
Like the
other pins, this file exists to be broken; it sits outside the
`QuantumQueryComplexity.Quantum` aggregate and **CI must build it explicitly**:
`lake build QuantumQueryComplexity.Quantum.AcceptanceU`.

Pinned, with every convention literal:

1. **the classical certificate** — `HasDual (dyckProduct k n)` at
   `2·|M|·agsStep^(k+2)·√n`, split out of `advPM_dyckProduct_le`
   (retained in `Dyck/Final.lean` as a weak-duality corollary, and the
   classical sandwich `advPM_dyckProduct_sandwich` unchanged), no
   quantum import in its proof;
2. **the native operational sandwich** — under exactly even `n`,
   `4·8^ℓ ≤ n ≤ N`, `4 + 10·ℓ ≤ k`:
   `7·(√n·√2^ℓ)/(2752·√2) ≤ Q_{1/3} ≤ min{n, 8192·(1 + 2·|M|·agsStep^(k+2)·√n)}`
   (the output is the finite monoid `DyckNF k`, so the lower bound is
   the direct plurality `7/1376` extraction — no recoding);
3. **the one-hot sandwich** at `7/(5504·√2)` and `16384` with the same
   exact cap.

As in the classical sandwich, the upper base is polynomial in `|M|` and
the lower bound exponential in the `J`-depth: the `2^Θ(J-depth)` gap,
operational.

Manual axiom checks:

    #print axioms MonoidProduct.dyck_qQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.dyck_oneHotQQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
open QuantumQueryComplexity
namespace AcceptanceU

variable {k N n ℓ : ℕ}

/-! ## 1. The classical certificate -/

theorem dual_pinned (hn : n ≤ N) :
    HasDual (dyckProduct k n)
      (2 * ((Fintype.card (DyckNF k) : ℝ)
        * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n))) :=
  hasDual_dyckProduct k N n hn

theorem advPM_pinned (hn : n ≤ N) :
    advPM (dyckProduct k n)
      ≤ 2 * ((Fintype.card (DyckNF k) : ℝ)
        * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n)) :=
  advPM_dyckProduct_le k N n hn

/-! ## 2. The native operational sandwich -/

theorem native_sandwich_pinned (heven : Even n) (hfit : 4 * 8 ^ ℓ ≤ n)
    (hk : 4 + 10 * ℓ ≤ k) (hn : n ≤ N) :
    7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (2752 * Real.sqrt 2)
        ≤ (qQuery (dyckProduct k n) (1 / 3) : ℝ)
      ∧ (qQuery (dyckProduct k n) (1 / 3) : ℝ)
        ≤ min (n : ℝ) (8192
            * (1 + 2 * ((Fintype.card (DyckNF k) : ℝ)
              * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n)))) := by
  have h := dyck_qQuery_sandwich heven hfit hk hn
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

/-! ## 3. The one-hot sandwich -/

theorem oneHot_sandwich_pinned (heven : Even n) (hfit : 4 * 8 ^ ℓ ≤ n)
    (hk : 4 + 10 * ℓ ≤ k) (hn : n ≤ N) :
    7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (5504 * Real.sqrt 2)
        ≤ (oneHotQQuery (dyckProduct k n) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (dyckProduct k n) (1 / 3) : ℝ)
        ≤ min (n : ℝ) (16384
            * (1 + 2 * ((Fintype.card (DyckNF k) : ℝ)
              * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n)))) :=
  dyck_oneHotQQuery_sandwich heven hfit hk hn

end AcceptanceU

end MonoidProduct
