import MonoidProduct.Dyck.Final
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.Plurality
import MonoidProduct.Quantum.OneHotApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The legacy Dyck sandwich: the operational quantum-query endpoints

The `2^Θ(J-depth)` sandwich (the paper's `cor:dyck`) on the explicit aperiodic
family `DyckNF k`, operational in both oracle models:

* **native** (transposition oracle): for `n ≤ N`,
  `Q_{1/3}(dyckProduct k n) ≤ min{n, 8192·(1 + 2·|M|·agsStep^(k+2)·√n)}`
  with `|M| = Fintype.card (DyckNF k)`, and — for even `n ≥ 4·8^ℓ` and
  depth `k ≥ 4 + 10·ℓ` —
  `7·(√n·√2^ℓ)/(2752·√2) ≤ Q_{1/3}(dyckProduct k n)`;
* **one-hot** (the canonical one-hot XOR oracle model): the same at a
  direct factor two — `16384` and `7/(5504·√2)` — with the **exact**
  read-all cap `n` in both models.

The upper route preserves the AGS certificate:
`hasDual_dyckProduct` (split out of `advPM_dyckProduct_le` in
`Dyck/Final.lean`, which is retained there as a weak-duality corollary)
`→ qQueryOn_third_le_of_hasDualOn_uniform`.  The lower route is
`dyckMonoid_product_lower_fixedBase` through the plurality `7/1376`
finite-output extraction at `read = id` — `DyckNF k` is a `Fintype`, so
no recoding is needed.  As in the classical sandwich, the upper bound's
base is polynomial in `|M|` and the lower bound exponential in the
`J`-depth, exhibiting the `2^Θ(J-depth)` gap operationally.

This file sits outside the `QuantumQueryComplexity.Quantum` aggregate: it is an
application layer importing both the classical Dyck development and the
quantum model, built by CI as an explicit cross-stream target.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {k N n ℓ : ℕ}

/-! ## The native model -/

/-- **The certificate-preserving compiler bound**: for `n ≤ N`,
`Q_{1/3}(dyckProduct k n) ≤ 8192·(1 + 2·|M|·agsStep^(k+2)·√n)`. -/
theorem dyck_qQuery_upper (hn : n ≤ N) :
    (qQuery (dyckProduct k n) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 2 * ((Fintype.card (DyckNF k) : ℝ)
            * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n))) := by
  refine qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_dyckProduct k N n hn).hasDualOn ?_
  have h1 : (1 : ℝ) ≤ agsStep N (DyckNF k) := one_le_agsStep N (DyckNF k)
  have h2 : (0 : ℝ) ≤ agsStep N (DyckNF k) ^ (k + 2) := by positivity
  positivity

/-- **Reading every letter**: the exact cap `Q_{1/3}(dyckProduct k n) ≤ n`. -/
theorem dyck_qQuery_upper_length :
    qQuery (dyckProduct k n) (1 / 3) ≤ n := by
  have h := qQueryOn_le_card
    (read := (id : (Fin n → Bool) → Fin n → Bool))
    (f := dyckProduct k n)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The unabsorbed minimum form**. -/
theorem dyck_qQuery_le_min (hn : n ≤ N) :
    (qQuery (dyckProduct k n) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (uniformExtractionConstant
          * (1 + 2 * ((Fintype.card (DyckNF k) : ℝ)
            * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n)))) :=
  le_min (by exact_mod_cast dyck_qQuery_upper_length) (dyck_qQuery_upper hn)

/-- **The operational lower bound**: for even `n ≥ 4·8^ℓ` and depth
`k ≥ 4 + 10·ℓ`, `7·(√n·√2^ℓ)/(2752·√2) ≤ Q_{1/3}(dyckProduct k n)` —
the block certificate through the plurality `7/1376` extraction. -/
theorem dyck_qQuery_lower (heven : Even n) (hfit : 4 * 8 ^ ℓ ≤ n)
    (hk : 4 + 10 * ℓ ≤ k) :
    7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (2752 * Real.sqrt 2)
      ≤ (qQuery (dyckProduct k n) (1 / 3) : ℝ) := by
  have hadv := dyckMonoid_product_lower_fixedBase ℓ n k heven hfit hk
  have hpar := mul_advPMOn_le_qQueryOn_third_finiteOutput
    (read := (id : (Fin n → Bool) → Fin n → Bool)) (f := dyckProduct k n)
    (fun x y hxy => by rw [show x = y from hxy])
  have hid : advPMOn (id : (Fin n → Bool) → Fin n → Bool) (dyckProduct k n)
      = advPM (dyckProduct k n) := rfl
  rw [hid] at hpar
  have h2 : Real.sqrt n * Real.sqrt 2 ^ ℓ / (2 * Real.sqrt 2)
      ≤ advPM (dyckProduct k n) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)]
    nlinarith [hadv]
  calc 7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (2752 * Real.sqrt 2)
      = (7 / 1376 : ℝ)
          * (Real.sqrt n * Real.sqrt 2 ^ ℓ / (2 * Real.sqrt 2)) := by ring
    _ ≤ (7 / 1376 : ℝ) * advPM (dyckProduct k n) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ _ := hpar

/-- **The operational `2^Θ(J-depth)` sandwich**: for even `n` with
`4·8^ℓ ≤ n ≤ N` and depth `k ≥ 4 + 10·ℓ`,

    7·(√n·√2^ℓ)/(2752·√2) ≤ Q_{1/3}(dyckProduct k n)
      ≤ min{n, 8192·(1 + 2·|M|·agsStep^(k+2)·√n)}. -/
theorem dyck_qQuery_sandwich (heven : Even n) (hfit : 4 * 8 ^ ℓ ≤ n)
    (hk : 4 + 10 * ℓ ≤ k) (hn : n ≤ N) :
    7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (2752 * Real.sqrt 2)
        ≤ (qQuery (dyckProduct k n) (1 / 3) : ℝ)
      ∧ (qQuery (dyckProduct k n) (1 / 3) : ℝ)
        ≤ min (n : ℝ) (uniformExtractionConstant
            * (1 + 2 * ((Fintype.card (DyckNF k) : ℝ)
              * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n)))) :=
  ⟨dyck_qQuery_lower heven hfit hk, dyck_qQuery_le_min hn⟩

/-! ## The one-hot model -/

/-- **The compiler bound in the one-hot model**, at a direct factor two. -/
theorem dyck_oneHotQQuery_upper (hn : n ≤ N) :
    (oneHotQQuery (dyckProduct k n) (1 / 3) : ℝ)
      ≤ 16384 * (1 + 2 * ((Fintype.card (DyckNF k) : ℝ)
          * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n))) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (dyckProduct k n)) (by norm_num) (dyck_qQuery_upper hn)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every letter, one-hot**: the exact cap `n` — direct, not
through simulation. -/
theorem dyck_oneHotQQuery_upper_length :
    oneHotQQuery (dyckProduct k n) (1 / 3) ≤ n := by
  have h := oneHotQQuery_le_card (dyckProduct k n)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The one-hot lower bound**, at a direct factor two:
`7·(√n·√2^ℓ)/(5504·√2) ≤ Q^{1-hot}_{1/3}(dyckProduct k n)`. -/
theorem dyck_oneHotQQuery_lower (heven : Even n) (hfit : 4 * 8 ^ ℓ ≤ n)
    (hk : 4 + 10 * ℓ ≤ k) :
    7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (5504 * Real.sqrt 2)
      ≤ (oneHotQQuery (dyckProduct k n) (1 / 3) : ℝ) := by
  have h2 := half_le_oneHotQQueryOn_of_le_qQueryOn
    (id_det (dyckProduct k n)) (by norm_num)
    (dyck_qQuery_lower heven hfit hk)
  calc 7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (5504 * Real.sqrt 2)
      = (7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (2752 * Real.sqrt 2)) / 2 := by
        ring
    _ ≤ _ := h2

/-- **The one-hot `2^Θ(J-depth)` sandwich**. -/
theorem dyck_oneHotQQuery_sandwich (heven : Even n) (hfit : 4 * 8 ^ ℓ ≤ n)
    (hk : 4 + 10 * ℓ ≤ k) (hn : n ≤ N) :
    7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (5504 * Real.sqrt 2)
        ≤ (oneHotQQuery (dyckProduct k n) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (dyckProduct k n) (1 / 3) : ℝ)
        ≤ min (n : ℝ) (16384
            * (1 + 2 * ((Fintype.card (DyckNF k) : ℝ)
              * (agsStep N (DyckNF k) ^ (k + 2) * Real.sqrt n)))) :=
  ⟨dyck_oneHotQQuery_lower heven hfit hk,
    le_min (by exact_mod_cast dyck_oneHotQQuery_upper_length)
      (dyck_oneHotQQuery_upper hn)⟩

end MonoidProduct
