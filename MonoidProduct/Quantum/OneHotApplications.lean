import MonoidProduct.Quantum.Applications
import QuantumQueryComplexity.Quantum.OneHotTransport
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The endpoints in the canonical one-hot XOR oracle model

`Applications.lean` states the paper's theorems in the native transposition
model.  This file transports them to the **canonical one-hot XOR oracle
model** of `OneHot.lean` — a concrete unitary realization of the paper's
whole-element value-oracle convention — through the direct factor-two
simulation of `OneHotSimulation.lean`:
lower bounds halve, upper bounds double, and the trivial cap `n` is kept
*exact* by the direct one-hot read-all of `OneHotReadAll.lean` rather than
inflated to `2n` by simulation.

The constants: `1/36 ↦ 1/72` on the tropical and unitriangular lower bounds,
`8192 ↦ 16384` on the unitriangular upper bound, and
`147456 ↦ 294912` on the 𝓙-trivial bound.  Nothing here claims equivalence
with every finite-alphabet oracle convention — only with this one.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## The tropical product -/

section Tropical

variable {k n d : ℕ}

/-- **The tropical lower bound, in the one-hot model**:
`1/72·√(nd/2) ≤ Q^{1-hot}_{1/3}(Prod_{U_k(T),n})` on the promise. -/
theorem tropical_oneHotQQuery_lower (hd : 0 < d) (hdn : d ≤ n) (hdk : d < k) :
    (1 / 72 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (oneHotQQueryOn (dsRead (modBlk n d hd))
          (fun x => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
            (dsRead (modBlk n d hd) x)) (1 / 3) : ℝ) := by
  have h := half_le_oneHotQQueryOn_of_le_qQueryOn
    (fun x y hxy => by rw [dsRead_injective _ hxy]) (by norm_num)
    (tropical_qQuery_lower hd hdn hdk)
  calc (1 / 72 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      = ((1 / 36 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)) / 2 := by ring
    _ ≤ _ := h

end Tropical

/-! ## The Boolean unitriangular product -/

section UT

variable {k n : ℕ}

/-- **The `UT_k(𝔹)` product, in the one-hot model**:
`Q^{1-hot}_{1/3}(Prod_{UT_k(𝔹),n}) ≤ 16384(1 + 8√(n·min{n, C(k,2)}))`. -/
theorem ut_oneHotQQuery_upper :
    (oneHotQQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
      ≤ 16384 * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ))) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
    (ut_qQuery_upper (k := k) (n := n))
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every letter**, with the exact cap:
`Q^{1-hot}_{1/3}(Prod_{UT_k(𝔹),n}) ≤ n`. -/
theorem ut_oneHotQQuery_upper_length :
    oneHotQQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) ≤ n := by
  have h := oneHotQQuery_le_card (fun w : Fin n → BUT k => wordProd id w)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The cross-edge lower bound, in the one-hot model**:
`1/72·√(n·min{n,⌊k²/4⌋}/2) ≤ Q^{1-hot}_{1/3}(Prod_{UT_k(𝔹),n})`. -/
theorem ut_oneHotQQuery_lower (hk : 2 ≤ k) (hn : 0 < n) :
    (1 / 72 : ℝ) * Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ)
      ≤ (oneHotQQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ) := by
  have h := half_le_oneHotQQueryOn_of_le_qQueryOn (id_det _) (by norm_num)
    (ut_qQuery_sandwich hk hn).1
  calc (1 / 72 : ℝ) * Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ)
      = ((1 / 36 : ℝ) * Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ)) / 2 := by
        ring
    _ ≤ _ := h

/-- **Theorem `thm:boolean-unitriangular`, in the one-hot model**: for
`k ≥ 2` and `n ≥ 1`,

    1/72·√(n·min{n,⌊k²/4⌋}/2) ≤ Q^{1-hot}_{1/3}(Prod_{UT_k(𝔹),n})
      ≤ min{n, 16384(1 + 8√(n·min{n, C(k,2)}))},

i.e. `Θ(min{n, k√n})` with universal constants. -/
theorem ut_oneHotQQuery_sandwich (hk : 2 ≤ k) (hn : 0 < n) :
    (1 / 72 : ℝ) * Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ)
        ≤ (oneHotQQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
        ≤ min (n : ℝ)
            (16384 * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)))) :=
  ⟨ut_oneHotQQuery_lower hk hn,
   le_min (by exact_mod_cast ut_oneHotQQuery_upper_length) ut_oneHotQQuery_upper⟩

/-! ## The 𝓙-trivial product -/

/-- **The unconditional 𝓙-trivial theorem, in the one-hot model**:
`Q^{1-hot}_{1/3}(Prod_{M,n}) ≤ min{n, 294912·√(n·min{n, C(τ(M),2)})}`. -/
theorem jtrivial_oneHotQQuery_le_min {M : Type} [Monoid M] [Fintype M]
    [DecidableEq M] (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
        (294912 * Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))) := by
  have hcard : oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) ≤ n := by
    have h := oneHotQQuery_le_card (fun w : Fin n → M => wordProd id w)
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [Fintype.card_fin] at h
  refine le_min (by exact_mod_cast hcard) ?_
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
    (le_trans (jtrivial_qQuery_le_min hJ hn) (min_le_right _ _))
  rw [show (294912 : ℝ) = 2 * 147456 by norm_num, mul_assoc]
  exact h

end UT

end MonoidProduct
