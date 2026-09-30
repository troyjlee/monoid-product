import MonoidProduct.Quantum.OneHotApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# One-hot oracle model: acceptance test

The statement pin for the **canonical one-hot XOR oracle model** and the
transport of the paper's endpoints into it.  Like the other pins, this file
exists to be broken: a refactor that changes a statement fails here.

Pinned:

1. **The model** — `Hot σ := σ → Bool`, `hotCode a b := decide (b = a)`; the
   oracle XORs `hotCode (x i)` into an active `Hot σ` register, fixes `none`
   and idle indices, and the clean answer is `some hotZero`.
2. **The direct factor-two comparison** — the exact membership contracts
   `q ∈ OneHotXorQueryCounts → 2q ∈ QueryCounts` and
   `q ∈ QueryCounts → 2q ∈ OneHotXorQueryCounts`, and the complexity
   comparisons they give; *not* routed through the Boolean XOR model.
3. **The exact cap** — `oneHotQQueryOn ≤ |ι|` from the direct one-hot
   read-all, not `2|ι|` from simulation.
4. **The transported endpoints** — tropical lower `1/72`;
   `UT_k(𝔹)` in `min{n, 16384(1 + 8√(n·min{n, C(k,2)}))}` with the `1/72`
   lower bound; 𝓙-trivial in `min{n, 294912·√(n·min{n, C(τ(M),2)})}`.

This pins one specific oracle convention.  It does not claim equivalence
with every finite-alphabet oracle convention.

    #print axioms QuantumQueryComplexity.qQueryOn_le_two_mul_oneHotQQueryOn
      → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
open QuantumQueryComplexity
namespace AcceptanceG

/-! ## 1. The model -/

example {σ : Type} [Fintype σ] [DecidableEq σ] (a b : σ) :
    hotCode a b = decide (b = a) := rfl

example {σ : Type} [Fintype σ] [DecidableEq σ] : Hot σ = (σ → Bool) := rfl

/-- The oracle on a clean active register reads the code; idle indices and
blank registers are fixed. -/
theorem oracle_pinned {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] [Fintype W] [DecidableEq W] (a : ι → σ) (i : ι)
    (t : Option (Hot σ)) (w : W) :
    oneHotOracleMap a ((some i, some hotZero, w) : QBasis ι (Hot σ) W)
        = (some i, some (hotCode (a i)), w)
      ∧ oneHotOracleMap a ((none, t, w) : QBasis ι (Hot σ) W) = (none, t, w)
      ∧ oneHotOracleMap a ((some i, none, w) : QBasis ι (Hot σ) W)
        = (some i, none, w) :=
  ⟨oneHotOracleMap_clean a i w, rfl, rfl⟩

theorem oracle_unitary_pinned {ι σ W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype W] [DecidableEq W] (a : ι → σ) :
    oneHotOracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι (Hot σ) W) ℂ
      ∧ oneHotOracleMat (W := W) a * oneHotOracleMat a = 1 :=
  ⟨oneHotOracleMat_mem_unitaryGroup a, oneHotOracleMat_mul_self a⟩

/-! ## 2. The direct factor-two comparison -/

section Compare

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [DecidableEq O] {X : Type} [Fintype X]

theorem membership_pinned {read : X → ι → σ} {f : X → O} {ε : ℝ} {q : ℕ} :
    (q ∈ OneHotXorQueryCounts read f ε → 2 * q ∈ QueryCounts read f ε)
      ∧ (q ∈ QueryCounts read f ε → 2 * q ∈ OneHotXorQueryCounts read f ε) :=
  ⟨two_mul_mem_queryCounts_of_oneHot, two_mul_mem_oneHotXorQueryCounts_of_std⟩

variable [Nonempty O]

theorem comparison_pinned {read : X → ι → σ} {f : X → O} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    qQueryOn read f ε ≤ 2 * oneHotQQueryOn read f ε
      ∧ oneHotQQueryOn read f ε ≤ 2 * qQueryOn read f ε :=
  ⟨qQueryOn_le_two_mul_oneHotQQueryOn hdet hε0,
   oneHotQQueryOn_le_two_mul_qQueryOn hdet hε0⟩

/-! ## 3. The exact cap -/

theorem cap_pinned {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) {ε : ℝ} (hε : 0 ≤ ε) :
    oneHotQQueryOn read f ε ≤ Fintype.card ι :=
  oneHotQQueryOn_le_card hdet hε

end Compare

/-! ## 4. The transported endpoints -/

theorem tropical_lower_pinned {k n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (hdk : d < k) :
    (1 / 72 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (oneHotQQueryOn (dsRead (modBlk n d hd))
          (fun x => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
            (dsRead (modBlk n d hd) x)) (1 / 3) : ℝ) :=
  tropical_oneHotQQuery_lower hd hdn hdk

theorem ut_pinned {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    (1 / 72 : ℝ) * Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ)
        ≤ (oneHotQQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
        ≤ min (n : ℝ)
            (16384 * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)))) :=
  ut_oneHotQQuery_sandwich hk hn

theorem jtrivial_pinned {M : Type} [Monoid M] [Fintype M] [DecidableEq M]
    {n : ℕ} (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
        (294912 * Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))) :=
  jtrivial_oneHotQQuery_le_min hJ hn

end AcceptanceG
end MonoidProduct
