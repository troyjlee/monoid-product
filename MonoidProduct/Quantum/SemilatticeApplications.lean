import MonoidProduct.SemilatticeCerts
import QuantumQueryComplexity.Quantum.UniformHasDual
import MonoidProduct.Quantum.OneHotApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Semilattice and semigroup products: the operational quantum-query
endpoints

The `O(√(n log |L|))` bounded-error quantum query complexity of computing
the product of the letters read at `n` query positions, as named theorems
in both oracle models:

* **join form** (a finite join-semilattice `A`):
  `Q_{1/3}(⋁ᵢ m(xᵢ)) ≤ min{n, 8192·(1 + 16·√(n·⌊log₂(|A|+1)⌋))}`;
* **semigroup form** (a finite commutative idempotent semigroup `M`):
  the same bound for `∏ᵢ m(xᵢ)`;
* **instance-sensitive promise form**: on the `SmallJoin` promise that
  every input's prefixes have at most `B` critical positions,
  `Q_{1/3} ≤ min{n, 8192·(1 + 16·√n·√B)}` — with no reference at all to
  the size of the value type;
* **one-hot**: the total forms at a direct factor two (`16384`), with the
  **exact** read-all cap `n` in both models;
* **ambient forms**: the value type may be **infinite** — only
  the finite subsemilattice/subsemigroup the letters generate is ever
  counted (`joinBits (Generated m)` / `joinBits (GeneratedSub m)`).

The upper route preserves the weighted-scan dual certificate:
`hasDual_joinMap`/`hasDual_prodMap`/`hasDualOn_joinMap_smallJoin`
(`SemilatticeCerts.lean`) `→ qQueryOn_third_le_of_hasDualOn_uniform` —
the cardinality-free extraction, so every bound is **uniform in the
letter alphabet**.  This family is an upper-bound story: no matching
lower bound is claimed, and the classical `advPM` theorems
(`advPM_joinMap_le`, `advPM_prodMap_le`, `advPMOn_joinMap_smallJoin`)
remain in place unchanged as the compatibility layer.

This file sits outside the `QuantumQueryComplexity.Quantum` aggregate: it is an
application layer importing both the classical semilattice development
and the quantum model, built by CI as an explicit cross-stream target.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type} [Fintype A] [DecidableEq A] [SemilatticeSup A]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## The join form, native -/

/-- **The compiler bound for the join**:
`Q_{1/3}(⋁ᵢ m(xᵢ)) ≤ 8192·(1 + 16·√(n·⌊log₂(|A|+1)⌋))`, uniformly in the
letter alphabet. -/
theorem joinMap_qQuery_upper [Nonempty A] (m : σ → A) :
    (qQuery (joinMap m : (ι → σ) → A) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ))) :=
  qQueryOn_third_le_of_hasDualOn_uniform (hasDual_joinMap m).hasDualOn
    (by positivity)

/-- **Reading every position**: the exact cap `Q_{1/3} ≤ n`. -/
theorem joinMap_qQuery_upper_length [Nonempty A] (m : σ → A) :
    qQuery (joinMap m : (ι → σ) → A) (1 / 3) ≤ Fintype.card ι :=
  qQueryOn_le_card (read := (id : (ι → σ) → ι → σ))
    (f := (joinMap m : (ι → σ) → A))
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form**:
`Q_{1/3}(⋁ᵢ m(xᵢ)) ≤ min{n, 8192·(1 + 16·√(n·⌊log₂(|A|+1)⌋))}`. -/
theorem joinMap_qQuery_le_min [Nonempty A] (m : σ → A) :
    (qQuery (joinMap m : (ι → σ) → A) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ)))) :=
  le_min (by exact_mod_cast joinMap_qQuery_upper_length m)
    (joinMap_qQuery_upper m)

/-! ## The join form, one-hot -/

/-- **The compiler bound in the one-hot model**, at a direct factor two:
`Q^{1-hot}_{1/3}(⋁ᵢ m(xᵢ)) ≤ 16384·(1 + 16·√(n·⌊log₂(|A|+1)⌋))`. -/
theorem joinMap_oneHotQQuery_upper [Nonempty A] (m : σ → A) :
    (oneHotQQuery (joinMap m : (ι → σ) → A) (1 / 3) : ℝ)
      ≤ 16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ))) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (joinMap m : (ι → σ) → A)) (by norm_num) (joinMap_qQuery_upper m)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every position, one-hot**: the exact cap `n` — direct, not
through simulation (which would weaken it to `2n`). -/
theorem joinMap_oneHotQQuery_upper_length [Nonempty A] (m : σ → A) :
    oneHotQQuery (joinMap m : (ι → σ) → A) (1 / 3) ≤ Fintype.card ι :=
  oneHotQQuery_le_card (joinMap m : (ι → σ) → A)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form, one-hot**. -/
theorem joinMap_oneHotQQuery_le_min [Nonempty A] (m : σ → A) :
    (oneHotQQuery (joinMap m : (ι → σ) → A) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ)))) :=
  le_min (by exact_mod_cast joinMap_oneHotQQuery_upper_length m)
    (joinMap_oneHotQQuery_upper m)

/-! ## The instance-sensitive promise form -/

/-- **The operational instance-sensitive bound**: on the promise that
every input's prefixes have at most `B` critical positions,
`Q_{1/3} ≤ 8192·(1 + 16·√n·√B)` — no reference to the size of the value
type. -/
theorem joinMap_qQueryOn_smallJoin_upper [Nonempty A] {B : ℕ} (m : σ → A)
    (hB : 0 < B) :
    (qQueryOn (SmallJoin.read m B)
        (fun x : SmallJoin (ι := ι) m B => joinMap m (SmallJoin.read m B x))
        (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)) :=
  qQueryOn_third_le_of_hasDualOn_uniform (hasDualOn_joinMap_smallJoin m hB)
    (by positivity)

/-- **Reading every position on the promise**: the exact cap `n`. -/
theorem joinMap_qQueryOn_smallJoin_upper_length [Nonempty A] {B : ℕ}
    (m : σ → A) :
    qQueryOn (SmallJoin.read m B)
        (fun x : SmallJoin (ι := ι) m B => joinMap m (SmallJoin.read m B x))
        (1 / 3)
      ≤ Fintype.card ι :=
  qQueryOn_le_card (read := SmallJoin.read m B)
    (fun x y h => by rw [show SmallJoin.read m B x = SmallJoin.read m B y
      from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form on the promise**:
`Q_{1/3} ≤ min{n, 8192·(1 + 16·√n·√B)}`. -/
theorem joinMap_qQueryOn_smallJoin_le_min [Nonempty A] {B : ℕ} (m : σ → A)
    (hB : 0 < B) :
    (qQueryOn (SmallJoin.read m B)
        (fun x : SmallJoin (ι := ι) m B => joinMap m (SmallJoin.read m B x))
        (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B))) :=
  le_min (by exact_mod_cast joinMap_qQueryOn_smallJoin_upper_length m)
    (joinMap_qQueryOn_smallJoin_upper m hB)

/-! ## The semigroup form -/

section Product

variable {M : Type} [Fintype M] [DecidableEq M] [Nonempty M]
  [IsIdemCommSemigroup M]

/-- **The compiler bound for the semigroup product**:
`Q_{1/3}(∏ᵢ m(xᵢ)) ≤ 8192·(1 + 16·√(n·⌊log₂(|M|+1)⌋))` in a finite
commutative idempotent semigroup, uniformly in the letter alphabet. -/
theorem prodMap_qQuery_upper (m : σ → M) :
    (qQuery (prodMap m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits M : ℝ))) :=
  qQueryOn_third_le_of_hasDualOn_uniform (hasDual_prodMap m).hasDualOn
    (by positivity)

/-- **Reading every position**: the exact cap `Q_{1/3} ≤ n`. -/
theorem prodMap_qQuery_upper_length (m : σ → M) :
    qQuery (prodMap m : (ι → σ) → M) (1 / 3) ≤ Fintype.card ι :=
  qQueryOn_le_card (read := (id : (ι → σ) → ι → σ))
    (f := (prodMap m : (ι → σ) → M))
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form**:
`Q_{1/3}(∏ᵢ m(xᵢ)) ≤ min{n, 8192·(1 + 16·√(n·⌊log₂(|M|+1)⌋))}`. -/
theorem prodMap_qQuery_le_min (m : σ → M) :
    (qQuery (prodMap m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits M : ℝ)))) :=
  le_min (by exact_mod_cast prodMap_qQuery_upper_length m)
    (prodMap_qQuery_upper m)

/-- **The compiler bound in the one-hot model**, at a direct factor two:
`Q^{1-hot}_{1/3}(∏ᵢ m(xᵢ)) ≤ 16384·(1 + 16·√(n·⌊log₂(|M|+1)⌋))`. -/
theorem prodMap_oneHotQQuery_upper (m : σ → M) :
    (oneHotQQuery (prodMap m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ 16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits M : ℝ))) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (prodMap m : (ι → σ) → M)) (by norm_num) (prodMap_qQuery_upper m)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every position, one-hot**: the exact cap `n`. -/
theorem prodMap_oneHotQQuery_upper_length (m : σ → M) :
    oneHotQQuery (prodMap m : (ι → σ) → M) (1 / 3) ≤ Fintype.card ι :=
  oneHotQQuery_le_card (prodMap m : (ι → σ) → M)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form, one-hot**. -/
theorem prodMap_oneHotQQuery_le_min (m : σ → M) :
    (oneHotQQuery (prodMap m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits M : ℝ)))) :=
  le_min (by exact_mod_cast prodMap_oneHotQQuery_upper_length m)
    (prodMap_oneHotQQuery_upper m)

end Product

/-! ## The ambient forms

The value type may be **infinite** — the cardinality-free extraction
never counts it, and the certificates charge only the finite
subsemilattice the letters generate. -/

section Ambient

variable [Nonempty σ]

/-- **The ambient join, operational**: for any (possibly infinite)
semilattice `M`, `Q_{1/3}(⋁ᵢ m(xᵢ)) ≤ 8192·(1 + 16·√(n·⌊log₂(|L_m|+1)⌋))`
where `L_m` is the subsemilattice generated by the letters. -/
theorem joinMapAmbient_qQuery_upper {M : Type} [SemilatticeSup M]
    [DecidableEq M] (m : σ → M) :
    (qQuery (joinMap m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (Generated m) : ℝ))) := by
  have hM : Nonempty M := ⟨m (Classical.arbitrary σ)⟩
  exact qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_joinMap_ambient m).hasDualOn (by positivity)

/-- **Reading every position**: the exact cap `n`, ambient. -/
theorem joinMapAmbient_qQuery_upper_length {M : Type} [SemilatticeSup M]
    [DecidableEq M] (m : σ → M) :
    qQuery (joinMap m : (ι → σ) → M) (1 / 3) ≤ Fintype.card ι := by
  have hM : Nonempty M := ⟨m (Classical.arbitrary σ)⟩
  exact qQueryOn_le_card (read := (id : (ι → σ) → ι → σ))
    (f := (joinMap m : (ι → σ) → M))
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form, ambient join**. -/
theorem joinMapAmbient_qQuery_le_min {M : Type} [SemilatticeSup M]
    [DecidableEq M] (m : σ → M) :
    (qQuery (joinMap m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (Generated m) : ℝ)))) :=
  le_min (by exact_mod_cast joinMapAmbient_qQuery_upper_length m)
    (joinMapAmbient_qQuery_upper m)

/-- **The ambient join in the one-hot model**, at a direct factor two. -/
theorem joinMapAmbient_oneHotQQuery_le_min {M : Type} [SemilatticeSup M]
    [DecidableEq M] (m : σ → M) :
    (oneHotQQuery (joinMap m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (Generated m) : ℝ)))) := by
  have hM : Nonempty M := ⟨m (Classical.arbitrary σ)⟩
  have hcap : oneHotQQuery (joinMap m : (ι → σ) → M) (1 / 3)
      ≤ Fintype.card ι :=
    oneHotQQuery_le_card _ (by norm_num : (0 : ℝ) ≤ 1 / 3)
  refine le_min (by exact_mod_cast hcap) ?_
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (joinMap m : (ι → σ) → M)) (by norm_num)
    (joinMapAmbient_qQuery_upper m)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **The ambient semigroup product, operational**: for any (possibly
infinite) commutative idempotent semigroup `M`,
`Q_{1/3}(∏ᵢ m(xᵢ)) ≤ 8192·(1 + 16·√(n·⌊log₂(|S_m|+1)⌋))` where `S_m` is
the subsemigroup generated by the letters. -/
theorem prodMapAmb_qQuery_upper {M : Type} [DecidableEq M]
    [IsIdemCommSemigroup M] (m : σ → M) :
    (qQuery (prodMapAmb m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (GeneratedSub m) : ℝ))) := by
  have hM : Nonempty M := ⟨m (Classical.arbitrary σ)⟩
  exact qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_prodMapAmb m).hasDualOn (by positivity)

/-- **Reading every position**: the exact cap `n`, ambient semigroup. -/
theorem prodMapAmb_qQuery_upper_length {M : Type} [DecidableEq M]
    [IsIdemCommSemigroup M] (m : σ → M) :
    qQuery (prodMapAmb m : (ι → σ) → M) (1 / 3) ≤ Fintype.card ι := by
  have hM : Nonempty M := ⟨m (Classical.arbitrary σ)⟩
  exact qQueryOn_le_card (read := (id : (ι → σ) → ι → σ))
    (f := (prodMapAmb m : (ι → σ) → M))
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form, ambient semigroup**. -/
theorem prodMapAmb_qQuery_le_min {M : Type} [DecidableEq M]
    [IsIdemCommSemigroup M] (m : σ → M) :
    (qQuery (prodMapAmb m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (GeneratedSub m) : ℝ)))) :=
  le_min (by exact_mod_cast prodMapAmb_qQuery_upper_length m)
    (prodMapAmb_qQuery_upper m)

/-- **The ambient semigroup product in the one-hot model**, at a direct
factor two. -/
theorem prodMapAmb_oneHotQQuery_le_min {M : Type} [DecidableEq M]
    [IsIdemCommSemigroup M] (m : σ → M) :
    (oneHotQQuery (prodMapAmb m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (GeneratedSub m) : ℝ)))) := by
  have hM : Nonempty M := ⟨m (Classical.arbitrary σ)⟩
  have hcap : oneHotQQuery (prodMapAmb m : (ι → σ) → M) (1 / 3)
      ≤ Fintype.card ι :=
    oneHotQQuery_le_card _ (by norm_num : (0 : ℝ) ≤ 1 / 3)
  refine le_min (by exact_mod_cast hcap) ?_
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (prodMapAmb m : (ι → σ) → M)) (by norm_num)
    (prodMapAmb_qQuery_upper m)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

end Ambient

end MonoidProduct
