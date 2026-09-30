import MonoidProduct.Aperiodic.Division
import QuantumQueryComplexity.Quantum.UniformHasDual
import MonoidProduct.Quantum.OneHotApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Division transports: the single-extraction operational endpoints

The certificate-level division transport (`Aperiodic/Division.lean`)
feeds the uniform extraction **once**, replacing the query-side route
`Q(Prod_M) ≤ 2·Q(Prod_{UT_k(𝔹)}) ≤ 2·8192·(1 + 8·√(n·min{n,C(k,2)}))`
(`jtrivial_qQuery_le`, `Quantum/Applications.lean` — retained unchanged)
by

    Q_{1/3}(Prod_{M,n}) ≤ 8192·(1 + 16·√(n·min{n, C(k,2)})),

for every finite monoid `M ≺ UT_k(𝔹)`, and unconditionally at
`k = τ(M)` for every finite 𝓙-trivial monoid; the factor two now sits on
the certificate (`HasDual.postcomp_of_determined`), not on the compiled
algorithm, so the additive `8192` is paid once.  One-hot forms at a
direct factor two (`16384`), with the **exact** read-all cap `n` in both
models.

This file sits outside the `QuantumQueryComplexity.Quantum` aggregate: it is an
application layer importing both the classical division transport and
the quantum model, built by CI as an explicit cross-stream target.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] {k n : ℕ}

/-- **Reading every letter**: the exact cap `Q_{1/3}(Prod_{M,n}) ≤ n` for
any finite monoid. -/
theorem wordProd_qQuery_upper_length :
    qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) ≤ n := by
  have h := qQueryOn_le_card
    (read := (id : (Fin n → M) → Fin n → M))
    (f := fun w : Fin n → M => wordProd (id : M → M) w)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **Reading every letter, one-hot**: the exact cap `n` — direct, not
through simulation. -/
theorem wordProd_oneHotQQuery_upper_length :
    oneHotQQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3)
      ≤ n := by
  have h := oneHotQQuery_le_card
    (fun w : Fin n → M => wordProd (id : M → M) w)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The single-extraction bound from a supplied division witness**:
`M ≺ UT_k(𝔹)` gives `Q_{1/3}(Prod_{M,n}) ≤ 8192·(1 + 16·√(n·min{n,C(k,2)}))`. -/
theorem but_division_cert_qQuery_upper (hn : 1 ≤ n)
    (T : Subsemigroup (BUT k)) (φ : T →ₙ* M) (ψ : M → T)
    (hsec : ∀ m, φ (ψ m) = m) :
    (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((n : ℝ)
            * ((min n (k.choose 2) : ℕ) : ℝ))) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_wordProd_of_but_division hn T φ ψ hsec).hasDualOn
    (by positivity)

/-- **The unconditional 𝓙-trivial bound, single extraction**:
`Q_{1/3}(Prod_{M,n}) ≤ 8192·(1 + 16·√(n·min{n, C(τ(M),2)}))`. -/
theorem jtrivial_cert_qQuery_upper (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((n : ℝ)
            * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_wordProd_jtrivial hJ hn).hasDualOn (by positivity)

/-- **The 𝓙-trivial unabsorbed minimum, single extraction**:
`Q_{1/3}(Prod_{M,n}) ≤ min{n, 8192·(1 + 16·√(n·min{n, C(τ(M),2)}))}`. -/
theorem jtrivial_cert_qQuery_le_min (hJ : IsJTrivialMonoid M)
    (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (uniformExtractionConstant
          * (1 + 16 * Real.sqrt ((n : ℝ)
            * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ)))) :=
  le_min (by exact_mod_cast wordProd_qQuery_upper_length)
    (jtrivial_cert_qQuery_upper hJ hn)

/-- **The 𝓙-trivial bound in the one-hot model**, at a direct factor two:
`Q^{1-hot}_{1/3}(Prod_{M,n}) ≤ min{n, 16384·(1 + 16·√(n·min{n, C(τ(M),2)}))}`. -/
theorem jtrivial_cert_oneHotQQuery_le_min (hJ : IsJTrivialMonoid M)
    (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd (id : M → M) w)
        (1 / 3) : ℝ)
      ≤ min (n : ℝ) (16384
          * (1 + 16 * Real.sqrt ((n : ℝ)
            * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ)))) := by
  refine le_min (by exact_mod_cast wordProd_oneHotQQuery_upper_length) ?_
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (fun w : Fin n → M => wordProd (id : M → M) w)) (by norm_num)
    (jtrivial_cert_qQuery_upper hJ hn)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

end MonoidProduct
