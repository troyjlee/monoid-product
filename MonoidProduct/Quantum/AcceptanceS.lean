import MonoidProduct.Quantum.DivisionApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Division transports: acceptance test

The statement pins for the certificate-level division transports.  Like the
other pins,
this file exists to be broken; it sits outside the `QuantumQueryComplexity.Quantum`
aggregate and **CI must build it explicitly**:
`lake build QuantumQueryComplexity.Quantum.AcceptanceS`.

Pinned, with every convention literal:

1. **the classical certificates** — the generic factor-two transport
   `hasDual_wordProd_of_section`, its `UT_k(𝔹)` instantiation at
   `16·√(n·min{n, C(k,2)})`, the unconditional 𝓙-trivial certificate at
   `k = τ(M)`, and the previously missing classical `advPM` corollary —
   no quantum import in their proofs;
2. **the single-extraction native minimum** at the literal `8192` —
   the factor two sits on the certificate, not the compiled algorithm,
   so the additive constant is paid once (the query-side route
   `jtrivial_qQuery_le`/`jtrivial_qQuery_le_min` in
   `Quantum/Applications.lean` is retained unchanged at `2·8192`);
3. **the one-hot minimum** at `16384` with the exact read-all cap `n`.

Manual axiom checks:

    #print axioms MonoidProduct.jtrivial_cert_qQuery_le_min
      → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.hasDual_wordProd_jtrivial
      → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
open QuantumQueryComplexity
namespace AcceptanceS

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] {k n : ℕ}

/-! ## 1. The classical certificates -/

theorem dual_division_pinned (hn : 1 ≤ n)
    (T : Subsemigroup (BUT k)) (φ : T →ₙ* M) (ψ : M → T)
    (hsec : ∀ m, φ (ψ m) = m) :
    HasDual (fun w : Fin n → M => wordProd (id : M → M) w)
      (16 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ))) :=
  hasDual_wordProd_of_but_division hn T φ ψ hsec

theorem dual_jtrivial_pinned (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    HasDual (fun w : Fin n → M => wordProd (id : M → M) w)
      (16 * Real.sqrt ((n : ℝ)
        * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))) :=
  hasDual_wordProd_jtrivial hJ hn

theorem advPM_jtrivial_pinned (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    advPM (fun w : Fin n → M => wordProd (id : M → M) w)
      ≤ 16 * Real.sqrt ((n : ℝ)
        * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ)) :=
  advPM_wordProd_le_of_jtrivial hJ hn

/-! ## 2. The single-extraction native minimum -/

theorem native_min_pinned (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (8192
          * (1 + 16 * Real.sqrt ((n : ℝ)
            * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ)))) := by
  have h := jtrivial_cert_qQuery_le_min hJ hn
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

/-! ## 3. The one-hot minimum -/

theorem oneHot_min_pinned (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    (oneHotQQuery (fun w : Fin n → M => wordProd (id : M → M) w)
        (1 / 3) : ℝ)
      ≤ min (n : ℝ) (16384
          * (1 + 16 * Real.sqrt ((n : ℝ)
            * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ)))) :=
  jtrivial_cert_oneHotQQuery_le_min hJ hn

end AcceptanceS

end MonoidProduct
