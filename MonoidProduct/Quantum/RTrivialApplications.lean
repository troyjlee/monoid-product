import MonoidProduct.Aperiodic.RTrivial
import MonoidProduct.Capped.RTrivial
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.OneHotTransport
import QuantumQueryComplexity.Quantum.Plurality
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `R`-trivial products: the operational quantum-query endpoints

`monoid.tex` Theorem `thm:rtrivial` and Proposition `prop:jtrivial-log-fails`
at the level of `Q_{1/3}`:

* `rtrivial_qQuery_le_min` : for a finite `R`-trivial monoid,
  `Q_{1/3}(Prod_{M,n}) ≤ min{n, 8192·(1 + 8√(n·min{n, d_R(M)}))}`, uniformly
  in the letter alphabet, from the prefix-scan certificate
  (`hasDual_wordProd_of_isRTrivial`) through the cardinality-free extraction;
* `rtrivial_promise_qQuery_upper` : the promise form at `8192·(1 + 8√(n·C))`
  for any bound `C` on the prefix changes over the promise;
* `rtrivial_oneHotQQuery_upper` : the one-hot form at a factor two;
* `capped_binary_qQuery_lower` : the capped counter `M_K` on binary inputs,
  `(7/1376)·√(n·min{n, K})/4 ≤ Q_{1/3}` — with `d_R(M_K) = K`
  (`Capped.rDepth_eq`) this is the sharpness of the `d_R` dependence and the
  failure of any uniform `Õ(√(n·log|M|))` bound for `𝓙`-trivial monoids.

An application file importing both hierarchies; imported by `MonoidProduct.lean`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Upper

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] {n : ℕ} (letter : σ → M)

/-- **Theorem `thm:rtrivial`, operational**:
`Q_{1/3}(Prod_{M,n}) ≤ 8192·(1 + 8√(n·min{n, d_R(M)}))`. -/
theorem rtrivial_qQuery_upper (hR : IsRTrivialMonoid M) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (rDepth M) : ℕ) : ℝ))) := by
  haveI : Nonempty M := ⟨1⟩
  exact qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_wordProd_of_isRTrivial letter hR).hasDualOn (by positivity)

/-- **Reading every letter**: the exact cap `n`. -/
theorem rtrivial_qQuery_upper_length :
    qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) ≤ n := by
  haveI : Nonempty M := ⟨1⟩
  have h := qQueryOn_le_card (read := (id : (Fin n → σ) → Fin n → σ))
    (f := fun x : Fin n → σ => wordProd letter x)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The unabsorbed minimum**:
`Q_{1/3}(Prod_{M,n}) ≤ min{n, 8192·(1 + 8√(n·min{n, d_R(M)}))}`. -/
theorem rtrivial_qQuery_le_min (hR : IsRTrivialMonoid M) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (rDepth M) : ℕ) : ℝ)))) :=
  le_min (by exact_mod_cast rtrivial_qQuery_upper_length letter)
    (rtrivial_qQuery_upper letter hR)

/-- **The promise form**: `Q_{1/3} ≤ 8192·(1 + 8√(n·C))` for any bound `C` on
the prefix changes over the promised inputs (the paper's `C_𝒟`). -/
theorem rtrivial_promise_qQuery_upper {X : Type} [Fintype X] [DecidableEq X]
    (read : X → Fin n → σ) {C : ℕ}
    (hC : ∀ x, changeCount (1 : M) (mulStep letter) (read x) ≤ C) :
    (qQueryOn read (fun x => wordProd letter (read x)) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + 8 * Real.sqrt ((n : ℝ) * (C : ℝ))) := by
  haveI : Nonempty M := ⟨1⟩
  exact qQueryOn_third_le_of_hasDualOn_uniform
    (hasDualOn_wordProd_of_changeCount letter read hC) (by positivity)

/-- **The one-hot form**, at a direct factor two. -/
theorem rtrivial_oneHotQQuery_upper (hR : IsRTrivialMonoid M) :
    (oneHotQQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ 2 * (uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (rDepth M) : ℕ) : ℝ)))) := by
  haveI : Nonempty M := ⟨1⟩
  exact oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (fun x : Fin n → σ => wordProd letter x)) (by norm_num)
    (rtrivial_qQuery_upper letter hR)

end Upper

section Lower

variable {k n : ℕ}

/-- **Proposition `prop:jtrivial-log-fails`, operational**: the capped
counter on binary inputs needs `(7/1376)·√(n·min{n, K})/4` queries, through
the plurality finite-output extraction at `read = id`. -/
theorem capped_binary_qQuery_lower (hk : 0 < k) [Nonempty (Fin n)] :
    (7 / 1376 : ℝ) * (Real.sqrt ((n : ℝ) * ((min n k : ℕ) : ℝ)) / 4)
      ≤ (qQuery (fun x : Fin n → Bool => ∏ i, (if x i then Capped.gen else (1 : Capped k)))
          (1 / 3) : ℝ) := by
  haveI : Nonempty (Capped k) := ⟨1⟩
  have hpar := mul_advPMOn_le_qQueryOn_third_finiteOutput
    (read := (id : (Fin n → Bool) → Fin n → Bool))
    (f := fun x : Fin n → Bool => ∏ i, (if x i then Capped.gen else (1 : Capped k)))
    (fun x y h => by rw [show x = y from h])
  have hid : advPMOn (id : (Fin n → Bool) → Fin n → Bool)
      (fun x : Fin n → Bool => ∏ i, (if x i then Capped.gen else (1 : Capped k)))
      = advPM (fun x : Fin n → Bool => ∏ i, (if x i then Capped.gen else (1 : Capped k))) :=
    rfl
  rw [hid] at hpar
  exact (mul_le_mul_of_nonneg_left (Capped.sqrt_le_advPM_binary' hk) (by norm_num)).trans hpar

end Lower

end MonoidProduct
