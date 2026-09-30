import MonoidProduct.Quantum.RTrivialApplications

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `thm:rtrivial` in the paper's displayed form

`Q_{1/3}(Prod_{M,n}) = O(min{n, √(n·d_R(M))})` for a finite `R`-trivial monoid,
with the explicit constant `73728 = 9·8192` and no additive term: when
`d_R(M) = 0` the monoid is trivial (`subsingleton_of_rDepth_eq_zero`) and the
bound is `0`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- An `R`-trivial monoid of right-ideal depth `0` is trivial. -/
theorem subsingleton_of_rDepth_eq_zero (hR : IsRTrivialMonoid M) (h : rDepth M = 0) :
    Subsingleton M := by
  have hone : ∀ m : M, m = 1 := by
    intro m
    by_contra hm
    have hss : rightIdeal m ⊂ rightIdeal (1 : M) := by
      rw [rightIdeal_one]
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun heq => hm ?_⟩
      exact hR _ _ (heq.trans (rightIdeal_one (M := M)).symm)
    have hlt := rLevel_lt_of_ssubset hss
    have hle := rLevel_le_rDepth m
    simp only [rLevel_one] at hlt
    omega
  exact ⟨fun a b => (hone a).trans (hone b).symm⟩

/-- **Theorem `thm:rtrivial`, query clause as displayed**: for a finite
`R`-trivial monoid, `Q_{1/3}(Prod_{M,n}) ≤ 73728·min{n, √(n·d_R(M))}`. -/
theorem rtrivial_qQuery_le_paper (letter : σ → M) (hR : IsRTrivialMonoid M) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ 73728 * min (n : ℝ) (Real.sqrt ((n : ℝ) * (rDepth M : ℝ))) := by
  have : Nonempty M := ⟨1⟩
  rcases Nat.eq_zero_or_pos (rDepth M) with h0 | hpos
  · have := subsingleton_of_rDepth_eq_zero hR h0
    have hz : qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) = 0 :=
      qQueryOn_const_eq_zero id (c := 1) (fun _ => Subsingleton.elim _ _) (by norm_num)
    rw [hz, Nat.cast_zero]
    positivity
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h := rtrivial_qQuery_upper_length (n := 0) letter
    have : qQuery (fun x : Fin 0 → σ => wordProd letter x) (1 / 3) = 0 := by omega
    rw [this]; simp
  have hlen : (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ) ≤ n := by
    exact_mod_cast rtrivial_qQuery_upper_length letter
  have hup := rtrivial_qQuery_upper letter hR (n := n)
  have hc : uniformExtractionConstant = (8192 : ℝ) := by
    simp [uniformExtractionConstant]
  rw [hc] at hup
  set m : ℕ := min n (rDepth M) with hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := le_min hn hpos
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * m) := by
    rw [Real.one_le_sqrt]; nlinarith
  have hsle : Real.sqrt ((n : ℝ) * m) ≤ Real.sqrt ((n : ℝ) * (rDepth M : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have : (m : ℝ) ≤ rDepth M := by exact_mod_cast min_le_right _ _
    nlinarith
  have hsn : Real.sqrt ((n : ℝ) * m) ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (m : ℝ) ≤ n := by exact_mod_cast min_le_left _ _
    nlinarith
  have hmin : Real.sqrt ((n : ℝ) * m)
      ≤ min (n : ℝ) (Real.sqrt ((n : ℝ) * (rDepth M : ℝ))) := le_min hsn hsle
  nlinarith

end MonoidProduct
