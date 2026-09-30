import MonoidProduct.Aperiodic.InfixCost
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Infix search with the paper's recursive hypothesis

`lem:infix` assumes equality tests `P_s` only for the values `s` with `MrM ⊆ MsM`.
`hasDual_badInfixFor_strict` asks instead for every strict parent of `m`, a larger
family (every `(a, r, b) ∈ G(m)` has `MmM ⊊ MrM`, `twoIdeal_lt_of_mem_setG`).
`hasDual_badInfixFor_paper` gives the statement with exactly the paper's family: each
split `r = pq` asks only for `s` with `p ∈ Ms` or `q ∈ sM` (`hasDual_markedAt_above`),
and all of these satisfy `MrM ⊆ MsM`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- A left factor's left-ideal parents lie above the product. -/
lemma twoIdeal_mul_subset_of_mem_leftAbove {p q s : M} (hs : s ∈ leftAbove p) :
    twoIdeal (p * q) ⊆ twoIdeal s := by
  obtain ⟨t, rfl⟩ := mem_leftIdeal.1 (mem_leftAbove.1 hs)
  exact twoIdeal_subset_of_mem (mem_twoIdeal.2 ⟨t, q, by simp [mul_assoc]⟩)

/-- A right factor's right-ideal parents lie above the product. -/
lemma twoIdeal_mul_subset_of_mem_rightAbove {p q s : M} (hs : s ∈ rightAbove q) :
    twoIdeal (p * q) ⊆ twoIdeal s := by
  obtain ⟨t, rfl⟩ := mem_rightIdeal.1 (mem_rightAbove.1 hs)
  exact twoIdeal_subset_of_mem (mem_twoIdeal.2 ⟨p, t, by simp [mul_assoc]⟩)

/-- **Infix search (`lem:infix`), with the paper's hypothesis**: for `(a, r, b) ∈ G(m)`, if
every `P_s` with `MrM ⊆ MsM` has an all-pairs dual of cost `B·√ℓ` at every length
`ℓ ≤ n`, then event (W) for the triple `(a, r, b)` has an all-pairs dual of cost
`infixCost n M B = O(|M|^{3/2}·B·√n·log^{3/2}(n+1))`, for every `n`. -/
theorem hasDual_badInfixFor_paper (letter : σ → M) {m a r b : M}
    (hG : (a, r, b) ∈ setG m) {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hrec : ∀ s : M, twoIdeal r ⊆ twoIdeal s → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (fun x : Fin n → σ => badInfixFor letter a r b x)
      (infixCost n M B) :=
  hasDual_badInfixFor_of_markedAt letter hB fun _ _ hpq _ _ hc =>
    hasDual_markedAt_above letter hG hpq hc hB
      (fun s hs => hrec s (hpq ▸ twoIdeal_mul_subset_of_mem_leftAbove hs))
      (fun s hs => hrec s (hpq ▸ twoIdeal_mul_subset_of_mem_rightAbove hs))

end

end MonoidProduct
