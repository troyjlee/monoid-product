import MonoidProduct.Ordered.BetaSampling
import MonoidProduct.Ordered.RankDoublingLemma

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option synthInstance.maxSize 4096

/-!
# Acceptance: the sampling and rank-doubling lemmas

Statement pins for the paper's `lem:beta-sampling` and `lem:beta-rank-doubling` as standalone
lemmas (`Ordered/BetaSampling.lean`, `Ordered/RankDoublingLemma.lean`).  Like the library's
other pins, this file exists to be broken: a refactor that changes a statement fails here.

1. **`lem:beta-sampling`**, in its existential form (`beta_sampling`) and with the construction
   named (`beta_sampling_explicit`): records of at most `b` positions, a dual of cost
   `768·b·T·√h·(L+1)^{3/2}` for every seed, and `eq:beta-small-mass` with probability at least
   `1 − 1/(100·2^L)`.
2. **`lem:beta-rank-doubling`** (`rank_doubling`): from a rank-`r` family on every dyadic
   interval of `[2^L]` with arbitrary input-independent seed weights, failure mass at most
   `(1/100)^(L+2)` and duals of cost `A·√(2^j)`, a rank-`2r` family with the same failure mass
   and duals of cost `5760·b·A·L⁴·√(2^j)`.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

section Lemmas

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable [DecidableLE M] (letter : σ → M)

/-! ## 1. `lem:beta-sampling` -/

omit [DecidableEq M] in
/-- **`lem:beta-sampling`, existential form.** -/
theorem acceptance_beta_sampling (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    (hb1 : 1 ≤ b) {n L : ℕ} (hL : 1 ≤ L) (hbN : b ≤ 2 ^ L) {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] {ν : Ω → ℝ} (hν : IsWeight ν) (cand : Ω → (Fin n → σ) → Record n σ)
    (hcT : ∀ ω x, (cand ω x).Truthful x) {T : ℝ} (hT : 0 ≤ T) (hc : ∀ ω, HasDual (cand ω) T)
    {h : ℕ} (hh1 : 1 ≤ h) (hhN : h ≤ 2 ^ L) :
    ∃ (Θ : Type) (_ : Fintype Θ) (_ : DecidableEq Θ) (θw : Θ → ℝ)
      (K : Θ → (Fin n → σ) → Record n σ),
      IsWeight θw
      ∧ (∀ θ x, (K θ x).Truthful x ∧ (K θ x).supp.card ≤ b)
      ∧ (∀ θ, HasDual (K θ) (768 * b * T * Real.sqrt h * ((L + 1) * Real.sqrt (L + 1))))
      ∧ ∀ x : Fin n → σ, ∑ θ, θw θ
          * (if 1 / (2 * (h : ℝ)) ≤ ∑ U, pushW ν (fun ω => cand ω x) U
              * (if U.prod letter ≤ (K θ x).prod letter then 0 else 1)
            then 1 else 0)
        ≤ 1 / (100 * 2 ^ L) :=
  beta_sampling letter hst hb hb1 hL hbN hν cand hcT hT hc hh1 hhN

/-- **`lem:beta-sampling`, with the construction named.** -/
theorem acceptance_beta_sampling_explicit (hst : IsStableOrder M) {b : ℕ}
    (hb : IsBreadthBound letter b)
    (hb1 : 1 ≤ b) {n L : ℕ} (hL : 1 ≤ L) (hbN : b ≤ 2 ^ L) {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] {ν : Ω → ℝ} (hν : IsWeight ν) (cand : Ω → (Fin n → σ) → Record n σ)
    (hcT : ∀ ω x, (cand ω x).Truthful x) {T : ℝ} (hT : 0 ≤ T) (hc : ∀ ω, HasDual (cand ω) T)
    {h : ℕ} (hh1 : 1 ≤ h) (hhN : h ≤ 2 ^ L) :
    (∀ (θ : BetaSeed Ω b L h) (x : Fin n → σ), (betaSampleK letter b L h cand θ x).Truthful x
        ∧ (betaSampleK letter b L h cand θ x).supp.card ≤ b)
    ∧ (∀ θ : BetaSeed Ω b L h, HasDual (betaSampleK letter b L h cand θ)
        (768 * b * T * Real.sqrt h * ((L + 1) * Real.sqrt (L + 1))))
    ∧ ∀ x : Fin n → σ, ∑ θ : BetaSeed Ω b L h, tupleW (tupleW (tupleW ν)) θ
        * (if 1 / (2 * (h : ℝ)) ≤ ∑ U, pushW ν (fun ω => cand ω x) U
            * (if U.prod letter ≤ (betaSampleK letter b L h cand θ x).prod letter then 0 else 1)
          then 1 else 0)
      ≤ 1 / (100 * 2 ^ L) :=
  beta_sampling_explicit letter hst hb hb1 hL hbN hν cand hcT hT hc hh1 hhN

/-! ## 2. `lem:beta-rank-doubling` -/

variable (b : ℕ)

open Classical in
/-- **`lem:beta-rank-doubling`.** -/
theorem acceptance_rank_doubling (hst : IsStableOrder M) (hb : IsBreadthBound letter b)
    (hb1 : 1 ≤ b)
    {L r : ℕ} (hL : 1 ≤ L) (hr : 1 ≤ r) {A : ℝ} (hA : 1 ≤ A)
    {Ω : ℕ → ℕ → Type} [∀ j q, Fintype (Ω j q)] [∀ j q, DecidableEq (Ω j q)]
    [∀ j q, Nonempty (Ω j q)] (w : ∀ j q, Ω j q → ℝ) (hw : ∀ j q, IsWeight (w j q))
    (F : ∀ j q, Ω j q → (Fin (2 ^ L) → σ) → Record (2 ^ L) σ)
    (hrec : ∀ j q, (q + 1) * 2 ^ j ≤ 2 ^ L → ∀ ω x,
      (F j q ω x).Truthful x ∧ (F j q ω x).supp ⊆ ivl j q ∧ (F j q ω x).supp.card ≤ b)
    (hfail : ∀ j q, (q + 1) * 2 ^ j ≤ 2 ^ L → ∀ x,
      ∑ ω, w j q ω * (if IsSummary letter x b r j q (F j q ω x) then 0 else 1)
        ≤ (1 / 100) ^ (L + 2))
    (hdual : ∀ j q, (q + 1) * 2 ^ j ≤ 2 ^ L → ∀ ω,
      HasDual (F j q ω) (A * Real.sqrt (2 ^ j))) :
    ∃ (Ω' : ℕ → ℕ → Type) (_ : ∀ j q, Fintype (Ω' j q)) (_ : ∀ j q, DecidableEq (Ω' j q))
      (_ : ∀ j q, Nonempty (Ω' j q)) (w' : ∀ j q, Ω' j q → ℝ)
      (F' : ∀ j q, Ω' j q → (Fin (2 ^ L) → σ) → Record (2 ^ L) σ),
      (∀ j q, IsWeight (w' j q)) ∧ ∀ j q, (q + 1) * 2 ^ j ≤ 2 ^ L →
        (∀ ω x, (F' j q ω x).Truthful x ∧ (F' j q ω x).supp ⊆ ivl j q
          ∧ (F' j q ω x).supp.card ≤ b)
        ∧ (∀ x, ∑ ω, w' j q ω
            * (if IsSummary letter x b (2 * r) j q (F' j q ω x) then 0 else 1)
            ≤ (1 / 100) ^ (L + 2))
        ∧ ∀ ω, HasDual (F' j q ω) (5760 * b * A * L ^ 4 * Real.sqrt (2 ^ j)) :=
  rank_doubling letter b hst hb hb1 hL hr hA w hw F hrec hfail hdual

end Lemmas

end MonoidProduct
