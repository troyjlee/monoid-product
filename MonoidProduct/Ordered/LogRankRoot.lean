import MonoidProduct.Ordered.Root
import MonoidProduct.Ordered.LogRankCorrect

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Root extraction from an arbitrary seeded summary

`Root.lean` extracts the product-and-core algorithm from the seeded summary of the
padded word used for the linear-exponent theorem (`thm:ordered-beta-product`).  The
argument only uses three properties of the seed family: every seed's function has a dual
of cost `A`, the seeds are uniform, and the failure mass at the root is at most `1/100`.
`exists_root_alg_of` states it in that generality, and `qQuery_wordProd_le_root_of`
derives the `Q_{1/10}` bound `8192·(1 + A)`; the rank-doubling stage summaries of the
quasipolynomial theorem (`thm:ordered-beta-log-product`) plug in through
`summary2_correct`.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

section LogRankRoot

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable [DecidableLE M] (letter : σ → M)
variable (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
include hst hb

open Classical in
/-- **The product-and-core algorithm from any seeded summary** with duals of cost `A` and
root failure mass at most `1/100`: at most `8192·(1 + A)` queries, a good record with
probability at least `9/10`. -/
theorem exists_root_alg_of {n L : ℕ} (hn : n ≤ 2 ^ L)
    {Ω' : Type} [Fintype Ω'] [DecidableEq Ω'] [Nonempty Ω']
    (F : Ω' → (Fin (2 ^ L) → Option σ) → Record (2 ^ L) (Option σ)) {A : ℝ} (hA : 0 ≤ A)
    (hdual : ∀ ω, HasDual (F ω) A)
    (hcorr : ∀ x : Fin n → σ, ∑ ω, unifW Ω' ω * (if IsSummary (letterOpt letter) (pad (L := L) x)
      b b L 0 (F ω (pad (L := L) x)) then 0 else 1) ≤ 1 / 100) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ L) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ uniformExtractionConstant * (1 + A)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  have hb' : IsBreadthBound (letterOpt letter) b := isBreadthBound_letterOpt letter hb
  -- every seed's function has a dual through the padding
  have hdual' : ∀ ω : Ω', HasDual (fun x : Fin n → σ => F ω (pad (L := L) x)) A := fun ω =>
    HasDual.restrict (e := Fin.castLE hn) (castLE_injective' hn) (Φ := fun x => pad (L := L) x)
      (fun x y i => by rw [pad_castLE hn, pad_castLE hn, Option.some_inj])
      (fun x y j hj => by
        have hlt : ¬ (j : ℕ) < n := fun hlt => hj ⟨j, hlt⟩ (Fin.ext rfl)
        rw [pad_of_not_lt x j hlt, pad_of_not_lt y j hlt])
      (hdual ω)
  -- one algorithm per seed
  have hex : ∀ ω : Ω', ∃ q ∈ QueryCounts (X := Fin n → σ) id
      (fun x => F ω (pad (L := L) x)) (1 / 16),
      (q : ℝ) ≤ uniformExtractionConstant * (1 + A) := by
    intro ω
    obtain ⟨K, hK, Pd, hPd⟩ := (hdual' ω).hasDualOn
    let _ := hK
    exact exists_algorithm_of_dualPairOn_uniform Pd hPd hA
  choose q hq hqle using hex
  choose W hW hW' Alg hAlg using hq
  let _ : ∀ ω, Fintype (W ω) := hW
  let _ : ∀ ω, DecidableEq (W ω) := hW'
  -- the mixture at a common query count
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, ⌊uniformExtractionConstant * (1 + A)⌋₊ = Q := ⟨_, rfl⟩
  have hQ : ∀ ω, q ω ≤ Q := fun ω => hQdef ▸ Nat.le_floor (hqle ω)
  obtain ⟨W', hW'1, hW'2, B, hB⟩ := exists_mixture (unifW Ω')
    (isWeight_unifW _).nonneg (isWeight_unifW _).sum_one q Q hQ Alg
  refine ⟨W', hW'1, hW'2, B, Q, hQdef ▸ Nat.floor_le (mul_nonneg
    (by unfold uniformExtractionConstant; norm_num) (by linarith)), fun x => ?_⟩
  -- correct seeds give good records
  have hgood : ∀ ω, IsSummary (letterOpt letter) (pad (L := L) x) b b L 0 (F ω (pad (L := L) x)) →
      GoodRec letter b x (F ω (pad (L := L) x)) := by
    intro ω hS
    refine ⟨hS.truthful, hS.card_le, ?_⟩
    rw [prod_eq_wordProd_of_isSummary (letterOpt letter) hst hb' hS
      (fun i => by rw [mem_ivl]; simp), wordProd_pad letter hn]
  have hfail := hcorr x
  have h1 : (15 / 16 : ℝ) * (1 - ∑ ω, unifW Ω' ω * (if IsSummary (letterOpt letter)
        (pad (L := L) x) b b L 0 (F ω (pad (L := L) x)) then (0 : ℝ) else 1))
      = ∑ ω, unifW Ω' ω * (if IsSummary (letterOpt letter) (pad (L := L) x) b b L 0
          (F ω (pad (L := L) x)) then (15 / 16 : ℝ) else 0) := by
    have e : (1 : ℝ) - ∑ ω, unifW Ω' ω * (if IsSummary (letterOpt letter)
          (pad (L := L) x) b b L 0 (F ω (pad (L := L) x)) then (0 : ℝ) else 1)
        = ∑ ω, (unifW Ω' ω - unifW Ω' ω * (if IsSummary (letterOpt letter)
          (pad (L := L) x) b b L 0 (F ω (pad (L := L) x)) then (0 : ℝ) else 1)) := by
      rw [Finset.sum_sub_distrib, (isWeight_unifW Ω').sum_one]
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  calc (9 / 10 : ℝ)
      ≤ (15 / 16 : ℝ) * (1 - ∑ ω, unifW Ω' ω * (if IsSummary (letterOpt letter)
          (pad (L := L) x) b b L 0 (F ω (pad (L := L) x)) then (0 : ℝ) else 1)) := by linarith
    _ = ∑ ω, unifW Ω' ω * (if IsSummary (letterOpt letter) (pad (L := L) x) b b L 0
          (F ω (pad (L := L) x)) then (15 / 16 : ℝ) else 0) := h1
    _ ≤ ∑ ω, unifW Ω' ω
          * ∑ K ∈ Finset.univ.filter (GoodRec letter b x), (Alg ω).prob x (q ω) K := by
        refine Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left ?_ ((isWeight_unifW _).nonneg ω)
        split_ifs with hS
        · calc (15 / 16 : ℝ) = 1 - 1 / 16 := by norm_num
            _ ≤ (Alg ω).prob x (q ω) (F ω (pad (L := L) x)) := hAlg ω x
            _ ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), (Alg ω).prob x (q ω) K :=
                Finset.single_le_sum (f := fun K => (Alg ω).prob x (q ω) K)
                  (fun K _ => (Alg ω).prob_nonneg x (q ω) K)
                  (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgood ω hS⟩)
        · exact Finset.sum_nonneg fun K _ => (Alg ω).prob_nonneg _ _ _
    _ = ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
        simp only [hB, Finset.mul_sum]
        rw [Finset.sum_comm]

open Classical in
/-- **The `Q_{1/10}` bound from any seeded summary**: `8192·(1 + A)`. -/
theorem qQuery_wordProd_le_root_of {n L : ℕ} (hn : n ≤ 2 ^ L)
    {Ω' : Type} [Fintype Ω'] [DecidableEq Ω'] [Nonempty Ω']
    (F : Ω' → (Fin (2 ^ L) → Option σ) → Record (2 ^ L) (Option σ)) {A : ℝ} (hA : 0 ≤ A)
    (hdual : ∀ ω, HasDual (F ω) A)
    (hcorr : ∀ x : Fin n → σ, ∑ ω, unifW Ω' ω * (if IsSummary (letterOpt letter) (pad (L := L) x)
      b b L 0 (F ω (pad (L := L) x)) then 0 else 1) ≤ 1 / 100) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ uniformExtractionConstant * (1 + A) := by
  obtain ⟨W, hW, hW', B, Q, hQ, hgood⟩ := exists_root_alg_of letter hst hb hn F hA hdual hcorr
  let _ := hW
  let _ := hW'
  have hcomp : ComputesWithErrorOn (B.postcomp fun K => K.prod (letterOpt letter)) Q id
      (fun x : Fin n → σ => wordProd letter x) (1 / 10) := by
    intro x
    refine le_trans ?_ (sum_prob_le_prob_postcomp B _ x Q
      (Finset.univ.filter (GoodRec letter b x)) (wordProd letter x)
      fun K hK => (Finset.mem_filter.1 hK).2.2.2)
    linarith [hgood x]
  have := qQueryOn_le hcomp
  exact le_trans (by exact_mod_cast this) hQ

end LogRankRoot

end MonoidProduct
