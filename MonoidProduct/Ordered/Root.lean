import MonoidProduct.Ordered.Cost
import QuantumQueryComplexity.Quantum.Mixture
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.Postcomp
import QuantumQueryComplexity.Promise.HasDual
import QuantumQueryComplexity.Quantum.ReadAll

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# The root algorithm (structural half)

A word of length `n ≤ 2^L` is padded to length `2^L` over the alphabet
`Option σ`, where `none` reads as the identity (`pad`, `wordProd_pad`).  For every
root seed `ω`, the rank-`b` summary of the padded word is a function of the
original word with a dual of cost `costA b P b L` (`HasDual.restrict` along the
padding), so the uniform extraction gives one quantum algorithm per seed with
error `1/16` in at most `8192·(1 + costA)` queries.  The uniform finite mixture
of these algorithms (`exists_mixture`) returns, with probability at least
`(99/100)·(15/16) > 9/10`, a record that is truthful for the padded word, has at
most `b` positions and has the word's product (`exists_root_alg`).  Reading the
product off the record is free postprocessing (`qQuery_wordProd_le_root`).

Only the merger parameters are still abstract here: `GoodParams` and the rounds/
proposal bounds are discharged numerically in `Quantum/OrderedApplications.lean`.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity

section Root

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M)

/-! ## Padding -/

/-- Pad a word to length `2^L` with the identity letter `none`. -/
def pad {n L : ℕ} (x : Fin n → σ) : Fin (2 ^ L) → Option σ :=
  fun j => if h : (j : ℕ) < n then some (x ⟨j, h⟩) else none

lemma pad_castLE {n L : ℕ} (hn : n ≤ 2 ^ L) (x : Fin n → σ) (i : Fin n) :
    pad (L := L) x (Fin.castLE hn i) = some (x i) := by
  unfold pad
  rw [dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
  rfl

lemma pad_of_not_lt {n L : ℕ} (x : Fin n → σ) (j : Fin (2 ^ L)) (hj : ¬ (j : ℕ) < n) :
    pad x j = none := by
  unfold pad
  rw [dif_neg hj]

lemma castLE_injective' {n L : ℕ} (hn : n ≤ 2 ^ L) : Function.Injective (Fin.castLE hn) :=
  fun i j h => Fin.ext (by simpa [Fin.val_castLE] using congrArg Fin.val h)

/-- **Identity padding preserves the product.** -/
theorem wordProd_pad {n L : ℕ} (hn : n ≤ 2 ^ L) (x : Fin n → σ) :
    wordProd (letterOpt letter) (pad (L := L) x) = wordProd letter x := by
  unfold wordProd
  have h := orderedProd_comp_orderEmb (Fin.castLEOrderEmb hn)
    (fun j => letterOpt letter (pad (L := L) x j)) (fun j hj => by
      have hlt : ¬ (j : ℕ) < n := fun hlt => hj ⟨⟨j, hlt⟩, Fin.ext rfl⟩
      show letterOpt letter (pad x j) = 1
      rw [pad_of_not_lt x j hlt]
      rfl)
  rw [← h]
  congr 1
  funext i
  show letterOpt letter (pad (L := L) x (Fin.castLE hn i)) = letter (x i)
  rw [pad_castLE hn]
  rfl

/-! ## Good records -/

/-- **A good record** for the word `x`: truthful for the padded word, at most `b` positions,
and the word's product. -/
def GoodRec (b : ℕ) {n L : ℕ} (x : Fin n → σ) (K : Record (2 ^ L) (Option σ)) : Prop :=
  K.Truthful (pad (L := L) x) ∧ K.supp.card ≤ b ∧ K.prod (letterOpt letter) = wordProd letter x

/-- **A good record is a core of at most `b` original positions.** -/
theorem GoodRec.exists_core {b n L : ℕ} (hn : n ≤ 2 ^ L) {x : Fin n → σ}
    {K : Record (2 ^ L) (Option σ)} (h : GoodRec letter b x K) :
    ∃ D : Finset (Fin n), D.card ≤ b ∧ IsCore letter x D := by
  obtain ⟨htr, hcard, hprod⟩ := h
  refine ⟨Finset.univ.filter fun i => Fin.castLE hn i ∈ K.supp, ?_, ?_⟩
  · refine le_trans (Finset.card_le_card_of_injOn (Fin.castLE hn) ?_ ?_) hcard
    · intro i hi
      exact (Finset.mem_filter.1 hi).2
    · intro i _ j _ hij
      exact castLE_injective' hn hij
  · unfold IsCore
    rw [← hprod, Record.prod_of_truthful (letterOpt letter) htr,
      subwordProd_eq_orderedProd_maskWord, subwordProd_eq_orderedProd_maskWord]
    have h := orderedProd_comp_orderEmb (Fin.castLEOrderEmb hn)
      (maskWord (letterOpt letter) (pad (L := L) x) K.supp) (fun j hj => by
        have hlt : ¬ (j : ℕ) < n := fun hlt => hj ⟨⟨j, hlt⟩, Fin.ext rfl⟩
        unfold maskWord
        split_ifs
        · rw [pad_of_not_lt x j hlt]; rfl
        · rfl)
    rw [← h]
    congr 1
    funext i
    show maskWord letter x _ i
      = maskWord (letterOpt letter) (pad (L := L) x) K.supp (Fin.castLE hn i)
    unfold maskWord
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs
    · rw [pad_castLE hn]; rfl
    · rfl

/-- A postcomposed algorithm gives an outcome at least as often as any set of preimages. -/
lemma sum_prob_le_prob_postcomp {ι O O' W : Type} [Fintype ι] [DecidableEq ι] [DecidableEq O]
    [DecidableEq O'] [Fintype W] [DecidableEq W] (A : QAlg ι σ O W) (g : O → O') (a : ι → σ)
    (t : ℕ) (S : Finset O) (o' : O') (hS : ∀ K ∈ S, g K = o') :
    ∑ K ∈ S, A.prob a t K ≤ (A.postcomp g).prob a t o' := by
  simp only [QAlg.prob, QAlg.postcomp_state, QAlg.postcomp_readout, qProb]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun h _ => ?_
  rw [Finset.sum_ite_eq]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (hS _ h1) h2
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-! ## The root theorem -/

variable (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b)
include hst hb hb1

open Classical in
/-- **The product-and-core algorithm with abstract parameters.**  For `n ≤ 2^L` and merger
parameters `P` satisfying `GoodParams`, there is a quantum algorithm with at most
`8192·(1 + costA b P b L)` queries returning a good record with probability at least `9/10`. -/
theorem exists_root_alg {n L : ℕ} (hn : n ≤ 2 ^ L) (P : MParams) (hP : GoodParams b (2 ^ L) P)
    (hk : ∀ h, 1 ≤ h → 1 ≤ (P h).2) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ L) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ uniformExtractionConstant * (1 + costA b P b L)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  have hb' : IsBreadthBound (letterOpt letter) b := isBreadthBound_letterOpt letter hb
  have hc : 0 ≤ costA b P b L := costA_nonneg b P b L
  -- every seed's function has a dual through the padding
  have hdual : ∀ ω : Ω b P b L,
      HasDual (fun x : Fin n → σ => summary (letterOpt letter) b P b L 0 ω (pad (L := L) x))
        (costA b P b L) := fun ω =>
    HasDual.restrict (e := Fin.castLE hn) (castLE_injective' hn) (Φ := fun x => pad (L := L) x)
      (fun x y i => by rw [pad_castLE hn, pad_castLE hn, Option.some_inj])
      (fun x y j hj => by
        have hlt : ¬ (j : ℕ) < n := fun hlt => hj ⟨j, hlt⟩ (Fin.ext rfl)
        rw [pad_of_not_lt x j hlt, pad_of_not_lt y j hlt])
      (hasDual_summary (letterOpt letter) hb1 P hk b L 0 ω)
  -- one algorithm per seed
  have hex : ∀ ω : Ω b P b L, ∃ q ∈ QueryCounts (X := Fin n → σ) id
      (fun x => summary (letterOpt letter) b P b L 0 ω (pad (L := L) x)) (1 / 16),
      (q : ℝ) ≤ uniformExtractionConstant * (1 + costA b P b L) := by
    intro ω
    obtain ⟨K, hK, Pd, hPd⟩ := (hdual ω).hasDualOn
    let _ := hK
    exact exists_algorithm_of_dualPairOn_uniform Pd hPd hc
  choose q hq hqle using hex
  choose W hW hW' A hA using hq
  let _ : ∀ ω, Fintype (W ω) := hW
  let _ : ∀ ω, DecidableEq (W ω) := hW'
  -- the mixture at a common query count
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, ⌊uniformExtractionConstant * (1 + costA b P b L)⌋₊ = Q := ⟨_, rfl⟩
  have hQ : ∀ ω, q ω ≤ Q := fun ω => hQdef ▸ Nat.le_floor (hqle ω)
  obtain ⟨W', hW'1, hW'2, B, hB⟩ := exists_mixture (unifW (Ω b P b L))
    (isWeight_unifW _).nonneg (isWeight_unifW _).sum_one q Q hQ A
  refine ⟨W', hW'1, hW'2, B, Q, hQdef ▸ Nat.floor_le (mul_nonneg (by unfold uniformExtractionConstant; norm_num) (by linarith)), fun x => ?_⟩
  -- correct seeds give good records
  have hgood : ∀ ω, IsSummary (letterOpt letter) (pad (L := L) x) b b L 0
      (summary (letterOpt letter) b P b L 0 ω (pad (L := L) x)) →
      GoodRec letter b x (summary (letterOpt letter) b P b L 0 ω (pad (L := L) x)) := by
    intro ω hS
    refine ⟨hS.truthful, hS.card_le, ?_⟩
    rw [prod_eq_wordProd_of_isSummary (letterOpt letter) hst hb' hS
      (fun i => by rw [mem_ivl]; simp), wordProd_pad letter hn]
  have hfail := summary_correct (letterOpt letter) hst hb' hb1 P hP b L 0 (by simp) (pad (L := L) x)
  have h1 : (15 / 16 : ℝ) * (1 - failMass (letterOpt letter) b P b L 0 (pad (L := L) x))
      = ∑ ω, unifW (Ω b P b L) ω * (if IsSummary (letterOpt letter) (pad (L := L) x) b b L 0
          (summary (letterOpt letter) b P b L 0 ω (pad (L := L) x)) then (15 / 16 : ℝ) else 0) := by
    unfold failMass
    nth_rewrite 1 [← (isWeight_unifW (Ω b P b L)).sum_one]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  calc (9 / 10 : ℝ)
      ≤ (15 / 16 : ℝ) * (1 - failMass (letterOpt letter) b P b L 0 (pad (L := L) x)) := by linarith
    _ = ∑ ω, unifW (Ω b P b L) ω * (if IsSummary (letterOpt letter) (pad (L := L) x) b b L 0
          (summary (letterOpt letter) b P b L 0 ω (pad (L := L) x)) then (15 / 16 : ℝ) else 0) := h1
    _ ≤ ∑ ω, unifW (Ω b P b L) ω
          * ∑ K ∈ Finset.univ.filter (GoodRec letter b x), (A ω).prob x (q ω) K := by
        refine Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left ?_ ((isWeight_unifW _).nonneg ω)
        split_ifs with hS
        · calc (15 / 16 : ℝ) = 1 - 1 / 16 := by norm_num
            _ ≤ (A ω).prob x (q ω) (summary (letterOpt letter) b P b L 0 ω (pad (L := L) x)) := hA ω x
            _ ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), (A ω).prob x (q ω) K :=
                Finset.single_le_sum (f := fun K => (A ω).prob x (q ω) K)
                  (fun K _ => (A ω).prob_nonneg x (q ω) K)
                  (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgood ω hS⟩)
        · exact Finset.sum_nonneg fun K _ => (A ω).prob_nonneg _ _ _
    _ = ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
        simp only [hB, Finset.mul_sum]
        rw [Finset.sum_comm]

open Classical in
/-- **The exact algorithm**: read every letter and compress the full record; `n` queries,
a good record with certainty.  Used for the lengths below the threshold of the numerics. -/
theorem exists_exact_core_alg {n L : ℕ} (hn : n ≤ 2 ^ L) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ L) (Option σ)) W),
      ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x n K := by
  have hb' : IsBreadthBound (letterOpt letter) b := isBreadthBound_letterOpt letter hb
  let full : (Fin n → σ) → Record (2 ^ L) (Option σ) := fun x j => some (pad (L := L) x j)
  have hfull : ∀ x, (full x).Truthful (pad (L := L) x) := fun x i s h => Option.some.inj h
  have hsupp : ∀ x, (full x).supp = Finset.univ := fun x => by
    ext i; simp [Record.supp, mem_optSupp, full]
  let f : (Fin n → σ) → Record (2 ^ L) (Option σ) := fun x =>
    Record.compress (letterOpt letter) b (full x)
  have hgood : ∀ x, GoodRec letter b x (f x) := fun x =>
    ⟨Record.truthful_compress (letterOpt letter) (hfull x) b,
      (Record.compress_spec (letterOpt letter) hb' _).2.1, by
        change (Record.compress (letterOpt letter) b (full x)).prod (letterOpt letter) = _
        rw [(Record.compress_spec (letterOpt letter) hb' _).2.2,
          Record.prod_of_truthful (letterOpt letter) (hfull x), hsupp x, subwordProd_univ,
          wordProd_pad letter hn]⟩
  obtain ⟨A, hA⟩ := exists_computesWithErrorOn (read := (id : (Fin n → σ) → Fin n → σ)) (f := f)
    (fun x y h => congrArg f h) (le_refl (0 : ℝ))
  rw [Fintype.card_fin] at hA
  refine ⟨_, inferInstance, inferInstance, A, fun x => ?_⟩
  calc (9 / 10 : ℝ) ≤ 1 - 0 := by norm_num
    _ ≤ A.prob x n (f x) := hA x
    _ ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), A.prob x n K :=
        Finset.single_le_sum (f := fun K => A.prob x n K) (fun K _ => A.prob_nonneg x n K)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgood x⟩)

open Classical in
/-- **The product bound with abstract parameters**: `Q_{1/10}(wordProd) ≤ 8192·(1 + costA)`. -/
theorem qQuery_wordProd_le_root {n L : ℕ} (hn : n ≤ 2 ^ L) (P : MParams)
    (hP : GoodParams b (2 ^ L) P) (hk : ∀ h, 1 ≤ h → 1 ≤ (P h).2) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ uniformExtractionConstant * (1 + costA b P b L) := by
  obtain ⟨W, hW, hW', B, Q, hQ, hgood⟩ := exists_root_alg letter hst hb hb1 hn P hP hk
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

end Root

end MonoidProduct
