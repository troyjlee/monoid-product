import MonoidProduct.Ordered.MergeSeeded
import MonoidProduct.Ordered.PiProb

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# Thinning a fixed candidate table with exact uniform draws
(part of the rank doubling of Section `sec:beta-rank-doubling`)

A finite label set `Λ` carries a fixed table of truthful candidate records `cand ℓ`.  A
label is *marked* (live) with respect to the saved history if its candidate passes the
marking test of the merger (`thinLive`); each round saves the accumulated union
(`saveBatch`), so unmarking is permanent.  A draw is an *ordering* of the labels, a bijection
`Λ ≃ Fin |Λ|`; the label drawn is the live label of least rank (`firstIn`).  For a
uniformly random ordering this label is exactly uniform on the live set: precomposing
the ordering with the transposition of two live labels transposes the first label, so
all fibres have the same size (`sum_unifW_firstIn`).  Consequently the law of the drawn
*record* is the conditional candidate law of the merger (`pushW_firstIn`), and the
halving lemma applies verbatim: a round of `2b` draws halves the expected live mass
(`thinRound_liveMass_le`), `R` rounds leave expected live mass `≤ 2^{-R}`
(`thinRun_liveMass_le`), and the probability that any label is still live is at most
`|Λ|·2^{-R}` (`thinRun_fail_le`).  When no label is live, every candidate is dominated
by the compressed cache (`prod_le_of_thinLive_empty`).

There is no rejection sampling here and hence no proposal budget: the first live label
of an ordering is found, in the seeded procedure of `RankDoubling.lean`, by a binary
search with transcript-tree decisions.
-/

namespace MonoidProduct

open Finset FiniteProb Seeded

section Thinning

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) {n : ℕ}
variable {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-- Orderings of the labels: bijections with an initial segment. -/
abbrev Ord (Λ : Type) [Fintype Λ] : Type := Λ ≃ Fin (Fintype.card Λ)

instance instNonemptyOrd : Nonempty (Ord Λ) := ⟨Fintype.equivFin Λ⟩

/-! ## The first label of a set in an ordering -/

/-- The label of `S` with the least rank. -/
noncomputable def firstIn (e : Ord Λ) (S : Finset Λ) (hS : S.Nonempty) : Λ :=
  e.symm ((S.image e).min' (hS.image e))

lemma firstIn_mem (e : Ord Λ) {S : Finset Λ} (hS : S.Nonempty) : firstIn e S hS ∈ S := by
  obtain ⟨ℓ, hℓ, hℓe⟩ := Finset.mem_image.1 (Finset.min'_mem _ (hS.image e))
  unfold firstIn
  rw [← hℓe, Equiv.symm_apply_apply]
  exact hℓ

lemma firstIn_le (e : Ord Λ) {S : Finset Λ} (hS : S.Nonempty) {ℓ : Λ} (hℓ : ℓ ∈ S) :
    e (firstIn e S hS) ≤ e ℓ := by
  unfold firstIn
  rw [Equiv.apply_symm_apply]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem e hℓ)

/-- The first label is the unique member of least rank. -/
lemma firstIn_eq_of_le (e : Ord Λ) {S : Finset Λ} (hS : S.Nonempty) {ℓ : Λ} (hℓ : ℓ ∈ S)
    (hmin : ∀ ℓ' ∈ S, e ℓ ≤ e ℓ') : firstIn e S hS = ℓ := by
  apply e.injective
  exact le_antisymm (firstIn_le e hS hℓ) (hmin _ (firstIn_mem e hS))

lemma swap_mem {S : Finset Λ} {ℓ ℓ' a : Λ} (hℓ : ℓ ∈ S) (hℓ' : ℓ' ∈ S) (ha : a ∈ S) :
    Equiv.swap ℓ ℓ' a ∈ S := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

lemma image_swap {S : Finset Λ} {ℓ ℓ' : Λ} (hℓ : ℓ ∈ S) (hℓ' : ℓ' ∈ S) :
    S.image (Equiv.swap ℓ ℓ') = S := by
  ext m
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact swap_mem hℓ hℓ' ha
  · intro hm
    exact ⟨Equiv.swap ℓ ℓ' m, swap_mem hℓ hℓ' hm, Equiv.swap_apply_self _ _ _⟩

lemma min'_congr {α : Type} [LinearOrder α] {T₁ T₂ : Finset α} (h₁ : T₁.Nonempty)
    (h₂ : T₂.Nonempty) (h : T₁ = T₂) : T₁.min' h₁ = T₂.min' h₂ := by
  subst h; rfl

/-- Precomposing the ordering with the transposition of two members of `S` transposes the
first label. -/
lemma firstIn_swap (e : Ord Λ) {S : Finset Λ} (hS : S.Nonempty) {ℓ ℓ' : Λ} (hℓ : ℓ ∈ S)
    (hℓ' : ℓ' ∈ S) :
    firstIn ((Equiv.swap ℓ ℓ').trans e) S hS = Equiv.swap ℓ ℓ' (firstIn e S hS) := by
  unfold firstIn
  have himg : S.image ((Equiv.swap ℓ ℓ').trans e) = S.image e := by
    rw [Equiv.coe_trans, ← Finset.image_image, image_swap hℓ hℓ']
  rw [Equiv.symm_trans_apply, Equiv.symm_swap, min'_congr _ (hS.image e) himg]

/-- The fibres of `firstIn` over two members of `S` have the same size. -/
lemma card_fiber_firstIn {S : Finset Λ} (hS : S.Nonempty) {ℓ ℓ' : Λ} (hℓ : ℓ ∈ S) (hℓ' : ℓ' ∈ S) :
    (Finset.univ.filter fun e : Ord Λ => firstIn e S hS = ℓ).card
      = (Finset.univ.filter fun e : Ord Λ => firstIn e S hS = ℓ').card := by
  refine Finset.card_bij (fun e _ => (Equiv.swap ℓ ℓ').trans e) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [firstIn_swap e hS hℓ hℓ', he.2, Equiv.swap_apply_left]
  · intro e₁ _ e₂ _ h
    refine Equiv.ext fun a => ?_
    have := congrArg (fun f : Ord Λ => f (Equiv.swap ℓ ℓ' a)) h
    simpa [Equiv.trans_apply, Equiv.swap_apply_self] using this
  · intro e' he'
    rw [Finset.mem_filter] at he'
    refine ⟨(Equiv.swap ℓ ℓ').trans e', Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [firstIn_swap e' hS hℓ hℓ', he'.2, Equiv.swap_apply_right]
    · refine Equiv.ext fun a => ?_
      simp [Equiv.trans_apply, Equiv.swap_apply_self]

/-- **Uniformity**: the first label of a uniformly random ordering is uniform on `S`. -/
theorem sum_unifW_firstIn {S : Finset Λ} (hS : S.Nonempty) {ℓ : Λ} (hℓ : ℓ ∈ S) :
    ∑ e : Ord Λ, unifW (Ord Λ) e * (if firstIn e S hS = ℓ then (1 : ℝ) else 0) = 1 / S.card := by
  classical
  have hfib : ∀ ℓ' ∈ S, (Finset.univ.filter fun e : Ord Λ => firstIn e S hS = ℓ').card
      = (Finset.univ.filter fun e : Ord Λ => firstIn e S hS = ℓ).card :=
    fun ℓ' hℓ' => card_fiber_firstIn hS hℓ' hℓ
  have hpart : Fintype.card (Ord Λ)
      = S.card * (Finset.univ.filter fun e : Ord Λ => firstIn e S hS = ℓ).card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := fun e : Ord Λ => firstIn e S hS) (t := S) (fun e _ => firstIn_mem e hS)]
    rw [Finset.sum_congr rfl (fun ℓ' hℓ' => hfib ℓ' hℓ'), Finset.sum_const, smul_eq_mul]
  have hsum : ∑ e : Ord Λ, unifW (Ord Λ) e * (if firstIn e S hS = ℓ then (1 : ℝ) else 0)
      = ((Finset.univ.filter fun e : Ord Λ => firstIn e S hS = ℓ).card : ℝ)
          / Fintype.card (Ord Λ) := by
    unfold unifW
    rw [← Finset.mul_sum, Finset.sum_boole, one_div, inv_mul_eq_div]
  rw [hsum, hpart]
  have hcardpos : (0 : ℝ) < Fintype.card (Ord Λ) := by exact_mod_cast Fintype.card_pos
  have hfpos : (0 : ℝ) < (Finset.univ.filter fun e : Ord Λ => firstIn e S hS = ℓ).card := by
    rw [hpart] at hcardpos
    push_cast at hcardpos
    have hS' : (0 : ℝ) ≤ S.card := by positivity
    by_contra hle
    push Not at hle
    nlinarith
  push_cast
  field_simp

/-! ## Rounds and runs -/

variable (cand : Λ → Record n σ) (b : ℕ)

/-- The live labels. -/
def thinLive (completed : List (Record n σ)) : Finset Λ :=
  Finset.univ.filter fun ℓ => liveTest letter completed (cand ℓ)

/-- One thinning round: `2b` first-marked draws, saved as the accumulated union with the
previous saved union (`saveBatch`); when no label is marked the round is idle and saves a
duplicate of the current union (the marked set stays empty and the saved product is
unchanged; this keeps the fixed-length transcript of `RankDoubling.lean`). -/
noncomputable def thinRound (completed : List (Record n σ)) (row : Fin (2 * b) → Ord Λ) :
    List (Record n σ) :=
  if h : (thinLive letter cand completed).Nonempty then
    saveBatch completed (unionTuple (fun i => cand (firstIn (row i) _ h)))
  else saveBatch completed emptyRec

/-- `R` rounds. -/
noncomputable def thinRun :
    ∀ (R : ℕ), List (Record n σ) → (Fin R → Fin (2 * b) → Ord Λ) → List (Record n σ)
  | 0, completed, _ => completed
  | R + 1, completed, rows => thinRun R (thinRound letter cand b completed (rows 0)) (Fin.tail rows)

lemma thinRun_zero (completed : List (Record n σ)) (rows : Fin 0 → Fin (2 * b) → Ord Λ) :
    thinRun letter cand b 0 completed rows = completed := rfl

lemma thinRun_succ (R : ℕ) (completed : List (Record n σ)) (row : Fin (2 * b) → Ord Λ)
    (rest : Fin R → Fin (2 * b) → Ord Λ) :
    thinRun letter cand b (R + 1) completed (Fin.cons row rest)
      = thinRun letter cand b R (thinRound letter cand b completed row) rest := by
  simp [thinRun, Fin.cons_zero, Fin.tail_cons]

variable (x : Fin n → σ) (hcand : ∀ ℓ, (cand ℓ).Truthful x)
include hcand

lemma thinRound_truthful {completed : List (Record n σ)} (hc : ∀ A ∈ completed, A.Truthful x)
    (row : Fin (2 * b) → Ord Λ) : ∀ A ∈ thinRound letter cand b completed row, A.Truthful x := by
  unfold thinRound
  split_ifs with h
  · exact truthful_saveBatch hc (truthful_unionTuple fun i => hcand _)
  · exact truthful_saveBatch hc (truthful_emptyRec x)

lemma thinRun_truthful : ∀ (R : ℕ) (completed : List (Record n σ)), (∀ A ∈ completed, A.Truthful x) →
    ∀ rows : Fin R → Fin (2 * b) → Ord Λ, ∀ A ∈ thinRun letter cand b R completed rows, A.Truthful x
  | 0, _, hc, _ => hc
  | R + 1, completed, hc, rows =>
    thinRun_truthful R _ (thinRound_truthful letter cand b x hcand hc (rows 0)) (Fin.tail rows)

/-! ## The candidate law -/

variable [Nonempty Λ]

/-- The law of a uniformly random candidate. -/
noncomputable def candW : Record n σ → ℝ := pushW (unifW Λ) cand

omit hcand in
lemma isWeight_candW : IsWeight (candW cand) := isWeight_pushW (isWeight_unifW Λ) cand

lemma candW_truthful : ∀ e, candW cand e ≠ 0 → e.Truthful x := by
  intro e he
  unfold candW pushW at he
  obtain ⟨ℓ, _, hℓ⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  split_ifs at hℓ with hc
  · rw [← hc]; exact hcand ℓ
  · exact absurd rfl hℓ

omit hcand in
lemma liveMass_candW (completed : List (Record n σ)) :
    liveMass (candW cand) (liveTest letter completed)
      = (thinLive letter cand completed).card / Fintype.card Λ := by
  unfold liveMass
  have h : ∀ e, (if liveTest letter completed e then candW cand e else 0)
      = candW cand e * (if liveTest letter completed e then 1 else 0) := fun e => by
    split_ifs <;> simp
  simp only [h]
  rw [candW, sum_pushW]
  unfold unifW thinLive
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs <;> simp

omit hcand in
lemma card_filter_cand_eq {completed : List (Record n σ)} {e₀ : Record n σ}
    (hlive : liveTest letter completed e₀ = true) :
    Finset.univ.filter (fun ℓ => cand ℓ = e₀) = (thinLive letter cand completed).filter fun ℓ => cand ℓ = e₀ := by
  ext ℓ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, thinLive]
  constructor
  · intro hc; exact ⟨by rw [hc]; exact hlive, hc⟩
  · exact fun h => h.2

omit hcand in
/-- **The draw law**: the record of the first live label of a uniformly random ordering has the
conditional candidate law. -/
theorem pushW_firstIn (completed : List (Record n σ))
    (h : (thinLive letter cand completed).Nonempty) :
    pushW (unifW (Ord Λ)) (fun e => cand (firstIn e (thinLive letter cand completed) h))
      = condW (candW cand) (liveTest letter completed) := by
  classical
  funext e₀
  set S := thinLive letter cand completed with hSdef
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.2 h
  have hL : pushW (unifW (Ord Λ)) (fun e => cand (firstIn e S h)) e₀
      = ∑ ℓ ∈ S, (if cand ℓ = e₀ then (1 : ℝ) / S.card else 0) := by
    unfold pushW
    calc ∑ e, (if cand (firstIn e S h) = e₀ then unifW (Ord Λ) e else 0)
        = ∑ e, ∑ ℓ ∈ S, (if firstIn e S h = ℓ then
            (if cand ℓ = e₀ then unifW (Ord Λ) e else 0) else 0) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_eq_single (firstIn e S h)]
          · rw [if_pos rfl]
          · intro ℓ _ hne; rw [if_neg (Ne.symm hne)]
          · intro hnot; exact absurd (firstIn_mem e h) hnot
      _ = ∑ ℓ ∈ S, ∑ e, (if firstIn e S h = ℓ then
            (if cand ℓ = e₀ then unifW (Ord Λ) e else 0) else 0) := Finset.sum_comm
      _ = ∑ ℓ ∈ S, (if cand ℓ = e₀ then (1 : ℝ) / S.card else 0) := by
          refine Finset.sum_congr rfl fun ℓ hℓ => ?_
          by_cases hc : cand ℓ = e₀
          · simp only [hc, if_true]
            rw [← sum_unifW_firstIn h hℓ]
            refine Finset.sum_congr rfl fun e _ => ?_
            split_ifs <;> simp
          · simp only [hc, if_false]
            simp
  have hμ : candW cand e₀ = ((Finset.univ.filter fun ℓ => cand ℓ = e₀).card : ℝ) / Fintype.card Λ := by
    unfold candW pushW unifW
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, one_div,
      div_eq_mul_inv]
  rw [hL]
  unfold condW
  rw [hμ, liveMass_candW letter cand completed]
  by_cases hlive : liveTest letter completed e₀ = true
  · rw [if_pos hlive, card_filter_cand_eq letter cand hlive]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hq : (0 : ℝ) < Fintype.card Λ := by exact_mod_cast Fintype.card_pos
    rw [← hSdef]
    field_simp
  · rw [if_neg hlive]
    refine Finset.sum_eq_zero fun ℓ hℓ => ?_
    rw [if_neg]
    intro hc
    apply hlive
    have := (Finset.mem_filter.1 hℓ).2
    rwa [hc] at this

/-! ## Halving and the chain -/

variable (hst : IsStableOrder M) (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b)
include hst hb hb1

theorem thinRound_liveMass_le {completed : List (Record n σ)} (hc : ∀ A ∈ completed, A.Truthful x)
    :
    ∑ row : Fin (2 * b) → Ord Λ, tupleW (unifW (Ord Λ)) row
        * liveMass (candW cand) (liveTest letter (thinRound letter cand b completed row))
      ≤ (1 / 2) * liveMass (candW cand) (liveTest letter completed) := by
  by_cases h : (thinLive letter cand completed).Nonempty
  · have hrow : ∀ row : Fin (2 * b) → Ord Λ, thinRound letter cand b completed row
        = saveBatch completed (unionTuple (fun i => cand (firstIn (row i) _ h))) := fun row => by
      unfold thinRound; rw [dif_pos h]
    simp only [hrow]
    rw [sum_tupleW_map (isWeight_unifW (Ord Λ)) (fun e => cand (firstIn e _ h))
      (fun y => liveMass (candW cand) (liveTest letter (saveBatch completed (unionTuple y)))),
      pushW_firstIn letter cand completed h]
    have hw : 0 < liveMass (candW cand) (liveTest letter completed) := by
      rw [liveMass_candW]
      have : (0 : ℝ) < (thinLive letter cand completed).card := by
        exact_mod_cast Finset.card_pos.2 h
      positivity
    refine (halving_saveBatch letter x (candW cand) hst hb (isWeight_candW cand)
      (candW_truthful cand x hcand) completed hc hw).trans ?_
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hlm := liveMass_nonneg (isWeight_candW cand) (liveTest letter completed)
    have : (b : ℝ) / (2 * b + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    exact mul_le_mul_of_nonneg_right this hlm
  · have hrow : ∀ row : Fin (2 * b) → Ord Λ, thinRound letter cand b completed row
        = saveBatch completed emptyRec := fun row => by unfold thinRound; rw [dif_neg h]
    simp only [hrow]
    rw [← Finset.sum_mul, (isWeight_tupleW (isWeight_unifW _) _).sum_one, one_mul]
    have h0 : liveMass (candW cand) (liveTest letter completed) = 0 := by
      rw [liveMass_candW, Finset.not_nonempty_iff_eq_empty.1 h]; simp
    have hsub : thinLive letter cand (saveBatch completed emptyRec)
        ⊆ thinLive letter cand completed := by
      intro ℓ hℓ
      unfold thinLive at hℓ ⊢
      rw [Finset.mem_filter] at hℓ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have := hℓ.2
      rw [liveTest_saveBatch] at this
      exact (Bool.and_eq_true_iff.1 this).1
    have h1 : liveMass (candW cand) (liveTest letter (saveBatch completed emptyRec)) = 0 := by
      rw [liveMass_candW, Finset.card_eq_zero.2 (Finset.subset_empty.1 (by
        rw [← Finset.not_nonempty_iff_eq_empty.1 h]; exact hsub))]
      simp
    rw [h0, h1]; norm_num

theorem thinRun_liveMass_le : ∀ (R : ℕ) (completed : List (Record n σ)),
    (∀ A ∈ completed, A.Truthful x) →
    ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows
        * liveMass (candW cand) (liveTest letter (thinRun letter cand b R completed rows))
      ≤ (1 / 2) ^ R * liveMass (candW cand) (liveTest letter completed)
  | 0, completed, _ => by
    rw [sum_pi_zero, tupleW_zero, one_mul, pow_zero, one_mul, thinRun_zero]
  | R + 1, completed, hc => by
    rw [sum_pi_succ]
    simp only [tupleW_cons, thinRun_succ]
    have hW : ∀ row : Fin (2 * b) → Ord Λ, 0 ≤ tupleW (unifW (Ord Λ)) row :=
      fun row => tupleW_nonneg (isWeight_unifW _) row
    calc ∑ row : Fin (2 * b) → Ord Λ, ∑ rest : Fin R → Fin (2 * b) → Ord Λ,
          tupleW (unifW (Ord Λ)) row * tupleW (tupleW (unifW (Ord Λ))) rest
            * liveMass (candW cand) (liveTest letter
                (thinRun letter cand b R (thinRound letter cand b completed row) rest))
        = ∑ row : Fin (2 * b) → Ord Λ, tupleW (unifW (Ord Λ)) row
            * ∑ rest : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rest
              * liveMass (candW cand) (liveTest letter
                  (thinRun letter cand b R (thinRound letter cand b completed row) rest)) := by
          refine Finset.sum_congr rfl fun row _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun rest _ => ?_
          ring
      _ ≤ ∑ row : Fin (2 * b) → Ord Λ, tupleW (unifW (Ord Λ)) row
            * ((1 / 2) ^ R * liveMass (candW cand)
                (liveTest letter (thinRound letter cand b completed row))) :=
          Finset.sum_le_sum fun row _ => mul_le_mul_of_nonneg_left
            (thinRun_liveMass_le R _ (thinRound_truthful letter cand b x hcand hc row)) (hW row)
      _ = (1 / 2) ^ R * ∑ row : Fin (2 * b) → Ord Λ, tupleW (unifW (Ord Λ)) row
            * liveMass (candW cand) (liveTest letter (thinRound letter cand b completed row)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun row _ => ?_
          ring
      _ ≤ (1 / 2) ^ R * ((1 / 2) * liveMass (candW cand) (liveTest letter completed)) :=
          mul_le_mul_of_nonneg_left (thinRound_liveMass_le letter cand b x hcand hst hb hb1 hc)
            (by positivity)
      _ = (1 / 2) ^ (R + 1) * liveMass (candW cand) (liveTest letter completed) := by ring

/-- **Failure probability**: some label is still live after `R` rounds with probability at
most `|Λ|·2^{-R}`. -/
theorem thinRun_fail_le (R : ℕ) {completed : List (Record n σ)}
    (hc : ∀ A ∈ completed, A.Truthful x) :
    ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows
        * (if (thinLive letter cand (thinRun letter cand b R completed rows)).Nonempty then (1 : ℝ) else 0)
      ≤ (Fintype.card Λ : ℝ) * (1 / 2) ^ R := by
  have hq : (0 : ℝ) < Fintype.card Λ := by exact_mod_cast Fintype.card_pos
  have hpt : ∀ rows : Fin R → Fin (2 * b) → Ord Λ,
      (if (thinLive letter cand (thinRun letter cand b R completed rows)).Nonempty then (1 : ℝ) else 0)
        ≤ (Fintype.card Λ : ℝ)
          * liveMass (candW cand) (liveTest letter (thinRun letter cand b R completed rows)) := by
    intro rows
    rw [liveMass_candW]
    split_ifs with h
    · have : (1 : ℝ) ≤ (thinLive letter cand (thinRun letter cand b R completed rows)).card := by
        exact_mod_cast Finset.card_pos.2 h
      rw [mul_div_cancel₀ _ hq.ne']
      exact this
    · positivity
  calc ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows
        * (if (thinLive letter cand (thinRun letter cand b R completed rows)).Nonempty then (1 : ℝ) else 0)
      ≤ ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows
          * ((Fintype.card Λ : ℝ)
            * liveMass (candW cand) (liveTest letter (thinRun letter cand b R completed rows))) :=
        Finset.sum_le_sum fun rows _ => mul_le_mul_of_nonneg_left (hpt rows)
          (tupleW_nonneg (isWeight_tupleW (isWeight_unifW _) _) rows)
    _ = (Fintype.card Λ : ℝ) * ∑ rows : Fin R → Fin (2 * b) → Ord Λ,
          tupleW (tupleW (unifW (Ord Λ))) rows
            * liveMass (candW cand) (liveTest letter (thinRun letter cand b R completed rows)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun rows _ => ?_
        ring
    _ ≤ (Fintype.card Λ : ℝ) * ((1 / 2) ^ R * liveMass (candW cand) (liveTest letter completed)) :=
        mul_le_mul_of_nonneg_left (thinRun_liveMass_le letter cand b x hcand hst hb hb1 R completed hc)
          hq.le
    _ ≤ (Fintype.card Λ : ℝ) * ((1 / 2) ^ R * 1) := by
        gcongr
        exact liveMass_le_one (isWeight_candW cand) _
    _ = (Fintype.card Λ : ℝ) * (1 / 2) ^ R := by ring

/-- **Domination**: when no label is live, every candidate is dominated by the compressed
cache. -/
theorem prod_le_of_thinLive_empty [DecidableLE M] {completed : List (Record n σ)}
    (hc : ∀ A ∈ completed, A.Truthful x) (h : ¬ (thinLive letter cand completed).Nonempty) (ℓ : Λ) :
    (cand ℓ).prod letter ≤ (Record.compress letter b (unionList completed)).prod letter := by
  refine prod_le_of_not_live letter x hst hb completed hc (hcand ℓ) ?_
  rw [Finset.not_nonempty_iff_eq_empty] at h
  by_contra hne
  have hmem : ℓ ∈ thinLive letter cand completed := by
    unfold thinLive
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hne⟩
  rw [h] at hmem
  exact absurd hmem (Finset.notMem_empty ℓ)

end Thinning

end MonoidProduct
