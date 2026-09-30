import MonoidProduct.Ordered.RankDoubling
import MonoidProduct.Ordered.Cost

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# Logarithmic rank depth: the stage recursion

The iterated rank doubling behind `thm:ordered-beta-log-product`.

Stage `s` produces rank-`2^s` summaries of every dyadic interval `(j, q)` of the padded
word.  Stage `0` is the rank-`1` summary of the ordered
product theorem (`thm:ordered-beta-product`); stage `s+1` on `(j+1, q)` is the rank
doubling of `RankDoubling.lean` with the stage-`s` summaries of the tree's nodes as child
functions; every stage is **amplified** by taking the compressed union of `c`
independent copies (`amp`): the union is a summary whenever one copy is
(`isSummary_amp`), so the failure probability is raised to the power `c`
(`amp_fail_le`).

* `Ω2 s j` are the seeds: `c` copies of (child seeds for every node, orderings for the
  rounds), by recursion on `s`.
* `summary2 s j q ω x` is the record; `summary2_truthful`, `summary2_supp_subset`,
  `summary2_card_le` hold for every seed.
* `costB s j` is the dual cost: `2c·costA` at stage `0`, and at stage `s+1`
  `2c · 2R·2b·((j+3)·Vc + Pc)` with `Vc = 4∑_d costB s (j−d)·√2^d`, the common value of
  the path and total sums of the tree-search dual under the weights
  `β_w = 2^{-depth w/4}`, and `Pc = 8∑_{j' ≤ j} costB s j'` the path cost of a retrieval
  (`hasDual_summary2`).
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

section LogRank

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable [DecidableLE M] (letter : σ → M) {N : ℕ} (b : ℕ)

/-! ## Amplification by union of independent copies -/

/-- The compressed union of `c` copies. -/
noncomputable def amp {Ω' : Type} (c : ℕ) (f : Ω' → (Fin N → σ) → Record N σ) (ω : Fin c → Ω')
    (x : Fin N → σ) : Record N σ :=
  Record.compress letter b (unionList (List.ofFn fun i => f (ω i) x))

lemma amp_truthful {Ω' : Type} (c : ℕ) (f : Ω' → (Fin N → σ) → Record N σ)
    (hf : ∀ ω x, (f ω x).Truthful x) (ω : Fin c → Ω') (x : Fin N → σ) : (amp letter b c f ω x).Truthful x := by
  unfold amp
  refine Record.truthful_compress letter (truthful_unionList x fun A hA => ?_) b
  rw [List.mem_ofFn] at hA
  obtain ⟨i, rfl⟩ := hA
  exact hf _ x

lemma supp_amp_subset (hb : IsBreadthBound letter b) {Ω' : Type} (c : ℕ)
    (f : Ω' → (Fin N → σ) → Record N σ) (I : Finset (Fin N)) (hf : ∀ ω x, (f ω x).supp ⊆ I)
    (ω : Fin c → Ω') (x : Fin N → σ) : (amp letter b c f ω x).supp ⊆ I := by
  unfold amp
  refine (Record.compress_spec letter hb _).1.trans (supp_unionList_subset _ _ fun A hA => ?_)
  rw [List.mem_ofFn] at hA
  obtain ⟨i, rfl⟩ := hA
  exact hf _ x

lemma card_amp_le (hb : IsBreadthBound letter b) {Ω' : Type} (c : ℕ)
    (f : Ω' → (Fin N → σ) → Record N σ) (ω : Fin c → Ω') (x : Fin N → σ) :
    (amp letter b c f ω x).supp.card ≤ b :=
  (Record.compress_spec letter hb _).2.1

theorem hasDual_amp {Ω' : Type} (c : ℕ) (f : Ω' → (Fin N → σ) → Record N σ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ ω, HasDual (f ω) A) (ω : Fin c → Ω') :
    HasDual (amp letter b c f ω) (2 * (c * A)) := by
  have h := HasDual.combine (fun K : Fin c → Record N σ =>
    Record.compress letter b (unionList (List.ofFn K))) (c := fun _ => A) (fun _ => hA)
    (fun i => hf (ω i))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

/-- **The union is a summary when one copy is.** -/
theorem isSummary_amp (hst : IsStableOrder M) (hb : IsBreadthBound letter b) {Ω' : Type} (c : ℕ)
    (f : Ω' → (Fin N → σ) → Record N σ) {r j q : ℕ} (x : Fin N → σ)
    (hf : ∀ ω x, (f ω x).Truthful x) (hs : ∀ ω x, (f ω x).supp ⊆ ivl j q) (ω : Fin c → Ω')
    (i : Fin c) (hi : IsSummary letter x b r j q (f (ω i) x)) :
    IsSummary letter x b r j q (amp letter b c f ω x) where
  truthful := amp_truthful letter b c f hf ω x
  supp_subset := supp_amp_subset letter b hb c f _ hs ω x
  card_le := card_amp_le letter b hb c f ω x
  dom := fun U hU hcard => by
    refine (hi.dom U hU hcard).trans ?_
    unfold amp
    rw [(Record.compress_spec letter hb _).2.2,
      Record.prod_of_truthful letter (truthful_unionList x fun A hA => by
        rw [List.mem_ofFn] at hA; obtain ⟨k, rfl⟩ := hA; exact hf _ x),
      Record.prod_of_truthful letter (hf _ x)]
    exact hst.subwordProd_mono letter x (supp_subset_unionList (by rw [List.mem_ofFn]; exact ⟨i, rfl⟩))

/-- Product of sums over independent coordinates. -/
lemma sum_tupleW_prod {E : Type} [Fintype E] [DecidableEq E] {μ : E → ℝ} (g : E → ℝ) :
    ∀ c : ℕ, ∑ z : Fin c → E, tupleW μ z * ∏ i, g (z i) = (∑ e, μ e * g e) ^ c
  | 0 => by
    rw [sum_pi_zero, tupleW_zero, pow_zero]
    simp
  | c + 1 => by
    rw [sum_pi_succ]
    simp only [tupleW_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [pow_succ', ← sum_tupleW_prod g c, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun z _ => ?_
    ring

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Amplification**: if each copy fails with mass at most `δ`, the union fails with mass at most
`δ^c`. -/
theorem amp_fail_le (hst : IsStableOrder M) (hb : IsBreadthBound letter b) {Ω' : Type} [Fintype Ω']
    [DecidableEq Ω'] [Nonempty Ω'] (c : ℕ) (f : Ω' → (Fin N → σ) → Record N σ) {r j q : ℕ}
    (x : Fin N → σ) (hf : ∀ ω x, (f ω x).Truthful x) (hs : ∀ ω x, (f ω x).supp ⊆ ivl j q) {δ : ℝ}
    (_hδ : 0 ≤ δ)
    (hfail : ∑ ω, unifW Ω' ω * (if IsSummary letter x b r j q (f ω x) then 0 else 1) ≤ δ) :
    ∑ ω : Fin c → Ω', unifW (Fin c → Ω') ω
        * (if IsSummary letter x b r j q (amp letter b c f ω x) then 0 else 1) ≤ δ ^ c := by
  calc ∑ ω : Fin c → Ω', unifW (Fin c → Ω') ω
          * (if IsSummary letter x b r j q (amp letter b c f ω x) then 0 else 1)
      ≤ ∑ ω : Fin c → Ω', tupleW (unifW Ω') ω
          * ∏ i, (if IsSummary letter x b r j q (f (ω i) x) then (0 : ℝ) else 1) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        rw [unifW_pi]
        refine mul_le_mul_of_nonneg_left ?_ (tupleW_nonneg (isWeight_unifW _) ω)
        split_ifs with h
        · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
        · rw [Finset.prod_eq_one fun i _ => ?_]
          rw [if_neg]
          intro hi
          exact h (isSummary_amp letter b hst hb c f x hf hs ω i hi)
    _ = (∑ e, unifW Ω' e * (if IsSummary letter x b r j q (f e x) then (0 : ℝ) else 1)) ^ c :=
        sum_tupleW_prod (fun e => if IsSummary letter x b r j q (f e x) then (0 : ℝ) else 1) c
    _ ≤ δ ^ c := pow_le_pow_left₀ (Finset.sum_nonneg fun e _ =>
        mul_nonneg ((isWeight_unifW _).nonneg e) (by split_ifs <;> norm_num)) hfail c

/-! ## Seeds -/

variable (P : MParams) (c R : ℕ)

/-- **The seed spaces of the stages.** -/
def Ω2 : ℕ → ℕ → Type
  | 0, j => Fin c → Ω b P 1 j
  | _ + 1, 0 => Unit
  | s + 1, j + 1 => Fin c →
      ((∀ w : DNode j, Ω2 s (j + 1 - w.1)) × (Fin R → Fin (2 * b) → Ord (DNode j)))

@[instance_reducible] def fintypeΩ2 : ∀ s j, Fintype (Ω2 b P c R s j)
  | 0, j => inferInstanceAs (Fintype (Fin c → Ω b P 1 j))
  | _ + 1, 0 => inferInstanceAs (Fintype Unit)
  | s + 1, j + 1 =>
      letI : ∀ j', Fintype (Ω2 b P c R s j') := fun j' => fintypeΩ2 s j'
      inferInstanceAs (Fintype (Fin c →
        ((∀ w : DNode j, Ω2 b P c R s (j + 1 - w.1)) × (Fin R → Fin (2 * b) → Ord (DNode j)))))

def decEqΩ2 : ∀ s j, DecidableEq (Ω2 b P c R s j)
  | 0, j => inferInstanceAs (DecidableEq (Fin c → Ω b P 1 j))
  | _ + 1, 0 => inferInstanceAs (DecidableEq Unit)
  | s + 1, j + 1 =>
      letI : ∀ j', DecidableEq (Ω2 b P c R s j') := fun j' => decEqΩ2 s j'
      letI : ∀ j', Fintype (Ω2 b P c R s j') := fun j' => fintypeΩ2 b P c R s j'
      inferInstanceAs (DecidableEq (Fin c →
        ((∀ w : DNode j, Ω2 b P c R s (j + 1 - w.1)) × (Fin R → Fin (2 * b) → Ord (DNode j)))))

instance instFintypeΩ2 {s j : ℕ} : Fintype (Ω2 b P c R s j) := fintypeΩ2 b P c R s j
instance instDecidableEqΩ2 {s j : ℕ} : DecidableEq (Ω2 b P c R s j) := decEqΩ2 b P c R s j

theorem nonemptyΩ2 : ∀ s j, Nonempty (Ω2 b P c R s j)
  | 0, _ => ⟨fun _ => Classical.arbitrary _⟩
  | _ + 1, 0 => ⟨()⟩
  | s + 1, j + 1 => ⟨fun _ => (fun w => (nonemptyΩ2 s (j + 1 - w.1)).some, fun _ _ => Fintype.equivFin _)⟩

instance instNonemptyΩ2 {s j : ℕ} : Nonempty (Ω2 b P c R s j) := nonemptyΩ2 b P c R s j

/-! ## The stage summaries -/

/-- **The stage-`s` summary of `(j, q)`.** -/
noncomputable def summary2 : ∀ (s j : ℕ), ℕ → Ω2 b P c R s j → (Fin N → σ) → Record N σ
  | 0, j, q, ω, x => amp letter b c (fun ω' => summary letter b P 1 j q ω') ω x
  | _ + 1, 0, q, _, x => letterRecN x q
  | s + 1, j + 1, q, ω, x =>
      amp letter b c (fun ω' : (∀ w : DNode j, Ω2 b P c R s (j + 1 - w.1))
          × (Fin R → Fin (2 * b) → Ord (DNode j)) =>
        dblOut letter j
          (fun w => summary2 s (j + 1 - w.1) (q * 2 ^ (w.1 : ℕ) + w.2) (ω'.1 w)) b ω'.2) ω x

lemma summary2_zero (j q : ℕ) (ω : Ω2 b P c R 0 j) (x : Fin N → σ) :
    summary2 letter b P c R 0 j q ω x
      = amp letter b c (fun ω' => summary letter b P 1 j q ω') ω x := rfl

lemma summary2_succ_zero (s q : ℕ) (ω : Ω2 b P c R (s + 1) 0) (x : Fin N → σ) :
    summary2 letter b P c R (s + 1) 0 q ω x = letterRecN x q := rfl

lemma summary2_succ_succ (s j q : ℕ) (ω : Ω2 b P c R (s + 1) (j + 1)) (x : Fin N → σ) :
    summary2 letter b P c R (s + 1) (j + 1) q ω x
      = amp letter b c (fun ω' : (∀ w : DNode j, Ω2 b P c R s (j + 1 - w.1))
          × (Fin R → Fin (2 * b) → Ord (DNode j)) =>
        dblOut letter j
          (fun w => summary2 letter b P c R s (j + 1 - w.1) (q * 2 ^ (w.1 : ℕ) + w.2) (ω'.1 w)) b ω'.2)
        ω x := rfl

/-! ## Invariants for every seed -/

section Invariants

variable (hst : IsStableOrder M) (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b)
include hb hb1

theorem summary2_truthful :
    ∀ (s j q : ℕ) (ω : Ω2 b P c R s j) (x : Fin N → σ), (summary2 letter b P c R s j q ω x).Truthful x
  | 0, j, q, ω, x => by
    rw [summary2_zero]
    exact amp_truthful letter b c _ (fun ω' x => summary_truthful letter hb hb1 P 1 j q ω' x) ω x
  | _ + 1, 0, q, _, x => by
    rw [summary2_succ_zero]
    unfold letterRecN
    split_ifs
    · exact letterRec_truthful x _
    · exact truthful_emptyRec x
  | s + 1, j + 1, q, ω, x => by
    rw [summary2_succ_succ]
    refine amp_truthful letter b c _ (fun ω' x => ?_) ω x
    exact dblOut_truthful letter j _ b x (fun w _ => summary2_truthful s _ _ _ x) ω'.2

theorem summary2_card_le :
    ∀ (s j q : ℕ) (ω : Ω2 b P c R s j) (x : Fin N → σ), (summary2 letter b P c R s j q ω x).supp.card ≤ b
  | 0, j, q, ω, x => by
    rw [summary2_zero]
    exact card_amp_le letter b hb c _ ω x
  | _ + 1, 0, q, _, x => by
    rw [summary2_succ_zero]
    unfold letterRecN
    split_ifs
    · rw [supp_letterRec, Finset.card_singleton]; exact hb1
    · simp
  | s + 1, j + 1, q, ω, x => by
    rw [summary2_succ_succ]
    exact card_amp_le letter b hb c _ ω x

theorem summary2_supp_subset :
    ∀ (s j q : ℕ) (ω : Ω2 b P c R s j) (x : Fin N → σ), (summary2 letter b P c R s j q ω x).supp ⊆ ivl j q
  | 0, j, q, ω, x => by
    rw [summary2_zero]
    exact supp_amp_subset letter b hb c _ _ (fun ω' x => summary_supp_subset letter hb hb1 P 1 j q ω' x) ω x
  | _ + 1, 0, q, _, x => by
    rw [summary2_succ_zero]
    unfold letterRecN
    split_ifs with h
    · rw [supp_letterRec, ivl_zero q h]
    · simp
  | s + 1, j + 1, q, ω, x => by
    rw [summary2_succ_succ]
    refine supp_amp_subset letter b hb c _ _ (fun ω' x => ?_) ω x
    exact supp_dblOut_subset letter j q _ x hb (fun w _ => summary2_supp_subset s _ _ _ x) ω'.2

end Invariants

/-! ## Costs -/

/-- The cost of a round of the tree search at stage `s+1` on `(j+1, ·)`: the common value of
the path and total sums under the weights `β_w = 2^{-depth/4}`. -/
noncomputable def VcOf (A : ℕ → ℝ) (j : ℕ) : ℝ :=
  4 * ∑ d ∈ Finset.range (j + 1), A (j - d) * Real.sqrt 2 ^ d

/-- The retrieval cost: twice the path sum of cell costs. -/
noncomputable def PcOf (A : ℕ → ℝ) (j : ℕ) : ℝ :=
  2 * (4 * ∑ d ∈ Finset.range (j + 1), A (j - d))

/-- **The cost recurrence of the stages.** -/
noncomputable def costB : ℕ → ℕ → ℝ
  | 0, j => 2 * (c * costA b P 1 j)
  | _ + 1, 0 => 2
  | s + 1, j + 1 =>
      2 * (c * (2 * (R * ((2 * b : ℕ) * ((j + 3) * VcOf (costB s) j + PcOf (costB s) j)))))

lemma costB_nonneg : ∀ s j, 0 ≤ costB b P c R s j
  | 0, j => by unfold costB; have := costA_nonneg b P 1 j; positivity
  | _ + 1, 0 => by unfold costB; norm_num
  | s + 1, j + 1 => by
    unfold costB
    have hV : 0 ≤ VcOf (costB b P c R s) j := by
      unfold VcOf
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => ?_)
      have := costB_nonneg s (j - d); positivity
    have hP : 0 ≤ PcOf (costB b P c R s) j := by
      unfold PcOf
      refine mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => ?_))
      exact costB_nonneg s (j - d)
    positivity

/-! ## The weights and the two sums -/

/-- `β_w = 2^{-depth w/4}`. -/
noncomputable def βD (J : ℕ) (w : DNode J) : ℝ := (Real.sqrt (Real.sqrt 2))⁻¹ ^ (w.1 : ℕ)

lemma βD_ne_zero (J : ℕ) (w : DNode J) : βD J w ≠ 0 := by
  unfold βD
  apply pow_ne_zero
  apply inv_ne_zero
  positivity

lemma βD_sq (J : ℕ) (w : DNode J) : (βD J w) ^ 2 = ((Real.sqrt 2) ^ (w.1 : ℕ))⁻¹ := by
  unfold βD
  rw [← pow_mul, mul_comm, pow_mul, inv_pow, Real.sq_sqrt (Real.sqrt_nonneg 2), inv_pow]

lemma two_pow_eq_sqrt_sq (d : ℕ) : (2 : ℝ) ^ d = Real.sqrt 2 ^ d * Real.sqrt 2 ^ d := by
  rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]

/-- The cell costs at stage `s+1` on the tree below `(j+1, ·)`: depth-`d` internal vertices cost
`4·costB s (j − d)`. -/
noncomputable def tD (s j : ℕ) : DNode j → ℝ :=
  tcost j (fun d => costB b P c R s (j + 1 - d))

lemma tD_eq (s j : ℕ) (w : DNode j) :
    tD b P c R s j w = if (w.1 : ℕ) < j + 1 then 4 * costB b P c R s (j - w.1) else 0 := by
  unfold tD tcost
  split_ifs with h
  · show 4 * costB b P c R s (j + 1 - ((w.1 : ℕ) + 1)) = _
    rw [Nat.add_sub_add_right]
  · rfl

lemma tD_nonneg (s j : ℕ) (w : DNode j) : 0 ≤ tD b P c R s j w :=
  tcost_nonneg j (fun d => costB_nonneg b P c R s _) w

/-- The path sum against `β^{-2}` is at most `Vc`. -/
theorem path_sum_le (s j : ℕ) (v : DNode j) :
    ∑ w ∈ (tnodeTree (j + 1)).path v, tD b P c R s j w / (βD j w) ^ 2 ≤ VcOf (costB b P c R s) j := by
  rw [AncTree.path, Finset.sum_image ((tnodeTree (j + 1)).ancAt_injOn v)]
  have hdep : (tnodeTree (j + 1)).depth v = (v.1 : ℕ) := rfl
  rw [hdep]
  have hterm : ∀ i ∈ Finset.range ((v.1 : ℕ) + 1),
      tD b P c R s j ((tnodeTree (j + 1)).ancAt v i) / (βD j ((tnodeTree (j + 1)).ancAt v i)) ^ 2
        = if i < j + 1 then 4 * costB b P c R s (j - i) * Real.sqrt 2 ^ i else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hfst : (((tnodeTree (j + 1)).ancAt v i).1 : ℕ) = i := tnodeAncAt_fst v (by omega)
    rw [tD_eq, βD_sq, hfst]
    split_ifs
    · rw [div_inv_eq_mul]
    · simp
  rw [Finset.sum_congr rfl hterm]
  unfold VcOf
  rw [Finset.mul_sum]
  -- the terms with `i ≤ j` are among those of `range (j+1)`; the term `i = j+1` vanishes
  have hv : (v.1 : ℕ) + 1 ≤ j + 2 := by have := v.1.isLt; omega
  calc ∑ i ∈ Finset.range ((v.1 : ℕ) + 1),
        (if i < j + 1 then 4 * costB b P c R s (j - i) * Real.sqrt 2 ^ i else 0)
      = ∑ i ∈ Finset.range ((v.1 : ℕ) + 1) with i < j + 1, 4 * costB b P c R s (j - i) * Real.sqrt 2 ^ i := by
        rw [Finset.sum_filter]
    _ ≤ ∑ i ∈ Finset.range (j + 1), 4 * costB b P c R s (j - i) * Real.sqrt 2 ^ i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => ?_
        · intro i hi
          rw [Finset.mem_filter] at hi
          exact Finset.mem_range.2 hi.2
        · have := costB_nonneg b P c R s (j - i); positivity
    _ = ∑ i ∈ Finset.range (j + 1), 4 * (costB b P c R s (j - i) * Real.sqrt 2 ^ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_; ring

/-- The total sum against `β^2` equals `Vc`. -/
theorem all_sum_eq (s j : ℕ) :
    ∑ w : DNode j, tD b P c R s j w * (βD j w) ^ 2 = VcOf (costB b P c R s) j := by
  rw [Fintype.sum_sigma]
  simp only [tD_eq, βD_sq]
  have hd : ∀ d : Fin (j + 2), ∑ ν : Fin (2 ^ (d : ℕ)),
      (if ((⟨d, ν⟩ : DNode j).1 : ℕ) < j + 1 then 4 * costB b P c R s (j - (⟨d, ν⟩ : DNode j).1) else 0)
        * ((Real.sqrt 2 ^ ((⟨d, ν⟩ : DNode j).1 : ℕ))⁻¹)
      = if (d : ℕ) < j + 1 then 4 * costB b P c R s (j - d) * Real.sqrt 2 ^ (d : ℕ) else 0 := by
    intro d
    simp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    split_ifs with h
    · have h2 : Real.sqrt 2 ^ (d : ℕ) ≠ 0 := pow_ne_zero _ (by positivity)
      rw [Nat.cast_pow, Nat.cast_ofNat, two_pow_eq_sqrt_sq]
      field_simp
    · simp
  rw [Finset.sum_congr rfl fun d _ => hd d]
  rw [Fin.sum_univ_eq_sum_range (fun d => if d < j + 1 then 4 * costB b P c R s (j - d) * Real.sqrt 2 ^ d else 0) (j + 2)]
  rw [Finset.sum_range_succ, if_neg (lt_irrefl _), add_zero]
  unfold VcOf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_range] at hd
  rw [if_pos hd]
  ring

/-- The retrieval path cost is at most `Pc`. -/
theorem path_cost_le (s j : ℕ) (v : DNode j) :
    2 * ∑ w ∈ (tnodeTree (j + 1)).path v, tD b P c R s j w ≤ PcOf (costB b P c R s) j := by
  rw [AncTree.path, Finset.sum_image ((tnodeTree (j + 1)).ancAt_injOn v)]
  have hdep : (tnodeTree (j + 1)).depth v = (v.1 : ℕ) := rfl
  rw [hdep]
  have hterm : ∀ i ∈ Finset.range ((v.1 : ℕ) + 1),
      tD b P c R s j ((tnodeTree (j + 1)).ancAt v i)
        = if i < j + 1 then 4 * costB b P c R s (j - i) else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hfst : (((tnodeTree (j + 1)).ancAt v i).1 : ℕ) = i := tnodeAncAt_fst v (by omega)
    rw [tD_eq, hfst]
  rw [Finset.sum_congr rfl hterm]
  unfold PcOf
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [Finset.mul_sum]
  calc ∑ i ∈ Finset.range ((v.1 : ℕ) + 1), (if i < j + 1 then 4 * costB b P c R s (j - i) else 0)
      = ∑ i ∈ Finset.range ((v.1 : ℕ) + 1) with i < j + 1, 4 * costB b P c R s (j - i) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ i ∈ Finset.range (j + 1), 4 * costB b P c R s (j - i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => ?_
        · intro i hi
          rw [Finset.mem_filter] at hi
          exact Finset.mem_range.2 hi.2
        · have := costB_nonneg b P c R s (j - i); positivity

/-! ## The dual of every stage -/

/-- **Every seed's stage summary has a dual of cost `costB s j`.** -/
theorem hasDual_summary2 (hb1 : 1 ≤ b) (hk : ∀ h, 1 ≤ h → 1 ≤ (P h).2) :
    ∀ (s j q : ℕ) (ω : Ω2 b P c R s j),
      HasDual (fun x : Fin N → σ => summary2 letter b P c R s j q ω x) (costB b P c R s j)
  | 0, j, q, ω => by
    simp only [summary2_zero]
    unfold costB
    exact hasDual_amp letter b c _ (costA_nonneg b P 1 j) (fun ω' => hasDual_summary letter hb1 P hk 1 j q ω') ω
  | _ + 1, 0, q, _ => by
    simp only [summary2_succ_zero]
    unfold letterRecN costB
    split_ifs with hq
    · exact hasDual_letterRec ⟨q, hq⟩
    · exact (hasDual_const fun _ _ => rfl).mono (by norm_num)
  | s + 1, j + 1, q, ω => by
    simp only [summary2_succ_succ]
    unfold costB
    have hVc : 0 ≤ VcOf (costB b P c R s) j := by
      unfold VcOf
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => ?_)
      have := costB_nonneg b P c R s (j - d); positivity
    have hPc : 0 ≤ PcOf (costB b P c R s) j := by
      unfold PcOf
      refine mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => ?_))
      exact costB_nonneg b P c R s (j - d)
    refine hasDual_amp letter b c _ (by positivity) (fun ω' => ?_) ω
    have hcell : ∀ v, HasDual (cell j (fun w => summary2 letter b P c R s (j + 1 - w.1)
        (q * 2 ^ (w.1 : ℕ) + w.2) (ω'.1 w)) v) (tD b P c R s j v) :=
      fun v => hasDual_cell j _ (fun d => costB_nonneg b P c R s _)
        (fun w _ => hasDual_summary2 hb1 hk s _ _ (ω'.1 w)) v
    exact hasDual_dblOut letter j _ b (tD_nonneg b P c R s j) hcell hVc
      (fun completed e k => hasDual_decD letter j _ (βD_ne_zero j) (tD_nonneg b P c R s j) hcell _
        (path_sum_le b P c R s j) (all_sum_eq b P c R s j).le completed e k)
      hPc (path_cost_le b P c R s j) ω'.2

end LogRank

end MonoidProduct
