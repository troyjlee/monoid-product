import MonoidProduct.Ordered.LogRankCorrect
import MonoidProduct.Ordered.LogRankCost

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option synthInstance.maxSize 4096

/-!
# Rank doubling for an arbitrary input family (`lem:beta-rank-doubling`)

Fix `N = 2^L`, a breadth bound `b ≥ 1`, a rank `r ≥ 1` and `δ = (1/100)^(L+2)`.  Suppose
every dyadic interval `(j, q)` of the word carries a finite family `F j q ω` of deterministic
record functions, indexed by seeds `ω` with an input-independent weight `w j q`, such that
every output is a truthful record of at most `b` positions inside the interval, every input
gets an `r`-summary except with mass at most `δ`, and every seed's function has a dual of
cost `A·√(2^j)` (`A ≥ 1`).  **The rank-doubling lemma** (`rank_doubling`) gives a family of
the same kind which gets `2r`-summaries except with mass at most `δ`, and whose functions
have duals of cost `5760·b·A·L⁴·√(2^j)` (`eq:beta-rank-doubling`).

The family is explicit (`dblFamily`, with seeds `DblSeed` and weights `dblW`).  A single
position returns its letter.  On `(j+1, q)`, one **copy** (`copyOut`) draws a seed of the
input family for every node of the interval's binary tree, independently with the input
weights, and uniform orderings for the rounds (`copyW`), and runs the seeded rank doubling
`dblOut` of `RankDoubling.lean` with `R` rounds on the input functions at the nodes; the
output is the compressed union of `c` independent copies (`amp`).  The parameters are those
of `eq:beta-doubling-parameters`: `c = L + 2` copies and `R = L + 11` rounds.

* `dblFamily_spec`: every seed gives a truthful record of at most `b` positions inside the
  interval.
* `dblFamily_fail_le`: one copy fails only if one of the `< 2^{L+1}` child summaries fails
  or the thinning fails, so with mass at most `2^{L+1}·δ + 2^{L+1}·2^{-R} ≤ 1/200`
  (`copy_fail_le_of_weight`); the `c` independent copies fail together with mass at most
  `(1/100)^c = δ` (`amp_fail_le_of_weight`).  These two steps are `copy_fail_le` and
  `amp_fail_le` of the uniform seeds, for arbitrary seed weights.
* `hasDual_dblFamily`: a copy's dual is assembled from the duals of the cells, the tree
  searches and the retrievals (`hasDual_copyOut`, for an arbitrary cost profile `G` of the
  input family); for `G j = A·√(2^j)` the search and retrieval costs are at most
  `4(j+1)·A√(2^j)` and `8(j+1)·A√(2^j)`, and `c ≤ 3L`, `R ≤ 12L` (`dblCost_le`).
* `summary2_succ_succ_eq`: the iterated doubling `summary2` of `LogRank.lean` is the doubled
  family of its previous rank, with the same seeds.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

section RankDoublingLemma

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable [DecidableLE M] (letter : σ → M) {N : ℕ} (b : ℕ)

/-! ## Amplification under an arbitrary seed weight -/

open Classical in
/-- **Amplification**: if one copy fails with mass at most `δ` under the seed weight `μ`, the
compressed union of `c` independent copies fails with mass at most `δ^c`. -/
theorem amp_fail_le_of_weight (hst : IsStableOrder M) (hb : IsBreadthBound letter b)
    {Ω' : Type} [Fintype Ω'] {μ : Ω' → ℝ} (hμ : IsWeight μ) (c : ℕ)
    (f : Ω' → (Fin N → σ) → Record N σ) {r j q : ℕ} (x : Fin N → σ)
    (hf : ∀ ω x, (f ω x).Truthful x) (hs : ∀ ω x, (f ω x).supp ⊆ ivl j q) {δ : ℝ}
    (hfail : ∑ ω, μ ω * (if IsSummary letter x b r j q (f ω x) then 0 else 1) ≤ δ) :
    ∑ ω : Fin c → Ω', tupleW μ ω
        * (if IsSummary letter x b r j q (amp letter b c f ω x) then 0 else 1) ≤ δ ^ c := by
  classical
  calc ∑ ω : Fin c → Ω', tupleW μ ω
          * (if IsSummary letter x b r j q (amp letter b c f ω x) then 0 else 1)
      ≤ ∑ ω : Fin c → Ω', tupleW μ ω
          * ∏ i, (if IsSummary letter x b r j q (f (ω i) x) then (0 : ℝ) else 1) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (tupleW_nonneg hμ ω)
        split_ifs with h
        · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
        · rw [Finset.prod_eq_one fun i _ =>
            ite_eq_right fun hi => h (isSummary_amp letter b hst hb c f x hf hs ω i hi)]
    _ = (∑ e, μ e * (if IsSummary letter x b r j q (f e x) then (0 : ℝ) else 1)) ^ c :=
        sum_tupleW_prod (fun e => if IsSummary letter x b r j q (f e x) then (0 : ℝ) else 1) c
    _ ≤ δ ^ c := pow_le_pow_left₀ (Finset.sum_nonneg fun e _ =>
        mul_nonneg (hμ.nonneg e) (by split_ifs <;> norm_num)) hfail c

/-! ## One copy of the doubling under arbitrary child weights -/

/-- The weight of one copy's seed: independent child seeds with the weights `ν`, and
independent uniform orderings for the rounds. -/
noncomputable def copyWt {j : ℕ} {Ω' : DNode j → Type} (ν : ∀ v, Ω' v → ℝ) (R : ℕ)
    (ω' : (∀ v, Ω' v) × (Fin R → Fin (2 * b) → Ord (DNode j))) : ℝ :=
  piWD ν ω'.1 * tupleW (tupleW (unifW (Ord (DNode j)))) ω'.2

lemma isWeight_copyWt {j : ℕ} {Ω' : DNode j → Type} [∀ v, Fintype (Ω' v)]
    {ν : ∀ v, Ω' v → ℝ} (hν : ∀ v, IsWeight (ν v)) (R : ℕ) : IsWeight (copyWt b ν R) := by
  have hT : IsWeight (tupleW (tupleW (unifW (Ord (DNode j))) (k := 2 * b)) (k := R)) :=
    isWeight_tupleW (isWeight_tupleW (isWeight_unifW _) _) _
  refine ⟨fun ω' => mul_nonneg (piWD_nonneg hν _) (hT.nonneg _), ?_⟩
  unfold copyWt
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, hT.sum_one, mul_one]
  exact sum_piWD hν

open Classical in
/-- **One copy fails only if a child fails or the thinning fails.**  With independent child
seeds whose summaries fail with mass `≤ δ` under arbitrary weights `ν`, and independent
uniform orderings, one copy of the rank doubling fails with mass at most
`|DNode j|·δ + |DNode j|·(1/2)^R`. -/
theorem copy_fail_le_of_weight (hst : IsStableOrder M) (hb : IsBreadthBound letter b)
    (hb1 : 1 ≤ b) {j q : ℕ} (x : Fin N → σ) {r : ℕ} (hr : 1 ≤ r) {Ω' : DNode j → Type}
    [∀ v, Fintype (Ω' v)] {ν : ∀ v, Ω' v → ℝ} (hν : ∀ v, IsWeight (ν v))
    (S : ∀ v, Ω' v → (Fin N → σ) → Record N σ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hS : ∀ v : DNode j, 1 ≤ (v.1 : ℕ) →
      ∑ t, ν v t * (if IsSummary letter x b r (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2)
        (S v t x) then 0 else 1) ≤ δ)
    (R : ℕ) :
    ∑ ω', copyWt b ν R ω'
        * (if IsSummary letter x b (2 * r) (j + 1) q
            (dblOut letter j (fun v => S v (ω'.1 v)) b ω'.2 x) then 0 else 1)
      ≤ Fintype.card (DNode j) * δ + Fintype.card (DNode j) * (1 / 2) ^ R := by
  have hT : IsWeight (tupleW (tupleW (unifW (Ord (DNode j))) (k := 2 * b)) (k := R)) :=
    isWeight_tupleW (isWeight_tupleW (isWeight_unifW _) _) _
  -- the children are summaries
  let OK : (∀ v, Ω' v) → Prop := fun ωc => ∀ v : DNode j, 1 ≤ (v.1 : ℕ) →
    IsSummary letter x b r (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2) (S v (ωc v) x)
  -- the failure indicator of the copy
  let G : (∀ v, Ω' v) → (Fin R → Fin (2 * b) → Ord (DNode j)) → ℝ := fun ωc rows =>
    if IsSummary letter x b (2 * r) (j + 1) q (dblOut letter j (fun v => S v (ωc v)) b rows x)
      then 0 else 1
  have hG01 : ∀ ωc rows, 0 ≤ G ωc rows ∧ G ωc rows ≤ 1 := fun ωc rows => by
    simp only [G]; split_ifs <;> norm_num
  have hpt : ∀ ωc rows,
      G ωc rows ≤ (if OK ωc then 0 else 1) + (if OK ωc then G ωc rows else 0) := by
    intro ωc rows
    by_cases h : OK ωc
    · rw [ite_eq_left h, ite_eq_left h, zero_add]
    · rw [ite_eq_right h, ite_eq_right h, add_zero]
      exact (hG01 ωc rows).2
  -- the union bound over the children
  have hA : ∑ ωc, piWD ν ωc * (if OK ωc then 0 else 1) ≤ Fintype.card (DNode j) * δ := by
    have hU := sum_piWD_exists_le hν (fun v t => 1 ≤ (v.1 : ℕ) ∧ ¬ IsSummary letter x b r
      (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2) (S v t x))
    have heq : ∀ ωc, (if OK ωc then (0 : ℝ) else 1) = if ∃ v, 1 ≤ (v.1 : ℕ) ∧
        ¬ IsSummary letter x b r (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2) (S v (ωc v) x)
          then 1 else 0 := by
      intro ωc
      by_cases h : OK ωc
      · rw [ite_eq_left h, ite_eq_right]
        rintro ⟨v, hv, hn⟩
        exact hn (h v hv)
      · rw [ite_eq_right h, ite_eq_left]
        by_contra hne
        exact h fun v hv => by_contra fun hn => hne ⟨v, hv, hn⟩
    simp only [heq]
    refine hU.trans ?_
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : 1 ≤ (v.1 : ℕ)
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun t _ => ?_)) (hS v hv)
      congr 1
      by_cases hs : IsSummary letter x b r (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2) (S v t x)
      · rw [ite_eq_right (fun h => h.2 hs), ite_eq_left hs]
      · rw [ite_eq_left ⟨hv, hs⟩, ite_eq_right hs]
    · refine le_trans (le_of_eq (Finset.sum_eq_zero fun t _ => ?_)) hδ
      rw [ite_eq_right (fun h => hv h.1), mul_zero]
  -- the thinning bound given correct children
  have hB : ∀ ωc, ∑ rows, tupleW (tupleW (unifW (Ord (DNode j)))) rows
      * (if OK ωc then G ωc rows else 0) ≤ Fintype.card (DNode j) * (1 / 2) ^ R := by
    intro ωc
    by_cases h : OK ωc
    · simp only [ite_eq_left h]
      exact dbl_fail_le letter j q (fun v => S v (ωc v)) x hst hb hb1 hr h R
    · simp only [ite_eq_right h, mul_zero, Finset.sum_const_zero]
      positivity
  calc ∑ ω', copyWt b ν R ω' * G ω'.1 ω'.2
      = ∑ ωc, ∑ rows, piWD ν ωc * tupleW (tupleW (unifW (Ord (DNode j)))) rows * G ωc rows := by
        rw [Fintype.sum_prod_type]
        rfl
    _ ≤ ∑ ωc, ∑ rows, piWD ν ωc * tupleW (tupleW (unifW (Ord (DNode j)))) rows
          * ((if OK ωc then 0 else 1) + (if OK ωc then G ωc rows else 0)) :=
        Finset.sum_le_sum fun ωc _ => Finset.sum_le_sum fun rows _ =>
          mul_le_mul_of_nonneg_left (hpt ωc rows)
            (mul_nonneg (piWD_nonneg hν ωc) (hT.nonneg rows))
    _ = ∑ ωc, piWD ν ωc * (if OK ωc then 0 else 1)
          + ∑ ωc, piWD ν ωc * ∑ rows, tupleW (tupleW (unifW (Ord (DNode j)))) rows
            * (if OK ωc then G ωc rows else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ωc _ => ?_
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · rw [← Finset.sum_mul, ← Finset.mul_sum, hT.sum_one, mul_one]
        · exact Finset.sum_congr rfl fun rows _ => by ring
    _ ≤ Fintype.card (DNode j) * δ
          + ∑ ωc, piWD ν ωc * (Fintype.card (DNode j) * (1 / 2) ^ R) :=
        add_le_add hA (Finset.sum_le_sum fun ωc _ =>
          mul_le_mul_of_nonneg_left (hB ωc) (piWD_nonneg hν ωc))
    _ = Fintype.card (DNode j) * δ + Fintype.card (DNode j) * (1 / 2) ^ R := by
        rw [← Finset.sum_mul, sum_piWD hν, one_mul]

/-! ## The cell costs of an arbitrary cost profile -/

variable (G : ℕ → ℝ)

/-- The cell costs below `(j+1, ·)` when every child function of log-length `j'` has a dual
of cost `G j'`: `4·G (j − d)` at the internal vertices of depth `d`, `0` at the leaves. -/
noncomputable def tG (j : ℕ) : DNode j → ℝ := tcost j (fun d => G (j + 1 - d))

lemma tG_eq (j : ℕ) (v : DNode j) :
    tG G j v = if (v.1 : ℕ) < j + 1 then 4 * G (j - v.1) else 0 := by
  unfold tG tcost
  split_ifs
  · change 4 * G (j + 1 - ((v.1 : ℕ) + 1)) = _
    rw [Nat.add_sub_add_right]
  · rfl

lemma tG_nonneg (hG : ∀ d, 0 ≤ G d) (j : ℕ) (v : DNode j) : 0 ≤ tG G j v :=
  tcost_nonneg j (fun _ => hG _) v

/-- The path sum of the cell costs against `β^{-2}` is at most `VcOf G j`. -/
theorem path_sum_le_of (hG : ∀ d, 0 ≤ G d) (j : ℕ) (v : DNode j) :
    ∑ w ∈ (tnodeTree (j + 1)).path v, tG G j w / (βD j w) ^ 2 ≤ VcOf G j := by
  rw [AncTree.path, Finset.sum_image ((tnodeTree (j + 1)).ancAt_injOn v)]
  have hdep : (tnodeTree (j + 1)).depth v = (v.1 : ℕ) := rfl
  rw [hdep]
  have hterm : ∀ i ∈ Finset.range ((v.1 : ℕ) + 1),
      tG G j ((tnodeTree (j + 1)).ancAt v i) / (βD j ((tnodeTree (j + 1)).ancAt v i)) ^ 2
        = if i < j + 1 then 4 * G (j - i) * Real.sqrt 2 ^ i else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hfst : (((tnodeTree (j + 1)).ancAt v i).1 : ℕ) = i := tnodeAncAt_fst v (by omega)
    rw [tG_eq, βD_sq, hfst]
    split_ifs
    · rw [div_inv_eq_mul]
    · simp
  rw [Finset.sum_congr rfl hterm]
  unfold VcOf
  rw [Finset.mul_sum]
  calc ∑ i ∈ Finset.range ((v.1 : ℕ) + 1),
        (if i < j + 1 then 4 * G (j - i) * Real.sqrt 2 ^ i else 0)
      = ∑ i ∈ Finset.range ((v.1 : ℕ) + 1) with i < j + 1,
          4 * G (j - i) * Real.sqrt 2 ^ i := by
        rw [Finset.sum_filter]
    _ ≤ ∑ i ∈ Finset.range (j + 1), 4 * G (j - i) * Real.sqrt 2 ^ i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => ?_
        · intro i hi
          rw [Finset.mem_filter] at hi
          exact Finset.mem_range.2 hi.2
        · have := hG (j - i); positivity
    _ = ∑ i ∈ Finset.range (j + 1), 4 * (G (j - i) * Real.sqrt 2 ^ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_; ring

/-- The total sum of the cell costs against `β^2` equals `VcOf G j`. -/
theorem all_sum_eq_of (j : ℕ) : ∑ w : DNode j, tG G j w * (βD j w) ^ 2 = VcOf G j := by
  rw [Fintype.sum_sigma]
  simp only [tG_eq, βD_sq]
  have hd : ∀ d : Fin (j + 2), ∑ ν : Fin (2 ^ (d : ℕ)),
      (if ((⟨d, ν⟩ : DNode j).1 : ℕ) < j + 1 then 4 * G (j - (⟨d, ν⟩ : DNode j).1) else 0)
        * ((Real.sqrt 2 ^ ((⟨d, ν⟩ : DNode j).1 : ℕ))⁻¹)
      = if (d : ℕ) < j + 1 then 4 * G (j - d) * Real.sqrt 2 ^ (d : ℕ) else 0 := by
    intro d
    simp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    split_ifs
    · have h2 : Real.sqrt 2 ^ (d : ℕ) ≠ 0 := pow_ne_zero _ (by positivity)
      rw [Nat.cast_pow, Nat.cast_ofNat, two_pow_eq_sqrt_sq]
      field_simp
    · simp
  rw [Finset.sum_congr rfl fun d _ => hd d]
  rw [Fin.sum_univ_eq_sum_range
    (fun d => if d < j + 1 then 4 * G (j - d) * Real.sqrt 2 ^ d else 0) (j + 2)]
  rw [Finset.sum_range_succ, ite_eq_right (lt_irrefl _), add_zero]
  unfold VcOf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_range] at hd
  rw [ite_eq_left hd]
  ring

/-- The retrieval cost, twice the path sum of the cell costs, is at most `PcOf G j`. -/
theorem path_cost_le_of (hG : ∀ d, 0 ≤ G d) (j : ℕ) (v : DNode j) :
    2 * ∑ w ∈ (tnodeTree (j + 1)).path v, tG G j w ≤ PcOf G j := by
  rw [AncTree.path, Finset.sum_image ((tnodeTree (j + 1)).ancAt_injOn v)]
  have hdep : (tnodeTree (j + 1)).depth v = (v.1 : ℕ) := rfl
  rw [hdep]
  have hterm : ∀ i ∈ Finset.range ((v.1 : ℕ) + 1),
      tG G j ((tnodeTree (j + 1)).ancAt v i) = if i < j + 1 then 4 * G (j - i) else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hfst : (((tnodeTree (j + 1)).ancAt v i).1 : ℕ) = i := tnodeAncAt_fst v (by omega)
    rw [tG_eq, hfst]
  rw [Finset.sum_congr rfl hterm]
  unfold PcOf
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [Finset.mul_sum]
  calc ∑ i ∈ Finset.range ((v.1 : ℕ) + 1), (if i < j + 1 then 4 * G (j - i) else 0)
      = ∑ i ∈ Finset.range ((v.1 : ℕ) + 1) with i < j + 1, 4 * G (j - i) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ i ∈ Finset.range (j + 1), 4 * G (j - i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => ?_
        · intro i hi
          rw [Finset.mem_filter] at hi
          exact Finset.mem_range.2 hi.2
        · have := hG (j - i); positivity

/-- **The cost of one copy, bounded** for the cost profile `G j = A·√(2^j)` on intervals of
log-length `j + 1 ≤ L`, with `c = L + 2` copies of `R = L + 11` rounds. -/
theorem dblCost_le {L j : ℕ} (hL : 1 ≤ L) (hj : j + 1 ≤ L) {A : ℝ} (hA : 0 ≤ A) :
    2 * (((L + 2 : ℕ) : ℝ) * (2 * (((L + 11 : ℕ) : ℝ) * (((2 * b : ℕ) : ℝ)
        * (((j : ℝ) + 3) * VcOf (fun d => A * Real.sqrt (2 ^ d)) j
          + PcOf (fun d => A * Real.sqrt (2 ^ d)) j)))))
      ≤ 5760 * b * A * L ^ 4 * Real.sqrt (2 ^ (j + 1)) := by
  set X := A * Real.sqrt 2 ^ j with hX
  have hX0 : 0 ≤ X := by positivity
  have hterm : ∀ d ∈ Finset.range (j + 1),
      A * Real.sqrt (2 ^ (j - d)) * Real.sqrt 2 ^ d = X := by
    intro d hd
    rw [Finset.mem_range] at hd
    rw [sqrt_two_pow, hX, mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
  have hterm' : ∀ d ∈ Finset.range (j + 1), A * Real.sqrt (2 ^ (j - d)) ≤ X := by
    intro d _
    rw [sqrt_two_pow, hX]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_sqrt_two (Nat.sub_le j d)) hA
  have hV : VcOf (fun d => A * Real.sqrt (2 ^ d)) j = 4 * (((j : ℝ) + 1) * X) := by
    unfold VcOf
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hP : PcOf (fun d => A * Real.sqrt (2 ^ d)) j ≤ 8 * (((j : ℝ) + 1) * X) := by
    unfold PcOf
    calc 2 * (4 * ∑ d ∈ Finset.range (j + 1), A * Real.sqrt (2 ^ (j - d)))
        ≤ 2 * (4 * ∑ d ∈ Finset.range (j + 1), X) := by
          gcongr with d hd
          exact hterm' d hd
      _ = 8 * (((j : ℝ) + 1) * X) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hjL : (j : ℝ) + 1 ≤ L := by exact_mod_cast hj
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hM : ((j : ℝ) + 3) * VcOf (fun d => A * Real.sqrt (2 ^ d)) j
      + PcOf (fun d => A * Real.sqrt (2 ^ d)) j ≤ 20 * (L : ℝ) ^ 2 * X := by
    have h2 : ((j : ℝ) + 1) * ((j : ℝ) + 5) ≤ 5 * (L : ℝ) ^ 2 := by nlinarith
    rw [hV]
    calc ((j : ℝ) + 3) * (4 * (((j : ℝ) + 1) * X)) + PcOf (fun d => A * Real.sqrt (2 ^ d)) j
        ≤ ((j : ℝ) + 3) * (4 * (((j : ℝ) + 1) * X)) + 8 * (((j : ℝ) + 1) * X) := by linarith
      _ = 4 * (((j : ℝ) + 1) * ((j : ℝ) + 5)) * X := by ring
      _ ≤ 4 * (5 * (L : ℝ) ^ 2) * X := by gcongr
      _ = 20 * (L : ℝ) ^ 2 * X := by ring
  have hM0 : 0 ≤ ((j : ℝ) + 3) * VcOf (fun d => A * Real.sqrt (2 ^ d)) j
      + PcOf (fun d => A * Real.sqrt (2 ^ d)) j := by
    have h1 := VcOf_nonneg (A := fun d => A * Real.sqrt (2 ^ d)) (fun d => by positivity) j
    have h2 := PcOf_nonneg (A := fun d => A * Real.sqrt (2 ^ d)) (fun d => by positivity) j
    positivity
  have hcR : ((L + 2 : ℕ) : ℝ) * ((L + 11 : ℕ) : ℝ) ≤ 36 * (L : ℝ) ^ 2 := by
    push_cast
    nlinarith
  calc 2 * (((L + 2 : ℕ) : ℝ) * (2 * (((L + 11 : ℕ) : ℝ) * (((2 * b : ℕ) : ℝ)
        * (((j : ℝ) + 3) * VcOf (fun d => A * Real.sqrt (2 ^ d)) j
          + PcOf (fun d => A * Real.sqrt (2 ^ d)) j)))))
      = 8 * (b : ℝ) * ((((L + 2 : ℕ) : ℝ) * ((L + 11 : ℕ) : ℝ))
          * (((j : ℝ) + 3) * VcOf (fun d => A * Real.sqrt (2 ^ d)) j
            + PcOf (fun d => A * Real.sqrt (2 ^ d)) j)) := by
        push_cast
        ring
    _ ≤ 8 * (b : ℝ) * ((36 * (L : ℝ) ^ 2) * (20 * (L : ℝ) ^ 2 * X)) := by
        gcongr
    _ = 5760 * b * A * L ^ 4 * Real.sqrt 2 ^ j := by
        rw [hX]
        ring
    _ ≤ 5760 * b * A * L ^ 4 * Real.sqrt (2 ^ (j + 1)) := by
        rw [sqrt_two_pow]
        gcongr
        · exact one_le_sqrt_two
        · omega

/-! ## The doubled family -/

variable (Ω : ℕ → ℕ → Type)

/-- **The seed of one copy** on `(j+1, q)`: a seed of the input family for every node of the
interval's binary tree (the root's is not read) and the orderings of the `R` rounds. -/
abbrev CopySeed (R j q : ℕ) : Type :=
  (∀ v : DNode j, Ω (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2))
    × (Fin R → Fin (2 * b) → Ord (DNode j))

/-- **The seeds of the doubled family**: none on a single position, `c` copy seeds on a
longer interval. -/
def DblSeed (c R : ℕ) : ℕ → ℕ → Type
  | 0, _ => Unit
  | j + 1, q => Fin c → CopySeed b Ω R j q

instance instFintypeDblSeed [∀ j q, Fintype (Ω j q)] {c R j q : ℕ} :
    Fintype (DblSeed b Ω c R j q) :=
  match j with
  | 0 => inferInstanceAs (Fintype Unit)
  | j + 1 => inferInstanceAs (Fintype (Fin c → CopySeed b Ω R j q))

instance instDecidableEqDblSeed [∀ j q, DecidableEq (Ω j q)] {c R j q : ℕ} :
    DecidableEq (DblSeed b Ω c R j q) :=
  match j with
  | 0 => inferInstanceAs (DecidableEq Unit)
  | j + 1 => inferInstanceAs (DecidableEq (Fin c → CopySeed b Ω R j q))

instance instNonemptyDblSeed [∀ j q, Nonempty (Ω j q)] {c R j q : ℕ} :
    Nonempty (DblSeed b Ω c R j q) :=
  match j with
  | 0 => inferInstanceAs (Nonempty Unit)
  | j + 1 => inferInstanceAs (Nonempty (Fin c → CopySeed b Ω R j q))

/-- The weight of a copy seed: the input weights at the nodes, independently, and uniform
orderings. -/
noncomputable abbrev copyW (w : ∀ j q, Ω j q → ℝ) (R j q : ℕ) : CopySeed b Ω R j q → ℝ :=
  copyWt b (fun v : DNode j => w (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2)) R

/-- **The seed weights of the doubled family**: `c` independent copy seeds. -/
noncomputable def dblW (w : ∀ j q, Ω j q → ℝ) (c R : ℕ) : ∀ j q, DblSeed b Ω c R j q → ℝ
  | 0, _, _ => 1
  | j + 1, q, ω => tupleW (copyW b Ω w R j q) ω

/-- **The seed weights are input-independent probability weights.** -/
theorem isWeight_dblW [∀ j q, Fintype (Ω j q)] {w : ∀ j q, Ω j q → ℝ}
    (hw : ∀ j q, IsWeight (w j q)) (c R : ℕ) : ∀ j q, IsWeight (dblW b Ω w c R j q)
  | 0, _ => ⟨fun _ => zero_le_one, by
      change ∑ _ : Unit, (1 : ℝ) = 1
      simp⟩
  | j + 1, q => by
    classical
    change IsWeight (tupleW (copyW b Ω w R j q) (k := c))
    exact isWeight_tupleW (isWeight_copyWt b
      (fun v : DNode j => hw (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2)) R) c

/-- **One copy of the doubling** on `(j+1, q)`: the seeded rank doubling `dblOut` on the
input functions at the nodes of the interval's binary tree. -/
noncomputable def copyOut (F : ∀ j q, Ω j q → (Fin N → σ) → Record N σ) (R j q : ℕ)
    (ω' : CopySeed b Ω R j q) : (Fin N → σ) → Record N σ :=
  dblOut letter j (fun v => F (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2) (ω'.1 v)) b ω'.2

/-- **The doubled family**: the letter on a single position, the compressed union of `c`
independent copies of the doubling on a longer interval. -/
noncomputable def dblFamily (F : ∀ j q, Ω j q → (Fin N → σ) → Record N σ) (c R : ℕ) :
    ∀ j q, DblSeed b Ω c R j q → (Fin N → σ) → Record N σ
  | 0, q, _, x => letterRecN x q
  | j + 1, q, ω, x => amp letter b c (copyOut letter b Ω F R j q) ω x

lemma dblFamily_zero (F : ∀ j q, Ω j q → (Fin N → σ) → Record N σ) (c R q : ℕ)
    (ω : DblSeed b Ω c R 0 q) (x : Fin N → σ) :
    dblFamily letter b Ω F c R 0 q ω x = letterRecN x q := rfl

lemma dblFamily_succ (F : ∀ j q, Ω j q → (Fin N → σ) → Record N σ) (c R j q : ℕ)
    (ω : DblSeed b Ω c R (j + 1) q) (x : Fin N → σ) :
    dblFamily letter b Ω F c R (j + 1) q ω x = amp letter b c (copyOut letter b Ω F R j q) ω x :=
  rfl

/-! ## The three properties -/

variable {Ω} {F : ∀ j q, Ω j q → (Fin N → σ) → Record N σ}

/-- **Every seed gives a truthful record of at most `b` positions inside the interval.** -/
theorem dblFamily_spec (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b)
    (hF : ∀ j q, (q + 1) * 2 ^ j ≤ N → ∀ ω x,
      (F j q ω x).Truthful x ∧ (F j q ω x).supp ⊆ ivl j q) (c R : ℕ) :
    ∀ j q, (q + 1) * 2 ^ j ≤ N → ∀ ω x,
      (dblFamily letter b Ω F c R j q ω x).Truthful x
        ∧ (dblFamily letter b Ω F c R j q ω x).supp ⊆ ivl j q
        ∧ (dblFamily letter b Ω F c R j q ω x).supp.card ≤ b
  | 0, q, hq, ω, x => by
    have hqN : q < N := by simpa using hq
    rw [dblFamily_zero, letterRecN, dite_eq_left hqN]
    exact ⟨letterRec_truthful x _, by rw [supp_letterRec, ivl_zero q hqN],
      by rw [supp_letterRec, Finset.card_singleton]; exact hb1⟩
  | j + 1, q, hq, ω, x => by
    rw [dblFamily_succ]
    refine ⟨amp_truthful letter b c _ (fun ω' x => ?_) ω x,
      supp_amp_subset letter b hb c _ _ (fun ω' x => ?_) ω x, card_amp_le letter b hb c _ ω x⟩
    · exact dblOut_truthful letter j _ b x (fun v _ => (hF _ _ (child_len_le hq v) _ x).1) ω'.2
    · exact supp_dblOut_subset letter j q _ x hb
        (fun v _ => (hF _ _ (child_len_le hq v) _ x).2) ω'.2

/-- The log-length of a dyadic interval of a word of length `N ≤ 2^L` is at most `L`. -/
lemma log_le_of_fits {L j q : ℕ} (hN : N ≤ 2 ^ L) (hq : (q + 1) * 2 ^ j ≤ N) : j ≤ L := by
  have h : 2 ^ j ≤ 2 ^ L :=
    le_trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos q)) (hq.trans hN)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

open Classical in
/-- **The doubled family fails with mass at most `δ = (1/100)^(L+2)`** when the input family
does: one copy fails with mass at most `2^{L+1}·δ + 2^{L+1}·2^{-(L+11)} ≤ 1/200`, and the
`L + 2` independent copies fail together with mass at most `(1/100)^(L+2)`. -/
theorem dblFamily_fail_le [∀ j q, Fintype (Ω j q)] (hst : IsStableOrder M)
    (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) {L r : ℕ} (hr : 1 ≤ r) (hN : N ≤ 2 ^ L)
    {w : ∀ j q, Ω j q → ℝ} (hw : ∀ j q, IsWeight (w j q))
    (hF : ∀ j q, (q + 1) * 2 ^ j ≤ N → ∀ ω x,
      (F j q ω x).Truthful x ∧ (F j q ω x).supp ⊆ ivl j q)
    (hfail : ∀ j q, (q + 1) * 2 ^ j ≤ N → ∀ x,
      ∑ ω, w j q ω * (if IsSummary letter x b r j q (F j q ω x) then 0 else 1)
        ≤ (1 / 100) ^ (L + 2)) :
    ∀ j q, (q + 1) * 2 ^ j ≤ N → ∀ x,
      ∑ ω, dblW b Ω w (L + 2) (L + 11) j q ω
          * (if IsSummary letter x b (2 * r) j q
              (dblFamily letter b Ω F (L + 2) (L + 11) j q ω x) then 0 else 1)
        ≤ (1 / 100) ^ (L + 2)
  | 0, q, hq, x => by
    have hqN : q < N := by simpa using hq
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun ω _ => ?_)) (by positivity)
    rw [dblFamily_zero, letterRecN, dite_eq_left hqN,
      ite_eq_left (isSummary_letterRec letter hst x hb1 _ q hqN), mul_zero]
  | j + 1, q, hq, x => by
    have hjL : j + 1 ≤ L := log_le_of_fits hN hq
    have hcard : (Fintype.card (DNode j) : ℝ) ≤ 2 ^ (L + 1) := by
      have h := card_DNode_lt j
      have h2 : 2 ^ (j + 2) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast (h.trans_le h2).le
    have hA : (Fintype.card (DNode j) : ℝ) * (1 / 100) ^ (L + 2) ≤ 1 / 400 := by
      have h1 : ((2 : ℝ) / 100) ^ (L + 1) ≤ 2 / 100 :=
        pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
      calc (Fintype.card (DNode j) : ℝ) * (1 / 100) ^ (L + 2)
          ≤ 2 ^ (L + 1) * (1 / 100) ^ (L + 2) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = ((2 : ℝ) / 100) ^ (L + 1) * (1 / 100) := by
            simp only [div_pow, one_pow]
            rw [pow_succ (100 : ℝ) (L + 1)]
            field_simp
        _ ≤ 2 / 100 * (1 / 100) := by gcongr
        _ ≤ 1 / 400 := by norm_num
    have hB : (Fintype.card (DNode j) : ℝ) * (1 / 2) ^ (L + 11) ≤ 1 / 400 := by
      calc (Fintype.card (DNode j) : ℝ) * (1 / 2) ^ (L + 11)
          ≤ 2 ^ (L + 1) * (1 / 2) ^ (L + 11) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 1 / 1024 := by
            rw [show L + 11 = (L + 1) + 10 by ring, pow_add (1 / 2 : ℝ) (L + 1) 10, ← mul_assoc,
              ← mul_pow]
            norm_num
        _ ≤ 1 / 400 := by norm_num
    have hcopy : ∑ ω', copyW b Ω w (L + 11) j q ω'
        * (if IsSummary letter x b (2 * r) (j + 1) q (copyOut letter b Ω F (L + 11) j q ω' x)
          then 0 else 1) ≤ 1 / 200 := by
      refine le_trans (copy_fail_le_of_weight letter b hst hb hb1 x hr
        (fun v : DNode j => hw (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2))
        (fun v t => F (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2) t) (by positivity)
        (fun v _ => hfail _ _ (child_len_le hq v) x) (L + 11)) ?_
      linarith
    have hamp := amp_fail_le_of_weight letter b hst hb
      (isWeight_copyWt b (fun v : DNode j => hw (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2)) _)
      (L + 2) (copyOut letter b Ω F (L + 11) j q) x
      (fun ω' x => dblOut_truthful letter j _ b x
        (fun v _ => (hF _ _ (child_len_le hq v) _ x).1) ω'.2)
      (fun ω' x => supp_dblOut_subset letter j q _ x hb
        (fun v _ => (hF _ _ (child_len_le hq v) _ x).2) ω'.2) hcopy
    exact hamp.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)

/-- **One copy's dual** for an input family whose functions on intervals of log-length `j'`
have duals of cost `G j'`. -/
theorem hasDual_copyOut {G : ℕ → ℝ} (hG : ∀ d, 0 ≤ G d)
    (hF : ∀ j q, (q + 1) * 2 ^ j ≤ N → ∀ ω, HasDual (F j q ω) (G j)) {R j q : ℕ}
    (hq : (q + 1) * 2 ^ (j + 1) ≤ N) (ω' : CopySeed b Ω R j q) :
    HasDual (copyOut letter b Ω F R j q ω')
      (2 * (R * ((2 * b : ℕ) * ((j + 3) * VcOf G j + PcOf G j)))) := by
  have hcell : ∀ v, HasDual (cell j (fun v => F (j + 1 - v.1) (q * 2 ^ (v.1 : ℕ) + v.2)
      (ω'.1 v)) v) (tG G j v) :=
    fun v => hasDual_cell j _ (Acost := fun d => G (j + 1 - d)) (fun _ => hG _)
      (fun u _ => hF _ _ (child_len_le hq u) _) v
  exact hasDual_dblOut letter j _ b (tG_nonneg G hG j) hcell (VcOf_nonneg hG j)
    (fun completed e k => hasDual_decD letter j _ (βD_ne_zero j) (tG_nonneg G hG j) hcell _
      (path_sum_le_of G hG j) (all_sum_eq_of G j).le completed e k)
    (PcOf_nonneg hG j) (path_cost_le_of G hG j) ω'.2

/-- **Every seed's function has a dual of cost `5760·b·A·L⁴·√(2^j)`** when the input
family's functions have duals of cost `A·√(2^j)`. -/
theorem hasDual_dblFamily (hb1 : 1 ≤ b) {L : ℕ} (hL : 1 ≤ L) (hN : N ≤ 2 ^ L) {A : ℝ}
    (hA : 1 ≤ A)
    (hF : ∀ j q, (q + 1) * 2 ^ j ≤ N → ∀ ω, HasDual (F j q ω) (A * Real.sqrt (2 ^ j))) :
    ∀ j q, (q + 1) * 2 ^ j ≤ N → ∀ ω,
      HasDual (dblFamily letter b Ω F (L + 2) (L + 11) j q ω)
        (5760 * b * A * L ^ 4 * Real.sqrt (2 ^ j))
  | 0, q, hq, ω => by
    have hqN : q < N := by simpa using hq
    have h : HasDual (dblFamily letter b Ω F (L + 2) (L + 11) 0 q ω) 2 :=
      (hasDual_letterRec ⟨q, hqN⟩).ofEq fun x => by
        rw [dblFamily_zero, letterRecN, dite_eq_left hqN]
    refine h.mono ?_
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hL' : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hL)
    rw [pow_zero, Real.sqrt_one, mul_one]
    nlinarith [mul_le_mul hb' hA zero_le_one (by positivity),
      mul_le_mul (mul_le_mul hb' hA zero_le_one (by positivity)) hL' zero_le_one (by positivity)]
  | j + 1, q, hq, ω => by
    have hjL : j + 1 ≤ L := log_le_of_fits hN hq
    have hA0 : 0 ≤ A := by linarith
    have hG : ∀ d, 0 ≤ A * Real.sqrt (2 ^ d) := fun d => by positivity
    have hT : 0 ≤ 2 * ((L + 11 : ℕ) * ((2 * b : ℕ) * ((j + 3)
        * VcOf (fun d => A * Real.sqrt (2 ^ d)) j + PcOf (fun d => A * Real.sqrt (2 ^ d)) j))) := by
      have := VcOf_nonneg hG j
      have := PcOf_nonneg hG j
      positivity
    have h := hasDual_amp letter b (L + 2) _ hT
      (fun ω' => hasDual_copyOut letter b hG hF (R := L + 11) hq ω') ω
    exact (h.ofEq fun x => (dblFamily_succ letter b Ω F _ _ j q ω x).symm).mono
      (dblCost_le b hL hjL hA0)

/-! ## The iterated doubling of `LogRank.lean` -/

/-- **The iterated doubling is built from the doubled family**: on intervals of length at
least two, the rank-`2^{s+1}` summaries `summary2 (s + 1)` are the doubled family of the
rank-`2^s` summaries `summary2 s`, with the same seeds. -/
theorem summary2_succ_succ_eq (P : MParams) (c R s j q : ℕ) (ω : Ω2 b P c R (s + 1) (j + 1))
    (x : Fin N → σ) :
    summary2 letter b P c R (s + 1) (j + 1) q ω x
      = dblFamily letter b (fun j _ => Ω2 b P c R s j)
          (fun j q => summary2 letter b P c R s j q) c R (j + 1) q ω x := rfl

/-- On single positions both families return the letter. -/
theorem summary2_succ_zero_eq (P : MParams) (c R s q : ℕ) (ω : Ω2 b P c R (s + 1) 0)
    (x : Fin N → σ) :
    summary2 letter b P c R (s + 1) 0 q ω x
      = dblFamily letter b (fun j _ => Ω2 b P c R s j)
          (fun j q => summary2 letter b P c R s j q) c R 0 q ω x := rfl

/-! ## The rank-doubling lemma -/

open Classical in
/-- **The rank-doubling lemma** (`lem:beta-rank-doubling`).  Let `N = 2^L` with `L ≥ 1`, let
`b ≥ 1` be a breadth bound, `r ≥ 1` and `A ≥ 1`.  Suppose every dyadic interval `(j, q)` of
the word has a finite family `F j q ω` of record functions, indexed by seeds with an
input-independent weight `w j q`, such that (1) every output is a truthful record of at most
`b` positions inside the interval, (2) for every input the output is an `r`-summary except
with mass at most `δ = (1/100)^(L+2)`, and (3) every seed's function has a dual of cost
`A·√(2^j)`.  Then every dyadic interval has such a family whose outputs are `2r`-summaries
except with mass at most `δ`, and whose functions have duals of cost `5760·b·A·L⁴·√(2^j)`
(`eq:beta-rank-doubling` with `C = 5760`).  The family is `dblFamily` with `c = L + 2` copies
and `R = L + 11` rounds, and its weights are `dblW`. -/
theorem rank_doubling (hst : IsStableOrder M) (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b)
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
        ∧ ∀ ω, HasDual (F' j q ω) (5760 * b * A * L ^ 4 * Real.sqrt (2 ^ j)) := by
  have hF : ∀ j q, (q + 1) * 2 ^ j ≤ 2 ^ L → ∀ ω x,
      (F j q ω x).Truthful x ∧ (F j q ω x).supp ⊆ ivl j q :=
    fun j q hq ω x => ⟨(hrec j q hq ω x).1, (hrec j q hq ω x).2.1⟩
  exact ⟨DblSeed b Ω (L + 2) (L + 11), fun _ _ => inferInstance, fun _ _ => inferInstance,
    fun _ _ => inferInstance, dblW b Ω w (L + 2) (L + 11),
    dblFamily letter b Ω F (L + 2) (L + 11), isWeight_dblW b Ω hw _ _, fun j q hq =>
      ⟨dblFamily_spec letter b hb hb1 hF _ _ j q hq,
        dblFamily_fail_le letter b hst hb hb1 hr le_rfl hw hF hfail j q hq,
        hasDual_dblFamily letter b hb1 hL le_rfl hA hdual j q hq⟩⟩

end RankDoublingLemma

end MonoidProduct
