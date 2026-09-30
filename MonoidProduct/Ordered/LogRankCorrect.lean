import MonoidProduct.Ordered.LogRank
import MonoidProduct.Ordered.Correct

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# Correctness of the stage recursion

`summary2_correct`: for every stage `s`, every dyadic interval `(j, q)` inside the word and
every input, the uniform seed fails to produce a rank-`2^s` summary with mass at most
`(1/100)^c`, provided the copy count `c` and the thinning rounds `R` are large enough for
the word (`2^{J+2}·(1/100)^c ≤ 1/400` and `2^{J+2}·(1/2)^R ≤ 1/400` for `2^J ≤ N`).

The step from stage `s` to `s+1` on `(j+1, q)` is `copy_fail_le`: one copy of the rank
doubling fails only if one of the `< 2^{j+2}` child summaries fails (a union bound over the
independent child seeds, `sum_piWD_exists_le`) or all children are correct and the thinning
fails (`dbl_fail_le`); the amplification `amp_fail_le` then raises `1/200` to the power `c`.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

/-! ## Product weights over an arbitrary finite index -/

section PiUnion

variable {D : Type} [Fintype D] [DecidableEq D] {T : D → Type} [∀ d, Fintype (T d)]

/-- The product of coordinate weights (arbitrary finite index). -/
def piWD (w : ∀ d, T d → ℝ) (ω : ∀ d, T d) : ℝ := ∏ d, w d (ω d)

lemma piWD_nonneg {w : ∀ d, T d → ℝ} (h : ∀ d, IsWeight (w d)) (ω : ∀ d, T d) : 0 ≤ piWD w ω :=
  Finset.prod_nonneg fun d _ => (h d).nonneg _

lemma sum_piWD {w : ∀ d, T d → ℝ} (h : ∀ d, IsWeight (w d)) : ∑ ω : ∀ d, T d, piWD w ω = 1 := by
  unfold piWD
  rw [← Fintype.prod_sum]
  simp [(h _).sum_one]

/-- The uniform weight on a dependent product is the product of the uniform weights. -/
lemma unifW_dpi' (T : D → Type) [∀ d, Fintype (T d)] [∀ d, DecidableEq (T d)] (ω : ∀ d, T d) :
    unifW (∀ d, T d) ω = piWD (fun d => unifW (T d)) ω := by
  unfold unifW piWD
  rw [Fintype.card_pi]
  push_cast
  simp only [one_div]
  rw [Finset.prod_inv_distrib]

/-- **The marginal of one coordinate.** -/
theorem sum_piWD_coord {w : ∀ d, T d → ℝ} (h : ∀ d, IsWeight (w d)) (d : D) (f : T d → ℝ) :
    ∑ ω : ∀ d, T d, piWD w ω * f (ω d) = ∑ t, w d t * f t := by
  have h1 : ∀ ω : ∀ d, T d, piWD w ω * f (ω d)
      = ∏ d', (w d' (ω d') * if hd : d' = d then f (hd ▸ ω d') else 1) := by
    intro ω
    rw [Finset.prod_mul_distrib, Finset.prod_dite_eq' Finset.univ d (fun d' hd => f (hd ▸ ω d'))]
    simp [piWD]
  have h3 := Fintype.prod_sum (fun d' (t : T d') => w d' t * if hd : d' = d then f (hd ▸ t) else 1)
  rw [Finset.sum_congr rfl fun ω _ => h1 ω, ← h3]
  have h2 : ∀ d', ∑ t, (w d' t * if hd : d' = d then f (hd ▸ t) else 1)
      = if d' = d then ∑ t, w d t * f t else 1 := by
    intro d'
    by_cases hd : d' = d
    · subst hd; simp
    · simp [hd, (h d').sum_one]
  rw [Finset.prod_congr rfl fun d' _ => h2 d', Finset.prod_ite_eq' Finset.univ d]
  simp

/-- **The union bound over coordinates.** -/
theorem sum_piWD_exists_le {w : ∀ d, T d → ℝ} (h : ∀ d, IsWeight (w d))
    (B : ∀ d, T d → Prop) [∀ d, DecidablePred (B d)] :
    ∑ ω : ∀ d, T d, piWD w ω * (if ∃ d, B d (ω d) then 1 else 0)
      ≤ ∑ d, ∑ t, w d t * (if B d t then 1 else 0) := by
  calc ∑ ω : ∀ d, T d, piWD w ω * (if ∃ d, B d (ω d) then 1 else 0)
      ≤ ∑ ω : ∀ d, T d, piWD w ω * ∑ d, (if B d (ω d) then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (piWD_nonneg h ω)
        split_ifs with hz
        · obtain ⟨d, hd⟩ := hz
          calc (1 : ℝ) = if B d (ω d) then 1 else 0 := by rw [if_pos hd]
            _ ≤ ∑ d, (if B d (ω d) then (1 : ℝ) else 0) :=
                Finset.single_le_sum (f := fun d => if B d (ω d) then (1 : ℝ) else 0)
                  (fun d _ => by split_ifs <;> norm_num) (Finset.mem_univ d)
        · exact Finset.sum_nonneg fun d _ => by split_ifs <;> norm_num
    _ = ∑ d, ∑ ω : ∀ d, T d, piWD w ω * (if B d (ω d) then 1 else 0) := by
        simp only [Finset.mul_sum]; exact Finset.sum_comm
    _ = ∑ d, ∑ t, w d t * (if B d t then 1 else 0) :=
        Finset.sum_congr rfl fun d _ => sum_piWD_coord h d (fun t => if B d t then 1 else 0)

end PiUnion

/-- The uniform weight on two-level tuples. -/
lemma unifW_pi2 (E : Type) [Fintype E] [DecidableEq E] (R m : ℕ) :
    unifW (Fin R → Fin m → E) = tupleW (tupleW (unifW E)) := by
  funext t
  simp only [unifW_pi, tupleW]

section LogRankCorrect

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable [DecidableLE M] (letter : σ → M) {N : ℕ} (b : ℕ)

/-- A summary of rank `r` is a summary of every smaller rank. -/
lemma IsSummary.mono_rank {x : Fin N → σ} {r r' j q : ℕ} {K : Record N σ}
    (h : IsSummary letter x b r j q K) (hr : r' ≤ r) : IsSummary letter x b r' j q K where
  truthful := h.truthful
  supp_subset := h.supp_subset
  card_le := h.card_le
  dom := fun U hU hc => h.dom U hU (hc.trans hr)

/-! ## Arithmetic of the children -/

lemma child_len_le {j q : ℕ} (hq : (q + 1) * 2 ^ (j + 1) ≤ N) (w : DNode j) :
    (q * 2 ^ (w.1 : ℕ) + w.2 + 1) * 2 ^ (j + 1 - w.1) ≤ N := by
  have hw : (w.1 : ℕ) ≤ j + 1 := by have := w.1.isLt; omega
  have h2 : (w.2 : ℕ) + 1 ≤ 2 ^ (w.1 : ℕ) := w.2.isLt
  calc (q * 2 ^ (w.1 : ℕ) + w.2 + 1) * 2 ^ (j + 1 - w.1)
      ≤ (q * 2 ^ (w.1 : ℕ) + 2 ^ (w.1 : ℕ)) * 2 ^ (j + 1 - w.1) :=
        Nat.mul_le_mul_right _ (by rw [add_assoc]; exact Nat.add_le_add_left h2 _)
    _ = (q + 1) * 2 ^ (j + 1) := by
        rw [← add_one_mul, mul_assoc, ← pow_add, Nat.add_sub_cancel' hw]
    _ ≤ N := hq

lemma two_pow_le_of_len {j q : ℕ} (hq : (q + 1) * 2 ^ (j + 1) ≤ N) : 2 ^ j ≤ N :=
  calc 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ (q + 1) * 2 ^ (j + 1) := Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ N := hq

/-! ## One copy of the rank doubling -/

variable (hst : IsStableOrder M) (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b)
include hst hb hb1

open Classical in
/-- **One copy fails only if a child fails or the thinning fails.**  With independent child
seeds of failure mass `≤ δ` and independent thinning seeds, the failure mass of one copy of the
rank doubling is at most `|DNode j|·δ + |DNode j|·(1/2)^R`. -/
theorem copy_fail_le {j q : ℕ} (x : Fin N → σ) {r : ℕ} (hr : 1 ≤ r)
    {Ω' : DNode j → Type} [∀ w, Fintype (Ω' w)] [∀ w, DecidableEq (Ω' w)] [∀ w, Nonempty (Ω' w)]
    (F : ∀ w, Ω' w → (Fin N → σ) → Record N σ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : ∀ w : DNode j, 1 ≤ (w.1 : ℕ) →
      ∑ t, unifW (Ω' w) t * (if IsSummary letter x b r (j + 1 - w.1) (q * 2 ^ (w.1 : ℕ) + w.2)
        (F w t x) then 0 else 1) ≤ δ)
    (R : ℕ) :
    ∑ ω' : (∀ w, Ω' w) × (Fin R → Fin (2 * b) → Ord (DNode j)), unifW _ ω'
        * (if IsSummary letter x b (2 * r) (j + 1) q
            (dblOut letter j (fun w => F w (ω'.1 w)) b ω'.2 x) then 0 else 1)
      ≤ Fintype.card (DNode j) * δ + Fintype.card (DNode j) * (1 / 2) ^ R := by
  have : Nonempty (Ord (DNode j)) := ⟨Fintype.equivFin _⟩
  have hrows1 : ∑ rows : Fin R → Fin (2 * b) → Ord (DNode j), unifW _ rows = 1 :=
    (isWeight_unifW _).sum_one
  have hΩ1 : ∑ ωc : ∀ w, Ω' w, unifW _ ωc = 1 := (isWeight_unifW _).sum_one
  rw [Fintype.sum_prod_type]
  simp only [unifW_prod]
  -- the three indicators
  set G : (∀ w, Ω' w) → (Fin R → Fin (2 * b) → Ord (DNode j)) → ℝ := fun ωc rows =>
    if IsSummary letter x b (2 * r) (j + 1) q (dblOut letter j (fun w => F w (ωc w)) b rows x)
      then 0 else 1 with hG
  set E : (∀ w, Ω' w) → ℝ := fun ωc =>
    if ∃ w : DNode j, 1 ≤ (w.1 : ℕ) ∧ ¬ IsSummary letter x b r (j + 1 - w.1)
      (q * 2 ^ (w.1 : ℕ) + w.2) (F w (ωc w) x) then 1 else 0 with hE
  set Bf : (∀ w, Ω' w) → (Fin R → Fin (2 * b) → Ord (DNode j)) → ℝ := fun ωc rows =>
    if (∀ w : DNode j, 1 ≤ (w.1 : ℕ) → IsSummary letter x b r (j + 1 - w.1)
        (q * 2 ^ (w.1 : ℕ) + w.2) (F w (ωc w) x))
      ∧ ¬ IsSummary letter x b (2 * r) (j + 1) q (dblOut letter j (fun w => F w (ωc w)) b rows x)
      then 1 else 0 with hBf
  have hpt : ∀ ωc rows, G ωc rows ≤ E ωc + Bf ωc rows := by
    intro ωc rows
    simp only [hG, hE, hBf]
    by_cases hG' : IsSummary letter x b (2 * r) (j + 1) q
        (dblOut letter j (fun w => F w (ωc w)) b rows x)
    · rw [if_pos hG']; split_ifs <;> norm_num
    · rw [if_neg hG']
      by_cases hE' : ∃ w : DNode j, 1 ≤ (w.1 : ℕ) ∧ ¬ IsSummary letter x b r (j + 1 - w.1)
          (q * 2 ^ (w.1 : ℕ) + w.2) (F w (ωc w) x)
      · rw [if_pos hE']; split_ifs <;> norm_num
      · rw [if_neg hE', if_pos ⟨fun w hw => by_contra fun h => hE' ⟨w, hw, h⟩, hG'⟩]; norm_num
  -- the union bound over the children
  have hA : ∑ ωc : ∀ w, Ω' w, unifW _ ωc * E ωc ≤ Fintype.card (DNode j) * δ := by
    simp only [unifW_dpi', hE]
    have hU := sum_piWD_exists_le (T := Ω') (w := fun w => unifW (Ω' w))
      (fun w => isWeight_unifW (Ω' w))
      (fun w t => 1 ≤ (w.1 : ℕ) ∧ ¬ IsSummary letter x b r (j + 1 - w.1)
        (q * 2 ^ (w.1 : ℕ) + w.2) (F w t x))
    refine le_trans hU ?_
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_le_sum fun w _ => ?_
    by_cases hw : 1 ≤ (w.1 : ℕ)
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun t _ => ?_)) (hF w hw)
      congr 1
      by_cases hS : IsSummary letter x b r (j + 1 - w.1) (q * 2 ^ (w.1 : ℕ) + w.2) (F w t x)
      · rw [if_pos hS, if_neg (fun h => h.2 hS)]
      · rw [if_neg hS, if_pos ⟨hw, hS⟩]
    · refine le_trans (le_of_eq (Finset.sum_eq_zero fun t _ => ?_)) hδ
      rw [if_neg (fun h => hw h.1), mul_zero]
  -- the thinning bound given correct children
  have hB : ∑ ωc : ∀ w, Ω' w, unifW _ ωc * ∑ rows, unifW _ rows * Bf ωc rows
      ≤ Fintype.card (DNode j) * (1 / 2) ^ R := by
    calc ∑ ωc : ∀ w, Ω' w, unifW _ ωc * ∑ rows, unifW _ rows * Bf ωc rows
        ≤ ∑ ωc : ∀ w, Ω' w, unifW _ ωc * (Fintype.card (DNode j) * (1 / 2) ^ R) := by
          refine Finset.sum_le_sum fun ωc _ =>
            mul_le_mul_of_nonneg_left ?_ ((isWeight_unifW _).nonneg _)
          by_cases hall : ∀ w : DNode j, 1 ≤ (w.1 : ℕ) → IsSummary letter x b r (j + 1 - w.1)
              (q * 2 ^ (w.1 : ℕ) + w.2) (F w (ωc w) x)
          · refine le_trans (le_of_eq (Finset.sum_congr rfl fun rows _ => ?_))
              (dbl_fail_le letter j q (fun w => F w (ωc w)) x hst hb hb1 hr hall R)
            rw [unifW_pi2]
            congr 1
            simp only [hBf]
            by_cases hG' : IsSummary letter x b (2 * r) (j + 1) q
                (dblOut letter j (fun w => F w (ωc w)) b rows x)
            · rw [if_pos hG', if_neg (fun h => h.2 hG')]
            · rw [if_neg hG', if_pos ⟨hall, hG'⟩]
          · refine le_trans (le_of_eq (Finset.sum_eq_zero fun rows _ => ?_)) (by positivity)
            simp only [hBf]
            rw [if_neg (fun h => hall h.1), mul_zero]
      _ = Fintype.card (DNode j) * (1 / 2) ^ R := by rw [← Finset.sum_mul, hΩ1, one_mul]
  calc ∑ ωc : ∀ w, Ω' w, ∑ rows : Fin R → Fin (2 * b) → Ord (DNode j),
          unifW _ ωc * unifW _ rows * G ωc rows
      ≤ ∑ ωc : ∀ w, Ω' w, ∑ rows : Fin R → Fin (2 * b) → Ord (DNode j),
          unifW _ ωc * unifW _ rows * (E ωc + Bf ωc rows) :=
        Finset.sum_le_sum fun ωc _ => Finset.sum_le_sum fun rows _ =>
          mul_le_mul_of_nonneg_left (hpt ωc rows)
            (mul_nonneg ((isWeight_unifW _).nonneg _) ((isWeight_unifW _).nonneg _))
    _ = (∑ ωc : ∀ w, Ω' w, unifW _ ωc * E ωc)
          + ∑ ωc : ∀ w, Ω' w, unifW _ ωc * ∑ rows, unifW _ rows * Bf ωc rows := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ωc _ => ?_
        have e1 : ∑ rows : Fin R → Fin (2 * b) → Ord (DNode j),
            unifW _ ωc * unifW _ rows * E ωc = unifW _ ωc * E ωc := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hrows1, mul_one]
        have e2 : ∑ rows : Fin R → Fin (2 * b) → Ord (DNode j),
            unifW _ ωc * unifW _ rows * Bf ωc rows
              = unifW _ ωc * ∑ rows, unifW _ rows * Bf ωc rows := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun rows _ => by ring
        rw [← e1, ← e2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun rows _ => by ring
    _ ≤ Fintype.card (DNode j) * δ + Fintype.card (DNode j) * (1 / 2) ^ R := add_le_add hA hB

/-! ## The stage correctness theorem -/

variable (P : MParams) (c R : ℕ)

omit hst hb hb1 in
open Classical in
/-- The failure mass of a stage summary. -/
noncomputable def failMass2 (s j q : ℕ) (x : Fin N → σ) : ℝ :=
  ∑ ω : Ω2 b P c R s j, unifW (Ω2 b P c R s j) ω
    * (if IsSummary letter x b (2 ^ s) j q (summary2 letter b P c R s j q ω x) then 0 else 1)

open Classical in
/-- **Every stage fails with mass at most `(1/100)^c`.** -/
theorem summary2_correct (hP : GoodParams b N P)
    (hc : ∀ J : ℕ, 2 ^ J ≤ N → ((2 : ℝ) ^ (J + 2)) * (1 / 100) ^ c ≤ 1 / 400)
    (hR : ∀ J : ℕ, 2 ^ J ≤ N → ((2 : ℝ) ^ (J + 2)) * (1 / 2) ^ R ≤ 1 / 400) :
    ∀ (s j q : ℕ), (q + 1) * 2 ^ j ≤ N → ∀ x : Fin N → σ,
      failMass2 letter b P c R s j q x ≤ (1 / 100) ^ c
  | 0, j, q, hq, x => by
    unfold failMass2
    simp only [summary2_zero, pow_zero]
    exact amp_fail_le letter b hst hb c _ x (fun ω x => summary_truthful letter hb hb1 P 1 j q ω x)
      (fun ω x => summary_supp_subset letter hb hb1 P 1 j q ω x) (by norm_num)
      (summary_correct letter hst hb hb1 P hP 1 j q hq x)
  | s + 1, 0, q, hq, x => by
    unfold failMass2
    have hqN : q < N := by simp at hq; omega
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun ω _ => ?_)) (by positivity)
    rw [summary2_succ_zero, letterRecN, dif_pos hqN,
      if_pos (isSummary_letterRec letter hst x hb1 _ q hqN), mul_zero]
  | s + 1, j + 1, q, hq, x => by
    have hj : 2 ^ j ≤ N := two_pow_le_of_len hq
    have hcard : (Fintype.card (DNode j) : ℝ) ≤ 2 ^ (j + 2) := by
      exact_mod_cast (card_DNode_lt j).le
    have hcA : (Fintype.card (DNode j) : ℝ) * (1 / 100) ^ c ≤ 1 / 400 :=
      le_trans (mul_le_mul_of_nonneg_right hcard (by positivity)) (hc j hj)
    have hcB : (Fintype.card (DNode j) : ℝ) * (1 / 2) ^ R ≤ 1 / 400 :=
      le_trans (mul_le_mul_of_nonneg_right hcard (by positivity)) (hR j hj)
    unfold failMass2
    simp only [summary2_succ_succ]
    refine le_trans (amp_fail_le letter b hst hb c _ x (fun ω' x => ?_) (fun ω' x => ?_)
      (by norm_num) ?_) (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 200 : ℝ) ≤ 1 / 100) c)
    · exact dblOut_truthful letter j _ b x
        (fun w _ => summary2_truthful letter b P c R hb hb1 s _ _ _ x) ω'.2
    · exact supp_dblOut_subset letter j q _ x hb
        (fun w _ => summary2_supp_subset letter b P c R hb hb1 s _ _ _ x) ω'.2
    · rw [show (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s from pow_succ' 2 s]
      refine le_trans (copy_fail_le letter b hst hb hb1 x Nat.one_le_two_pow
        (fun w t => summary2 letter b P c R s (j + 1 - w.1) (q * 2 ^ (w.1 : ℕ) + w.2) t)
        (by positivity) (fun w _ => summary2_correct hP hc hR s _ _ (child_len_le hq w) x) R) ?_
      linarith [hcA, hcB]

end LogRankCorrect

end MonoidProduct
