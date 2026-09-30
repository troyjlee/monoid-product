import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import QuantumQueryComplexity.RejectionTree

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Finite probability for the merger

The probability facts behind the seeded rejection sampling of Section
`sec:beta-sampling` of the paper.

Everything is a finite sum with real weights: a **weight** is a nonnegative
function summing to one; the **i.i.d. weight** on tuples `Fin k → E` is the
product; expectations are `∑ μ z * F z`.

* `sum_pi_succ`, `tupleW_cons` — peeling the first coordinate of a tuple;
* `sum_tupleW_ess_eq`, `mul_sum_tupleW_ess_last` — **exchangeability**: for an
  index predicate equivariant under permutations of the tuple, every index is
  essential with the same probability, so `k·Pr[last essential] = E[#essential]`;
* `firstLive`, `expect_firstLive` — the **exact law of a truncated draw**: the
  first live entry of a row of `k` i.i.d. proposals fails with probability
  `(1 − w)^k` and otherwise has the conditional law `μ(· | live)`, the success
  flag being independent of the returned value (`w` the live mass);
* `expect_batch` — a batch of `m` independent truncated draws, on the event
  that all succeed, is `Pr[success]^m` times an i.i.d. sample of the conditional
  law.
-/

namespace MonoidProduct.FiniteProb

open Finset QuantumQueryComplexity

variable {E : Type} [Fintype E] [DecidableEq E]

/-- A probability weight on a finite type. -/
structure IsWeight (μ : E → ℝ) : Prop where
  nonneg : ∀ e, 0 ≤ μ e
  sum_one : ∑ e, μ e = 1

/-- The i.i.d. weight on tuples. -/
def tupleW (μ : E → ℝ) {k : ℕ} (z : Fin k → E) : ℝ := ∏ t, μ (z t)

lemma tupleW_nonneg {μ : E → ℝ} (h : IsWeight μ) {k : ℕ} (z : Fin k → E) : 0 ≤ tupleW μ z :=
  Finset.prod_nonneg fun t _ => h.nonneg _

lemma sum_tupleW {μ : E → ℝ} (h : IsWeight μ) (k : ℕ) : ∑ z : Fin k → E, tupleW μ z = 1 := by
  unfold tupleW
  rw [← Fintype.prod_sum]
  simp [h.sum_one]

lemma isWeight_tupleW {μ : E → ℝ} (h : IsWeight μ) (k : ℕ) : IsWeight (tupleW μ (k := k)) :=
  ⟨tupleW_nonneg h, sum_tupleW h k⟩

lemma tupleW_zero (μ : E → ℝ) (z : Fin 0 → E) : tupleW μ z = 1 := by simp [tupleW]

lemma tupleW_cons (μ : E → ℝ) {k : ℕ} (e : E) (z : Fin k → E) :
    tupleW μ (Fin.cons e z) = μ e * tupleW μ z := by
  unfold tupleW
  rw [Fin.prod_univ_succ]
  simp

/-- Peeling the first coordinate of a tuple sum. -/
lemma sum_pi_succ {k : ℕ} (F : (Fin (k + 1) → E) → ℝ) :
    ∑ z, F z = ∑ e, ∑ z' : Fin k → E, F (Fin.cons e z') := by
  rw [← (Fin.consEquiv fun _ => E).sum_comp, Fintype.sum_prod_type]
  rfl

lemma sum_pi_zero (F : (Fin 0 → E) → ℝ) : ∑ z, F z = F Fin.elim0 := by
  rw [Fintype.sum_unique]
  rfl

/-! ## Exchangeability -/

/-- Reindexing a tuple by a permutation. -/
def permTuple {k : ℕ} (π : Equiv.Perm (Fin k)) : (Fin k → E) ≃ (Fin k → E) where
  toFun z := z ∘ π
  invFun z := z ∘ π.symm
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp

lemma tupleW_comp_perm (μ : E → ℝ) {k : ℕ} (π : Equiv.Perm (Fin k)) (z : Fin k → E) :
    tupleW μ (z ∘ π) = tupleW μ z := by
  unfold tupleW
  exact Equiv.prod_comp π (fun t => μ (z t))

/-- **Exchangeability**: an equivariant index predicate has the same probability at
every index. -/
theorem sum_tupleW_ess_eq (μ : E → ℝ) {k : ℕ} (ess : (Fin k → E) → Fin k → Bool)
    (hess : ∀ (π : Equiv.Perm (Fin k)) z i, ess (z ∘ π) i = ess z (π i)) (i j : Fin k) :
    ∑ z, tupleW μ z * (if ess z i then 1 else 0)
      = ∑ z, tupleW μ z * (if ess z j then 1 else 0) := by
  rw [← (permTuple (Equiv.swap i j)).sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  show tupleW μ (z ∘ Equiv.swap i j) * (if ess (z ∘ Equiv.swap i j) i then 1 else 0) = _
  rw [tupleW_comp_perm, hess, Equiv.swap_apply_left]

/-- `k · Pr[index j essential] = E[#essential]`. -/
theorem mul_sum_tupleW_ess (μ : E → ℝ) {k : ℕ} (ess : (Fin k → E) → Fin k → Bool)
    (hess : ∀ (π : Equiv.Perm (Fin k)) z i, ess (z ∘ π) i = ess z (π i)) (j : Fin k) :
    (k : ℝ) * ∑ z, tupleW μ z * (if ess z j then 1 else 0)
      = ∑ z, tupleW μ z * ((Finset.univ.filter fun i => ess z i).card : ℝ) := by
  have h1 : ∀ z : Fin k → E, ((Finset.univ.filter fun i => ess z i).card : ℝ)
      = ∑ i, (if ess z i then (1 : ℝ) else 0) := by
    intro z
    rw [Finset.sum_boole]
  calc (k : ℝ) * ∑ z, tupleW μ z * (if ess z j then 1 else 0)
      = ∑ _i : Fin k, ∑ z, tupleW μ z * (if ess z j then 1 else 0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ i : Fin k, ∑ z, tupleW μ z * (if ess z i then 1 else 0) :=
        Finset.sum_congr rfl fun i _ => sum_tupleW_ess_eq μ ess hess j i
    _ = ∑ z, ∑ i : Fin k, tupleW μ z * (if ess z i then 1 else 0) := Finset.sum_comm
    _ = ∑ z, tupleW μ z * ((Finset.univ.filter fun i => ess z i).card : ℝ) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [h1, Finset.mul_sum]

/-- If at most `b` indices are ever essential, the last one is essential with
probability at most `b / k`. -/
theorem sum_tupleW_ess_le {μ : E → ℝ} (h : IsWeight μ) {k : ℕ} (hk : 0 < k)
    (ess : (Fin k → E) → Fin k → Bool)
    (hess : ∀ (π : Equiv.Perm (Fin k)) z i, ess (z ∘ π) i = ess z (π i)) {b : ℕ}
    (hb : ∀ z, (Finset.univ.filter fun i => ess z i).card ≤ b) (j : Fin k) :
    ∑ z, tupleW μ z * (if ess z j then 1 else 0) ≤ (b : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hk', mul_comm, mul_sum_tupleW_ess μ ess hess j]
  calc ∑ z, tupleW μ z * ((Finset.univ.filter fun i => ess z i).card : ℝ)
      ≤ ∑ z, tupleW μ z * b := by
        refine Finset.sum_le_sum fun z _ => ?_
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb z) (tupleW_nonneg h z)
    _ = b := by rw [← Finset.sum_mul, sum_tupleW h, one_mul]

/-! ## Marginals, pushforwards, union bounds -/

lemma cons_comp {A B : Type} (f : A → B) {m : ℕ} (a : A) (v : Fin m → A) :
    (fun i => f ((Fin.cons a v : Fin (m + 1) → A) i)) = Fin.cons (f a) (fun i => f (v i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro i; simp

/-- The marginal of one coordinate of an i.i.d. tuple. -/
lemma sum_tupleW_coord {μ : E → ℝ} (h : IsWeight μ) :
    ∀ {m : ℕ} (i : Fin m) (f : E → ℝ), ∑ z : Fin m → E, tupleW μ z * f (z i) = ∑ e, μ e * f e
  | 0, i, _ => i.elim0
  | m + 1, i, f => by
    rw [sum_pi_succ]
    simp only [tupleW_cons]
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [show ∑ z' : Fin m → E, μ e * tupleW μ z' * f e = μ e * f e * ∑ z' : Fin m → E, tupleW μ z' by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z' _ => ?_; ring, sum_tupleW h, mul_one]
    · intro i'
      simp only [Fin.cons_succ]
      have ih := sum_tupleW_coord h i' f
      rw [show ∑ e, ∑ z' : Fin m → E, μ e * tupleW μ z' * f (z' i')
          = (∑ e, μ e) * ∑ z' : Fin m → E, tupleW μ z' * f (z' i') by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z' _ => ?_; ring, h.sum_one, one_mul, ih]

/-- **Union bound** over the coordinates of an i.i.d. tuple. -/
lemma sum_tupleW_exists_le {μ : E → ℝ} (h : IsWeight μ) {m : ℕ} (P : E → Prop) [DecidablePred P] :
    ∑ z : Fin m → E, tupleW μ z * (if ∃ i, P (z i) then 1 else 0)
      ≤ (m : ℝ) * ∑ e, μ e * (if P e then 1 else 0) := by
  calc ∑ z : Fin m → E, tupleW μ z * (if ∃ i, P (z i) then 1 else 0)
      ≤ ∑ z : Fin m → E, tupleW μ z * ∑ i, (if P (z i) then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (tupleW_nonneg h z)
        split_ifs with hz
        · obtain ⟨i, hi⟩ := hz
          calc (1 : ℝ) = if P (z i) then 1 else 0 := by rw [if_pos hi]
            _ ≤ ∑ i, (if P (z i) then (1 : ℝ) else 0) :=
                Finset.single_le_sum (f := fun j => if P (z j) then (1 : ℝ) else 0)
                  (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
        · exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
    _ = ∑ i : Fin m, ∑ z : Fin m → E, tupleW μ z * (if P (z i) then 1 else 0) := by
        simp only [Finset.mul_sum]; exact Finset.sum_comm
    _ = ∑ _i : Fin m, ∑ e, μ e * (if P e then 1 else 0) :=
        Finset.sum_congr rfl fun i _ => sum_tupleW_coord h i (fun e => if P e then 1 else 0)
    _ = (m : ℝ) * ∑ e, μ e * (if P e then 1 else 0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Markov**: `Pr[F ≥ a] ≤ E[F] / a` for nonnegative `F`. -/
lemma sum_indicator_ge_le {μ : E → ℝ} (h : IsWeight μ) (F : E → ℝ) (hF : ∀ e, 0 ≤ F e) {a : ℝ}
    (ha : 0 < a) :
    ∑ e, μ e * (if a ≤ F e then 1 else 0) ≤ (∑ e, μ e * F e) / a := by
  rw [le_div_iff₀ ha, Finset.sum_mul]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (h.nonneg e)
  split_ifs with he
  · rw [one_mul]; exact he
  · rw [zero_mul]; exact hF e

/-- The pushforward of a weight along a map. -/
def pushW {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ν : Ω → ℝ) (φ : Ω → E) : E → ℝ :=
  fun e => ∑ ω, if φ ω = e then ν ω else 0

lemma isWeight_pushW {Ω : Type} [Fintype Ω] [DecidableEq Ω] {ν : Ω → ℝ} (h : IsWeight ν) (φ : Ω → E) :
    IsWeight (pushW ν φ) := by
  constructor
  · intro e
    exact Finset.sum_nonneg fun ω _ => by split_ifs <;> [exact h.nonneg ω; exact le_rfl]
  · unfold pushW
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact h.sum_one

lemma sum_pushW {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ν : Ω → ℝ) (φ : Ω → E) (G : E → ℝ) :
    ∑ e, pushW ν φ e * G e = ∑ ω, ν ω * G (φ ω) := by
  unfold pushW
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp [Finset.sum_ite_eq]

/-- **Pushing an i.i.d. tuple forward** coordinatewise gives the i.i.d. tuple of the
pushforward. -/
theorem sum_tupleW_map {Ω : Type} [Fintype Ω] [DecidableEq Ω] {ν : Ω → ℝ} (h : IsWeight ν) (φ : Ω → E) :
    ∀ {k : ℕ} (F : (Fin k → E) → ℝ),
      ∑ ω : Fin k → Ω, tupleW ν ω * F (fun i => φ (ω i))
        = ∑ z : Fin k → E, tupleW (pushW ν φ) z * F z
  | 0, F => by
    rw [sum_pi_zero, sum_pi_zero, tupleW_zero, tupleW_zero]
    exact congrArg (fun v => 1 * F v) (Subsingleton.elim _ _)
  | k + 1, F => by
    rw [sum_pi_succ, sum_pi_succ (E := E)]
    have step1 : ∀ ω₀ : Ω, ∑ ω : Fin k → Ω, tupleW ν (Fin.cons ω₀ ω)
          * F (fun i => φ ((Fin.cons ω₀ ω : Fin (k + 1) → Ω) i))
        = ν ω₀ * ∑ z : Fin k → E, tupleW (pushW ν φ) z * F (Fin.cons (φ ω₀) z) := by
      intro ω₀
      rw [← sum_tupleW_map h φ (fun z => F (Fin.cons (φ ω₀) z)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [tupleW_cons, cons_comp]
      ring
    have step2 : ∀ e : E, ∑ z : Fin k → E, tupleW (pushW ν φ) (Fin.cons e z) * F (Fin.cons e z)
        = pushW ν φ e * ∑ z : Fin k → E, tupleW (pushW ν φ) z * F (Fin.cons e z) := by
      intro e
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [tupleW_cons]
      ring
    rw [Finset.sum_congr rfl (fun ω₀ _ => step1 ω₀), Finset.sum_congr rfl (fun e _ => step2 e)]
    exact (sum_pushW ν φ (fun e => ∑ z : Fin k → E, tupleW (pushW ν φ) z * F (Fin.cons e z))).symm

/-! ## The truncated draw -/

open QuantumQueryComplexity (firstLive firstLive_zero firstLive_cons)

/-- The live mass. -/
def liveMass (μ : E → ℝ) (live : E → Bool) : ℝ := ∑ e, if live e then μ e else 0

lemma liveMass_nonneg {μ : E → ℝ} (h : IsWeight μ) (live : E → Bool) : 0 ≤ liveMass μ live :=
  Finset.sum_nonneg fun e _ => by split_ifs <;> [exact h.nonneg e; exact le_rfl]

lemma liveMass_le_one {μ : E → ℝ} (h : IsWeight μ) (live : E → Bool) : liveMass μ live ≤ 1 := by
  rw [← h.sum_one]
  refine Finset.sum_le_sum fun e _ => ?_
  split_ifs <;> [exact le_rfl; exact h.nonneg e]

lemma sum_dead {μ : E → ℝ} (h : IsWeight μ) (live : E → Bool) :
    (∑ e, if live e then 0 else μ e) = 1 - liveMass μ live := by
  rw [liveMass, eq_sub_iff_add_eq, ← Finset.sum_add_distrib, ← h.sum_one]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

/-- **The exact law of a truncated draw.** -/
theorem expect_firstLive {μ : E → ℝ} (h : IsWeight μ) (live : E → Bool) (G : Option E → ℝ) :
    ∀ k : ℕ, ∑ row : Fin k → E, tupleW μ row * G (firstLive live row)
      = (1 - liveMass μ live) ^ k * G none
        + (∑ t ∈ Finset.range k, (1 - liveMass μ live) ^ t)
          * ∑ e, (if live e then μ e * G (some e) else 0)
  | 0 => by
    rw [sum_pi_zero, tupleW_zero, firstLive_zero]
    simp
  | k + 1 => by
    rw [sum_pi_succ]
    simp only [tupleW_cons, firstLive_cons]
    have ih := expect_firstLive h live G k
    have hsplit : ∀ e : E, ∑ z' : Fin k → E, μ e * tupleW μ z'
          * G (if live e then some e else firstLive live z')
        = (if live e then μ e * G (some e) else 0)
          + (if live e then 0 else μ e) * ∑ z' : Fin k → E, tupleW μ z' * G (firstLive live z') := by
      intro e
      by_cases hl : live e = true
      · simp only [if_pos hl]
        rw [show ∑ z' : Fin k → E, μ e * tupleW μ z' * G (some e)
            = μ e * G (some e) * ∑ z' : Fin k → E, tupleW μ z' by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z' _ => ?_; ring]
        rw [sum_tupleW h]
        ring
      · simp only [if_neg hl]
        rw [zero_add, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z' _ => ?_
        ring
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul, sum_dead h, ih,
      Finset.sum_range_succ', pow_zero, pow_succ]
    ring

lemma prob_firstLive_none {μ : E → ℝ} (h : IsWeight μ) (live : E → Bool) (k : ℕ) :
    ∑ row : Fin k → E, tupleW μ row * (if firstLive live row = none then 1 else 0)
      = (1 - liveMass μ live) ^ k := by
  have := expect_firstLive h live (fun o => if o = none then 1 else 0) k
  simp only [if_true, mul_one, reduceCtorEq, if_false, mul_zero, ite_self,
    Finset.sum_const_zero, add_zero] at this
  exact this

/-- The success probability, as a geometric sum. -/
lemma geom_liveMass (w : ℝ) (k : ℕ) :
    (∑ t ∈ Finset.range k, (1 - w) ^ t) * w = 1 - (1 - w) ^ k := by
  have := geom_sum_mul_neg (1 - w) k
  rwa [sub_sub_cancel] at this

/-- The conditional weight `μ(· | live)`. -/
noncomputable def condW (μ : E → ℝ) (live : E → Bool) : E → ℝ :=
  fun e => if live e then μ e / liveMass μ live else 0

lemma isWeight_condW {μ : E → ℝ} (h : IsWeight μ) {live : E → Bool}
    (hw : 0 < liveMass μ live) : IsWeight (condW μ live) := by
  constructor
  · intro e
    unfold condW
    split_ifs
    · exact div_nonneg (h.nonneg e) hw.le
    · exact le_rfl
  · show (∑ e, if live e = true then μ e / liveMass μ live else 0) = 1
    have : (∑ e, if live e = true then μ e / liveMass μ live else 0)
        = (∑ e, if live e = true then μ e else 0) / liveMass μ live := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs <;> simp
    rw [this]
    exact div_self hw.ne'

/-- A successful draw, in terms of the conditional weight. -/
lemma sum_live_eq_condW {μ : E → ℝ} (live : E → Bool) (hw : 0 < liveMass μ live)
    (G : E → ℝ) :
    (∑ e, if live e then μ e * G e else 0) = liveMass μ live * ∑ e, condW μ live e * G e := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold condW
  split_ifs
  · field_simp
  · simp

/-- **A batch of independent truncated draws**, on the event that all succeed, is
`Pr[success]^m` times an i.i.d. sample of the conditional law.  Stated for a
functional `H` of the optional results that vanishes as soon as one draw failed. -/
theorem expect_batch {μ : E → ℝ} (h : IsWeight μ) (live : E → Bool) (hw : 0 < liveMass μ live)
    (k : ℕ) :
    ∀ (m : ℕ) (H : (Fin m → Option E) → ℝ), (∀ o, (∃ i, o i = none) → H o = 0) →
      ∑ z : Fin m → (Fin k → E), tupleW (tupleW μ) z * H (fun i => firstLive live (z i))
        = (1 - (1 - liveMass μ live) ^ k) ^ m
          * ∑ y : Fin m → E, tupleW (condW μ live) y * H (fun i => some (y i))
  | 0, H, _ => by
    rw [sum_pi_zero, sum_pi_zero, tupleW_zero, tupleW_zero]
    simp only [pow_zero, one_mul]
    congr 1
    funext i
    exact i.elim0
  | m + 1, H, hH => by
    rw [sum_pi_succ, sum_pi_succ (E := E)]
    simp only [tupleW_cons, cons_comp]
    have hnone : ∀ rest : Fin m → (Fin k → E),
        H (Fin.cons none fun i => firstLive live (rest i)) = 0 :=
      fun rest => hH _ ⟨0, by simp⟩
    have hH' : ∀ e : E, ∀ o : Fin m → Option E, (∃ i, o i = none)
        → H (Fin.cons (some e) o) = 0 := by
      rintro e o ⟨i, hi⟩
      exact hH _ ⟨i.succ, by simp [hi]⟩
    have ih : ∀ e : E, ∑ z : Fin m → (Fin k → E), tupleW (tupleW μ) z
          * H (Fin.cons (some e) fun i => firstLive live (z i))
        = (1 - (1 - liveMass μ live) ^ k) ^ m
          * ∑ y : Fin m → E, tupleW (condW μ live) y * H (Fin.cons (some e) fun i => some (y i)) :=
      fun e => expect_batch h live hw k m (fun o => H (Fin.cons (some e) o)) (hH' e)
    -- swap the sums and apply the single-draw law to the first row
    have hswap : ∑ row : Fin k → E, ∑ rest : Fin m → (Fin k → E),
          tupleW μ row * tupleW (tupleW μ) rest
            * H (Fin.cons (firstLive live row) fun i => firstLive live (rest i))
        = ∑ rest : Fin m → (Fin k → E), tupleW (tupleW μ) rest
            * ∑ row : Fin k → E, tupleW μ row
              * H (Fin.cons (firstLive live row) fun i => firstLive live (rest i)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun rest _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun row _ => ?_
      ring
    rw [hswap]
    have hrow : ∀ rest : Fin m → (Fin k → E),
        ∑ row : Fin k → E, tupleW μ row
            * H (Fin.cons (firstLive live row) fun i => firstLive live (rest i))
        = (1 - (1 - liveMass μ live) ^ k)
            * ∑ e, condW μ live e * H (Fin.cons (some e) fun i => firstLive live (rest i)) := by
      intro rest
      rw [expect_firstLive h live (fun o => H (Fin.cons o fun i => firstLive live (rest i))) k]
      simp only [hnone, mul_zero, zero_add]
      rw [sum_live_eq_condW live hw, ← mul_assoc, geom_liveMass]
    simp only [hrow]
    -- pull the constant out, swap, and apply the induction hypothesis
    have e1 : ∑ rest : Fin m → (Fin k → E), tupleW (tupleW μ) rest
          * ((1 - (1 - liveMass μ live) ^ k)
            * ∑ e, condW μ live e * H (Fin.cons (some e) fun i => firstLive live (rest i)))
        = (1 - (1 - liveMass μ live) ^ k) * ∑ e, condW μ live e
            * ∑ rest : Fin m → (Fin k → E), tupleW (tupleW μ) rest
              * H (Fin.cons (some e) fun i => firstLive live (rest i)) := by
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun rest _ => Finset.sum_congr rfl fun e _ => ?_
      ring
    rw [e1]
    simp only [ih]
    rw [pow_succ, Finset.mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun y _ => ?_
    ring

/-- The batch lemma for a functional of the accepted records themselves. -/
theorem expect_batch' {μ : E → ℝ} (h : IsWeight μ) (live : E → Bool) (hw : 0 < liveMass μ live)
    (k m : ℕ) (F : (Fin m → E) → ℝ) :
    ∑ z : Fin m → (Fin k → E), tupleW (tupleW μ) z
        * (if hs : ∀ i, (firstLive live (z i)).isSome
            then F (fun i => (firstLive live (z i)).get (hs i)) else 0)
      = (1 - (1 - liveMass μ live) ^ k) ^ m * ∑ y : Fin m → E, tupleW (condW μ live) y * F y := by
  have := expect_batch h live hw k m
    (fun o => if hs : ∀ i, (o i).isSome then F (fun i => (o i).get (hs i)) else 0)
    (fun o ⟨i, hi⟩ => by
      rw [dif_neg]
      intro hs
      have := hs i
      rw [hi] at this
      simp at this)
  simp only [Option.isSome_some, Option.get_some, implies_true, dite_true] at this
  exact this

end MonoidProduct.FiniteProb
