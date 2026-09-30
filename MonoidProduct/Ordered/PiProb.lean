import MonoidProduct.Ordered.FiniteProb
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Uniform product weights on dependent products (stage D2 infrastructure)

The seed space of a rank is a dependent product over depths, `(d : Fin m) → T d`.
Its uniform weight is the product of the uniform weights of the factors
(`piW`), so a one-coordinate event has its marginal probability
(`sum_piW_coord`) and the union bound over coordinates holds
(`sum_piW_exists_le`).
-/

namespace MonoidProduct.FiniteProb

open Finset

variable {m : ℕ} {T : Fin m → Type} [∀ d, Fintype (T d)] [∀ d, DecidableEq (T d)]

/-- The product of coordinate weights. -/
def piW (w : ∀ d, T d → ℝ) (ω : ∀ d, T d) : ℝ := ∏ d, w d (ω d)

lemma piW_nonneg {w : ∀ d, T d → ℝ} (h : ∀ d, IsWeight (w d)) (ω : ∀ d, T d) : 0 ≤ piW w ω :=
  Finset.prod_nonneg fun d _ => (h d).nonneg _

lemma sum_piW {w : ∀ d, T d → ℝ} (h : ∀ d, IsWeight (w d)) : ∑ ω : ∀ d, T d, piW w ω = 1 := by
  unfold piW
  rw [← Fintype.prod_sum]
  simp [(h _).sum_one]

lemma isWeight_piW {w : ∀ d, T d → ℝ} (h : ∀ d, IsWeight (w d)) : IsWeight (piW w) :=
  ⟨piW_nonneg h, sum_piW h⟩

/-- **The marginal of one coordinate.** -/
theorem sum_piW_coord {m : ℕ} {T : Fin (m + 1) → Type} [∀ d, Fintype (T d)]
    [∀ d, DecidableEq (T d)] {w : ∀ d, T d → ℝ} (h : ∀ d, IsWeight (w d)) (d : Fin (m + 1))
    (f : T d → ℝ) : ∑ ω : ∀ d, T d, piW w ω * f (ω d) = ∑ t, w d t * f t := by
  rw [← (Fin.insertNthEquiv T d).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  have key : ∀ ω' : ∀ i : Fin m, T (d.succAbove i),
      piW w ((Fin.insertNthEquiv T d) (t, ω')) * f (((Fin.insertNthEquiv T d) (t, ω')) d)
        = w d t * f t * ∏ i, w (d.succAbove i) (ω' i) := by
    intro ω'
    have e : (Fin.insertNthEquiv T d) (t, ω') = Fin.insertNth d t ω' := rfl
    rw [e, Fin.insertNth_apply_same]
    unfold piW
    rw [Fin.prod_univ_succAbove _ d, Fin.insertNth_apply_same]
    simp only [Fin.insertNth_apply_succAbove]
    ring
  simp only [key]
  rw [← Finset.mul_sum, ← Fintype.prod_sum]
  simp [(h _).sum_one]

/-- **The union bound over coordinates.** -/
theorem sum_piW_exists_le {m : ℕ} {T : Fin (m + 1) → Type} [∀ d, Fintype (T d)]
    [∀ d, DecidableEq (T d)] {w : ∀ d, T d → ℝ} (h : ∀ d, IsWeight (w d))
    (B : ∀ d, T d → Prop) [∀ d, DecidablePred (B d)] :
    ∑ ω : ∀ d, T d, piW w ω * (if ∃ d, B d (ω d) then 1 else 0)
      ≤ ∑ d, ∑ t, w d t * (if B d t then 1 else 0) := by
  calc ∑ ω : ∀ d, T d, piW w ω * (if ∃ d, B d (ω d) then 1 else 0)
      ≤ ∑ ω : ∀ d, T d, piW w ω * ∑ d, (if B d (ω d) then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (piW_nonneg h ω)
        split_ifs with hz
        · obtain ⟨d, hd⟩ := hz
          calc (1 : ℝ) = if B d (ω d) then 1 else 0 := by rw [if_pos hd]
            _ ≤ ∑ d, (if B d (ω d) then (1 : ℝ) else 0) :=
                Finset.single_le_sum (f := fun d => if B d (ω d) then (1 : ℝ) else 0)
                  (fun d _ => by split_ifs <;> norm_num) (Finset.mem_univ d)
        · exact Finset.sum_nonneg fun d _ => by split_ifs <;> norm_num
    _ = ∑ d, ∑ ω : ∀ d, T d, piW w ω * (if B d (ω d) then 1 else 0) := by
        simp only [Finset.mul_sum]; exact Finset.sum_comm
    _ = ∑ d, ∑ t, w d t * (if B d t then 1 else 0) :=
        Finset.sum_congr rfl fun d _ => sum_piW_coord h d (fun t => if B d t then 1 else 0)

/-- The uniform weight on a finite type. -/
noncomputable def unifW (E : Type) [Fintype E] : E → ℝ := fun _ => 1 / Fintype.card E

lemma isWeight_unifW (E : Type) [Fintype E] [Nonempty E] : IsWeight (unifW E) := by
  constructor
  · intro e; unfold unifW; positivity
  · unfold unifW
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
    field_simp

/-- The uniform weight on a product is the product of uniform weights. -/
lemma unifW_prod (A B : Type) [Fintype A] [Fintype B] (p : A × B) :
    unifW (A × B) p = unifW A p.1 * unifW B p.2 := by
  unfold unifW
  rw [Fintype.card_prod]
  push_cast
  rw [one_div_mul_one_div]

/-- The uniform weight on tuples is the i.i.d. tuple of the uniform weight. -/
lemma unifW_pi (E : Type) [Fintype E] [DecidableEq E] (k : ℕ) (z : Fin k → E) :
    unifW (Fin k → E) z = tupleW (unifW E) z := by
  unfold unifW tupleW
  rw [Fintype.card_fun, Fintype.card_fin]
  simp [one_div]

/-- The uniform weight on a dependent product is the product of the uniform weights. -/
lemma unifW_dpi {m : ℕ} (T : Fin m → Type) [∀ d, Fintype (T d)] [∀ d, DecidableEq (T d)]
    (ω : ∀ d, T d) : unifW (∀ d, T d) ω = piW (fun d => unifW (T d)) ω := by
  unfold unifW piW
  rw [Fintype.card_pi]
  push_cast
  simp only [one_div]
  rw [Finset.prod_inv_distrib]

/-! ## Uniform products -/

lemma sum_unifW_prod_fst (A B : Type) [Fintype A] [Fintype B] [Nonempty B] (f : A → ℝ) :
    ∑ p : A × B, unifW (A × B) p * f p.1 = ∑ a, unifW A a * f a := by
  rw [Fintype.sum_prod_type]
  simp only [unifW_prod]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ∑ b, unifW A a * unifW B b * f a = unifW A a * f a * ∑ b, unifW B b by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring]
  rw [(isWeight_unifW B).sum_one, mul_one]

lemma sum_unifW_prod_snd (A B : Type) [Fintype A] [Fintype B] [Nonempty A] (f : B → ℝ) :
    ∑ p : A × B, unifW (A × B) p * f p.2 = ∑ b, unifW B b * f b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [unifW_prod]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show ∑ a, unifW A a * unifW B b * f b = unifW B b * f b * ∑ a, unifW A a by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring]
  rw [(isWeight_unifW A).sum_one, mul_one]

/-- The mass of a product event with a fixed first coordinate. -/
lemma sum_unifW_prod_fst_eq (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] (a₀ : A)
    (g : B → ℝ) :
    ∑ p : A × B, unifW (A × B) p * (if p.1 = a₀ then g p.2 else 0)
      = (1 / Fintype.card A) * ∑ b, unifW B b * g b := by
  rw [Fintype.sum_prod_type]
  simp only [unifW_prod]
  rw [Finset.sum_eq_single a₀]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [if_pos rfl]
    unfold unifW
    ring
  · intro a _ ha
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `Pr[P ∧ Q] ≥ 1 − Pr[¬P] − Pr[¬Q]` on a uniform product. -/
lemma sum_unifW_and_ge (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q] :
    1 - (∑ a, unifW A a * (if P a then 0 else 1)) - (∑ b, unifW B b * (if Q b then 0 else 1))
      ≤ ∑ p : A × B, unifW (A × B) p * (if P p.1 ∧ Q p.2 then 1 else 0) := by
  rw [← sum_unifW_prod_fst A B (fun a => if P a then 0 else 1),
    ← sum_unifW_prod_snd A B (fun b => if Q b then 0 else 1)]
  nth_rewrite 1 [← (isWeight_unifW (A × B)).sum_one]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  have h0 := (isWeight_unifW (A × B)).nonneg p
  have key : (1 : ℝ) - (if P p.1 then 0 else 1) - (if Q p.2 then 0 else 1)
      ≤ (if P p.1 ∧ Q p.2 then 1 else 0) := by
    by_cases hP : P p.1 <;> by_cases hQ : Q p.2 <;> simp [hP, hQ]
  calc unifW (A × B) p - unifW (A × B) p * (if P p.1 then 0 else 1)
        - unifW (A × B) p * (if Q p.2 then 0 else 1)
      = unifW (A × B) p * (1 - (if P p.1 then 0 else 1) - (if Q p.2 then 0 else 1)) := by ring
    _ ≤ unifW (A × B) p * (if P p.1 ∧ Q p.2 then 1 else 0) :=
        mul_le_mul_of_nonneg_left key h0

lemma sum_unifW_ite_nonneg (A : Type) [Fintype A] (P : A → Prop) [DecidablePred P] :
    0 ≤ ∑ a, unifW A a * (if P a then 1 else 0) :=
  Finset.sum_nonneg fun a _ => mul_nonneg (by unfold unifW; positivity) (by split_ifs <;> norm_num)

end MonoidProduct.FiniteProb
