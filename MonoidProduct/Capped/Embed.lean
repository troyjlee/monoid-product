import QuantumQueryComplexity.Spectral
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Extension by zero along a section

Transfer layer for lower bounds proved on an embedded sub-cube of the input
space: a matrix `M` on `A` extends by zero along an injection `emb : A → B`
to a matrix `embMat M` on `B`, using an *explicit* retraction
`retr : B → A` (`retr ∘ emb = id`) so no choice is involved.

The lemmas are exactly what a `norm_div_le_advPM` certificate needs:

* `embMat_apply_emb` — the extension restricts back to `M`;
* `embMat_isHermitian` — Hermitian transfer;
* `l2_opNorm_embMat_le` — `‖embMat M‖ ≤ ‖M‖` (test vectors pull back);
* `embMat_hadamard` — `embMat M ⊙ N = embMat (M ⊙ N.submatrix emb emb)`,
  so Hadamard masks on `B` become masks on `A`;
* `embMat_mulVec_embVec` — eigenvectors extend by zero
  (`embVec`), so `‖embMat M‖ ≥ |θ|` for any eigenvalue `θ` of `M`.

Also here: `l2_opNorm_le_one_of_equiv_support` — a matrix supported on the
graph of a bijection with entries of absolute value ≤ 1 has norm ≤ 1 (the
"matching" bound; Cauchy–Schwarz plus reindexing along the bijection).
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {B : Type*} [Fintype B] [DecidableEq B]

section Embed

variable (emb : A → B) (retr : B → A)

/-- The indicator of the image of `emb`, detected via the retraction. -/
def embInd (x : B) : ℝ := if emb (retr x) = x then 1 else 0

/-- Extension of a matrix by zero along the section `emb`. -/
def embMat (M : Matrix A A ℝ) : Matrix B B ℝ :=
  Matrix.of fun x y => embInd emb retr x * embInd emb retr y
    * M (retr x) (retr y)

/-- Extension of a vector by zero along the section `emb`. -/
def embVec (v : A → ℝ) : B → ℝ :=
  fun x => embInd emb retr x * v (retr x)

variable {emb retr}

@[simp] lemma embMat_apply (M : Matrix A A ℝ) (x y : B) :
    embMat emb retr M x y
      = embInd emb retr x * embInd emb retr y * M (retr x) (retr y) := rfl

lemma embInd_nonneg (x : B) : 0 ≤ embInd emb retr x := by
  rw [embInd]; split_ifs <;> norm_num

lemma embInd_le_one (x : B) : embInd emb retr x ≤ 1 := by
  rw [embInd]; split_ifs <;> norm_num

section Retraction

variable (hre : ∀ a, retr (emb a) = a)
include hre

lemma embInd_emb (a : A) : embInd emb retr (emb a) = 1 := by
  rw [embInd, hre, if_pos rfl]

lemma emb_injective : Function.Injective emb := fun a a' h => by
  have := congrArg retr h
  rwa [hre, hre] at this

lemma embMat_apply_emb (M : Matrix A A ℝ) (a a' : A) :
    embMat emb retr M (emb a) (emb a') = M a a' := by
  rw [embMat_apply, embInd_emb hre, embInd_emb hre, hre, hre, one_mul,
    one_mul]

lemma embVec_emb (v : A → ℝ) (a : A) : embVec emb retr v (emb a) = v a := by
  rw [embVec, embInd_emb hre, hre, one_mul]

lemma embVec_ne_zero {v : A → ℝ} (hv : v ≠ 0) :
    embVec emb retr v ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
  exact Function.ne_iff.mpr ⟨emb a, by rwa [embVec_emb hre]⟩

/-- The key reindexing: an `embInd`-weighted sum over `B` collapses to a sum
over `A`. -/
lemma sum_embInd_mul (H : A → B → ℝ) :
    ∑ x, embInd emb retr x * H (retr x) x = ∑ a, H a (emb a) := by
  have hfilter : (Finset.univ.filter fun x : B => emb (retr x) = x)
      = Finset.univ.image emb := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro h
      exact ⟨retr x, h⟩
    · rintro ⟨a, rfl⟩
      rw [hre]
  calc ∑ x, embInd emb retr x * H (retr x) x
      = ∑ x ∈ Finset.univ.filter fun x : B => emb (retr x) = x,
          H (retr x) x := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [embInd]
        split_ifs <;> ring
    _ = ∑ x ∈ Finset.univ.image emb, H (retr x) x := by rw [hfilter]
    _ = ∑ a, H (retr (emb a)) (emb a) :=
        Finset.sum_image fun a _ a' _ h => emb_injective hre h
    _ = ∑ a, H a (emb a) := Finset.sum_congr rfl fun a _ => by rw [hre]

lemma dotProduct_embMat (M : Matrix A A ℝ) (u v : B → ℝ) :
    u ⬝ᵥ embMat emb retr M *ᵥ v = (u ∘ emb) ⬝ᵥ M *ᵥ (v ∘ emb) := by
  rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum]
  calc ∑ x, ∑ y, u x * embMat emb retr M x y * v y
      = ∑ x, embInd emb retr x
          * ∑ y, embInd emb retr y
              * (u x * M (retr x) (retr y) * v y) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [embMat_apply]
        ring
    _ = ∑ a, ∑ y, embInd emb retr y
          * (u (emb a) * M a (retr y) * v y) :=
        sum_embInd_mul hre fun a x => ∑ y, embInd emb retr y
          * (u x * M a (retr y) * v y)
    _ = ∑ a, ∑ a', u (emb a) * M a a' * v (emb a') :=
        Finset.sum_congr rfl fun a _ =>
          sum_embInd_mul hre fun a' y => u (emb a) * M a a' * v y
    _ = ∑ a, ∑ a', (u ∘ emb) a * M a a' * (v ∘ emb) a' := rfl

lemma comp_dotProduct_self_le (u : B → ℝ) :
    (u ∘ emb) ⬝ᵥ (u ∘ emb) ≤ u ⬝ᵥ u := by
  have h : ∀ x : B, u x * u x = u x ^ 2 := fun x => by ring
  calc (u ∘ emb) ⬝ᵥ (u ∘ emb) = ∑ a, u (emb a) ^ 2 := by
        rw [dotProduct]; exact Finset.sum_congr rfl fun a _ => h _
    _ = ∑ x ∈ Finset.univ.image emb, u x ^ 2 := by
        rw [Finset.sum_image fun a _ a' _ hh => emb_injective hre hh]
    _ ≤ ∑ x, u x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun x _ _ => sq_nonneg _
    _ = u ⬝ᵥ u := by
        rw [dotProduct]; exact Finset.sum_congr rfl fun x _ => (h x).symm

/-- **Extension by zero does not increase the norm.** -/
theorem l2_opNorm_embMat_le (M : Matrix A A ℝ) :
    ‖embMat emb retr M‖ ≤ ‖M‖ := by
  refine l2_opNorm_le_of_forall_dotProduct _ (norm_nonneg M) fun u v => ?_
  rw [dotProduct_embMat hre]
  calc |(u ∘ emb) ⬝ᵥ M *ᵥ (v ∘ emb)|
      ≤ ‖M‖ * Real.sqrt ((u ∘ emb) ⬝ᵥ (u ∘ emb))
          * Real.sqrt ((v ∘ emb) ⬝ᵥ (v ∘ emb)) :=
        abs_dotProduct_mulVec_le M _ _
    _ ≤ ‖M‖ * Real.sqrt (u ⬝ᵥ u)
          * Real.sqrt ((v ∘ emb) ⬝ᵥ (v ∘ emb)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (comp_dotProduct_self_le hre u))
          (norm_nonneg M)
    _ ≤ ‖M‖ * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) :=
        mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (comp_dotProduct_self_le hre v))
          (by positivity)

/-- **Eigenvectors extend by zero.** -/
lemma embMat_mulVec_embVec (M : Matrix A A ℝ) (v : A → ℝ) :
    embMat emb retr M *ᵥ embVec emb retr v
      = embVec emb retr (M *ᵥ v) := by
  funext x
  calc (embMat emb retr M *ᵥ embVec emb retr v) x
      = ∑ y, embMat emb retr M x y * embVec emb retr v y := rfl
    _ = embInd emb retr x * ∑ y, embInd emb retr y
          * (M (retr x) (retr y) * v (retr y)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [embMat_apply, embVec]
        have h : embInd emb retr y * embInd emb retr y
            = embInd emb retr y := by
          rw [embInd]; split_ifs <;> ring
        calc embInd emb retr x * embInd emb retr y * M (retr x) (retr y)
              * (embInd emb retr y * v (retr y))
            = embInd emb retr x * ((embInd emb retr y * embInd emb retr y)
                * (M (retr x) (retr y) * v (retr y))) := by ring
          _ = embInd emb retr x * (embInd emb retr y
                * (M (retr x) (retr y) * v (retr y))) := by rw [h]
    _ = embInd emb retr x * ∑ a', M (retr x) a' * v a' := by
        rw [sum_embInd_mul hre fun a' y => M (retr x) a' * v (retr y)]
        congr 1
        refine Finset.sum_congr rfl fun a' _ => by rw [hre]
    _ = embVec emb retr (M *ᵥ v) x := rfl

end Retraction

lemma embMat_isHermitian {M : Matrix A A ℝ} (hM : M.IsHermitian) :
    (embMat emb retr M).IsHermitian := by
  have key : ∀ p q, M q p = M p q := fun p q => by
    conv_lhs => rw [← hM]
    simp [Matrix.conjTranspose_apply]
  refine Matrix.IsHermitian.ext fun x y => ?_
  simp only [Matrix.conjTranspose_apply, embMat_apply, star_trivial]
  rw [key (retr y) (retr x)]
  ring

lemma embMat_hadamard (M : Matrix A A ℝ) (N : Matrix B B ℝ) :
    embMat emb retr M ⊙ N
      = embMat emb retr (M ⊙ N.submatrix emb emb) := by
  ext x y
  simp only [Matrix.hadamard_apply, embMat_apply, Matrix.submatrix_apply,
    embInd]
  by_cases hx : emb (retr x) = x
  · by_cases hy : emb (retr y) = y
    · rw [if_pos hx, if_pos hy, hx, hy]
      ring
    · rw [if_neg hy]
      ring
  · rw [if_neg hx]
    ring

end Embed

/-! ## The matching bound -/

/-- Cauchy–Schwarz for dot products (public copy of the `EDLower` version). -/
lemma abs_dotProduct_le_sqrt {X : Type*} [Fintype X] (v w : X → ℝ) :
    |v ⬝ᵥ w| ≤ Real.sqrt (v ⬝ᵥ v) * Real.sqrt (w ⬝ᵥ w) := by
  have hsq : ∀ u : X → ℝ, (∑ t, u t ^ 2) = u ⬝ᵥ u := fun u => by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [abs_le]
  constructor
  · have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun t => -v t) w
    have hrw : (∑ t, -v t * w t) = -(v ⬝ᵥ w) := by
      rw [dotProduct, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    have hneg : (∑ t, (-v t) ^ 2) = v ⬝ᵥ v := by
      rw [← hsq v]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hrw, hneg, hsq w] at h
    linarith
  · have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ v w
    rw [hsq v, hsq w] at h
    exact h.trans_eq' (by rw [dotProduct])

/-- **A matrix supported on the graph of a bijection, with entries of
absolute value at most one, has operator norm at most one** — the matching
bound for `Γ ⊙ Δᵢ` masks. -/
theorem l2_opNorm_le_one_of_equiv_support {X : Type*} [Fintype X]
    [DecidableEq X] (M : Matrix X X ℝ) (μ : X ≃ X)
    (hsupp : ∀ x y, y ≠ μ x → M x y = 0) (hent : ∀ x y, |M x y| ≤ 1) :
    ‖M‖ ≤ 1 := by
  refine l2_opNorm_le_of_forall_dotProduct _ zero_le_one fun u v => ?_
  rw [dotProduct_mulVec_eq_sum]
  have hrow : ∀ x, ∑ y, u x * M x y * v y = u x * (M x (μ x) * v (μ x)) :=
    fun x => by
      rw [Finset.sum_eq_single (μ x)
        (fun y _ hy => by rw [hsupp x y hy]; ring)
        (fun h => absurd (Finset.mem_univ _) h)]
      ring
  rw [Finset.sum_congr rfl fun x _ => hrow x]
  set w : X → ℝ := fun x => M x (μ x) * v (μ x) with hw
  have h1 : |∑ x, u x * w x| ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (w ⬝ᵥ w) :=
    abs_dotProduct_le_sqrt u w
  have h2 : w ⬝ᵥ w ≤ v ⬝ᵥ v := by
    calc w ⬝ᵥ w = ∑ x, (M x (μ x) * v (μ x)) * (M x (μ x) * v (μ x)) := rfl
      _ ≤ ∑ x, v (μ x) * v (μ x) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have hm := hent x (μ x)
          have ha : M x (μ x) * M x (μ x) ≤ 1 := by
            have h := abs_mul_abs_self (M x (μ x))
            nlinarith [abs_nonneg (M x (μ x))]
          nlinarith [ha, mul_self_nonneg (v (μ x))]
      _ = ∑ x, v x * v x := μ.sum_comp fun x => v x * v x
      _ = v ⬝ᵥ v := rfl
  calc |∑ x, u x * w x|
      ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (w ⬝ᵥ w) := h1
    _ ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by
        gcongr
    _ = 1 * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by ring

end MonoidProduct
