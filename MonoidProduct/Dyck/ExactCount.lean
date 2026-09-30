import QuantumQueryComplexity.Promise.Basic
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The exact-count promise and its adversary witness

`Ex_{2m}^{m|m+1}`: read `2m` bits promised to contain either `m` or `m+1`
zeros, and decide which.  This is the inner problem of the recursive Dyck
construction of Ambainis et al., Appendix E.

The witness is the inclusion graph between the two promised Hamming layers,

  `exactGamma m x y = 1  ↔  zeroSet x ⊂ zeroSet y  or  zeroSet y ⊂ zeroSet x`,

a biregular bipartite graph with left degree `m` (an `m`-set has `2m - m = m`
supersets of size `m+1`) and right degree `m+1` (an `(m+1)`-set has `m+1`
subsets of size `m`).  Hence

  `sqrt_mul_succ_le_advPMOn_exactCount : √(m(m+1)) ≤ ADV±(Ex_{2m}^{m|m+1})`.

## Only the lower bound on `‖Γ‖` is proved

The spectral norm is `‖Γ‖ = √(m(m+1))`, but `norm_div_le_advPMOn` consumes a *lower*
bound on `‖Γ‖` and an *upper* bound on the masked norms, so the `≤` direction of
the norm is never used.  It is therefore not proved: the lower bound comes from
an explicit eigenvector (`exactVec`, taking `√m` on the `m`-layer and `√(m+1)`
on the `(m+1)`-layer), for which the eigenvalue equation is exactly the two
degree counts.  That replaces a Cauchy–Schwarz analysis of the bipartite
bilinear form by a pair of `Finset.card_bij` arguments.

## Masks are partial matchings

A supported pair differs in exactly one coordinate, so masking at `i` leaves at
most one nonzero entry in each row and column (`mask_zeroSet`).  The norm bound
is then the Schur test `l2_opNorm_le_of_rowcol_le`, itself obtained from the
rescaling lemma `l2_opNorm_le_of_quadratic`: a bound of the shape
`|uᵀAv| ≤ (c/2)(‖u‖² + ‖v‖²)` upgrades to `‖A‖ ≤ c` by applying it to
`(‖v‖ • u, ‖u‖ • v)`.  Both are general and would sit naturally in
`QuantumQueryComplexity/Spectral.lean`; they are here only because editing that file
rebuilds the entire project.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Two general operator-norm tools -/

section NormTools

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Rescaling.**  A *quadratic* bilinear bound upgrades to an operator-norm
bound: the bilinear form is bihomogeneous, so applying the hypothesis at
`(‖v‖ • u, ‖u‖ • v)` turns the arithmetic-mean bound into a geometric-mean
one. -/
theorem l2_opNorm_le_of_quadratic {A : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ u v : n → ℝ, |u ⬝ᵥ A *ᵥ v| ≤ c / 2 * ((u ⬝ᵥ u) + (v ⬝ᵥ v))) :
    ‖A‖ ≤ c := by
  refine l2_opNorm_le_of_forall_dotProduct A hc fun u v => ?_
  by_cases hu : u = 0
  · subst hu
    simp
  by_cases hv : v = 0
  · subst hv
    simp
  have huu : 0 < u ⬝ᵥ u := by
    rcases (dotProduct_self_nonneg u).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (dotProduct_self_eq_zero.mp h'.symm) hu
  have hvv : 0 < v ⬝ᵥ v := by
    rcases (dotProduct_self_nonneg v).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (dotProduct_self_eq_zero.mp h'.symm) hv
  set p := Real.sqrt (u ⬝ᵥ u) with hpdef
  set q := Real.sqrt (v ⬝ᵥ v) with hqdef
  have hp : 0 < p := Real.sqrt_pos.mpr huu
  have hq : 0 < q := Real.sqrt_pos.mpr hvv
  have hpp : p * p = u ⬝ᵥ u := Real.mul_self_sqrt (dotProduct_self_nonneg u)
  have hqq : q * q = v ⬝ᵥ v := Real.mul_self_sqrt (dotProduct_self_nonneg v)
  have key := h (q • u) (p • v)
  have hL : (q • u) ⬝ᵥ A *ᵥ (p • v) = (q * p) * (u ⬝ᵥ A *ᵥ v) := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  have hU : (q • u) ⬝ᵥ (q • u) = q * q * (u ⬝ᵥ u) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hV : (p • v) ⬝ᵥ (p • v) = p * p * (v ⬝ᵥ v) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hL, hU, hV, ← hpp, ← hqq, abs_mul,
    abs_of_pos (mul_pos hq hp)] at key
  refine le_of_mul_le_mul_left (key.trans (le_of_eq ?_)) (mul_pos hq hp)
  ring

/-- **Schur test** with a common row/column bound. -/
theorem l2_opNorm_le_of_rowcol_le {A : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hrow : ∀ x, ∑ y, |A x y| ≤ c) (hcol : ∀ y, ∑ x, |A x y| ≤ c) :
    ‖A‖ ≤ c := by
  refine l2_opNorm_le_of_quadratic hc fun u v => ?_
  have hAM : ∀ x y : n, |u x * A x y * v y|
      ≤ |A x y| * ((u x * u x + v y * v y) / 2) := by
    intro x y
    have hst : |u x| * |v y| ≤ (u x * u x + v y * v y) / 2 := by
      nlinarith [mul_self_nonneg (|u x| - |v y|), abs_mul_abs_self (u x),
        abs_mul_abs_self (v y), abs_nonneg (u x), abs_nonneg (v y)]
    calc |u x * A x y * v y| = |A x y| * (|u x| * |v y|) := by
          rw [abs_mul, abs_mul]
          ring
      _ ≤ |A x y| * ((u x * u x + v y * v y) / 2) :=
          mul_le_mul_of_nonneg_left hst (abs_nonneg _)
  have hS1 : ∑ x, ∑ y, |A x y| * (u x * u x) ≤ c * (u ⬝ᵥ u) := by
    calc ∑ x, ∑ y, |A x y| * (u x * u x)
        = ∑ x, (∑ y, |A x y|) * (u x * u x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_mul]
      _ ≤ ∑ x, c * (u x * u x) :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_right (hrow x) (mul_self_nonneg _)
      _ = c * (u ⬝ᵥ u) := by rw [← Finset.mul_sum]; rfl
  have hS2 : ∑ x, ∑ y, |A x y| * (v y * v y) ≤ c * (v ⬝ᵥ v) := by
    calc ∑ x, ∑ y, |A x y| * (v y * v y)
        = ∑ y, ∑ x, |A x y| * (v y * v y) := Finset.sum_comm
      _ = ∑ y, (∑ x, |A x y|) * (v y * v y) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_mul]
      _ ≤ ∑ y, c * (v y * v y) :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_right (hcol y) (mul_self_nonneg _)
      _ = c * (v ⬝ᵥ v) := by rw [← Finset.mul_sum]; rfl
  have hsplit : ∑ x, ∑ y, |A x y| * ((u x * u x + v y * v y) / 2)
      = (∑ x, ∑ y, |A x y| * (u x * u x)) / 2
        + (∑ x, ∑ y, |A x y| * (v y * v y)) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  calc |u ⬝ᵥ A *ᵥ v|
      = |∑ x, ∑ y, u x * A x y * v y| := by rw [dotProduct_mulVec_eq_sum]
    _ ≤ ∑ x, ∑ y, |u x * A x y * v y| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x, ∑ y, |A x y| * ((u x * u x + v y * v y) / 2) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hAM x y
    _ = (∑ x, ∑ y, |A x y| * (u x * u x)) / 2
        + (∑ x, ∑ y, |A x y| * (v y * v y)) / 2 := hsplit
    _ ≤ c * (u ⬝ᵥ u) / 2 + c * (v ⬝ᵥ v) / 2 := by
        gcongr
    _ = c / 2 * ((u ⬝ᵥ u) + (v ⬝ᵥ v)) := by ring

/-- A nonnegative family bounded by `1` with at most one nonzero member sums to
at most `1`. -/
theorem sum_le_one_of_unique_support {ι : Type*} [Fintype ι] {f : ι → ℝ}
    (h1 : ∀ i, f i ≤ 1) (huniq : ∀ i j, f i ≠ 0 → f j ≠ 0 → i = j) :
    ∑ i, f i ≤ 1 := by
  by_cases h : ∀ i, f i = 0
  · rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const_zero]
    exact zero_le_one
  · push_neg at h
    obtain ⟨i₀, hi₀⟩ := h
    rw [Finset.sum_eq_single i₀]
    · exact h1 i₀
    · intro j _ hj
      by_contra hfj
      exact hj (huniq j i₀ hfj hi₀)
    · intro hc
      exact absurd (Finset.mem_univ _) hc

end NormTools

/-! ## The exact-count promise -/

/-- The set of `false` positions — `false` is the counted value, matching the
parenthesis convention in which `false` opens. -/
def zeroSet {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = false

/-- The number of `false` positions. -/
def falseCount {n : ℕ} (x : Fin n → Bool) : ℕ := (zeroSet x).card

@[simp] lemma mem_zeroSet {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    i ∈ zeroSet x ↔ x i = false := by simp [zeroSet]

lemma falseCount_eq_card {n : ℕ} (x : Fin n → Bool) :
    falseCount x = (zeroSet x).card := rfl

lemma zeroSet_injective {n : ℕ} : Function.Injective (zeroSet (n := n)) := by
  intro x y h
  funext i
  have hi := Finset.ext_iff.mp h i
  rw [mem_zeroSet, mem_zeroSet] at hi
  cases hx : x i <;> cases hy : y i <;> simp_all

lemma zeroSet_indicator {n : ℕ} (s : Finset (Fin n)) :
    zeroSet (fun k => decide (k ∉ s)) = s := by
  ext k
  simp [mem_zeroSet]

lemma zeroSet_update_false {n : ℕ} (x : Fin n → Bool) (j : Fin n) :
    zeroSet (Function.update x j false) = insert j (zeroSet x) := by
  ext i
  by_cases hij : i = j
  · subst hij
    simp [Function.update_self]
  · simp [Function.update_of_ne hij, hij]

lemma zeroSet_update_true {n : ℕ} (x : Fin n → Bool) (j : Fin n) :
    zeroSet (Function.update x j true) = (zeroSet x).erase j := by
  ext i
  by_cases hij : i = j
  · subst hij
    simp [Function.update_self]
  · simp [Function.update_of_ne hij, hij]

/-- Two words agree at `i` exactly when `i` has the same membership status in
the two zero sets. -/
lemma apply_eq_iff_mem_iff {n : ℕ} (x y : Fin n → Bool) (i : Fin n) :
    x i = y i ↔ (i ∈ zeroSet x ↔ i ∈ zeroSet y) := by
  rw [mem_zeroSet, mem_zeroSet]
  cases hx : x i <;> cases hy : y i <;> simp

/-- **The exact-count promise domain**: `2m` bits, either `m` or `m+1` of them
`false`. -/
def ExactDom (m : ℕ) : Type :=
  {x : Fin (2 * m) → Bool // falseCount x = m ∨ falseCount x = m + 1}

instance ExactDom.instDecidableEq (m : ℕ) : DecidableEq (ExactDom m) :=
  Subtype.instDecidableEq

instance ExactDom.instFintype (m : ℕ) : Fintype (ExactDom m) :=
  Subtype.fintype _

/-- The observation map: a query reads one bit of the word. -/
def exactRead {m : ℕ} (x : ExactDom m) : Fin (2 * m) → Bool := x.1

/-- The answer: `true` exactly on the lower layer. -/
def exactOut (m : ℕ) (x : ExactDom m) : Bool := decide (falseCount x.1 = m)

lemma exactRead_injective {m : ℕ} :
    Function.Injective (exactRead (m := m)) := fun _ _ h => Subtype.ext h

lemma exactDom_card (m : ℕ) (x : ExactDom m) :
    (zeroSet x.1).card = m ∨ (zeroSet x.1).card = m + 1 := x.2

lemma exactOut_of_card_eq {m : ℕ} {x : ExactDom m}
    (h : (zeroSet x.1).card = m) : exactOut m x = true := by
  simp [exactOut, falseCount_eq_card, h]

lemma exactOut_of_card_eq_succ {m : ℕ} {x : ExactDom m}
    (h : (zeroSet x.1).card = m + 1) : exactOut m x = false := by
  simp [exactOut, falseCount_eq_card, h]

lemma nonempty_exactDom (m : ℕ) : Nonempty (ExactDom m) := by
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (2 * m))))
      (n := m) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  exact ⟨⟨fun k => decide (k ∉ s), Or.inl (by
    rw [falseCount_eq_card, zeroSet_indicator, hs])⟩⟩

/-! ## The inclusion-graph witness -/

/-- The inclusion matrix of the two promised layers. -/
def exactGamma (m : ℕ) : Matrix (ExactDom m) (ExactDom m) ℝ :=
  Matrix.of fun x y =>
    if zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1 then 1 else 0

lemma exactGamma_apply (m : ℕ) (x y : ExactDom m) :
    exactGamma m x y =
      if zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1 then 1 else 0 :=
  rfl

lemma exactGamma_symm (m : ℕ) (x y : ExactDom m) :
    exactGamma m x y = exactGamma m y x := by
  rw [exactGamma_apply, exactGamma_apply]
  exact if_congr or_comm rfl rfl

lemma exactGamma_isHermitian (m : ℕ) : (exactGamma m).IsHermitian := by
  show (exactGamma m)ᴴ = exactGamma m
  ext x y
  rw [Matrix.conjTranspose_apply, star_trivial]
  exact exactGamma_symm m y x

/-- A supported pair straddles the two layers. -/
lemma neighbour_card {m : ℕ} {x y : ExactDom m}
    (h : zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1) :
    ((zeroSet x.1).card = m ∧ (zeroSet y.1).card = m + 1)
      ∨ ((zeroSet x.1).card = m + 1 ∧ (zeroSet y.1).card = m) := by
  have hx := exactDom_card m x
  have hy := exactDom_card m y
  rcases h with h | h <;>
    · have hlt := Finset.card_lt_card h
      omega

lemma exactGamma_apply_eq_zero {m : ℕ} {x y : ExactDom m}
    (h : exactOut m x = exactOut m y) : exactGamma m x y = 0 := by
  rw [exactGamma_apply, if_neg]
  intro hss
  rcases neighbour_card hss with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [exactOut_of_card_eq h1, exactOut_of_card_eq_succ h2] at h
    exact Bool.noConfusion h
  · rw [exactOut_of_card_eq_succ h1, exactOut_of_card_eq h2] at h
    exact Bool.noConfusion h

lemma isAdvMatrixOn_exactGamma (m : ℕ) :
    IsAdvMatrixOn (exactOut m) (exactGamma m) :=
  ⟨exactGamma_isHermitian m, fun _ _ h => exactGamma_apply_eq_zero h⟩

/-! ### The two degree counts -/

/-- Turning a `true` coordinate `false` moves an `m`-set up one layer. -/
def upNbr {m : ℕ} (x : ExactDom m) (hx : (zeroSet x.1).card = m)
    (j : Fin (2 * m)) (hj : j ∉ zeroSet x.1) : ExactDom m :=
  ⟨Function.update x.1 j false, Or.inr (by
    rw [falseCount_eq_card, zeroSet_update_false,
      Finset.card_insert_of_notMem hj, hx])⟩

/-- Turning a `false` coordinate `true` moves an `(m+1)`-set down one layer. -/
def downNbr {m : ℕ} (x : ExactDom m) (hx : (zeroSet x.1).card = m + 1)
    (j : Fin (2 * m)) (hj : j ∈ zeroSet x.1) : ExactDom m :=
  ⟨Function.update x.1 j true, Or.inl (by
    rw [falseCount_eq_card, zeroSet_update_true, Finset.card_erase_of_mem hj,
      hx]
    omega)⟩

@[simp] lemma upNbr_val {m : ℕ} (x : ExactDom m) (hx : (zeroSet x.1).card = m)
    (j : Fin (2 * m)) (hj : j ∉ zeroSet x.1) :
    (upNbr x hx j hj).1 = Function.update x.1 j false := rfl

@[simp] lemma downNbr_val {m : ℕ} (x : ExactDom m)
    (hx : (zeroSet x.1).card = m + 1) (j : Fin (2 * m)) (hj : j ∈ zeroSet x.1) :
    (downNbr x hx j hj).1 = Function.update x.1 j true := rfl

/-- The neighbourhood of a point, as a `Finset`. -/
def nbhd {m : ℕ} (x : ExactDom m) : Finset (ExactDom m) :=
  Finset.univ.filter fun y => zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1

@[simp] lemma mem_nbhd {m : ℕ} (x y : ExactDom m) :
    y ∈ nbhd x ↔ zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1 := by
  simp [nbhd]

/-- **Left degree**: an `m`-set has exactly `m` neighbours. -/
lemma card_nbhd_of_card_eq {m : ℕ} (x : ExactDom m)
    (hx : (zeroSet x.1).card = m) : (nbhd x).card = m := by
  classical
  have hcompl : ((zeroSet x.1)ᶜ).card = m := by
    rw [Finset.card_compl, hx, Fintype.card_fin]
    omega
  have hbij : ((zeroSet x.1)ᶜ).card = (nbhd x).card := by
    refine Finset.card_bij
      (fun j hj => upNbr x hx j (Finset.mem_compl.mp hj)) ?_ ?_ ?_
    · intro j hj
      rw [mem_nbhd]
      refine Or.inl ?_
      show zeroSet x.1 ⊂ zeroSet (Function.update x.1 j false)
      rw [zeroSet_update_false]
      exact Finset.ssubset_insert (Finset.mem_compl.mp hj)
    · intro j hj j' hj' hEq
      by_contra hne
      have hval : Function.update x.1 j false = Function.update x.1 j' false :=
        congrArg Subtype.val hEq
      have h1 := congrFun hval j
      rw [Function.update_self, Function.update_of_ne hne] at h1
      exact (Finset.mem_compl.mp hj) ((mem_zeroSet x.1 j).mpr h1.symm)
    · intro y hy
      rw [mem_nbhd] at hy
      have hup : zeroSet x.1 ⊂ zeroSet y.1 := by
        rcases hy with h | h
        · exact h
        · exact absurd (Finset.card_lt_card h)
            (by have := exactDom_card m y; omega)
      have hcy : (zeroSet y.1).card = m + 1 := by
        have := Finset.card_lt_card hup
        have := exactDom_card m y
        omega
      obtain ⟨j, hjy, hjx⟩ := Finset.exists_of_ssubset hup
      refine ⟨j, Finset.mem_compl.mpr hjx, ?_⟩
      refine Subtype.ext (zeroSet_injective ?_)
      rw [upNbr_val, zeroSet_update_false]
      refine Finset.eq_of_subset_of_card_le
        (Finset.insert_subset hjy hup.subset) ?_
      have hc : (insert j (zeroSet x.1)).card = m + 1 := by
        rw [Finset.card_insert_of_notMem hjx, hx]
      omega
  rw [← hbij, hcompl]

/-- **Right degree**: an `(m+1)`-set has exactly `m+1` neighbours. -/
lemma card_nbhd_of_card_eq_succ {m : ℕ} (x : ExactDom m)
    (hx : (zeroSet x.1).card = m + 1) : (nbhd x).card = m + 1 := by
  classical
  have hbij : (zeroSet x.1).card = (nbhd x).card := by
    refine Finset.card_bij (fun j hj => downNbr x hx j hj) ?_ ?_ ?_
    · intro j hj
      rw [mem_nbhd]
      refine Or.inr ?_
      show zeroSet (Function.update x.1 j true) ⊂ zeroSet x.1
      rw [zeroSet_update_true]
      exact Finset.erase_ssubset hj
    · intro j hj j' hj' hEq
      by_contra hne
      have hval : Function.update x.1 j true = Function.update x.1 j' true :=
        congrArg Subtype.val hEq
      have h1 := congrFun hval j
      rw [Function.update_self, Function.update_of_ne hne] at h1
      have : x.1 j = false := (mem_zeroSet x.1 j).mp hj
      rw [this] at h1
      exact Bool.noConfusion h1
    · intro y hy
      rw [mem_nbhd] at hy
      have hdown : zeroSet y.1 ⊂ zeroSet x.1 := by
        rcases hy with h | h
        · exact absurd (Finset.card_lt_card h)
            (by have := exactDom_card m y; omega)
        · exact h
      have hcy : (zeroSet y.1).card = m := by
        have := Finset.card_lt_card hdown
        have := exactDom_card m y
        omega
      obtain ⟨j, hjx, hjy⟩ := Finset.exists_of_ssubset hdown
      refine ⟨j, hjx, ?_⟩
      refine Subtype.ext (zeroSet_injective ?_)
      rw [downNbr_val, zeroSet_update_true]
      symm
      refine Finset.eq_of_subset_of_card_le
        (Finset.subset_erase.mpr ⟨hdown.subset, hjy⟩) ?_
      have hc : ((zeroSet x.1).erase j).card = m := by
        rw [Finset.card_erase_of_mem hjx, hx]
        omega
      omega
  rw [← hbij, hx]

/-! ### The eigenvector -/

/-- `√m` on the lower layer, `√(m+1)` on the upper one. -/
noncomputable def exactVec (m : ℕ) : ExactDom m → ℝ :=
  fun x => if (zeroSet x.1).card = m then Real.sqrt m else Real.sqrt (m + 1)

lemma exactGamma_mulVec_apply (m : ℕ) (u : ExactDom m → ℝ) (x : ExactDom m) :
    (exactGamma m *ᵥ u) x = ∑ y ∈ nbhd x, u y := by
  show ∑ y, exactGamma m x y * u y = _
  rw [nbhd, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [exactGamma_apply]
  by_cases h : zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

lemma exactGamma_mulVec_exactVec (m : ℕ) :
    exactGamma m *ᵥ exactVec m = Real.sqrt ((m : ℝ) * (m + 1)) • exactVec m := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsplit : Real.sqrt ((m : ℝ) * (m + 1))
      = Real.sqrt (m : ℝ) * Real.sqrt ((m : ℝ) + 1) := Real.sqrt_mul hm0 _
  have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
    Real.mul_self_sqrt hm0
  have hsq' : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  funext x
  rw [exactGamma_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  rcases exactDom_card m x with hx | hx
  · -- lower layer: `m` neighbours, all on the upper layer
    have hconst : ∀ y ∈ nbhd x, exactVec m y = Real.sqrt ((m : ℝ) + 1) := by
      intro y hy
      rw [mem_nbhd] at hy
      rcases neighbour_card hy with ⟨_, h2⟩ | ⟨h1, _⟩
      · rw [exactVec, if_neg (by omega)]
      · omega
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      card_nbhd_of_card_eq x hx, nsmul_eq_mul, exactVec, if_pos hx, hsplit]
    push_cast
    linear_combination (-Real.sqrt ((m : ℝ) + 1)) * hsq
  · -- upper layer: `m+1` neighbours, all on the lower layer
    have hconst : ∀ y ∈ nbhd x, exactVec m y = Real.sqrt (m : ℝ) := by
      intro y hy
      rw [mem_nbhd] at hy
      rcases neighbour_card hy with ⟨h1, _⟩ | ⟨_, h2⟩
      · omega
      · rw [exactVec, if_pos h2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      card_nbhd_of_card_eq_succ x hx, nsmul_eq_mul, exactVec,
      if_neg (by omega), hsplit]
    push_cast
    linear_combination (-Real.sqrt ((m : ℝ))) * hsq'

lemma exactVec_ne_zero (m : ℕ) (hm : 0 < m) : exactVec m ≠ 0 := by
  obtain ⟨x⟩ := nonempty_exactDom m
  intro h
  have hx := congrFun h x
  rw [Pi.zero_apply, exactVec] at hx
  have hpos : (0 : ℝ) < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hpos' : (0 : ℝ) < Real.sqrt ((m : ℝ) + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  split at hx
  · exact hpos.ne' hx
  · exact hpos'.ne' hx

theorem sqrt_le_norm_exactGamma (m : ℕ) (hm : 0 < m) :
    Real.sqrt ((m : ℝ) * (m + 1)) ≤ ‖exactGamma m‖ := by
  have h := abs_eigenvalue_le_norm (exactGamma_mulVec_exactVec m)
    (exactVec_ne_zero m hm)
  rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h

/-! ### The coordinate masks are partial matchings -/

/-- A masked neighbour is determined: the two words differ in exactly the
masked coordinate. -/
lemma mask_zeroSet {m : ℕ} (i : Fin (2 * m)) {x y : ExactDom m}
    (h : (exactGamma m ⊙ advDOn (exactRead (m := m)) i) x y ≠ 0) :
    ((zeroSet x.1).card = m ∧ zeroSet y.1 = insert i (zeroSet x.1))
      ∨ ((zeroSet x.1).card = m + 1 ∧ zeroSet y.1 = (zeroSet x.1).erase i) := by
  rw [hadamard_advDOn_apply] at h
  have hne : ¬ exactRead x i = exactRead y i := by
    intro hc
    rw [if_pos hc] at h
    exact h rfl
  rw [if_neg hne] at h
  have hss : zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1 := by
    by_contra hc
    rw [exactGamma_apply, if_neg hc] at h
    exact h rfl
  have hmem : ¬ (i ∈ zeroSet x.1 ↔ i ∈ zeroSet y.1) := by
    intro hc
    exact hne ((apply_eq_iff_mem_iff x.1 y.1 i).mpr hc)
  rcases neighbour_card hss with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    have hup : zeroSet x.1 ⊂ zeroSet y.1 := by
      rcases hss with hs | hs
      · exact hs
      · exact absurd (Finset.card_lt_card hs) (by omega)
    have hix : i ∉ zeroSet x.1 := fun hc => hmem ⟨fun _ => hup.subset hc, fun _ => hc⟩
    have hiy : i ∈ zeroSet y.1 := by
      by_contra hc
      exact hmem ⟨fun hc' => absurd hc' hix, fun hc' => absurd hc' hc⟩
    symm
    refine Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hiy hup.subset) ?_
    have hc : (insert i (zeroSet x.1)).card = m + 1 := by
      rw [Finset.card_insert_of_notMem hix, h1]
    omega
  · refine Or.inr ⟨h1, ?_⟩
    have hdown : zeroSet y.1 ⊂ zeroSet x.1 := by
      rcases hss with hs | hs
      · exact absurd (Finset.card_lt_card hs) (by omega)
      · exact hs
    have hiy : i ∉ zeroSet y.1 := fun hc => hmem ⟨fun _ => hc, fun _ => hdown.subset hc⟩
    have hix : i ∈ zeroSet x.1 := by
      by_contra hc
      exact hmem ⟨fun hc' => absurd hc' hc, fun hc' => absurd hc' hiy⟩
    refine Finset.eq_of_subset_of_card_le
      (Finset.subset_erase.mpr ⟨hdown.subset, hiy⟩) ?_
    have hc : ((zeroSet x.1).erase i).card = m := by
      rw [Finset.card_erase_of_mem hix, h1]
      omega
    omega

lemma mask_row_le_one {m : ℕ} (i : Fin (2 * m)) (x : ExactDom m) :
    ∑ y, |(exactGamma m ⊙ advDOn (exactRead (m := m)) i) x y| ≤ 1 := by
  refine sum_le_one_of_unique_support ?_ ?_
  · intro y
    rw [hadamard_advDOn_apply, exactGamma_apply]
    split
    · rw [abs_zero]
      exact zero_le_one
    · split
      · rw [abs_one]
      · rw [abs_zero]
        exact zero_le_one
  · intro y z hy hz
    have hy' := mask_zeroSet i (fun hc => hy (by rw [hc, abs_zero]))
    have hz' := mask_zeroSet i (fun hc => hz (by rw [hc, abs_zero]))
    refine Subtype.ext (zeroSet_injective ?_)
    rcases hy' with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
      rcases hz' with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
    · rw [hy2, hz2]
    · omega
    · omega
    · rw [hy2, hz2]

theorem norm_exactGamma_hadamard_le_one (m : ℕ) (i : Fin (2 * m)) :
    ‖exactGamma m ⊙ advDOn (exactRead (m := m)) i‖ ≤ 1 := by
  have hsymm : ∀ x y : ExactDom m,
      (exactGamma m ⊙ advDOn (exactRead (m := m)) i) x y
        = (exactGamma m ⊙ advDOn (exactRead (m := m)) i) y x := by
    intro x y
    rw [hadamard_advDOn_apply, hadamard_advDOn_apply, exactGamma_symm m x y]
    exact if_congr eq_comm rfl rfl
  refine l2_opNorm_le_of_rowcol_le zero_le_one (mask_row_le_one i) fun y => ?_
  rw [Finset.sum_congr rfl fun x _ => by rw [hsymm x y]]
  exact mask_row_le_one i y

/-! ## The exact-count lower bounds -/

/-- **The exact-count lower bound**: the exact-count promise problem has adversary bound at
least `√(m(m+1))`. -/
theorem sqrt_mul_succ_le_advPMOn_exactCount (m : ℕ) (hm : 0 < m) :
    Real.sqrt ((m : ℝ) * (m + 1))
      ≤ advPMOn (exactRead (m := m)) (exactOut m) := by
  have hdet := separates_of_injective (exactRead_injective (m := m)) (exactOut m)
  have h := norm_div_le_advPMOn hdet (isAdvMatrixOn_exactGamma m)
    (norm_exactGamma_hadamard_le_one m) one_pos
  rw [div_one] at h
  exact (sqrt_le_norm_exactGamma m hm).trans h

/-! ### Finite checks

`|ExactDom m| = C(2m, m) + C(2m, m+1)`, and the two degree counts hold on the
nose.  These exercise the definitions against independent arithmetic; the
degrees are the informative check, since the *proved* norm statement is a lower
bound and a numerical spectral comparison would only test the unproved
converse. -/

example : Fintype.card (ExactDom 1) = 3 := by decide
example : Fintype.card (ExactDom 2) = 10 := by decide

example : ∀ x : ExactDom 1,
    (nbhd x).card = if (zeroSet x.1).card = 1 then 1 else 2 := by decide

example : ∀ x : ExactDom 2,
    (nbhd x).card = if (zeroSet x.1).card = 2 then 2 else 3 := by decide

/-- The convenient integer weakening. -/
theorem nat_le_advPMOn_exactCount (m : ℕ) (hm : 0 < m) :
    (m : ℝ) ≤ advPMOn (exactRead (m := m)) (exactOut m) := by
  refine le_trans ?_ (sqrt_mul_succ_le_advPMOn_exactCount m hm)
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : Real.sqrt ((m : ℝ) * (m : ℝ)) ≤ Real.sqrt ((m : ℝ) * ((m : ℝ) + 1)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_mul_self hm0] at h1

end MonoidProduct
