import MonoidProduct.Dyck.ExactCount
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The promised-AND star witness

The outer problem of the `√n` amplification: `r` bits promised to be either all
`true` or `true` except at one coordinate, and we must decide which.  Its
adversary matrix is the star with the all-`true` input at the centre, so

  `sqrt_le_advPMOn_andStar : √r ≤ ADV±(AndStar r)`.

## This is the `a = 0` layer of the same inclusion graph

`AndStarDom r` is `{x : Fin r → Bool // falseCount x = 0 ∨ falseCount x = 1}` —
literally `ExactDom`'s shape with the two promised layers `0` and `1` and an
arbitrary universe size.  The witness is again the inclusion matrix, and the
eigenvector argument is the same: the lower layer (here a single point, the
centre) carries `√(degree of the centre) = √r` and the upper layer carries
`√(degree of a leaf) = 1`.

Both files are instances of one biregular pattern — layers `a` and `a+1` inside
`Fin n`, degrees `n - a` and `a + 1`, norm `√((n-a)(a+1))`.  Factoring that out
would remove the duplication below; it is not done here because it would mean
reworking a file the whole Dyck development already depends on.  `ExactCount`
is the `n = 2m, a = m` instance and this is `a = 0`.

The two general norm tools (`l2_opNorm_le_of_rowcol_le`,
`sum_le_one_of_unique_support`) are reused from `ExactCount.lean` as they stand.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## The domain -/

/-- All-`true`, or `true` except at exactly one coordinate. -/
def AndStarDom (r : ℕ) : Type :=
  {x : Fin r → Bool // falseCount x = 0 ∨ falseCount x = 1}

instance AndStarDom.instDecidableEq (r : ℕ) : DecidableEq (AndStarDom r) :=
  Subtype.instDecidableEq

instance AndStarDom.instFintype (r : ℕ) : Fintype (AndStarDom r) :=
  Subtype.fintype _

/-- A query reads one bit. -/
def andStarRead {r : ℕ} (x : AndStarDom r) : Fin r → Bool := x.1

/-- `true` exactly on the all-`true` input. -/
def andStarOut (r : ℕ) (x : AndStarDom r) : Bool := decide (falseCount x.1 = 0)

lemma andStarRead_injective {r : ℕ} :
    Function.Injective (andStarRead (r := r)) := fun _ _ h => Subtype.ext h

lemma andStarDom_card {r : ℕ} (x : AndStarDom r) :
    (zeroSet x.1).card = 0 ∨ (zeroSet x.1).card = 1 := x.2

/-- The centre of the star: the all-`true` input. -/
def andStarCenter (r : ℕ) : AndStarDom r :=
  ⟨fun _ => true, Or.inl (by
    rw [falseCount, show zeroSet (fun _ : Fin r => true) = ∅ from by ext k; simp]
    exact Finset.card_empty)⟩

/-- The leaf that is `false` exactly at `i`. -/
def andStarLeaf {r : ℕ} (i : Fin r) : AndStarDom r :=
  ⟨fun k => decide (k ∉ ({i} : Finset (Fin r))), Or.inr (by
    rw [falseCount, zeroSet_indicator, Finset.card_singleton])⟩

@[simp] lemma zeroSet_andStarCenter (r : ℕ) :
    zeroSet (andStarCenter r).1 = ∅ := by
  ext k
  simp [andStarCenter]

@[simp] lemma zeroSet_andStarLeaf {r : ℕ} (i : Fin r) :
    zeroSet (andStarLeaf i).1 = {i} := zeroSet_indicator _

/-- A point of the promise is the centre or a leaf, according to its layer. -/
lemma eq_center_of_card_zero {r : ℕ} {x : AndStarDom r}
    (h : (zeroSet x.1).card = 0) : x = andStarCenter r := by
  refine Subtype.ext (zeroSet_injective ?_)
  rw [zeroSet_andStarCenter, Finset.card_eq_zero.mp h]

lemma exists_leaf_of_card_one {r : ℕ} {x : AndStarDom r}
    (h : (zeroSet x.1).card = 1) : ∃ i, x = andStarLeaf i := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  exact ⟨i, Subtype.ext (zeroSet_injective (by rw [hi, zeroSet_andStarLeaf]))⟩

/-! ## The star matrix -/

/-- The inclusion matrix on the two promised layers: a star. -/
def andStarGamma (r : ℕ) : Matrix (AndStarDom r) (AndStarDom r) ℝ :=
  Matrix.of fun x y =>
    if zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1 then 1 else 0

lemma andStarGamma_apply (r : ℕ) (x y : AndStarDom r) :
    andStarGamma r x y =
      if zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1 then 1 else 0 :=
  rfl

lemma andStarGamma_symm (r : ℕ) (x y : AndStarDom r) :
    andStarGamma r x y = andStarGamma r y x := by
  rw [andStarGamma_apply, andStarGamma_apply]
  exact if_congr or_comm rfl rfl

lemma andStarGamma_isHermitian (r : ℕ) : (andStarGamma r).IsHermitian := by
  show (andStarGamma r)ᴴ = andStarGamma r
  ext x y
  rw [Matrix.conjTranspose_apply, star_trivial]
  exact andStarGamma_symm r y x

/-- A supported pair straddles the two layers. -/
lemma andStar_neighbour_card {r : ℕ} {x y : AndStarDom r}
    (h : zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1) :
    ((zeroSet x.1).card = 0 ∧ (zeroSet y.1).card = 1)
      ∨ ((zeroSet x.1).card = 1 ∧ (zeroSet y.1).card = 0) := by
  have hx := andStarDom_card x
  have hy := andStarDom_card y
  rcases h with h | h <;>
    · have hlt := Finset.card_lt_card h
      omega

lemma andStarGamma_apply_eq_zero {r : ℕ} {x y : AndStarDom r}
    (h : andStarOut r x = andStarOut r y) : andStarGamma r x y = 0 := by
  rw [andStarGamma_apply, if_neg]
  intro hss
  rcases andStar_neighbour_card hss with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    · rw [andStarOut, andStarOut, falseCount, falseCount, h1, h2] at h
      simp at h

lemma isAdvMatrixOn_andStarGamma (r : ℕ) :
    IsAdvMatrixOn (andStarOut r) (andStarGamma r) :=
  ⟨andStarGamma_isHermitian r, fun _ _ h => andStarGamma_apply_eq_zero h⟩

/-! ## The two degrees -/

/-- The neighbourhood of a point. -/
def andStarNbhd {r : ℕ} (x : AndStarDom r) : Finset (AndStarDom r) :=
  Finset.univ.filter fun y =>
    zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1

@[simp] lemma mem_andStarNbhd {r : ℕ} (x y : AndStarDom r) :
    y ∈ andStarNbhd x ↔
      zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1 := by
  simp [andStarNbhd]

/-- **The centre has degree `r`.** -/
lemma card_andStarNbhd_center (r : ℕ) :
    (andStarNbhd (andStarCenter r)).card = r := by
  classical
  have hbij : (Finset.univ : Finset (Fin r)).card
      = (andStarNbhd (andStarCenter r)).card := by
    refine Finset.card_bij (fun i _ => andStarLeaf i) ?_ ?_ ?_
    · intro i _
      rw [mem_andStarNbhd]
      refine Or.inl ?_
      rw [zeroSet_andStarCenter, zeroSet_andStarLeaf]
      exact Finset.ssubset_iff_of_subset (Finset.empty_subset _) |>.mpr
        ⟨i, Finset.mem_singleton_self i, Finset.notMem_empty i⟩
    · intro i _ j _ hEq
      have := congrArg (fun z : AndStarDom r => zeroSet z.1) hEq
      rw [zeroSet_andStarLeaf, zeroSet_andStarLeaf] at this
      exact Finset.singleton_injective this
    · intro y hy
      rw [mem_andStarNbhd] at hy
      have hcy : (zeroSet y.1).card = 1 := by
        rcases andStar_neighbour_card hy with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact h2
        · rw [zeroSet_andStarCenter, Finset.card_empty] at h1
          exact absurd h1 (by omega)
      obtain ⟨i, rfl⟩ := exists_leaf_of_card_one hcy
      exact ⟨i, Finset.mem_univ i, rfl⟩
  rw [← hbij, Finset.card_univ, Fintype.card_fin]

/-- **A leaf has degree `1`.** -/
lemma card_andStarNbhd_leaf {r : ℕ} (i : Fin r) :
    (andStarNbhd (andStarLeaf i)).card = 1 := by
  classical
  rw [show andStarNbhd (andStarLeaf i) = {andStarCenter r} from ?_,
    Finset.card_singleton]
  ext y
  rw [mem_andStarNbhd, Finset.mem_singleton]
  constructor
  · intro hy
    have hcy : (zeroSet y.1).card = 0 := by
      rcases andStar_neighbour_card hy with ⟨h1, -⟩ | ⟨-, h2⟩
      · rw [zeroSet_andStarLeaf, Finset.card_singleton] at h1
        exact absurd h1 (by omega)
      · exact h2
    exact eq_center_of_card_zero hcy
  · rintro rfl
    refine Or.inr ?_
    rw [zeroSet_andStarCenter, zeroSet_andStarLeaf]
    exact Finset.ssubset_iff_of_subset (Finset.empty_subset _) |>.mpr
      ⟨i, Finset.mem_singleton_self i, Finset.notMem_empty i⟩

/-! ## The eigenvector -/

/-- `√r` at the centre, `1` at each leaf. -/
noncomputable def andStarVec (r : ℕ) : AndStarDom r → ℝ :=
  fun x => if (zeroSet x.1).card = 0 then Real.sqrt r else 1

lemma andStarGamma_mulVec_apply (r : ℕ) (u : AndStarDom r → ℝ)
    (x : AndStarDom r) :
    (andStarGamma r *ᵥ u) x = ∑ y ∈ andStarNbhd x, u y := by
  show ∑ y, andStarGamma r x y * u y = _
  rw [andStarNbhd, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [andStarGamma_apply]
  by_cases h : zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

lemma andStarGamma_mulVec_andStarVec (r : ℕ) :
    andStarGamma r *ᵥ andStarVec r = Real.sqrt r • andStarVec r := by
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hsq : Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) = (r : ℝ) :=
    Real.mul_self_sqrt hr0
  funext x
  rw [andStarGamma_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  rcases andStarDom_card x with hx | hx
  · -- the centre: `r` leaves, each carrying `1`
    obtain rfl := eq_center_of_card_zero hx
    have hconst : ∀ y ∈ andStarNbhd (andStarCenter r), andStarVec r y = 1 := by
      intro y hy
      rw [mem_andStarNbhd] at hy
      rcases andStar_neighbour_card hy with ⟨-, h2⟩ | ⟨h1, -⟩
      · rw [andStarVec, if_neg (by omega)]
      · rw [zeroSet_andStarCenter, Finset.card_empty] at h1
        exact absurd h1 (by omega)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      card_andStarNbhd_center r, nsmul_eq_mul, mul_one, andStarVec,
      zeroSet_andStarCenter, Finset.card_empty, if_pos rfl, hsq]
  · -- a leaf: its single neighbour is the centre, carrying `√r`
    obtain ⟨i, rfl⟩ := exists_leaf_of_card_one hx
    have hnb : andStarNbhd (andStarLeaf i) = {andStarCenter r} := by
      ext y
      rw [mem_andStarNbhd, Finset.mem_singleton]
      constructor
      · intro hy
        have hcy : (zeroSet y.1).card = 0 := by
          rcases andStar_neighbour_card hy with ⟨h1, -⟩ | ⟨-, h2⟩
          · rw [zeroSet_andStarLeaf, Finset.card_singleton] at h1
            exact absurd h1 (by omega)
          · exact h2
        exact eq_center_of_card_zero hcy
      · rintro rfl
        refine Or.inr ?_
        rw [zeroSet_andStarCenter, zeroSet_andStarLeaf]
        exact Finset.ssubset_iff_of_subset (Finset.empty_subset _) |>.mpr
          ⟨i, Finset.mem_singleton_self i, Finset.notMem_empty i⟩
    rw [hnb, Finset.sum_singleton, andStarVec, zeroSet_andStarCenter,
      Finset.card_empty, if_pos rfl, andStarVec, zeroSet_andStarLeaf,
      Finset.card_singleton, if_neg (by omega), mul_one]

lemma andStarVec_ne_zero (r : ℕ) (hr : 0 < r) : andStarVec r ≠ 0 := by
  intro h
  have hx := congrFun h (andStarCenter r)
  rw [Pi.zero_apply, andStarVec, zeroSet_andStarCenter, Finset.card_empty,
    if_pos rfl] at hx
  have : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr (by exact_mod_cast hr)
  exact this.ne' hx

theorem sqrt_le_norm_andStarGamma (r : ℕ) (hr : 0 < r) :
    Real.sqrt r ≤ ‖andStarGamma r‖ := by
  have h := abs_eigenvalue_le_norm (andStarGamma_mulVec_andStarVec r)
    (andStarVec_ne_zero r hr)
  rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h

/-! ## The coordinate masks -/

lemma andStar_mask_zeroSet {r : ℕ} (j : Fin r) {x y : AndStarDom r}
    (h : (andStarGamma r ⊙ advDOn (andStarRead (r := r)) j) x y ≠ 0) :
    ((zeroSet x.1).card = 0 ∧ zeroSet y.1 = insert j (zeroSet x.1))
      ∨ ((zeroSet x.1).card = 1 ∧ zeroSet y.1 = (zeroSet x.1).erase j) := by
  rw [hadamard_advDOn_apply] at h
  have hne : ¬ andStarRead x j = andStarRead y j := by
    intro hc
    rw [if_pos hc] at h
    exact h rfl
  rw [if_neg hne] at h
  have hss : zeroSet x.1 ⊂ zeroSet y.1 ∨ zeroSet y.1 ⊂ zeroSet x.1 := by
    by_contra hc
    rw [andStarGamma_apply, if_neg hc] at h
    exact h rfl
  have hmem : ¬ (j ∈ zeroSet x.1 ↔ j ∈ zeroSet y.1) := fun hc =>
    hne ((apply_eq_iff_mem_iff x.1 y.1 j).mpr hc)
  rcases andStar_neighbour_card hss with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    have hup : zeroSet x.1 ⊂ zeroSet y.1 := by
      rcases hss with hs | hs
      · exact hs
      · exact absurd (Finset.card_lt_card hs) (by omega)
    have hjx : j ∉ zeroSet x.1 := fun hc =>
      hmem ⟨fun _ => hup.subset hc, fun _ => hc⟩
    have hjy : j ∈ zeroSet y.1 := by
      by_contra hc
      exact hmem ⟨fun hc' => absurd hc' hjx, fun hc' => absurd hc' hc⟩
    symm
    refine Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hjy hup.subset) ?_
    have hc : (insert j (zeroSet x.1)).card = 1 := by
      rw [Finset.card_insert_of_notMem hjx, h1]
    omega
  · refine Or.inr ⟨h1, ?_⟩
    have hdown : zeroSet y.1 ⊂ zeroSet x.1 := by
      rcases hss with hs | hs
      · exact absurd (Finset.card_lt_card hs) (by omega)
      · exact hs
    have hjy : j ∉ zeroSet y.1 := fun hc =>
      hmem ⟨fun _ => hc, fun _ => hdown.subset hc⟩
    have hjx : j ∈ zeroSet x.1 := by
      by_contra hc
      exact hmem ⟨fun hc' => absurd hc' hc, fun hc' => absurd hc' hjy⟩
    refine Finset.eq_of_subset_of_card_le
      (Finset.subset_erase.mpr ⟨hdown.subset, hjy⟩) ?_
    have hc : ((zeroSet x.1).erase j).card = 0 := by
      rw [Finset.card_erase_of_mem hjx, h1]
    omega

lemma andStar_mask_row_le_one {r : ℕ} (j : Fin r) (x : AndStarDom r) :
    ∑ y, |(andStarGamma r ⊙ advDOn (andStarRead (r := r)) j) x y| ≤ 1 := by
  refine sum_le_one_of_unique_support ?_ ?_
  · intro y
    rw [hadamard_advDOn_apply, andStarGamma_apply]
    split
    · rw [abs_zero]
      exact zero_le_one
    · split
      · rw [abs_one]
      · rw [abs_zero]
        exact zero_le_one
  · intro y z hy hz
    have hy' := andStar_mask_zeroSet j (fun hc => hy (by rw [hc, abs_zero]))
    have hz' := andStar_mask_zeroSet j (fun hc => hz (by rw [hc, abs_zero]))
    refine Subtype.ext (zeroSet_injective ?_)
    rcases hy' with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
      rcases hz' with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
    · rw [hy2, hz2]
    · omega
    · omega
    · rw [hy2, hz2]

theorem norm_andStarGamma_hadamard_le_one (r : ℕ) (j : Fin r) :
    ‖andStarGamma r ⊙ advDOn (andStarRead (r := r)) j‖ ≤ 1 := by
  have hsymm : ∀ x y : AndStarDom r,
      (andStarGamma r ⊙ advDOn (andStarRead (r := r)) j) x y
        = (andStarGamma r ⊙ advDOn (andStarRead (r := r)) j) y x := by
    intro x y
    rw [hadamard_advDOn_apply, hadamard_advDOn_apply, andStarGamma_symm r x y]
    exact if_congr eq_comm rfl rfl
  refine l2_opNorm_le_of_rowcol_le zero_le_one (andStar_mask_row_le_one j)
    fun y => ?_
  rw [Finset.sum_congr rfl fun x _ => by rw [hsymm x y]]
  exact andStar_mask_row_le_one j y

/-! ## The star lower bound -/

/-- **The promised-AND star bound**: the promised-AND problem has adversary bound at least
`√r`. -/
theorem sqrt_le_advPMOn_andStar (r : ℕ) (hr : 0 < r) :
    Real.sqrt r ≤ advPMOn (andStarRead (r := r)) (andStarOut r) := by
  have hdet := separates_of_injective (andStarRead_injective (r := r))
    (andStarOut r)
  have h := norm_div_le_advPMOn hdet (isAdvMatrixOn_andStarGamma r)
    (norm_andStarGamma_hadamard_le_one r) one_pos
  rw [div_one] at h
  exact (sqrt_le_norm_andStarGamma r hr).trans h

end MonoidProduct
