import MonoidProduct.Aperiodic.CubeRoot.PrincipalAction
import MonoidProduct.Aperiodic.CubeRoot.Compression
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The row/column action as matrices

The partial maps of `PrincipalAction.lean`, turned into the `RowColAction` `compressedRep` consumes,
and read off pointwise on the class.

**The conventions are forced by handedness.**  `rowMap` is a *left* action and
`colMap` a *right* one, and matrix multiplication composes in only one order, so

    `(rowMat m) p q = 1 ↔ rowMap m q = some p`,
    `(colMat m) p q = 1 ↔ colMap m p = some q`.

The transposed convention on the column side is exactly what turns a right
action into something that composes correctly; with it `rowMat` is a monoid
homomorphism, which is what `RowColAction.row` demands.

**The intertwining is one fact read two ways.**  Both `P·rowMat m` and
`colMat m·P` have entry `(l, q)` equal to the indicator of `x·m·y` staying in
the class, for `x` an `L`-class representative and `y` an `R`-class one
(`crossEntry`).  On the row side that is "`m·y` survives *and* `x` meets it", on
the column side "`x·m` survives *and* it meets `y`" — the same product, bracketed
the two ways, which is why associativity is the whole content.  Death absorbing
(`PrincipalAction.lean`) is what makes the two `none` branches agree.

**The endpoint is pointwise, not an equality of actions.**  `rowMat_cell` and
`colMat_cell` give `row(z) = E_{r(z),ℓ(z)}·P` and `col(z) = P·E_{r(z),ℓ(z)}` for
`z` in the class, and `compressedRep_cell_of_mem` turns the first into
`D·E_{r(z),ℓ(z)}·C`.  This is deliberately *not* an equality with `blockAction`,
whose domain is `WithOne (ReesZero Q)` and so is not the monoid's; what the spanning
argument below needs is the value on cells, and that is what these deliver across the domain
mismatch.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace PrincipalFactor

open Matrix

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## A general right-multiplication-by-a-cell entry formula

`ReesBlock.mul_single_apply'` is stated for a square `Matrix I I ℚ`; the column
side needs it for the rectangular sandwich. -/

lemma mul_single_apply_gen {κ ι Θ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq Θ]
    (N : Matrix κ ι ℚ) (j : ι) (m : Θ) (p : κ) (q : Θ) :
    (N * Matrix.single j m (1 : ℚ)) p q = if q = m then N p j else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · by_cases hq : q = m
    · subst hq
      simp [Matrix.single]
    · simp [Matrix.single, Ne.symm hq, hq]
  · intro y _ hy
    simp [Matrix.single, Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-! ## The sandwich as a matrix -/

variable (M) in
/-- The class's sandwich matrix. -/
noncomputable def sandwichMat (a : M) : Matrix (LIdx M a) (RIdx M a) ℚ :=
  sandwich fun l i => sandwichBool M l i

lemma sandwichMat_apply {a : M} (l : LIdx M a) (i : RIdx M a) :
    sandwichMat M a l i = if sandwichBool M l i then 1 else 0 := rfl

/-! ## The two matrices -/

variable (M) in
/-- **The row matrix**: `1` at `(p, q)` when left multiplication carries the
`R`-class `q` to `p`. -/
noncomputable def rowMat {a : M} (m : M) : Matrix (RIdx M a) (RIdx M a) ℚ :=
  Matrix.of fun p q => if rowMap M m q = some p then 1 else 0

variable (M) in
/-- **The column matrix**, transposed relative to the row one — which is what
makes the right action compose. -/
noncomputable def colMat {a : M} (m : M) : Matrix (LIdx M a) (LIdx M a) ℚ :=
  Matrix.of fun p q => if colMap M m p = some q then 1 else 0

lemma rowMat_apply {a : M} (m : M) (p q : RIdx M a) :
    rowMat M m p q = if rowMap M m q = some p then 1 else 0 := rfl

lemma colMat_apply {a : M} (m : M) (p q : LIdx M a) :
    colMat M m p q = if colMap M m p = some q then 1 else 0 := rfl

/-! ## The row matrix is a monoid homomorphism -/

theorem rowMat_one {a : M} :
    rowMat M (1 : M) = (1 : Matrix (RIdx M a) (RIdx M a) ℚ) := by
  ext p q
  rw [rowMat_apply, rowMap_one, Matrix.one_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h, Ne.symm h]

theorem rowMat_mul {a : M} (m n : M) :
    rowMat M (m * n) = (rowMat M m : Matrix (RIdx M a) (RIdx M a) ℚ) * rowMat M n := by
  ext p r
  rw [Matrix.mul_apply, rowMat_apply]
  cases hn : rowMap M n r with
  | none =>
      rw [rowMap_bind_none hn, if_neg (by simp)]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [rowMat_apply (a := a) n j r, hn, if_neg (by simp), mul_zero]
  | some q₀ =>
      have hmn : rowMap M (m * n) r = rowMap M m q₀ := by rw [rowMap_mul, hn]; rfl
      rw [hmn, Finset.sum_eq_single q₀]
      · rw [rowMat_apply (a := a) n q₀ r, hn, if_pos rfl, mul_one, rowMat_apply]
      · intro y _ hy
        rw [rowMat_apply (a := a) n y r, hn, if_neg (by simpa using Ne.symm hy), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ q₀) h

variable (M) in
/-- The row action, bundled. -/
noncomputable def rowHom (a : M) : M →* Matrix (RIdx M a) (RIdx M a) ℚ where
  toFun m := rowMat M m
  map_one' := rowMat_one
  map_mul' m n := rowMat_mul m n

@[simp] lemma rowHom_apply (a m : M) : rowHom M a m = rowMat M m := rfl

/-! ## The intertwining

Both products have the same entry, and it is the indicator of one associativity
statement. -/

variable (M) in
/-- The common value of the two sides of the intertwining. -/
noncomputable def crossEntry {a : M} (m : M) (l : LIdx M a) (q : RIdx M a) : ℚ :=
  if twoIdeal ((lRep M l).1 * m * (rRep M q).1) = twoIdeal a then 1 else 0

theorem sandwichMat_mul_rowMat_apply {a : M} (m : M) (l : LIdx M a) (q : RIdx M a) :
    (sandwichMat M a * rowMat M (a := a) m) l q = crossEntry M m l q := by
  have hyJ : twoIdeal (rRep M q).1 = twoIdeal a := mem_jClass.1 (rRep M q).2
  have hassoc : (lRep M l).1 * m * (rRep M q).1 = (lRep M l).1 * (m * (rRep M q).1) :=
    mul_assoc _ _ _
  rw [Matrix.mul_apply, crossEntry, hassoc]
  cases h : rowMap M m q with
  | none =>
      have hne : twoIdeal (m * (rRep M q).1) ≠ twoIdeal a := by
        intro hc
        rw [rowMap, rClassOf_eq_some hc] at h
        exact Option.some_ne_none _ h
      have hsub : twoIdeal (m * (rRep M q).1) ⊆ twoIdeal a := by
        rw [← hyJ]
        exact twoIdeal_subset_of_lLe (lLe_iff_exists.2 ⟨m, rfl⟩)
      rw [if_neg (twoIdeal_mul_left_ne hsub hne _)]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [rowMat_apply, h, if_neg (by simp), mul_zero]
  | some i₀ =>
      have hmem : twoIdeal (m * (rRep M q).1) = twoIdeal a := by
        by_contra hc
        rw [rowMap, rClassOf_eq_none hc] at h
        exact Option.some_ne_none _ h.symm
      have hi : i₀ = rIdx M ⟨m * (rRep M q).1, mem_jClass.2 hmem⟩ := by
        rw [rowMap, rClassOf_eq_some hmem] at h
        exact (Option.some.inj h).symm
      rw [Finset.sum_eq_single i₀]
      · rw [rowMat_apply, h, if_pos rfl, mul_one, sandwichMat_apply, hi]
        have := sandwich_eq_true_iff (lRep M l) ⟨m * (rRep M q).1, mem_jClass.2 hmem⟩
        rw [lIdx_lRep] at this
        by_cases hb : sandwichBool M l (rIdx M ⟨m * (rRep M q).1, mem_jClass.2 hmem⟩) = true
        · rw [if_pos hb, if_pos (this.1 hb)]
        · rw [if_neg hb, if_neg (fun hc => hb (this.2 hc))]
      · intro y _ hy
        rw [rowMat_apply, h, if_neg (by simpa using Ne.symm hy), mul_zero]
      · intro hcon
        exact absurd (Finset.mem_univ i₀) hcon

theorem colMat_mul_sandwichMat_apply {a : M} (m : M) (l : LIdx M a) (q : RIdx M a) :
    (colMat M (a := a) m * sandwichMat M a) l q = crossEntry M m l q := by
  have hxJ : twoIdeal (lRep M l).1 = twoIdeal a := mem_jClass.1 (lRep M l).2
  rw [Matrix.mul_apply, crossEntry]
  cases h : colMap M m l with
  | none =>
      have hne : twoIdeal ((lRep M l).1 * m) ≠ twoIdeal a := by
        intro hc
        rw [colMap, lClassOf_eq_some hc] at h
        exact Option.some_ne_none _ h
      have hsub : twoIdeal ((lRep M l).1 * m) ⊆ twoIdeal a := by
        rw [← hxJ]
        exact twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨m, rfl⟩)
      rw [if_neg (twoIdeal_mul_right_ne hsub hne _)]
      refine Finset.sum_eq_zero fun μ _ => ?_
      rw [colMat_apply, h, if_neg (by simp), zero_mul]
  | some μ₀ =>
      have hmem : twoIdeal ((lRep M l).1 * m) = twoIdeal a := by
        by_contra hc
        rw [colMap, lClassOf_eq_none hc] at h
        exact Option.some_ne_none _ h.symm
      have hμ : μ₀ = lIdx M ⟨(lRep M l).1 * m, mem_jClass.2 hmem⟩ := by
        rw [colMap, lClassOf_eq_some hmem] at h
        exact (Option.some.inj h).symm
      rw [Finset.sum_eq_single μ₀]
      · rw [colMat_apply, h, if_pos rfl, one_mul, sandwichMat_apply, hμ]
        have := sandwich_eq_true_iff (⟨(lRep M l).1 * m, mem_jClass.2 hmem⟩ : JType M a)
          (rRep M q)
        rw [rIdx_rRep] at this
        by_cases hb : sandwichBool M (lIdx M (⟨(lRep M l).1 * m, mem_jClass.2 hmem⟩ :
            JType M a)) q = true
        · rw [if_pos hb, if_pos (this.1 hb)]
        · rw [if_neg hb, if_neg (fun hc => hb (this.2 hc))]
      · intro y _ hy
        rw [colMat_apply, h, if_neg (by simpa using Ne.symm hy), zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ μ₀) hcon

variable (M) in
/-- **The monoid's row/column action on the principal factor.**  This is the
`RowColAction` the principal-factor coordinate needs, and the input `compressedRep` consumes. -/
noncomputable def rowColAction (a : M) : RowColAction M (sandwichMat M a) where
  row := rowHom M a
  col := colMat M
  intertwine m := by
    ext l q
    rw [rowHom_apply, sandwichMat_mul_rowMat_apply, colMat_mul_sandwichMat_apply]

/-! ## The pointwise cell formulas -/

/-- **The row matrix of a class element is `E_{r(z),ℓ(z)}·P`.** -/
theorem rowMat_cell {a : M} [IsAperiodicMonoid M] (z : JType M a) :
    rowMat M z.1 = Matrix.single (rIdx M z) (lIdx M z) (1 : ℚ) * sandwichMat M a := by
  ext p q
  rw [rowMat_apply, single_mul_apply', sandwichMat_apply, rowMap]
  have hsw := sandwich_eq_true_iff z (rRep M q)
  rw [rIdx_rRep] at hsw
  by_cases hmem : twoIdeal (z.1 * (rRep M q).1) = twoIdeal a
  · rw [rClassOf_eq_some hmem, rIdx_mul z (rRep M q) hmem, if_pos (hsw.2 hmem)]
    by_cases hp : p = rIdx M z
    · rw [if_pos hp, if_pos (by rw [hp])]
    · rw [if_neg hp, if_neg (fun hc => hp (Option.some.inj hc).symm)]
  · rw [rClassOf_eq_none hmem, if_neg (fun hc => hmem (hsw.1 hc)), if_neg (by simp)]
    simp

/-- **The column matrix of a class element is `P·E_{r(z),ℓ(z)}`.** -/
theorem colMat_cell {a : M} [IsAperiodicMonoid M] (z : JType M a) :
    colMat M z.1 = sandwichMat M a * Matrix.single (rIdx M z) (lIdx M z) (1 : ℚ) := by
  ext p q
  rw [colMat_apply, mul_single_apply_gen, sandwichMat_apply, colMap]
  have hsw := sandwich_eq_true_iff (lRep M p) z
  rw [lIdx_lRep] at hsw
  by_cases hmem : twoIdeal ((lRep M p).1 * z.1) = twoIdeal a
  · rw [lClassOf_eq_some hmem, lIdx_mul (lRep M p) z hmem, if_pos (hsw.2 hmem)]
    by_cases hq : q = lIdx M z
    · rw [if_pos hq, if_pos (by rw [hq])]
    · rw [if_neg hq, if_neg (fun hc => hq (Option.some.inj hc).symm)]
  · rw [lClassOf_eq_none hmem, if_neg (fun hc => hmem (hsw.1 hc)), if_neg (by simp)]
    simp

/-- **The compressed representation on a class element**, `D·E_{r(z),ℓ(z)}·C` —
the endpoint of the row/column action, and the spanning matrices of the
spanning argument below. -/
theorem compressedRep_cell_of_mem {a : M} [IsAperiodicMonoid M]
    (F : RankFactorization (sandwichMat M a)) (z : JType M a) :
    compressedRep F (rowColAction M a) z.1
      = F.D * Matrix.single (rIdx M z) (lIdx M z) (1 : ℚ) * F.C := by
  rw [compressedRep_apply]
  change F.D * rowMat M z.1 * F.Dinv = _
  rw [rowMat_cell z]
  calc F.D * (Matrix.single (rIdx M z) (lIdx M z) (1 : ℚ) * sandwichMat M a) * F.Dinv
      = F.D * (Matrix.single (rIdx M z) (lIdx M z) (1 : ℚ) * (F.C * F.D)) * F.Dinv := by
        rw [F.factor]
    _ = F.D * Matrix.single (rIdx M z) (lIdx M z) (1 : ℚ) * F.C * (F.D * F.Dinv) := by
        simp only [Matrix.mul_assoc]
    _ = F.D * Matrix.single (rIdx M z) (lIdx M z) (1 : ℚ) * F.C := by
        rw [F.D_Dinv, Matrix.mul_one]


/-! ## The block is spanned

The per-`J` half of the coordinate's surjectivity, in the form that is actually
a theorem about `ρ_J`: its image **spans** the block over `ℚ`.  `ρ_J` itself
*need not* be onto — for `d > 0` it never is, the monoid being finite and
`M_d(ℚ)` not, though at `d = 0` the block is a singleton and every map onto it
is surjective.  `coordAlgHom_surjective` below turns the span into genuine
surjectivity, of the induced `AlgHom` out of `MonoidAlgebra ℚ M`.

Two inputs, and nothing else.  `D` is right-invertible and `C` left-invertible,
so `X ↦ D·X·C` is **onto** `M_d(ℚ)` — with `X = Dinv·Y·Cinv` reconstructing any
`Y`.  And every cell `(i, λ)` of the class is *occupied*, which is
`cellMap_surjective` of `PrincipalFactor.lean`, so every `D·E_{iλ}·C` is genuinely in the image.  Since the
`E_{iλ}` span the rectangular matrices, their images span the block.

**Regularity is not needed here — nor for the charge.**  Only aperiodicity, and
only through the cell bijection: `rank_sq_le_card_jClass` below is
`rank_sandwich_sq_le` composed with `card_jClass_eq`, and neither uses
regularity.  What regularity supplies is the idempotent apex and the no-zero
rows and columns — that is, it is what makes this a *regular* principal-factor
coordinate, not what makes the dimensions work. -/

/-- **Reconstruction.**  A rank factorization's one-sided inverses make
`X ↦ D·X·C` onto. -/
lemma reconstruct_of_rankFactorization {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {P : Matrix κ ι ℚ} (F : RankFactorization P)
    (Y : Matrix (Fin F.d) (Fin F.d) ℚ) : F.D * (F.Dinv * Y * F.Cinv) * F.C = Y := by
  have h1 : F.D * (F.Dinv * Y * F.Cinv) * F.C = F.D * F.Dinv * Y * (F.Cinv * F.C) := by
    simp only [Matrix.mul_assoc]
  rw [h1, F.D_Dinv, F.Cinv_C, Matrix.one_mul, Matrix.mul_one]

/-- **Every cell is occupied**, so every `D·E_{iλ}·C` is in the image — the cell
surjectivity of `PrincipalFactor.lean`, read through the cell formula above. -/
theorem cellMatrix_mem_range [IsAperiodicMonoid M] {a : M}
    (F : RankFactorization (sandwichMat M a)) (i : RIdx M a) (l : LIdx M a) :
    F.D * Matrix.single i l (1 : ℚ) * F.C
      ∈ Set.range (fun m : M => compressedRep F (rowColAction M a) m) := by
  obtain ⟨z, hz⟩ := cellMap_surjective a (i, l)
  refine ⟨z.1, ?_⟩
  change compressedRep F (rowColAction M a) z.1 = F.D * Matrix.single i l (1 : ℚ) * F.C
  have h1 : rIdx M z = i := congrArg Prod.fst hz
  have h2 : lIdx M z = l := congrArg Prod.snd hz
  rw [compressedRep_cell_of_mem F z, h1, h2]

/-- **Per-`J` spanning**: the image of `ρ_J` spans the whole block.  This is
the statement the next section transfers to the monoid algebra. -/
theorem span_range_compressedRep_eq_top [IsAperiodicMonoid M] {a : M}
    (F : RankFactorization (sandwichMat M a)) :
    Submodule.span ℚ (Set.range (fun m : M => compressedRep F (rowColAction M a) m)) = ⊤ := by
  rw [eq_top_iff]
  rintro Y -
  set X : Matrix (RIdx M a) (LIdx M a) ℚ := F.Dinv * Y * F.Cinv with hX
  have hstep : ∀ (i : RIdx M a) (l : LIdx M a),
      X i l • (F.D * Matrix.single i l (1 : ℚ) * F.C)
        = F.D * Matrix.single i l (X i l) * F.C := by
    intro i l
    rw [show Matrix.single i l (X i l) = X i l • Matrix.single i l (1 : ℚ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], Matrix.mul_smul, Matrix.smul_mul]
  have hsum : ∑ i : RIdx M a, ∑ l : LIdx M a,
        X i l • (F.D * Matrix.single i l (1 : ℚ) * F.C) = F.D * X * F.C := by
    calc ∑ i : RIdx M a, ∑ l : LIdx M a, X i l • (F.D * Matrix.single i l (1 : ℚ) * F.C)
        = ∑ i : RIdx M a, ∑ l : LIdx M a, F.D * Matrix.single i l (X i l) * F.C :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => hstep i l
      _ = F.D * (∑ i : RIdx M a, ∑ l : LIdx M a, Matrix.single i l (X i l)) * F.C := by
          simp only [Matrix.mul_sum, Matrix.sum_mul]
      _ = F.D * X * F.C := by rw [← Matrix.matrix_eq_sum_single X]
  have hrec : F.D * X * F.C = Y := by rw [hX]; exact reconstruct_of_rankFactorization F Y
  have hYeq : Y = ∑ i : RIdx M a, ∑ l : LIdx M a,
      X i l • (F.D * Matrix.single i l (1 : ℚ) * F.C) := by
    rw [hsum, hrec]
  rw [hYeq]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span (cellMatrix_mem_range F i l))

/-- **The apex charge**, `d² ≤ |J|`: the sandwich's rank bound composed with the
cell count.  Aperiodicity only — no regularity anywhere in it. -/
theorem rank_sq_le_card_jClass [IsAperiodicMonoid M] (a : M) :
    (sandwichMat M a).rank ^ 2 ≤ (jClass M a).card := by
  rw [card_jClass_eq a]
  exact rank_sandwich_sq_le _

/-! ## The transfer to the monoid algebra

The span becomes honest surjectivity once it is read
at the algebra: `MonoidAlgebra ℚ M` is the package's common ambient algebra, so
this is where the per-`J` statement has to land.

It says nothing about the *joint* map.  Surjectivity of each coordinate
projection is not surjectivity of the product onto `∏_J M_{d_J}(ℚ)`; that is a
statement about distinct blocks and stays a separate theorem. -/

/-- **The coordinate algebra map**: the linear extension of `ρ_J` to the monoid
algebra.  No aperiodicity — the lift and its basis formula are formal.  It
enters only at `coordAlgHom_surjective`, through cell occupancy. -/
noncomputable def coordAlgHom {a : M}
    (F : RankFactorization (sandwichMat M a)) :
    MonoidAlgebra ℚ M →ₐ[ℚ] Matrix (Fin F.d) (Fin F.d) ℚ :=
  MonoidAlgebra.lift ℚ (Matrix (Fin F.d) (Fin F.d) ℚ) M (compressedRep F (rowColAction M a))

@[simp] lemma coordAlgHom_single {a : M}
    (F : RankFactorization (sandwichMat M a)) (m : M) :
    coordAlgHom F (MonoidAlgebra.single m (1 : ℚ)) = compressedRep F (rowColAction M a) m := by
  rw [coordAlgHom, MonoidAlgebra.lift_single, one_smul]

/-- **The coordinate map is onto the block.**  This is the surjectivity the
coordinate actually has: at the algebra, where it can be true. -/
theorem coordAlgHom_surjective [IsAperiodicMonoid M] {a : M}
    (F : RankFactorization (sandwichMat M a)) :
    Function.Surjective (coordAlgHom F) := by
  have hle : Submodule.span ℚ (Set.range (fun m : M => compressedRep F (rowColAction M a) m))
      ≤ LinearMap.range (coordAlgHom F).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact ⟨MonoidAlgebra.single m (1 : ℚ), by simp⟩
  have htop : ⊤ ≤ LinearMap.range (coordAlgHom F).toLinearMap := by
    rw [← span_range_compressedRep_eq_top F]
    exact hle
  exact LinearMap.range_eq_top.1 (top_le_iff.1 htop)

/-! ## Annihilation below `J`

The remaining `ApexCoordinate` field, and it is pure ideal descent — no
aperiodicity, no regularity, no matrices until the last line.

If `m` sits *strictly* below the class then `m·y` does too for every `y` in the
class, since `m·y` is below `m` on the right.  So the partial row action is
**everywhere dead**, `rowMat m` is the zero matrix, and `compressedRep` collapses
with it.  The column side is the mirror image and is recorded for symmetry; the
coordinate's `rep` is the compressed row map, so it is the row side the package
consumes. -/

/-- **Strictly below the class, the row action is everywhere dead.** -/
theorem rowMap_eq_none_of_ssubset {a : M} (m : M) (h : twoIdeal m ⊂ twoIdeal a)
    (q : RIdx M a) : rowMap M m q = none := by
  obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.1 h
  refine rClassOf_eq_none fun hc => hne ?_
  have hdown : twoIdeal (m * (rRep M q).1) ⊆ twoIdeal m :=
    twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨(rRep M q).1, rfl⟩)
  rw [hc] at hdown
  exact Finset.Subset.antisymm hsub hdown

/-- The column action is dead too — the mirror statement. -/
theorem colMap_eq_none_of_ssubset {a : M} (m : M) (h : twoIdeal m ⊂ twoIdeal a)
    (l : LIdx M a) : colMap M m l = none := by
  obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.1 h
  refine lClassOf_eq_none fun hc => hne ?_
  have hdown : twoIdeal ((lRep M l).1 * m) ⊆ twoIdeal m :=
    twoIdeal_subset_of_lLe (lLe_iff_exists.2 ⟨(lRep M l).1, rfl⟩)
  rw [hc] at hdown
  exact Finset.Subset.antisymm hsub hdown

/-- **The row matrix vanishes strictly below the class.** -/
theorem rowMat_eq_zero_of_ssubset {a : M} (m : M) (h : twoIdeal m ⊂ twoIdeal a) :
    (rowMat M m : Matrix (RIdx M a) (RIdx M a) ℚ) = 0 := by
  ext p q
  rw [rowMat_apply, rowMap_eq_none_of_ssubset m h q, if_neg (by simp), Matrix.zero_apply]

/-- **Annihilation below `J`** — the
`ApexCoordinate.annihilate` field: the coordinate is zero on everything strictly
below its own class. -/
theorem compressedRep_eq_zero_of_ssubset {a : M}
    (F : RankFactorization (sandwichMat M a)) (m : M) (h : twoIdeal m ⊂ twoIdeal a) :
    compressedRep F (rowColAction M a) m = 0 := by
  rw [compressedRep_apply]
  change F.D * rowMat M m * F.Dinv = 0
  rw [rowMat_eq_zero_of_ssubset m h, Matrix.mul_zero, Matrix.zero_mul]

/-! ## Annihilation off the cone above `J`

The previous section kills the coordinate *strictly below* the class.  The
kernel-filtration argument (`KernelFiltration.lean`) also meets elements **incomparable** to the class — the
cardinality filtration mixes all classes of one ideal size — and the same
ideal-descent argument kills those: if the row action of `m` moves any
`R`-class of `J` inside `J`, then `twoIdeal a ⊆ twoIdeal m`.  So the
coordinate vanishes on every `m` that is not *above* the class. -/

/-- **Off the cone above the class, the row action is everywhere dead.** -/
theorem rowMap_eq_none_of_not_subset {a : M} (m : M) (h : ¬ twoIdeal a ⊆ twoIdeal m)
    (q : RIdx M a) : rowMap M m q = none := by
  refine rClassOf_eq_none fun hc => h ?_
  have hdown : twoIdeal (m * (rRep M q).1) ⊆ twoIdeal m :=
    twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨(rRep M q).1, rfl⟩)
  rw [hc] at hdown
  exact hdown

/-- The row matrix vanishes off the cone above the class. -/
theorem rowMat_eq_zero_of_not_subset {a : M} (m : M) (h : ¬ twoIdeal a ⊆ twoIdeal m) :
    (rowMat M m : Matrix (RIdx M a) (RIdx M a) ℚ) = 0 := by
  ext p q
  rw [rowMat_apply, rowMap_eq_none_of_not_subset m h q, if_neg (by simp), Matrix.zero_apply]

/-- **The coordinate vanishes off the cone above its class** — the form of
annihilation the kernel filtration consumes: on the filtration ideal at the
class's own size, everything outside the class itself is killed. -/
theorem compressedRep_eq_zero_of_not_subset {a : M}
    (F : RankFactorization (sandwichMat M a)) (m : M) (h : ¬ twoIdeal a ⊆ twoIdeal m) :
    compressedRep F (rowColAction M a) m = 0 := by
  rw [compressedRep_apply]
  change F.D * rowMat M m * F.Dinv = 0
  rw [rowMat_eq_zero_of_not_subset m h, Matrix.mul_zero, Matrix.zero_mul]

/-! ## The sandwich of a non-regular class is zero

The other half of the null/regular dichotomy: a `true` sandwich entry is a
product of two class elements staying in the class, which manufactures an
idempotent (`isRegularClass_of_mul_mem`).  A non-regular — *null* — class
therefore has an identically false sandwich, and its layer products vanish
with no coordinate needed. -/

/-- A `true` sandwich entry certifies regularity of the class. -/
theorem isRegularClass_of_sandwichBool {a : M} [IsAperiodicMonoid M]
    {l : LIdx M a} {i : RIdx M a} (h : sandwichBool M l i = true) :
    IsRegularClass a := by
  have hmul := (sandwich_eq_true_iff (lRep M l) (rRep M i)).1 (by
    rw [lIdx_lRep, rIdx_rRep]; exact h)
  exact isRegularClass_of_mul_mem (mem_jClass.1 (lRep M l).2) (mem_jClass.1 (rRep M i).2) hmul

/-- **A null class has a zero sandwich.** -/
theorem sandwichMat_eq_zero_of_not_isRegularClass {a : M} [IsAperiodicMonoid M]
    (h : ¬ IsRegularClass a) : sandwichMat M a = 0 := by
  ext l i
  rw [sandwichMat_apply, Matrix.zero_apply, if_neg]
  intro hc
  exact h (isRegularClass_of_sandwichBool hc)

end PrincipalFactor

end MonoidProduct
