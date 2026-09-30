import MonoidProduct.Aperiodic.CubeRoot.Green
import Mathlib.LinearAlgebra.Matrix.Rank

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Regular height in a finite matrix monoid

The paper's regular matrix-rank ceiling (`lem:ags-matrix-rank-ceiling`).  The
localized AGS construction of the regular-action simulation depends only on the height of chains of
**regular** `J`-classes, and in a matrix representation ordinary matrix rank
bounds that height.

* rank of a represented element, at most the degree (`mrank_le_deg`) and
  monotone along the two-sided order (`mrank_mono`);
* the **ceiling**, `twoIdeal_eq_of_mrank_eq`: equal rank inside a two-sided
  ideal forces equal ideals.  The engine is one linear-algebra lemma — an inner
  inverse of `B` acts as the identity on `range B`, so it fixes any `C` whose
  range sits inside — applied once to columns and once, through transposes, to
  rows.  Only the **lower** element need be regular: the intermediate `c = p·b`
  inherits regularity across the `R`-equivalence the column half produces, in
  time for the row half;
* hence `mrank_lt_of_ssubset`, a strict regular ascent strictly increases rank,
  and the strong invariant `regHeight_add_mrank_le`:

      `regHeight a + mrank ρ a ≤ d`   for regular `a`,

  with the public corollary `regHeight_le_deg`.  The *sum* is what the chain
  argument controls, and it is the shape the regular-height recursion's budget
`ℓ + h ≤ H` consumes (Section `sec:ags-regular-height`).

The representation is a monoid hom `ρ` into `d × d` rational matrices.  Rank
and its monotonicity need nothing of `ρ` but that it is a hom; the ceiling
needs it **faithful**, since it concludes membership in an ideal *of `T`* from
an identity between matrices, and steps 4–5 inherit that hypothesis from it.
-/

namespace MonoidProduct

open scoped Matrix

section MatrixRank

variable {T : Type} [Monoid T] [Fintype T] [DecidableEq T] {d : ℕ}
variable (ρ : T →* Matrix (Fin d) (Fin d) ℚ)

/-- The rank of a represented element. -/
noncomputable def mrank (a : T) : ℕ := (ρ a).rank

omit [Fintype T] [DecidableEq T] in
/-- **Step 1: the rank is at most the degree.**  Nothing finite about `T` is
involved — only that `ρ` is a homomorphism. -/
theorem mrank_le_deg (a : T) : mrank ρ a ≤ d := by
  rw [mrank]
  simpa using Matrix.rank_le_card_width (ρ a)

/-- **Step 2: rank is monotone along the two-sided order.**  A product can only
lose rank, and membership in `twoIdeal b` exhibits `a` as a two-sided multiple
of `b`. -/
theorem mrank_mono {a b : T} (h : twoIdeal a ⊆ twoIdeal b) :
    mrank ρ a ≤ mrank ρ b := by
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 (h (self_mem_twoIdeal a))
  have hρ : ρ a = ρ p * ρ b * ρ q := by
    rw [← hpq, map_mul, map_mul]
  rw [mrank, mrank, hρ]
  exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)

/-- The same, from a `J`-equality. -/
theorem mrank_congr {a b : T} (h : twoIdeal a = twoIdeal b) :
    mrank ρ a = mrank ρ b :=
  le_antisymm (mrank_mono ρ h.subset) (mrank_mono ρ h.symm.subset)

end MatrixRank

/-! ## The rank ceiling

The paper's regular matrix-rank ceiling (`lem:ags-matrix-rank-ceiling`): a strict ascent between regular
classes strictly increases the rank.  The engine is one linear-algebra lemma —
an inner inverse of `B` acts as the identity on `range B`, so it fixes any `C`
whose range sits inside — applied once to columns and once, through transposes,
to rows.
-/

section Ceiling

variable {d : ℕ}

/-- **An inner inverse fixes everything in its range.**  If `B B⁻ B = B` and
`C`'s columns lie in `B`'s column space, then `B B⁻ C = C`. -/
theorem mul_innerInv_mul_of_range_le {B Binv C : Matrix (Fin d) (Fin d) ℚ}
    (hinv : B * Binv * B = B)
    (hle : LinearMap.range C.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    B * Binv * C = C := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have hmem : C.mulVecLin (Pi.single j 1) ∈ LinearMap.range B.mulVecLin :=
    hle ⟨Pi.single j 1, rfl⟩
  obtain ⟨w, hw⟩ := hmem
  have hC : Matrix.mulVec C (Pi.single j 1) = Matrix.mulVec B w := by
    rw [← Matrix.mulVecLin_apply, ← Matrix.mulVecLin_apply, hw]
  have key : Matrix.mulVec (B * Binv * C) (Pi.single j 1)
      = Matrix.mulVec (B * Binv) (Matrix.mulVec C (Pi.single j 1)) :=
    (Matrix.mulVec_mulVec _ _ _).symm
  rw [key, hC, Matrix.mulVec_mulVec, hinv]

/-- Column spaces of equal rank, one inside the other, coincide. -/
theorem range_eq_of_le_of_rank_le {B C : Matrix (Fin d) (Fin d) ℚ}
    (hle : LinearMap.range C.mulVecLin ≤ LinearMap.range B.mulVecLin)
    (hr : B.rank ≤ C.rank) :
    LinearMap.range C.mulVecLin = LinearMap.range B.mulVecLin :=
  Submodule.eq_of_le_of_finrank_le hle hr

/-- A right multiple's column space sits inside. -/
theorem range_mul_le (B Y : Matrix (Fin d) (Fin d) ℚ) :
    LinearMap.range (B * Y).mulVecLin ≤ LinearMap.range B.mulVecLin := by
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- **The row-space analogue**, by transposing.  If `C`'s rows lie in `B`'s row
space and `B B⁻ B = B`, then `C B⁻ B = C`. -/
theorem mul_innerInv_mul_of_range_le' {B Binv C : Matrix (Fin d) (Fin d) ℚ}
    (hinv : B * Binv * B = B)
    (hle : LinearMap.range (Cᵀ).mulVecLin ≤ LinearMap.range (Bᵀ).mulVecLin) :
    C * Binv * B = C := by
  have hinvT : Bᵀ * Binvᵀ * Bᵀ = Bᵀ := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul]
    congr 1
    rw [← Matrix.mul_assoc]
    exact hinv
  have h := mul_innerInv_mul_of_range_le hinvT hle
  have := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this

/-- A left multiple's row space sits inside. -/
theorem range_transpose_mul_le (P B : Matrix (Fin d) (Fin d) ℚ) :
    LinearMap.range ((P * B)ᵀ).mulVecLin ≤ LinearMap.range (Bᵀ).mulVecLin := by
  rw [Matrix.transpose_mul]
  exact range_mul_le _ _

end Ceiling

/-! ## The rank ceiling in the monoid

Faithfulness enters exactly here, and only here: the arguments below conclude
membership in an ideal **of `T`** from an identity between matrices. -/

section Faithful

variable {T : Type} [Monoid T] [Fintype T] [DecidableEq T] {d : ℕ}
variable {ρ : T →* Matrix (Fin d) (Fin d) ℚ}

/-- **The column half.**  If `a = c·q` with `a` regular and of the same rank as
`c`, then `a` and `c` generate the same right ideal. -/
theorem rEq_of_mul_of_mrank_eq (hρ : Function.Injective ρ) {a c q : T}
    (hac : c * q = a) (hreg : IsVonNeumannRegular a)
    (hrank : mrank ρ c ≤ mrank ρ a) :
    REq a c := by
  obtain ⟨ainv, hainv⟩ := hreg
  have hle : LinearMap.range (ρ c).mulVecLin ≤ LinearMap.range (ρ a).mulVecLin := by
    have hrange : LinearMap.range (ρ a).mulVecLin
        ≤ LinearMap.range (ρ c).mulVecLin := by
      rw [← hac, map_mul]
      exact range_mul_le _ _
    exact le_of_eq (range_eq_of_le_of_rank_le hrange hrank).symm
  have hinv : ρ a * ρ ainv * ρ a = ρ a := by rw [← map_mul, ← map_mul, hainv]
  have hfix : ρ a * ρ ainv * ρ c = ρ c := mul_innerInv_mul_of_range_le hinv hle
  have hmem : a * (ainv * c) = c := by
    refine hρ ?_
    rw [map_mul, map_mul, ← Matrix.mul_assoc]
    exact hfix
  refine rEq_iff.2 ⟨rLe_iff_exists.2 ⟨q, hac⟩, rLe_iff_exists.2 ⟨ainv * c, hmem⟩⟩

/-- **The row half.**  If `c = p·b` with `c` regular and of the same rank as
`b`, then `c` and `b` generate the same left ideal. -/
theorem lEq_of_mul_of_mrank_eq (hρ : Function.Injective ρ) {b c p : T}
    (hcb : p * b = c) (hreg : IsVonNeumannRegular c)
    (hrank : mrank ρ b ≤ mrank ρ c) :
    LEq c b := by
  obtain ⟨cinv, hcinv⟩ := hreg
  have hle : LinearMap.range ((ρ b)ᵀ).mulVecLin
      ≤ LinearMap.range ((ρ c)ᵀ).mulVecLin := by
    have hrange : LinearMap.range ((ρ c)ᵀ).mulVecLin
        ≤ LinearMap.range ((ρ b)ᵀ).mulVecLin := by
      rw [← hcb, map_mul]
      exact range_transpose_mul_le _ _
    refine le_of_eq (range_eq_of_le_of_rank_le hrange ?_).symm
    rwa [Matrix.rank_transpose, Matrix.rank_transpose]
  have hinv : ρ c * ρ cinv * ρ c = ρ c := by rw [← map_mul, ← map_mul, hcinv]
  have hfix : ρ b * ρ cinv * ρ c = ρ b := mul_innerInv_mul_of_range_le' hinv hle
  have hmem : (b * cinv) * c = b := by
    refine hρ ?_
    rw [map_mul, map_mul]
    exact hfix
  refine lEq_iff.2 ⟨lLe_iff_exists.2 ⟨p, hcb⟩, lLe_iff_exists.2 ⟨b * cinv, hmem⟩⟩

/-- **Step 3: the regular matrix-rank ceiling** (`lem:ags-matrix-rank-ceiling`).
If `a` lies in the two-sided ideal of `b` and has the same rank, then the two generate the same ideal.

Only the **lower** element `a` need be regular: writing `a = p·b·q` and putting
`c = p·b`, the rank squeeze forces all three ranks equal, the column half gives
`a R c` — whence `c` is regular too, regularity being an `R`-class invariant —
and the row half then gives `c L b`. -/
theorem twoIdeal_eq_of_mrank_eq (hρ : Function.Injective ρ) {a b : T}
    (hsub : twoIdeal a ⊆ twoIdeal b) (hreg : IsVonNeumannRegular a)
    (hrank : mrank ρ b ≤ mrank ρ a) :
    twoIdeal a = twoIdeal b := by
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 (hsub (self_mem_twoIdeal a))
  -- the intermediate element and the rank squeeze
  have hac : (p * b) * q = a := by rw [mul_assoc] at hpq ⊢; exact hpq
  have h1 : mrank ρ a ≤ mrank ρ (p * b) := by
    rw [mrank, mrank, ← hac, map_mul]
    exact Matrix.rank_mul_le_left _ _
  have h2 : mrank ρ (p * b) ≤ mrank ρ b := by
    rw [mrank, mrank, map_mul]
    exact Matrix.rank_mul_le_right _ _
  -- the column half
  have hR : REq a (p * b) :=
    rEq_of_mul_of_mrank_eq hρ hac hreg (by omega)
  have hregc : IsVonNeumannRegular (p * b) := hreg.of_rEq hR
  -- the row half
  have hL : LEq (p * b) b :=
    lEq_of_mul_of_mrank_eq hρ rfl hregc (by omega)
  rw [twoIdeal_eq_of_rEq hR, twoIdeal_eq_of_lEq hL]

/-- **Step 4: a strict regular ascent strictly increases the rank.** -/
theorem mrank_lt_of_ssubset (hρ : Function.Injective ρ) {a b : T}
    (hsub : twoIdeal a ⊂ twoIdeal b) (hreg : IsVonNeumannRegular a) :
    mrank ρ a < mrank ρ b := by
  rcases lt_or_ge (mrank ρ a) (mrank ρ b) with h | h
  · exact h
  · exact absurd (twoIdeal_eq_of_mrank_eq hρ hsub.subset hreg h)
      (ne_of_lt (lt_of_lt_of_le hsub le_rfl))

/-- **Step 5: the rank ceiling on the regular height**, in the strong form.
The sum is what the chain argument controls — a strict regular ascent raises
the rank and lowers the height by at least one each — and it is also the shape
the regular-height recursion's budget `ℓ + h ≤ H` consumes.

No case split is needed for an empty parent set or for `d = 0`: an empty `sup`
is `0`, and `mrank_le_deg` covers the rest. -/
theorem regHeight_add_mrank_le [IsAperiodicMonoid T] (hρ : Function.Injective ρ) :
    ∀ a : T, IsVonNeumannRegular a → regHeight a + mrank ρ a ≤ d := by
  intro a
  induction a using regHeight.induct with
  | _ a ih =>
      intro hreg
      have hda : mrank ρ a ≤ d := mrank_le_deg ρ a
      have hsup : regHeight a ≤ d - mrank ρ a := by
        rw [regHeight_eq]
        refine Finset.sup_le fun b hb => ?_
        obtain ⟨hlt, hregb⟩ := mem_regAboveJ.1 hb
        have hbreg : IsVonNeumannRegular b := isVonNeumannRegular_of_isRegularClass hregb
        have hIH : regHeight b + mrank ρ b ≤ d := ih ⟨b, hb⟩ hbreg
        have hrk := mrank_lt_of_ssubset hρ hlt hreg
        omega
      omega

/-- **The public corollary**: the regular height is at most the degree. -/
theorem regHeight_le_deg [IsAperiodicMonoid T] (hρ : Function.Injective ρ)
    {a : T} (hreg : IsVonNeumannRegular a) : regHeight a ≤ d := by
  have := regHeight_add_mrank_le hρ a hreg
  omega

end Faithful

end MonoidProduct
