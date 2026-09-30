import MonoidProduct.Aperiodic.CubeRoot.ReesBlock
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Group.WithOne.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The compressed simple representation of a Rees block

The direct Munn map of `ReesBlock.lean` has degree `|I|`, while the apex
charge is `rank(P)²`.  The simple block of degree `d = rank P` is obtained
by **compression** through a rank factorization `P = C·D` with one-sided
inverses `Cinv·C = 1`, `D·Dinv = 1`:

    (i, λ) ↦ D · E_{iλ} · C    (a `d × d` matrix).

The globalization to a whole monoid `M` is the theorem `compressedRep`: if
`M` acts on the rows of the block by a monoid homomorphism
`row : M →* Matrix I I ℚ` and on its columns by any `col : M → Matrix Λ Λ ℚ`
with the **intertwining** `P·row m = col m·P` (in the principal factor this
is associativity, `(λ-column)·m·(j-row)`), then

    m ↦ D · row m · Dinv

is a monoid homomorphism `M →* Matrix (Fin d) (Fin d) ℚ`.  The proof is
two lines of algebra: intertwining gives `D·row m = (Cinv·col m·C)·D`, so
`D·row m·Dinv·D·row n·Dinv = (Cinv·col m·C)·D·row n·Dinv = D·row m·row n·Dinv`.
The block's own left action (the Munn map, adjoined identity) is an
instance, and on cells the compressed representation is `D·E_{iλ}·C`.

`exists_rankFactorization` supplies the factorization with `d = rank P`
from a basis of the column space; the rank-`1` calibration
`onesFactorization` shows the rectangular band `M⁰(1; 2, 2; J)` collapsing
to the trivial block, as it must.
-/

namespace MonoidProduct

open Matrix

variable {I Λ : Type} [Fintype I] [DecidableEq I] [Fintype Λ] [DecidableEq Λ]

/-! ## Rank factorizations -/

/-- A factorization `P = C·D` through `Fin d` with one-sided inverses. -/
structure RankFactorization (P : Matrix Λ I ℚ) where
  /-- The inner dimension. -/
  d : ℕ
  /-- The left factor. -/
  C : Matrix Λ (Fin d) ℚ
  /-- The right factor. -/
  D : Matrix (Fin d) I ℚ
  /-- The factorization. -/
  factor : C * D = P
  /-- A left inverse of `C`. -/
  Cinv : Matrix (Fin d) Λ ℚ
  /-- `Cinv·C = 1`. -/
  Cinv_C : Cinv * C = 1
  /-- A right inverse of `D`. -/
  Dinv : Matrix I (Fin d) ℚ
  /-- `D·Dinv = 1`. -/
  D_Dinv : D * Dinv = 1

/-- **Every rational matrix has a rank factorization** with inner dimension
its rank: a basis of the column space gives `C`, coordinates give `D`. -/
theorem exists_rankFactorization (P : Matrix Λ I ℚ) :
    ∃ F : RankFactorization P, F.d = P.rank := by
  classical
  let V := LinearMap.range P.mulVecLin
  let b : Module.Basis (Fin (Module.finrank ℚ V)) ℚ V := Module.finBasis ℚ V
  have hcol : ∀ j : I, P.col j ∈ V := fun j => by
    refine ⟨Pi.single j 1, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single]
    simp
  let colV : I → V := fun j => ⟨P.col j, hcol j⟩
  let C : Matrix Λ (Fin (Module.finrank ℚ V)) ℚ := Matrix.of fun l k => (b k : Λ → ℚ) l
  let D : Matrix (Fin (Module.finrank ℚ V)) I ℚ := Matrix.of fun k j => b.equivFun (colV j) k
  -- the factorization
  have hfactor : C * D = P := by
    ext l j
    have h := congrArg (fun v : V => (v : Λ → ℚ) l) (b.sum_repr (colV j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [C, D, Matrix.of_apply, Module.Basis.equivFun_apply]
    rw [show P l j = (colV j : Λ → ℚ) l from rfl, ← h]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- `C` has a left inverse: its columns are the basis vectors
  have hCinj : LinearMap.ker (Matrix.toLin' C) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hsum : (∑ k, c k • b k : V) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
      funext l
      have := congrFun hc l
      rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] at this
      simpa [C, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using this
    funext k
    exact Fintype.linearIndependent_iff.mp b.linearIndependent c hsum k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C) hCinj
  -- `D` has a right inverse: the columns of `P` span `V`
  have hDsurj : LinearMap.range (Matrix.toLin' D) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    obtain ⟨u, hu⟩ := (b.equivFun.symm c).2
    refine ⟨u, ?_⟩
    have hv : (∑ j, u j • colV j : V) = b.equivFun.symm c := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      rw [← hu, Matrix.mulVecLin_apply]
      funext l
      simp [colV, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    have : Matrix.toLin' D u = b.equivFun (∑ j, u j • colV j) := by
      funext k
      rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum]
      simp only [D, Matrix.of_apply, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this, hv, LinearEquiv.apply_symm_apply]
  obtain ⟨g', hg'⟩ := LinearMap.exists_rightInverse_of_surjective (Matrix.toLin' D) hDsurj
  have hCinv : LinearMap.toMatrix' g * C = 1 := by
    rw [← LinearMap.toMatrix'_toLin' C, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hDinv : D * LinearMap.toMatrix' g' = 1 := by
    rw [← LinearMap.toMatrix'_toLin' D, ← LinearMap.toMatrix'_comp, hg', LinearMap.toMatrix'_id]
  exact ⟨⟨Module.finrank ℚ V, C, D, hfactor, LinearMap.toMatrix' g, hCinv,
    LinearMap.toMatrix' g', hDinv⟩, rfl⟩

/-! ## The compressed representation of an intertwined action -/

/-- **A row/column action of a monoid on a block**: a monoid homomorphism on
rows, any map on columns, intertwined through the sandwich. -/
structure RowColAction (M : Type) [Monoid M] (P : Matrix Λ I ℚ) where
  /-- The action on rows. -/
  row : M →* Matrix I I ℚ
  /-- The action on columns. -/
  col : M → Matrix Λ Λ ℚ
  /-- The intertwining `P·row m = col m·P`. -/
  intertwine : ∀ m, P * row m = col m * P

variable {M : Type} [Monoid M] {P : Matrix Λ I ℚ}

/-- Intertwining pushed through the factorization: `D·row m = (Cinv·col m·C)·D`. -/
lemma RowColAction.D_mul_row (F : RankFactorization P) (act : RowColAction M P) (m : M) :
    F.D * act.row m = F.Cinv * act.col m * F.C * F.D := by
  have h : F.C * F.D * act.row m = act.col m * (F.C * F.D) := by
    rw [F.factor]
    exact act.intertwine m
  calc F.D * act.row m = (F.Cinv * F.C) * F.D * act.row m := by rw [F.Cinv_C, Matrix.one_mul]
    _ = F.Cinv * (F.C * F.D * act.row m) := by simp only [Matrix.mul_assoc]
    _ = F.Cinv * (act.col m * (F.C * F.D)) := by rw [h]
    _ = F.Cinv * act.col m * F.C * F.D := by simp only [Matrix.mul_assoc]

/-- **The compressed representation** `m ↦ D·row m·Dinv`, a monoid
homomorphism of degree `d`. -/
def compressedRep (F : RankFactorization P) (act : RowColAction M P) :
    M →* Matrix (Fin F.d) (Fin F.d) ℚ where
  toFun m := F.D * act.row m * F.Dinv
  map_one' := by rw [map_one, Matrix.mul_one, F.D_Dinv]
  map_mul' m n := by
    rw [map_mul]
    calc F.D * (act.row m * act.row n) * F.Dinv
        = (F.D * act.row m) * act.row n * F.Dinv := by simp only [Matrix.mul_assoc]
      _ = F.Cinv * act.col m * F.C * F.D * act.row n * F.Dinv := by rw [act.D_mul_row F]
      _ = F.Cinv * act.col m * F.C * (F.D * F.Dinv) * F.D * act.row n * F.Dinv := by
          rw [F.D_Dinv, Matrix.mul_one]
      _ = (F.D * act.row m) * F.Dinv * (F.D * act.row n * F.Dinv) := by
          rw [act.D_mul_row F]
          simp only [Matrix.mul_assoc]

@[simp] lemma compressedRep_apply (F : RankFactorization P) (act : RowColAction M P) (m : M) :
    compressedRep F act m = F.D * act.row m * F.Dinv := rfl

/-! ## The block's own action -/

section Block

variable (Q : Λ → I → Bool)

/-- The column action of a cell: `(i, λ) ↦ P·E_{iλ}`. -/
def colMap : ReesZero Q → Matrix Λ Λ ℚ := fun a =>
  match a.toOpt with
  | none => 0
  | some (i, l) => sandwich Q * Matrix.single i l (1 : ℚ)

/-- The block acting on itself, with the identity adjoined: rows by the Munn
map, columns by `colMap`. -/
noncomputable def blockAction : RowColAction (WithOne (ReesZero Q)) (sandwich Q) where
  row := WithOne.lift ⟨munn Q, munn_mul Q⟩
  col := WithOne.recOneCoe 1 (colMap Q)
  intertwine := by
    intro a
    induction a using WithOne.recOneCoe with
    | one => simp
    | coe b =>
        rcases b with ⟨_ | ⟨i, l⟩⟩
        · change sandwich Q * (0 : Matrix I I ℚ) = (0 : Matrix Λ Λ ℚ) * sandwich Q
          simp
        · change sandwich Q * munn Q (ReesZero.cell Q i l)
            = colMap Q (ReesZero.cell Q i l) * sandwich Q
          rw [munn_cell]
          change sandwich Q * (Matrix.single i l 1 * sandwich Q)
            = sandwich Q * Matrix.single i l 1 * sandwich Q
          rw [Matrix.mul_assoc]

/-- **On cells the compressed block representation is `D·E_{iλ}·C`.** -/
theorem compressedRep_cell (F : RankFactorization (sandwich Q)) (i : I) (l : Λ) :
    compressedRep F (blockAction Q) (ReesZero.cell Q i l : ReesZero Q)
      = F.D * Matrix.single i l (1 : ℚ) * F.C := by
  rw [compressedRep_apply]
  change F.D * (WithOne.lift ⟨munn Q, munn_mul Q⟩ (ReesZero.cell Q i l : ReesZero Q)) * F.Dinv = _
  rw [WithOne.lift_coe]
  change F.D * munn Q (ReesZero.cell Q i l) * F.Dinv = _
  rw [munn_cell]
  calc F.D * (Matrix.single i l (1 : ℚ) * sandwich Q) * F.Dinv
      = F.D * (Matrix.single i l (1 : ℚ) * (F.C * F.D)) * F.Dinv := by rw [F.factor]
    _ = F.D * Matrix.single i l (1 : ℚ) * F.C * (F.D * F.Dinv) := by
        simp only [Matrix.mul_assoc]
    _ = F.D * Matrix.single i l (1 : ℚ) * F.C := by rw [F.D_Dinv, Matrix.mul_one]

/-- **The apex charge of the compressed block**: with `d = rank P`,
`d² ≤ |I|·|Λ|`. -/
theorem rankFactorization_charge (F : RankFactorization (sandwich Q))
    (hd : F.d = (sandwich Q).rank) :
    F.d ^ 2 ≤ Fintype.card I * Fintype.card Λ := by
  rw [hd]
  exact rank_sandwich_sq_le Q

end Block

/-! ## Calibration: a rank-`1` block collapses -/

/-- The all-ones `2 × 2` sandwich: the rectangular band `M⁰(1; 2, 2; J)`. -/
def onesSandwich : Fin 2 → Fin 2 → Bool := fun _ _ => true

/-- An explicit rank-`1` factorization of the all-ones sandwich. -/
def onesFactorization : RankFactorization (sandwich onesSandwich) where
  d := 1
  C := Matrix.of fun _ _ => 1
  D := Matrix.of fun _ _ => 1
  factor := by
    ext l j
    simp [Matrix.mul_apply, sandwich, onesSandwich]
  Cinv := Matrix.of fun _ l => if l = 0 then 1 else 0
  Cinv_C := by
    ext k k'
    simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim k k']
  Dinv := Matrix.of fun j _ => if j = 0 then 1 else 0
  D_Dinv := by
    ext k k'
    simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim k k']

set_option linter.flexible false in
/-- Every cell of the rectangular band compresses to the `1 × 1` identity:
the block's simple representation is trivial, as it must be for a band. -/
example (i l : Fin 2) :
    compressedRep onesFactorization (blockAction onesSandwich)
      (ReesZero.cell onesSandwich i l : ReesZero onesSandwich) = 1 := by
  rw [compressedRep_cell]
  have : Subsingleton (Fin onesFactorization.d) := (inferInstance : Subsingleton (Fin 1))
  ext k k'
  rw [Subsingleton.elim k' k, Matrix.one_apply_eq]
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases l <;> simp [onesFactorization, Matrix.single, Fin.sum_univ_two] <;>
    exact one_mul (1 : ℚ)

end MonoidProduct
