import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basis

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The Rees 0-matrix block and its rational Munn map

The regular principal factors of a finite **aperiodic** monoid are Rees
0-matrix semigroups over the *trivial* group: `M⁰(1; I, Λ; P)` with a 0/1
sandwich matrix `P : Λ → I → Bool`, elements `0` and `(i, λ)`, and product
`(i, λ)(j, μ) = (i, μ)` if `P λ j` and `0` otherwise.

This file sets up the block-level algebra on which the Munn–Ponizovskiĭ
construction (`lem:ags-munn-decomposition`) builds.  The **Munn map**

    (i, λ) ↦ E_{iλ} · P,   0 ↦ 0

lands in `Matrix I I ℚ` and is a semigroup homomorphism for the *ordinary*
matrix product, because `E_{iλ} P E_{jμ} = P_{λj} E_{iμ}`.  No monoid
algebra, contracted or otherwise, is needed to represent a block; the
matrix bound `d² ≤ |I|·|Λ|` for `d = rank P` is the two trivial rank
bounds.  So a block is represented
directly, and the degree-`d` compression (`Compression.lean`) is the
simple block.

What this file does **not** do: the globalization
theorem `compressedRep` is *conditional* on a supplied `RowColAction`
(an intertwined row/column action of the monoid on the block);
constructing that action from an actual regular `J`-class of a finite
aperiodic monoid — its principal factor as `M⁰(1; I, Λ; P)` — is done
later, in the Munn–Ponizovskiĭ construction.  So are the two facts that turn the matrix bound into the apex-class
charge `degree² ≤ |J|`: the principal-factor sandwich of a regular class
has **no zero row and no zero column** (regularity), and its cells
identify `J` with `I × Λ`.
-/

namespace MonoidProduct

open Matrix

variable {I Λ : Type} [Fintype I] [DecidableEq I] [Fintype Λ] [DecidableEq Λ]

/-! ## The block -/

/-- The Rees 0-matrix semigroup over the trivial group with sandwich `P`:
`none` is the zero, `some (i, λ)` the cell `(i, λ)`.  The sandwich is a
phantom parameter so that the multiplication is an instance. -/
structure ReesZero (P : Λ → I → Bool) where
  /-- The underlying cell, or zero. -/
  toOpt : Option (I × Λ)

variable (P : Λ → I → Bool)

/-- The product on cells: `(i, λ)(j, μ) = (i, μ)` when `P λ j`, else zero. -/
def reesOpt : Option (I × Λ) → Option (I × Λ) → Option (I × Λ)
  | some (i, l), some (j, m) => if P l j then some (i, m) else none
  | _, _ => none

lemma reesOpt_assoc (a b c : Option (I × Λ)) :
    reesOpt P (reesOpt P a b) c = reesOpt P a (reesOpt P b c) := by
  rcases a with _ | ⟨i, l⟩ <;> rcases b with _ | ⟨j, m⟩ <;> rcases c with _ | ⟨k, o⟩ <;>
    simp only [reesOpt] <;> split_ifs <;> simp_all

instance : Mul (ReesZero P) := ⟨fun a b => ⟨reesOpt P a.toOpt b.toOpt⟩⟩

@[simp] lemma ReesZero.mul_toOpt (a b : ReesZero P) :
    (a * b).toOpt = reesOpt P a.toOpt b.toOpt := rfl

instance : Semigroup (ReesZero P) where
  mul_assoc a b c := by
    cases a
    cases b
    cases c
    simp only [HMul.hMul, Mul.mul]
    rw [reesOpt_assoc]

/-- The zero of the block. -/
def ReesZero.zero : ReesZero P := ⟨none⟩

/-- The cell `(i, λ)`. -/
def ReesZero.cell (i : I) (l : Λ) : ReesZero P := ⟨some (i, l)⟩

lemma ReesZero.cell_mul_cell (i : I) (l : Λ) (j : I) (m : Λ) :
    ReesZero.cell P i l * ReesZero.cell P j m
      = if P l j then ReesZero.cell P i m else ReesZero.zero P := by
  simp only [HMul.hMul, Mul.mul, ReesZero.cell, ReesZero.zero, reesOpt]
  split_ifs <;> rfl

/-! ## The rational sandwich matrix and the Munn map -/

/-- The sandwich matrix as a rational `0/1` matrix. -/
def sandwich : Matrix Λ I ℚ := Matrix.of fun l j => if P l j then 1 else 0

/-- **The Munn map**: `(i, λ) ↦ E_{iλ}·P`, `0 ↦ 0`. -/
def munn (a : ReesZero P) : Matrix I I ℚ :=
  match a.toOpt with
  | none => 0
  | some (i, l) => Matrix.single i l (1 : ℚ) * sandwich P

@[simp] lemma munn_zero : munn P (ReesZero.zero P) = 0 := rfl

@[simp] lemma munn_cell (i : I) (l : Λ) :
    munn P (ReesZero.cell P i l) = Matrix.single i l (1 : ℚ) * sandwich P := rfl

/-- Left multiplication by `E_{iλ}` selects row `λ` into row `i`. -/
lemma single_mul_apply' (N : Matrix Λ I ℚ) (i : I) (l : Λ) (a x : I) :
    (Matrix.single i l (1 : ℚ) * N) a x = if a = i then N l x else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · by_cases ha : a = i
    · subst ha
      simp [Matrix.single]
    · simp [Matrix.single, Ne.symm ha, ha]
  · intro y _ hy
    simp [Matrix.single, Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-- Right multiplication by `E_{jμ}` selects column `j` into column `μ`. -/
lemma mul_single_apply' (N : Matrix I I ℚ) (j : I) (m : Λ) (a : I) (b : Λ) :
    (N * Matrix.single j m (1 : ℚ)) a b = if b = m then N a j else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · by_cases hb : b = m
    · subst hb
      simp [Matrix.single]
    · simp [Matrix.single, Ne.symm hb, hb]
  · intro y _ hy
    simp [Matrix.single, Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `E_{iλ} · P · E_{jμ} = P_{λj} · E_{iμ}`. -/
lemma single_mul_sandwich_mul_single (i : I) (l : Λ) (j : I) (m : Λ) :
    Matrix.single i l (1 : ℚ) * sandwich P * Matrix.single j m (1 : ℚ)
      = if P l j then Matrix.single i m (1 : ℚ) else 0 := by
  ext a b
  rw [mul_single_apply', single_mul_apply']
  by_cases hb : b = m
  · subst hb
    by_cases ha : a = i
    · subst ha
      by_cases hP : P l j = true <;> simp [hP, sandwich, Matrix.single]
    · by_cases hP : P l j = true <;> simp [hP, ha, Matrix.single, Ne.symm ha]
  · by_cases hP : P l j = true <;> simp [hP, hb, Matrix.single, Ne.symm hb]

/-- **The Munn map is a semigroup homomorphism** for the ordinary matrix
product. -/
theorem munn_mul (a b : ReesZero P) : munn P (a * b) = munn P a * munn P b := by
  rcases a with ⟨_ | ⟨i, l⟩⟩ <;> rcases b with ⟨_ | ⟨j, m⟩⟩
  · simp [munn, reesOpt]
  · simp [munn, reesOpt]
  · simp [munn, reesOpt]
  · change munn P (ReesZero.cell P i l * ReesZero.cell P j m)
      = munn P (ReesZero.cell P i l) * munn P (ReesZero.cell P j m)
    rw [ReesZero.cell_mul_cell]
    by_cases h : P l j = true
    · rw [if_pos h, munn_cell, munn_cell, munn_cell, ← Matrix.mul_assoc,
        single_mul_sandwich_mul_single, if_pos h]
    · rw [if_neg h, munn_zero, munn_cell, munn_cell, ← Matrix.mul_assoc,
        single_mul_sandwich_mul_single, if_neg h, Matrix.zero_mul]

/-! ## The apex charge -/

/-- **The apex charge of a block**: the rank of its sandwich matrix satisfies
`d² ≤ |I|·|Λ|`, from the two trivial rank bounds. -/
theorem rank_sandwich_sq_le : (sandwich P).rank ^ 2 ≤ Fintype.card I * Fintype.card Λ := by
  have h1 := Matrix.rank_le_card_width (sandwich P)
  have h2 := Matrix.rank_le_card_height (sandwich P)
  calc (sandwich P).rank ^ 2 = (sandwich P).rank * (sandwich P).rank := by ring
    _ ≤ Fintype.card I * Fintype.card Λ := Nat.mul_le_mul h1 h2

/-! ## Calibration: the Brandt block `B₂` -/

/-- The `2 × 2` identity sandwich: the Brandt semigroup `B₂`. -/
def brandtSandwich : Fin 2 → Fin 2 → Bool := fun l j => decide (l = j)

example : ReesZero.cell brandtSandwich 0 1 * ReesZero.cell brandtSandwich 1 0
    = ReesZero.cell brandtSandwich 0 0 := by
  rw [ReesZero.cell_mul_cell]
  rfl

example : ReesZero.cell brandtSandwich 0 1 * ReesZero.cell brandtSandwich 0 1
    = ReesZero.zero brandtSandwich := by
  rw [ReesZero.cell_mul_cell]
  rfl

end MonoidProduct
