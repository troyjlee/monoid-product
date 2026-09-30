import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Defs

set_option linter.style.header false

/-!
# The layer algebra, and what is *not* true about it

The local model of one regular layer.  Coefficient matrices `X : I × Λ`
multiply by the sandwich in the middle,

    `X ⋆ Y = X · P · Y`,   `P = C · D`,

and the coordinate is the compression `X ↦ D · X · C`, so the **local kernel**
is `{X : D·X·C = 0}`.

**A non-fact.**  One might hope for the one-step drop
`Ker · A_s ⊆ A_{s-1}` — that a kernel element times *anything* in the layer's
ideal falls to the next layer down.  That is **false**, and
`layer_kernel_mul_ne_zero` is the machine-checked witness: with `P` the all-ones
`2×2` sandwich, `X = E₀₀ − E₁₀` is in the local kernel yet `X ⋆ Y = X ≠ 0` for
`Y = E₀₀`.  The monoid realizing it is the `2×2` all-ones rectangular band with
an identity adjoined, where `X` is `δ(e₀₀) − δ(e₁₀)`: every joint coordinate
kills it, and multiplying by `δ(e₀₀)` returns it unchanged.

The witness is stated at the layer, not at the monoid, deliberately.  That is
where the mechanism lives — a kernel element need not annihilate a non-kernel
one — and it is decidable arithmetic, whereas the monoid-level statement would
have to evaluate the classical choices inside `jointCoord`.

**What is true**, and what the kernel filtration is built on: a kernel element in the
**middle** of a triple product kills it, because the compression closes up:

    `X ⋆ Y ⋆ Z = X·C·(D·Y·C)·D·Z`.

So the local kernel is cube-zero even though it is not square-zero.
`KernelFiltration.lean` turns this into the global triple drop
`A_s·(Ker ∩ A_s)·A_s ⊆ A_{s-1}` — tripling the exponent per layer, hence only
the *existence* statement `Ker^(3^|M|) = ⊥` — and `MunnPackage.lean` converts
existence into the quantitative `Ker^|M| = ⊥` by strict power descent, which
is what `nilExponent_le` asks for.  No per-layer linear exponent is ever
needed.
-/

namespace MonoidProduct

namespace MunnLayer

open Matrix

/-! ## The positive fact: a kernel element in the middle kills a triple -/

/-- **The compression closes up.**  If the middle factor is in the local kernel
(`D·Y·C = 0`) then the triple product vanishes — whatever the outer factors are.

This is the replacement for the false one-step drop: it is why the local kernel
is cube-zero, and it is the shape the global argument has to be reduced to. -/
theorem layer_triple_eq_zero {ι κ δ : Type} [Fintype ι] [Fintype κ] [Fintype δ]
    (Cm : Matrix κ δ ℚ) (Dm : Matrix δ ι ℚ) (X Y Z : Matrix ι κ ℚ)
    (hY : Dm * Y * Cm = 0) :
    X * (Cm * Dm) * Y * (Cm * Dm) * Z = 0 := by
  have hassoc : X * (Cm * Dm) * Y * (Cm * Dm) * Z
      = X * Cm * (Dm * Y * Cm) * (Dm * Z) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, hY, Matrix.mul_zero, Matrix.zero_mul]

/-! ## The counterexample: the local kernel is not square-zero

`P` all-ones on two `R`-classes and two `L`-classes, `C` and `D` the rank-one
factorization.  This is the `2×2` all-ones rectangular band, read at the layer. -/

/-- The rank-one left factor of the all-ones sandwich. -/
def exC : Matrix (Fin 2) (Fin 1) ℚ := !![1; 1]

/-- The rank-one right factor. -/
def exD : Matrix (Fin 1) (Fin 2) ℚ := !![1, 1]

/-- The all-ones sandwich. -/
def exP : Matrix (Fin 2) (Fin 2) ℚ := exC * exD

/-- A kernel element: `E₀₀ − E₁₀`, the band's `δ(e₀₀) − δ(e₁₀)`. -/
def exX : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; -1, 0]

/-- A non-kernel element: `E₀₀`, the band's `δ(e₀₀)`. -/
def exY : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]

/-- `X` is in the local kernel. -/
theorem exX_mem_kernel : exD * exX * exC = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [exD, exX, exC, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Y` is **not**. -/
theorem exY_not_mem_kernel : exD * exY * exC ≠ 0 := by
  intro h
  have h00 : (exD * exY * exC) 0 0 = (0 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 := by rw [h]
  simp [exD, exY, exC, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- **The one-step drop is false.**  `X` is in the local kernel, yet `X ⋆ Y`
returns `X` itself — it does not fall to the next layer.  So a kernel element
times an arbitrary layer element need not vanish, and no `Ker · A_s ⊆ A_{s-1}`
can hold. -/
theorem layer_kernel_mul_ne_zero : exX * exP * exY = exX ∧ exX ≠ 0 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [exX, exY, exP, exC, exD, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h00 : exX 0 0 = (0 : Matrix (Fin 2) (Fin 2) ℚ) 0 0 := by rw [h]
    simp [exX] at h00

/-- A second kernel element: `E₀₀ − E₀₁`, the band's `δ(e₀₀) − δ(e₀₁)`. -/
def exZ : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; 0, 0]

/-- `Z` is in the local kernel too. -/
theorem exZ_mem_kernel : exD * exZ * exC = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [exD, exZ, exC, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The local kernel is genuinely not square-zero**: `X` and `Z` are both in
it, yet `X ⋆ Z = E₀₀ − E₀₁ − E₁₀ + E₁₁ ≠ 0`.  (`layer_kernel_mul_ne_zero`
above only shows the *one-sided* failure — its right factor is not in the
kernel — so this is the witness the section's heading actually claims, and the
reason the monoid-level `Ker² ≠ ⊥` with two `J`-classes.) -/
theorem layer_kernel_sq_ne_zero : exX * exP * exZ ≠ 0 := by
  intro h
  have h00 : (exX * exP * exZ) 0 0 = (0 : Matrix (Fin 2) (Fin 2) ℚ) 0 0 := by rw [h]
  simp [exX, exZ, exP, exC, exD, Matrix.mul_apply, Fin.sum_univ_two] at h00

end MunnLayer

end MonoidProduct
