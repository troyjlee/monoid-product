import MonoidProduct.Aperiodic.CubeRoot.LocallyThin
import Mathlib.Data.ZMod.Basic

set_option linter.style.header false

/-!
# Calibration: a square-zero kernel in `ZMod 4`

The abstract local-thinness theorem is tested before anything is built on it,
on the smallest instance that is not vacuous.

`A = ZMod 4`, kernel `J = (2)` — square-zero, since `2 · 2 = 0` — and
`S = {0, 1, 2}`, the two-element null semigroup with an identity adjoined,
which is aperiodic.  The quotient map collapses `0` and `2`, so the fibre over
`0` has two elements and there is a genuine loop to be trivialized: `2` and `1`
are *different elements of `S`* that the theorem identifies as the same arrow
at `(0, 0)`.

Two things this calibration is chosen to catch:

* **vacuity** — `sameArrow_two_one` exhibits an identification of two distinct
  elements, and `calibration_is_nontrivial` checks the fibre really has two
  elements, so the interface is not being satisfied by a trivial `φ`;
* **a hidden characteristic hypothesis** — `ZMod 4` has characteristic `4`.
  The paper's argument (`lem:ags-square-zero-lift`) divides by `ℓ₂ - ℓ₁` and
  needs characteristic zero; the
  formal proof uses aperiodicity's *consecutive* coincident powers instead, so
  it must go through here.  `sameArrow_two_one_by_computation` re-derives the
  same conclusion by `decide`, independently of the abstract proof.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace LocallyThinCalibration

open LocallyThin

/-- `{0, 1, 2} ⊆ ZMod 4`: a null semigroup with an identity adjoined. -/
def calMonoid : Submonoid (ZMod 4) where
  carrier := {0, 1, 2}
  one_mem' := by
    change (1 : ZMod 4) ∈ ({0, 1, 2} : Set (ZMod 4))
    simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide

instance : DecidablePred (· ∈ calMonoid) := fun a =>
  decidable_of_iff (a = 0 ∨ a = 1 ∨ a = 2) (by
    change (a = 0 ∨ a = 1 ∨ a = 2) ↔ a ∈ ({0, 1, 2} : Set (ZMod 4))
    simp)

instance : IsAperiodicMonoid ↥calMonoid where
  stabilizes a := ⟨2, by norm_num, by revert a; decide⟩

/-- The quotient map, collapsing `0` and `2`. -/
def calφ : ↥calMonoid →* ZMod 2 where
  toFun s := if (s : ZMod 4) = 1 then 1 else 0
  map_one' := by decide
  map_mul' := by decide

/-- The square-zero kernel `(2) ⊆ ZMod 4`. -/
def calJ : Ideal (ZMod 4) := Ideal.span {(2 : ZMod 4)}

theorem calJ_mem (z : ZMod 4) : z ∈ calJ ↔ z = 0 ∨ z = 2 := by
  constructor
  · intro hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    clear hz
    revert c
    decide
  · rintro (rfl | rfl)
    · exact Ideal.zero_mem _
    · exact Ideal.subset_span rfl

/-- The calibration instance of the algebraic input. -/
theorem calKernel : SquareZeroKernel calφ calMonoid.subtype calJ where
  twoSided := inferInstance
  sq_zero := by
    intro a ha b hb
    rcases (calJ_mem a).1 ha with rfl | rfl <;>
      rcases (calJ_mem b).1 hb with rfl | rfl <;> decide
  emb_inj := Subtype.val_injective
  fibre := by
    intro s s' h
    have key : ∀ a b : ↥calMonoid, calφ a = calφ b →
        ((a : ZMod 4) - (b : ZMod 4) = 0 ∨ (a : ZMod 4) - (b : ZMod 4) = 2) := by
      decide
    exact (calJ_mem _).2 (key s s' h)

/-- **The calibration**: the abstract interface is satisfied here. -/
theorem calibration : LocallyThinKernel calφ :=
  locallyThinKernel_of_squareZero calKernel

/-- The nontrivial element of the fibre over `0`. -/
def calTwo : ↥calMonoid := ⟨2, by
  change (2 : ZMod 4) ∈ ({0, 1, 2} : Set (ZMod 4))
  simp⟩

/-- The other element of that fibre. -/
def calZero : ↥calMonoid := ⟨0, by
  change (0 : ZMod 4) ∈ ({0, 1, 2} : Set (ZMod 4))
  simp⟩

/-- **Not vacuous.**  The fibre over `0` genuinely has two elements, and the
loop element is not the identity of `S` — so the identification below is not an
artefact of a trivial quotient. -/
theorem calibration_is_nontrivial :
    calTwo ≠ 1 ∧ calTwo ≠ calZero ∧ calφ calTwo = calφ calZero :=
  ⟨by decide, by decide, by decide⟩

/-- **The loop is trivialized.**  `2` and `1` are distinct in `S` and are the
same arrow at `(0, 0)` — which is the whole content of local thinness. -/
theorem sameArrow_two_one : SameArrow calφ 0 0 calTwo 1 :=
  calibration.loop_id 0 0 calTwo ⟨by decide, by decide⟩

/-- **The same conclusion by direct computation**, independent of the abstract
proof.  If these ever disagree, the abstract statement is wrong. -/
theorem sameArrow_two_one_by_computation :
    ∀ x y : ↥calMonoid, calφ x = 0 → calφ y = 0 →
      x * calTwo * y = x * 1 * y := by decide

/-- **The identity fibre is a singleton here**, as the interface promises. -/
theorem calibration_fibre_one : ∀ s : ↥calMonoid, calφ s = 1 → s = 1 :=
  calibration.fibre_one

/-- **Cut objects alone do not determine the product.**  This is why the
compiler's descriptor must carry the *raw* letter at an active leaf, and not
only `T × T` cut data: without it, `HasDual.postcomp_of_determined` would have
a false determinacy hypothesis.

The two one-letter words `fun _ => calZero` and `fun _ => calTwo` have
identical cut objects at **every** cut of the clipped range — at cut `0` both
give `(1, 0)`, at cut `1` both give `(0, 1)`, since `φ` collapses `0` and `2` —
and yet their products are `0` and `2`. -/
theorem cutObj_not_determining :
    LocallyThin.cutObj calφ (fun _ : Fin 1 => calZero) 0
        = LocallyThin.cutObj calφ (fun _ : Fin 1 => calTwo) 0
      ∧ LocallyThin.cutObj calφ (fun _ : Fin 1 => calZero) 1
        = LocallyThin.cutObj calφ (fun _ : Fin 1 => calTwo) 1
      ∧ rangeProd (fun _ : Fin 1 => calZero) 0 1
        ≠ rangeProd (fun _ : Fin 1 => calTwo) 0 1 :=
  ⟨by decide, by decide, by decide⟩

end LocallyThinCalibration

end MonoidProduct
