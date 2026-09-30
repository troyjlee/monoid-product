import MonoidProduct.Aperiodic.CubeRoot.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Hom

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The abstract simple-apex interface

The two consumers downstream — the fixed-apex peel (`lem:ags-fixed-apex-peel`)
and the radical tower (Section `sec:ags-radical-lift`) — are proved against this
interface; the Munn–Ponizovskiĭ construction (`lem:ags-munn-decomposition`)
instantiates it for every finite aperiodic monoid.

Shape:

* a **coordinate** is a finite rational matrix representation attached to a
  regular apex `J`-class (an idempotent representative), annihilating
  everything strictly below the apex, with the charge `degree² ≤ |J|`.  The
  identity `J`-class is allowed — the full Munn–Ponizovskiĭ tuple contains
  the identity simple block — and the fixed-apex peel asks separately for
  the coordinates it can peel (`ApexCoordinate.IsProper`: a nonidentity
  apex with a proper principal ideal);
* the **package** carries the joint coordinate map out of an ambient
  **rational algebra** `Alg` receiving the monoid **faithfully** (the
  radical lift cancels nonzero integers, in the algebra and in its quotient layers, and
  the radical tower recovers `embed (product)`, so it needs the embedded
  product to determine the monoid product), together with a *quantitative*
  nilpotency exponent `e ≤ |M|` of the kernel: `(ker toCoord)^e = ⊥`.  The
  kernel is a two-sided `Ideal` automatically (`RingHom.ker`), which is what
  the doubling transition of `RadicalStep.lean` consumes.

The blocks themselves need no algebra: `Compression.lean` represents a Rees
block by the compressed Munn map of degree `rank P`, and the Munn–Ponizovskiĭ
construction's default ambient algebra is `MonoidAlgebra ℚ M` with the lifted joint map.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable (M : Type) [Monoid M] [Fintype M] [DecidableEq M]

/-- The `J`-class of `a`: the elements generating the same two-sided ideal. -/
def jClass (a : M) : Finset M := Finset.univ.filter fun b => twoIdeal b = twoIdeal a

variable {M}

lemma mem_jClass {a b : M} : b ∈ jClass M a ↔ twoIdeal b = twoIdeal a := by
  simp [jClass]

lemma self_mem_jClass (a : M) : a ∈ jClass M a := mem_jClass.mpr rfl

variable (M)

/-- **A simple-apex coordinate**: a finite rational matrix representation
attached to a regular apex `J`-class, vanishing strictly below the apex,
with the charge `degree² ≤ |apex class|`.  The identity class is allowed. -/
structure ApexCoordinate where
  /-- The matrix degree. -/
  degree : ℕ
  /-- The representation. -/
  rep : M →* Matrix (Fin degree) (Fin degree) ℚ
  /-- An idempotent representative of the apex `J`-class. -/
  apex : M
  /-- The apex is idempotent (its `J`-class is regular). -/
  apex_idem : apex * apex = apex
  /-- Annihilation strictly below the apex. -/
  annihilate : ∀ s : M, twoIdeal s ⊂ twoIdeal apex → rep s = 0
  /-- The apex charge. -/
  degree_sq_le : degree ^ 2 ≤ (jClass M apex).card

variable {M}

/-- **A peelable coordinate**: its apex is not the identity and generates a
proper ideal.  This is the input of the fixed-apex peel; the identity
coordinate of a package is not peeled. -/
structure ApexCoordinate.IsProper (c : ApexCoordinate M) : Prop where
  /-- The apex is not the identity. -/
  apex_ne_one : c.apex ≠ 1
  /-- Its principal ideal is proper. -/
  ideal_proper : (1 : M) ∉ twoIdeal c.apex

variable (M)

/-- **The simple-apex package** of a finite monoid: finitely many coordinates
with pairwise distinct apex classes, the joint coordinate map out of an
ambient rational algebra receiving the monoid faithfully, and a
quantitative nilpotency exponent for the joint kernel. -/
structure ApexPackage where
  /-- The number of coordinates. -/
  count : ℕ
  /-- The coordinates. -/
  coord : Fin count → ApexCoordinate M
  /-- Distinct coordinates have distinct apex classes. -/
  disjoint : ∀ i j, twoIdeal (coord i).apex = twoIdeal (coord j).apex → i = j
  /-- The total charge is at most the carrier. -/
  charge : ∑ i, (coord i).degree ^ 2 ≤ Fintype.card M
  /-- The ambient algebra. -/
  Alg : Type
  /-- Its ring structure. -/
  [instRing : Ring Alg]
  /-- Its rational structure: nonzero integers cancel. -/
  [instAlgebra : Algebra ℚ Alg]
  /-- The monoid inside the ambient algebra, multiplicatively. -/
  embed : M →* Alg
  /-- Faithfully: the embedded product determines the monoid product. -/
  embed_injective : Function.Injective embed
  /-- The joint coordinate map. -/
  toCoord : Alg →ₐ[ℚ] ∀ i, Matrix (Fin (coord i).degree) (Fin (coord i).degree) ℚ
  /-- The joint map restricts to the coordinates on the monoid. -/
  toCoord_embed : ∀ (m : M) (i : Fin count), toCoord (embed m) i = (coord i).rep m
  /-- The nilpotency exponent of the joint kernel. -/
  nilExponent : ℕ
  /-- It is at most the carrier. -/
  nilExponent_le : nilExponent ≤ Fintype.card M
  /-- The joint kernel is nilpotent with that exponent. -/
  kernel_pow : RingHom.ker toCoord.toRingHom ^ nilExponent = ⊥

attribute [instance] ApexPackage.instRing ApexPackage.instAlgebra

namespace ApexPackage

variable {M} (Pk : ApexPackage M)

/-- The joint kernel, a two-sided ideal of the ambient algebra. -/
def kernel : Ideal Pk.Alg := RingHom.ker Pk.toCoord.toRingHom

instance : Pk.kernel.IsTwoSided :=
  inferInstanceAs (RingHom.ker Pk.toCoord.toRingHom).IsTwoSided

lemma kernel_pow_eq_bot : Pk.kernel ^ Pk.nilExponent = ⊥ := Pk.kernel_pow

/-- Two monoid elements have the same coordinates exactly when their
difference lies in the kernel. -/
lemma toCoord_embed_eq_iff (a b : M) :
    Pk.toCoord (Pk.embed a) = Pk.toCoord (Pk.embed b)
      ↔ Pk.embed a - Pk.embed b ∈ Pk.kernel := by
  rw [kernel, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, sub_eq_zero]

/-- Faithfulness: equal embedded elements are equal. -/
lemma embed_eq_iff (a b : M) : Pk.embed a = Pk.embed b ↔ a = b :=
  Pk.embed_injective.eq_iff

end ApexPackage

end MonoidProduct
