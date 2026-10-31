import MonoidProduct.Certificates.Basic
import MonoidProduct.Aperiodic.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Quotient
set_option linter.style.header false

/-!
# The extension monoid

`monoid.tex`, section `sec:strong-certificates`, `def:extension-monoid`, and the cardinality
bound after `cor:certificate-queries`.

For `f : Finset U → O`, the **extension monoid** is the quotient

  `M_f = 2^U / ∼_f`,  `[S][T] = [S ∪ T]`,  `1 = [∅]`,

where `∼_f` is equivalence under extensions (`ExtensionEquiv`).  It is a new type,
`ExtensionMonoid f`, and every instance lives on it rather than on `Finset U`:

* `ExtensionMonoid.mk f S` is the class `[S]`, with `mk_eq_mk : [S] = [T] ↔ S ∼_f T`;
* multiplication is induced by union, which is well defined because `∼_f` is a congruence of
  the union monoid (`ExtensionEquiv.union`); the result is a commutative monoid
  (`instCommMonoid`) in which every element is idempotent (`mul_self`), hence aperiodic
  (`instIsAperiodicMonoid`);
* `ExtensionMonoid.readout f : [S] ↦ f S` is well defined by the empty extension;
* a product of classes is the class of the union (`prod_mk`);
* over a finite universe the quotient is finite (`instFintype`), and decidable equality is
  classical (`instDecidableEq`): the query model treats input-independent computation as free.

`card_extensionMonoid_le_sum_choose` is the bound `|M_f| ≤ ∑_{j=0}^{b_f(U)} C(|U|, j)`: every
class has a representative with at most `b_f(U)` elements, namely a smallest strong certificate
of any representative.
-/

namespace MonoidProduct.Certificates

variable {U O : Type*} [DecidableEq U]

/-- The relation `∼_f` as a setoid on `Finset U`. -/
def extensionSetoid (f : Finset U → O) : Setoid (Finset U) :=
  ⟨ExtensionEquiv f, extensionEquiv_equivalence f⟩

/-- **The extension monoid** `M_f = 2^U / ∼_f` (`def:extension-monoid`).  The monoid structure
(`[S][T] = [S ∪ T]`, `1 = [∅]`) is defined on this type, not on `Finset U`. -/
def ExtensionMonoid (f : Finset U → O) : Type _ :=
  Quotient (extensionSetoid f)

namespace ExtensionMonoid

variable {f : Finset U → O}

/-- The class `[S]` of a set in the extension monoid. -/
def mk (f : Finset U → O) (S : Finset U) : ExtensionMonoid f :=
  Quotient.mk (extensionSetoid f) S

/-- Two sets have the same class exactly when they are equivalent under extensions. -/
theorem mk_eq_mk {S T : Finset U} : mk f S = mk f T ↔ ExtensionEquiv f S T :=
  Quotient.eq (r := extensionSetoid f)

theorem mk_surjective : Function.Surjective (mk f) :=
  Quotient.mk_surjective

/-- Induction on the classes of the extension monoid. -/
@[elab_as_elim]
theorem ind {p : ExtensionMonoid f → Prop} (h : ∀ S, p (mk f S)) (a : ExtensionMonoid f) : p a :=
  Quotient.ind h a

/-- **The readout** `[S] ↦ f S`, well defined by the empty extension. -/
def readout (f : Finset U → O) : ExtensionMonoid f → O :=
  Quotient.lift f fun _ _ h => ExtensionEquiv.apply_eq h

@[simp] theorem readout_mk (S : Finset U) : readout f (mk f S) = f S := rfl

/-- The identity `[∅]`. -/
instance : One (ExtensionMonoid f) := ⟨mk f ∅⟩

/-- Multiplication `[S][T] = [S ∪ T]`, well defined since `∼_f` is a congruence for union. -/
instance : Mul (ExtensionMonoid f) :=
  ⟨Quotient.map₂ (· ∪ ·) fun _ _ h₁ _ _ h₂ => ExtensionEquiv.union h₁ h₂⟩

theorem one_def : (1 : ExtensionMonoid f) = mk f ∅ := rfl

@[simp] theorem mk_mul_mk (S T : Finset U) : mk f S * mk f T = mk f (S ∪ T) := rfl

@[simp] theorem mk_empty : mk f (∅ : Finset U) = 1 := rfl

/-- `M_f` is a commutative monoid. -/
instance instCommMonoid : CommMonoid (ExtensionMonoid f) where
  mul_assoc a b c := by
    induction a using ind with | _ S =>
    induction b using ind with | _ T =>
    induction c using ind with | _ R =>
    simp only [mk_mul_mk, Finset.union_assoc]
  one_mul a := by
    induction a using ind with | _ S =>
    rw [← mk_empty, mk_mul_mk, Finset.empty_union]
  mul_one a := by
    induction a using ind with | _ S =>
    rw [← mk_empty, mk_mul_mk, Finset.union_empty]
  mul_comm a b := by
    induction a using ind with | _ S =>
    induction b using ind with | _ T =>
    simp only [mk_mul_mk, Finset.union_comm]

/-- Every element of `M_f` is idempotent. -/
@[simp] theorem mul_self (a : ExtensionMonoid f) : a * a = a := by
  induction a using ind with | _ S =>
  rw [mk_mul_mk, Finset.union_self]

/-- An idempotent monoid is aperiodic, with stabilisation at exponent one. -/
instance instIsAperiodicMonoid : IsAperiodicMonoid (ExtensionMonoid f) :=
  ⟨fun a => ⟨1, one_pos, by rw [pow_one, pow_two, mul_self]⟩⟩

/-- A product of classes is the class of the union. -/
theorem prod_mk {ι : Type*} (T : Finset ι) (F : ι → Finset U) :
    ∏ i ∈ T, mk f (F i) = mk f (T.biUnion F) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.biUnion_empty, mk_empty]
  | insert a T ha ih => rw [Finset.prod_insert ha, ih, mk_mul_mk, Finset.biUnion_insert]

open scoped Classical in
/-- Decidable equality on `M_f`, classically. -/
noncomputable instance instDecidableEq : DecidableEq (ExtensionMonoid f) :=
  Classical.decEq _

open scoped Classical in
/-- Over a finite universe the extension monoid is finite. -/
noncomputable instance instFintype [Fintype U] : Fintype (ExtensionMonoid f) :=
  Quotient.fintype (extensionSetoid f)

instance : Inhabited (ExtensionMonoid f) := ⟨1⟩

end ExtensionMonoid

open ExtensionMonoid

/-- Every class has a representative with at most `b` elements when `b` is a certificate
bound, so `|M_f| ≤ ∑_{j=0}^{b} C(|U|, j)`. -/
theorem card_extensionMonoid_le_sum_choose_of_bound [Fintype U] {f : Finset U → O} {b : ℕ}
    (h : HasStrongCertificateBound f b) :
    Fintype.card (ExtensionMonoid f) ≤
      ∑ j ∈ Finset.range (b + 1), (Fintype.card U).choose j := by
  classical
  set small : Finset (Finset U) :=
    (Finset.range (b + 1)).biUnion fun j => Finset.powersetCard j Finset.univ with hsmall
  have hcover : ∀ a : ExtensionMonoid f, a ∈ small.image (mk f) := by
    intro a
    induction a using ExtensionMonoid.ind with | _ S =>
    obtain ⟨C, hC, hcard⟩ := h S
    refine Finset.mem_image.mpr ⟨C, ?_, mk_eq_mk.mpr hC.2⟩
    exact Finset.mem_biUnion.mpr ⟨C.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hcard),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ C, rfl⟩⟩
  calc Fintype.card (ExtensionMonoid f)
      = (Finset.univ : Finset (ExtensionMonoid f)).card := Finset.card_univ.symm
    _ ≤ (small.image (mk f)).card := Finset.card_le_card fun a _ => hcover a
    _ ≤ small.card := Finset.card_image_le
    _ ≤ ∑ j ∈ Finset.range (b + 1), (Finset.powersetCard j (Finset.univ : Finset U)).card :=
        Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (b + 1), (Fintype.card U).choose j := by
        simp only [Finset.card_powersetCard, Finset.card_univ]

/-- **The cardinality bound** after `cor:certificate-queries`:
`|M_f| ≤ ∑_{j=0}^{b_f(U)} C(|U|, j)`.  The monoid may still be exponentially large when
certificates are small; the query bound depends only on `b_f(U)`. -/
theorem card_extensionMonoid_le_sum_choose [Fintype U] (f : Finset U → O) :
    Fintype.card (ExtensionMonoid f) ≤
      ∑ j ∈ Finset.range (strongCertificateSize f + 1), (Fintype.card U).choose j :=
  card_extensionMonoid_le_sum_choose_of_bound (hasStrongCertificateBound_strongCertificateSize f)

end MonoidProduct.Certificates
