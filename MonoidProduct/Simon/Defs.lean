import MonoidProduct.Aperiodic.Ideals
import MonoidProduct.UT.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Green's 𝓙 relation, 𝓙-triviality, and semigroup division

The definitional layer of the Simon formalization.  Everything is bridged to
the existing principal-ideal API of `Aperiodic/Ideals.lean`:

* `JLe a b` is `a ∈ M b M` — the 𝓙-preorder;
* `JEq a b` is `M a M = M b M` — Green's 𝓙, equivalently `JLe` both ways
  (`mem_twoIdeal_iff_subset`);
* `IsJTrivialMonoid M` says 𝓙 is the identity;
* `SemigroupDivides M S` is the exact algebraic interface of the division
  compiler: a subsemigroup `T ≤ S` with a surjective semigroup
  homomorphism `T → M`.  `SemigroupDivides.exists_section` extracts the
  section that `qQuery_le_of_but_division` consumes.

The target, in exactly this vocabulary and in the forward
direction only, is

    exists_divides_but_of_isJTrivial :
      IsJTrivialMonoid M → ∃ k, 1 ≤ k ∧ SemigroupDivides M (BUT k),

Simon's theorem; it is proved in `Simon/Chain.lean`
(`exists_divides_but_of_isJTrivial`) through the kernel of `Simon/Kernel.lean`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Green

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- The 𝓙-preorder: `a ≤_𝓙 b` iff `a ∈ M b M`. -/
def JLe (a b : M) : Prop := a ∈ twoIdeal b

/-- Green's 𝓙: equal principal two-sided ideals. -/
def JEq (a b : M) : Prop := twoIdeal a = twoIdeal b

lemma jLe_iff_subset {a b : M} : JLe a b ↔ twoIdeal a ⊆ twoIdeal b :=
  mem_twoIdeal_iff_subset

lemma jLe_refl (a : M) : JLe a a := self_mem_twoIdeal a

lemma jLe_trans {a b c : M} (hab : JLe a b) (hbc : JLe b c) : JLe a c :=
  jLe_iff_subset.mpr ((jLe_iff_subset.mp hab).trans (jLe_iff_subset.mp hbc))

/-- `𝓙` is mutual `≤_𝓙`. -/
lemma jEq_iff {a b : M} : JEq a b ↔ JLe a b ∧ JLe b a := by
  rw [JEq, jLe_iff_subset, jLe_iff_subset]
  exact ⟨fun h => ⟨h.subset, h.symm.subset⟩, fun h => Finset.Subset.antisymm h.1 h.2⟩

lemma jEq_refl (a : M) : JEq a a := rfl

lemma jEq_symm {a b : M} (h : JEq a b) : JEq b a := h.symm

lemma jEq_trans {a b c : M} (hab : JEq a b) (hbc : JEq b c) : JEq a c :=
  hab.trans hbc

/-- Products only descend in the 𝓙-preorder. -/
lemma jLe_mul_left (a b : M) : JLe (a * b) a :=
  jLe_iff_subset.mpr (twoIdeal_mul_subset_left a b)

lemma jLe_mul_right (a b : M) : JLe (a * b) b :=
  jLe_iff_subset.mpr (twoIdeal_mul_subset_right a b)

/-- **𝓙-trivial**: Green's 𝓙 is the identity relation. -/
def IsJTrivialMonoid (M : Type) [Monoid M] [Fintype M] [DecidableEq M] : Prop :=
  ∀ a b : M, JEq a b → a = b

lemma IsJTrivialMonoid.eq_of_jLe_jLe (h : IsJTrivialMonoid M) {a b : M}
    (hab : JLe a b) (hba : JLe b a) : a = b :=
  h a b (jEq_iff.mpr ⟨hab, hba⟩)

end Green

/-! ## Semigroup division -/

/-- **Semigroup division** `M ≺ S`: a subsemigroup `T ≤ S` with a surjective
semigroup homomorphism `T → M`.  This is exactly the interface of the
division compiler (`qQuery_prodFun_le_of_division`). -/
def SemigroupDivides (M S : Type) [Mul M] [Mul S] : Prop :=
  ∃ T : Subsemigroup S, ∃ φ : T →ₙ* M, Function.Surjective φ

/-- A surjective homomorphism has a section, which is what the compiler
consumes. -/
lemma SemigroupDivides.exists_section {M S : Type} [Mul M] [Mul S]
    (h : SemigroupDivides M S) :
    ∃ T : Subsemigroup S, ∃ φ : T →ₙ* M, ∃ ψ : M → T, ∀ m, φ (ψ m) = m := by
  obtain ⟨T, φ, hφ⟩ := h
  exact ⟨T, φ, Function.surjInv hφ, Function.surjInv_eq hφ⟩

/-- Division is reflexive: `S ≺ S` through the top subsemigroup. -/
lemma semigroupDivides_refl (S : Type) [Semigroup S] : SemigroupDivides S S :=
  ⟨⊤, MulMemClass.subtype (⊤ : Subsemigroup S), fun s => ⟨⟨s, trivial⟩, rfl⟩⟩

end MonoidProduct
