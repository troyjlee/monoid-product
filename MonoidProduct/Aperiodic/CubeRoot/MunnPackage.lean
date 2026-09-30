import MonoidProduct.Aperiodic.CubeRoot.KernelFiltration
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Finsupp

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The quantitative nilpotency exponent, and the Munn package

`KernelFiltration.lean` delivers *a* nilpotency exponent — `Ker^(3^|M|) = ⊥`,
exponentially far from the `nilExponent ≤ |M|` the frozen `ApexPackage`
demands.  The gap closes with no further semigroup theory:

* **stabilization at a nonzero power contradicts nilpotency**
  (`pow_eq_bot_of_pow_succ_eq`): if `I^(j+1) = I^j` then `I^j = I^(j+d)` for
  every `d`, and some power is `⊥`;
* therefore the powers of a nilpotent ideal descend **strictly** until they
  hit `⊥`, and by the `finrank` pigeonhole a proper nilpotent two-sided
  ideal of a finite-dimensional rational algebra satisfies
  `I^(finrank) = ⊥` (`pow_eq_bot_of_exists_pow_eq_bot`).

No Nakayama, no Jacobson radical, no simple modules: nilpotency-existence
plus dimension counting is the entire argument.  With
`finrank ℚ (ℚ[M]) = |M|` this gives `Ker^|M| = ⊥` (`ker_pow_card_eq_bot`) —
exactly `nilExponent_le`.  Properness of the kernel is free: were `Ker = ⊤`,
its powers would all be `⊤ ∋ 1 ≠ 0`, contradicting the existence exponent.

**`munnPackage`** is the unconditional `ApexPackage` for every
finite aperiodic monoid, on `MonoidAlgebra ℚ M` with the listed Munn
coordinates, `nilExponent = |M|` — the Munn–Ponizovskiĭ coordinates of the
paper's `lem:ags-munn-decomposition`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open PrincipalFactor

/-! ## Strict power descent for nilpotent two-sided ideals -/

section Descent

variable {A : Type} [Ring A] [Algebra ℚ A]

/-- **Stabilization at any power forces that power to `⊥`**, given that some
power is `⊥` — the reason a nilpotent ideal's powers descend strictly. -/
lemma pow_eq_bot_of_pow_succ_eq {I : Ideal A} [I.IsTwoSided] {j n : ℕ}
    (hstab : I ^ (j + 1) = I ^ j) (hnil : I ^ n = ⊥) : I ^ j = ⊥ := by
  have hall : ∀ d : ℕ, I ^ (j + d) = I ^ j := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
        have hsplit : I ^ (j + (d + 1)) = I ^ (j + d) * I ^ 1 := by
          rw [show j + (d + 1) = (j + d) + 1 by omega, ← Ideal.IsTwoSided.pow_add]
        have hstab' : I ^ j * I ^ 1 = I ^ j := by
          rw [← Ideal.IsTwoSided.pow_add]
          exact hstab
        rw [hsplit, ih, hstab']
  have hle : I ^ j ≤ ⊥ := by
    rw [← hall n, ← hnil]
    exact Ideal.pow_le_pow_right (by omega)
  exact le_bot_iff.1 hle

/-- **The finrank pigeonhole.**  A proper two-sided ideal of a
finite-dimensional rational algebra with *some* nilpotency exponent already
satisfies `I^N = ⊥` for every `N` at least the dimension: the powers descend
strictly (stabilizing would contradict nilpotency), and a strict chain of
subspaces exhausts the dimension. -/
theorem pow_eq_bot_of_exists_pow_eq_bot [FiniteDimensional ℚ A] {I : Ideal A}
    [I.IsTwoSided] (hnil : ∃ n, I ^ n = ⊥) (hproper : I ≠ ⊤) {N : ℕ}
    (hN : Module.finrank ℚ A ≤ N) (hN0 : 0 < N) : I ^ N = ⊥ := by
  obtain ⟨n, hn⟩ := hnil
  have main : ∀ j : ℕ, I ^ (j + 1) = ⊥ ∨
      Module.finrank ℚ (Submodule.restrictScalars ℚ (I ^ (j + 1))) + j
        < Module.finrank ℚ A := by
    intro j
    induction j with
    | zero =>
        by_cases h0 : I ^ 1 = ⊥
        · exact Or.inl h0
        · refine Or.inr ?_
          rw [Nat.add_zero]
          have hne : I ^ 1 ≠ ⊤ := fun hc =>
            hproper (top_le_iff.1 (hc ▸ Ideal.pow_le_self one_ne_zero))
          exact Submodule.finrank_lt
            (fun hc => hne ((Submodule.restrictScalars_eq_top_iff _ _ _).1 hc))
    | succ j ih =>
        rcases ih with h | h
        · refine Or.inl (le_bot_iff.1 ?_)
          rw [← h]
          exact Ideal.pow_le_pow_right (by omega)
        · by_cases hstab : I ^ (j + 1 + 1) = I ^ (j + 1)
          · refine Or.inl (le_bot_iff.1 ?_)
            rw [← pow_eq_bot_of_pow_succ_eq hstab hn]
            exact Ideal.pow_le_pow_right (by omega)
          · refine Or.inr ?_
            have hlt : I ^ (j + 1 + 1) < I ^ (j + 1) :=
              lt_of_le_of_ne (Ideal.pow_le_pow_right (by omega)) hstab
            have hfr := Submodule.finrank_lt_finrank_of_lt
              (Submodule.restrictScalars_lt ℚ |>.2 hlt)
            omega
  rcases main (N - 1) with h | h
  · rwa [show N - 1 + 1 = N by omega] at h
  · rw [show N - 1 + 1 = N by omega] at h
    have hzero : Module.finrank ℚ (Submodule.restrictScalars ℚ (I ^ N)) = 0 := by omega
    exact (Submodule.restrictScalars_eq_bot_iff _ _ _).1 (Submodule.finrank_eq_zero.1 hzero)

end Descent

namespace PrincipalFactor

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The monoid algebra is finite-dimensional of dimension `|M|` -/

instance : Module.Finite ℚ (MonoidAlgebra ℚ M) :=
  Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ) (M := M)).symm

lemma finrank_monoidAlgebra :
    Module.finrank ℚ (MonoidAlgebra ℚ M) = Fintype.card M := by
  rw [(MonoidAlgebra.coeffLinearEquiv (R := ℚ) (S := ℚ) (M := M)).finrank_eq,
    Module.finrank_finsupp_self]

/-! ## The quantitative exponent -/

variable [IsAperiodicMonoid M]

/-- The joint kernel is proper — otherwise its powers would all be the unit
ideal, contradicting the existence exponent in a nontrivial algebra. -/
lemma ker_jointAlgHom_ne_top :
    RingHom.ker (jointAlgHom M).toRingHom ≠ ⊤ := by
  intro htop
  have hone : ∀ k : ℕ, (1 : MonoidAlgebra ℚ M) ∈ (⊤ : Ideal (MonoidAlgebra ℚ M)) ^ k := by
    intro k
    induction k with
    | zero =>
        rw [Submodule.pow_zero, Submodule.one_eq_span]
        exact Submodule.subset_span (Set.mem_singleton 1)
    | succ k ih =>
        have hsplit : (⊤ : Ideal (MonoidAlgebra ℚ M)) ^ (k + 1) = ⊤ ^ k * ⊤ ^ 1 := by
          rw [← Ideal.IsTwoSided.pow_add]
        rw [hsplit]
        have h1 : (1 : MonoidAlgebra ℚ M) * 1 ∈ (⊤ : Ideal (MonoidAlgebra ℚ M)) ^ k * ⊤ ^ 1 :=
          Ideal.mul_mem_mul ih (by
            rw [Submodule.pow_one]
            exact Submodule.mem_top)
        rwa [mul_one] at h1
  have hbot := ker_pow_exists_eq_bot (M := M)
  rw [htop] at hbot
  have h0 : (1 : MonoidAlgebra ℚ M) ∈ (⊥ : Ideal (MonoidAlgebra ℚ M)) := by
    rw [← hbot]
    exact hone _
  have : Nonempty M := ⟨1⟩
  exact one_ne_zero (Submodule.mem_bot _ |>.1 h0)

/-- **The quantitative nilpotency exponent**: `Ker^|M| = ⊥` — the
`kernel_pow` field of the package, at `nilExponent = |M|` exactly. -/
theorem ker_jointAlgHom_pow_card :
    RingHom.ker (jointAlgHom M).toRingHom ^ Fintype.card M = ⊥ := by
  refine pow_eq_bot_of_exists_pow_eq_bot
    ⟨3 ^ Fintype.card M, ker_pow_exists_eq_bot⟩ ker_jointAlgHom_ne_top
    (le_of_eq finrank_monoidAlgebra) ?_
  exact Fintype.card_pos_iff.2 ⟨1⟩

/-! ## The package -/

variable (M) in
/-- **The unconditional simple-apex package** of a finite aperiodic monoid —
Munn–Ponizovskiĭ, in the shape the fixed-apex peel (`FixedApex.lean`) and
the radical tower (`RadicalTower.lean`) consume.  Ambient algebra `ℚ[M]`, the
listed Munn coordinates,
`nilExponent = |M|`. -/
noncomputable def munnPackage : ApexPackage M where
  count := (idemIdeals M).card
  coord := jointCoord M
  disjoint := jointCoord_disjoint
  charge := charge_jointCoord
  Alg := MonoidAlgebra ℚ M
  embed := MonoidAlgebra.of ℚ M
  embed_injective := of_injective
  toCoord := jointAlgHom M
  toCoord_embed := fun m k => jointAlgHom_of m k
  nilExponent := Fintype.card M
  nilExponent_le := le_refl _
  kernel_pow := ker_jointAlgHom_pow_card

/-- Every finite aperiodic monoid carries an apex package. -/
theorem exists_apexPackage : Nonempty (ApexPackage M) := ⟨munnPackage M⟩

end PrincipalFactor

end MonoidProduct
