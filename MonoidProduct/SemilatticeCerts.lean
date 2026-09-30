import QuantumQueryComplexity.Promise.HasDual
import MonoidProduct.Promise.Semilattice
import MonoidProduct.Semilattice.Semigroup
import MonoidProduct.Semilattice.Generated
set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Semilattice-product certificates, bundled

The semilattice development (`Semilattice/*`, `Promise/Semilattice.lean`)
exposes its duals as bare existentials and its promise bounds through
`advPMOn`; this file bundles the same certificates as `HasDual` /
`HasDualOn` — what the operational extraction
(`Quantum/SemilatticeApplications.lean`) consumes:

* `hasDual_joinMap` — the join of a value map in a finite join-semilattice
  `A`, at `16·√(n·⌊log₂(|A|+1)⌋)`;
* `hasDual_prodMap` — the same certificate read through `AsJoin` for the
  product in a finite commutative idempotent semigroup, the dual vectors
  unchanged;
* `hasDualOn_joinMap_of_bound` / `hasDualOn_joinMap_smallJoin` — the
  instance-sensitive promise certificates at `16·√(n·B)`, charging only
  the critical budget `B` of the allowed inputs;
* `hasDual_joinMap_ambient` / `hasDual_prodMapAmb` — the ambient forms:
  the value type may be **infinite**; only the finite subsemilattice the
  letters generate is ever counted, and the certificate is the generated
  one with its constraint transported along the injective inclusion,
  vectors unchanged.

The file lives downstream of both the semilattice development and
`Promise/HasDual.lean`; no quantum import appears anywhere in this
hierarchy.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Join

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type} [Fintype A] [DecidableEq A] [SemilatticeSup A]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- **The semilattice-product certificate, bundled**:
`HasDual (⋁ᵢ m(xᵢ)) (16·√(n·⌊log₂(|A|+1)⌋))`. -/
theorem hasDual_joinMap [Nonempty A] (m : σ → A) :
    HasDual (joinMap m : (ι → σ) → A)
      (16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ))) := by
  obtain ⟨P, hP⟩ := exists_joinMap_dual_isCostLe (ι := ι) (σ := σ) (A := A) m
  exact ⟨_, inferInstance, P, hP⟩

/-- **The promise certificate from any critical budget**: on a domain whose
inputs all have at most `B` critical positions per prefix, the join has a
dual of cost `16·√(n·B)` — the total scan dual restricted, vectors
unchanged. -/
theorem hasDualOn_joinMap_of_bound {X : Type} [Fintype X] [DecidableEq X]
    {B : ℕ}
    (m : σ → A) (hB : 0 < B) (read : X → ι → σ)
    (hcrit : ∀ (x : X) (T : Finset ι),
      (criticalSet (fun i => m (read x i)) T).card ≤ B) :
    HasDualOn read (fun x => joinMap m (read x))
      (16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)) := by
  obtain ⟨P, hP⟩ := exists_joinMap_dual_pointwise (ι := ι) (A := A) (σ := σ) m hB
  exact ⟨_, inferInstance, P.restrictTo read,
    DualPair.restrictTo_isCostLe
      (fun x => (hP (read x) (hcrit x)).1)
      (fun x => (hP (read x) (hcrit x)).2)⟩

/-- **The instance-sensitive certificate** on the `SmallJoin` promise:
`16·√(n·B)`, with no reference to the size of the value type. -/
theorem hasDualOn_joinMap_smallJoin {B : ℕ} (m : σ → A) (hB : 0 < B) :
    HasDualOn (SmallJoin.read m B)
      (fun x : SmallJoin (ι := ι) m B => joinMap m (SmallJoin.read m B x))
      (16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)) :=
  hasDualOn_joinMap_of_bound m hB _ fun x T => SmallJoin.crit x T

end Join

section Product

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {M : Type} [Fintype M] [DecidableEq M] [Nonempty M]
  [IsIdemCommSemigroup M]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- **The semigroup-product certificate, bundled**: the join certificate
read through `AsJoin`, the dual vectors unchanged — only the constraint is
transported along the injectivity of `AsJoin.val`. -/
theorem hasDual_prodMap (m : σ → M) :
    HasDual (prodMap m : (ι → σ) → M)
      (16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits M : ℝ))) := by
  obtain ⟨P, hP⟩ := exists_joinMap_dual_isCostLe (ι := ι) (A := AsJoin M)
    (σ := σ) (fun s => AsJoin.mk (m s))
  have hcon : ∀ x y : ι → σ,
      (∑ i, if x i = y i then (0 : ℝ) else ∑ k, P.u x i k * P.v y i k)
        = if prodMap m x = prodMap m y then 0 else 1 := by
    intro x y
    rw [P.constraint x y]
    by_cases hxy : joinMap (ι := ι) (A := AsJoin M) (fun s => AsJoin.mk (m s)) x
        = joinMap (ι := ι) (A := AsJoin M) (fun s => AsJoin.mk (m s)) y
    · rw [if_pos hxy,
        if_pos (show prodMap m x = prodMap m y from congrArg AsJoin.val hxy)]
    · rw [if_neg hxy, if_neg (show ¬ prodMap m x = prodMap m y from
        fun hc => hxy (AsJoin.val_injective hc))]
  exact ⟨_, inferInstance, ⟨P.u, P.v, hcon⟩, hP.1, hP.2⟩

end Product

section Ambient

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ]

/-- **The ambient semilattice certificate, bundled**: the value type `M`
may be infinite; the cost counts only the finite subsemilattice
`Generated m` the letters generate.  The certificate is the generated
one, its constraint transported along the injective inclusion with the
dual vectors unchanged. -/
theorem hasDual_joinMap_ambient {M : Type} [SemilatticeSup M]
    [DecidableEq M] (m : σ → M) :
    HasDual (joinMap m : (ι → σ) → M)
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (joinBits (Generated m) : ℝ))) := by
  obtain ⟨P, hP⟩ := exists_joinMap_dual_isCostLe (ι := ι) (A := Generated m)
    (σ := σ) (Generated.of m)
  have hcon : ∀ x y : ι → σ,
      (∑ i, if x i = y i then (0 : ℝ) else ∑ k, P.u x i k * P.v y i k)
        = if joinMap (ι := ι) m x = joinMap (ι := ι) m y then 0 else 1 := by
    intro x y
    rw [P.constraint x y]
    by_cases hxy : joinMap (ι := ι) (Generated.of m) x
        = joinMap (ι := ι) (Generated.of m) y
    · rw [if_pos hxy,
        if_pos (show joinMap (ι := ι) m x = joinMap (ι := ι) m y from by
          rw [← coe_joinMap_of m x, ← coe_joinMap_of m y, hxy])]
    · rw [if_neg hxy,
        if_neg (show ¬ joinMap (ι := ι) m x = joinMap (ι := ι) m y from
          fun hc => hxy (Generated.coe_injective (by
            rw [coe_joinMap_of m x, coe_joinMap_of m y, hc])))]
  exact ⟨_, inferInstance, ⟨P.u, P.v, hcon⟩, hP.1, hP.2⟩

/-- **The ambient semigroup certificate, bundled**: the product in a
possibly infinite commutative idempotent semigroup, counting only the
generated subsemigroup. -/
theorem hasDual_prodMapAmb {M : Type} [DecidableEq M]
    [IsIdemCommSemigroup M] (m : σ → M) :
    HasDual (prodMapAmb m : (ι → σ) → M)
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (joinBits (GeneratedSub m) : ℝ))) :=
  hasDual_joinMap_ambient (ι := ι) (M := AsJoin M) (σ := σ)
    (fun s => AsJoin.mk (m s))

end Ambient

end MonoidProduct
