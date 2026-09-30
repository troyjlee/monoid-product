import MonoidProduct.Quantum.SemilatticeApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Semilattice and semigroup products: acceptance test

The statement pins for the operational `O(√(n log|L|))` semilattice-product
endpoints.  Sections 1–4 are the finite forms, and section 5 the ambient
forms with a possibly infinite value type.  Like the other pins, this file exists to be broken; it sits
outside the `QuantumQueryComplexity.Quantum` aggregate and **CI must build it
explicitly**: `lake build QuantumQueryComplexity.Quantum.AcceptanceP`.

Pinned, with every convention literal:

1. **the classical certificates** — `HasDual` at
   `16·√(n·⌊log₂(|A|+1)⌋)` for the join in a finite join-semilattice and
   for the product in a finite commutative idempotent semigroup, and
   `HasDualOn` at `16·√n·√B` on the `SmallJoin` promise, no quantum
   import in their proofs;
2. **the native unabsorbed minimum** at the literal `8192`, error exactly
   `1/3`, exact read-all cap `n`, in both algebraic forms;
3. **the instance-sensitive promise minimum** at `8192` and `16·√n·√B`,
   with the same exact cap — no reference to the size of the value type;
4. **the one-hot unabsorbed minimums** at `16384` with the same exact
   caps;
5. **the ambient forms**: the value type may be **infinite** —
   both certificates and both operational minimums count only the
   finite subsemilattice/subsemigroup the letters generate
   (`joinBits (Generated m)` / `joinBits (GeneratedSub m)`), at the same
   literal `8192`/`16384`.

This family is an upper-bound story; the classical `advPM` theorems
(`advPM_joinMap_le`, `advPM_prodMap_le`, `advPMOn_joinMap_smallJoin`)
remain in place unchanged as the compatibility layer.

Manual axiom checks on the two total minimum forms and the promise form:

    #print axioms MonoidProduct.joinMap_qQuery_le_min
      → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.prodMap_qQuery_le_min
      → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.joinMap_qQueryOn_smallJoin_le_min
      → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
open QuantumQueryComplexity
namespace AcceptanceP

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type} [Fintype A] [DecidableEq A] [SemilatticeSup A]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Fintype M] [DecidableEq M] [Nonempty M]
  [IsIdemCommSemigroup M]

/-! ## 1. The classical certificates -/

theorem dual_join_pinned [Nonempty A] (m : σ → A) :
    HasDual (joinMap m : (ι → σ) → A)
      (16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ))) :=
  hasDual_joinMap m

theorem dual_prod_pinned (m : σ → M) :
    HasDual (prodMap m : (ι → σ) → M)
      (16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits M : ℝ))) :=
  hasDual_prodMap m

theorem dual_smallJoin_pinned {B : ℕ} (m : σ → A) (hB : 0 < B) :
    HasDualOn (SmallJoin.read m B)
      (fun x : SmallJoin (ι := ι) m B => joinMap m (SmallJoin.read m B x))
      (16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B)) :=
  hasDualOn_joinMap_smallJoin m hB

/-! ## 2. The native unabsorbed minimums -/

theorem join_min_pinned [Nonempty A] (m : σ → A) :
    (qQuery (joinMap m : (ι → σ) → A) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (8192
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ)))) := by
  have h := joinMap_qQuery_le_min (ι := ι) m
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

theorem prod_min_pinned (m : σ → M) :
    (qQuery (prodMap m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (8192
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits M : ℝ)))) := by
  have h := prodMap_qQuery_le_min (ι := ι) m
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

/-! ## 3. The instance-sensitive promise minimum -/

theorem smallJoin_min_pinned [Nonempty A] {B : ℕ} (m : σ → A) (hB : 0 < B) :
    (qQueryOn (SmallJoin.read m B)
        (fun x : SmallJoin (ι := ι) m B => joinMap m (SmallJoin.read m B x))
        (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (8192
          * (1 + 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B))) := by
  have h := joinMap_qQueryOn_smallJoin_le_min (ι := ι) m hB
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

/-! ## 4. The one-hot unabsorbed minimums -/

theorem join_oneHot_min_pinned [Nonempty A] (m : σ → A) :
    (oneHotQQuery (joinMap m : (ι → σ) → A) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ)))) :=
  joinMap_oneHotQQuery_le_min m

theorem prod_oneHot_min_pinned (m : σ → M) :
    (oneHotQQuery (prodMap m : (ι → σ) → M) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits M : ℝ)))) :=
  prodMap_oneHotQQuery_le_min m

/-! ## 5. The ambient forms -/

section Ambient

variable [Nonempty σ]

theorem dual_ambient_join_pinned {W : Type} [SemilatticeSup W]
    [DecidableEq W] (m : σ → W) :
    HasDual (joinMap m : (ι → σ) → W)
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (joinBits (Generated m) : ℝ))) :=
  hasDual_joinMap_ambient m

theorem dual_ambient_prod_pinned {W : Type} [DecidableEq W]
    [IsIdemCommSemigroup W] (m : σ → W) :
    HasDual (prodMapAmb m : (ι → σ) → W)
      (16 * Real.sqrt ((Fintype.card ι : ℝ)
        * (joinBits (GeneratedSub m) : ℝ))) :=
  hasDual_prodMapAmb m

theorem ambient_join_min_pinned {W : Type} [SemilatticeSup W]
    [DecidableEq W] (m : σ → W) :
    (qQuery (joinMap m : (ι → σ) → W) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (8192
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (Generated m) : ℝ)))) := by
  have h := joinMapAmbient_qQuery_le_min (ι := ι) m
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

theorem ambient_prod_min_pinned {W : Type} [DecidableEq W]
    [IsIdemCommSemigroup W] (m : σ → W) :
    (qQuery (prodMapAmb m : (ι → σ) → W) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (8192
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (GeneratedSub m) : ℝ)))) := by
  have h := prodMapAmb_qQuery_le_min (ι := ι) m
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

theorem ambient_join_oneHot_min_pinned {W : Type} [SemilatticeSup W]
    [DecidableEq W] (m : σ → W) :
    (oneHotQQuery (joinMap m : (ι → σ) → W) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (Generated m) : ℝ)))) :=
  joinMapAmbient_oneHotQQuery_le_min m

theorem ambient_prod_oneHot_min_pinned {W : Type} [DecidableEq W]
    [IsIdemCommSemigroup W] (m : σ → W) :
    (oneHotQQuery (prodMapAmb m : (ι → σ) → W) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (16384
          * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ)
            * (joinBits (GeneratedSub m) : ℝ)))) :=
  prodMapAmb_oneHotQQuery_le_min m

end Ambient

end AcceptanceP

end MonoidProduct
