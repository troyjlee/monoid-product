import QuantumQueryComplexity.Promise.Defs
import MonoidProduct.Semilattice.Final
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The instance-sensitive semilattice bound

`advPM_joinMap_le` charges `⌊log₂(|A|+1)⌋` for the whole value type, because
`advPM` is one number for a total function.  What the algorithm really pays is
governed by the letters of the input actually presented.  On a promise domain
that can be said:

  `advPMOn read (⋁ᵢ m (read x i)) ≤ 16 √(n B)`

as soon as every promise input has at most `B` critical positions in each of its
prefixes — for instance, whenever the semilattice its letters generate has at
most `2^B - 1` elements.

Nothing new is constructed.  `exists_joinMap_dual_pointwise` already bounds the
mass of one fixed dual solution *at each input separately*, using only that
input's critical budget; `DualPair.restrictTo` then reads that solution on the
promise, where its cost is the maximum of those pointwise masses.  This is why
the promise API is worth having: the same witness serves every promise, and only
the accounting changes.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [SemilatticeSup A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The semilattice product bound on a promise domain.**

`B` bounds the critical positions of the promise inputs only.  The value type may
be far larger than `2 ^ B`; what is charged is the local structure of each
allowed input. -/
theorem advPMOn_joinMap_le_of_bound {B : ℕ} (m : σ → A) (hB : 0 < B)
    (read : X → ι → σ)
    (hcrit : ∀ (x : X) (T : Finset ι),
      (criticalSet (fun i => m (read x i)) T).card ≤ B) :
    advPMOn read (fun x => joinMap m (read x))
      ≤ 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B) := by
  obtain ⟨P, hP⟩ := exists_joinMap_dual_pointwise (ι := ι) (A := A) (σ := σ) m hB
  refine advPMOn_le_of_dualPairOn (P.restrictTo read) (by positivity) ?_
  exact DualPair.restrictTo_isCostLe
    (fun x => (hP (read x) (hcrit x)).1) (fun x => (hP (read x) (hcrit x)).2)

/-! ## The promise of a small generated semilattice -/

/-- The inputs whose letters generate a semilattice small enough that no prefix
has more than `B` critical positions. -/
def SmallJoin (m : σ → A) (B : ℕ) : Type _ :=
  {x : ι → σ // ∀ T : Finset ι, (criticalSet (fun i => m (x i)) T).card ≤ B}

namespace SmallJoin

variable {m : σ → A} {B : ℕ}

instance : Finite (SmallJoin (ι := ι) m B) :=
  Subtype.finite

noncomputable instance : Fintype (SmallJoin (ι := ι) m B) :=
  Fintype.ofFinite _

noncomputable instance : DecidableEq (SmallJoin (ι := ι) m B) :=
  Classical.decEq _

/-- Reading a promise input. -/
def read (m : σ → A) (B : ℕ) (x : SmallJoin (ι := ι) m B) : ι → σ := x.1

lemma crit (x : SmallJoin (ι := ι) m B) (T : Finset ι) :
    (criticalSet (fun i => m (read m B x i)) T).card ≤ B := x.2 T

end SmallJoin

/-- **The instance-sensitive bound**.

On the promise that every input's prefixes have at most `B` critical positions,
the product costs `16 √(n B)` — with no reference at all to the size of the
ambient value type. -/
theorem advPMOn_joinMap_smallJoin {B : ℕ} (m : σ → A) (hB : 0 < B) :
    advPMOn (SmallJoin.read m B)
        (fun x : SmallJoin (ι := ι) m B => joinMap m (SmallJoin.read m B x))
      ≤ 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt B) :=
  advPMOn_joinMap_le_of_bound m hB _ fun x T => SmallJoin.crit x T

/-- The total bound is the promise bound at the trivial promise: every input has
at most `joinBits A` critical positions. -/
theorem advPMOn_joinMap_total [Nonempty A] (m : σ → A) :
    advPMOn (fun x : ι → σ => x) (joinMap m : (ι → σ) → A)
      ≤ 16 * (Real.sqrt (Fintype.card ι) * Real.sqrt (joinBits A)) :=
  advPMOn_joinMap_le_of_bound m joinBits_pos _
    fun x T => card_criticalSet_le (fun i => m (x i)) T

end MonoidProduct
