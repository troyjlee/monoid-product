import MonoidProduct.Width.Main
import QuantumQueryComplexity.Scan.Join
import MonoidProduct.Semilattice.Critical
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Instantiating the essential-width theorem: maximum and semilattice join

Two instantiations, serving as regression tests for `advPM_le_of_summary`
against the bespoke scans:

* **Maximum** has essential width `1`: a position of `T` is essential exactly
  when it is the *unique* occurrence of the maximum of `T`.  In a linear order
  two essential positions would each have to strictly dominate the join of the
  rest — including the other — which is absurd.  Hence
  `ADV±(MAX) ≤ 16√n`, with no dependence on the alphabet, matching
  `exists_maxMap_dual_isCostLe_sixteen`.

* **Semilattice join** has `essentialSet = criticalSet`: deleting `i` changes
  the join exactly when `xᵢ` is not absorbed by the join of the rest, which is
  the criticality condition of `MonoidProduct/Semilattice/Critical.lean`.  Its
  budget `⌊log₂(|A|+1)⌋` is `card_criticalSet_le`, giving
  `ADV±(⋁ᵢ m(xᵢ)) ≤ 16√(n·joinBits A)`, matching `advPM_joinMap_le`.

Both summaries share their state — the join over the revealed set, `⊥` when
nothing is revealed — so the summary is defined once for a `SemilatticeSup`
and the maximum case specialises it to a `LinearOrder`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The join summary -/

section Join

variable {A : Type*} [Fintype A] [DecidableEq A] [SemilatticeSup A]

/-- The join over the full index set is the final state. -/
lemma joinMap_eq_sup_joinOn (m : σ → A) (x : ι → σ) :
    ((joinMap m x : A) : WithBot A) = joinOn (fun j => m (x j)) Finset.univ := by
  rw [coe_joinMap]
  rfl

/-- The join over a revealed set of coordinates, as an incremental summary:
the state is `joinOn`, the output is `joinMap`. -/
noncomputable def joinSummary (m : σ → A) : IncrementalSummary ι σ A (WithBot A) where
  state x T := joinOn (fun j => m (x j)) T
  out x := joinMap m x
  state_empty x y := by simp [joinOn]
  state_insert x y T i hi hstate hxy := by
    rw [joinOn, joinOn, Finset.sup_insert, Finset.sup_insert, hxy,
      show (T.sup fun j => ((m (x j) : A) : WithBot A)) = joinOn (fun j => m (x j)) T
        from rfl,
      show (T.sup fun j => ((m (y j) : A) : WithBot A)) = joinOn (fun j => m (y j)) T
        from rfl,
      hstate]
  out_congr x y h := by
    have hx := joinMap_eq_sup_joinOn (ι := ι) m x
    have hy := joinMap_eq_sup_joinOn (ι := ι) m y
    have : ((joinMap m x : A) : WithBot A) = ((joinMap m y : A) : WithBot A) := by
      rw [hx, hy, h]
    exact_mod_cast this

/-- The join with one member split off. -/
lemma joinOn_eq_sup_erase (x : ι → A) {T : Finset ι} {i : ι} (hi : i ∈ T) :
    joinOn x T = (x i : WithBot A) ⊔ joinOn x (T.erase i) := by
  conv_lhs => rw [show T = insert i (T.erase i) from (Finset.insert_erase hi).symm]
  exact Finset.sup_insert

/-- Deleting `i` changes the join exactly when `xᵢ` is not absorbed: the
essential set of the join summary **is** the critical set. -/
lemma essentialSet_joinSummary (m : σ → A) (x : ι → σ) (T : Finset ι) :
    (joinSummary (ι := ι) m).essentialSet x T
      = criticalSet (fun j => m (x j)) T := by
  ext i
  rw [IncrementalSummary.mem_essentialSet, mem_criticalSet]
  refine and_congr_right fun hi => ?_
  show (joinOn (fun j => m (x j)) T ≠ joinOn (fun j => m (x j)) (T.erase i))
    ↔ ¬ ((m (x i) : WithBot A) ≤ joinOn (fun j => m (x j)) (T.erase i))
  rw [joinOn_eq_sup_erase (fun j => m (x j)) hi]
  constructor
  · intro hne hle
    exact hne (sup_eq_right.mpr hle)
  · intro hnle heq
    exact hnle (le_of_sup_eq heq)

/-- **The semilattice product bound, from the essential-width theorem**
(regression against `advPM_joinMap_le`). -/
theorem advPM_joinMap_le_of_summary [Nonempty A] (m : σ → A) :
    advPM (joinMap m : (ι → σ) → A)
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits A : ℝ)) := by
  have h := advPM_le_of_summary (joinSummary (ι := ι) (σ := σ) m)
    (B := joinBits A) (joinBits_pos (A := A))
    (fun x T => by
      rw [essentialSet_joinSummary]
      exact card_criticalSet_le _ T)
  have hout : (joinSummary (ι := ι) (σ := σ) m).out
      = (joinMap m : (ι → σ) → A) := rfl
  rw [hout] at h
  exact h

end Join

/-! ## The maximum summary -/

section Max

variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]

/-- The maximum is the join of the values. -/
lemma coe_maxFun (x : ι → A) :
    ((maxFun x : A) : WithBot A) = joinOn x Finset.univ := by
  refine le_antisymm ?_ (Finset.sup_le fun i _ => ?_)
  · obtain ⟨i, hi⟩ := exists_eq_maxFun x
    rw [← hi]
    exact Finset.le_sup (f := fun j => ((x j : A) : WithBot A)) (Finset.mem_univ i)
  · exact_mod_cast le_maxFun x i

/-- The maximum, as an incremental summary: the join summary of a linear
order. -/
noncomputable def maxSummary (m : σ → A) : IncrementalSummary ι σ A (WithBot A) :=
  { joinSummary (ι := ι) m with
    out := fun x => maxFun fun j => m (x j)
    out_congr := fun x y h => by
      have hx : ((maxFun fun j => m (x j) : A) : WithBot A)
          = joinOn (fun j => m (x j)) Finset.univ := coe_maxFun _
      have hy : ((maxFun fun j => m (y j) : A) : WithBot A)
          = joinOn (fun j => m (y j)) Finset.univ := coe_maxFun _
      have : ((maxFun fun j => m (x j) : A) : WithBot A)
          = ((maxFun fun j => m (y j) : A) : WithBot A) := by
        rw [hx, hy]
        exact h
      exact_mod_cast this }

/-- **Maximum has essential width one**: two positions cannot both strictly
dominate the join of everything else. -/
lemma card_essentialSet_maxSummary_le (m : σ → A) (x : ι → σ) (T : Finset ι) :
    ((maxSummary (ι := ι) m).essentialSet x T).card ≤ 1 := by
  rw [show (maxSummary (ι := ι) m).essentialSet x T
      = (joinSummary (ι := ι) m).essentialSet x T from rfl,
    essentialSet_joinSummary]
  refine Finset.card_le_one.mpr fun i hi j hj => ?_
  rw [mem_criticalSet] at hi hj
  by_contra hne
  have hij : (m (x i) : WithBot A)
      ≤ joinOn (fun j' => m (x j')) (T.erase j) :=
    le_joinOn (x := fun j' => m (x j')) (Finset.mem_erase.mpr ⟨hne, hi.1⟩)
  have hji : (m (x j) : WithBot A)
      ≤ joinOn (fun j' => m (x j')) (T.erase i) :=
    le_joinOn (x := fun j' => m (x j'))
      (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hj.1⟩)
  -- in a linear order, non-domination means strict domination the other way
  have hilt : joinOn (fun j' => m (x j')) (T.erase i) < (m (x i) : WithBot A) :=
    lt_of_not_ge hi.2
  have hjlt : joinOn (fun j' => m (x j')) (T.erase j) < (m (x j) : WithBot A) :=
    lt_of_not_ge hj.2
  exact absurd (lt_trans (lt_of_le_of_lt hij hjlt) (lt_of_le_of_lt hji hilt))
    (lt_irrefl _)

/-- **`ADV±(MAX) ≤ 16√n`, from the essential-width theorem** (regression
against `exists_maxMap_dual_isCostLe_sixteen`; no dependence on the
alphabet). -/
theorem advPM_maxFun_le_of_summary (m : σ → A) :
    advPM ((fun x : ι → σ => maxFun fun j => m (x j)))
      ≤ 16 * Real.sqrt (Fintype.card ι) := by
  have h := advPM_le_of_summary (maxSummary (ι := ι) (σ := σ) m) (B := 1) one_pos
    (fun x T => card_essentialSet_maxSummary_le m x T)
  have hout : (maxSummary (ι := ι) (σ := σ) m).out
      = fun x : ι → σ => maxFun fun j => m (x j) := rfl
  rw [hout] at h
  simpa using h

end Max

end MonoidProduct
