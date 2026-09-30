import MonoidProduct.Matroid.Records
import MonoidProduct.Width.Summary
set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# The canonical basis as an incremental summary

This file supplies the essential-width input of `thm:matroid-basis-query` in `monoid.tex`
(section `sec:matroid-bases`).  The state of a revealed set `T` of positions is the canonical
basis `basisRecords M x T`: the selected **records**, carrying their elements and weights,
not merely their positions (positions alone do not determine the next update).  The input
alphabet is the physical one, `Option (E × W)`: a query returns a whole weighted element or
a null record.

* `matroidBasisSummary`: the incremental summary with this state and any readout of the
  final state.  The empty state is `∅`, and the insertion law is the merge law
  `lem:matroid-greedy-merge` in the form `basisRecords_insert_congr`.
* `basisRecords_essentialSet_eq`: the essential positions of `T` are **exactly** the
  selected positions `basisIndices M x T`.  Deleting an unselected position changes nothing,
  while deleting a selected one removes its uniquely tagged record.
* `card_essentialSet_matroidBasisSummary_le`: the essential width is at most `r` whenever
  `M.eRank ≤ r`, and `card_essentialSet_matroidBasisSummary_le_card` bounds it by `#T`.
-/

namespace MonoidProduct.Matroid
open Set

variable {ι E W O : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder E] [LinearOrder W]
variable [Fintype E] [Fintype W] [Fintype O] [DecidableEq O]
variable {M : _root_.Matroid E}

/-- **The canonical basis as an incremental summary** (`thm:matroid-basis-query`): the state
of a revealed position set `T` is the set `basisRecords M x T` of selected records, and the
output is any function `g` of the final state. -/
noncomputable def matroidBasisSummary (hM : M.E = univ)
    (g : Finset (WeightedRecord ι E W) → O) :
    IncrementalSummary ι (Option (E × W)) O (Finset (WeightedRecord ι E W)) where
  state x T := basisRecords M x T
  out x := g (basisRecords M x Finset.univ)
  state_empty x y := by rw [basisRecords_empty, basisRecords_empty]
  state_insert _ _ _ _ _ hT hi := basisRecords_insert_congr hM hT hi
  out_congr _ _ h := congrArg g h

@[simp] lemma matroidBasisSummary_state (hM : M.E = univ)
    (g : Finset (WeightedRecord ι E W) → O) (x : ι → Option (E × W)) (T : Finset ι) :
    (matroidBasisSummary hM g).state x T = basisRecords M x T := rfl

@[simp] lemma matroidBasisSummary_out (hM : M.E = univ)
    (g : Finset (WeightedRecord ι E W) → O) (x : ι → Option (E × W)) :
    (matroidBasisSummary hM g).out x = g (basisRecords M x Finset.univ) := rfl

/-- **The essential positions are exactly the selected positions**
(`thm:matroid-basis-query`). -/
theorem basisRecords_essentialSet_eq (hM : M.E = univ)
    (g : Finset (WeightedRecord ι E W) → O) (x : ι → Option (E × W)) (T : Finset ι) :
    (matroidBasisSummary hM g).essentialSet x T = basisIndices M x T := by
  ext i
  rw [IncrementalSummary.mem_essentialSet, matroidBasisSummary_state,
    matroidBasisSummary_state, ne_comm, Ne, basisRecords_erase_eq_iff hM, not_not]
  exact ⟨And.right, fun h => ⟨basisIndices_subset M x T h, h⟩⟩

/-- **Essential width at most the rank**: under `M.eRank ≤ r`, at most `r` positions of any
revealed set are essential. -/
theorem card_essentialSet_matroidBasisSummary_le (hM : M.E = univ) {r : ℕ}
    (hr : M.eRank ≤ r) (g : Finset (WeightedRecord ι E W) → O) (x : ι → Option (E × W))
    (T : Finset ι) : ((matroidBasisSummary hM g).essentialSet x T).card ≤ r := by
  rw [basisRecords_essentialSet_eq, card_basisIndices]
  exact_mod_cast (card_basisRecords_le_eRank hM x T).trans hr

/-- The essential width is also at most the number of revealed positions. -/
theorem card_essentialSet_matroidBasisSummary_le_card (hM : M.E = univ)
    (g : Finset (WeightedRecord ι E W) → O) (x : ι → Option (E × W)) (T : Finset ι) :
    ((matroidBasisSummary hM g).essentialSet x T).card ≤ T.card :=
  Finset.card_le_card ((matroidBasisSummary hM g).essentialSet_subset x T)

end MonoidProduct.Matroid
