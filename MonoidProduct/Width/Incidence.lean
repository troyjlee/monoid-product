import MonoidProduct.Width.Summary
import MonoidProduct.Semilattice.Record
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The essential-incidence count

The probability-free heart of the essential-width theorem: for a fixed input,
at most a `B/(t+1)` fraction of scan orders are red at time `t`, stated as

  `(t+1) · |{e : the step at time t is red}| ≤ B · |Order ι|`.

This is `MonoidProduct/Semilattice/Record.lean`'s incidence double count with the
critical set abstracted to **any** assignment `E : Finset ι → Finset ι` with
`E T ⊆ T` and `|E T| ≤ B`:

* the events "the coordinate at position `s ≤ t` lies in `E` of the prefix"
  are equinumerous, by composing an order with the transposition of positions
  `s` and `t` (which fixes the prefix set);
* summing them over `s ≤ t` counts, order by order, `|E (prefix)| ≤ B`.

Nothing about joins survives in the argument, which is why the same count
serves every incremental summary.  The events may overlap — several members of
a prefix can be essential at once — which is exactly what the double count
tolerates and the maximum scan's disjoint-event proof
(`QuantumQueryComplexity/Scan/Record.lean`) does not.

The second half identifies the red event of a summary's scan with membership
of the last-scanned coordinate in the essential set of the prefix: the
before-set of the top coordinate is the prefix minus it
(`beforeSet_eq_erase`), and red means precisely that deleting it changes the
state.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## The abstract incidence count -/

open scoped Classical in
/-- The orders for which the coordinate at position `s` lies in `E` of the
prefix of length `t+1`. -/
noncomputable def essEvent (E : Finset ι → Finset ι)
    (t s : Fin (Fintype.card ι)) : Finset (Order ι) :=
  Finset.univ.filter fun e => e.symm s ∈ E (prefixSet e t)

lemma mem_essEvent {E : Finset ι → Finset ι} {t s : Fin (Fintype.card ι)}
    {e : Order ι} :
    e ∈ essEvent E t s ↔ e.symm s ∈ E (prefixSet e t) := by
  classical
  simp [essEvent]

/-- **The events at the positions `s ≤ t` all have the same size**: transposing
positions `s` and `t` fixes the prefix set and exchanges the two coordinates. -/
lemma card_essEvent_eq (E : Finset ι → Finset ι)
    {t s : Fin (Fintype.card ι)} (hs : s ≤ t) :
    (essEvent E t s).card = (essEvent E t t).card := by
  classical
  refine Finset.card_nbij' (fun e => e.trans (Equiv.swap s t))
    (fun e => e.trans (Equiv.swap s t)) ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_coe, mem_essEvent] at he ⊢
    rw [prefixSet_swap e hs, symm_trans_swap, Equiv.swap_apply_right]
    exact he
  · intro e he
    simp only [Finset.mem_coe, mem_essEvent] at he ⊢
    rw [prefixSet_swap e hs, symm_trans_swap, Equiv.swap_apply_left]
    exact he
  · intro e _
    simp [Equiv.trans_assoc]
  · intro e _
    simp [Equiv.trans_assoc]

/-- For a fixed order, the positions `s ≤ t` whose coordinate lies in `E` of
the prefix biject with `E` of the prefix itself. -/
lemma card_filter_Iic_ess (E : Finset ι → Finset ι)
    (hsub : ∀ T, E T ⊆ T) (e : Order ι) (t : Fin (Fintype.card ι)) :
    ((Finset.Iic t).filter fun s => e.symm s ∈ E (prefixSet e t)).card
      = (E (prefixSet e t)).card := by
  classical
  refine Finset.card_bij (fun s _ => e.symm s) ?_ ?_ ?_
  · intro s hs
    exact (Finset.mem_filter.1 hs).2
  · intro s _ s' _ h
    exact e.symm.injective h
  · intro i hi
    refine ⟨e i, ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_Iic.2 ?_, ?_⟩
      · exact mem_prefixSet.1 (hsub _ hi)
      · rw [Equiv.symm_apply_apply]
        exact hi
    · rw [Equiv.symm_apply_apply]

/-- **The incidence count**: at most a `B/(t+1)` fraction of scan orders place
a member of `E` at position `t`, for any uniform bound `B` on `|E T|`. -/
theorem card_essEvent_mul_le_of_bound {B : ℕ} (E : Finset ι → Finset ι)
    (hsub : ∀ T, E T ⊆ T) (hB : ∀ T, (E T).card ≤ B)
    (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) * (essEvent E t t).card ≤ B * Fintype.card (Order ι) := by
  classical
  have hconst : (∑ _s ∈ Finset.Iic t, (essEvent E t t).card)
      = ((t : ℕ) + 1) * (essEvent E t t).card := by
    rw [Finset.sum_const, Fin.card_Iic, smul_eq_mul]
  have hsame : (∑ s ∈ Finset.Iic t, (essEvent E t s).card)
      = ∑ _s ∈ Finset.Iic t, (essEvent E t t).card :=
    Finset.sum_congr rfl fun s hs => card_essEvent_eq E (Finset.mem_Iic.1 hs)
  have hswap : (∑ s ∈ Finset.Iic t, (essEvent E t s).card)
      = ∑ e : Order ι, (E (prefixSet e t)).card := by
    calc (∑ s ∈ Finset.Iic t, (essEvent E t s).card)
        = ∑ s ∈ Finset.Iic t, ∑ e : Order ι,
            (if e.symm s ∈ E (prefixSet e t) then 1 else 0) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [essEvent, Finset.card_filter]
      _ = ∑ e : Order ι, ∑ s ∈ Finset.Iic t,
            (if e.symm s ∈ E (prefixSet e t) then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ e : Order ι, (E (prefixSet e t)).card := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.card_filter]
          exact card_filter_Iic_ess E hsub e t
  rw [← hconst, ← hsame, hswap]
  calc (∑ e : Order ι, (E (prefixSet e t)).card)
      ≤ ∑ _e : Order ι, B := Finset.sum_le_sum fun e _ => hB _
    _ = B * Fintype.card (Order ι) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

/-! ## The red event of a summary's scan -/

namespace IncrementalSummary

variable (S : IncrementalSummary ι σ O Q)

/-- The prefix up to and including the coordinate at position `t` is the
prefix set. -/
lemma upToSet_symm_eq_prefixSet (e : Order ι) (t : Fin (Fintype.card ι)) :
    upToSet (⇑e) (e.symm t) = prefixSet e t := by
  ext j
  rw [mem_upToSet, mem_prefixSet, Equiv.apply_symm_apply]

/-- **The red event of a summary's scan is essentiality at the top of the
prefix.** -/
lemma toScan_col_iff_mem_essentialSet (e : Order ι) (x : ι → σ)
    (t : Fin (Fintype.card ι)) :
    (S.toScan ⇑e e.injective).col x (e.symm t) = true
      ↔ e.symm t ∈ S.essentialSet x (prefixSet e t) := by
  rw [S.toScan_col_eq_true_iff, mem_essentialSet,
    upToSet_symm_eq_prefixSet, beforeSet_eq_erase]
  have hmem : e.symm t ∈ prefixSet e t := by
    rw [mem_prefixSet, Equiv.apply_symm_apply]
  exact ⟨fun h => ⟨hmem, h⟩, fun h => h.2⟩

/-- **The red count for a summary**, in counting form: with essential width at
most `B`, at most a `B/(t+1)` fraction of scan orders are red at time `t`. -/
theorem card_red_mul_le_of_bound {B : ℕ} (x : ι → σ)
    (hB : ∀ T : Finset ι, (S.essentialSet x T).card ≤ B)
    (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) * (Finset.univ.filter fun e : Order ι =>
        (S.toScan ⇑e e.injective).col x (e.symm t) = true).card
      ≤ B * Fintype.card (Order ι) := by
  classical
  have hset : (Finset.univ.filter fun e : Order ι =>
      (S.toScan ⇑e e.injective).col x (e.symm t) = true)
      = essEvent (S.essentialSet x) t t := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_essEvent]
    exact S.toScan_col_iff_mem_essentialSet e x t
  rw [hset]
  exact card_essEvent_mul_le_of_bound (S.essentialSet x)
    (fun T => S.essentialSet_subset x T) hB t

end IncrementalSummary

end MonoidProduct
