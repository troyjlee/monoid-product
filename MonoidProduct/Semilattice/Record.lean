import MonoidProduct.Semilattice.Critical
import QuantumQueryComplexity.Scan.Record
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The critical-incidence count

Over a uniformly random scan order, the step at time `t` is red for at most a
`B / (t+1)` fraction of orders, where `B = ⌊log₂(|A|+1)⌋`.  Stated without
probabilities, as Lean wants it:

  `(t+1) · |{e : the step at time t is red}| ≤ B · |Order ι|`.

The maximum case (`QuantumQueryComplexity/Scan/Record.lean`) proves the corresponding fact by
exhibiting `t+1` **disjoint** events — a strict dominator is unique.  That is
unavailable here: several positions of a prefix can be critical at once, so the
events `𝒞_{t,s}` overlap.  The replacement is an incidence double count.  Both

  `∑_{s ≤ t} |𝒞_{t,s}|`   and   `∑_e |C(x, prefix of e at t)|`

count the pairs `(s, e)` with `e.symm s` critical in that prefix; the first sum
has `t+1` equal terms because composing an order with the transposition of
positions `s` and `t` fixes the prefix and exchanges which coordinate sits at
`s` and `t`, and the second is bounded termwise by `B`.

Finally the event at the *top* position is exactly the red event of the join
scan: the other members of the prefix are precisely the coordinates scanned
earlier, so `¬ (x_{e⁻¹(t)} ≤ ⋁_{s<t} x_{e⁻¹(s)})` is both the criticality of
`e⁻¹(t)` in the prefix and `isJoinRecord`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [SemilatticeSup A]

/-! ## Prefixes and critical events -/

/-- The coordinates scanned at time at most `t`. -/
def prefixSet (e : Order ι) (t : Fin (Fintype.card ι)) : Finset ι :=
  Finset.univ.filter fun i => e i ≤ t

lemma mem_prefixSet {e : Order ι} {t : Fin (Fintype.card ι)} {i : ι} :
    i ∈ prefixSet e t ↔ e i ≤ t := by simp [prefixSet]

open scoped Classical in
/-- The orders for which the coordinate at position `s` is critical in the
prefix of length `t+1`. -/
noncomputable def critEvent (x : ι → A) (t s : Fin (Fintype.card ι)) :
    Finset (Order ι) :=
  Finset.univ.filter fun e => e.symm s ∈ criticalSet x (prefixSet e t)

lemma mem_critEvent {x : ι → A} {t s : Fin (Fintype.card ι)} {e : Order ι} :
    e ∈ critEvent x t s ↔ e.symm s ∈ criticalSet x (prefixSet e t) := by
  classical
  simp [critEvent]

/-! ## The events at different positions are equinumerous -/

lemma swap_le_iff {s t u : Fin (Fintype.card ι)} (hs : s ≤ t) :
    Equiv.swap s t u ≤ t ↔ u ≤ t := by
  rcases eq_or_ne u s with rfl | hus
  · rw [Equiv.swap_apply_left]
    simp [hs]
  · rcases eq_or_ne u t with rfl | hut
    · rw [Equiv.swap_apply_right]
      simp [hs]
    · rw [Equiv.swap_apply_of_ne_of_ne hus hut]

/-- Transposing two positions of the scan order does not change the prefix. -/
lemma prefixSet_swap (e : Order ι) {t s : Fin (Fintype.card ι)} (hs : s ≤ t) :
    prefixSet (e.trans (Equiv.swap s t)) t = prefixSet e t := by
  ext i
  simp only [mem_prefixSet, Equiv.trans_apply]
  exact swap_le_iff hs

lemma symm_trans_swap (e : Order ι) (s t u : Fin (Fintype.card ι)) :
    (e.trans (Equiv.swap s t)).symm u = e.symm (Equiv.swap s t u) := by
  simp [Equiv.symm_trans_apply, Equiv.symm_swap]

/-- **The critical events at the positions `s ≤ t` all have the same size.** -/
lemma card_critEvent_eq (x : ι → A) {t s : Fin (Fintype.card ι)} (hs : s ≤ t) :
    (critEvent x t s).card = (critEvent x t t).card := by
  classical
  refine Finset.card_nbij' (fun e => e.trans (Equiv.swap s t))
    (fun e => e.trans (Equiv.swap s t)) ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_coe, mem_critEvent] at he ⊢
    rw [prefixSet_swap e hs, symm_trans_swap, Equiv.swap_apply_right]
    exact he
  · intro e he
    simp only [Finset.mem_coe, mem_critEvent] at he ⊢
    rw [prefixSet_swap e hs, symm_trans_swap, Equiv.swap_apply_left]
    exact he
  · intro e _
    simp [Equiv.trans_assoc]
  · intro e _
    simp [Equiv.trans_assoc]

/-! ## The incidence double count -/

/-- For a fixed order, the positions `s ≤ t` whose coordinate is critical in the
prefix biject with the critical positions themselves. -/
lemma card_filter_Iic (x : ι → A) (e : Order ι) (t : Fin (Fintype.card ι)) :
    ((Finset.Iic t).filter fun s =>
        e.symm s ∈ criticalSet x (prefixSet e t)).card
      = (criticalSet x (prefixSet e t)).card := by
  classical
  refine Finset.card_bij (fun s _ => e.symm s) ?_ ?_ ?_
  · intro s hs
    exact (Finset.mem_filter.1 hs).2
  · intro s _ s' _ h
    exact e.symm.injective h
  · intro i hi
    refine ⟨e i, ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_Iic.2 ?_, ?_⟩
      · exact mem_prefixSet.1 (criticalSet_subset x _ hi)
      · rw [Equiv.symm_apply_apply]
        exact hi
    · rw [Equiv.symm_apply_apply]

/-- **The record count.**  At most a `B/(t+1)` fraction of scan orders make the
step at time `t` critical, for any uniform bound `B` on the number of critical
positions.  Abstracting the budget keeps the analytic half of the argument
independent of *why* critical sets are small: `joinBits` is one instantiation,
and a chain — where at most one position per prefix is critical — is another,
recovering the maximum bound. -/
theorem card_critEvent_mul_le_of_bound {B : ℕ} (x : ι → A)
    (hcrit : ∀ T : Finset ι, (criticalSet x T).card ≤ B)
    (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) * (critEvent x t t).card
      ≤ B * Fintype.card (Order ι) := by
  classical
  have hconst : (∑ _s ∈ Finset.Iic t, (critEvent x t t).card)
      = ((t : ℕ) + 1) * (critEvent x t t).card := by
    rw [Finset.sum_const, Fin.card_Iic, smul_eq_mul]
  have hsame : (∑ s ∈ Finset.Iic t, (critEvent x t s).card)
      = ∑ _s ∈ Finset.Iic t, (critEvent x t t).card :=
    Finset.sum_congr rfl fun s hs => card_critEvent_eq x (Finset.mem_Iic.1 hs)
  have hswap : (∑ s ∈ Finset.Iic t, (critEvent x t s).card)
      = ∑ e : Order ι, (criticalSet x (prefixSet e t)).card := by
    calc (∑ s ∈ Finset.Iic t, (critEvent x t s).card)
        = ∑ s ∈ Finset.Iic t, ∑ e : Order ι,
            (if e.symm s ∈ criticalSet x (prefixSet e t) then 1 else 0) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [critEvent, Finset.card_filter]
      _ = ∑ e : Order ι, ∑ s ∈ Finset.Iic t,
            (if e.symm s ∈ criticalSet x (prefixSet e t) then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ e : Order ι, (criticalSet x (prefixSet e t)).card := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.card_filter]
          exact card_filter_Iic x e t
  rw [← hconst, ← hsame, hswap]
  calc (∑ e : Order ι, (criticalSet x (prefixSet e t)).card)
      ≤ ∑ _e : Order ι, B := Finset.sum_le_sum fun e _ => hcrit _
    _ = B * Fintype.card (Order ι) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

/-- The record count with the cardinality budget. -/
theorem card_critEvent_mul_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) * (critEvent x t t).card
      ≤ joinBits A * Fintype.card (Order ι) :=
  card_critEvent_mul_le_of_bound x (fun T => card_criticalSet_le x T) t

/-! ## The red event of the join scan -/

lemma beforeSet_eq_erase (e : Order ι) (t : Fin (Fintype.card ι)) :
    beforeSet (⇑e) (e.symm t) = (prefixSet e t).erase (e.symm t) := by
  ext j
  simp only [beforeSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, mem_prefixSet, Equiv.apply_symm_apply]
  constructor
  · intro h
    refine ⟨fun hj => ?_, le_of_lt h⟩
    rw [hj, Equiv.apply_symm_apply] at h
    exact absurd h (lt_irrefl _)
  · rintro ⟨hne, hle⟩
    refine lt_of_le_of_ne hle fun hh => hne ?_
    rw [← hh, Equiv.symm_apply_apply]

/-- **The red event is exactly criticality at the top of the prefix.** -/
lemma isJoinRecord_iff_mem_critEvent (x : ι → A) (e : Order ι)
    (t : Fin (Fintype.card ι)) :
    isJoinRecord (⇑e) x (e.symm t) = true ↔ e ∈ critEvent x t t := by
  rw [isJoinRecord_eq_true_iff, mem_critEvent, mem_criticalSet]
  have hmem : e.symm t ∈ prefixSet e t := by
    rw [mem_prefixSet, Equiv.apply_symm_apply]
  have hjoin : joinOn x ((prefixSet e t).erase (e.symm t))
      = runBefore (⇑e) x (e.symm t) := by
    rw [joinOn, runBefore, beforeSet_eq_erase]
  rw [hjoin]
  exact ⟨fun h => ⟨hmem, h⟩, fun h => h.2⟩

/-- **The record lemma for the join scan**, in counting form. -/
theorem card_joinRecord_mul_le_of_bound {B : ℕ} (x : ι → A)
    (hcrit : ∀ T : Finset ι, (criticalSet x T).card ≤ B)
    (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) * (Finset.univ.filter fun e : Order ι =>
        isJoinRecord (⇑e) x (e.symm t) = true).card
      ≤ B * Fintype.card (Order ι) := by
  classical
  have hset : (Finset.univ.filter fun e : Order ι =>
      isJoinRecord (⇑e) x (e.symm t) = true) = critEvent x t t := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isJoinRecord_iff_mem_critEvent x e t
  rw [hset]
  exact card_critEvent_mul_le_of_bound x hcrit t

theorem card_joinRecord_mul_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) * (Finset.univ.filter fun e : Order ι =>
        isJoinRecord (⇑e) x (e.symm t) = true).card
      ≤ joinBits A * Fintype.card (Order ι) :=
  card_joinRecord_mul_le_of_bound x (fun T => card_criticalSet_le x T) t

end MonoidProduct
