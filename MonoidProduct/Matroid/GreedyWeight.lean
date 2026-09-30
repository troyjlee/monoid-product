import MonoidProduct.Matroid.Greedy
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Fin
set_option linter.style.header false

/-!
# Greedy bases have minimum total weight

This file proves the optimality step in the proof of `thm:matroid-basis-query` of
`monoid.tex`: for a matroid on a linearly ordered ground type and any monotone cost
function, the greedy basis `greedy M S` of `S` is a basis of `S` whose total cost is at
most that of every basis of `S`.

The argument is the one in `monoid.tex`.  On every order prefix the greedy basis
retains a basis of that prefix (`isBasis_greedy_inter`), hence at least as many
elements as any other basis `J` of `S`.  Both bases have the same size, so the `j`-th
smallest element of the greedy basis is at most the `j`-th smallest element of `J`
(`orderEmbOfFin_le_of_card_filter_le`, a general statement about finite subsets of a
linear order).  Summing the monotone cost over these pointwise comparisons gives
`greedy_minWeight`.

No hypothesis on the costs beyond monotonicity is used: ties between costs, negative
costs, the empty set, and sets `S` of rank smaller than that of the matroid are all
covered by the same statement.
-/

namespace MonoidProduct

open Finset

section Dominance

variable {α : Type*} [LinearOrder α]

/-- **Prefix-count dominance gives pointwise dominance.**  If two finite sets of a linear
order have the same size `k` and every initial segment `(-∞, a]` contains at least as
many elements of `A` as of `B`, then the `i`-th smallest element of `A` is at most the
`i`-th smallest element of `B`. -/
theorem orderEmbOfFin_le_of_card_filter_le {A B : Finset α} {k : ℕ}
    (hA : #A = k) (hB : #B = k)
    (hdom : ∀ a, #(B.filter (· ≤ a)) ≤ #(A.filter (· ≤ a))) (i : Fin k) :
    A.orderEmbOfFin hA i ≤ B.orderEmbOfFin hB i := by
  classical
  set b := B.orderEmbOfFin hB i
  by_contra hlt
  rw [not_le] at hlt
  -- at least `i + 1` elements of `B` are at most `b`
  have hlow : (Iic i).card ≤ #(B.filter (· ≤ b)) := by
    rw [← card_map (B.orderEmbOfFin hB).toEmbedding]
    refine card_le_card fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := mem_map.1 hx
    exact mem_filter.2 ⟨B.orderEmbOfFin_mem hB j,
      (B.orderEmbOfFin hB).monotone (mem_Iic.1 hj)⟩
  -- at most `i` elements of `A` are at most `b`
  have hhigh : #(A.filter (· ≤ b)) ≤ (Iio i).card := by
    rw [← card_map (A.orderEmbOfFin hA).toEmbedding]
    refine card_le_card fun x hx => ?_
    obtain ⟨hxA, hxb⟩ := mem_filter.1 hx
    have hx' : x ∈ Set.range (A.orderEmbOfFin hA) := by
      rw [range_orderEmbOfFin]; exact hxA
    obtain ⟨j, rfl⟩ := hx'
    refine mem_map.2 ⟨j, mem_Iio.2 ?_, rfl⟩
    exact (A.orderEmbOfFin hA).lt_iff_lt.1 (lt_of_le_of_lt hxb hlt)
  have := (hlow.trans (hdom b)).trans hhigh
  rw [Fin.card_Iic, Fin.card_Iio] at this
  omega

/-- Summing a monotone function over two finite sets of equal size, where the first
dominates the second on every initial segment, gives the smaller total on the first. -/
theorem sum_le_sum_of_card_filter_le {β : Type*} [AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β] {A B : Finset α} (hcard : #A = #B)
    (hdom : ∀ a, #(B.filter (· ≤ a)) ≤ #(A.filter (· ≤ a)))
    {f : α → β} (hf : Monotone f) : ∑ x ∈ A, f x ≤ ∑ x ∈ B, f x := by
  have hsum : ∀ (C : Finset α) (h : #C = #A),
      ∑ x ∈ C, f x = ∑ i : Fin #A, f (C.orderEmbOfFin h i) := by
    intro C h
    conv_lhs => rw [← C.map_orderEmbOfFin_univ h]
    rw [sum_map]
    rfl
  rw [hsum A rfl, hsum B hcard.symm]
  exact sum_le_sum fun i _ => hf (orderEmbOfFin_le_of_card_filter_le rfl hcard.symm hdom i)

end Dominance

namespace Matroid

variable {E : Type*} [LinearOrder E] {M : _root_.Matroid E}

/-- On every initial segment, the greedy basis of `S` has at least as many elements as
any independent subset of `S`. -/
lemma card_filter_le_card_filter_greedy (hM : M.E = Set.univ) {S J : Finset E}
    (hJ : M.Indep ↑J) (hJS : J ⊆ S) (a : E) :
    #(J.filter (· ≤ a)) ≤ #((greedy M S).filter (· ≤ a)) := by
  have hB := isBasis_greedy_inter hM S (isLowerSet_Iic a)
  have h : (↑J ∩ Set.Iic a : Set E).encard
      ≤ (↑(greedy M S) ∩ Set.Iic a : Set E).encard := by
    rw [hB.encard_eq_eRk]
    exact (hJ.subset Set.inter_subset_left).encard_le_eRk_of_subset
      (Set.inter_subset_inter_left _ (by exact_mod_cast hJS))
  rw [← coe_filter_le_eq_inter_Iic, ← coe_filter_le_eq_inter_Iic,
    Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

omit [LinearOrder E] in
/-- Any two bases of the same set have the same number of elements. -/
lemma card_eq_card_of_isBasis_finset {S I J : Finset E} (hI : M.IsBasis ↑I ↑S)
    (hJ : M.IsBasis ↑J ↑S) : #I = #J := by
  have h := hI.encard_eq_eRk.trans hJ.encard_eq_eRk.symm
  rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

/-- **Minimum weight** (`thm:matroid-basis-query`): for every monotone cost function, the
greedy basis of `S` costs no more than any basis `J` of `S`. -/
theorem greedy_minWeight (hM : M.E = Set.univ) {β : Type*} [AddCommMonoid β]
    [PartialOrder β] [IsOrderedAddMonoid β] {cost : E → β} (hcost : Monotone cost)
    {S J : Finset E} (hJ : M.IsBasis ↑J ↑S) :
    ∑ e ∈ greedy M S, cost e ≤ ∑ e ∈ J, cost e :=
  sum_le_sum_of_card_filter_le (card_eq_card_of_isBasis_finset (isBasis_greedy hM S) hJ)
    (card_filter_le_card_filter_greedy hM hJ.indep (by exact_mod_cast hJ.subset)) hcost

/-- The greedy basis of `S` is a minimum-cost basis of `S` for every monotone cost. -/
theorem greedy_isMinWeightBasis (hM : M.E = Set.univ) {β : Type*} [AddCommMonoid β]
    [PartialOrder β] [IsOrderedAddMonoid β] {cost : E → β} (hcost : Monotone cost)
    (S : Finset E) :
    M.IsBasis ↑(greedy M S) ↑S ∧
      ∀ J : Finset E, M.IsBasis ↑J ↑S →
        ∑ e ∈ greedy M S, cost e ≤ ∑ e ∈ J, cost e :=
  ⟨isBasis_greedy hM S, fun _ hJ => greedy_minWeight hM hcost hJ⟩

end Matroid

end MonoidProduct
