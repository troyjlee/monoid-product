/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import MonoidProduct

/-!
# MonoidProduct axiom checks

Every headline theorem of the semigroup product development is asserted, via
`#guard_msgs`, to depend on exactly `[propext, Classical.choice, Quot.sound]`,
the axioms of ordinary classical mathematics in Lean. If a `sorry` (the axiom
`sorryAx`) or any new axiom enters a proof upstream, this file stops compiling,
so CI turns the axiom policy into a build invariant.

The checks are grouped by the sections of the paper; the paper correspondence
(`docs/monoid-product/PAPER_CORRESPONDENCE.md`) says which result each
declaration formalizes.
-/

-- The expected messages are single lines longer than the style limit.
set_option linter.style.longLine false

/-! ## Main results: commutative aperiodic monoids (Theorem 18, `thm:commutative-beta`) -/

/-- info: 'MonoidProduct.advPM_prodFun_le_breadth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.advPM_prodFun_le_breadth

/-- info: 'MonoidProduct.commutative_qQuery_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.commutative_qQuery_sandwich

/-- info: 'MonoidProduct.commutative_qQuery_lower_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.commutative_qQuery_lower_total

/-- info: 'MonoidProduct.qQuery_prodFun_le_min_of_breadth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQuery_prodFun_le_min_of_breadth_le

/-! ## Main results: stably ordered monoids (Theorem 42, `thm:ordered-beta-log-product`) -/

/-- info: 'MonoidProduct.ordered_qQuery_third_le_quasipoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.ordered_qQuery_third_le_quasipoly

/-- info: 'MonoidProduct.ordered_exists_core_alg_quasipoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.ordered_exists_core_alg_quasipoly

/-- info: 'MonoidProduct.ordered_exists_verified_core_alg_quasipoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.ordered_exists_verified_core_alg_quasipoly

/-- info: 'MonoidProduct.ordered_truthful_core_alg_quasipoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.ordered_truthful_core_alg_quasipoly

/-! ## Main results: aperiodic monoids and semigroups (Theorem 73, `thm:ags-cuberoot-size`) -/

/-- info: 'MonoidProduct.aperiodic_qQuery_final_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.aperiodic_qQuery_final_exact

/-- info: 'MonoidProduct.aperiodic_oneHotQQuery_final_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.aperiodic_oneHotQQuery_final_exact

/-- info: 'MonoidProduct.aperiodic_qQuery_intro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.aperiodic_qQuery_intro

/-- info: 'MonoidProduct.aperiodic_oneHotQQuery_intro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.aperiodic_oneHotQQuery_intro

/-- info: 'MonoidProduct.aperiodic_qQuery_paper_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.aperiodic_qQuery_paper_real

/-- info: 'MonoidProduct.aperiodic_semigroup_oneHotQQuery_final_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.aperiodic_semigroup_oneHotQQuery_final_exact

/-- info: 'MonoidProduct.aperiodic_semigroup_oneHotQQuery_intro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.aperiodic_semigroup_oneHotQQuery_intro

/-! ## Preliminaries and lower bounds (Section 3, `sec:prelim`) -/

/-- info: 'MonoidProduct.qQuery_semigroupProd_le_of_division_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQuery_semigroupProd_le_of_division_lift

/-- info: 'MonoidProduct.qQuery_semigroupProd_lower_of_not_aperiodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQuery_semigroupProd_lower_of_not_aperiodic

/-- info: 'MonoidProduct.trichotomy_lower_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.trichotomy_lower_bounds

/-- info: 'MonoidProduct.index_qQuery_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.index_qQuery_lower

/-! ## General techniques (Section 4, `sec:width`) -/

/-- info: 'MonoidProduct.advPM_le_of_summary_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.advPM_le_of_summary_nonneg

/-- info: 'MonoidProduct.PromiseSummary.advPMOn_le_of_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.PromiseSummary.advPMOn_le_of_width

/-- info: 'MonoidProduct.advPM_wordProd_le_of_isRTrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.advPM_wordProd_le_of_isRTrivial

/-! ## Commutative monoids (Section 5, `sec:lattice`) -/

/-- info: 'MonoidProduct.isJTrivialMonoid_of_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.isJTrivialMonoid_of_comm

/-- info: 'MonoidProduct.isWidthBound_iff_isBreadthBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.isWidthBound_iff_isBreadthBound

/-- info: 'MonoidProduct.qQuery_prodFun_le_joinClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQuery_prodFun_le_joinClosure

/-- info: 'MonoidProduct.qQuery_prodFun_le_indexTwo_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQuery_prodFun_le_indexTwo_min

/-- info: 'MonoidProduct.qQuery_prodFun_le_indexK_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQuery_prodFun_le_indexK_min

/-- info: 'MonoidProduct.cappedLen_qQuery_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.cappedLen_qQuery_theta

/-- info: 'MonoidProduct.capped_binary_qQuery_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.capped_binary_qQuery_lower

/-! ## Minimum-weight matroid bases (Section 6, `sec:matroid-bases`) -/

/-- info: 'MonoidProduct.Matroid.greedy_union_eq_greedy_union_greedy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.greedy_union_eq_greedy_union_greedy

/-- info: 'MonoidProduct.Matroid.greedyBasis_breadth_eq_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.greedyBasis_breadth_eq_rank

/-- info: 'MonoidProduct.Matroid.matroidBasis_minWeight_and_qQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.matroidBasis_minWeight_and_qQuery

/-- info: 'MonoidProduct.Matroid.matroidBasisIndices_qQuery_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.matroidBasisIndices_qQuery_eq_zero

/--
info: 'MonoidProduct.Matroid.minSpanningForest_minWeight_and_qQuery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Matroid.minSpanningForest_minWeight_and_qQuery

/-- info: 'MonoidProduct.Matroid.vectorBasis_minWeight_and_qQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.vectorBasis_minWeight_and_qQuery

/-! ## Ordered monoid products (Section 7, `sec:beta`) -/

/-- info: 'MonoidProduct.ordered_qQuery_third_le_five_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.ordered_qQuery_third_le_five_halves

/-- info: 'MonoidProduct.median_frontier_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.median_frontier_covers

/-- info: 'MonoidProduct.tree_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.tree_sampling

/-- info: 'MonoidProduct.ordered_qQuery_third_le_logrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.ordered_qQuery_third_le_logrank

/-! ## Stock and unitriangular products (Sections 8 and 9) -/

/-- info: 'MonoidProduct.GenStock.gstockProfit_qQuery_third_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.GenStock.gstockProfit_qQuery_third_le

/-- info: 'MonoidProduct.utrop_qQuery_third_le_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.utrop_qQuery_third_le_paper

/-- info: 'MonoidProduct.but_qQuery_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.but_qQuery_theta

/-- info: 'MonoidProduct.jtrivial_qQuery_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.jtrivial_qQuery_le_min

/-! ## The AGS bound and the Dyck obstruction (Section 10, `sec:ags`) -/

/-- info: 'MonoidProduct.orderedProd_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.orderedProd_eq_iff

/-- info: 'MonoidProduct.ags_oneHotQQuery_le_display_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.ags_oneHotQQuery_le_display_logb

/-- info: 'MonoidProduct.dyckLB_qQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.dyckLB_qQuery

/-- info: 'MonoidProduct.breadth_dyck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.breadth_dyck

/-- info: 'MonoidProduct.envD_dyck_qQuery_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.envD_dyck_qQuery_lower

/-- info: 'MonoidProduct.dyckNL_nearLinear_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.dyckNL_nearLinear_lower

/-! ## The cube-root bound and the envelope (Section 11, `sec:ags-cuberoot-size`) -/

/-- info: 'MonoidProduct.solvRec_qQuery_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.solvRec_qQuery_le

/-- info: 'MonoidProduct.Infix.brandt_two_colour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Infix.brandt_two_colour

/-- info: 'MonoidProduct.envD_aperiodic_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.envD_aperiodic_envelope

/-- info: 'MonoidProduct.aperiodic_envelope_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.aperiodic_envelope_linear

/-! ## Displayed forms of further statements -/

/-- info: 'MonoidProduct.idealRank_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.idealRank_mono

/-- info: 'MonoidProduct.prop_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.prop_identity

/-- info: 'MonoidProduct.fixed_monoid_trichotomy_qQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.fixed_monoid_trichotomy_qQuery

/-- info: 'MonoidProduct.fixed_semigroup_trichotomy_qQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.fixed_semigroup_trichotomy_qQuery

/-- info: 'MonoidProduct.qQuery_prodFun_of_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQuery_prodFun_of_subsingleton

/-- info: 'MonoidProduct.cappedLen_qQuery_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.cappedLen_qQuery_size

/-- info: 'MonoidProduct.hasDual_eqProd_localStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.hasDual_eqProd_localStep

/-- info: 'MonoidProduct.qQuery_eqProd_localStep_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQuery_eqProd_localStep_paper

/-- info: 'MonoidProduct.rtrivial_qQuery_le_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.rtrivial_qQuery_le_paper

/-- info: 'QuantumQueryComplexity.AncTree.qQuery_third_treeSearch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuantumQueryComplexity.AncTree.qQuery_third_treeSearch

/-- info: 'MonoidProduct.Matroid.eRank_graphicMatroid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.eRank_graphicMatroid

/-- info: 'MonoidProduct.Matroid.weightedSpanningForest_breadth_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.weightedSpanningForest_breadth_eq

/-- info: 'MonoidProduct.Matroid.ex_spanning_forest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.ex_spanning_forest

/-- info: 'MonoidProduct.hasDual_badInfixFor_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.hasDual_badInfixFor_paper

/-- info: 'MonoidProduct.ags_oneHotQQuery_le_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.ags_oneHotQQuery_le_paper

/-- info: 'MonoidProduct.ags_qQuery_le_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.ags_qQuery_le_paper
