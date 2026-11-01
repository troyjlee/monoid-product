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

/-! ## Main results: stably ordered monoids (Theorem 46, `thm:ordered-beta-log-product`) -/

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

/-! ## Main results: aperiodic monoids and semigroups (Theorem 77, `thm:ags-cuberoot-size`) -/

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

/-! ## Strong certificates and product breadth (Section 6, `sec:strong-certificates`) -/

/-- info: 'MonoidProduct.Certificates.strongCertificateSize_eq_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificateSize_eq_sup

/-- info: 'MonoidProduct.Certificates.extensionLetter_breadth_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.extensionLetter_breadth_eq

/-- info: 'MonoidProduct.Certificates.extensionMonoid_breadth_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.extensionMonoid_breadth_eq

/-- info: 'MonoidProduct.Certificates.certificate_breadth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.certificate_breadth

/--
info: 'MonoidProduct.Certificates.card_extensionMonoid_le_sum_choose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.card_extensionMonoid_le_sum_choose

/--
info: 'MonoidProduct.Certificates.strongCertificate_qQuery_le_min_sqrt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificate_qQuery_le_min_sqrt

/--
info: 'MonoidProduct.Certificates.strongCertificate_qQuery_le_min_sqrt_of_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificate_qQuery_le_min_sqrt_of_bound

/-- info: 'MonoidProduct.Certificates.strongCertificate_qQuery_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificate_qQuery_eq_zero

/--
info: 'MonoidProduct.Certificates.encodedCertificate_qQuery_le_min_sqrt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.encodedCertificate_qQuery_le_min_sqrt

/-- info: 'MonoidProduct.Certificates.eq_false_of_sparseYes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.eq_false_of_sparseYes

/--
info: 'MonoidProduct.Certificates.extensionLetter_qQuery_le_min_sqrt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.extensionLetter_qQuery_le_min_sqrt

/-- info: 'MonoidProduct.Certificates.qQuery_recordSet_le_qQuery_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.qQuery_recordSet_le_qQuery_prod

/--
info: 'MonoidProduct.Certificates.strongCertificate_qQuery_le_min_sqrt_fintype' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificate_qQuery_le_min_sqrt_fintype

/--
info: 'MonoidProduct.Certificates.card_essentialSet_encodedSummary_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.card_essentialSet_encodedSummary_le

/--
info: 'MonoidProduct.Certificates.encodedCertificate_qQuery_le_min_sqrt_of_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.encodedCertificate_qQuery_le_min_sqrt_of_bound

/--
info: 'MonoidProduct.Certificates.encodedCertificate_qQuery_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.encodedCertificate_qQuery_eq_zero

/-- info: 'MonoidProduct.Certificates.ExtensionEquiv.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionEquiv.refl

/-- info: 'MonoidProduct.Certificates.ExtensionEquiv.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionEquiv.symm

/-- info: 'MonoidProduct.Certificates.ExtensionEquiv.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionEquiv.trans

/-- info: 'MonoidProduct.Certificates.ExtensionEquiv.apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionEquiv.apply_eq

/-- info: 'MonoidProduct.Certificates.ExtensionEquiv.union_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionEquiv.union_right

/-- info: 'MonoidProduct.Certificates.ExtensionEquiv.union_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionEquiv.union_left

/-- info: 'MonoidProduct.Certificates.ExtensionEquiv.union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionEquiv.union

/-- info: 'MonoidProduct.Certificates.ExtensionEquiv.postcomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionEquiv.postcomp

/-- info: 'MonoidProduct.Certificates.extensionEquiv_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.extensionEquiv_equivalence

/-- info: 'MonoidProduct.Certificates.extensionEquiv_iff_of_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.extensionEquiv_iff_of_merge

/-- info: 'MonoidProduct.Certificates.isStrongCertificate_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.isStrongCertificate_self

/-- info: 'MonoidProduct.Certificates.IsStrongCertificate.of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.IsStrongCertificate.of_subset

/-- info: 'MonoidProduct.Certificates.IsStrongCertificate.postcomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.IsStrongCertificate.postcomp

/-- info: 'MonoidProduct.Certificates.HasStrongCertificateBound.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.HasStrongCertificateBound.mono

/--
info: 'MonoidProduct.Certificates.HasStrongCertificateBound.postcomp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.HasStrongCertificateBound.postcomp

/-- info: 'MonoidProduct.Certificates.hasStrongCertificateBound_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.hasStrongCertificateBound_card

/-- info: 'MonoidProduct.Certificates.strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificateSize_le

/--
info: 'MonoidProduct.Certificates.hasStrongCertificateBound_strongCertificateSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.hasStrongCertificateBound_strongCertificateSize

/--
info: 'MonoidProduct.Certificates.hasStrongCertificateBound_iff_size_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.hasStrongCertificateBound_iff_size_le

/--
info: 'MonoidProduct.Certificates.exists_isStrongCertificate_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.exists_isStrongCertificate_card_le

/-- info: 'MonoidProduct.Certificates.strongCertificateSize_le_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificateSize_le_card

/-- info: 'MonoidProduct.Certificates.le_strongCertificateSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.le_strongCertificateSize

/--
info: 'MonoidProduct.Certificates.strongCertificateSize_postcomp_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificateSize_postcomp_le

/--
info: 'MonoidProduct.Certificates.strongCertificateSize_of_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificateSize_of_injective

/--
info: 'MonoidProduct.Certificates.hasStrongCertificateBound_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.hasStrongCertificateBound_zero_iff

/--
info: 'MonoidProduct.Certificates.strongCertificateSize_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificateSize_eq_zero_iff

/--
info: 'MonoidProduct.Certificates.exists_isStrongCertificate_card_eq_min' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.exists_isStrongCertificate_card_eq_min

/-- info: 'MonoidProduct.Certificates.minStrongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.minStrongCertificateSize_le

/-- info: 'MonoidProduct.Certificates.minStrongCertificateSize_le_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.minStrongCertificateSize_le_card

/--
info: 'MonoidProduct.Certificates.hasStrongCertificateBound_iff_forall_min_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.hasStrongCertificateBound_iff_forall_min_le

/-- info: 'MonoidProduct.Certificates.mem_recordSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.mem_recordSet

/-- info: 'MonoidProduct.Certificates.card_biUnion_toFinset_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.card_biUnion_toFinset_le

/-- info: 'MonoidProduct.Certificates.extensionLetter_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.extensionLetter_none

/-- info: 'MonoidProduct.Certificates.extensionLetter_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.extensionLetter_some

/-- info: 'MonoidProduct.Certificates.prod_extensionLetter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.prod_extensionLetter

/-- info: 'MonoidProduct.Certificates.prod_univ_extensionLetter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.prod_univ_extensionLetter

/-- info: 'MonoidProduct.Certificates.readout_prod_extensionLetter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.readout_prod_extensionLetter

/--
info: 'MonoidProduct.Certificates.hasStrongCertificateBound_of_isBreadthBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.hasStrongCertificateBound_of_isBreadthBound

/--
info: 'MonoidProduct.Certificates.isBreadthBound_of_hasStrongCertificateBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.isBreadthBound_of_hasStrongCertificateBound

/--
info: 'MonoidProduct.Certificates.isBreadthBound_id_of_hasStrongCertificateBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.isBreadthBound_id_of_hasStrongCertificateBound

/--
info: 'MonoidProduct.Certificates.isBreadthBound_extensionLetter_of_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.isBreadthBound_extensionLetter_of_id

/--
info: 'MonoidProduct.Certificates.isBreadthBound_extensionLetter_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.isBreadthBound_extensionLetter_iff

/-- info: 'MonoidProduct.Certificates.isBreadthBound_id_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.isBreadthBound_id_iff

/-- info: 'MonoidProduct.Certificates.ExtensionMonoid.mk_eq_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionMonoid.mk_eq_mk

/-- info: 'MonoidProduct.Certificates.ExtensionMonoid.mk_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionMonoid.mk_surjective

/-- info: 'MonoidProduct.Certificates.ExtensionMonoid.ind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionMonoid.ind

/-- info: 'MonoidProduct.Certificates.ExtensionMonoid.readout_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionMonoid.readout_mk

/-- info: 'MonoidProduct.Certificates.ExtensionMonoid.one_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionMonoid.one_def

/-- info: 'MonoidProduct.Certificates.ExtensionMonoid.mk_mul_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionMonoid.mk_mul_mk

/-- info: 'MonoidProduct.Certificates.ExtensionMonoid.mk_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionMonoid.mk_empty

/-- info: 'MonoidProduct.Certificates.ExtensionMonoid.mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionMonoid.mul_self

/-- info: 'MonoidProduct.Certificates.ExtensionMonoid.prod_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Certificates.ExtensionMonoid.prod_mk

/--
info: 'MonoidProduct.Certificates.card_extensionMonoid_le_sum_choose_of_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.card_extensionMonoid_le_sum_choose_of_bound

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

/-- info: 'MonoidProduct.Matroid.extensionEquiv_greedy_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.extensionEquiv_greedy_iff

/-- info: 'MonoidProduct.Matroid.greedy_strongCertificateSize_eq_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.greedy_strongCertificateSize_eq_rank

/-- info: 'MonoidProduct.Matroid.extensionMonoidGreedyMulEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.extensionMonoidGreedyMulEquiv

/--
info: 'MonoidProduct.Matroid.matroidBasisRecords_qQuery_le_min_sqrt_of_certificates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Matroid.matroidBasisRecords_qQuery_le_min_sqrt_of_certificates

/--
info: 'MonoidProduct.Matroid.matroidBasisIndices_qQuery_le_min_sqrt_of_certificates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Matroid.matroidBasisIndices_qQuery_le_min_sqrt_of_certificates

/--
info: 'MonoidProduct.Matroid.matroidBasisRecords_qQuery_eq_zero_of_certificates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Matroid.matroidBasisRecords_qQuery_eq_zero_of_certificates

/-- info: 'MonoidProduct.Matroid.greedy_union_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.greedy_union_congr

/-- info: 'MonoidProduct.Matroid.greedy_isStrongCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.greedy_isStrongCertificate

/-- info: 'MonoidProduct.Matroid.hasStrongCertificateBound_greedy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.hasStrongCertificateBound_greedy

/-- info: 'MonoidProduct.Matroid.greedy_strongCertificateSize_le_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.greedy_strongCertificateSize_le_rank

/-- info: 'MonoidProduct.Matroid.extensionMonoidGreedyMulEquiv_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.extensionMonoidGreedyMulEquiv_mk

/-- info: 'MonoidProduct.Matroid.val_extensionMonoidGreedyMulEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.val_extensionMonoidGreedyMulEquiv

/--
info: 'MonoidProduct.Matroid.extensionMonoidGreedyMulEquiv_extensionLetter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Matroid.extensionMonoidGreedyMulEquiv_extensionLetter

/-- info: 'MonoidProduct.Matroid.basisRecords_isStrongCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.basisRecords_isStrongCertificate

/--
info: 'MonoidProduct.Matroid.hasStrongCertificateBound_recordMatroid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Matroid.hasStrongCertificateBound_recordMatroid

/--
info: 'MonoidProduct.Matroid.recordMatroid_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Matroid.recordMatroid_strongCertificateSize_le

/-- info: 'MonoidProduct.Matroid.encodedSet_tagEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Matroid.encodedSet_tagEncoding

/-! ## Graph properties with small certificates (Section 6, `sec:graph-certificates`) -/

/--
info: 'MonoidProduct.Certificates.hasStrongCertificateBound_of_sparseYes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.hasStrongCertificateBound_of_sparseYes

/--
info: 'MonoidProduct.Certificates.sparseYes_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.sparseYes_strongCertificateSize_le

/--
info: 'MonoidProduct.Certificates.hasStrongCertificateBound_min_of_sparseYes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.hasStrongCertificateBound_min_of_sparseYes

/-- info: 'MonoidProduct.Graph.card_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_edge

/-- info: 'MonoidProduct.Graph.toGraph_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_adj

/-- info: 'MonoidProduct.Graph.mem_connectedComponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_connectedComponents

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_connectedComponents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_connectedComponents

/--
info: 'MonoidProduct.Graph.connectedComponents_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectedComponents_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.connectivity_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectivity_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.hasStrongCertificateBound_isConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_isConnected

/-- info: 'MonoidProduct.Graph.stConnectivity_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.stConnectivity_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.hasStrongCertificateBound_isSTConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_isSTConnected

/-- info: 'MonoidProduct.Graph.mem_twoColorings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_twoColorings

/-- info: 'MonoidProduct.Graph.hasStrongCertificateBound_twoColorings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_twoColorings

/-- info: 'MonoidProduct.Graph.twoColorings_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.bipartite_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bipartite_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.hasStrongCertificateBound_isBipartite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_isBipartite

/--
info: 'MonoidProduct.Graph.properTwoColoring_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.properTwoColoring_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_properTwoColoring' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_properTwoColoring

/-- info: 'MonoidProduct.Graph.isAcyclic_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isAcyclic_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.hasStrongCertificateBound_isAcyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_isAcyclic

/-- info: 'MonoidProduct.Graph.cycle_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycle_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.hasStrongCertificateBound_hasCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_hasCycle

/-- info: 'MonoidProduct.Graph.sparseYes_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sparseYes_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.hasStrongCertificateBound_of_sparseYes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_of_sparseYes

/-- info: 'MonoidProduct.Graph.mem_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_pairs

/-- info: 'MonoidProduct.Graph.coe_mem_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.coe_mem_pairs

/-- info: 'MonoidProduct.Graph.card_pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_pairs

/-- info: 'MonoidProduct.Graph.edgeSet_toGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeSet_toGraph

/-- info: 'MonoidProduct.Graph.coe_mem_edgeSet_toGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.coe_mem_edgeSet_toGraph

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_toGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_toGraph

/-- info: 'MonoidProduct.Graph.toGraph_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_mono

/-- info: 'MonoidProduct.Graph.toGraph_le_toGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_le_toGraph

/-- info: 'MonoidProduct.Graph.toGraph_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_injective

/-- info: 'MonoidProduct.Graph.toGraph_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_empty

/-- info: 'MonoidProduct.Graph.toGraph_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_singleton

/-- info: 'MonoidProduct.Graph.toGraph_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_union

/-- info: 'MonoidProduct.Graph.toGraph_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_sdiff

/-- info: 'MonoidProduct.Graph.toGraph_sdiff_eq_deleteEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_sdiff_eq_deleteEdges

/-- info: 'MonoidProduct.Graph.toGraph_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_insert

/-- info: 'MonoidProduct.Graph.mem_ofGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_ofGraph

/-- info: 'MonoidProduct.Graph.toGraph_ofGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_ofGraph

/-- info: 'MonoidProduct.Graph.ofGraph_toGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ofGraph_toGraph

/-- info: 'MonoidProduct.Graph.toGraph_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_univ

/-- info: 'MonoidProduct.Graph.card_le_of_isAcyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_le_of_isAcyclic

/-- info: 'MonoidProduct.Graph.graphicMatroid_indep_pairs_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.graphicMatroid_indep_pairs_iff

/-- info: 'MonoidProduct.Graph.exists_spanningForest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_spanningForest

/-- info: 'MonoidProduct.Graph.connectedComponents_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectedComponents_eq_iff

/-- info: 'MonoidProduct.Graph.reachable_union_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_union_of

/-- info: 'MonoidProduct.Graph.connectedComponents_union_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectedComponents_union_congr

/-- info: 'MonoidProduct.Graph.extensionEquiv_connectedComponents_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.extensionEquiv_connectedComponents_iff

/-- info: 'MonoidProduct.Graph.isStrongCertificate_connectedComponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isStrongCertificate_connectedComponents

/-- info: 'MonoidProduct.Graph.isConnected_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isConnected_eq_true_iff

/-- info: 'MonoidProduct.Graph.isSTConnected_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isSTConnected_eq_true_iff

/--
info: 'MonoidProduct.Graph.isConnected_eq_true_iff_connectedComponents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.isConnected_eq_true_iff_connectedComponents

/-- info: 'MonoidProduct.Graph.eq_iff_eq_of_reachable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eq_iff_eq_of_reachable

/-- info: 'MonoidProduct.Graph.mem_twoColorings_iff_exists_coloring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_twoColorings_iff_exists_coloring

/-- info: 'MonoidProduct.Graph.twoColorings_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_union

/-- info: 'MonoidProduct.Graph.twoColorings_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_anti

/-- info: 'MonoidProduct.Graph.twoColorings_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_nonempty_iff

/-- info: 'MonoidProduct.Graph.extensionEquiv_twoColorings_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.extensionEquiv_twoColorings_iff

/-- info: 'MonoidProduct.Graph.twoColorings_eq_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_eq_of_reachable

/-- info: 'MonoidProduct.Graph.twoColorings_insert_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_insert_eq_empty

/-- info: 'MonoidProduct.Graph.isBipartite_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isBipartite_eq_true_iff

/-- info: 'MonoidProduct.Graph.chooseColoring_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chooseColoring_mem

/-- info: 'MonoidProduct.Graph.chooseColoring_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chooseColoring_eq_none_iff

/-- info: 'MonoidProduct.Graph.properTwoColoring_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.properTwoColoring_spec

/-- info: 'MonoidProduct.Graph.properTwoColoring_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.properTwoColoring_eq_none_iff

/-- info: 'MonoidProduct.Graph.isAcyclic_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isAcyclic_eq_true_iff

/-- info: 'MonoidProduct.Graph.hasCycle_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasCycle_eq_true_iff

/-- info: 'MonoidProduct.Graph.hasCycle_eq_not_isAcyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasCycle_eq_not_isAcyclic

/-! ## Graph query models (Section 6, `sec:graph-certificates`, `eq:graph-model-comparison`) -/

/-- info: 'MonoidProduct.qQueryOn_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQueryOn_reindex

/-- info: 'MonoidProduct.qQuery_comp_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQuery_comp_reindex

/-- info: 'MonoidProduct.qQueryOn_comp_eq_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQueryOn_comp_eq_of_surjective

/-- info: 'MonoidProduct.qQueryOn_positionAlphabetMap_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.qQueryOn_positionAlphabetMap_le

/-- info: 'MonoidProduct.Graph.qQuery_recordSet_eq_qList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qQuery_recordSet_eq_qList

/-- info: 'MonoidProduct.Graph.qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qList_le

/-- info: 'MonoidProduct.Graph.mem_matrixGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_matrixGraph

/-- info: 'MonoidProduct.Graph.matrixGraph_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.matrixGraph_indicator

/-- info: 'MonoidProduct.Graph.matrixGraph_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.matrixGraph_injective

/-- info: 'MonoidProduct.Graph.qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le

/-- info: 'MonoidProduct.Graph.matrixGraph_eq_recordSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.matrixGraph_eq_recordSet

/-- info: 'MonoidProduct.Graph.adjGraph_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.adjGraph_adj

/-- info: 'MonoidProduct.Graph.degree_toGraph_adjGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.degree_toGraph_adjGraph

/-- info: 'MonoidProduct.Graph.sum_deg_eq_two_mul_card_adjGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sum_deg_eq_two_mul_card_adjGraph

/-- info: 'MonoidProduct.Graph.exists_adjArray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_adjArray

/-- info: 'MonoidProduct.Graph.qAdj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdj_le

/-- info: 'MonoidProduct.Graph.qAdj_le_qAdjEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdj_le_qAdjEdges

/-- info: 'MonoidProduct.Graph.qAdjEdges_le_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdjEdges_le_of_forall

/-- info: 'MonoidProduct.Graph.qMatrix_le_two_mul_qList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le_two_mul_qList

/-- info: 'MonoidProduct.Graph.qAdj_le_two_mul_qList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdj_le_two_mul_qList

/-- info: 'MonoidProduct.Graph.qAdjEdges_le_two_mul_qList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdjEdges_le_two_mul_qList

/-- info: 'MonoidProduct.Graph.qList_le_min_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qList_le_min_sqrt

/-- info: 'MonoidProduct.Graph.qMatrix_le_min_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le_min_sqrt

/-- info: 'MonoidProduct.Graph.qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.qAdj_le_min_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdj_le_min_sqrt

/-- info: 'MonoidProduct.Graph.qAdjEdges_le_min_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdjEdges_le_min_sqrt

/-- info: 'MonoidProduct.Graph.qAdjEdges_le_mul_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdjEdges_le_mul_min

/-- info: 'MonoidProduct.Graph.qList_le_min_sqrt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qList_le_min_sqrt_of_le

/-- info: 'MonoidProduct.Graph.qMatrix_le_min_sqrt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le_min_sqrt_of_le

/-- info: 'MonoidProduct.Graph.qMatrix_le_mul_sqrt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le_mul_sqrt_of_le

/-- info: 'MonoidProduct.Graph.qAdj_le_min_sqrt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdj_le_min_sqrt_of_le

/-- info: 'MonoidProduct.Graph.qAdjEdges_le_min_sqrt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qAdjEdges_le_min_sqrt_of_le

/-- info: 'MonoidProduct.Graph.connectedComponents_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectedComponents_qList_le

/-- info: 'MonoidProduct.Graph.connectedComponents_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectedComponents_qMatrix_le

/-- info: 'MonoidProduct.Graph.connectedComponents_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectedComponents_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.connectedComponents_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectedComponents_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.connectivity_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectivity_qList_le

/-- info: 'MonoidProduct.Graph.connectivity_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectivity_qMatrix_le

/-- info: 'MonoidProduct.Graph.connectivity_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectivity_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.connectivity_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectivity_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.stConnectivity_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.stConnectivity_qList_le

/-- info: 'MonoidProduct.Graph.stConnectivity_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.stConnectivity_qMatrix_le

/-- info: 'MonoidProduct.Graph.stConnectivity_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.stConnectivity_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.stConnectivity_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.stConnectivity_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.twoColorings_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_qList_le

/-- info: 'MonoidProduct.Graph.twoColorings_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_qMatrix_le

/-- info: 'MonoidProduct.Graph.twoColorings_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.twoColorings_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twoColorings_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.bipartite_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bipartite_qList_le

/-- info: 'MonoidProduct.Graph.bipartite_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bipartite_qMatrix_le

/-- info: 'MonoidProduct.Graph.bipartite_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bipartite_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.bipartite_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bipartite_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.properTwoColoring_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.properTwoColoring_qList_le

/-- info: 'MonoidProduct.Graph.properTwoColoring_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.properTwoColoring_qMatrix_le

/-- info: 'MonoidProduct.Graph.properTwoColoring_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.properTwoColoring_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.properTwoColoring_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.properTwoColoring_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.cycle_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycle_qList_le

/-- info: 'MonoidProduct.Graph.cycle_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycle_qMatrix_le

/-- info: 'MonoidProduct.Graph.cycle_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycle_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.cycle_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycle_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.sparseYes_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sparseYes_qList_le

/-- info: 'MonoidProduct.Graph.sparseYes_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sparseYes_qMatrix_le

/-- info: 'MonoidProduct.Graph.sparseYes_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sparseYes_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.sparseYes_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sparseYes_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.recordSet_comp_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.recordSet_comp_equiv

/-- info: 'MonoidProduct.Graph.card_adjPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_adjPos

/-- info: 'MonoidProduct.Graph.adjEdge_eq_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.adjEdge_eq_some_iff

/-- info: 'MonoidProduct.Graph.mem_adjGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_adjGraph

/-- info: 'MonoidProduct.indexRelabel_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.indexRelabel_apply

/-- info: 'MonoidProduct.oracleMap_indexRelabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.oracleMap_indexRelabel

/-- info: 'MonoidProduct.oracleMap_indexRelabel_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.oracleMap_indexRelabel_symm

/-- info: 'MonoidProduct.reindexAlg_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.reindexAlg_state

/-- info: 'MonoidProduct.computesWithErrorOn_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.computesWithErrorOn_reindex

/-- info: 'MonoidProduct.queryCounts_subset_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.queryCounts_subset_reindex

/-- info: 'MonoidProduct.queryCounts_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.queryCounts_reindex

/-- info: 'MonoidProduct.queryCounts_comp_eq_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.queryCounts_comp_eq_of_surjective

/-- info: 'MonoidProduct.posLiftSwap_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posLiftSwap_self

/-- info: 'MonoidProduct.posLiftSwapMap_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posLiftSwapMap_involutive

/-- info: 'MonoidProduct.posGadget_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posGadget_snd

/-- info: 'MonoidProduct.posGadget_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posGadget_blank

/-- info: 'MonoidProduct.posLiftSwapMat_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posLiftSwapMat_mulVec_apply

/-- info: 'MonoidProduct.posLiftSwapMat_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posLiftSwapMat_mem_unitaryGroup

/-- info: 'MonoidProduct.posGadget_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posGadget_mulVec

/-- info: 'MonoidProduct.posMapAlphabet_step_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posMapAlphabet_step_even

/-- info: 'MonoidProduct.posMapAlphabet_step_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posMapAlphabet_step_odd

/-- info: 'MonoidProduct.posMapAlphabet_runUpto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.posMapAlphabet_runUpto

/-- info: 'MonoidProduct.computesWithErrorOn_posMapAlphabet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.computesWithErrorOn_posMapAlphabet

/-! ## Planarity (Section 6, `sec:graph-certificates`) -/

/-- info: 'MonoidProduct.Graph.dartReverse_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.dartReverse_apply

/-- info: 'MonoidProduct.Graph.eq_of_sameCycle_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eq_of_sameCycle_of_forall

/-- info: 'MonoidProduct.Graph.RotationSystem.face_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.face_apply

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_face

/--
info: 'MonoidProduct.Graph.RotationSystem.connectedComponentMk_fst_face' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.connectedComponentMk_fst_face

/-- info: 'MonoidProduct.Graph.RotationSystem.Face.component_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.Face.component_mk

/-- info: 'MonoidProduct.Graph.ncard_dartsIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_dartsIn_eq

/-- info: 'MonoidProduct.Graph.ncard_componentEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_componentEdges_le

/-- info: 'MonoidProduct.Graph.componentEdges_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.componentEdges_nonempty

/-- info: 'MonoidProduct.Graph.one_le_ncard_supp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.one_le_ncard_supp

/-- info: 'MonoidProduct.Graph.RotationSystem.face_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.face_ne

/-- info: 'MonoidProduct.Graph.RotationSystem.face_face_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.face_face_ne

/-- info: 'MonoidProduct.Graph.RotationSystem.three_le_ncard_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.three_le_ncard_sameCycle

/-- info: 'MonoidProduct.Graph.RotationSystem.four_le_ncard_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.four_le_ncard_sameCycle

/-- info: 'MonoidProduct.Graph.RotationSystem.mul_ncard_facesIn_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.mul_ncard_facesIn_le

/--
info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.mul_le_of_faces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.mul_le_of_faces

/-- info: 'MonoidProduct.Graph.ncard_componentEdges_lt_of_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_componentEdges_lt_of_le_two

/-- info: 'MonoidProduct.Graph.mul_ncard_edgeSet_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mul_ncard_edgeSet_add_le

/-- info: 'MonoidProduct.Graph.IsPlanar.ncard_edgeSet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.ncard_edgeSet_le

/-- info: 'MonoidProduct.Graph.IsPlanar.ncard_edgeSet_le_of_colorable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.ncard_edgeSet_le_of_colorable

/-- info: 'MonoidProduct.Graph.isPlanar_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_bot

/-- info: 'MonoidProduct.Graph.k4_face_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.k4_face_three

/-- info: 'MonoidProduct.Graph.k4_sameCycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.k4_sameCycle_iff

/-- info: 'MonoidProduct.Graph.natCard_k4Face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_k4Face

/-- info: 'MonoidProduct.Graph.isPlanar_top_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_top_four

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_top_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_top_four

/-- info: 'MonoidProduct.Graph.not_isPlanar_top_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.not_isPlanar_top_five

/--
info: 'MonoidProduct.Graph.ncard_edgeSet_completeBipartite_three_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_completeBipartite_three_three

/--
info: 'MonoidProduct.Graph.not_isPlanar_completeBipartite_three_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.not_isPlanar_completeBipartite_three_three

/-- info: 'MonoidProduct.Graph.isPlanar_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_eq_true_iff

/-- info: 'MonoidProduct.Graph.card_le_of_isPlanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_le_of_isPlanar

/-- info: 'MonoidProduct.Graph.planarity_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.planarity_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.hasStrongCertificateBound_isPlanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_isPlanar

/-- info: 'MonoidProduct.Graph.planarity_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.planarity_qList_le

/-- info: 'MonoidProduct.Graph.planarity_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.planarity_qMatrix_le

/-- info: 'MonoidProduct.Graph.planarity_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.planarity_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.planarity_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.planarity_qAdjEdges_le

/-! ## Planar subgraphs: Euler's inequality and edge deletion -/

/-- info: 'MonoidProduct.Graph.natCard_quotient_eq_add_one_of_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_quotient_eq_add_one_of_join

/-- info: 'MonoidProduct.Graph.natCard_quotient_eq_of_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_quotient_eq_of_join

/-- info: 'MonoidProduct.Graph.pow_apply_eq_of_forall_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.pow_apply_eq_of_forall_lt

/-- info: 'MonoidProduct.Graph.pow_apply_eq_pow_mod_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.pow_apply_eq_pow_mod_apply

/-- info: 'MonoidProduct.Graph.exists_first_pow_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_first_pow_mem

/-- info: 'MonoidProduct.Graph.exists_pos_pow_apply_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_pos_pow_apply_eq_self

/-- info: 'MonoidProduct.Graph.sameCycle_iff_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_iff_of_agree

/-- info: 'MonoidProduct.Graph.sameCycle_or_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_or_of_agree

/-- info: 'MonoidProduct.Graph.mul_swap_apply_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mul_swap_apply_of_ne

/-- info: 'MonoidProduct.Graph.pow_mul_swap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.pow_mul_swap_apply

/-- info: 'MonoidProduct.Graph.sameCycle_mul_swap_of_not_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_mul_swap_of_not_sameCycle

/-- info: 'MonoidProduct.Graph.not_sameCycle_mul_swap_of_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.not_sameCycle_mul_swap_of_sameCycle

/-- info: 'MonoidProduct.Graph.sameCycle_of_mul_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_of_mul_swap

/-- info: 'MonoidProduct.Graph.sameCycle_iff_mul_swap_of_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_iff_mul_swap_of_sameCycle

/-- info: 'MonoidProduct.Graph.sameCycle_mul_swap_iff_of_not_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_mul_swap_iff_of_not_sameCycle

/-- info: 'MonoidProduct.Graph.cycleCount_mul_swap_of_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_mul_swap_of_sameCycle

/-- info: 'MonoidProduct.Graph.cycleCount_mul_swap_of_not_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_mul_swap_of_not_sameCycle

/-- info: 'MonoidProduct.Graph.cycleCount_eq_add_of_sameCycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_eq_add_of_sameCycle_iff

/-- info: 'MonoidProduct.Graph.sameCycle_permCongr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_permCongr

/-- info: 'MonoidProduct.Graph.cycleCount_permCongr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_permCongr

/-- info: 'MonoidProduct.Graph.bypass_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bypass_apply_self

/-- info: 'MonoidProduct.Graph.bypass_apply_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bypass_apply_of_ne

/-- info: 'MonoidProduct.Graph.bypass_of_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bypass_of_apply_eq

/-- info: 'MonoidProduct.Graph.bypass_eq_mul_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bypass_eq_mul_swap

/-- info: 'MonoidProduct.Graph.apply_bypass_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.apply_bypass_eq

/-- info: 'MonoidProduct.Graph.sameCycle_bypass_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_bypass_iff

/-- info: 'MonoidProduct.Graph.cycleCount_bypass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_bypass

/-- info: 'MonoidProduct.Graph.bypass_apply_ne_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bypass_apply_ne_iff

/-- info: 'MonoidProduct.Graph.eraseOne_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eraseOne_apply

/-- info: 'MonoidProduct.Graph.sameCycle_eraseOne_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_eraseOne_iff

/-- info: 'MonoidProduct.Graph.cycleCount_subtypePerm_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_subtypePerm_add

/-- info: 'MonoidProduct.Graph.cycleCount_eraseOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_eraseOne

/-- info: 'MonoidProduct.Graph.bypass_bypass_apply_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bypass_bypass_apply_left

/-- info: 'MonoidProduct.Graph.bypass_bypass_apply_ne_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bypass_bypass_apply_ne_iff

/-- info: 'MonoidProduct.Graph.eraseTwo_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eraseTwo_apply

/-- info: 'MonoidProduct.Graph.eraseOne_eraseOne_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eraseOne_eraseOne_apply

/-- info: 'MonoidProduct.Graph.sameCycle_eraseTwo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_eraseTwo_iff

/-- info: 'MonoidProduct.Graph.cycleCount_eraseTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_eraseTwo

/-- info: 'MonoidProduct.Graph.cycleCount_eraseTwo_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_eraseTwo_add

/-- info: 'MonoidProduct.Graph.bypass_permCongr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bypass_permCongr

/-- info: 'MonoidProduct.Graph.eraseOne_permCongr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eraseOne_permCongr

/-- info: 'MonoidProduct.Graph.finite_dart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.finite_dart

/-- info: 'MonoidProduct.Graph.dart_edge_ne_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.dart_edge_ne_iff

/-- info: 'MonoidProduct.Graph.RotationSystem.rot_ne_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.rot_ne_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.rot_symm_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.rot_symm_ne

/-- info: 'MonoidProduct.Graph.RotationSystem.rot_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.rot_eq_self_iff

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_bypass_bypass_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_bypass_bypass_rot

/-- info: 'MonoidProduct.Graph.RotationSystem.bypass_bypass_rot_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.bypass_bypass_rot_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.deleteEdge_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.deleteEdge_face

/--
info: 'MonoidProduct.Graph.RotationSystem.natCard_face_deleteEdge_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.natCard_face_deleteEdge_add

/--
info: 'MonoidProduct.Graph.RotationSystem.fst_mem_isolatedVerts_deleteEdges_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_mem_isolatedVerts_deleteEdges_iff

/--
info: 'MonoidProduct.Graph.RotationSystem.mem_isolatedVerts_deleteEdges_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.mem_isolatedVerts_deleteEdges_iff

/--
info: 'MonoidProduct.Graph.RotationSystem.ncard_isolatedVerts_deleteEdges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.ncard_isolatedVerts_deleteEdges

/--
info: 'MonoidProduct.Graph.RotationSystem.completedFaceCount_deleteEdge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.completedFaceCount_deleteEdge

/--
info: 'MonoidProduct.Graph.RotationSystem.completedFaceCount_deleteEdge_of_sameCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.completedFaceCount_deleteEdge_of_sameCycle

/--
info: 'MonoidProduct.Graph.RotationSystem.completedFaceCount_deleteEdge_of_not_sameCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.completedFaceCount_deleteEdge_of_not_sameCycle

/-- info: 'MonoidProduct.Graph.reachable_iff_deleteEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_iff_deleteEdges

/--
info: 'MonoidProduct.Graph.natCard_connectedComponent_deleteEdges_of_isBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_connectedComponent_deleteEdges_of_isBridge

/--
info: 'MonoidProduct.Graph.natCard_connectedComponent_deleteEdges_of_not_isBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_connectedComponent_deleteEdges_of_not_isBridge

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_deleteEdges_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_deleteEdges_add_one

/--
info: 'MonoidProduct.Graph.RotationSystem.sameCycle_face_of_isBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_face_of_isBridge

/--
info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_deleteEdge_of_isBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_deleteEdge_of_isBridge

/--
info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_deleteEdge_of_not_sameCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_deleteEdge_of_not_sameCycle

/--
info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_deleteEdge_of_sameCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_deleteEdge_of_sameCycle

/--
info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_deleteEdge_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_deleteEdge_le

/--
info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_eq_zero_of_edgeSet_eq_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_eq_zero_of_edgeSet_eq_empty

/-- info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_nonneg

/-- info: 'MonoidProduct.Graph.sum_ncard_inter_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sum_ncard_inter_preimage

/-- info: 'MonoidProduct.Graph.eq_of_reachable_of_mem_isolatedVerts' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eq_of_reachable_of_mem_isolatedVerts

/-- info: 'MonoidProduct.Graph.isolatedVerts_inter_supp_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isolatedVerts_inter_supp_eq_empty

/-- info: 'MonoidProduct.Graph.supp_subset_isolatedVerts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.supp_subset_isolatedVerts

/-- info: 'MonoidProduct.Graph.RotationSystem.facesIn_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.facesIn_eq_empty

/--
info: 'MonoidProduct.Graph.RotationSystem.componentDefect_of_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.componentDefect_of_nonempty

/--
info: 'MonoidProduct.Graph.RotationSystem.componentDefect_of_not_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.componentDefect_of_not_nonempty

/-- info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_eq_finsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_eq_finsum

/--
info: 'MonoidProduct.Graph.RotationSystem.isSpherical_iff_forall_componentDefect_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.isSpherical_iff_forall_componentDefect_eq_zero

/-- info: 'MonoidProduct.Graph.exists_reachable_induce_of_walk_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_reachable_induce_of_walk_closed

/-- info: 'MonoidProduct.Graph.induceComponentMap_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.induceComponentMap_mk

/-- info: 'MonoidProduct.Graph.supp_induceComponentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.supp_induceComponentMap

/-- info: 'MonoidProduct.Graph.componentEdges_induceComponentMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.componentEdges_induceComponentMap

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_face_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_face_mem_iff

/-- info: 'MonoidProduct.Graph.RotationSystem.restrict_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.restrict_face

/--
info: 'MonoidProduct.Graph.RotationSystem.sameCycle_restrict_face_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_restrict_face_iff

/--
info: 'MonoidProduct.Graph.RotationSystem.restrictFaceMap_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.restrictFaceMap_injective

/--
info: 'MonoidProduct.Graph.RotationSystem.facesIn_induceComponentMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.facesIn_induceComponentMap

/-- info: 'MonoidProduct.Graph.RotationSystem.componentDefect_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.componentDefect_restrict

/-- info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.restrict

/-- info: 'MonoidProduct.Graph.RotationSystem.componentDefect_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.componentDefect_nonneg

/--
info: 'MonoidProduct.Graph.RotationSystem.ncard_supp_add_ncard_facesIn_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.ncard_supp_add_ncard_facesIn_le

/--
info: 'MonoidProduct.Graph.RotationSystem.isSpherical_iff_eulerDefect_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.isSpherical_iff_eulerDefect_eq_zero

/-- info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.deleteEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.deleteEdge

/--
info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.sameCycle_face_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.sameCycle_face_iff

/--
info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_eq_zero_of_isAcyclic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_eq_zero_of_isAcyclic

/-- info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.of_isAcyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.of_isAcyclic

/-- info: 'MonoidProduct.Graph.IsPlanar.deleteEdges_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.deleteEdges_singleton

/-- info: 'MonoidProduct.Graph.IsPlanar.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.mono

/-- info: 'MonoidProduct.Graph.IsPlanar.deleteEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.deleteEdges

/-- info: 'MonoidProduct.Graph.IsPlanar.induce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.induce

/-- info: 'MonoidProduct.Graph.isSpherical_k4Rotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isSpherical_k4Rotation

/-! ## Planar minors: contraction and the easy direction of Wagner's theorem -/

/-- info: 'MonoidProduct.Graph.contractVertex_of_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractVertex_of_ne

/-- info: 'MonoidProduct.Graph.contractVertex_self' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractVertex_self

/-- info: 'MonoidProduct.Graph.contractVertex_val' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractVertex_val

/-- info: 'MonoidProduct.Graph.val_contractVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.val_contractVertex

/-- info: 'MonoidProduct.Graph.contractVertex_eq_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractVertex_eq_iff

/-- info: 'MonoidProduct.Graph.contractEdge_adj_contractVertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractEdge_adj_contractVertex

/-- info: 'MonoidProduct.Graph.contractVertex_eq_or_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractVertex_eq_or_adj

/-- info: 'MonoidProduct.Graph.reachable_contractVertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_contractVertex

/-- info: 'MonoidProduct.Graph.reachable_of_reachable_contractEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_of_reachable_contractEdge

/-- info: 'MonoidProduct.Graph.reachable_val_contractVertex' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_val_contractVertex

/-- info: 'MonoidProduct.Graph.natCard_connectedComponent_contractEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_connectedComponent_contractEdge

/-- info: 'MonoidProduct.Graph.IsConnectedSet.image_of_eq_or_adj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsConnectedSet.image_of_eq_or_adj

/-- info: 'MonoidProduct.Graph.IsConnectedSet.exists_adj_of_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsConnectedSet.exists_adj_of_ne

/-- info: 'MonoidProduct.Graph.MinorModel.branch_contractEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.MinorModel.branch_contractEdge

/-- info: 'MonoidProduct.Graph.natCard_subtype_ne_and_ne_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_subtype_ne_and_ne_add_two

/-- info: 'MonoidProduct.Graph.natCard_subtype_ne_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_subtype_ne_add_one

/-- info: 'MonoidProduct.Graph.two_mul_ncard_edgeSet_eq_natCard_dart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.two_mul_ncard_edgeSet_eq_natCard_dart

/-- info: 'MonoidProduct.Graph.contractEdge_adj_of_dart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractEdge_adj_of_dart

/-- info: 'MonoidProduct.Graph.contractDart_survivorSymm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractDart_survivorSymm

/-- info: 'MonoidProduct.Graph.contractDart_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractDart_surjective

/-- info: 'MonoidProduct.Graph.contractDart_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractDart_injective

/-- info: 'MonoidProduct.Graph.contractDartEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractDartEquiv_apply

/--
info: 'MonoidProduct.Graph.RotationSystem.contractVertex_fst_rot_mul_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.contractVertex_fst_rot_mul_swap

/-- info: 'MonoidProduct.Graph.RotationSystem.contract_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.contract_rot

/--
info: 'MonoidProduct.Graph.RotationSystem.bypass_bypass_rot_mul_swap_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.bypass_bypass_rot_mul_swap_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.contract_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.contract_face

/--
info: 'MonoidProduct.Graph.RotationSystem.natCard_face_contract_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.natCard_face_contract_add

/-- info: 'MonoidProduct.Graph.RotationSystem.rot_eq_self_and_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.rot_eq_self_and_iff

/--
info: 'MonoidProduct.Graph.RotationSystem.ncard_isolatedVerts_contractEdge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.ncard_isolatedVerts_contractEdge

/--
info: 'MonoidProduct.Graph.RotationSystem.natCard_contractEdge_vertices_add_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.natCard_contractEdge_vertices_add_one

/--
info: 'MonoidProduct.Graph.RotationSystem.ncard_edgeSet_contractEdge_add_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.ncard_edgeSet_contractEdge_add_one

/--
info: 'MonoidProduct.Graph.RotationSystem.completedFaceCount_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.completedFaceCount_contract

/-- info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_contract

/-- info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.contract

/-- info: 'MonoidProduct.Graph.deleteEdges_thinEdges_adj_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.deleteEdges_thinEdges_adj_iff

/-- info: 'MonoidProduct.Graph.deleteEdges_thinEdges_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.deleteEdges_thinEdges_adj

/--
info: 'MonoidProduct.Graph.disjoint_neighborSet_deleteEdges_thinEdges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.disjoint_neighborSet_deleteEdges_thinEdges

/-- info: 'MonoidProduct.Graph.contractEdge_deleteEdges_thinEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractEdge_deleteEdges_thinEdges

/-- info: 'MonoidProduct.Graph.IsPlanar.contractEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.contractEdge

/-- info: 'MonoidProduct.Graph.IsPlanar.of_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.of_injective

/-- info: 'MonoidProduct.Graph.IsPlanar.of_minor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.of_minor

/-- info: 'MonoidProduct.Graph.IsPlanar.not_isMinor_top_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.not_isMinor_top_five

/--
info: 'MonoidProduct.Graph.IsPlanar.not_isMinor_completeBipartite_three_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.not_isMinor_completeBipartite_three_three

/-- info: 'MonoidProduct.Graph.IsPlanar.wagner_easy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.wagner_easy

/-- info: 'MonoidProduct.Graph.isMinorClosed_isPlanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinorClosed_isPlanar

/-- info: 'MonoidProduct.Graph.isProperClass_isPlanar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isProperClass_isPlanar

/-! ## Connectivity, separations and cyclic arcs -/

/-- info: 'MonoidProduct.Graph.IsConnectedSet.insert_of_adj' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsConnectedSet.insert_of_adj

/-- info: 'MonoidProduct.Graph.isConnectedSet_of_isChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isConnectedSet_of_isChain

/-- info: 'MonoidProduct.Graph.rotate_eq_rotate_of_getElem?_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.rotate_eq_rotate_of_getElem?_zero

/-- info: 'MonoidProduct.Graph.take_rotate_of_add_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.take_rotate_of_add_le

/-- info: 'MonoidProduct.Graph.mem_take_iff_idxOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_take_iff_idxOf_lt

/-- info: 'MonoidProduct.Graph.length_startAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.length_startAt

/-- info: 'MonoidProduct.Graph.mem_startAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_startAt

/-- info: 'MonoidProduct.Graph.nodup_startAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.nodup_startAt

/-- info: 'MonoidProduct.Graph.getElem?_startAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.getElem?_startAt_zero

/-- info: 'MonoidProduct.Graph.startAt_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.startAt_rotate

/-- info: 'MonoidProduct.Graph.cycDist_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_rotate

/-- info: 'MonoidProduct.Graph.arc_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.arc_rotate

/-- info: 'MonoidProduct.Graph.closedArc_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.closedArc_rotate

/-- info: 'MonoidProduct.Graph.cycDist_lt_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_lt_length

/-- info: 'MonoidProduct.Graph.getElem?_startAt_cycDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.getElem?_startAt_cycDist

/-- info: 'MonoidProduct.Graph.getElem_startAt_cycDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.getElem_startAt_cycDist

/-- info: 'MonoidProduct.Graph.cycDist_eq_of_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_eq_of_getElem?

/-- info: 'MonoidProduct.Graph.cycDist_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_self

/-- info: 'MonoidProduct.Graph.cycDist_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_eq_zero_iff

/-- info: 'MonoidProduct.Graph.cycDist_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_pos

/-- info: 'MonoidProduct.Graph.eq_of_cycDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eq_of_cycDist_eq

/-- info: 'MonoidProduct.Graph.startAt_eq_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.startAt_eq_rotate

/-- info: 'MonoidProduct.Graph.cycDist_add_cycDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_add_cycDist

/-- info: 'MonoidProduct.Graph.cycDist_add_cycDist_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_add_cycDist_of_lt

/-- info: 'MonoidProduct.Graph.cycDist_add_cycDist_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_add_cycDist_comm

/-- info: 'MonoidProduct.Graph.mem_arc_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_arc_iff

/-- info: 'MonoidProduct.Graph.mem_closedArc_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_closedArc_iff

/-- info: 'MonoidProduct.Graph.nodup_arc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.nodup_arc

/-- info: 'MonoidProduct.Graph.nodup_closedArc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.nodup_closedArc

/-- info: 'MonoidProduct.Graph.mem_of_mem_arc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_of_mem_arc

/-- info: 'MonoidProduct.Graph.mem_of_mem_closedArc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_of_mem_closedArc

/-- info: 'MonoidProduct.Graph.left_mem_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.left_mem_arc

/-- info: 'MonoidProduct.Graph.right_not_mem_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.right_not_mem_arc

/-- info: 'MonoidProduct.Graph.arc_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.arc_ne_nil

/-- info: 'MonoidProduct.Graph.left_mem_closedArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.left_mem_closedArc

/-- info: 'MonoidProduct.Graph.right_mem_closedArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.right_mem_closedArc

/-- info: 'MonoidProduct.Graph.closedArc_eq_arc_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.closedArc_eq_arc_append

/-- info: 'MonoidProduct.Graph.arc_append_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.arc_append_arc

/-- info: 'MonoidProduct.Graph.arc_append_arc_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.arc_append_arc_self

/-- info: 'MonoidProduct.Graph.disjoint_arc_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.disjoint_arc_arc

/-- info: 'MonoidProduct.Graph.disjoint_arc_arc_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.disjoint_arc_arc_self

/-- info: 'MonoidProduct.Graph.mem_arc_or_mem_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_arc_or_mem_arc

/-- info: 'MonoidProduct.Graph.arc_append_arc_append_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.arc_append_arc_append_arc

/-- info: 'MonoidProduct.Graph.arc_append_arc_append_arc_append_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.arc_append_arc_append_arc_append_arc

/-- info: 'MonoidProduct.Graph.exists_isConsecutive_mem_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_isConsecutive_mem_arc

/-- info: 'MonoidProduct.Graph.IsConsecutive.right_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsConsecutive.right_eq

/-- info: 'MonoidProduct.Graph.IsConsecutive.eq_of_mem_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsConsecutive.eq_of_mem_arc

/-- info: 'MonoidProduct.Graph.IsCycleList.rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsCycleList.rotate

/-- info: 'MonoidProduct.Graph.IsCycleList.isChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsCycleList.isChain

/-- info: 'MonoidProduct.Graph.IsCycleList.isChain_startAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsCycleList.isChain_startAt

/-- info: 'MonoidProduct.Graph.IsCycleList.isConnectedSet_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsCycleList.isConnectedSet_arc

/-- info: 'MonoidProduct.Graph.IsCycleList.isConnectedSet_closedArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsCycleList.isConnectedSet_closedArc

/-- info: 'MonoidProduct.Graph.IsCycleList.exists_mem_arc_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsCycleList.exists_mem_arc_adj

/-- info: 'MonoidProduct.Graph.NoKuratowskiMinor.of_isMinor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.NoKuratowskiMinor.of_isMinor

/-- info: 'MonoidProduct.Graph.reachable_induce_iff_restrictTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_induce_iff_restrictTo

/-- info: 'MonoidProduct.Graph.mem_of_reachable_of_forall_adj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_of_reachable_of_forall_adj

/-- info: 'MonoidProduct.Graph.isConnectedSet_setOf_reachable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isConnectedSet_setOf_reachable

/--
info: 'MonoidProduct.Graph.isVertexConnected_eq_true_iff_isKConnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.isVertexConnected_eq_true_iff_isKConnected

/-- info: 'MonoidProduct.Graph.IsKConnected.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsKConnected.mono

/-- info: 'MonoidProduct.Graph.IsKConnected.connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsKConnected.connected

/-- info: 'MonoidProduct.Graph.IsKConnected.le_ncard_neighborSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsKConnected.le_ncard_neighborSet

/-- info: 'MonoidProduct.Graph.IsKConnected.induce_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsKConnected.induce_ne

/-- info: 'MonoidProduct.Graph.exists_minimum_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_minimum_separator

/-- info: 'MonoidProduct.Graph.IsProperSeparation.symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsProperSeparation.symm

/-- info: 'MonoidProduct.Graph.IsProperSeparation.natCard_lt_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsProperSeparation.natCard_lt_left

/-- info: 'MonoidProduct.Graph.IsProperSeparation.natCard_lt_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsProperSeparation.natCard_lt_right

/-- info: 'MonoidProduct.Graph.IsProperSeparation.mem_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsProperSeparation.mem_of_reachable

/-- info: 'MonoidProduct.Graph.IsProperSeparation.not_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsProperSeparation.not_reachable

/-- info: 'MonoidProduct.Graph.exists_isProperSeparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_isProperSeparation

/-- info: 'MonoidProduct.Graph.exists_adj_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_adj_reachable

/-- info: 'MonoidProduct.Graph.isMinor_sup_edge_induce_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_sup_edge_induce_left

/-- info: 'MonoidProduct.Graph.isMinor_sup_edge_induce_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_sup_edge_induce_right

/-! ## Face walks of rotation systems -/

/-- info: 'MonoidProduct.Graph.length_orbitList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.length_orbitList

/-- info: 'MonoidProduct.Graph.getElem_orbitList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.getElem_orbitList

/-- info: 'MonoidProduct.Graph.pow_minimalPeriod_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.pow_minimalPeriod_apply

/-- info: 'MonoidProduct.Graph.pow_apply_eq_pow_mod_minimalPeriod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.pow_apply_eq_pow_mod_minimalPeriod

/-- info: 'MonoidProduct.Graph.mem_periodicPts_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_periodicPts_perm

/-- info: 'MonoidProduct.Graph.minimalPeriod_perm_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.minimalPeriod_perm_pos

/-- info: 'MonoidProduct.Graph.orbitList_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.orbitList_ne_nil

/-- info: 'MonoidProduct.Graph.nodup_orbitList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.nodup_orbitList

/-- info: 'MonoidProduct.Graph.mem_orbitList_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_orbitList_iff

/-- info: 'MonoidProduct.Graph.mem_orbitList_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_orbitList_self

/-- info: 'MonoidProduct.Graph.getElem_orbitList_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.getElem_orbitList_zero

/-- info: 'MonoidProduct.Graph.getElem_orbitList_succ_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.getElem_orbitList_succ_mod

/-- info: 'MonoidProduct.Graph.minimalPeriod_perm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.minimalPeriod_perm_apply

/-- info: 'MonoidProduct.Graph.orbitList_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.orbitList_apply

/-- info: 'MonoidProduct.Graph.orbitList_pow_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.orbitList_pow_apply

/-- info: 'MonoidProduct.Graph.isRotated_orbitList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isRotated_orbitList

/-- info: 'MonoidProduct.Graph.orbitList_eq_of_getElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.orbitList_eq_of_getElem

/-- info: 'MonoidProduct.Graph.isRotated_orbitList_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isRotated_orbitList_of_mem

/-- info: 'MonoidProduct.Graph.orbitList_permCongr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.orbitList_permCongr

/-- info: 'MonoidProduct.Graph.RotationSystem.length_faceDarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.length_faceDarts

/-- info: 'MonoidProduct.Graph.RotationSystem.length_faceWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.length_faceWalk

/-- info: 'MonoidProduct.Graph.RotationSystem.getElem_faceDarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.getElem_faceDarts

/-- info: 'MonoidProduct.Graph.RotationSystem.getElem_faceWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.getElem_faceWalk

/-- info: 'MonoidProduct.Graph.RotationSystem.getElem_faceWalk_eq_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.getElem_faceWalk_eq_fst

/-- info: 'MonoidProduct.Graph.RotationSystem.nodup_faceDarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.nodup_faceDarts

/-- info: 'MonoidProduct.Graph.RotationSystem.two_le_length_faceDarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.two_le_length_faceDarts

/-- info: 'MonoidProduct.Graph.RotationSystem.two_le_length_faceWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.two_le_length_faceWalk

/-- info: 'MonoidProduct.Graph.RotationSystem.mem_faceDarts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.mem_faceDarts_iff

/-- info: 'MonoidProduct.Graph.RotationSystem.mem_faceWalk_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.mem_faceWalk_iff

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_mem_faceWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_mem_faceWalk

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_mem_faceWalk_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_mem_faceWalk_self

/--
info: 'MonoidProduct.Graph.RotationSystem.getElem_faceDarts_succ_mod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.getElem_faceDarts_succ_mod

/-- info: 'MonoidProduct.Graph.RotationSystem.snd_getElem_faceDarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.snd_getElem_faceDarts

/-- info: 'MonoidProduct.Graph.RotationSystem.adj_getElem_faceWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.adj_getElem_faceWalk

/-- info: 'MonoidProduct.Graph.RotationSystem.isCycleList_faceWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.isCycleList_faceWalk

/-- info: 'MonoidProduct.Graph.RotationSystem.nodup_faceWalk_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.nodup_faceWalk_iff

/-- info: 'MonoidProduct.Graph.RotationSystem.faceDarts_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.faceDarts_face

/-- info: 'MonoidProduct.Graph.RotationSystem.faceWalk_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.faceWalk_face

/-- info: 'MonoidProduct.Graph.RotationSystem.isRotated_faceDarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.isRotated_faceDarts

/-- info: 'MonoidProduct.Graph.RotationSystem.isRotated_faceWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.isRotated_faceWalk

/-- info: 'MonoidProduct.Graph.RotationSystem.faceDarts_mapIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.faceDarts_mapIso

/-- info: 'MonoidProduct.Graph.RotationSystem.faceWalk_mapIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.faceWalk_mapIso

/-! ## Obstructions on a cycle: the `K₅` and `K₃,₃` models and the interval lemma -/

/-- info: 'MonoidProduct.Graph.mem_arc_iff_of_cycDist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_arc_iff_of_cycDist_le

/-- info: 'MonoidProduct.Graph.mem_arc_iff_cycDist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_arc_iff_cycDist_le

/--
info: 'MonoidProduct.Graph.exists_isConsecutive_subset_closedArc_of_cyclic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_isConsecutive_subset_closedArc_of_cyclic

/-- info: 'MonoidProduct.Graph.isMinor_top_five_of_three_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_top_five_of_three_common

/-- info: 'MonoidProduct.Graph.isMinor_top_five_of_three_common'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_top_five_of_three_common'

/--
info: 'MonoidProduct.Graph.isMinor_completeBipartite_of_alternating' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_completeBipartite_of_alternating

/-- info: 'MonoidProduct.Graph.exists_isConsecutive_subset_closedArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_isConsecutive_subset_closedArc

/-! ## A contractible edge in a `3`-connected graph -/

/-- info: 'MonoidProduct.Graph.connected_induce_contractEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connected_induce_contractEdge

/-- info: 'MonoidProduct.Graph.isKConnected_contractEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isKConnected_contractEdge

/-- info: 'MonoidProduct.Graph.isKConnected_contractEdge_three_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isKConnected_contractEdge_three_iff

/-- info: 'MonoidProduct.Graph.exists_separating_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_separating_triple

/-- info: 'MonoidProduct.Graph.setOf_reachable_subset' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.setOf_reachable_subset

/-- info: 'MonoidProduct.Graph.exists_ncard_setOf_reachable_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_ncard_setOf_reachable_lt

/-- info: 'MonoidProduct.Graph.exists_contractEdge_isKConnected_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_contractEdge_isKConnected_three

/-! ## Faces of `2`-connected spherical rotation systems, and vertex deletion -/

/-- info: 'MonoidProduct.Graph.swap_mul_eq_permCongr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.swap_mul_eq_permCongr

/-- info: 'MonoidProduct.Graph.sameCycle_swap_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_swap_mul_iff

/-- info: 'MonoidProduct.Graph.not_sameCycle_swap_mul_of_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.not_sameCycle_swap_mul_of_sameCycle

/-- info: 'MonoidProduct.Graph.cycleCount_swap_mul_of_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycleCount_swap_mul_of_sameCycle

/-- info: 'MonoidProduct.Graph.sameCycle_swap_mul_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_swap_mul_or

/-- info: 'MonoidProduct.Graph.dartGraph_adj' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.dartGraph_adj

/-- info: 'MonoidProduct.Graph.fst_toDartGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_toDartGraph

/-- info: 'MonoidProduct.Graph.snd_toDartGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.snd_toDartGraph

/-- info: 'MonoidProduct.Graph.toDartGraph_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toDartGraph_symm

/-- info: 'MonoidProduct.Graph.toDartGraph_surjective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toDartGraph_surjective

/-- info: 'MonoidProduct.Graph.toDartGraph_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toDartGraph_injective

/-- info: 'MonoidProduct.Graph.dartGraphEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.dartGraphEquiv_apply

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_dartGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_dartGraph

/-- info: 'MonoidProduct.Graph.RotationSystem.ofDartGraph_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.ofDartGraph_rot

/-- info: 'MonoidProduct.Graph.RotationSystem.ofDartGraph_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.ofDartGraph_face

/-- info: 'MonoidProduct.Graph.RotationSystem.natCard_face_ofDartGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.natCard_face_ofDartGraph

/-- info: 'MonoidProduct.Graph.natCard_connectedComponent_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_connectedComponent_eq_one

/-- info: 'MonoidProduct.Graph.RotationSystem.splitTail_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitTail_eq_none

/-- info: 'MonoidProduct.Graph.RotationSystem.splitTail_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitTail_eq_some

/-- info: 'MonoidProduct.Graph.RotationSystem.splitTail_of_fst_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitTail_of_fst_ne

/-- info: 'MonoidProduct.Graph.RotationSystem.splitTail_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitTail_self

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_eq_of_splitTail_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_eq_of_splitTail_eq

/-- info: 'MonoidProduct.Graph.RotationSystem.splitTail_ne_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitTail_ne_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.splitTail_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitTail_inj

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_swap_mul_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_swap_mul_rot

/-- info: 'MonoidProduct.Graph.RotationSystem.splitTail_swap_mul_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitTail_swap_mul_rot

/--
info: 'MonoidProduct.Graph.RotationSystem.sameCycle_of_splitTail_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_of_splitTail_eq

/-- info: 'MonoidProduct.Graph.RotationSystem.splitTail_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitTail_left

/-- info: 'MonoidProduct.Graph.RotationSystem.splitGraph_adj_some_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitGraph_adj_some_some

/-- info: 'MonoidProduct.Graph.RotationSystem.splitGraph_adj_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitGraph_adj_none

/-- info: 'MonoidProduct.Graph.RotationSystem.splitGraph_adj_some_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitGraph_adj_some_fst

/-- info: 'MonoidProduct.Graph.RotationSystem.splitGraph_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.splitGraph_connected

/-- info: 'MonoidProduct.Graph.RotationSystem.isolatedVerts_splitGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.isolatedVerts_splitGraph

/-- info: 'MonoidProduct.Graph.RotationSystem.ncard_edgeSet_splitGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.ncard_edgeSet_splitGraph

/--
info: 'MonoidProduct.Graph.RotationSystem.natCard_face_splitRotation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.natCard_face_splitRotation

/--
info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_splitRotation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_splitRotation

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_injective_on_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_injective_on_face

/--
info: 'MonoidProduct.Graph.RotationSystem.nodup_faceWalk_of_isKConnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.nodup_faceWalk_of_isKConnected

/--
info: 'MonoidProduct.Graph.RotationSystem.isCycleList_faceWalk_of_isKConnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.isCycleList_faceWalk_of_isKConnected

/-- info: 'MonoidProduct.Graph.fst_ofInduceDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_ofInduceDart

/-- info: 'MonoidProduct.Graph.snd_ofInduceDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.snd_ofInduceDart

/-- info: 'MonoidProduct.Graph.ofInduceDart_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ofInduceDart_symm

/-- info: 'MonoidProduct.Graph.ofInduceDart_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ofInduceDart_injective

/-- info: 'MonoidProduct.Graph.exists_rotationSystem_induce_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_rotationSystem_induce_ne

/-- info: 'MonoidProduct.Graph.exists_mem_faceWalk_induce_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_mem_faceWalk_induce_ne

/-- info: 'MonoidProduct.Graph.exists_induce_ne_faceWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_induce_ne_faceWalk

/-- info: 'MonoidProduct.Graph.exists_induce_ne_isCycleList_faceWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_induce_ne_isCycleList_faceWalk

/-! ## Inserting chords, leaves and vertices into faces -/

/-- info: 'MonoidProduct.Graph.chord_extendDomain_apply_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_extendDomain_apply_left

/-- info: 'MonoidProduct.Graph.chord_extendDomain_apply_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_extendDomain_apply_right

/-- info: 'MonoidProduct.Graph.chord_not_sameCycle_of_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_not_sameCycle_of_apply_eq

/-- info: 'MonoidProduct.Graph.chord_sameCycle_mul_swap_of_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_sameCycle_mul_swap_of_apply_eq

/--
info: 'MonoidProduct.Graph.chord_sameCycle_mul_swap_self_of_apply_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_sameCycle_mul_swap_self_of_apply_eq

/-- info: 'MonoidProduct.Graph.chord_cycleCount_extendDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_cycleCount_extendDomain

/-- info: 'MonoidProduct.Graph.chord_not_sameCycle_extendDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_not_sameCycle_extendDomain

/--
info: 'MonoidProduct.Graph.chord_not_sameCycle_extendDomain_mul_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_not_sameCycle_extendDomain_mul_swap

/--
info: 'MonoidProduct.Graph.chord_cycleCount_extendDomain_mul_swap_mul_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_cycleCount_extendDomain_mul_swap_mul_swap

/--
info: 'MonoidProduct.Graph.chord_cycleCount_extendDomain_mul_swap_mul_swap_mul_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_cycleCount_extendDomain_mul_swap_mul_swap_mul_swap

/-- info: 'MonoidProduct.Graph.chord_eq_extendDomain_mul_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_eq_extendDomain_mul_swap

/--
info: 'MonoidProduct.Graph.chord_extendDomain_mul_swap_mul_swap_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_extendDomain_mul_swap_mul_swap_mul

/-- info: 'MonoidProduct.Graph.chord_extendDomain_mul_swap_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_extendDomain_mul_swap_mul

/-- info: 'MonoidProduct.Graph.chord_orbitList_eq_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_orbitList_eq_cons

/--
info: 'MonoidProduct.Graph.chord_getElem_left_of_orbitList_eq_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_getElem_left_of_orbitList_eq_append

/--
info: 'MonoidProduct.Graph.chord_getElem_right_of_orbitList_eq_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_getElem_right_of_orbitList_eq_append

/--
info: 'MonoidProduct.Graph.chord_apply_getElem_of_orbitList_eq_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_apply_getElem_of_orbitList_eq_append

/--
info: 'MonoidProduct.Graph.chord_apply_getLast_of_orbitList_eq_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_apply_getLast_of_orbitList_eq_append

/--
info: 'MonoidProduct.Graph.chord_apply_getLast_right_of_orbitList_eq_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_apply_getLast_right_of_orbitList_eq_append

/--
info: 'MonoidProduct.Graph.chord_orbitList_head_of_orbitList_eq_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_orbitList_head_of_orbitList_eq_append

/-- info: 'MonoidProduct.Graph.chord_orbitList_splice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_orbitList_splice

/-- info: 'MonoidProduct.Graph.chord_reachable_map_of_adj' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.chord_reachable_map_of_adj

/-- info: 'MonoidProduct.Graph.isAddEdge_sup_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isAddEdge_sup_edge

/-- info: 'MonoidProduct.Graph.IsAddEdge.le' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.le

/-- info: 'MonoidProduct.Graph.IsAddEdge.adj' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.adj

/-- info: 'MonoidProduct.Graph.IsAddEdge.ne' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.ne

/-- info: 'MonoidProduct.Graph.IsAddEdge.fst_dart' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.fst_dart

/-- info: 'MonoidProduct.Graph.IsAddEdge.snd_dart' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.snd_dart

/-- info: 'MonoidProduct.Graph.IsAddEdge.fst_incl' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.fst_incl

/-- info: 'MonoidProduct.Graph.IsAddEdge.snd_incl' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.snd_incl

/-- info: 'MonoidProduct.Graph.IsAddEdge.incl_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.incl_symm

/-- info: 'MonoidProduct.Graph.IsAddEdge.incl_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.incl_injective

/-- info: 'MonoidProduct.Graph.IsAddEdge.dart_symm_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.dart_symm_ne

/-- info: 'MonoidProduct.Graph.IsAddEdge.eq_sup_edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.eq_sup_edge

/-- info: 'MonoidProduct.Graph.IsAddEdge.incl_ne_dart' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.incl_ne_dart

/-- info: 'MonoidProduct.Graph.IsAddEdge.incl_ne_dart_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.incl_ne_dart_symm

/-- info: 'MonoidProduct.Graph.IsAddEdge.coe_dartEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.coe_dartEquiv

/-- info: 'MonoidProduct.Graph.IsAddEdge.eq_dart_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.eq_dart_or

/-- info: 'MonoidProduct.Graph.IsAddEdge.ncard_edgeSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.ncard_edgeSet

/-- info: 'MonoidProduct.Graph.IsAddEdge.natCard_connectedComponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.natCard_connectedComponent

/-- info: 'MonoidProduct.Graph.IsAddEdge.isolatedVerts_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsAddEdge.isolatedVerts_eq

/-- info: 'MonoidProduct.Graph.RotationSystem.chord_fst_rot_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.chord_fst_rot_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.chord_face_symm_rot_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.chord_face_symm_rot_symm

/--
info: 'MonoidProduct.Graph.RotationSystem.chord_sameCycle_face_symm_rot_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.chord_sameCycle_face_symm_rot_symm

/--
info: 'MonoidProduct.Graph.RotationSystem.chord_fst_extendDomain_rot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.chord_fst_extendDomain_rot

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_chordRot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_chordRot

/-- info: 'MonoidProduct.Graph.RotationSystem.sameCycle_chordRot_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_chordRot_incl

/-- info: 'MonoidProduct.Graph.RotationSystem.sameCycle_chordRot_dart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_chordRot_dart

/--
info: 'MonoidProduct.Graph.RotationSystem.sameCycle_chordRot_dart_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_chordRot_dart_symm

/--
info: 'MonoidProduct.Graph.RotationSystem.exists_sameCycle_chordRot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.exists_sameCycle_chordRot

/-- info: 'MonoidProduct.Graph.RotationSystem.chordRot_apply_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.chordRot_apply_incl

/-- info: 'MonoidProduct.Graph.RotationSystem.chordRot_apply_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.chordRot_apply_left

/-- info: 'MonoidProduct.Graph.RotationSystem.chordRot_apply_dart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.chordRot_apply_dart

/-- info: 'MonoidProduct.Graph.RotationSystem.chordRot_apply_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.chordRot_apply_right

/-- info: 'MonoidProduct.Graph.RotationSystem.chordRot_apply_dart_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.chordRot_apply_dart_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.insertChord_face_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertChord_face_incl

/-- info: 'MonoidProduct.Graph.RotationSystem.insertChord_face_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertChord_face_left

/-- info: 'MonoidProduct.Graph.RotationSystem.insertChord_face_dart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertChord_face_dart

/-- info: 'MonoidProduct.Graph.RotationSystem.insertChord_face_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertChord_face_right

/--
info: 'MonoidProduct.Graph.RotationSystem.insertChord_face_dart_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertChord_face_dart_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.insertChord_face_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertChord_face_eq

/-- info: 'MonoidProduct.Graph.RotationSystem.natCard_face_insertChord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.natCard_face_insertChord

/-- info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_insertChord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_insertChord

/-- info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.insertChord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.insertChord

/-- info: 'MonoidProduct.Graph.RotationSystem.faceDarts_insertChord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.faceDarts_insertChord

/--
info: 'MonoidProduct.Graph.RotationSystem.faceDarts_insertChord_of_not_sameCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.faceDarts_insertChord_of_not_sameCycle

/-- info: 'MonoidProduct.Graph.RotationSystem.faceWalk_insertChord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.faceWalk_insertChord

/-- info: 'MonoidProduct.Graph.isPlanar_sup_edge_of_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_sup_edge_of_sameCycle

/-- info: 'MonoidProduct.Graph.attachVertex_adj_none_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.attachVertex_adj_none_some

/-- info: 'MonoidProduct.Graph.attachVertex_adj_some_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.attachVertex_adj_some_none

/-- info: 'MonoidProduct.Graph.attachVertex_adj_some_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.attachVertex_adj_some_some

/-- info: 'MonoidProduct.Graph.attachVertex_adj_none_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.attachVertex_adj_none_none

/-- info: 'MonoidProduct.Graph.fst_attachDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_attachDart

/-- info: 'MonoidProduct.Graph.snd_attachDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.snd_attachDart

/-- info: 'MonoidProduct.Graph.attachDart_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.attachDart_injective

/-- info: 'MonoidProduct.Graph.attachDart_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.attachDart_symm

/-- info: 'MonoidProduct.Graph.isAddEdge_attachVertex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isAddEdge_attachVertex

/-- info: 'MonoidProduct.Graph.attachVertex_insert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.attachVertex_insert

/-- info: 'MonoidProduct.Graph.fst_leafDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_leafDart

/-- info: 'MonoidProduct.Graph.snd_leafDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.snd_leafDart

/-- info: 'MonoidProduct.Graph.leafDart_symm_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.leafDart_symm_ne

/-- info: 'MonoidProduct.Graph.attachDart_ne_leafDart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.attachDart_ne_leafDart

/-- info: 'MonoidProduct.Graph.attachDart_ne_leafDart_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.attachDart_ne_leafDart_symm

/-- info: 'MonoidProduct.Graph.eq_leafDart_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eq_leafDart_or

/-- info: 'MonoidProduct.Graph.coe_leafDartEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.coe_leafDartEquiv

/--
info: 'MonoidProduct.Graph.natCard_connectedComponent_attachVertex_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_connectedComponent_attachVertex_leaf

/-- info: 'MonoidProduct.Graph.isolatedVerts_attachVertex_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isolatedVerts_attachVertex_leaf

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_extendDomain_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_extendDomain_leaf

/-- info: 'MonoidProduct.Graph.RotationSystem.fst_leafRot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fst_leafRot

/--
info: 'MonoidProduct.Graph.RotationSystem.sameCycle_leafRot_attachDart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_leafRot_attachDart

/--
info: 'MonoidProduct.Graph.RotationSystem.sameCycle_leafRot_leafDart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_leafRot_leafDart

/-- info: 'MonoidProduct.Graph.RotationSystem.leafRot_apply_attachDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.leafRot_apply_attachDart

/-- info: 'MonoidProduct.Graph.RotationSystem.leafRot_apply_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.leafRot_apply_left

/-- info: 'MonoidProduct.Graph.RotationSystem.leafRot_apply_leafDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.leafRot_apply_leafDart

/--
info: 'MonoidProduct.Graph.RotationSystem.leafRot_apply_leafDart_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.leafRot_apply_leafDart_symm

/--
info: 'MonoidProduct.Graph.RotationSystem.insertLeaf_face_attachDart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertLeaf_face_attachDart

/-- info: 'MonoidProduct.Graph.RotationSystem.insertLeaf_face_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertLeaf_face_left

/-- info: 'MonoidProduct.Graph.RotationSystem.insertLeaf_face_leafDart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertLeaf_face_leafDart

/--
info: 'MonoidProduct.Graph.RotationSystem.insertLeaf_face_leafDart_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertLeaf_face_leafDart_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.insertLeaf_face_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.insertLeaf_face_eq

/-- info: 'MonoidProduct.Graph.RotationSystem.natCard_face_insertLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.natCard_face_insertLeaf

/-- info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_insertLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_insertLeaf

/-- info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.insertLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.insertLeaf

/-- info: 'MonoidProduct.Graph.RotationSystem.faceDarts_insertLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.faceDarts_insertLeaf

/-- info: 'MonoidProduct.Graph.RotationSystem.exists_fan_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.exists_fan_aux

/--
info: 'MonoidProduct.Graph.RotationSystem.fan_exists_faceWalk_eq_startAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.fan_exists_faceWalk_eq_startAt

/--
info: 'MonoidProduct.Graph.exists_isSpherical_attachVertex_faceWalk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_isSpherical_attachVertex_faceWalk

/--
info: 'MonoidProduct.Graph.isPlanar_attachVertex_of_subset_faceWalk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_attachVertex_of_subset_faceWalk

/-! ## Gluing planar graphs across separators of size zero, one and two -/

/-- info: 'MonoidProduct.Graph.sumDart_bijective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sumDart_bijective

/-- info: 'MonoidProduct.Graph.sumDartEquiv_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sumDartEquiv_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.sum_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sum_face

/-- info: 'MonoidProduct.Graph.RotationSystem.sameCycle_sum_face_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_sum_face_inl

/-- info: 'MonoidProduct.Graph.RotationSystem.sameCycle_sum_face_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_sum_face_inr

/-- info: 'MonoidProduct.Graph.RotationSystem.natCard_face_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.natCard_face_sum

/-- info: 'MonoidProduct.Graph.natCard_connectedComponent_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_connectedComponent_sum

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_sum

/-- info: 'MonoidProduct.Graph.isolatedVerts_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isolatedVerts_sum

/-- info: 'MonoidProduct.Graph.ncard_isolatedVerts_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_isolatedVerts_sum

/-- info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_sum

/-- info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.sum

/-- info: 'MonoidProduct.Graph.IsPlanar.sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.sum

/-- info: 'MonoidProduct.Graph.identify_ne_of_not_reachable' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.identify_ne_of_not_reachable

/--
info: 'MonoidProduct.Graph.natCard_connectedComponent_contractEdge_add_one_of_not_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_connectedComponent_contractEdge_add_one_of_not_reachable

/-- info: 'MonoidProduct.Graph.contractEdge_adj_contractVertex_of_not_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractEdge_adj_contractVertex_of_not_reachable

/-- info: 'MonoidProduct.Graph.identifyDart_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.identifyDart_injective

/-- info: 'MonoidProduct.Graph.identifyDart_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.identifyDart_surjective

/-- info: 'MonoidProduct.Graph.fst_identifyDartEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_identifyDartEquiv

/-- info: 'MonoidProduct.Graph.identifyDartEquiv_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.identifyDartEquiv_symm

/-- info: 'MonoidProduct.Graph.identifyDartEquiv_symm_apply_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.identifyDartEquiv_symm_apply_symm

/--
info: 'MonoidProduct.Graph.ncard_edgeSet_contractEdge_of_not_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_contractEdge_of_not_reachable

/--
info: 'MonoidProduct.Graph.mem_isolatedVerts_contractEdge_iff_of_not_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_isolatedVerts_contractEdge_iff_of_not_reachable

/--
info: 'MonoidProduct.Graph.ncard_isolatedVerts_contractEdge_add_one_of_not_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_isolatedVerts_contractEdge_add_one_of_not_reachable

/--
info: 'MonoidProduct.Graph.ncard_isolatedVerts_contractEdge_of_not_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_isolatedVerts_contractEdge_of_not_reachable

/-- info: 'MonoidProduct.Graph.RotationSystem.identifyPlain_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.identifyPlain_face

/-- info: 'MonoidProduct.Graph.RotationSystem.identifySplice_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.identifySplice_face

/--
info: 'MonoidProduct.Graph.RotationSystem.natCard_face_identifySplice_add_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.natCard_face_identifySplice_add_one

/--
info: 'MonoidProduct.Graph.RotationSystem.sameCycle_identifySplice_face' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.sameCycle_identifySplice_face

/--
info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_identifyPlain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_identifyPlain

/--
info: 'MonoidProduct.Graph.RotationSystem.eulerDefect_identifySplice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.eulerDefect_identifySplice

/-- info: 'MonoidProduct.Graph.fst_glueDartLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_glueDartLeft

/-- info: 'MonoidProduct.Graph.fst_glueDartRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_glueDartRight

/-- info: 'MonoidProduct.Graph.exists_isSpherical_glueVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_isSpherical_glueVertex

/-- info: 'MonoidProduct.Graph.IsPlanar.glueVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.glueVertex

/-- info: 'MonoidProduct.Graph.glueSide_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.glueSide_of_mem

/-- info: 'MonoidProduct.Graph.glueSide_of_notMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.glueSide_of_notMem

/-- info: 'MonoidProduct.Graph.elim_glueSide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.elim_glueSide

/-- info: 'MonoidProduct.Graph.glueSide_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.glueSide_injective

/-- info: 'MonoidProduct.Graph.sum_adj_glueSide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sum_adj_glueSide

/-- info: 'MonoidProduct.Graph.isPlanar_of_induce_of_inter_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_of_induce_of_inter_eq_empty

/-- info: 'MonoidProduct.Graph.glueSide_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.glueSide_ne

/-- info: 'MonoidProduct.Graph.glueVertexMap_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.glueVertexMap_injective

/-- info: 'MonoidProduct.Graph.glueVertexMap_adj_of_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.glueVertexMap_adj_of_side

/-- info: 'MonoidProduct.Graph.glueVertexMap_adj_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.glueVertexMap_adj_self

/--
info: 'MonoidProduct.Graph.isPlanar_of_induce_of_inter_eq_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_of_induce_of_inter_eq_singleton

/-- info: 'MonoidProduct.Graph.isPlanar_of_induce_of_inter_eq_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_of_induce_of_inter_eq_pair

/-! ## The converse of Wagner's theorem, and the equivalence -/

/-- info: 'MonoidProduct.Graph.idxOf_map_of_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.idxOf_map_of_injective

/-- info: 'MonoidProduct.Graph.startAt_map_of_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.startAt_map_of_injective

/-- info: 'MonoidProduct.Graph.cycDist_map_of_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.cycDist_map_of_injective

/-- info: 'MonoidProduct.Graph.arc_map_of_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.arc_map_of_injective

/-- info: 'MonoidProduct.Graph.closedArc_map_of_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.closedArc_map_of_injective

/-- info: 'MonoidProduct.Graph.isConsecutive_map_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isConsecutive_map_iff

/-- info: 'MonoidProduct.Graph.IsCycleList.map_of_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsCycleList.map_of_injective

/-- info: 'MonoidProduct.Graph.isPlanar_of_natCard_le_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_of_natCard_le_four

/-- info: 'MonoidProduct.Graph.wagner_threeConnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.wagner_threeConnected

/-- info: 'MonoidProduct.Graph.wagner_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.wagner_hard

/-- info: 'MonoidProduct.Graph.wagner_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.wagner_iff

/-! ## Minor-closed and sparse graph classes (Section 6, `sec:graph-certificates`) -/

/-- info: 'MonoidProduct.Graph.restrictTo_adj' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.restrictTo_adj

/-- info: 'MonoidProduct.Graph.restrictTo_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.restrictTo_mono

/-- info: 'MonoidProduct.Graph.isConnectedSet_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isConnectedSet_iff

/-- info: 'MonoidProduct.Graph.isConnectedSet_singleton' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isConnectedSet_singleton

/-- info: 'MonoidProduct.Graph.isConnectedSet_pair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isConnectedSet_pair

/-- info: 'MonoidProduct.Graph.IsConnectedSet.image' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsConnectedSet.image

/-- info: 'MonoidProduct.Graph.reachable_biUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_biUnion

/-- info: 'MonoidProduct.Graph.IsMinor.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsMinor.refl

/-- info: 'MonoidProduct.Graph.IsMinor.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsMinor.trans

/-- info: 'MonoidProduct.Graph.isMinor_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_of_le

/-- info: 'MonoidProduct.Graph.isMinor_induce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_induce

/-- info: 'MonoidProduct.Graph.Iso.isMinor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.Iso.isMinor

/-- info: 'MonoidProduct.Graph.isMinor_top_of_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_top_of_equiv

/-- info: 'MonoidProduct.Graph.contractEdge_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.contractEdge_adj

/-- info: 'MonoidProduct.Graph.isMinor_contractEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_contractEdge

/-- info: 'MonoidProduct.Graph.two_mul_ncard_edgeSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.two_mul_ncard_edgeSet

/-- info: 'MonoidProduct.Graph.ncard_neighborSet_induce_neighborSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_neighborSet_induce_neighborSet

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_le_contractEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_le_contractEdge

/-- info: 'MonoidProduct.Graph.isMinor_top_succ_of_induce_neighborSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_top_succ_of_induce_neighborSet

/-- info: 'MonoidProduct.Graph.isMinor_top_two_of_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_top_two_of_adj

/-- info: 'MonoidProduct.Graph.isMinor_top_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinor_top_of_le

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_le_of_not_isMinor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_le_of_not_isMinor

/-- info: 'MonoidProduct.Graph.IsMinorClosed.exists_ncard_edgeSet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsMinorClosed.exists_ncard_edgeSet_le

/-- info: 'MonoidProduct.Graph.apex_adj_none_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.apex_adj_none_some

/-- info: 'MonoidProduct.Graph.apex_adj_some_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.apex_adj_some_some

/-- info: 'MonoidProduct.Graph.apex_adj_some_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.apex_adj_some_none

/-- info: 'MonoidProduct.Graph.apex_not_adj_none_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.apex_not_adj_none_none

/-- info: 'MonoidProduct.Graph.edgeSet_apex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeSet_apex

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_apex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_apex

/-- info: 'MonoidProduct.Graph.IsOuterplanar.ncard_edgeSet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsOuterplanar.ncard_edgeSet_le

/-- info: 'MonoidProduct.Graph.not_isOuterplanar_top_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.not_isOuterplanar_top_four

/-- info: 'MonoidProduct.Graph.apex_top_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.apex_top_three

/-- info: 'MonoidProduct.Graph.isOuterplanar_top_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isOuterplanar_top_three

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_top_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_top_three

/-- info: 'MonoidProduct.Graph.ncard_edgeSet_le_of_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_edgeSet_le_of_decomposition

/-- info: 'MonoidProduct.Graph.TreewidthLE.ncard_edgeSet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.TreewidthLE.ncard_edgeSet_le

/-- info: 'MonoidProduct.Graph.treewidthLE_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.treewidthLE_top

/-- info: 'MonoidProduct.Graph.treewidthLE_one_path3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.treewidthLE_one_path3

/-- info: 'MonoidProduct.Graph.EmbeddingScheme.fst_traceStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.EmbeddingScheme.fst_traceStep

/--
info: 'MonoidProduct.Graph.EmbeddingScheme.connectedComponentMk_fst_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.EmbeddingScheme.connectedComponentMk_fst_trace

/-- info: 'MonoidProduct.Graph.GenusLE.eulerGenusLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.GenusLE.eulerGenusLE

/-- info: 'MonoidProduct.Graph.ncard_supp_le_two_of_rot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ncard_supp_le_two_of_rot_eq

/-- info: 'MonoidProduct.Graph.EmbeddingScheme.trace_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.EmbeddingScheme.trace_apply

/-- info: 'MonoidProduct.Graph.EmbeddingScheme.trace_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.EmbeddingScheme.trace_ne

/-- info: 'MonoidProduct.Graph.EmbeddingScheme.trace_trace_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.EmbeddingScheme.trace_trace_ne

/--
info: 'MonoidProduct.Graph.EmbeddingScheme.three_le_ncard_sameCycle_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.EmbeddingScheme.three_le_ncard_sameCycle_trace

/-- info: 'MonoidProduct.Graph.EmbeddingScheme.ncard_statesIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.EmbeddingScheme.ncard_statesIn

/-- info: 'MonoidProduct.Graph.EmbeddingScheme.mul_ncard_orbitsIn_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.EmbeddingScheme.mul_ncard_orbitsIn_le

/-- info: 'MonoidProduct.Graph.mul_ncard_edgeSet_add_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mul_ncard_edgeSet_add_le_add

/-- info: 'MonoidProduct.Graph.EmbeddingScheme.edges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.EmbeddingScheme.edges_le

/-- info: 'MonoidProduct.Graph.EulerGenusLE.ncard_edgeSet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.EulerGenusLE.ncard_edgeSet_le

/-- info: 'MonoidProduct.Graph.sameCycle_iff_of_semiconj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.sameCycle_iff_of_semiconj

/-- info: 'MonoidProduct.Graph.RotationSystem.trace_toScheme_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.trace_toScheme_false

/-- info: 'MonoidProduct.Graph.RotationSystem.trace_toScheme_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.trace_toScheme_true

/-- info: 'MonoidProduct.Graph.RotationSystem.snd_trace_toScheme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.snd_trace_toScheme

/-- info: 'MonoidProduct.Graph.RotationSystem.two_mul_ncard_facesIn_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.two_mul_ncard_facesIn_le

/-- info: 'MonoidProduct.Graph.IsPlanar.genusLE_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.genusLE_zero

/-- info: 'MonoidProduct.Graph.GenusLE.ncard_edgeSet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.GenusLE.ncard_edgeSet_le

/-- info: 'MonoidProduct.Graph.fst_dartEquivOfIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_dartEquivOfIso

/-- info: 'MonoidProduct.Graph.fst_dartEquivOfIso_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_dartEquivOfIso_symm

/-- info: 'MonoidProduct.Graph.dartEquivOfIso_symm_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.dartEquivOfIso_symm_symm

/-- info: 'MonoidProduct.Graph.RotationSystem.mapIso_rot_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.mapIso_rot_apply

/-- info: 'MonoidProduct.Graph.RotationSystem.mapIso_face_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.mapIso_face_apply

/-- info: 'MonoidProduct.Graph.RotationSystem.face_mapIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.face_mapIso

/-- info: 'MonoidProduct.Graph.RotationSystem.IsSpherical.mapIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.RotationSystem.IsSpherical.mapIso

/-- info: 'MonoidProduct.Graph.IsPlanar.of_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.IsPlanar.of_iso

/-- info: 'MonoidProduct.Graph.isPlanar_iff_of_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isPlanar_iff_of_iso

/-- info: 'MonoidProduct.Graph.strongCertificateSize_le_mul_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.strongCertificateSize_le_mul_of_linear

/-- info: 'MonoidProduct.Graph.classIndicator_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.classIndicator_eq_true_iff

/--
info: 'MonoidProduct.Graph.minorClosed_strongCertificateSize_le_linear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.minorClosed_strongCertificateSize_le_linear

/-- info: 'MonoidProduct.Graph.isMinorClosed_not_isMinor_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isMinorClosed_not_isMinor_top

/-- info: 'MonoidProduct.Graph.isProperClass_not_isMinor_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isProperClass_not_isMinor_top

/-- info: 'MonoidProduct.Graph.isOuterplanar_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isOuterplanar_eq_true_iff

/-- info: 'MonoidProduct.Graph.hasTreewidthLE_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasTreewidthLE_eq_true_iff

/-- info: 'MonoidProduct.Graph.hasEulerGenusLE_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasEulerGenusLE_eq_true_iff

/-- info: 'MonoidProduct.Graph.hasGenusLE_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasGenusLE_eq_true_iff

/-- info: 'MonoidProduct.Graph.outerplanarity_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.outerplanarity_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.outerplanarity_strongCertificateSize_le_linear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.outerplanarity_strongCertificateSize_le_linear

/-- info: 'MonoidProduct.Graph.treewidth_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.treewidth_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.treewidth_strongCertificateSize_le_linear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.treewidth_strongCertificateSize_le_linear

/-- info: 'MonoidProduct.Graph.EulerGenusLE.ncard_edgeSet_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.EulerGenusLE.ncard_edgeSet_le_mul

/--
info: 'MonoidProduct.Graph.surfaceEmbedding_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.surfaceEmbedding_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.genus_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.genus_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.genusLE_zero_top_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.genusLE_zero_top_four

/-- info: 'MonoidProduct.Graph.not_eulerGenusLE_zero_top_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.not_eulerGenusLE_zero_top_five

/-- info: 'MonoidProduct.Graph.eulerGenusLE_zero_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eulerGenusLE_zero_bot

/-- info: 'MonoidProduct.Graph.minorClosed_query_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.minorClosed_query_le

/-- info: 'MonoidProduct.Graph.outerplanarity_query_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.outerplanarity_query_le

/-- info: 'MonoidProduct.Graph.treewidth_query_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.treewidth_query_le

/-- info: 'MonoidProduct.Graph.surfaceEmbedding_query_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.surfaceEmbedding_query_le

/-- info: 'MonoidProduct.Graph.k7_face_face_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.k7_face_face_face

/-- info: 'MonoidProduct.Graph.k7_sameCycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.k7_sameCycle_iff

/-- info: 'MonoidProduct.Graph.natCard_k7Face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_k7Face

/-- info: 'MonoidProduct.Graph.twiceEulerGenus_k7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.twiceEulerGenus_k7

/-- info: 'MonoidProduct.Graph.genusLE_one_top_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.genusLE_one_top_seven

/-- info: 'MonoidProduct.Graph.not_eulerGenusLE_one_top_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.not_eulerGenusLE_one_top_seven

/-! ## Edge-failure profiles (Section 6, `sec:failure-profiles`) -/

/--
info: 'MonoidProduct.Certificates.IsStrongCertificate.of_determined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.IsStrongCertificate.of_determined

/--
info: 'MonoidProduct.Certificates.HasStrongCertificateBound.of_determined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.HasStrongCertificateBound.of_determined

/--
info: 'MonoidProduct.Certificates.strongCertificateSize_le_of_determined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Certificates.strongCertificateSize_le_of_determined

/-- info: 'MonoidProduct.Graph.mem_edgeFailureProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_edgeFailureProfile

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_union_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_union_congr

/-- info: 'MonoidProduct.Graph.extensionEquiv_edgeFailureProfile_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.extensionEquiv_edgeFailureProfile_iff

/-- info: 'MonoidProduct.Graph.isStrongCertificate_edgeFailureProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isStrongCertificate_edgeFailureProfile

/-- info: 'MonoidProduct.Graph.forestStack_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.forestStack_subset

/-- info: 'MonoidProduct.Graph.forestStack_eq_biUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.forestStack_eq_biUnion

/-- info: 'MonoidProduct.Graph.isAcyclic_forestLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isAcyclic_forestLayer

/-- info: 'MonoidProduct.Graph.reachable_forestLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_forestLayer

/-- info: 'MonoidProduct.Graph.disjoint_forestLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.disjoint_forestLayer

/-- info: 'MonoidProduct.Graph.card_forestStack_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_forestStack_le

/-- info: 'MonoidProduct.Graph.exists_disjoint_forestLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_disjoint_forestLayer

/-- info: 'MonoidProduct.Graph.connectedComponents_forestStack_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.connectedComponents_forestStack_sdiff

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_forestStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_forestStack

/-- info: 'MonoidProduct.Graph.isStrongCertificate_forestStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isStrongCertificate_forestStack

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_edgeFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_edgeFailureProfile

/--
info: 'MonoidProduct.Graph.edgeFailureProfile_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_min_edgeFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_min_edgeFailureProfile

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_of_le

/--
info: 'MonoidProduct.Graph.edgeFailureProfile_strongCertificateSize_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_strongCertificateSize_mono

/--
info: 'MonoidProduct.Graph.edgeFailureProfile_zero_strongCertificateSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_zero_strongCertificateSize

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_one

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_one_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_one_eq_iff

/--
info: 'MonoidProduct.Graph.edgeFailureProfile_one_strongCertificateSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_one_strongCertificateSize

/-- info: 'MonoidProduct.Graph.mem_bridges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_bridges

/-- info: 'MonoidProduct.Graph.isBridge_iff_not_reachable_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isBridge_iff_not_reachable_sdiff

/-- info: 'MonoidProduct.Graph.mem_bridges_iff_edgeFailureProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_bridges_iff_edgeFailureProfile

/-- info: 'MonoidProduct.Graph.mem_bridges_iff_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_bridges_iff_card_lt

/-- info: 'MonoidProduct.Graph.bridges_eq_of_edgeFailureProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridges_eq_of_edgeFailureProfile

/-- info: 'MonoidProduct.Graph.bridges_strongCertificateSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridges_strongCertificateSize_le

/-- info: 'MonoidProduct.Graph.hasStrongCertificateBound_bridges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_bridges

/-- info: 'MonoidProduct.Graph.bridgePartitions_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridgePartitions_eq_some_iff

/-- info: 'MonoidProduct.Graph.bridgePartitions_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridgePartitions_eq_none_iff

/--
info: 'MonoidProduct.Graph.bridgePartitions_eq_of_edgeFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridgePartitions_eq_of_edgeFailureProfile

/--
info: 'MonoidProduct.Graph.bridgePartitions_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridgePartitions_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_bridgePartitions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_bridgePartitions

/-- info: 'MonoidProduct.Graph.isEdgeConnected_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isEdgeConnected_eq_true_iff

/-- info: 'MonoidProduct.Graph.isEdgeConnected_iff_edgeFailureProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isEdgeConnected_iff_edgeFailureProfile

/--
info: 'MonoidProduct.Graph.isEdgeConnected_eq_of_edgeFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.isEdgeConnected_eq_of_edgeFailureProfile

/--
info: 'MonoidProduct.Graph.edgeConnectivity_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeConnectivity_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_isEdgeConnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_isEdgeConnected

/-- info: 'MonoidProduct.Graph.qMatrix_le_mul_min_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le_mul_min_of_le

/-- info: 'MonoidProduct.Graph.qMatrix_le_two_pow_mul_sqrt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le_two_pow_mul_sqrt_of_le

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_qList_le

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_qMatrix_le

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_qMatrix_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_qMatrix_le_min

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.bridges_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridges_qList_le

/-- info: 'MonoidProduct.Graph.bridges_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridges_qMatrix_le

/-- info: 'MonoidProduct.Graph.bridges_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridges_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.bridges_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridges_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.bridgePartitions_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridgePartitions_qList_le

/-- info: 'MonoidProduct.Graph.bridgePartitions_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridgePartitions_qMatrix_le

/-- info: 'MonoidProduct.Graph.bridgePartitions_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridgePartitions_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.bridgePartitions_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.bridgePartitions_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.edgeConnectivity_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeConnectivity_qList_le

/-- info: 'MonoidProduct.Graph.edgeConnectivity_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeConnectivity_qMatrix_le

/-- info: 'MonoidProduct.Graph.edgeConnectivity_qMatrix_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeConnectivity_qMatrix_le_min

/-- info: 'MonoidProduct.Graph.edgeConnectivity_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeConnectivity_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.spanningForest_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.spanningForest_subset

/-- info: 'MonoidProduct.Graph.reachable_spanningForest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_spanningForest

/-- info: 'MonoidProduct.Graph.isAcyclic_spanningForest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isAcyclic_spanningForest

/-- info: 'MonoidProduct.Graph.card_spanningForest_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_spanningForest_le

/-- info: 'MonoidProduct.Graph.forestStack_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.forestStack_succ

/-- info: 'MonoidProduct.Graph.forestLayer_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.forestLayer_subset

/-- info: 'MonoidProduct.Graph.forestStack_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.forestStack_mono

/-- info: 'MonoidProduct.Graph.forestLayer_subset_forestStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.forestLayer_subset_forestStack

/-- info: 'MonoidProduct.Graph.exists_edge_eq_mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_edge_eq_mk

/-- info: 'MonoidProduct.Graph.toGraph_sdiff_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_sdiff_singleton

/-! ## Failure-profile lower bounds (Section 6, `prop:failure-profile-complexity`) -/

/-- info: 'MonoidProduct.Graph.reachable_induce_of_walk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_induce_of_walk

/-- info: 'MonoidProduct.Graph.reachable_of_induce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_of_induce

/-- info: 'MonoidProduct.Graph.eq_of_reachable_of_forall_not_adj' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eq_of_reachable_of_forall_not_adj

/-- info: 'MonoidProduct.Graph.mem_vertexFailureProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_vertexFailureProfile

/-- info: 'MonoidProduct.Graph.fst_notMem_of_mem_vertexFailureProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.fst_notMem_of_mem_vertexFailureProfile

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_of_le

/-- info: 'MonoidProduct.Graph.mem_vertexFailureProfile_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_vertexFailureProfile_empty

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_one_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_one_eq_iff

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_zero

/-- info: 'MonoidProduct.Graph.two_mul_abs_mul_le_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.two_mul_abs_mul_le_weighted

/-- info: 'MonoidProduct.Graph.l2_opNorm_le_of_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.l2_opNorm_le_of_weighted

/-- info: 'MonoidProduct.Graph.nonempty_jTuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.nonempty_jTuple

/-- info: 'MonoidProduct.Graph.card_insert_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_insert_erase

/-- info: 'MonoidProduct.Graph.exch_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exch_self

/-- info: 'MonoidProduct.Graph.exch_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exch_ne

/-- info: 'MonoidProduct.Graph.exch_exch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exch_exch

/-- info: 'MonoidProduct.Graph.eq_exch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eq_exch

/-- info: 'MonoidProduct.Graph.Exch.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.Exch.symm

/-- info: 'MonoidProduct.Graph.Exch.ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.Exch.ne

/-- info: 'MonoidProduct.Graph.card_exch_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_exch_ge

/-- info: 'MonoidProduct.Graph.card_maskedExch_le_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_maskedExch_le_of_mem

/-- info: 'MonoidProduct.Graph.card_maskedExch_le_of_notMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_maskedExch_le_of_notMem

/-- info: 'MonoidProduct.Graph.johnsonΓ_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.johnsonΓ_symm

/-- info: 'MonoidProduct.Graph.johnsonΓ_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.johnsonΓ_isHermitian

/-- info: 'MonoidProduct.Graph.johnsonΓ_norm_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.johnsonΓ_norm_ge

/-- info: 'MonoidProduct.Graph.johnsonΓ_hadamard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.johnsonΓ_hadamard_le

/-- info: 'MonoidProduct.Graph.enumeration_advPMOn_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.enumeration_advPMOn_ge

/-- info: 'MonoidProduct.Graph.enumeration_qQuery_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.enumeration_qQuery_ge

/-- info: 'MonoidProduct.Graph.one_le_advPMOn_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.one_le_advPMOn_of_ne

/-- info: 'MonoidProduct.Graph.qMatrix_postcomp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_postcomp_le

/-- info: 'MonoidProduct.Graph.qMatrix_ge_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_ge_of_ne

/-- info: 'MonoidProduct.Graph.qMatrix_ge_of_enumeration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_ge_of_enumeration

/-- info: 'MonoidProduct.Graph.FailureLower.position_of_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.position_of_base

/-- info: 'MonoidProduct.Graph.FailureLower.adj_aVert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.adj_aVert_iff

/-- info: 'MonoidProduct.Graph.FailureLower.isolated_sdiff_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.isolated_sdiff_iff

/-- info: 'MonoidProduct.Graph.FailureLower.isolated_induce_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.isolated_induce_iff

/--
info: 'MonoidProduct.Graph.FailureLower.edgeFailureProfile_baseGraph_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.edgeFailureProfile_baseGraph_injective

/--
info: 'MonoidProduct.Graph.FailureLower.vertexFailureProfile_baseGraph_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.vertexFailureProfile_baseGraph_injective

/--
info: 'MonoidProduct.Graph.FailureLower.mem_connectedComponents_star' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.mem_connectedComponents_star

/--
info: 'MonoidProduct.Graph.FailureLower.connectedComponents_starGraph_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.connectedComponents_starGraph_injective

/-- info: 'MonoidProduct.Graph.qMatrix_ge_clique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_ge_clique

/-- info: 'MonoidProduct.Graph.qMatrix_ge_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_ge_star

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_qMatrix_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_qMatrix_ge

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_qMatrix_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_qMatrix_ge

/-- info: 'MonoidProduct.Graph.edgeFailureProfile_qMatrix_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgeFailureProfile_qMatrix_theta

/-- info: 'MonoidProduct.Graph.johnsonΓ_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.johnsonΓ_apply

/-- info: 'MonoidProduct.Graph.FailureLower.aVert_ne_bVert' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.aVert_ne_bVert

/-- info: 'MonoidProduct.Graph.FailureLower.aVert_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.aVert_injective

/-- info: 'MonoidProduct.Graph.FailureLower.bVert_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.bVert_injective

/-- info: 'MonoidProduct.Graph.FailureLower.mk_aVert_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.mk_aVert_eq_iff

/-- info: 'MonoidProduct.Graph.FailureLower.crossEdge_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.crossEdge_injective

/-- info: 'MonoidProduct.Graph.FailureLower.mem_crossEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.mem_crossEdges

/-- info: 'MonoidProduct.Graph.FailureLower.crossEdge_mem_crossEdges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.crossEdge_mem_crossEdges

/--
info: 'MonoidProduct.Graph.FailureLower.aVert_notMem_of_mem_bClique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.aVert_notMem_of_mem_bClique

/-- info: 'MonoidProduct.Graph.FailureLower.crossEdge_notMem_bClique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.crossEdge_notMem_bClique

/-- info: 'MonoidProduct.Graph.FailureLower.aVert_notMem_image_bVert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.aVert_notMem_image_bVert

/-- info: 'MonoidProduct.Graph.FailureLower.mem_of_reachable_of_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.FailureLower.mem_of_reachable_of_closed

/-! ## Vertex-failure certificates (Section 6, `sec:failure-profiles`) -/

/-- info: 'MonoidProduct.Graph.two_mul_choose_two_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.two_mul_choose_two_le_sq

/-- info: 'MonoidProduct.Graph.qMatrix_le_mul_min_of_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le_mul_min_of_le_two_mul

/-- info: 'MonoidProduct.Graph.qMatrix_le_two_pow_mul_sqrt_of_le_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.qMatrix_le_two_pow_mul_sqrt_of_le_four

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_qList_le

/-- info: 'MonoidProduct.Graph.failureProfiles_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.failureProfiles_qList_le

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_qMatrix_le

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_qMatrix_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_qMatrix_le_min

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_qMatrix_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_qMatrix_theta

/-- info: 'MonoidProduct.Graph.failureProfiles_qMatrix_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.failureProfiles_qMatrix_theta

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.articulationPoints_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPoints_qList_le

/-- info: 'MonoidProduct.Graph.articulationPoints_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPoints_qMatrix_le

/-- info: 'MonoidProduct.Graph.articulationPoints_qMatrix_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPoints_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.articulationPoints_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPoints_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.articulationPartitions_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPartitions_qList_le

/-- info: 'MonoidProduct.Graph.articulationPartitions_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPartitions_qMatrix_le

/--
info: 'MonoidProduct.Graph.articulationPartitions_qMatrix_le_mul_sqrt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPartitions_qMatrix_le_mul_sqrt

/-- info: 'MonoidProduct.Graph.articulationPartitions_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPartitions_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.vertexConnectivity_qList_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexConnectivity_qList_le

/-- info: 'MonoidProduct.Graph.vertexConnectivity_qMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexConnectivity_qMatrix_le

/-- info: 'MonoidProduct.Graph.vertexConnectivity_qMatrix_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexConnectivity_qMatrix_le_min

/-- info: 'MonoidProduct.Graph.vertexConnectivity_qAdjEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexConnectivity_qAdjEdges_le

/-- info: 'MonoidProduct.Graph.natCard_connectedComponent_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.natCard_connectedComponent_congr

/-- info: 'MonoidProduct.Graph.mem_articulationPoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_articulationPoints

/-- info: 'MonoidProduct.Graph.mem_articulationPoints_iff_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_articulationPoints_iff_separates

/-- info: 'MonoidProduct.Graph.reachable_induce_ne_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_induce_ne_iff

/--
info: 'MonoidProduct.Graph.mem_articulationPoints_iff_vertexFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_articulationPoints_iff_vertexFailureProfile

/--
info: 'MonoidProduct.Graph.articulationPoints_eq_of_vertexFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPoints_eq_of_vertexFailureProfile

/--
info: 'MonoidProduct.Graph.vertexFailureProfile_two_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_two_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.articulationPoints_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPoints_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_articulationPoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_articulationPoints

/-- info: 'MonoidProduct.Graph.mem_deletionPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_deletionPartition

/--
info: 'MonoidProduct.Graph.deletionPartition_eq_vertexFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.deletionPartition_eq_vertexFailureProfile

/-- info: 'MonoidProduct.Graph.articulationPartitions_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPartitions_eq_some_iff

/-- info: 'MonoidProduct.Graph.articulationPartitions_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPartitions_eq_none_iff

/--
info: 'MonoidProduct.Graph.articulationPartitions_eq_of_vertexFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPartitions_eq_of_vertexFailureProfile

/--
info: 'MonoidProduct.Graph.articulationPartitions_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.articulationPartitions_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_articulationPartitions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_articulationPartitions

/-- info: 'MonoidProduct.Graph.isVertexConnected_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isVertexConnected_eq_true_iff

/--
info: 'MonoidProduct.Graph.isVertexConnected_iff_vertexFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.isVertexConnected_iff_vertexFailureProfile

/--
info: 'MonoidProduct.Graph.isVertexConnected_eq_of_vertexFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.isVertexConnected_eq_of_vertexFailureProfile

/-- info: 'MonoidProduct.Graph.isVertexConnected_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isVertexConnected_one_iff

/--
info: 'MonoidProduct.Graph.vertexConnectivity_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexConnectivity_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_isVertexConnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_isVertexConnected

/-- info: 'MonoidProduct.Graph.mem_edgesWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_edgesWithin

/-- info: 'MonoidProduct.Graph.mem_edgesWithin_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_edgesWithin_of_eq

/-- info: 'MonoidProduct.Graph.edgesWithin_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgesWithin_subset

/-- info: 'MonoidProduct.Graph.edgesWithin_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgesWithin_mono

/-- info: 'MonoidProduct.Graph.toGraph_edgesWithin_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_edgesWithin_adj

/-- info: 'MonoidProduct.Graph.edgesWithin_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgesWithin_union

/-- info: 'MonoidProduct.Graph.edgesWithin_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.edgesWithin_univ

/-- info: 'MonoidProduct.Graph.exists_reachable_induce_of_walk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_reachable_induce_of_walk

/-- info: 'MonoidProduct.Graph.reachable_induce_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_induce_iff

/-- info: 'MonoidProduct.Graph.toGraph_edgesWithin_compl_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.toGraph_edgesWithin_compl_adj

/-- info: 'MonoidProduct.Graph.eq_of_reachable_edgesWithin_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.eq_of_reachable_edgesWithin_compl

/-- info: 'MonoidProduct.Graph.reachable_induce_compl_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_induce_compl_iff

/--
info: 'MonoidProduct.Graph.mem_vertexFailureProfile_iff_edgesWithin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_vertexFailureProfile_iff_edgesWithin

/-- info: 'MonoidProduct.Graph.reachable_edgesWithin_compl_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.reachable_edgesWithin_compl_iff

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_eq_iff

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_union_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_union_congr

/-- info: 'MonoidProduct.Graph.extensionEquiv_vertexFailureProfile_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.extensionEquiv_vertexFailureProfile_iff

/--
info: 'MonoidProduct.Graph.isStrongCertificate_vertexFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.isStrongCertificate_vertexFailureProfile

/-- info: 'MonoidProduct.Graph.not_separable_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.not_separable_of_mem

/-- info: 'MonoidProduct.Graph.Separable.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.Separable.mono

/-- info: 'MonoidProduct.Graph.blocking_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.blocking_empty

/-- info: 'MonoidProduct.Graph.greedyStep_of_separable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.greedyStep_of_separable

/-- info: 'MonoidProduct.Graph.greedyStep_of_not_separable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.greedyStep_of_not_separable

/-- info: 'MonoidProduct.Graph.subset_greedyStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.subset_greedyStep

/-- info: 'MonoidProduct.Graph.greedyStep_subset_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.greedyStep_subset_insert

/-- info: 'MonoidProduct.Graph.mem_or_not_separable_greedyStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_or_not_separable_greedyStep

/-- info: 'MonoidProduct.Graph.Blocking.greedyStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.Blocking.greedyStep

/-- info: 'MonoidProduct.Graph.foldl_greedyStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.foldl_greedyStep

/-- info: 'MonoidProduct.Graph.greedyCert_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.greedyCert_subset

/-- info: 'MonoidProduct.Graph.blocking_greedyCert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.blocking_greedyCert

/-- info: 'MonoidProduct.Graph.mem_or_not_separable_greedyCert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_or_not_separable_greedyCert

/-- info: 'MonoidProduct.Graph.vertexFailureProfile_greedyCert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_greedyCert

/-- info: 'MonoidProduct.Graph.isStrongCertificate_greedyCert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.isStrongCertificate_greedyCert

/-- info: 'MonoidProduct.Graph.card_edgesWithin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_edgesWithin_le

/-- info: 'MonoidProduct.Graph.card_edgesWithin_erase_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_edgesWithin_erase_add

/-- info: 'MonoidProduct.Graph.card_filter_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_filter_mem_le

/-- info: 'MonoidProduct.Graph.ne_of_edge_eq_mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.ne_of_edge_eq_mk

/-- info: 'MonoidProduct.Graph.mem_of_mem_edgesWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.mem_of_mem_edgesWithin

/-- info: 'MonoidProduct.Graph.card_edgesWithin_le_of_blocking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_edgesWithin_le_of_blocking

/-- info: 'MonoidProduct.Graph.card_le_of_blocking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_le_of_blocking

/-- info: 'MonoidProduct.Graph.card_greedyCert_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.card_greedyCert_le

/-- info: 'MonoidProduct.Graph.exists_vertexFailureCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.Graph.exists_vertexFailureCertificate

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_vertexFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_vertexFailureProfile

/--
info: 'MonoidProduct.Graph.vertexFailureProfile_strongCertificateSize_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_strongCertificateSize_le

/--
info: 'MonoidProduct.Graph.hasStrongCertificateBound_min_vertexFailureProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.hasStrongCertificateBound_min_vertexFailureProfile

/--
info: 'MonoidProduct.Graph.vertexFailureProfile_strongCertificateSize_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_strongCertificateSize_mono

/--
info: 'MonoidProduct.Graph.vertexFailureProfile_zero_strongCertificateSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_zero_strongCertificateSize

/--
info: 'MonoidProduct.Graph.vertexFailureProfile_one_strongCertificateSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MonoidProduct.Graph.vertexFailureProfile_one_strongCertificateSize

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

/-! ## The sampling and rank-doubling lemmas (Section 7, `lem:beta-sampling`, `lem:beta-rank-doubling`) -/

/-- info: 'MonoidProduct.beta_sampling_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.beta_sampling_explicit

/-- info: 'MonoidProduct.beta_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.beta_sampling

/-- info: 'MonoidProduct.amp_fail_le_of_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.amp_fail_le_of_weight

/-- info: 'MonoidProduct.copy_fail_le_of_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.copy_fail_le_of_weight

/-- info: 'MonoidProduct.path_sum_le_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.path_sum_le_of

/-- info: 'MonoidProduct.all_sum_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.all_sum_eq_of

/-- info: 'MonoidProduct.path_cost_le_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.path_cost_le_of

/-- info: 'MonoidProduct.dblCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.dblCost_le

/-- info: 'MonoidProduct.isWeight_dblW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.isWeight_dblW

/-- info: 'MonoidProduct.dblFamily_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.dblFamily_spec

/-- info: 'MonoidProduct.dblFamily_fail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.dblFamily_fail_le

/-- info: 'MonoidProduct.hasDual_copyOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.hasDual_copyOut

/-- info: 'MonoidProduct.hasDual_dblFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.hasDual_dblFamily

/-- info: 'MonoidProduct.summary2_succ_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.summary2_succ_succ_eq

/-- info: 'MonoidProduct.summary2_succ_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.summary2_succ_zero_eq

/-- info: 'MonoidProduct.rank_doubling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MonoidProduct.rank_doubling

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
