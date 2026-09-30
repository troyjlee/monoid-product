import MonoidProduct.Matroid.Quantum
set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# Selection and distinct types

This file formalizes the selection examples following `thm:matroid-basis-query` in
`monoid.tex` (section `sec:matroid-bases`): for a uniform rank-`k` matroid on distinct input
elements the canonical minimum-weight basis consists of the `k` smallest weights; a partition
matroid with capacity one in each part selects a minimum-weight representative of each
occurring type; truncating its rank to `k` selects the `k` cheapest distinct types, or all
types if fewer occur.

The matroids are constructed here:

* `uniformRankMatroid α k`: a set is independent when it has at most `k` elements; its rank
  is `min{|α|, k}` (`eRank_uniformRankMatroid`), and its closure and rank functions are
  `mem_closure_uniformRankMatroid_iff` and `eRk_uniformRankMatroid`.
* `typeRankMatroid τ k`, for a type map `τ : E → K`: the uniform matroid on the types, pulled
  back along `τ`.  A set is independent when its elements have distinct types and there are
  at most `k` of them (`typeRankMatroid_indep_iff`); its rank is the number of types
  occurring in `E`, capped at `k` (`eRank_typeRankMatroid`).
* `partitionOneMatroid τ = typeRankMatroid τ |K|`: a set is independent when its elements
  have distinct types (`partitionOneMatroid_indep_iff`); its rank is the number of types
  occurring in `E` (`eRank_partitionOneMatroid`).

The uniform matroid is `typeRankMatroid id k` (`typeRankMatroid_id`).  Ties are broken by
input position throughout: records are compared by `(weight, index)`.

The identification of the canonical basis `basisIndices` with the requested selection, in
terms of the original input:

* `mem_basisIndices_typeRankMatroid_iff_lightest`: a position is selected exactly when its
  record is the lightest of its type and fewer than `k` types have a lighter record;
  `card_basisIndices_typeRankMatroid`: `min{#types, k}` positions are selected;
  `typeRankMatroid_basisIndices_types_distinct`: their types are distinct.
* `mem_basisIndices_partitionOneMatroid_iff`: a position is selected exactly when its record
  is the lightest of its type; `card_basisIndices_partitionOneMatroid`: one per occurring
  type.
* `mem_basisIndices_uniformRankMatroid_iff`: on distinct elements, a position is selected
  exactly when fewer than `k` nonnull positions precede it;
  `card_basisIndices_uniformRankMatroid`: `min{m, k}` positions are selected, `m` the number
  of nonnull positions; `mem_basisIndices_uniformRankMatroid_of_lt`: the selection is
  downward closed.

The query bounds come from `thm:matroid-basis-query` with `r = k` or `r = |K|`:
`typeSelection_qQuery_le_min_sqrt`, `uniformSelection_qQuery_le_min_sqrt`,
`partitionSelection_qQuery_le_min_sqrt` (and the versions returning records).  The statements
`cheapestTypes_select_and_qQuery`, `lightestPerType_select_and_qQuery` and
`smallestWeights_select_and_qQuery` combine the characterization, the count, minimum total
weight and the bound `Q_{1/3} ≤ min{n, 2^18·√(n·r)}`, for every `n` including `n = 0`.
-/

namespace MonoidProduct.Matroid
open Set

/-! ### The uniform matroid -/

section Uniform

variable {α : Type*} {k : ℕ}

/-- The independence axioms of the uniform matroid of rank `k` on all of `α`. -/
def uniformRankIndepMatroid (α : Type*) (k : ℕ) : IndepMatroid α :=
  IndepMatroid.ofBddAugment univ (fun I => I.encard ≤ k) (by simp)
    (fun _ _ hJ hIJ => (encard_le_encard hIJ).trans hJ)
    (fun I J _ hJ hIJ => by
      have hne : (J \ I).Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h
        exact absurd (encard_le_encard (sdiff_eq_empty.1 h)) (not_le.2 hIJ)
      obtain ⟨e, heJ, heI⟩ := hne
      refine ⟨e, heJ, heI, ?_⟩
      rw [encard_insert_of_notMem heI]
      exact (Order.add_one_le_of_lt hIJ).trans hJ)
    ⟨k, fun _ h => h⟩ (fun _ _ => subset_univ _)

/-- The **uniform matroid** of rank `k` on `α`: a set is independent exactly when it has at
most `k` elements. -/
def uniformRankMatroid (α : Type*) (k : ℕ) : _root_.Matroid α :=
  (uniformRankIndepMatroid α k).matroid

@[simp] lemma uniformRankMatroid_ground : (uniformRankMatroid α k).E = univ := rfl

@[simp] lemma uniformRankMatroid_indep_iff {I : Set α} :
    (uniformRankMatroid α k).Indep I ↔ I.encard ≤ k := Iff.rfl

/-- Closure in the uniform matroid: a set spans only itself until it has `k` elements, and
then it spans everything. -/
theorem mem_closure_uniformRankMatroid_iff {X : Set α} {e : α} :
    e ∈ (uniformRankMatroid α k).closure X ↔ e ∈ X ∨ (k : ℕ∞) ≤ X.encard := by
  set U := uniformRankMatroid α k
  rcases le_or_gt (k : ℕ∞) X.encard with hk | hk
  · simp only [hk, or_true, iff_true]
    obtain ⟨Y, hYX, hY⟩ := exists_subset_encard_eq hk
    have hYi : U.Indep Y := by rw [uniformRankMatroid_indep_iff, hY]
    refine U.closure_subset_closure hYX ((hYi.mem_closure_iff).2 ?_)
    by_cases heY : e ∈ Y
    · exact Or.inr heY
    · refine Or.inl ⟨fun h => ?_, subset_univ _⟩
      rw [uniformRankMatroid_indep_iff, encard_insert_of_notMem heY, hY] at h
      exact absurd h (by norm_cast; omega)
  · have hXi : U.Indep X := by rw [uniformRankMatroid_indep_iff]; exact hk.le
    rw [hXi.mem_closure_iff]
    simp only [not_le.2 hk, or_false]
    refine or_iff_right fun h => h.1 ?_
    rw [uniformRankMatroid_indep_iff]
    exact (encard_insert_le X e).trans (Order.add_one_le_of_lt hk)

/-- Rank in the uniform matroid: `rk X = min{|X|, k}`. -/
theorem eRk_uniformRankMatroid (X : Set α) :
    (uniformRankMatroid α k).eRk X = min X.encard k := by
  set U := uniformRankMatroid α k
  rcases le_or_gt (k : ℕ∞) X.encard with hk | hk
  · rw [min_eq_right hk]
    obtain ⟨Y, hYX, hY⟩ := exists_subset_encard_eq hk
    have hYi : U.Indep Y := by rw [uniformRankMatroid_indep_iff, hY]
    have hB : U.IsBasis Y X := by
      refine hYi.isBasis_of_forall_insert hYX fun e he => ⟨fun h => ?_, subset_univ _⟩
      rw [uniformRankMatroid_indep_iff, encard_insert_of_notMem he.2, hY] at h
      exact absurd h (by norm_cast; omega)
    rw [← hB.encard_eq_eRk, hY]
  · rw [min_eq_left hk.le]
    exact (uniformRankMatroid_indep_iff.2 hk.le).eRk_eq_encard

/-- The rank of the uniform matroid is `min{|α|, k}`. -/
theorem eRank_uniformRankMatroid : (uniformRankMatroid α k).eRank = min (ENat.card α) k := by
  rw [← _root_.Matroid.eRk_ground, uniformRankMatroid_ground, eRk_uniformRankMatroid,
    encard_univ]

lemma eRank_uniformRankMatroid_le : (uniformRankMatroid α k).eRank ≤ k := by
  rw [eRank_uniformRankMatroid]; exact min_le_right _ _

end Uniform

/-! ### Partition matroids with capacity one, and their truncations -/

section Types

variable {E K : Type*} {τ : E → K} {k : ℕ}

/-- The **truncated partition matroid** with capacity one in each part: the parts are the
fibres of the type map `τ : E → K`, and a set is independent exactly when its elements have
distinct types and there are at most `k` of them. -/
def typeRankMatroid (τ : E → K) (k : ℕ) : _root_.Matroid E :=
  (uniformRankMatroid K k).comap τ

@[simp] lemma typeRankMatroid_ground : (typeRankMatroid τ k).E = univ := by
  simp [typeRankMatroid]

lemma typeRankMatroid_indep_iff {I : Set E} :
    (typeRankMatroid τ k).Indep I ↔ InjOn τ I ∧ I.encard ≤ k := by
  rw [typeRankMatroid, _root_.Matroid.comap_indep_iff, uniformRankMatroid_indep_iff]
  constructor
  · rintro ⟨h, hinj⟩; exact ⟨hinj, hinj.encard_image ▸ h⟩
  · rintro ⟨hinj, h⟩; exact ⟨hinj.encard_image ▸ h, hinj⟩

/-- Closure in the truncated partition matroid: `e` is spanned by `X` exactly when its type
already occurs in `X`, or `X` already has `k` distinct types. -/
theorem mem_closure_typeRankMatroid_iff {X : Set E} {e : E} :
    e ∈ (typeRankMatroid τ k).closure X ↔ τ e ∈ τ '' X ∨ (k : ℕ∞) ≤ (τ '' X).encard := by
  rw [typeRankMatroid, _root_.Matroid.comap_closure_eq, mem_preimage,
    mem_closure_uniformRankMatroid_iff]

/-- Rank in the truncated partition matroid: the number of distinct types, capped at `k`. -/
theorem eRk_typeRankMatroid (X : Set E) :
    (typeRankMatroid τ k).eRk X = min (τ '' X).encard k := by
  rw [typeRankMatroid, _root_.Matroid.eRk_comap, eRk_uniformRankMatroid]

/-- The rank of the truncated partition matroid: the number of types that occur in `E`,
capped at `k`. -/
theorem eRank_typeRankMatroid : (typeRankMatroid τ k).eRank = min (range τ).encard k := by
  rw [← _root_.Matroid.eRk_ground, typeRankMatroid_ground, eRk_typeRankMatroid, image_univ]

lemma eRank_typeRankMatroid_le : (typeRankMatroid τ k).eRank ≤ k := by
  rw [eRank_typeRankMatroid]; exact min_le_right _ _

/-- With the identity type map, the truncated partition matroid is the uniform matroid. -/
lemma typeRankMatroid_id : typeRankMatroid (id : E → E) k = uniformRankMatroid E k :=
  _root_.Matroid.comap_id _

variable [Fintype K]

/-- The **partition matroid** with capacity one in each part: the parts are the fibres of
`τ : E → K`, and a set is independent exactly when its elements have distinct types. -/
def partitionOneMatroid (τ : E → K) : _root_.Matroid E :=
  typeRankMatroid τ (Fintype.card K)

@[simp] lemma partitionOneMatroid_ground : (partitionOneMatroid τ).E = univ :=
  typeRankMatroid_ground

lemma encard_image_le_card (X : Set E) : (τ '' X).encard ≤ Fintype.card K := by
  rw [← ENat.card_eq_coe_fintype_card, ← encard_univ]
  exact encard_le_encard (subset_univ _)

lemma partitionOneMatroid_indep_iff {I : Set E} :
    (partitionOneMatroid τ).Indep I ↔ InjOn τ I := by
  rw [partitionOneMatroid, typeRankMatroid_indep_iff, and_iff_left_iff_imp]
  intro hinj
  rw [← hinj.encard_image]
  exact encard_image_le_card I

/-- The rank of the partition matroid is the number of types that occur in `E`. -/
theorem eRank_partitionOneMatroid : (partitionOneMatroid τ).eRank = (range τ).encard := by
  rw [partitionOneMatroid, eRank_typeRankMatroid, ← image_univ]
  exact min_eq_left (encard_image_le_card _)

lemma eRank_partitionOneMatroid_le : (partitionOneMatroid τ).eRank ≤ Fintype.card K :=
  eRank_typeRankMatroid_le

end Types

/-! ### The selected positions -/

section Selection

variable {ι E W K : Type*} [LinearOrder ι] [LinearOrder E] [LinearOrder W]
variable {x : ι → Option (E × W)} {T : Finset ι} {i : ι} {τ : E → K} {k : ℕ}

open Classical in
/-- The positions of `T` holding a nonnull record that precedes the key `(w, i)` in the order
by `(weight, index)`. -/
noncomputable def lighterPositions (x : ι → Option (E × W)) (T : Finset ι) (w : W) (i : ι) :
    Finset ι :=
  T.filter fun j => ∃ e' w', x j = some (e', w') ∧ toLex (w', j) < toLex (w, i)

lemma mem_lighterPositions {w : W} {j : ι} :
    j ∈ lighterPositions x T w i ↔
      j ∈ T ∧ ∃ e' w', x j = some (e', w') ∧ toLex (w', j) < toLex (w, i) := by
  classical
  simp only [lighterPositions, Finset.mem_filter]

lemma inputElements_lighterPositions (w : W) :
    inputElements x (lighterPositions x T w i) =
      {e' | ∃ j ∈ T, ∃ w', x j = some (e', w') ∧ toLex (w', j) < toLex (w, i)} := by
  ext e'
  simp only [inputElements, mem_lighterPositions, mem_ofPred_eq]
  constructor
  · rintro ⟨j, ⟨hj, e'', w'', hx', hlt⟩, w', hx⟩
    rw [hx, Option.some.injEq, Prod.mk.injEq] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    exact ⟨j, hj, w', hx, hlt⟩
  · rintro ⟨j, hj, w', hx, hlt⟩
    exact ⟨j, ⟨hj, e', w', hx, hlt⟩, w', hx⟩

/-- The types occurring at the positions lighter than the key `(w, i)`. -/
def lighterTypes (τ : E → K) (x : ι → Option (E × W)) (T : Finset ι) (w : W) (i : ι) :
    Set K :=
  τ '' inputElements x (lighterPositions x T w i)

/-- The types occurring at the positions of `T`. -/
def inputTypes (τ : E → K) (x : ι → Option (E × W)) (T : Finset ι) : Set K :=
  τ '' inputElements x T

/-- If the positions of `I` hold nonnull records of pairwise distinct types, then `I` has as
many positions as there are types among them. -/
theorem encard_image_inputElements_eq_card {I : Finset ι} (hs : ∀ i ∈ I, (x i).isSome)
    (hd : ∀ i ∈ I, ∀ j ∈ I, ∀ (e e' : E) (w w' : W), x i = some (e, w) →
      x j = some (e', w') → τ e = τ e' → i = j) :
    (τ '' inputElements x I).encard = I.card := by
  rw [← image_element_records, image_image]
  have hinj : InjOn (fun r : WeightedRecord ι E W => τ r.element) (records x I : Set _) := by
    intro r hr s hs' h
    obtain ⟨hri, hrx⟩ := mem_records.1 hr
    obtain ⟨hsi, hsx⟩ := mem_records.1 hs'
    exact records_injOn_index hr hs' (hd _ hri _ hsi _ _ _ _ hrx hsx h)
  have hc : (records x I).card = I.card := by
    conv_rhs => rw [← image_index_records_of_isSome hs]
    exact (Finset.card_image_of_injOn records_injOn_index).symm
  rw [hinj.encard_image, encard_coe_eq_coe_finsetCard, hc]

/-- **Selected positions of the truncated partition matroid**: position `i ∈ T` is
selected exactly when its record `(e, w)` is nonnull, no lighter position has the type of
`e`, and fewer than `k` types occur at lighter positions. -/
theorem mem_basisIndices_typeRankMatroid_iff :
    i ∈ basisIndices (typeRankMatroid τ k) x T ↔ i ∈ T ∧ ∃ e w, x i = some (e, w) ∧
      τ e ∉ lighterTypes τ x T w i ∧ (lighterTypes τ x T w i).encard < k := by
  rw [mem_basisIndices_iff]
  refine and_congr_right fun _ => exists_congr fun e => exists_congr fun w => and_congr_right
    fun _ => ?_
  rw [← inputElements_lighterPositions, mem_closure_typeRankMatroid_iff, not_or, not_le]
  rfl

/-- A type is absent from the lighter positions exactly when the key `(w, i)` is the lightest
among the records of that type. -/
lemma notMem_lighterTypes_iff {e : E} {w : W} :
    τ e ∉ lighterTypes τ x T w i ↔ ∀ j ∈ T, ∀ (e' : E) (w' : W), x j = some (e', w') →
      τ e' = τ e → toLex (w, i) ≤ toLex (w', j) := by
  rw [lighterTypes, inputElements_lighterPositions]
  constructor
  · intro h j hj e' w' hx ht
    by_contra hlt
    exact h ⟨e', ⟨j, hj, w', hx, not_le.1 hlt⟩, ht⟩
  · rintro h ⟨e', ⟨j, hj, w', hx, hlt⟩, ht⟩
    exact absurd (h j hj e' w' hx ht) (not_le.2 hlt)

/-- **Truncated partition matroid: the cheapest distinct types** (`sec:matroid-bases`).
Position `i ∈ T` is selected exactly when its record `(e, w)` is the lightest record of its
type `τ e` in the order by `(weight, index)`, and fewer than `k` other types have a lighter
record: one lightest representative of each of the `k` cheapest types is selected. -/
theorem mem_basisIndices_typeRankMatroid_iff_lightest :
    i ∈ basisIndices (typeRankMatroid τ k) x T ↔ i ∈ T ∧ ∃ e w, x i = some (e, w) ∧
      (∀ j ∈ T, ∀ (e' : E) (w' : W), x j = some (e', w') → τ e' = τ e →
        toLex (w, i) ≤ toLex (w', j)) ∧ (lighterTypes τ x T w i).encard < k := by
  simp only [mem_basisIndices_typeRankMatroid_iff, notMem_lighterTypes_iff]

/-- Parallel-copy independence in the truncated partition matroid: nonnull records of
pairwise distinct types, at most `k` of them. -/
theorem isParallelIndep_typeRankMatroid_iff {I : Finset ι} :
    IsParallelIndep (typeRankMatroid τ k) x I ↔ (∀ i ∈ I, (x i).isSome) ∧
      (∀ i ∈ I, ∀ j ∈ I, ∀ (e e' : E) (w w' : W), x i = some (e, w) →
        x j = some (e', w') → τ e = τ e' → i = j) ∧ I.card ≤ k := by
  rw [IsParallelIndep, typeRankMatroid_indep_iff]
  constructor
  · rintro ⟨hs, hel, hinj, hk⟩
    have hd : ∀ i ∈ I, ∀ j ∈ I, ∀ (e e' : E) (w w' : W), x i = some (e, w) →
        x j = some (e', w') → τ e = τ e' → i = j := by
      intro i hi j hj e e' w w' hx hy ht
      have hee : e = e' := hinj ⟨i, hi, w, hx⟩ ⟨j, hj, w', hy⟩ ht
      exact hel i hi j hj e w w' hx (hee ▸ hy)
    refine ⟨hs, hd, ?_⟩
    have h := encard_image_inputElements_eq_card hs hd
    rw [hinj.encard_image] at h
    exact_mod_cast h ▸ hk
  · rintro ⟨hs, hd, hk⟩
    have hinj : InjOn τ (inputElements x I) := by
      rintro e ⟨i, hi, w, hx⟩ e' ⟨j, hj, w', hy⟩ ht
      have hij := hd i hi j hj e e' w w' hx hy ht
      rw [hij, hy, Option.some.injEq, Prod.mk.injEq] at hx
      exact hx.1.symm
    refine ⟨hs, fun i hi j hj e w w' hx hy => hd i hi j hj e e w w' hx hy rfl, hinj, ?_⟩
    rw [← hinj.encard_image, encard_image_inputElements_eq_card hs hd]
    exact_mod_cast hk

/-- The number of selected positions equals the rank of the occurring elements. -/
theorem card_basisIndices_eq_eRk {M : _root_.Matroid E} (hM : M.E = univ) :
    ((basisIndices M x T).card : ℕ∞) = M.eRk (inputElements x T) := by
  obtain ⟨hB, hinj⟩ := isBasis_image_element_basisRecords hM x T
  rw [card_basisIndices, ← hB.encard_eq_eRk, hinj.encard_image, encard_coe_eq_coe_finsetCard]

/-- **The truncated partition matroid selects `min{k, #types}` positions**: the cheapest `k`
types, or all occurring types if fewer than `k` occur. -/
theorem card_basisIndices_typeRankMatroid :
    ((basisIndices (typeRankMatroid τ k) x T).card : ℕ∞) = min (inputTypes τ x T).encard k := by
  rw [card_basisIndices_eq_eRk typeRankMatroid_ground, eRk_typeRankMatroid, inputTypes]

/-- The selected positions have pairwise distinct types. -/
theorem typeRankMatroid_basisIndices_types_distinct {j : ι} {e e' : E} {w w' : W}
    (hi : i ∈ basisIndices (typeRankMatroid τ k) x T)
    (hj : j ∈ basisIndices (typeRankMatroid τ k) x T)
    (hx : x i = some (e, w)) (hy : x j = some (e', w')) (ht : τ e = τ e') : i = j :=
  (isParallelIndep_typeRankMatroid_iff.1
    (isParallelIndep_basisIndices typeRankMatroid_ground x T)).2.1 i hi j hj e e' w w' hx hy ht

lemma lighterPositions_mono {w w' : W} {j : ι} (hlt : toLex (w', j) < toLex (w, i)) :
    lighterPositions x T w' j ⊆ lighterPositions x T w i := fun l hl => by
  obtain ⟨hlT, e'', w'', hx, hl'⟩ := mem_lighterPositions.1 hl
  exact mem_lighterPositions.2 ⟨hlT, e'', w'', hx, hl'.trans hlt⟩

/-- **The selection is downward closed**: if `i` is selected and `j` holds the lightest
record of its type and precedes `i` in the order by `(weight, index)`, then `j` is selected
too. -/
theorem mem_basisIndices_typeRankMatroid_of_lt {j : ι} {e e' : E} {w w' : W}
    (hi : i ∈ basisIndices (typeRankMatroid τ k) x T) (hxi : x i = some (e, w))
    (hjT : j ∈ T) (hxj : x j = some (e', w')) (hlt : toLex (w', j) < toLex (w, i))
    (hmin : τ e' ∉ lighterTypes τ x T w' j) :
    j ∈ basisIndices (typeRankMatroid τ k) x T := by
  obtain ⟨-, e₀, w₀, hx₀, -, hk⟩ := mem_basisIndices_typeRankMatroid_iff.1 hi
  rw [hxi, Option.some.injEq, Prod.mk.injEq] at hx₀
  obtain ⟨rfl, rfl⟩ := hx₀
  refine mem_basisIndices_typeRankMatroid_iff.2 ⟨hjT, e', w', hxj, hmin,
    lt_of_le_of_lt (encard_le_encard ?_) hk⟩
  exact image_mono (inputElements_mono (lighterPositions_mono hlt))

/-- Minimum total weight of the type selection, in terms of the original input: the
selected positions weigh at most any maximal set of positions of `T` holding nonnull
records of pairwise distinct types, at most `k` of them (`isParallelIndep_typeRankMatroid_iff`
spells out this independence). -/
theorem basisIndices_typeRankMatroid_minWeight (weight : W ↪o ℝ) {J : Finset ι}
    (hJ : IsParallelBasis (typeRankMatroid τ k) x T J) :
    ∑ i ∈ basisIndices (typeRankMatroid τ k) x T, inputWeight weight x i ≤
      ∑ i ∈ J, inputWeight weight x i :=
  (basisRecords_isMinimumWeightBasis typeRankMatroid_ground weight x T).2.2.2 J hJ

/-! #### One lightest record of each type -/

section Partition

variable [Fintype K]

/-- **Partition matroid: one lightest representative of each type** (`sec:matroid-bases`).
Position `i ∈ T` is selected exactly when its record `(e, w)` is the lightest record of its
type `τ e` in the order by `(weight, index)`. -/
theorem mem_basisIndices_partitionOneMatroid_iff :
    i ∈ basisIndices (partitionOneMatroid τ) x T ↔ i ∈ T ∧ ∃ e w, x i = some (e, w) ∧
      ∀ j ∈ T, ∀ (e' : E) (w' : W), x j = some (e', w') → τ e' = τ e →
        toLex (w, i) ≤ toLex (w', j) := by
  rw [partitionOneMatroid, mem_basisIndices_typeRankMatroid_iff]
  refine and_congr_right fun _ => exists_congr fun e => exists_congr fun w => and_congr_right
    fun _ => ?_
  rw [← notMem_lighterTypes_iff, and_iff_left_iff_imp]
  intro he
  rw [← ENat.card_eq_coe_fintype_card, ← encard_univ]
  exact (toFinite _).encard_lt_encard (ssubset_univ_iff.2 fun h => he (h ▸ mem_univ _))

/-- Every occurring type has exactly one selected position: the number of selected positions
is the number of occurring types. -/
theorem card_basisIndices_partitionOneMatroid :
    ((basisIndices (partitionOneMatroid τ) x T).card : ℕ∞) = (inputTypes τ x T).encard := by
  rw [partitionOneMatroid, card_basisIndices_typeRankMatroid]
  exact min_eq_left (encard_image_le_card _)

end Partition

/-! #### The `k` lightest records on distinct elements -/

/-- The input elements are **distinct**: no element occurs at two positions. -/
def InputElementsDistinct (x : ι → Option (E × W)) : Prop :=
  ∀ (i j : ι) (e : E) (w w' : W), x i = some (e, w) → x j = some (e, w') → i = j

lemma notMem_lighterTypes_id (hd : InputElementsDistinct x) {e : E} {w : W}
    (hx : x i = some (e, w)) : id e ∉ lighterTypes id x T w i := by
  rintro ⟨e', ⟨j, hj, w', hy⟩, he⟩
  obtain ⟨-, e'', w'', hy', hlt⟩ := mem_lighterPositions.1 hj
  rw [id, id] at he
  subst he
  obtain rfl := hd _ _ _ _ _ hx hy
  rw [hx, Option.some.injEq, Prod.mk.injEq] at hy'
  obtain ⟨-, rfl⟩ := hy'
  exact lt_irrefl _ hlt

lemma encard_lighterTypes_id (hd : InputElementsDistinct x) (w : W) :
    (lighterTypes id x T w i).encard = (lighterPositions x T w i).card := by
  refine encard_image_inputElements_eq_card (fun j hj => ?_)
    fun j _ l _ e e' w₁ w₂ hx hy he => hd j l e w₁ w₂ hx (by rw [show e = e' from he]; exact hy)
  obtain ⟨-, e', w', hx, -⟩ := mem_lighterPositions.1 hj
  rw [hx]; rfl

/-- **Uniform matroid: the `k` lightest records** (`sec:matroid-bases`).  On an input whose
elements are distinct, position `i ∈ T` is selected exactly when its record `(e, w)` is
nonnull and fewer than `k` nonnull positions of `T` precede it in the order by
`(weight, index)`. -/
theorem mem_basisIndices_uniformRankMatroid_iff (hd : InputElementsDistinct x) :
    i ∈ basisIndices (uniformRankMatroid E k) x T ↔ i ∈ T ∧ ∃ e w, x i = some (e, w) ∧
      (lighterPositions x T w i).card < k := by
  rw [← typeRankMatroid_id, mem_basisIndices_typeRankMatroid_iff]
  refine and_congr_right fun _ => exists_congr fun e => exists_congr fun w => and_congr_right
    fun hx => ?_
  rw [encard_lighterTypes_id hd, and_iff_right (notMem_lighterTypes_id hd hx)]
  exact_mod_cast Iff.rfl

/-- The uniform selection is downward closed in the order by `(weight, index)`. -/
theorem mem_basisIndices_uniformRankMatroid_of_lt (hd : InputElementsDistinct x) {j : ι}
    {e e' : E} {w w' : W} (hi : i ∈ basisIndices (uniformRankMatroid E k) x T)
    (hxi : x i = some (e, w)) (hjT : j ∈ T) (hxj : x j = some (e', w'))
    (hlt : toLex (w', j) < toLex (w, i)) :
    j ∈ basisIndices (uniformRankMatroid E k) x T := by
  rw [← typeRankMatroid_id] at hi ⊢
  exact mem_basisIndices_typeRankMatroid_of_lt hi hxi hjT hxj hlt
    (notMem_lighterTypes_id hd hxj)

/-- **The uniform matroid selects `min{k, m}` positions**, where `m` is the number of nonnull
positions of `T`: the `k` lightest records, or all of them if fewer than `k` occur. -/
theorem card_basisIndices_uniformRankMatroid (hd : InputElementsDistinct x) :
    ((basisIndices (uniformRankMatroid E k) x T).card : ℕ∞) =
      min ((T.filter fun i => (x i).isSome).card : ℕ∞) k := by
  rw [← typeRankMatroid_id, card_basisIndices_typeRankMatroid, inputTypes]
  congr 1
  have hI : inputElements x (T.filter fun i => (x i).isSome) = inputElements x T := by
    ext e
    simp only [inputElements, Finset.mem_filter, mem_ofPred_eq]
    constructor
    · rintro ⟨i, ⟨hi, -⟩, w, hx⟩; exact ⟨i, hi, w, hx⟩
    · rintro ⟨i, hi, w, hx⟩; exact ⟨i, ⟨hi, by rw [hx]; rfl⟩, w, hx⟩
  rw [← hI]
  exact encard_image_inputElements_eq_card (fun i hi => (Finset.mem_filter.1 hi).2)
    fun j _ l _ e e' w₁ w₂ hx hy he => hd j l e w₁ w₂ hx (by rw [show e = e' from he]; exact hy)

end Selection

/-! ### Query bounds -/

section Quantum

open QuantumQueryComplexity

variable {E W : Type} [Fintype E] [LinearOrder E] [Fintype W] [LinearOrder W] {K : Type*}

/-- **Cheapest distinct types, operational** (`thm:matroid-basis-query` with the truncated
partition matroid, `r = k`): selecting one lightest record of each of the `k` cheapest types
costs `Q_{1/3} ≤ min{n, 2^18·√(n·k)}`. -/
theorem typeSelection_qQuery_le_min_sqrt (τ : E → K) (k n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) =>
        basisIndices (typeRankMatroid τ k) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * k)) :=
  matroidBasisIndices_qQuery_le_min_sqrt typeRankMatroid_ground eRank_typeRankMatroid_le n

/-- The same bound for the selected records together with their positions. -/
theorem typeSelectionRecords_qQuery_le_min_sqrt (τ : E → K) (k n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) =>
        basisRecords (typeRankMatroid τ k) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * k)) :=
  matroidBasisRecords_qQuery_le_min_sqrt typeRankMatroid_ground eRank_typeRankMatroid_le n

/-- At `k = 0` nothing is selected and no query is needed. -/
theorem typeSelection_qQuery_eq_zero (τ : E → K) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → Option (E × W) =>
      basisIndices (typeRankMatroid τ 0) x Finset.univ) ε = 0 :=
  matroidBasisIndices_qQuery_eq_zero typeRankMatroid_ground
    (le_antisymm (by exact_mod_cast eRank_typeRankMatroid_le) zero_le) n hε

/-- **Uniform selection, operational** (`thm:matroid-basis-query` with the uniform matroid,
`r = k`): `Q_{1/3} ≤ min{n, 2^18·√(n·k)}`. -/
theorem uniformSelection_qQuery_le_min_sqrt (k n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) =>
        basisIndices (uniformRankMatroid E k) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * k)) :=
  matroidBasisIndices_qQuery_le_min_sqrt uniformRankMatroid_ground eRank_uniformRankMatroid_le n

/-- The same bound for the selected records together with their positions. -/
theorem uniformSelectionRecords_qQuery_le_min_sqrt (k n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) =>
        basisRecords (uniformRankMatroid E k) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * k)) :=
  matroidBasisRecords_qQuery_le_min_sqrt uniformRankMatroid_ground eRank_uniformRankMatroid_le n

variable [Fintype K]

/-- **One lightest record per type, operational** (`thm:matroid-basis-query` with the
partition matroid, `r = |K|` the number of types): `Q_{1/3} ≤ min{n, 2^18·√(n·|K|)}`. -/
theorem partitionSelection_qQuery_le_min_sqrt (τ : E → K) (n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) =>
        basisIndices (partitionOneMatroid τ) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * Fintype.card K)) :=
  typeSelection_qQuery_le_min_sqrt τ (Fintype.card K) n

/-- The same bound for the selected records together with their positions. -/
theorem partitionSelectionRecords_qQuery_le_min_sqrt (τ : E → K) (n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) =>
        basisRecords (partitionOneMatroid τ) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * Fintype.card K)) :=
  typeSelectionRecords_qQuery_le_min_sqrt τ (Fintype.card K) n

omit [Fintype K] in
/-- **The `k` cheapest distinct types** (`sec:matroid-bases`, truncated partition matroid).
For every input `x : Fin n → Option (E × W)`,
1. position `i` is selected exactly when its record `(e, w)` is nonnull, is the lightest
   record of its type in the order by `(weight, index)`, and fewer than `k` types have a
   lighter record;
2. the number of selected positions is `min{#types occurring, k}`;
3. the selected positions have minimum total weight among all maximal sets of positions
   holding nonnull records of distinct types, at most `k` of them;

and computing the selected positions costs `Q_{1/3} ≤ min{n, 2^18·√(n·k)}`. -/
theorem cheapestTypes_select_and_qQuery (τ : E → K) (weight : W ↪o ℝ) (k n : ℕ) :
    (∀ x : Fin n → Option (E × W),
      (∀ i, i ∈ basisIndices (typeRankMatroid τ k) x Finset.univ ↔ ∃ e w, x i = some (e, w) ∧
        (∀ j (e' : E) (w' : W), x j = some (e', w') → τ e' = τ e →
          toLex (w, i) ≤ toLex (w', j)) ∧ (lighterTypes τ x Finset.univ w i).encard < k) ∧
      ((basisIndices (typeRankMatroid τ k) x Finset.univ).card : ℕ∞) =
        min (inputTypes τ x Finset.univ).encard k ∧
      ∀ J : Finset (Fin n), IsParallelBasis (typeRankMatroid τ k) x Finset.univ J →
        ∑ i ∈ basisIndices (typeRankMatroid τ k) x Finset.univ, inputWeight weight x i ≤
          ∑ i ∈ J, inputWeight weight x i) ∧
    (qQuery (fun x : Fin n → Option (E × W) =>
        basisIndices (typeRankMatroid τ k) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * k)) := by
  refine ⟨fun x => ⟨fun i => ?_, card_basisIndices_typeRankMatroid,
    fun J hJ => basisIndices_typeRankMatroid_minWeight weight hJ⟩,
    typeSelection_qQuery_le_min_sqrt τ k n⟩
  simp [mem_basisIndices_typeRankMatroid_iff_lightest]

/-- **A lightest representative of each occurring type** (`sec:matroid-bases`, partition
matroid with capacity one).  For every input `x : Fin n → Option (E × W)`,
1. position `i` is selected exactly when its record `(e, w)` is nonnull and is the lightest
   record of its type in the order by `(weight, index)`;
2. the number of selected positions is the number of occurring types;
3. the selected positions have minimum total weight among all maximal sets of positions
   holding nonnull records of distinct types;

and computing the selected positions costs `Q_{1/3} ≤ min{n, 2^18·√(n·|K|)}`. -/
theorem lightestPerType_select_and_qQuery (τ : E → K) (weight : W ↪o ℝ) (n : ℕ) :
    (∀ x : Fin n → Option (E × W),
      (∀ i, i ∈ basisIndices (partitionOneMatroid τ) x Finset.univ ↔ ∃ e w,
        x i = some (e, w) ∧ ∀ j (e' : E) (w' : W), x j = some (e', w') → τ e' = τ e →
          toLex (w, i) ≤ toLex (w', j)) ∧
      ((basisIndices (partitionOneMatroid τ) x Finset.univ).card : ℕ∞) =
        (inputTypes τ x Finset.univ).encard ∧
      ∀ J : Finset (Fin n), IsParallelBasis (partitionOneMatroid τ) x Finset.univ J →
        ∑ i ∈ basisIndices (partitionOneMatroid τ) x Finset.univ, inputWeight weight x i ≤
          ∑ i ∈ J, inputWeight weight x i) ∧
    (qQuery (fun x : Fin n → Option (E × W) =>
        basisIndices (partitionOneMatroid τ) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * Fintype.card K)) := by
  refine ⟨fun x => ⟨fun i => ?_, card_basisIndices_partitionOneMatroid,
    fun J hJ => basisIndices_typeRankMatroid_minWeight weight hJ⟩,
    partitionSelection_qQuery_le_min_sqrt τ n⟩
  simp [mem_basisIndices_partitionOneMatroid_iff]

omit [Fintype K] in
/-- **The `k` smallest weights** (`sec:matroid-bases`, uniform matroid of rank `k`).  For
every input `x : Fin n → Option (E × W)` whose elements are distinct,
1. position `i` is selected exactly when its record `(e, w)` is nonnull and fewer than `k`
   nonnull positions precede it in the order by `(weight, index)`;
2. the number of selected positions is `min{m, k}`, where `m` is the number of nonnull
   positions;
3. the selected positions have minimum total weight among all maximal sets of at most `k`
   nonnull positions;

and computing the selected positions costs `Q_{1/3} ≤ min{n, 2^18·√(n·k)}` (on all
inputs). -/
theorem smallestWeights_select_and_qQuery (weight : W ↪o ℝ) (k n : ℕ) :
    (∀ x : Fin n → Option (E × W), InputElementsDistinct x →
      (∀ i, i ∈ basisIndices (uniformRankMatroid E k) x Finset.univ ↔ ∃ e w,
        x i = some (e, w) ∧ (lighterPositions x Finset.univ w i).card < k) ∧
      ((basisIndices (uniformRankMatroid E k) x Finset.univ).card : ℕ∞) =
        min ((Finset.univ.filter fun i => (x i).isSome).card : ℕ∞) k ∧
      ∀ J : Finset (Fin n), IsParallelBasis (uniformRankMatroid E k) x Finset.univ J →
        ∑ i ∈ basisIndices (uniformRankMatroid E k) x Finset.univ, inputWeight weight x i ≤
          ∑ i ∈ J, inputWeight weight x i) ∧
    (qQuery (fun x : Fin n → Option (E × W) =>
        basisIndices (uniformRankMatroid E k) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * k)) := by
  refine ⟨fun x hd => ⟨fun i => ?_, card_basisIndices_uniformRankMatroid hd,
    fun J hJ => (basisRecords_isMinimumWeightBasis uniformRankMatroid_ground weight x
      Finset.univ).2.2.2 J hJ⟩, uniformSelection_qQuery_le_min_sqrt k n⟩
  simp [mem_basisIndices_uniformRankMatroid_iff hd]

end Quantum

/-! ### Examples -/

section Examples

variable {ι E W K : Type*} [LinearOrder ι] [LinearOrder E] [LinearOrder W]

/-- All-null input: nothing is selected. -/
example (τ : E → K) (k : ℕ) (x : ι → Option (E × W)) (hx : ∀ i, x i = none) (T : Finset ι) :
    basisIndices (typeRankMatroid τ k) x T = ∅ := by
  ext i
  simp [mem_basisIndices_typeRankMatroid_iff, hx]

/-- At `k = 0` nothing is selected. -/
example (τ : E → K) (x : ι → Option (E × W)) (T : Finset ι) :
    basisIndices (typeRankMatroid τ 0) x T = ∅ := by
  ext i
  simp [mem_basisIndices_typeRankMatroid_iff]

/-- Two records of the same type: the lighter one is selected and the heavier one is not. -/
example [Fintype K] (τ : E → K) {x : ι → Option (E × W)} {i j : ι} {e e' : E} {w w' : W}
    (hi : x i = some (e, w)) (hj : x j = some (e', w')) (ht : τ e = τ e') (hw : w < w') :
    j ∉ basisIndices (partitionOneMatroid τ) x {i, j} := by
  rw [mem_basisIndices_partitionOneMatroid_iff]
  rintro ⟨-, e'', w'', hj', h⟩
  rw [hj, Option.some.injEq, Prod.mk.injEq] at hj'
  obtain ⟨rfl, rfl⟩ := hj'
  exact absurd (h i (by simp) e w hi ht) (not_le.2 (Prod.Lex.toLex_lt_toLex.2 (Or.inl hw)))

end Examples

end MonoidProduct.Matroid
