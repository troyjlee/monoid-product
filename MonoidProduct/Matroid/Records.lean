import MonoidProduct.Matroid.GreedyWeight
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
set_option linter.style.header false

/-!
# Labelled input records and their minimum-weight bases

This file sets up the record universe of `thm:matroid-basis-query` in `monoid.tex`, section
`sec:matroid-bases`, and proves that the greedy basis of the labelled input records is a
minimum-weight basis of the input.

The input is a function `x : ι → Option (E × W)`: position `i` holds either a weighted
element `(e, w)` or a null record.  The **public record universe** is the type
`WeightedRecord ι E W` of triples `(element, weight, index)`.  It carries

* the fixed matroid `recordMatroid M = M.comap WeightedRecord.element`, in which a set of
  records is independent exactly when its element projection is injective with independent
  image: repeated occurrences of an element are parallel copies;
* the fixed **lexicographic** order by `(weight, index, element)` (`WeightedRecord.orderKey`
  is an order embedding into `W ×ₗ ι ×ₗ E`; this is not the product order).

Neither depends on the input.  The input enters only through `records x T`, the finite set
of nonnull records of the positions in `T`, each tagged with its position.  The canonical
answer is `basisRecords M x T = greedy (recordMatroid M) (records x T)`, and
`basisIndices M x T` is its set of positions.

The main results:

* `basisRecords_isMinimumWeightBasis`: every returned record is a truthful record of `x`
  at a position of `T`; the returned records are exactly the input records at the returned
  positions; the returned positions form a basis of the input restriction in the
  parallel-copy model (`IsParallelBasis`); and their total weight is at most that of every
  such basis.  The weights are real numbers through an order embedding `W ↪o ℝ`; they may
  be negative or tied.
* `isBasis_image_element_basisRecords`: the selected elements are distinct and form a basis
  of the elements occurring in the input — not necessarily of the whole ground set.
* `mem_basisIndices_iff`: the selection is greedy in increasing order of `(w_i, i)`; the
  element-order component of the record order never matters on an actual input
  (`lt_iff_of_mem_records`).
* The update laws of the incremental state `T ↦ basisRecords M x T`: the empty state,
  insertion of a fresh position (`records_insert_of_eq_some`, `basisRecords_insert`,
  `basisRecords_insert_congr`), and the deletion criterion `basisRecords_erase_eq_iff`.
-/

namespace MonoidProduct.Matroid

open Set

/-- A **labelled record** of `thm:matroid-basis-query`: a matroid element, a weight symbol,
and an input position. -/
@[ext] structure WeightedRecord (ι E W : Type*) where
  /-- The matroid element of the record. -/
  element : E
  /-- The weight symbol of the record. -/
  weight : W
  /-- The input position of the record. -/
  index : ι

namespace WeightedRecord

variable {ι E W : Type*}

/-- Records are triples. -/
def equivProd : WeightedRecord ι E W ≃ W × ι × E where
  toFun r := (r.weight, r.index, r.element)
  invFun p := ⟨p.2.2, p.1, p.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype ι] [Fintype E] [Fintype W] : Fintype (WeightedRecord ι E W) :=
  Fintype.ofEquiv _ equivProd.symm

variable [LinearOrder ι] [LinearOrder E] [LinearOrder W]

/-- The lexicographic sort key `(weight, index, element)` of a record. -/
def orderKey (r : WeightedRecord ι E W) : W ×ₗ ι ×ₗ E :=
  toLex (r.weight, toLex (r.index, r.element))

omit [LinearOrder ι] [LinearOrder E] [LinearOrder W] in
lemma orderKey_injective : Function.Injective (orderKey (ι := ι) (E := E) (W := W)) := by
  intro r s h
  simp only [orderKey, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact WeightedRecord.ext h₃ h₁ h₂

/-- The public linear order on records: lexicographic by `(weight, index, element)`. -/
instance : LinearOrder (WeightedRecord ι E W) :=
  LinearOrder.lift' orderKey orderKey_injective

lemma le_iff_orderKey {r s : WeightedRecord ι E W} : r ≤ s ↔ r.orderKey ≤ s.orderKey :=
  Iff.rfl

lemma lt_iff_orderKey {r s : WeightedRecord ι E W} : r < s ↔ r.orderKey < s.orderKey :=
  Iff.rfl

/-- `orderKey` as an order embedding into the lexicographic product. -/
def orderKeyEmbedding : WeightedRecord ι E W ↪o W ×ₗ ι ×ₗ E :=
  OrderEmbedding.ofStrictMono orderKey fun _ _ h => h

/-- The record order spelled out: lexicographic by weight, then index, then element. -/
lemma lt_iff_lex {r s : WeightedRecord ι E W} :
    r < s ↔ r.weight < s.weight ∨ r.weight = s.weight ∧
      (r.index < s.index ∨ r.index = s.index ∧ r.element < s.element) := by
  rw [lt_iff_orderKey, orderKey, orderKey, Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex]

/-- The weight is monotone in the record order. -/
lemma weight_le_weight_of_le {r s : WeightedRecord ι E W} (h : r ≤ s) :
    r.weight ≤ s.weight :=
  Prod.Lex.monotone_fst (orderKey r) (orderKey s) h

end WeightedRecord

open WeightedRecord

variable {ι E W : Type*} [LinearOrder ι] [LinearOrder E] [LinearOrder W]

/-- The record universe, as a local abbreviation. -/
local notation "Rec" => WeightedRecord ι E W

/-! ### The public matroid on records -/

/-- The public matroid on records: `M` pulled back along the element projection, so that
records with the same element are parallel copies. -/
def recordMatroid (M : _root_.Matroid E) : _root_.Matroid (WeightedRecord ι E W) :=
  M.comap WeightedRecord.element

variable {M : _root_.Matroid E}

omit [LinearOrder ι] [LinearOrder E] [LinearOrder W] in
lemma recordMatroid_ground (hM : M.E = univ) :
    (recordMatroid (ι := ι) (W := W) M).E = univ := by
  simp [recordMatroid, hM]

omit [LinearOrder ι] [LinearOrder E] [LinearOrder W] in
lemma recordMatroid_indep_iff {R : Set (WeightedRecord ι E W)} :
    (recordMatroid M).Indep R ↔ M.Indep (WeightedRecord.element '' R) ∧
      InjOn WeightedRecord.element R :=
  _root_.Matroid.comap_indep_iff

omit [LinearOrder ι] [LinearOrder E] [LinearOrder W] in
/-- The record matroid has rank at most that of `M`. -/
lemma eRank_recordMatroid_le : (recordMatroid (ι := ι) (W := W) M).eRank ≤ M.eRank := by
  obtain ⟨B, hB⟩ := (recordMatroid (ι := ι) (W := W) M).exists_isBase
  have hI := recordMatroid_indep_iff.1 hB.indep
  rw [← hB.encard_eq_eRank, ← hI.2.encard_image]
  exact hI.1.encard_le_eRank

/-! ### The labelled records of an input -/

/-- Tag a weighted element with the position it occupies. -/
def tagRecord (i : ι) (p : E × W) : WeightedRecord ι E W := ⟨p.1, p.2, i⟩

/-- The **labelled records** of the positions in `T`: the nonnull entries of `x`, each
tagged with its position. -/
def records (x : ι → Option (E × W)) (T : Finset ι) : Finset (WeightedRecord ι E W) :=
  T.biUnion fun i => ((x i).map (tagRecord i)).toFinset

/-- The elements occurring in the input at the positions of `T`. -/
def inputElements (x : ι → Option (E × W)) (T : Finset ι) : Set E :=
  {e | ∃ i ∈ T, ∃ w, x i = some (e, w)}

variable {x y : ι → Option (E × W)} {T : Finset ι} {i : ι}
  {r s : WeightedRecord ι E W}

omit [LinearOrder ι] [LinearOrder E] [LinearOrder W] in
/-- The occurring elements grow with the set of positions. -/
lemma inputElements_mono {I J : Finset ι} (h : I ⊆ J) : inputElements x I ⊆ inputElements x J :=
  fun _ ⟨i, hi, w, hx⟩ => ⟨i, h hi, w, hx⟩

/-- A record belongs to `records x T` exactly when it truthfully records the entry of `x`
at its position, and that position lies in `T`. -/
lemma mem_records :
    r ∈ records x T ↔ r.index ∈ T ∧ x r.index = some (r.element, r.weight) := by
  simp only [records, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, hi, p, hp, rfl⟩
    exact ⟨hi, hp⟩
  · rintro ⟨hi, h⟩
    exact ⟨r.index, hi, _, h, rfl⟩

lemma tagRecord_mem_records {p : E × W} (hi : i ∈ T) (hx : x i = some p) :
    tagRecord i p ∈ records x T :=
  mem_records.2 ⟨hi, hx⟩

@[simp] lemma records_empty (x : ι → Option (E × W)) : records x ∅ = ∅ := by
  simp [records]

lemma records_singleton (x : ι → Option (E × W)) (i : ι) :
    records x {i} = ((x i).map (tagRecord i)).toFinset := by
  simp [records]

/-- The records of a set depend only on the input entries at its positions. -/
lemma records_congr (h : ∀ i ∈ T, x i = y i) : records x T = records y T :=
  Finset.biUnion_congr rfl fun i hi => by rw [h i hi]

lemma records_mono {T' : Finset ι} (h : T ⊆ T') : records x T ⊆ records x T' :=
  fun _ hr => mem_records.2 ⟨h (mem_records.1 hr).1, (mem_records.1 hr).2⟩

lemma records_eq_empty_of_forall (hx : ∀ i ∈ T, x i = none) : records x T = ∅ := by
  ext r
  simp only [mem_records, Finset.notMem_empty, iff_false, not_and]
  intro hi h
  rw [hx _ hi] at h
  exact absurd h (by simp)

/-- Tagging a fresh position: the records of `insert i T` add the record at `i`. -/
lemma records_insert (x : ι → Option (E × W)) (i : ι) (T : Finset ι) :
    records x (insert i T) = records x {i} ∪ records x T := by
  rw [records, Finset.biUnion_insert, records_singleton, records]

lemma records_insert_of_eq_none (h : x i = none) : records x (insert i T) = records x T := by
  rw [records_insert, records_singleton, h]
  simp

lemma records_insert_of_eq_some {p : E × W} (h : x i = some p) :
    records x (insert i T) = insert (tagRecord i p) (records x T) := by
  rw [records_insert, records_singleton, h]
  simp

/-- Deleting a position deletes exactly the records tagged with it. -/
lemma records_erase (x : ι → Option (E × W)) (i : ι) (T : Finset ι) :
    records x (T.erase i) = (records x T).filter (·.index ≠ i) := by
  ext r
  simp only [mem_records, Finset.mem_erase, Finset.mem_filter]
  tauto

/-- **Index projection is injective** on the records of an input. -/
lemma records_injOn_index : InjOn WeightedRecord.index (records x T : Set Rec) := by
  intro r hr s hs h
  have hr' := (mem_records.1 hr).2
  have hs' := (mem_records.1 hs).2
  rw [h, hs', Option.some.injEq, Prod.mk.injEq] at hr'
  exact WeightedRecord.ext hr'.1.symm hr'.2.symm h

lemma image_element_records (x : ι → Option (E × W)) (T : Finset ι) :
    WeightedRecord.element '' (records x T : Set Rec) = inputElements x T := by
  ext e
  simp only [mem_image, Finset.mem_coe, mem_records, inputElements, mem_ofPred_eq]
  constructor
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    exact ⟨r.index, hr, r.weight, hx⟩
  · rintro ⟨i, hi, w, hx⟩
    exact ⟨⟨e, w, i⟩, ⟨hi, hx⟩, rfl⟩

/-- A subset of the records of `x` is recovered from its positions. -/
lemma records_image_index {R : Finset (WeightedRecord ι E W)} (hR : R ⊆ records x T) :
    records x (R.image WeightedRecord.index) = R := by
  ext r
  simp only [mem_records, Finset.mem_image]
  constructor
  · rintro ⟨⟨s, hs, hsr⟩, hx⟩
    have hsT := hR hs
    have hrT : r ∈ records x T := mem_records.2 ⟨hsr ▸ (mem_records.1 hsT).1, hx⟩
    rwa [records_injOn_index hrT hsT hsr.symm]
  · intro hr
    exact ⟨⟨r, hr, rfl⟩, (mem_records.1 (hR hr)).2⟩

lemma image_index_records_of_isSome (h : ∀ i ∈ T, (x i).isSome) :
    (records x T).image WeightedRecord.index = T := by
  ext i
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (mem_records.1 hr).1
  · intro hi
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (h i hi)
    exact ⟨tagRecord i p, tagRecord_mem_records hi hp, rfl⟩

/-- On the records of an actual input, the record order is the order by
`(weight, index)`: the element component never breaks a tie, because each position
supplies at most one record. -/
lemma lt_iff_of_mem_records (hs : s ∈ records x T) (hr : r ∈ records x T) :
    s < r ↔ toLex (s.weight, s.index) < toLex (r.weight, r.index) := by
  rw [lt_iff_lex, Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (h | ⟨h₁, h₂ | ⟨h₃, h₄⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h₁, h₂⟩
    · rw [records_injOn_index hs hr h₃] at h₄
      exact absurd h₄ (lt_irrefl _)
  · rintro (h | ⟨h₁, h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h₁, Or.inl h₂⟩

/-! ### The parallel-copy model on input positions -/

/-- **Parallel-copy independence** of a set `I` of input positions (`monoid.tex`, before
`thm:matroid-basis-query`): all its records are nonnull, their elements are distinct,
and the set of these elements is independent in `M`. -/
def IsParallelIndep (M : _root_.Matroid E) (x : ι → Option (E × W)) (I : Finset ι) :
    Prop :=
  (∀ i ∈ I, (x i).isSome) ∧
    (∀ i ∈ I, ∀ j ∈ I, ∀ (e : E) (w w' : W), x i = some (e, w) → x j = some (e, w') →
      i = j) ∧
    M.Indep (inputElements x I)

/-- A **basis of the input restriction** to `T`: a maximal parallel-copy independent set
of positions of `T`. -/
def IsParallelBasis (M : _root_.Matroid E) (x : ι → Option (E × W)) (T I : Finset ι) :
    Prop :=
  I ⊆ T ∧ IsParallelIndep M x I ∧
    ∀ J : Finset ι, I ⊆ J → J ⊆ T → IsParallelIndep M x J → J = I

lemma isParallelIndep_iff {I : Finset ι} :
    IsParallelIndep M x I ↔
      (∀ i ∈ I, (x i).isSome) ∧ (recordMatroid M).Indep (records x I : Set Rec) := by
  rw [recordMatroid_indep_iff, image_element_records, IsParallelIndep]
  refine and_congr_right fun _ => ⟨fun ⟨h, hI⟩ => ⟨hI, fun r hr s hs hrs => ?_⟩,
    fun ⟨hI, h⟩ => ⟨fun i hi j hj e w w' hx hy => ?_, hI⟩⟩
  · obtain ⟨hri, hrx⟩ := mem_records.1 hr
    obtain ⟨hsi, hsx⟩ := mem_records.1 hs
    rw [hrs] at hrx
    exact records_injOn_index hr hs (h _ hri _ hsi _ _ _ hrx hsx)
  · have := h (tagRecord_mem_records hi hx) (tagRecord_mem_records hj hy) rfl
    exact congrArg WeightedRecord.index this

/-- Parallel-copy bases of the input are exactly the position sets of record-matroid bases
of the input records. -/
theorem isParallelBasis_iff (hM : M.E = univ) {I : Finset ι} :
    IsParallelBasis M x T I ↔
      I ⊆ T ∧ (∀ i ∈ I, (x i).isSome) ∧
        (recordMatroid M).IsBasis (records x I : Set Rec) (records x T : Set Rec) := by
  have hg := recordMatroid_ground (ι := ι) (W := W) hM
  constructor
  · rintro ⟨hIT, hI, hmax⟩
    obtain ⟨hs, hind⟩ := isParallelIndep_iff.1 hI
    refine ⟨hIT, hs, hind.isBasis_of_forall_insert (by exact_mod_cast records_mono hIT)
      fun r ⟨hrT, hrI⟩ => ?_⟩
    rw [← _root_.Matroid.not_indep_iff (by rw [hg]; exact subset_univ _)]
    intro hins
    obtain ⟨hri, hrx⟩ := mem_records.1 hrT
    have hnot : r.index ∉ I := fun h => hrI (mem_records.2 ⟨h, hrx⟩)
    have hJ : IsParallelIndep M x (insert r.index I) := by
      refine isParallelIndep_iff.2 ⟨fun j hj => ?_, ?_⟩
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · rw [hrx]; rfl
        · exact hs j hj
      · rw [records_insert_of_eq_some hrx, Finset.coe_insert]
        exact hins
    have := hmax _ (Finset.subset_insert _ _) (Finset.insert_subset hri hIT) hJ
    exact hnot (this ▸ Finset.mem_insert_self _ _)
  · rintro ⟨hIT, hs, hB⟩
    refine ⟨hIT, isParallelIndep_iff.2 ⟨hs, hB.indep⟩, fun J hIJ hJT hJ => ?_⟩
    obtain ⟨hJs, hJind⟩ := isParallelIndep_iff.1 hJ
    have heq := hB.eq_of_subset_indep hJind (by exact_mod_cast records_mono hIJ)
      (by exact_mod_cast records_mono hJT)
    refine (Finset.Subset.antisymm ?_ hIJ)
    intro j hj
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (hJs j hj)
    have hmem : tagRecord j p ∈ ((records x I : Set Rec) : Set Rec) := by
      rw [heq]; exact tagRecord_mem_records hj hp
    exact (mem_records.1 hmem).1

/-! ### The canonical basis of the input records -/

/-- The **canonical basis records** of the positions in `T`: the greedy basis of the
labelled input records in the lexicographic record order. -/
noncomputable def basisRecords (M : _root_.Matroid E) (x : ι → Option (E × W))
    (T : Finset ι) : Finset (WeightedRecord ι E W) :=
  greedy (recordMatroid M) (records x T)

/-- The **canonical basis positions**: the positions of the canonical basis records. -/
noncomputable def basisIndices (M : _root_.Matroid E) (x : ι → Option (E × W))
    (T : Finset ι) : Finset ι :=
  (basisRecords M x T).image WeightedRecord.index

lemma basisRecords_subset_records (M : _root_.Matroid E) (x : ι → Option (E × W))
    (T : Finset ι) : basisRecords M x T ⊆ records x T :=
  greedy_subset _ _

/-- Every returned record is a truthful record of `x` at a position of `T`. -/
theorem mem_basisRecords_truthful (hr : r ∈ basisRecords M x T) :
    r.index ∈ T ∧ x r.index = some (r.element, r.weight) :=
  mem_records.1 (basisRecords_subset_records M x T hr)

lemma basisRecords_injOn_index : InjOn WeightedRecord.index (basisRecords M x T : Set Rec) :=
  records_injOn_index.mono (by exact_mod_cast basisRecords_subset_records M x T)

lemma basisIndices_subset (M : _root_.Matroid E) (x : ι → Option (E × W)) (T : Finset ι) :
    basisIndices M x T ⊆ T := by
  intro i hi
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hi
  exact (mem_basisRecords_truthful hr).1

lemma card_basisIndices (M : _root_.Matroid E) (x : ι → Option (E × W)) (T : Finset ι) :
    (basisIndices M x T).card = (basisRecords M x T).card :=
  Finset.card_image_of_injOn basisRecords_injOn_index

/-- The input records at the returned positions are exactly the returned records. -/
lemma records_basisIndices (M : _root_.Matroid E) (x : ι → Option (E × W))
    (T : Finset ι) : records x (basisIndices M x T) = basisRecords M x T :=
  records_image_index (basisRecords_subset_records M x T)

lemma isSome_of_mem_basisIndices (hi : i ∈ basisIndices M x T) : (x i).isSome := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hi
  rw [(mem_basisRecords_truthful hr).2]; rfl

/-- The canonical basis records form a basis of the input records in the record
matroid. -/
theorem isBasis_basisRecords (hM : M.E = univ) (x : ι → Option (E × W)) (T : Finset ι) :
    (recordMatroid M).IsBasis (basisRecords M x T : Set Rec) (records x T : Set Rec) :=
  isBasis_greedy (recordMatroid_ground hM) _

/-- The selected elements are distinct and form a basis of the elements occurring in the
input (not necessarily of the whole ground set). -/
theorem isBasis_image_element_basisRecords (hM : M.E = univ) (x : ι → Option (E × W))
    (T : Finset ι) :
    M.IsBasis (WeightedRecord.element '' (basisRecords M x T : Set Rec)) (inputElements x T) ∧
      InjOn WeightedRecord.element (basisRecords M x T : Set Rec) := by
  have h := isBasis_basisRecords hM x T
  rw [recordMatroid, _root_.Matroid.comap_isBasis_iff, image_element_records] at h
  exact ⟨h.1, h.2.1⟩

/-- The returned positions are independent in the parallel-copy model. -/
theorem isParallelIndep_basisIndices (hM : M.E = univ) (x : ι → Option (E × W))
    (T : Finset ι) : IsParallelIndep M x (basisIndices M x T) := by
  rw [isParallelIndep_iff, records_basisIndices]
  exact ⟨fun _ hi => isSome_of_mem_basisIndices hi, (isBasis_basisRecords hM x T).indep⟩

/-- The returned positions form a basis of the input restriction to `T`. -/
theorem isParallelBasis_basisIndices (hM : M.E = univ) (x : ι → Option (E × W))
    (T : Finset ι) : IsParallelBasis M x T (basisIndices M x T) := by
  rw [isParallelBasis_iff hM, records_basisIndices]
  exact ⟨basisIndices_subset M x T, fun _ hi => isSome_of_mem_basisIndices hi,
    isBasis_basisRecords hM x T⟩

/-- The returned positions span: their elements have the same rank as all the elements
occurring in the input. -/
theorem eRk_inputElements_basisIndices (hM : M.E = univ) (x : ι → Option (E × W))
    (T : Finset ι) : M.eRk (inputElements x (basisIndices M x T)) = M.eRk (inputElements x T) := by
  rw [← image_element_records, records_basisIndices]
  exact (isBasis_image_element_basisRecords hM x T).1.eRk_eq_eRk

/-- At most `rank M` records are selected. -/
theorem card_basisRecords_le_eRank (hM : M.E = univ) (x : ι → Option (E × W))
    (T : Finset ι) : ((basisRecords M x T).card : ℕ∞) ≤ M.eRank := by
  have hI := recordMatroid_indep_iff.1 (isBasis_basisRecords hM x T).indep
  rw [← Set.encard_coe_eq_coe_finsetCard, ← hI.2.encard_image]
  exact hI.1.encard_le_eRank

/-- At most `#T` records are selected. -/
theorem card_basisRecords_le_card (M : _root_.Matroid E) (x : ι → Option (E × W))
    (T : Finset ι) : (basisRecords M x T).card ≤ T.card := by
  rw [← card_basisIndices]
  exact Finset.card_le_card (basisIndices_subset M x T)

/-! ### Minimum total weight -/

/-- The real weight of the record at position `i` (zero for a null record). -/
def inputWeight (weight : W ↪o ℝ) (x : ι → Option (E × W)) (i : ι) : ℝ :=
  (x i).elim 0 fun p => weight p.2

lemma sum_inputWeight_image_index (weight : W ↪o ℝ) {R : Finset (WeightedRecord ι E W)}
    (hR : R ⊆ records x T) :
    ∑ i ∈ R.image WeightedRecord.index, inputWeight weight x i =
      ∑ r ∈ R, weight r.weight := by
  rw [Finset.sum_image (records_injOn_index.mono (by exact_mod_cast hR))]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [inputWeight, (mem_records.1 (hR hr)).2]
  rfl

/-- Among all record-matroid bases of the input records, the canonical one has minimum
total weight. -/
theorem basisRecords_minWeight (hM : M.E = univ) (weight : W ↪o ℝ)
    {R : Finset (WeightedRecord ι E W)} (hR : (recordMatroid M).IsBasis (R : Set Rec)
      (records x T : Set Rec)) :
    ∑ r ∈ basisRecords M x T, weight r.weight ≤ ∑ r ∈ R, weight r.weight :=
  greedy_minWeight (recordMatroid_ground hM)
    (fun _ _ h => weight.monotone (weight_le_weight_of_le h)) hR

/-- **Minimum-weight basis of the input records** (`thm:matroid-basis-query`).

For the input `x` restricted to the positions `T`:
1. every returned record is a truthful record of `x` at a position of `T`;
2. the input records at the returned positions are exactly the returned records;
3. the returned positions form a basis of the input restriction in the parallel-copy
   model;
4. their total weight is at most that of every such basis. -/
theorem basisRecords_isMinimumWeightBasis (hM : M.E = univ) (weight : W ↪o ℝ)
    (x : ι → Option (E × W)) (T : Finset ι) :
    (∀ r ∈ basisRecords M x T, r.index ∈ T ∧ x r.index = some (r.element, r.weight)) ∧
      records x (basisIndices M x T) = basisRecords M x T ∧
      IsParallelBasis M x T (basisIndices M x T) ∧
      ∀ J : Finset ι, IsParallelBasis M x T J →
        ∑ i ∈ basisIndices M x T, inputWeight weight x i ≤
          ∑ i ∈ J, inputWeight weight x i := by
  refine ⟨fun _ hr => mem_basisRecords_truthful hr, records_basisIndices M x T,
    isParallelBasis_basisIndices hM x T, fun J hJ => ?_⟩
  obtain ⟨-, hJs, hJB⟩ := (isParallelBasis_iff hM).1 hJ
  rw [basisIndices, sum_inputWeight_image_index weight (basisRecords_subset_records M x T)]
  conv_rhs => rw [← image_index_records_of_isSome hJs]
  rw [sum_inputWeight_image_index weight (Finset.Subset.refl _)]
  exact basisRecords_minWeight hM weight hJB

/-! ### Greedy by `(weight, index)` -/

lemma image_element_records_inter_Iio (hr : r ∈ records x T) :
    WeightedRecord.element '' ((records x T : Set Rec) ∩ Iio r) =
      {e | ∃ j ∈ T, ∃ w, x j = some (e, w) ∧ toLex (w, j) < toLex (r.weight, r.index)} := by
  ext e
  constructor
  · rintro ⟨s, ⟨hs, hsr⟩, rfl⟩
    exact ⟨s.index, (mem_records.1 hs).1, s.weight, (mem_records.1 hs).2,
      (lt_iff_of_mem_records hs hr).1 hsr⟩
  · rintro ⟨j, hj, w, hx, hlt⟩
    have hs := tagRecord_mem_records hj hx
    exact ⟨tagRecord j (e, w), ⟨hs, (lt_iff_of_mem_records hs hr).2 hlt⟩, rfl⟩

/-- **The canonical basis is greedy by `(weight, index)`**: position `i ∈ T` is selected
exactly when its record is nonnull and its element is not spanned by the elements of the
records that precede it in the order by `(weight, index)`. -/
theorem mem_basisIndices_iff :
    i ∈ basisIndices M x T ↔ i ∈ T ∧ ∃ e w, x i = some (e, w) ∧
      e ∉ M.closure
        {e' | ∃ j ∈ T, ∃ w', x j = some (e', w') ∧ toLex (w', j) < toLex (w, i)} := by
  have key : ∀ r ∈ records x T, (r ∈ basisRecords M x T ↔ r.element ∉ M.closure
      {e' | ∃ j ∈ T, ∃ w', x j = some (e', w') ∧
        toLex (w', j) < toLex (r.weight, r.index)}) := by
    intro r hr
    rw [basisRecords, mem_greedy, recordMatroid, _root_.Matroid.comap_closure_eq,
      image_element_records_inter_Iio hr]
    exact and_iff_right hr
  constructor
  · intro hi
    obtain ⟨r, hrB, rfl⟩ := Finset.mem_image.1 hi
    have hr := basisRecords_subset_records M x T hrB
    exact ⟨(mem_records.1 hr).1, r.element, r.weight, (mem_records.1 hr).2,
      (key r hr).1 hrB⟩
  · rintro ⟨hi, e, w, hx, hcl⟩
    have hr := tagRecord_mem_records hi hx
    exact Finset.mem_image.2 ⟨_, (key _ hr).2 hcl, rfl⟩

/-- A record spanned by a single record earlier in the order by `(weight, index)` is not
selected.  In particular, of two parallel copies the lighter one wins, and at equal weight
the one at the smaller position wins. -/
theorem notMem_basisIndices_of_mem_closure {j : ι} {e e' : E}
    {w w' : W} (hiT : i ∈ T) (hi : x i = some (e, w)) (hj : x j = some (e', w'))
    (hlt : toLex (w, i) < toLex (w', j)) (hcl : e' ∈ M.closure {e}) :
    j ∉ basisIndices M x T := by
  rw [mem_basisIndices_iff]
  rintro ⟨-, e'', w'', hj', hncl⟩
  rw [hj, Option.some.injEq, Prod.mk.injEq] at hj'
  obtain ⟨rfl, rfl⟩ := hj'
  refine hncl (M.closure_subset_closure ?_ hcl)
  rintro _ rfl
  exact ⟨i, hiT, w, hi, hlt⟩

/-! ### Update laws of the incremental state -/

@[simp] lemma basisRecords_empty (M : _root_.Matroid E) (x : ι → Option (E × W)) :
    basisRecords M x ∅ = ∅ := by
  simp [basisRecords]

/-- The state of a set depends only on the input entries at its positions. -/
lemma basisRecords_congr (h : ∀ i ∈ T, x i = y i) :
    basisRecords M x T = basisRecords M y T := by
  rw [basisRecords, basisRecords, records_congr h]

/-- **Insertion law**: the basis after revealing position `i` is determined by the old basis
and the record at `i` (`lem:matroid-greedy-merge`). -/
theorem basisRecords_insert (hM : M.E = univ) (x : ι → Option (E × W)) (i : ι)
    (T : Finset ι) :
    basisRecords M x (insert i T) =
      greedy (recordMatroid M) (records x {i} ∪ basisRecords M x T) := by
  have hg := recordMatroid_ground (ι := ι) (W := W) hM
  rw [basisRecords, records_insert, greedy_union_eq_greedy_union_greedy hg,
    greedy_union_eq_greedy_union_greedy hg (records x {i}), basisRecords, greedy_greedy hg]

/-- **Determinism of the update**: equal old states and equal entries at `i` give equal new
states. -/
theorem basisRecords_insert_congr (hM : M.E = univ)
    (hT : basisRecords M x T = basisRecords M y T) (hi : x i = y i) :
    basisRecords M x (insert i T) = basisRecords M y (insert i T) := by
  rw [basisRecords_insert hM, basisRecords_insert hM, hT, records_singleton,
    records_singleton, hi]

/-- **Deletion criterion**: deleting position `i` leaves the state unchanged exactly when
`i` is not selected. -/
theorem basisRecords_erase_eq_iff (hM : M.E = univ) :
    basisRecords M x (T.erase i) = basisRecords M x T ↔ i ∉ basisIndices M x T := by
  constructor
  · intro h hi
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hi
    rw [← h] at hr
    have := mem_basisRecords_truthful hr
    exact (Finset.mem_erase.1 this.1).1 rfl
  · intro hi
    refine greedy_eq_greedy_of_greedy_subset_of_subset (recordMatroid_ground hM)
      (fun r hr => ?_) (records_mono (Finset.erase_subset _ _))
    rw [records_erase, Finset.mem_filter]
    exact ⟨basisRecords_subset_records M x T hr,
      fun h => hi (Finset.mem_image.2 ⟨r, hr, h⟩)⟩

/-! ### Examples -/

section Examples

/-- All-null input: nothing is selected. -/
example (x : ι → Option (E × W)) (hx : ∀ i, x i = none) (T : Finset ι) :
    basisRecords M x T = ∅ ∧ basisIndices M x T = ∅ := by
  have h : basisRecords M x T = ∅ := by
    rw [basisRecords, records_eq_empty_of_forall fun i _ => hx i, greedy_empty]
  exact ⟨h, by rw [basisIndices, h, Finset.image_empty]⟩

/-- Duplicate elements with different weights: the heavier copy is never selected. -/
example (hM : M.E = univ) {j : ι} {e : E} {w w' : W} (hiT : i ∈ T)
    (hi : x i = some (e, w)) (hj : x j = some (e, w')) (hw : w < w') :
    j ∉ basisIndices M x T :=
  notMem_basisIndices_of_mem_closure hiT hi hj (Prod.Lex.toLex_lt_toLex.2 (Or.inl hw))
    (M.mem_closure_of_mem rfl (by rw [hM]; exact subset_univ _))

/-- Equal-weight copies: the one at the smaller position wins the tie. -/
example (hM : M.E = univ) {j : ι} {e : E} {w : W} (hiT : i ∈ T)
    (hi : x i = some (e, w)) (hj : x j = some (e, w)) (hij : i < j) :
    j ∉ basisIndices M x T :=
  notMem_basisIndices_of_mem_closure hiT hi hj
    (Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, hij⟩))
    (M.mem_closure_of_mem rfl (by rw [hM]; exact subset_univ _))

/-- A cheaper replacement preserving rank: if `f` is a nonloop spanning `e` and the record
of `f` is lighter, then only `f` is selected, and the selection has the full rank of the
input elements. -/
example (hM : M.E = univ) {j : ι} {e f : E} {w w' : W} (hi : x i = some (e, w))
    (hj : x j = some (f, w')) (hw : w' < w) (hef : e ∈ M.closure {f}) (hf : M.IsNonloop f) :
    basisIndices M x {i, j} = {j} ∧
      M.eRk (inputElements x (basisIndices M x {i, j})) = M.eRk (inputElements x {i, j}) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [hi, Option.some.injEq, Prod.mk.injEq] at hj
    exact absurd hj.2 (ne_of_gt hw)
  refine ⟨?_, eRk_inputElements_basisIndices hM x _⟩
  ext k
  simp only [Finset.mem_singleton]
  constructor
  · intro hk
    have hkT := basisIndices_subset M x _ hk
    rcases Finset.mem_insert.1 hkT with rfl | hk'
    · exact absurd hk (notMem_basisIndices_of_mem_closure (by simp) hj hi
        (Prod.Lex.toLex_lt_toLex.2 (Or.inl hw)) hef)
    · exact Finset.mem_singleton.1 hk'
  · rintro rfl
    rw [mem_basisIndices_iff]
    refine ⟨by simp, f, w', hj, fun hcl => hf.not_isLoop ?_⟩
    -- nothing precedes the lighter record, so the relevant span is that of `∅`
    have hempty : {e' | ∃ l ∈ ({i, k} : Finset ι), ∃ w'', x l = some (e', w'') ∧
        toLex (w'', l) < toLex (w', k)} = ∅ := by
      ext e'
      simp only [Finset.mem_insert, Finset.mem_singleton, mem_ofPred_eq, mem_empty_iff_false,
        iff_false, not_exists, not_and]
      rintro l (rfl | rfl) w'' hl hlt
      · rw [hi, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨-, rfl⟩ := hl
        rcases Prod.Lex.toLex_lt_toLex.1 hlt with h | ⟨h, -⟩
        · exact absurd (h.trans hw) (lt_irrefl _)
        · exact absurd h (ne_of_gt hw)
      · rw [hj, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨-, rfl⟩ := hl
        exact absurd hlt (lt_irrefl _)
    rw [hempty] at hcl
    exact hcl

end Examples

end MonoidProduct.Matroid
