import MonoidProduct.Matroid.Quantum
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# Weighted vector bases

This file formalizes the vector-matroid example of `sec:matroid-bases` in `monoid.tex`
(the paragraph *Examples* after `thm:matroid-basis-query`): for the vector matroid on
`𝔽_q^d`, a query reveals a vector and its weight, and a minimum-weight subset of the input
forming a basis of the input span is computed with `O(min{n, √(n·d)})` queries, uniformly
in `q`; with equal weights this computes the span itself, represented by a basis.  The cost
is for whole-vector queries.

* `vectorMatroid F V`: the matroid on a finite `F`-vector space `V` whose independent sets
  are the linearly independent sets of vectors (`vectorMatroid_indep_iff`), with ground set
  `univ`.  Its bases of a set `X` are the linearly independent subsets of `X` spanning `X`
  (`vectorMatroid_isBasis_iff`), and its rank is at most `finrank F V`
  (`eRank_vectorMatroid_le`), hence at most `d` on `Fin d → F`.
* The parallel-copy bridge: a set of input positions is independent in the parallel-copy
  model of `thm:matroid-basis-query` exactly when its records are nonnull and the family of
  its vectors is linearly independent (`isParallelIndep_vectorMatroid_iff`).  A linearly
  independent family has no repeated vector, so repeated vectors are parallel copies.
  Parallel-copy bases are exactly the sets of positions whose vectors form a basis of the
  span of the input vectors (`isParallelBasis_vectorMatroid_iff`, `IsInputSpanBasis`).
* `vectorBasis_minWeight_and_qQuery`: for `x : Fin n → Option ((Fin d → F) × W)` over a
  finite field `F`, the canonical positions `basisIndices` form a basis of the input span of
  minimum total weight, and both the selected records and the selected positions cost
  `Q_{1/3} ≤ min{n, 2^18·√(n·d)}`.  The bound is uniform in `F`, `W` and the weights.
* `spanBasis_isBasis_and_qQuery`: equal weights.  For unweighted input
  `y : Fin n → Option (Fin d → F)` the returned positions, and the returned vectors, form a
  basis of the span of the input vectors, at the same cost against the unweighted oracle.

The canonical answer requires a fixed public linear order on the vectors; any order works,
and `vectorLinearOrder` supplies one.
-/

namespace MonoidProduct.Matroid

open Set QuantumQueryComplexity

/-! ### The vector matroid -/

section VectorMatroid

variable (F V : Type*) [Field F] [AddCommGroup V] [Module F V]

/-- The augmentation axiom for linearly independent sets of vectors: a smaller independent
set extends by a vector of a larger one. -/
lemma linearIndepOn_id_exists_insert_of_ncard_lt [Finite V] {I J : Set V}
    (hI : LinearIndepOn F id I) (hJ : LinearIndepOn F id J) (hlt : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn F id (insert e I) := by
  classical
  by_contra h
  push Not at h
  have hsub : J ⊆ Submodule.span F I := by
    intro e he
    by_cases heI : e ∈ I
    · exact Submodule.subset_span heI
    · by_contra hspan
      exact h e he heI ((linearIndepOn_id_insert heI).2 ⟨hI, hspan⟩)
  have hle : Submodule.span F J ≤ Submodule.span F I := Submodule.span_le.2 hsub
  have : Fintype I := Fintype.ofFinite _
  have : Fintype J := Fintype.ofFinite _
  have : Module.Finite F (Submodule.span F I) :=
    FiniteDimensional.span_of_finite F (Set.toFinite I)
  have hmono := Submodule.finrank_mono hle
  rw [finrank_span_set_eq_card hI, finrank_span_set_eq_card hJ,
    ← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card'] at hmono
  omega

/-- The independence system of linearly independent sets of vectors. -/
noncomputable def vectorIndepMatroid [Finite V] : IndepMatroid V :=
  IndepMatroid.ofFinite Set.finite_univ (fun I => LinearIndepOn F id I)
    (linearIndepOn_empty F id) (fun _ _ hJ hIJ => hJ.mono hIJ)
    (fun _ _ hI hJ hlt => linearIndepOn_id_exists_insert_of_ncard_lt F V hI hJ hlt)
    (fun _ _ => subset_univ _)

/-- **The vector matroid** on a finite `F`-vector space `V` (`sec:matroid-bases`): its
independent sets are the linearly independent sets of vectors. -/
noncomputable def vectorMatroid [Finite V] : _root_.Matroid V :=
  (vectorIndepMatroid F V).matroid

variable {F V} [Finite V]

@[simp] lemma vectorMatroid_ground : (vectorMatroid F V).E = univ := rfl

/-- Independence in the vector matroid is linear independence. -/
@[simp] lemma vectorMatroid_indep_iff {I : Set V} :
    (vectorMatroid F V).Indep I ↔ LinearIndepOn F id I := by
  rw [vectorMatroid, IndepMatroid.matroid_indep_iff]
  rfl

/-- A basis of `X` in the vector matroid is a linearly independent subset of `X` whose span
contains `X`. -/
theorem vectorMatroid_isBasis_iff {B X : Set V} :
    (vectorMatroid F V).IsBasis B X ↔
      B ⊆ X ∧ LinearIndepOn F id B ∧ X ⊆ Submodule.span F B := by
  constructor
  · intro hB
    refine ⟨hB.subset, vectorMatroid_indep_iff.1 hB.indep, fun e he => ?_⟩
    by_cases heB : e ∈ B
    · exact Submodule.subset_span heB
    · by_contra hspan
      have hdep := hB.insert_dep ⟨he, heB⟩
      exact hdep.not_indep (vectorMatroid_indep_iff.2
        ((linearIndepOn_id_insert heB).2 ⟨vectorMatroid_indep_iff.1 hB.indep, hspan⟩))
  · rintro ⟨hBX, hB, hX⟩
    refine (vectorMatroid_indep_iff.2 hB).isBasis_of_forall_insert hBX
      fun e ⟨he, heB⟩ => ?_
    rw [← _root_.Matroid.not_indep_iff (by rw [vectorMatroid_ground]; exact subset_univ _),
      vectorMatroid_indep_iff, linearIndepOn_id_insert heB]
    exact fun h => h.2 (hX he)

/-- **The rank of the vector matroid is at most the dimension.** -/
theorem eRank_vectorMatroid_le [Module.Finite F V] :
    (vectorMatroid F V).eRank ≤ Module.finrank F V := by
  classical
  obtain ⟨B, hB⟩ := (vectorMatroid F V).exists_isBase
  rw [← hB.encard_eq_eRank, ← (Set.toFinite B).cast_ncard_eq]
  have hind : LinearIndepOn F id B := vectorMatroid_indep_iff.1 hB.indep
  have : Fintype B := Fintype.ofFinite _
  have h := Submodule.finrank_le (Submodule.span F B)
  rw [finrank_span_set_eq_card hind, ← ncard_eq_toFinset_card'] at h
  exact_mod_cast h

/-- The vector matroid on `Fin d → F` has rank at most `d`. -/
theorem eRank_vectorMatroid_fin_le {F : Type*} [Field F] [Finite F] (d : ℕ) :
    (vectorMatroid F (Fin d → F)).eRank ≤ d := by
  have h := eRank_vectorMatroid_le (F := F) (V := Fin d → F)
  rwa [Module.finrank_fin_fun] at h

end VectorMatroid

/-! ### Weighted input vectors and the parallel-copy model -/

section Bridge

variable {F V ι W : Type*} [Field F] [AddCommGroup V] [Module F V] [Finite V]

/-- The vector recorded at position `i` (zero for a null record). -/
def inputVector (x : ι → Option (V × W)) (i : ι) : V :=
  (x i).elim 0 Prod.fst

variable {x : ι → Option (V × W)}

lemma inputVector_of_eq_some {i : ι} {v : V} {w : W} (h : x i = some (v, w)) :
    inputVector x i = v := by
  rw [inputVector, h]
  rfl

/-- On nonnull positions, the input elements are the images of the positions under
`inputVector`. -/
lemma inputElements_eq_image {I : Finset ι} (hs : ∀ i ∈ I, (x i).isSome) :
    inputElements x I = inputVector x '' (I : Set ι) := by
  ext v
  constructor
  · rintro ⟨i, hi, w, hx⟩
    exact ⟨i, hi, inputVector_of_eq_some hx⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨⟨v, w⟩, hx⟩ := Option.isSome_iff_exists.1 (hs i hi)
    exact ⟨i, hi, w, by rw [hx, inputVector_of_eq_some hx]⟩

lemma inputVector_mem_inputElements {T : Finset ι} {i : ι} (hi : i ∈ T)
    (hs : (x i).isSome) : inputVector x i ∈ inputElements x T := by
  obtain ⟨⟨v, w⟩, hx⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨i, hi, w, by rw [hx, inputVector_of_eq_some hx]⟩

variable [LinearOrder V]

/-- **Parallel copies are repeated vectors** (`thm:matroid-basis-query`, `sec:matroid-bases`):
a set of positions is independent in the parallel-copy model of the vector matroid exactly
when its records are nonnull and the family of its vectors is linearly independent.  In
particular its vectors are pairwise distinct. -/
theorem isParallelIndep_vectorMatroid_iff {I : Finset ι} :
    IsParallelIndep (vectorMatroid F V) x I ↔
      (∀ i ∈ I, (x i).isSome) ∧ LinearIndepOn F (inputVector x) (I : Set ι) := by
  constructor
  · rintro ⟨hs, hinj, hind⟩
    refine ⟨hs, ?_⟩
    have hinjOn : InjOn (inputVector x) (I : Set ι) := by
      intro i hi j hj hij
      obtain ⟨⟨v, w⟩, hx⟩ := Option.isSome_iff_exists.1 (hs i hi)
      obtain ⟨⟨v', w'⟩, hy⟩ := Option.isSome_iff_exists.1 (hs j hj)
      rw [inputVector_of_eq_some hx, inputVector_of_eq_some hy] at hij
      subst hij
      exact hinj i hi j hj v w w' hx hy
    rw [linearIndepOn_iff_image hinjOn, ← inputElements_eq_image hs]
    exact vectorMatroid_indep_iff.1 hind
  · rintro ⟨hs, hlin⟩
    refine ⟨hs, fun i hi j hj v w w' hx hy => ?_, ?_⟩
    · refine hlin.injOn hi hj ?_
      rw [inputVector_of_eq_some hx, inputVector_of_eq_some hy]
    · rw [vectorMatroid_indep_iff, inputElements_eq_image hs]
      exact hlin.id_image

/-- **A basis of the input span**: a set `I ⊆ T` of nonnull positions whose vectors are
linearly independent (in particular pairwise distinct) and span the same subspace as all the
vectors occurring at the positions of `T`. -/
def IsInputSpanBasis (F : Type*) [Field F] [Module F V] (x : ι → Option (V × W))
    (T I : Finset ι) : Prop :=
  I ⊆ T ∧ (∀ i ∈ I, (x i).isSome) ∧ LinearIndepOn F (inputVector x) (I : Set ι) ∧
    Submodule.span F (inputVector x '' (I : Set ι)) = Submodule.span F (inputElements x T)

/-- The vectors of a basis of the input span are pairwise distinct. -/
lemma IsInputSpanBasis.injOn_inputVector {T I : Finset ι} (h : IsInputSpanBasis F x T I) :
    InjOn (inputVector x) (I : Set ι) :=
  h.2.2.1.injOn

/-- **Parallel-copy bases of the vector matroid are exactly the bases of the input span.** -/
theorem isParallelBasis_vectorMatroid_iff {T I : Finset ι} :
    IsParallelBasis (vectorMatroid F V) x T I ↔ IsInputSpanBasis F x T I := by
  classical
  constructor
  · rintro ⟨hIT, hI, hmax⟩
    obtain ⟨hs, hlin⟩ := isParallelIndep_vectorMatroid_iff.1 hI
    refine ⟨hIT, hs, hlin, le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact inputVector_mem_inputElements (hIT hi) (hs i hi)
    · rintro v ⟨j, hj, w, hx⟩
      by_contra hspan
      have hjv := inputVector_of_eq_some hx
      have hjI : j ∉ (I : Set ι) := fun h => hspan (Submodule.subset_span ⟨j, h, hjv⟩)
      have hJ : IsParallelIndep (vectorMatroid F V) x (insert j I) := by
        refine isParallelIndep_vectorMatroid_iff.2 ⟨fun k hk => ?_, ?_⟩
        · rcases Finset.mem_insert.1 hk with rfl | hk
          · rw [hx]; rfl
          · exact hs k hk
        · rw [Finset.coe_insert, linearIndepOn_insert hjI, hjv]
          exact ⟨hlin, hspan⟩
      have := hmax _ (Finset.subset_insert _ _) (Finset.insert_subset hj hIT) hJ
      exact hjI (by rw [← this]; exact Finset.mem_insert_self _ _)
  · rintro ⟨hIT, hs, hlin, hspan⟩
    refine ⟨hIT, isParallelIndep_vectorMatroid_iff.2 ⟨hs, hlin⟩, fun J hIJ hJT hJ => ?_⟩
    obtain ⟨hJs, hJlin⟩ := isParallelIndep_vectorMatroid_iff.1 hJ
    refine Finset.Subset.antisymm (fun j hj => ?_) hIJ
    by_contra hjI
    have hjI' : j ∉ (I : Set ι) := hjI
    have hins : LinearIndepOn F (inputVector x) (insert j (I : Set ι)) :=
      hJlin.mono (Set.insert_subset hj (by exact_mod_cast hIJ))
    rw [linearIndepOn_insert hjI', hspan] at hins
    exact hins.2 (Submodule.subset_span (inputVector_mem_inputElements (hJT hj) (hJs j hj)))

end Bridge

/-! ### The minimum-weight basis of the input span -/

section MinWeight

variable {F V ι W : Type*} [Field F] [AddCommGroup V] [Module F V] [Finite V]
  [LinearOrder V] [LinearOrder ι] [LinearOrder W]

/-- **Minimum-weight basis of the input span** (`sec:matroid-bases`, vector matroid): the
canonical positions form a basis of the span of the input vectors at the positions of `T`,
and their total weight is at most that of every such basis. -/
theorem vectorBasisIndices_isMinWeightSpanBasis (weight : W ↪o ℝ) (x : ι → Option (V × W))
    (T : Finset ι) :
    IsInputSpanBasis F x T (basisIndices (vectorMatroid F V) x T) ∧
      ∀ J : Finset ι, IsInputSpanBasis F x T J →
        ∑ i ∈ basisIndices (vectorMatroid F V) x T, inputWeight weight x i ≤
          ∑ i ∈ J, inputWeight weight x i := by
  obtain ⟨-, -, h3, h4⟩ :=
    basisRecords_isMinimumWeightBasis (vectorMatroid_ground (F := F)) weight x T
  exact ⟨isParallelBasis_vectorMatroid_iff.1 h3,
    fun J hJ => h4 J (isParallelBasis_vectorMatroid_iff.2 hJ)⟩

end MinWeight

/-! ### The query bound for weighted vectors -/

section Query

variable {F V W : Type} [Field F] [AddCommGroup V] [Module F V] [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W]

/-- **Weighted vector bases** (`sec:matroid-bases`, vector matroid; via
`thm:matroid-basis-query`), for any finite vector space of dimension at most `d` with any
public linear order on its vectors.  For every input `x : Fin n → Option (V × W)`:

1. every returned record is a truthful record of `x`;
2. the returned positions form a basis of the span of the input vectors, and their total
   weight is at most that of every such basis;
3. computing the returned records costs `Q_{1/3} ≤ min{n, 2^18·√(n·d)}`;
4. computing the returned positions costs `Q_{1/3} ≤ min{n, 2^18·√(n·d)}`. -/
theorem vectorBasis_minWeight_and_qQuery_of_finrank_le (weight : W ↪o ℝ) {d : ℕ}
    (hd : Module.finrank F V ≤ d) (n : ℕ) :
    (∀ x : Fin n → Option (V × W),
      (∀ s ∈ basisRecords (vectorMatroid F V) x Finset.univ,
        x s.index = some (s.element, s.weight)) ∧
      IsInputSpanBasis F x Finset.univ (basisIndices (vectorMatroid F V) x Finset.univ) ∧
      ∀ J : Finset (Fin n), IsInputSpanBasis F x Finset.univ J →
        ∑ i ∈ basisIndices (vectorMatroid F V) x Finset.univ, inputWeight weight x i ≤
          ∑ i ∈ J, inputWeight weight x i) ∧
    (qQuery (fun x : Fin n → Option (V × W) =>
        basisRecords (vectorMatroid F V) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * d)) ∧
    (qQuery (fun x : Fin n → Option (V × W) =>
        basisIndices (vectorMatroid F V) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * d)) := by
  have hr : (vectorMatroid F V).eRank ≤ d :=
    eRank_vectorMatroid_le.trans (by exact_mod_cast hd)
  refine ⟨fun x => ?_, matroidBasisRecords_qQuery_le_min_sqrt vectorMatroid_ground hr n,
    matroidBasisIndices_qQuery_le_min_sqrt vectorMatroid_ground hr n⟩
  obtain ⟨h1, -⟩ := basisRecords_isMinimumWeightBasis (vectorMatroid_ground (F := F)) weight x
    Finset.univ
  exact ⟨fun s hs => (h1 s hs).2, vectorBasisIndices_isMinWeightSpanBasis weight x _⟩

/-- **Weighted vector bases over a finite field** (`sec:matroid-bases`, vector matroid on
`𝔽_q^d`; via `thm:matroid-basis-query`).  A query reveals a whole vector of `Fin d → F`
together with its weight, or a null record.  For every input
`x : Fin n → Option ((Fin d → F) × W)`, the canonical positions form a minimum-weight subset
of the input whose vectors are a basis of the span of the input vectors, and computing these
positions, or the selected records, costs `Q_{1/3} ≤ min{n, 2^18·√(n·d)}`, uniformly in the
field, the weight alphabet and the weights.  Any public linear order on the vectors may be
used to break ties (for instance `vectorLinearOrder`). -/
theorem vectorBasis_minWeight_and_qQuery {F : Type} [Field F] [Fintype F]
    [LinearOrder (Fin d → F)] (weight : W ↪o ℝ) (n : ℕ) :
    (∀ x : Fin n → Option ((Fin d → F) × W),
      (∀ s ∈ basisRecords (vectorMatroid F (Fin d → F)) x Finset.univ,
        x s.index = some (s.element, s.weight)) ∧
      IsInputSpanBasis F x Finset.univ
        (basisIndices (vectorMatroid F (Fin d → F)) x Finset.univ) ∧
      ∀ J : Finset (Fin n), IsInputSpanBasis F x Finset.univ J →
        ∑ i ∈ basisIndices (vectorMatroid F (Fin d → F)) x Finset.univ,
            inputWeight weight x i ≤
          ∑ i ∈ J, inputWeight weight x i) ∧
    (qQuery (fun x : Fin n → Option ((Fin d → F) × W) =>
        basisRecords (vectorMatroid F (Fin d → F)) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * d)) ∧
    (qQuery (fun x : Fin n → Option ((Fin d → F) × W) =>
        basisIndices (vectorMatroid F (Fin d → F)) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * d)) :=
  vectorBasis_minWeight_and_qQuery_of_finrank_le weight (Module.finrank_fin_fun (R := F)).le n

end Query

/-! ### Equal weights: a basis of the input span -/

section EqualWeights

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Fintype V] [LinearOrder V]
variable {n : ℕ}

/-- An unweighted input, with every vector given the same (unit) weight. -/
def unitWeightedInput {ι : Type*} (y : ι → Option V) : ι → Option (V × Unit) :=
  fun i => (y i).map fun v => (v, ())

/-- The canonical selected records of an unweighted input. -/
noncomputable def spanBasisRecords (F : Type) [Field F] [Module F V] (y : Fin n → Option V) :
    Finset (WeightedRecord (Fin n) V Unit) :=
  basisRecords (vectorMatroid F V) (unitWeightedInput y) Finset.univ

/-- The positions of the canonical basis of the span of an unweighted input. -/
noncomputable def spanBasisIndices (F : Type) [Field F] [Module F V] (y : Fin n → Option V) :
    Finset (Fin n) :=
  (spanBasisRecords F y).image WeightedRecord.index

/-- The vectors of the canonical basis of the span of an unweighted input. -/
noncomputable def spanBasisVectors (F : Type) [Field F] [Module F V] (y : Fin n → Option V) :
    Finset V :=
  (spanBasisRecords F y).image WeightedRecord.element

/-- The set of vectors occurring in an unweighted input. -/
def inputVectorSet {ι : Type*} (y : ι → Option V) : Set V :=
  {v | ∃ i, y i = some v}

lemma inputElements_unitWeightedInput (y : Fin n → Option V) :
    inputElements (unitWeightedInput y) Finset.univ = inputVectorSet y := by
  ext v
  constructor
  · rintro ⟨i, -, w, h⟩
    refine ⟨i, ?_⟩
    unfold unitWeightedInput at h
    cases hy : y i with
    | none => rw [hy] at h; cases h
    | some u => rw [hy] at h; cases h; rfl
  · rintro ⟨i, h⟩
    exact ⟨i, Finset.mem_univ _, (), by rw [unitWeightedInput, h]; rfl⟩

lemma inputVector_unitWeightedInput (y : Fin n → Option V) (i : Fin n) :
    inputVector (unitWeightedInput y) i = (y i).getD 0 := by
  unfold inputVector unitWeightedInput
  cases y i <;> rfl

/-- **Equal weights: the canonical positions form a basis of the input span**
(`sec:matroid-bases`, vector matroid).  The returned positions carry nonnull records whose
vectors are linearly independent and span the span of all the input vectors; the returned
vectors are a linearly independent set of input vectors with the same span. -/
theorem spanBasis_isBasis (y : Fin n → Option V) :
    (∀ i ∈ spanBasisIndices F y, (y i).isSome) ∧
      LinearIndepOn F (fun i => (y i).getD 0) (spanBasisIndices F y : Set (Fin n)) ∧
      Submodule.span F ((fun i => (y i).getD 0) '' (spanBasisIndices F y : Set (Fin n))) =
        Submodule.span F (inputVectorSet y) ∧
    (spanBasisVectors F y : Set V) ⊆ inputVectorSet y ∧
      LinearIndepOn F id (spanBasisVectors F y : Set V) ∧
      Submodule.span F (spanBasisVectors F y : Set V) = Submodule.span F (inputVectorSet y) := by
  have hI : spanBasisIndices F y =
      basisIndices (vectorMatroid F V) (unitWeightedInput y) Finset.univ := rfl
  have hR : spanBasisVectors F y =
      (basisRecords (vectorMatroid F V) (unitWeightedInput y) Finset.univ).image
        WeightedRecord.element := rfl
  rw [hI, hR]
  obtain ⟨-, hs, hlin, hspan⟩ := isParallelBasis_vectorMatroid_iff.1
    (isParallelBasis_basisIndices (vectorMatroid_ground (F := F))
      (unitWeightedInput y) Finset.univ)
  have hv : inputVector (unitWeightedInput y) = fun i => (y i).getD 0 :=
    funext (inputVector_unitWeightedInput y)
  have hvec : (((basisRecords (vectorMatroid F V) (unitWeightedInput y) Finset.univ).image
        WeightedRecord.element : Finset V) : Set V) =
      inputVector (unitWeightedInput y) ''
        (basisIndices (vectorMatroid F V) (unitWeightedInput y) Finset.univ : Set (Fin n)) := by
    rw [← inputElements_eq_image hs, ← image_element_records, records_basisIndices,
      Finset.coe_image]
  rw [inputElements_unitWeightedInput] at hspan
  have hsome : ∀ i ∈ basisIndices (vectorMatroid F V) (unitWeightedInput y) Finset.univ,
      (y i).isSome := fun i hi => by
    have := hs i hi
    simpa [unitWeightedInput] using this
  refine ⟨hsome, hv ▸ hlin, hv ▸ hspan, ?_, ?_, ?_⟩
  · rw [hvec, ← inputElements_eq_image hs, ← inputElements_unitWeightedInput y]
    intro v ⟨i, _, w, h⟩
    exact ⟨i, Finset.mem_univ _, w, h⟩
  · rw [hvec]
    exact hlin.id_image
  · rw [hvec, hspan]

/-- The incremental summary for an unweighted input: the canonical state of the unit-weight
input, read through the physical alphabet `Option V`. -/
noncomputable def spanBasisSummary {O : Type} (g : Finset (WeightedRecord (Fin n) V Unit) → O) :
    IncrementalSummary (Fin n) (Option V) O (Finset (WeightedRecord (Fin n) V Unit)) where
  state y T := basisRecords (vectorMatroid F V) (unitWeightedInput y) T
  out y := g (basisRecords (vectorMatroid F V) (unitWeightedInput y) Finset.univ)
  state_empty _ _ := by rw [basisRecords_empty, basisRecords_empty]
  state_insert y z _ i _ hT hi := basisRecords_insert_congr vectorMatroid_ground hT
    (by simp only [unitWeightedInput, hi])
  out_congr _ _ h := congrArg g h

/-- The essential width of the unweighted summary is at most the dimension. -/
lemma card_essentialSet_spanBasisSummary_le {O : Type} [Fintype O] [DecidableEq O] {d : ℕ}
    (hd : Module.finrank F V ≤ d) (g : Finset (WeightedRecord (Fin n) V Unit) → O)
    (y : Fin n → Option V) (T : Finset (Fin n)) :
    ((spanBasisSummary (F := F) g).essentialSet y T).card ≤ d := by
  classical
  have hr : (vectorMatroid F V).eRank ≤ d := eRank_vectorMatroid_le.trans (by exact_mod_cast hd)
  refine le_trans (Finset.card_le_card fun i hi => ?_)
    (card_essentialSet_matroidBasisSummary_le vectorMatroid_ground hr g
      (unitWeightedInput y) T)
  rw [IncrementalSummary.mem_essentialSet] at hi ⊢
  exact hi

/-- **Equal weights, operational** (`sec:matroid-bases`, vector matroid): for unweighted
input `y : Fin n → Option V` in a vector space of dimension at most `d`, any readout of the
canonical records costs `Q_{1/3} ≤ min{n, 2^18·√(n·d)}` against the oracle returning a whole
vector (or a null record). -/
theorem spanBasisReadout_qQuery_le_min_sqrt {O : Type} [Fintype O] [DecidableEq O]
    [Nonempty O] {d : ℕ} (hd : Module.finrank F V ≤ d) (n : ℕ)
    (g : Finset (WeightedRecord (Fin n) V Unit) → O) :
    (qQuery (fun y : Fin n → Option V => g (spanBasisRecords F y)) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * d)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : qQuery (fun y : Fin 0 → Option V => g (spanBasisRecords F y)) (1 / 3) = 0 :=
      qQueryOn_const_eq_zero id (c := g (spanBasisRecords F (fun i => i.elim0)))
        (fun y => by rw [Subsingleton.elim y (fun i => i.elim0)]) (by norm_num)
    rw [h0]
    simp
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have h := summary_qQuery_le_min_sqrt (spanBasisSummary (F := F) g)
      (card_essentialSet_spanBasisSummary_le hd g)
    rw [Fintype.card_fin] at h
    exact h

/-- **Equal weights: computing a basis of the input span** (`sec:matroid-bases`, vector
matroid on `𝔽_q^d`).  For unweighted input `y : Fin n → Option (Fin d → F)` over a finite
field, the returned positions, and the returned vectors, form a basis of the span of the
input vectors; computing either costs `Q_{1/3} ≤ min{n, 2^18·√(n·d)}` against the oracle
returning a whole vector, uniformly in the field. -/
theorem spanBasis_isBasis_and_qQuery {F : Type} [Field F] [Fintype F] {d : ℕ}
    [LinearOrder (Fin d → F)] (n : ℕ) :
    (∀ y : Fin n → Option (Fin d → F),
      (∀ i ∈ spanBasisIndices F y, (y i).isSome) ∧
        LinearIndepOn F (fun i => (y i).getD 0) (spanBasisIndices F y : Set (Fin n)) ∧
        Submodule.span F ((fun i => (y i).getD 0) '' (spanBasisIndices F y : Set (Fin n))) =
          Submodule.span F (inputVectorSet y) ∧
      (spanBasisVectors F y : Set (Fin d → F)) ⊆ inputVectorSet y ∧
        LinearIndepOn F id (spanBasisVectors F y : Set (Fin d → F)) ∧
        Submodule.span F (spanBasisVectors F y : Set (Fin d → F)) =
          Submodule.span F (inputVectorSet y)) ∧
    (qQuery (fun y : Fin n → Option (Fin d → F) => spanBasisIndices F y) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * d)) ∧
    (qQuery (fun y : Fin n → Option (Fin d → F) => spanBasisVectors F y) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * d)) :=
  ⟨spanBasis_isBasis,
    spanBasisReadout_qQuery_le_min_sqrt (Module.finrank_fin_fun (R := F)).le n
      (Finset.image WeightedRecord.index),
    spanBasisReadout_qQuery_le_min_sqrt (Module.finrank_fin_fun (R := F)).le n
      (Finset.image WeightedRecord.element)⟩

end EqualWeights

/-! ### A public order on `Fin d → F` -/

/-- A fixed public linear order on the vectors of `Fin d → F`, transported from `Fin` along
an enumeration of the finite type.  Any linear order may be used for the canonical
answer. -/
@[instance_reducible]
noncomputable def vectorLinearOrder (F : Type) [Fintype F] (d : ℕ) :
    LinearOrder (Fin d → F) := by
  classical
  exact LinearOrder.lift' (Fintype.equivFin (Fin d → F)) (Equiv.injective _)

/-- The position bound instantiated with the order `vectorLinearOrder`. -/
example {F : Type} [Field F] [Fintype F] {W : Type} [Fintype W] [LinearOrder W]
    (weight : W ↪o ℝ) (d n : ℕ) :
    letI := vectorLinearOrder F d
    (qQuery (fun x : Fin n → Option ((Fin d → F) × W) =>
        basisIndices (vectorMatroid F (Fin d → F)) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * d)) :=
  letI := vectorLinearOrder F d
  (vectorBasis_minWeight_and_qQuery weight n).2.2

end MonoidProduct.Matroid
