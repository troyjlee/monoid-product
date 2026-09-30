import MonoidProduct.Matroid.Greedy
import MonoidProduct.Width.PaperForms
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The greedy-basis monoid and its product breadth

`monoid.tex`, section `sec:matroid-bases`, Proposition `prop:matroid-greedy-monoid`.

Fix a matroid `M` whose ground set is all of a linearly ordered type `E`.  The independent
finite sets form a commutative idempotent monoid `GreedyBasisMonoid M hM` under

  `A * C = B(A ∪ C)`,  identity `∅`,

where `B = greedy M` is the greedy basis of `Greedy.lean`.  Associativity is the merge law
`lem:matroid-greedy-merge` (`greedy_union_eq_greedy_union_greedy`); the identity and
idempotence laws hold because greedy leaves independent sets unchanged.  Idempotence gives
the aperiodicity instance (the powers stabilise at exponent one).

The alphabet of the proposition is `greedyBasisLetter M hM : Option E → _`, sending `none`
to the identity and `some e` to `B({e})` (which is `∅` when `e` is a loop).  The product
of a family of letters is the greedy basis of the union of their elements
(`prod_greedyBasisLetter`).  Consequently:

* `isBreadthBound_greedyBasisLetter`: if `M.eRank ≤ r` then every word has a core of at
  most `r` letters — keep one occurrence of each element of the final basis;
* `greedyBasis_breadth_eq_rank`: if `M.eRank = r` then `β_G(H) = r` exactly — the
  singleton letters of a basis of `E` form a word no proper subword of which has the same
  product (rank zero included);
* `greedyBasis_qQuery_le_min`: the resulting bound
  `Q_{1/3} ≤ min{n, 2¹⁸·√(n·min{n, r})}` for the product of `n` letters, from the query
  clause of `thm:commutative-beta` (`qQuery_prodFun_le_min_of_breadth_le`).

The monoid instances live on the new type only, never on `Finset E`.  The hypothesis
`hM : M.E = Set.univ` is a parameter of the type, since the product of two independent
sets is independent only for such matroids.
-/

namespace MonoidProduct.Matroid

open QuantumQueryComplexity

section Monoid

variable {E : Type*} [LinearOrder E] {M : _root_.Matroid E} {hM : M.E = Set.univ}

/-- Greedy absorbs a greedy basis on the left of a union. -/
lemma greedy_greedy_union (hM : M.E = Set.univ) (S T : Finset E) :
    greedy M (greedy M S ∪ T) = greedy M (S ∪ T) := by
  rw [greedy_union_eq_greedy_union_greedy hM (greedy M S), greedy_greedy hM,
    ← greedy_union_eq_greedy_union_greedy hM]

/-- Greedy absorbs a greedy basis on the right of a union. -/
lemma greedy_union_greedy (hM : M.E = Set.univ) (S T : Finset E) :
    greedy M (S ∪ greedy M T) = greedy M (S ∪ T) := by
  rw [Finset.union_comm, greedy_greedy_union hM, Finset.union_comm]

/-- The monoid `H` of `prop:matroid-greedy-monoid`: the independent finite sets of a
matroid on a linearly ordered type, with product `A * C = B(A ∪ C)`. -/
@[ext] structure GreedyBasisMonoid (M : _root_.Matroid E) (hM : M.E = Set.univ) where
  /-- The underlying independent set. -/
  val : Finset E
  /-- The underlying set is independent. -/
  indep : M.Indep ↑val

namespace GreedyBasisMonoid

variable (hM) in
/-- The greedy basis `B(S)` of a finite set, as an element of the monoid. -/
noncomputable def ofGreedy (S : Finset E) : GreedyBasisMonoid M hM :=
  ⟨greedy M S, indep_greedy hM S⟩

@[simp] lemma val_ofGreedy (S : Finset E) : (ofGreedy hM S).val = greedy M S := rfl

/-- Every element is the greedy basis of itself. -/
@[simp] lemma ofGreedy_val (A : GreedyBasisMonoid M hM) : ofGreedy hM A.val = A :=
  GreedyBasisMonoid.ext (greedy_eq_self_of_indep A.indep)

lemma ofGreedy_greedy (S : Finset E) : ofGreedy hM (greedy M S) = ofGreedy hM S :=
  GreedyBasisMonoid.ext (greedy_greedy hM S)

noncomputable instance : One (GreedyBasisMonoid M hM) := ⟨⟨∅, by simp⟩⟩

noncomputable instance : Mul (GreedyBasisMonoid M hM) :=
  ⟨fun A C => ofGreedy hM (A.val ∪ C.val)⟩

@[simp] lemma val_one : (1 : GreedyBasisMonoid M hM).val = ∅ := rfl

@[simp] lemma val_mul (A C : GreedyBasisMonoid M hM) : (A * C).val = greedy M (A.val ∪ C.val) :=
  rfl

@[simp] lemma ofGreedy_empty : ofGreedy hM (∅ : Finset E) = 1 :=
  GreedyBasisMonoid.ext (greedy_empty M)

/-- The product of two greedy bases is the greedy basis of the union (the merge law
`lem:matroid-greedy-merge`). -/
lemma ofGreedy_mul_ofGreedy (S T : Finset E) :
    ofGreedy hM S * ofGreedy hM T = ofGreedy hM (S ∪ T) := by
  ext1
  simp only [val_mul, val_ofGreedy]
  exact (greedy_union_eq_greedy_union_greedy hM S T).symm

/-- `prop:matroid-greedy-monoid`: the independent sets form a commutative monoid under
`A * C = B(A ∪ C)`, with identity `∅`. -/
noncomputable instance instCommMonoid : CommMonoid (GreedyBasisMonoid M hM) where
  mul_assoc A C D := by
    rw [← ofGreedy_val A, ← ofGreedy_val C, ← ofGreedy_val D, ofGreedy_mul_ofGreedy,
      ofGreedy_mul_ofGreedy, ofGreedy_mul_ofGreedy, ofGreedy_mul_ofGreedy, Finset.union_assoc]
  one_mul A := by
    rw [← ofGreedy_val A, ← ofGreedy_empty, ofGreedy_mul_ofGreedy, Finset.empty_union]
  mul_one A := by
    rw [← ofGreedy_val A, ← ofGreedy_empty, ofGreedy_mul_ofGreedy, Finset.union_empty]
  mul_comm A C := GreedyBasisMonoid.ext (by simp only [val_mul, Finset.union_comm])

/-- The greedy-basis monoid is idempotent: `A * A = A`. -/
@[simp] lemma mul_self_greedyBasis (A : GreedyBasisMonoid M hM) : A * A = A := by
  rw [← ofGreedy_val A, ofGreedy_mul_ofGreedy, Finset.union_self]

/-- An idempotent monoid is aperiodic, with stabilisation at exponent one. -/
instance instIsAperiodicMonoid : IsAperiodicMonoid (GreedyBasisMonoid M hM) :=
  ⟨fun A => ⟨1, one_pos, by rw [pow_one, pow_two, mul_self_greedyBasis]⟩⟩

open scoped Classical in
noncomputable instance instDecidableEq : DecidableEq (GreedyBasisMonoid M hM) :=
  Classical.decEq _

lemma val_injective : Function.Injective (GreedyBasisMonoid.val (M := M) (hM := hM)) :=
  fun _ _ h => GreedyBasisMonoid.ext h

open scoped Classical in
/-- Over a finite ground type the monoid is finite. -/
noncomputable instance instFintype [Fintype E] : Fintype (GreedyBasisMonoid M hM) :=
  Fintype.ofInjective _ val_injective

/-- A product over a finite family of greedy bases is the greedy basis of the union. -/
lemma prod_ofGreedy {ι : Type*} (T : Finset ι) (f : ι → Finset E) :
    ∏ i ∈ T, ofGreedy hM (f i) = ofGreedy hM (T.biUnion f) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, ih, ofGreedy_mul_ofGreedy, Finset.biUnion_insert]

end GreedyBasisMonoid

open GreedyBasisMonoid

variable (M hM) in
/-- The alphabet `G = {∅} ∪ {B({e}) : e ∈ E}` of `prop:matroid-greedy-monoid`, indexed by
`Option E`: `none` is the identity and `some e` is the greedy basis of `{e}`. -/
noncomputable def greedyBasisLetter (o : Option E) : GreedyBasisMonoid M hM :=
  ofGreedy hM o.toFinset

@[simp] lemma greedyBasisLetter_none : greedyBasisLetter M hM none = 1 := by
  simp [greedyBasisLetter]

@[simp] lemma val_greedyBasisLetter_some (e : E) :
    (greedyBasisLetter M hM (some e)).val = greedy M {e} := by
  simp [greedyBasisLetter]

/-- A loop letter is the identity. -/
lemma greedyBasisLetter_some_of_isLoop {e : E} (he : M.IsLoop e) :
    greedyBasisLetter M hM (some e) = 1 := by
  ext1
  rw [val_greedyBasisLetter_some, val_one, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  have hxe : x = e := Finset.mem_singleton.1 (greedy_subset M {e} hx)
  subst hxe
  have hind : M.Indep {x} :=
    (indep_greedy hM {x}).subset (Set.singleton_subset_iff.2 (Finset.mem_coe.2 hx))
  exact (_root_.Matroid.indep_singleton.1 hind).not_isLoop he

/-- A product of letters is the greedy basis of the union of their elements. -/
theorem prod_greedyBasisLetter {ι : Type*} (T : Finset ι) (x : ι → Option E) :
    ∏ i ∈ T, greedyBasisLetter M hM (x i) = ofGreedy hM (T.biUnion fun i => (x i).toFinset) :=
  prod_ofGreedy T _

/-- The underlying set of a product of letters: the greedy basis of the union of the
elements of the letters. -/
theorem val_prod_greedyBasisLetter {ι : Type*} (T : Finset ι) (x : ι → Option E) :
    (∏ i ∈ T, greedyBasisLetter M hM (x i)).val =
      greedy M (T.biUnion fun i => (x i).toFinset) := by
  rw [prod_greedyBasisLetter, val_ofGreedy]

/-- An independent finite set has at most `r` elements when `M.eRank ≤ r`. -/
lemma card_le_of_indep_of_eRank_le {I : Finset E} (hI : M.Indep ↑I) {r : ℕ}
    (hr : M.eRank ≤ r) : I.card ≤ r := by
  have h := hI.encard_le_eRank.trans hr
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

end Monoid

/-! ## Product breadth

The breadth API of `Width/Breadth.lean` is stated for alphabets and monoids in `Type`. -/

section Breadth

open GreedyBasisMonoid

variable {E : Type} [LinearOrder E] {M : _root_.Matroid E} {hM : M.E = Set.univ}

/-- The upper half of `prop:matroid-greedy-monoid`: when `M.eRank ≤ r`, every word over
the alphabet has a core of at most `r` letters, so `β_G(H) ≤ r`. -/
theorem isBreadthBound_greedyBasisLetter {r : ℕ} (hr : M.eRank ≤ r) :
    IsBreadthBound (greedyBasisLetter M hM) r := by
  classical
  intro n x
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact ⟨Finset.univ, by simp, isCore_univ _ x⟩
  set S : Finset E := Finset.univ.biUnion fun i => (x i).toFinset with hS
  have hpick : ∀ e ∈ greedy M S, ∃ i, x i = some e := by
    intro e he
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (greedy_subset M S he)
    exact ⟨i, Option.mem_toFinset.1 hi⟩
  choose! pick hpick using hpick
  refine ⟨(greedy M S).image pick, ?_, ?_⟩
  · exact Finset.card_image_le.trans (card_le_of_indep_of_eRank_le (indep_greedy hM S) hr)
  · rw [isCore_iff, prod_greedyBasisLetter, prod_greedyBasisLetter, ← hS]
    have hU : ((greedy M S).image pick).biUnion (fun i => (x i).toFinset) = greedy M S := by
      rw [Finset.image_biUnion]
      refine (Finset.biUnion_congr rfl fun e he => by rw [hpick e he]).trans ?_
      exact Finset.biUnion_singleton_eq_self
    rw [hU, ofGreedy_greedy]

/-- The breadth of the alphabet is finite whenever the rank is. -/
lemma exists_isBreadthBound_greedyBasisLetter {r : ℕ} (hr : M.eRank ≤ r) :
    ∃ b, IsBreadthBound (greedyBasisLetter M hM) b :=
  ⟨r, isBreadthBound_greedyBasisLetter hr⟩

/-- `β_G(H) ≤ r` whenever `M.eRank ≤ r`. -/
theorem greedyBasis_breadth_le {r : ℕ} (hr : M.eRank ≤ r) :
    breadth (greedyBasisLetter M hM) ≤ r :=
  breadth_le (isBreadthBound_greedyBasisLetter hr)

/-- The lower half of `prop:matroid-greedy-monoid`: the singleton letters of a basis of `E`
form a word every core of which is the whole word, so `r ≤ β_G(H)` when `M.eRank = r`. -/
theorem le_greedyBasis_breadth {r : ℕ} (hr : M.eRank = r) :
    r ≤ breadth (greedyBasisLetter M hM) := by
  classical
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hBenc : B.encard = r := hB.encard_eq_eRank.trans hr
  have hBfin : B.Finite := Set.finite_of_encard_eq_coe hBenc
  set F : Finset E := hBfin.toFinset with hF
  have hFB : (↑F : Set E) = B := hBfin.coe_toFinset
  have hFcard : F.card = r := by
    have h := hBenc
    rw [← hFB, Set.encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  let x : Fin F.card → Option E := fun j => some (F.equivFin.symm j).val
  refine hFcard ▸ le_breadth_of_forall_core
    (exists_isBreadthBound_greedyBasisLetter hr.le) x fun u hu => ?_
  rw [isCore_iff, prod_greedyBasisLetter, prod_greedyBasisLetter] at hu
  have hbu : ∀ v : Finset (Fin F.card), v.biUnion (fun i => (x i).toFinset) =
      v.image fun j => (F.equivFin.symm j).val := by
    intro v
    ext e
    simp [x, Finset.mem_biUnion, Finset.mem_image, eq_comm]
  have hsub : ∀ v : Finset (Fin F.card),
      M.Indep ↑(v.image fun j => (F.equivFin.symm j).val) := by
    intro v
    refine hB.indep.subset ?_
    rw [← hFB]
    intro e he
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
    exact Finset.mem_coe.2 (F.equivFin.symm j).2
  have hval := congrArg GreedyBasisMonoid.val hu
  simp only [val_ofGreedy, hbu] at hval
  rw [greedy_eq_self_of_indep (hsub u), greedy_eq_self_of_indep (hsub _)] at hval
  have hinj : Function.Injective fun j : Fin F.card => (F.equivFin.symm j).val :=
    fun a b h => F.equivFin.symm.injective (Subtype.ext h)
  have := congrArg Finset.card hval
  rw [Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin] at this
  exact this.ge

/-- **`prop:matroid-greedy-monoid`**: for a matroid of rank `r` on a linearly ordered type,
the alphabet `G = {∅} ∪ {B({e}) : e ∈ E}` has product breadth exactly `r` in the
greedy-basis monoid. -/
theorem greedyBasis_breadth_eq_rank {r : ℕ} (hr : M.eRank = r) :
    breadth (greedyBasisLetter M hM) = r :=
  (greedyBasis_breadth_le hr.le).antisymm (le_greedyBasis_breadth hr)

end Breadth

section Query

variable {E : Type} [LinearOrder E] [Fintype E] {M : _root_.Matroid E} {hM : M.E = Set.univ}

/-- The query clause of `thm:commutative-beta` for the greedy-basis monoid of
`prop:matroid-greedy-monoid`: if `M.eRank ≤ r`, the product of `n` letters (the greedy
basis of the union of the elements read) is computed with bounded error using
`min{n, 2¹⁸·√(n·min{n, r})}` queries. -/
theorem greedyBasis_qQuery_le_min {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {r : ℕ} (hr : M.eRank ≤ r) :
    (qQuery (fun x : ι → Option E => ∏ i, greedyBasisLetter M hM (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * min (Fintype.card ι : ℝ) r)) :=
  qQuery_prodFun_le_min_of_breadth_le _ (by exact_mod_cast greedyBasis_breadth_le hr)

end Query

section Examples

variable {E : Type} [LinearOrder E]

/-- Rank zero: the breadth is zero, so every word's product is the identity. -/
example {M : _root_.Matroid E} (hM : M.E = Set.univ) (h0 : M.eRank = 0) {n : ℕ}
    (x : Fin n → Option E) : ∏ i, greedyBasisLetter M hM (x i) = 1 := by
  have hb : IsBreadthBound (greedyBasisLetter M hM) 0 :=
    isBreadthBound_greedyBasisLetter (by simp [h0])
  rw [← wordProd_eq_prod]
  exact wordProd_eq_one_of_isBreadthBound_zero hb x

/-- Rank zero: the breadth is exactly zero. -/
example {M : _root_.Matroid E} (hM : M.E = Set.univ) (h0 : M.eRank = 0) :
    breadth (greedyBasisLetter M hM) = 0 :=
  greedyBasis_breadth_eq_rank (r := 0) (by simpa using h0)

/-- A loop letter acts as the identity. -/
example {M : _root_.Matroid E} (hM : M.E = Set.univ) {e : E} (he : M.IsLoop e)
    (A : GreedyBasisMonoid M hM) : greedyBasisLetter M hM (some e) * A = A := by
  rw [greedyBasisLetter_some_of_isLoop he, one_mul]

/-- In the free matroid every element is its own letter, and the product of letters is the
set of elements read. -/
example (S : Finset E) :
    (∏ e ∈ S, greedyBasisLetter (_root_.Matroid.freeOn Set.univ)
      (_root_.Matroid.freeOn_ground) (some e)).val = S := by
  rw [val_prod_greedyBasisLetter, greedy_eq_self_of_indep (by simp)]
  ext e
  simp

end Examples

end MonoidProduct.Matroid
