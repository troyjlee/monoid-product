import MonoidProduct.Certificates.ExtensionMonoid
import MonoidProduct.Width.Breadth
import Mathlib.Data.Finset.Option
set_option linter.style.header false

/-!
# Strong certificates and product breadth

`monoid.tex`, section `sec:strong-certificates`, `thm:certificate-breadth`:

  `β_{A_f}(M_f) = β(M_f) = b_f(U)`,

for the alphabet `A_f = {[∅]} ∪ {[{u}] : u ∈ U}` of the extension monoid `M_f`.

The alphabet is the image of the letter map `extensionLetter f : Option U → M_f`, which sends
the null record `none` to the identity `[∅]` and `some u` to `[{u}]`.  The library's breadth
`breadth letter` (`Width/Breadth.lean`) is the paper's `β_G(M)` for the image `G` of `letter`,
and `breadth id` is `β(M)`, for the full alphabet.

* `prod_extensionLetter`: a product of letters is the class of the union of the nonnull
  records, so a core of a word is a set of positions whose records form a set with the same
  class.
* `isBreadthBound_extensionLetter_iff`, `isBreadthBound_id_iff`: for every `b`, `b` is a
  breadth bound (for either alphabet) exactly when it is a uniform strong-certificate bound.
  One direction lists a set once, without repetition: a core of that word is a strong
  certificate.  The other chooses a small certificate of the union of arbitrary
  representatives, keeps one factor covering each certificate element, and applies the
  interval lemma.  Repeated letters, the identity, an empty certificate and the empty word are
  all covered.
* `extensionLetter_breadth_eq`, `extensionMonoid_breadth_eq`: the theorem.  The three sets of
  bounds coincide, so the equalities need no finiteness hypothesis.  Over a finite universe the
  common least bound is itself a bound (`hasStrongCertificateBound_strongCertificateSize`).

`recordSet x` is the set `{x_i : x_i ≠ ⊥}` of nonnull records of `x : ι → Option U`, the input
of `cor:certificate-queries`.
-/

namespace MonoidProduct.Certificates

open ExtensionMonoid

/-! ## Records -/

section Records

variable {U : Type*} [DecidableEq U]

/-- The set `{x_i : x_i ≠ ⊥}` of nonnull records of `x : ι → Option U`; repeated records
contribute one element. -/
def recordSet {ι : Type*} [Fintype ι] (x : ι → Option U) : Finset U :=
  Finset.univ.biUnion fun i => (x i).toFinset

theorem mem_recordSet {ι : Type*} [Fintype ι] {x : ι → Option U} {u : U} :
    u ∈ recordSet x ↔ ∃ i, x i = some u := by
  simp [recordSet]

/-- A set of positions covers at most as many records as it has positions. -/
theorem card_biUnion_toFinset_le {ι : Type*} (T : Finset ι) (x : ι → Option U) :
    (T.biUnion fun i => (x i).toFinset).card ≤ T.card := by
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ i ∈ T, ((x i).toFinset).card ≤ ∑ _i ∈ T, 1 :=
        Finset.sum_le_sum fun i _ => by cases x i <;> simp
    _ = T.card := by simp

end Records

/-! ## The alphabet `A_f` -/

section Letters

variable {U O : Type*} [DecidableEq U] {f : Finset U → O}

/-- **The letter map of `thm:certificate-breadth`**: the null record `none` is the identity
`[∅]`, and `some u` is `[{u}]`.  The alphabet `A_f` is the image of this map. -/
def extensionLetter (f : Finset U → O) (o : Option U) : ExtensionMonoid f :=
  mk f o.toFinset

@[simp] theorem extensionLetter_none : extensionLetter f none = 1 := rfl

@[simp] theorem extensionLetter_some (u : U) : extensionLetter f (some u) = mk f {u} := rfl

/-- A product of letters is the class of the union of the nonnull records. -/
theorem prod_extensionLetter {ι : Type*} (T : Finset ι) (x : ι → Option U) :
    ∏ i ∈ T, extensionLetter f (x i) = mk f (T.biUnion fun i => (x i).toFinset) :=
  prod_mk T _

/-- The product of a whole word is the class of its set of nonnull records. -/
theorem prod_univ_extensionLetter {ι : Type*} [Fintype ι] (x : ι → Option U) :
    ∏ i, extensionLetter f (x i) = mk f (recordSet x) :=
  prod_extensionLetter _ x

/-- Reading out the product of a word gives `f` of its set of nonnull records. -/
theorem readout_prod_extensionLetter {ι : Type*} [Fintype ι] (x : ι → Option U) :
    readout f (∏ i, extensionLetter f (x i)) = f (recordSet x) := by
  rw [prod_univ_extensionLetter, readout_mk]

end Letters

/-! ## Breadth bounds are certificate bounds -/

section Breadth

/-! The breadth API is stated for alphabets and monoids in `Type`. -/

variable {U : Type} {O : Type*} [DecidableEq U] {f : Finset U → O} {b : ℕ}

/-- A core of the word listing a set once is a strong certificate for that set. -/
theorem hasStrongCertificateBound_of_isBreadthBound (h : IsBreadthBound (extensionLetter f) b) :
    HasStrongCertificateBound f b := by
  intro S
  let x : Fin S.card → Option U := fun j => some (S.equivFin.symm j : U)
  obtain ⟨u, hu, hcore⟩ := h S.card x
  rw [isCore_iff, prod_extensionLetter, prod_extensionLetter] at hcore
  have hall : (Finset.univ.biUnion fun j => (x j).toFinset) = S := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, x, Option.mem_toFinset,
      Option.mem_def, Option.some.injEq]
    constructor
    · rintro ⟨j, rfl⟩
      exact (S.equivFin.symm j).2
    · intro ha
      exact ⟨S.equivFin ⟨a, ha⟩, by simp⟩
  have hsub : (u.biUnion fun j => (x j).toFinset) ⊆ Finset.univ.biUnion fun j => (x j).toFinset :=
    Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_univ u)
  rw [hall] at hsub hcore
  exact ⟨_, ⟨hsub, mk_eq_mk.mp hcore⟩, (card_biUnion_toFinset_le u x).trans hu⟩

/-- A small certificate of the union of the records gives a small core: keep one position
covering each certificate element. -/
theorem isBreadthBound_of_hasStrongCertificateBound (h : HasStrongCertificateBound f b) :
    IsBreadthBound (extensionLetter f) b := by
  intro n x
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact ⟨Finset.univ, by simp, isCore_univ _ x⟩
  obtain ⟨C, hC, hcard⟩ := h (Finset.univ.biUnion fun i => (x i).toFinset)
  have hpick : ∀ c ∈ C, ∃ i, x i = some c := fun c hc => by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hC.1 hc)
    exact ⟨i, Option.mem_def.mp (Option.mem_toFinset.mp hi)⟩
  choose! pick hpick using hpick
  refine ⟨C.image pick, Finset.card_image_le.trans hcard, ?_⟩
  rw [isCore_iff, prod_extensionLetter, prod_extensionLetter]
  refine mk_eq_mk.mpr (hC.of_subset (fun c hc => ?_) ?_).2
  · refine Finset.mem_biUnion.mpr ⟨pick c, Finset.mem_image_of_mem pick hc, ?_⟩
    rw [hpick c hc]
    exact Option.mem_toFinset.mpr rfl
  · exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_univ _)

/-- The same for arbitrary factors `[S₁], …, [Sₛ]`: choose representatives, take a small
certificate of their union, and keep one factor covering each of its elements. -/
theorem isBreadthBound_id_of_hasStrongCertificateBound (h : HasStrongCertificateBound f b) :
    IsBreadthBound (id : ExtensionMonoid f → ExtensionMonoid f) b := by
  intro n x
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact ⟨Finset.univ, by simp, isCore_univ _ x⟩
  choose R hR using fun i => mk_surjective (f := f) (x i)
  obtain rfl : x = fun i => mk f (R i) := funext fun i => (hR i).symm
  obtain ⟨C, hC, hcard⟩ := h (Finset.univ.biUnion R)
  have hpick : ∀ c ∈ C, ∃ i, c ∈ R i := fun c hc => by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hC.1 hc)
    exact ⟨i, hi⟩
  choose! pick hpick using hpick
  refine ⟨C.image pick, Finset.card_image_le.trans hcard, ?_⟩
  rw [isCore_iff]
  simp only [id]
  rw [prod_mk, prod_mk]
  refine mk_eq_mk.mpr (hC.of_subset (fun c hc => ?_) ?_).2
  · exact Finset.mem_biUnion.mpr ⟨pick c, Finset.mem_image_of_mem pick hc, hpick c hc⟩
  · exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_univ _)

/-- A breadth bound for the full alphabet is one for the letters `A_f ⊆ M_f`. -/
theorem isBreadthBound_extensionLetter_of_id
    (h : IsBreadthBound (id : ExtensionMonoid f → ExtensionMonoid f) b) :
    IsBreadthBound (extensionLetter f) b := fun n x => by
  obtain ⟨u, hu, hcore⟩ := h n fun i => extensionLetter f (x i)
  refine ⟨u, hu, ?_⟩
  rw [isCore_iff] at hcore ⊢
  simpa only [id] using hcore

/-- **Breadth bounds for `A_f` are strong-certificate bounds.** -/
theorem isBreadthBound_extensionLetter_iff :
    IsBreadthBound (extensionLetter f) b ↔ HasStrongCertificateBound f b :=
  ⟨hasStrongCertificateBound_of_isBreadthBound, isBreadthBound_of_hasStrongCertificateBound⟩

/-- **Breadth bounds for the full alphabet of `M_f` are strong-certificate bounds.** -/
theorem isBreadthBound_id_iff :
    IsBreadthBound (id : ExtensionMonoid f → ExtensionMonoid f) b ↔
      HasStrongCertificateBound f b :=
  ⟨fun h => hasStrongCertificateBound_of_isBreadthBound (isBreadthBound_extensionLetter_of_id h),
    isBreadthBound_id_of_hasStrongCertificateBound⟩

variable (f) in
/-- **`thm:certificate-breadth`, the alphabet `A_f`**: `β_{A_f}(M_f) = b_f(U)`. -/
theorem extensionLetter_breadth_eq : breadth (extensionLetter f) = strongCertificateSize f := by
  simp only [breadth, strongCertificateSize, isBreadthBound_extensionLetter_iff]

variable (f) in
/-- **`thm:certificate-breadth`, the full alphabet**: `β(M_f) = b_f(U)`. -/
theorem extensionMonoid_breadth_eq :
    breadth (id : ExtensionMonoid f → ExtensionMonoid f) = strongCertificateSize f := by
  simp only [breadth, strongCertificateSize, isBreadthBound_id_iff]

variable (f) in
/-- **`thm:certificate-breadth`** as displayed: `β_{A_f}(M_f) = β(M_f) = b_f(U)`. -/
theorem certificate_breadth :
    breadth (extensionLetter f) = breadth (id : ExtensionMonoid f → ExtensionMonoid f) ∧
      breadth (id : ExtensionMonoid f → ExtensionMonoid f) = strongCertificateSize f :=
  ⟨(extensionLetter_breadth_eq f).trans (extensionMonoid_breadth_eq f).symm,
    extensionMonoid_breadth_eq f⟩

end Breadth

end MonoidProduct.Certificates
