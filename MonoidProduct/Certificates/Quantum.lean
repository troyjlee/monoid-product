import MonoidProduct.Certificates.Breadth
import MonoidProduct.Width.PaperForms
set_option linter.style.header false

/-!
# Queries from strong certificates

`monoid.tex`, section `sec:strong-certificates`, `cor:certificate-queries`: given `n` records
`x_i ∈ U ∪ {⊥}`, where one query reveals a record and `⊥` is a null record,

  `Q_{1/3}(x ↦ f({x_i : x_i ≠ ⊥})) ≤ min{n, 2^18·√(n·b_f(U))}`

for every function `f : Finset U → O` on a finite universe.  The constant is universal: it
depends on neither `U`, `O`, `f` nor `n`.  Records are `x : Fin n → Option U` (or `ι → Option U`
for a finite index type), with `none` the null record.  The output type `O` needs decidable
equality, as every output of the query model does, but need not be finite.

The proof is the paper's.  Encode `u` by `[{u}]` and `⊥` by the identity (`extensionLetter`);
the product of the encoded letters is the class of the set of nonnull records
(`prod_univ_extensionLetter`).  The query clause of `thm:commutative-beta`
(`qQuery_prodFun_le_min_of_breadth_le`) bounds the cost of computing that class by
`min{n, 2^18·√(n·min{n, β_{A_f}(M_f)})}`, `thm:certificate-breadth` identifies the breadth with
`b_f(U)`, and reading out `f` is free classical postprocessing (`qQueryOn_postcomp_le`).  The
letter map is part of the product theorem, so no alphabet-simulation factor arises.  An empty
index type is split off first: there the input space is a single point.

* `strongCertificate_qQuery_le_min_sqrt`: the corollary, for every `n`, including `n = 0`;
* `strongCertificate_qQuery_le_min_sqrt_of_bound`: against any certificate bound `b`;
* `strongCertificate_qQuery_le_min_sqrt_fintype`: over any finite index type;
* `strongCertificate_qQuery_eq_zero`: certificate size zero needs no query.

**Position-dependent encodings.**  `encodedCertificate_qQuery_le_min_sqrt` gives the same bound
when position `i` of an input `y : ι → A` encodes the record `enc i (y i)` through a public map
`enc : ι → A → Option U` that may depend on the position.  It is proved directly, through the
incremental summary whose state on revealed positions `T` is the class of their records
(`encodedSummary`): a position outside a fixed choice of one covering position per element of
a small certificate is never essential (`card_essentialSet_encodedSummary_le`).
-/

namespace MonoidProduct.Certificates

open QuantumQueryComplexity ExtensionMonoid

variable {U O : Type} [DecidableEq U] [DecidableEq O]

/-! ## Records -/

section Records

variable [Fintype U]

section IndexType

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq O] in
/-- **The class of the nonnull records** costs
`Q_{1/3} ≤ min{|ι|, 2^18·√(|ι|·b_f(U))}`: `thm:commutative-beta` for the letters `A_f`, with
`thm:certificate-breadth`. -/
theorem extensionLetter_qQuery_le_min_sqrt (f : Finset U → O) :
    (qQuery (fun x : ι → Option U => ∏ i, extensionLetter f (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * strongCertificateSize f)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : qQuery (fun x : ι → Option U => ∏ i, extensionLetter f (x i)) (1 / 3) = 0 :=
      qQueryOn_const_eq_zero id (c := 1) (fun x => by simp) (by norm_num)
    rw [h0, Fintype.card_eq_zero]
    simp
  · have h := qQuery_prodFun_le_min_of_breadth_le (ι := ι) (extensionLetter f)
      (b := (strongCertificateSize f : ℝ)) (by exact_mod_cast (extensionLetter_breadth_eq f).le)
    refine h.trans (min_le_min_left _ ?_)
    gcongr
    exact min_le_right _ _

/-- **Reading out `f` is free**: computing `f` of the nonnull records is no harder than
computing their class in `M_f`. -/
theorem qQuery_recordSet_le_qQuery_prod (f : Finset U → O) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : ι → Option U => f (recordSet x)) ε
      ≤ qQuery (fun x : ι → Option U => ∏ i, extensionLetter f (x i)) ε := by
  have hne : (QueryCounts (X := ι → Option U) id
      (fun x => ∏ i, extensionLetter f (x i)) ε).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [show x = y from h]) hε
  have h := qQueryOn_postcomp_le (read := (id : (ι → Option U) → ι → Option U))
    (f := fun x => ∏ i, extensionLetter f (x i)) (ε := ε) (readout f) hne
  simpa only [readout_prod_extensionLetter] using h

/-- **`cor:certificate-queries` over any finite index type**:
`Q_{1/3}(x ↦ f({x_i : x_i ≠ ⊥})) ≤ min{|ι|, 2^18·√(|ι|·b_f(U))}`. -/
theorem strongCertificate_qQuery_le_min_sqrt_fintype (f : Finset U → O) :
    (qQuery (fun x : ι → Option U => f (recordSet x)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * strongCertificateSize f)) :=
  le_trans (by exact_mod_cast qQuery_recordSet_le_qQuery_prod f (by norm_num))
    (extensionLetter_qQuery_le_min_sqrt f)

/-- **Certificate size zero: no query is needed**, at every error `ε ≥ 0`: the function is
constant. -/
theorem strongCertificate_qQuery_eq_zero {f : Finset U → O} (h0 : strongCertificateSize f = 0)
    {ε : ℝ} (hε : 0 ≤ ε) : qQuery (fun x : ι → Option U => f (recordSet x)) ε = 0 :=
  qQueryOn_const_eq_zero id (c := f ∅) (fun _ => strongCertificateSize_eq_zero_iff.mp h0 _ _) hε

end IndexType

/-- **`cor:certificate-queries`**: for `n` records `x : Fin n → Option U` (`none` is the null
record `⊥`), computing `f({x_i : x_i ≠ ⊥})` costs `Q_{1/3} ≤ min{n, 2^18·√(n·b_f(U))}`, for every
`n` and every `f : Finset U → O`.  The constant is universal. -/
theorem strongCertificate_qQuery_le_min_sqrt (f : Finset U → O) (n : ℕ) :
    (qQuery (fun x : Fin n → Option U => f (recordSet x)) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * strongCertificateSize f)) := by
  have h := strongCertificate_qQuery_le_min_sqrt_fintype (ι := Fin n) f
  rwa [Fintype.card_fin] at h

/-- **`cor:certificate-queries` against a certificate bound**: if every set has a strong
certificate of at most `b` elements, `Q_{1/3} ≤ min{n, 2^18·√(n·b)}`. -/
theorem strongCertificate_qQuery_le_min_sqrt_of_bound {f : Finset U → O} {b : ℕ}
    (h : HasStrongCertificateBound f b) (n : ℕ) :
    (qQuery (fun x : Fin n → Option U => f (recordSet x)) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * b)) := by
  refine (strongCertificate_qQuery_le_min_sqrt f n).trans (min_le_min_left _ ?_)
  gcongr
  exact_mod_cast strongCertificateSize_le h

end Records

/-! ## Position-dependent encodings -/

section Encoded

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

/-- The set of records encoded by `y : ι → A` under a public position-wise encoding
`enc : ι → A → Option U`: position `i` holding `a` contributes the record `enc i a`, if any. -/
def encodedSet (enc : ι → A → Option U) (y : ι → A) : Finset U :=
  recordSet fun i => enc i (y i)

/-- The class of the encoded records as an incremental summary over the alphabet `A`: the
state of revealed positions `T` is the class of their encoded records. -/
noncomputable def encodedSummary (f : Finset U → O) (enc : ι → A → Option U) :
    IncrementalSummary ι A (ExtensionMonoid f) (ExtensionMonoid f) where
  state y T := mk f (T.biUnion fun i => (enc i (y i)).toFinset)
  out y := mk f (encodedSet enc y)
  state_empty y z := by simp only [Finset.biUnion_empty]
  state_insert y z T i _ hT hyz := by
    rw [Finset.biUnion_insert, Finset.biUnion_insert, ← mk_mul_mk, ← mk_mul_mk, hT, hyz]
  out_congr _ _ h := h

omit [DecidableEq O] [Fintype A] [DecidableEq A] in
/-- **At most `b` essential positions**: if `b` is a certificate bound, every revealed set of
positions has at most `b` essential positions.  Fix a certificate `C` of at most `b` elements
for the records of `T`, and one position of `T` covering each element of `C`; deleting any
other position leaves a set of records between `C` and the whole, of the same class. -/
theorem card_essentialSet_encodedSummary_le {f : Finset U → O} {b : ℕ}
    (h : HasStrongCertificateBound f b) (enc : ι → A → Option U) (y : ι → A) (T : Finset ι) :
    ((encodedSummary f enc).essentialSet y T).card ≤ b := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Finset.eq_empty_of_isEmpty ((encodedSummary f enc).essentialSet y T), Finset.card_empty]
    exact Nat.zero_le b
  set E : ι → Finset U := fun i => (enc i (y i)).toFinset with hE
  obtain ⟨C, hC, hcard⟩ := h (T.biUnion E)
  have hpick : ∀ c ∈ C, ∃ i, i ∈ T ∧ c ∈ E i := fun c hc => by
    obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.mp (hC.1 hc)
    exact ⟨i, hi, hci⟩
  choose! pick hpickT hpickE using hpick
  refine (Finset.card_le_card (t := C.image pick) fun j hj => ?_).trans
    (Finset.card_image_le.trans hcard)
  simp only [IncrementalSummary.essentialSet, Finset.mem_filter] at hj
  obtain ⟨hjT, hne⟩ := hj
  by_contra hjC
  apply hne
  change mk f (T.biUnion E) = mk f ((T.erase j).biUnion E)
  refine mk_eq_mk.mpr (hC.of_subset (fun c hc => ?_) ?_).2.symm
  · refine Finset.mem_biUnion.mpr ⟨pick c, Finset.mem_erase.mpr ⟨?_, hpickT c hc⟩, hpickE c hc⟩
    rintro rfl
    exact hjC (Finset.mem_image_of_mem pick hc)
  · exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset j T)

/-- **Strong certificates for position-dependent encodings**: if position `i` of
`y : ι → A` encodes the record `enc i (y i)` through a public map, computing `f` of the encoded
records costs `Q_{1/3} ≤ min{|ι|, 2^18·√(|ι|·b_f(U))}`. -/
theorem encodedCertificate_qQuery_le_min_sqrt [Finite U] (enc : ι → A → Option U)
    (f : Finset U → O) :
    (qQuery (fun y : ι → A => f (encodedSet enc y)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * strongCertificateSize f)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : qQuery (fun y : ι → A => f (encodedSet enc y)) (1 / 3) = 0 :=
      qQueryOn_const_eq_zero id (c := f ∅) (fun y => by simp [encodedSet, recordSet])
        (by norm_num)
    rw [h0, Fintype.card_eq_zero]
    simp
  · have := Fintype.ofFinite U
    have hne : (QueryCounts (X := ι → A) id (encodedSummary f enc).out (1 / 3)).Nonempty :=
      queryCounts_nonempty (fun x y h => by rw [show x = y from h]) (by norm_num)
    have hpost := qQueryOn_postcomp_le (read := (id : (ι → A) → ι → A))
      (f := (encodedSummary f enc).out) (ε := 1 / 3) (readout f) hne
    have hsum := summary_qQuery_le_min_sqrt (encodedSummary f enc) (B := strongCertificateSize f)
      (card_essentialSet_encodedSummary_le (hasStrongCertificateBound_strongCertificateSize f) enc)
    exact le_trans (by exact_mod_cast hpost) hsum

/-- The encoded bound against any certificate bound `b`. -/
theorem encodedCertificate_qQuery_le_min_sqrt_of_bound [Finite U] (enc : ι → A → Option U)
    {f : Finset U → O} {b : ℕ} (h : HasStrongCertificateBound f b) :
    (qQuery (fun y : ι → A => f (encodedSet enc y)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * b)) := by
  refine (encodedCertificate_qQuery_le_min_sqrt enc f).trans (min_le_min_left _ ?_)
  gcongr
  exact_mod_cast strongCertificateSize_le h

/-- Certificate size zero: an encoded input needs no query either. -/
theorem encodedCertificate_qQuery_eq_zero [Finite U] (enc : ι → A → Option U) {f : Finset U → O}
    (h0 : strongCertificateSize f = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun y : ι → A => f (encodedSet enc y)) ε = 0 :=
  qQueryOn_const_eq_zero id (c := f ∅) (fun _ => strongCertificateSize_eq_zero_iff.mp h0 _ _) hε

end Encoded

end MonoidProduct.Certificates
