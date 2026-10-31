import MonoidProduct.Matroid.Quantum
import MonoidProduct.Matroid.GreedyMonoid
import MonoidProduct.Certificates.Quantum
set_option linter.style.header false

/-!
# Greedy bases as strong certificates

`monoid.tex`, section `sec:matroid-bases`: the greedy-basis map is a concrete instance of the
strong-certificate construction of `sec:strong-certificates`.

Fix a matroid `M` whose ground set is all of a linearly ordered type `E`, and its greedy-basis
map `B = greedy M : Finset E → Finset E`.

* `extensionEquiv_greedy_iff`: `S ∼_B T ↔ B(S) = B(T)`.  Equality of greedy bases persists under
  every extension by the merge law `lem:matroid-greedy-merge`, and the converse is the empty
  extension.
* `greedy_isStrongCertificate`: `B(S)` is a strong certificate for `S` with respect to `B`.
* `greedy_strongCertificateSize_le_rank`, `greedy_strongCertificateSize_eq_rank`: `b_B ≤ r` when
  `M.eRank ≤ r`, with equality when `M.eRank = r` (a basis of `E` is its own only strong
  certificate).
* `extensionMonoidGreedyMulEquiv`: the extension monoid `M_B` is isomorphic to the greedy-basis
  monoid `GreedyBasisMonoid M hM` of `prop:matroid-greedy-monoid`, by `[S] ↦ B(S)`; the letters
  `A_B` go to the alphabet `G` (`extensionMonoidGreedyMulEquiv_extensionLetter`).
* `hasStrongCertificateBound_recordMatroid`, `recordMatroid_strongCertificateSize_le`: the same
  certificate bound for the public matroid on labelled weighted records of
  `thm:matroid-basis-query`, from its rank bound `eRank_recordMatroid_le`;
  `basisRecords_isStrongCertificate`: the canonical basis records certify the input records.

**`thm:matroid-basis-query` through certificates.**  Tagging each input record with its public
position is a position-dependent encoding (`tagEncoding`), whose encoded set is exactly the set of
labelled input records (`encodedSet_tagEncoding`).  The encoded form of `cor:certificate-queries`
(`encodedCertificate_qQuery_le_min_sqrt_of_bound`) then gives the bound
`Q_{1/3} ≤ min{n, 2^18·√(n·r)}` for the canonical basis records and positions, and zero queries at
rank zero: `matroidBasisRecords_qQuery_le_min_sqrt_of_certificates`,
`matroidBasisIndices_qQuery_le_min_sqrt_of_certificates`,
`matroidBasisRecords_qQuery_eq_zero_of_certificates`.  These rederive the operational endpoints
of `Matroid/Quantum.lean`, which are unchanged, with the same constant.
-/

namespace MonoidProduct.Matroid

open Set QuantumQueryComplexity MonoidProduct.Certificates

/-! ## The greedy-basis map -/

section Greedy

variable {E : Type*} [LinearOrder E] {M : _root_.Matroid E}

/-- Greedy bases of unions are determined by the greedy bases of the parts. -/
theorem greedy_union_congr (hM : M.E = univ) {S S' T T' : Finset E}
    (hS : greedy M S = greedy M S') (hT : greedy M T = greedy M T') :
    greedy M (S ∪ T) = greedy M (S' ∪ T') := by
  rw [greedy_union_eq_greedy_union_greedy hM S T, hS, hT,
    ← greedy_union_eq_greedy_union_greedy hM]

/-- **Extension equivalence for the greedy-basis map is equality of greedy bases**
(`sec:matroid-bases`): `S ∼_B T ↔ B(S) = B(T)`. -/
theorem extensionEquiv_greedy_iff (hM : M.E = univ) {S T : Finset E} :
    ExtensionEquiv (greedy M) S T ↔ greedy M S = greedy M T :=
  extensionEquiv_iff_of_merge fun _ _ _ _ hS hT => greedy_union_congr hM hS hT

/-- **The greedy basis is a strong certificate**: `B(S) ⊆ S` and `B(S) ∼_B S`. -/
theorem greedy_isStrongCertificate (hM : M.E = univ) (S : Finset E) :
    IsStrongCertificate (greedy M) (greedy M S) S :=
  ⟨greedy_subset M S, (extensionEquiv_greedy_iff hM).mpr (greedy_greedy hM S)⟩

/-- The greedy bases give the certificate bound `r` when `M.eRank ≤ r`. -/
theorem hasStrongCertificateBound_greedy (hM : M.E = univ) {r : ℕ} (hr : M.eRank ≤ r) :
    HasStrongCertificateBound (greedy M) r :=
  fun S => ⟨greedy M S, greedy_isStrongCertificate hM S,
    card_le_of_indep_of_eRank_le (indep_greedy hM S) hr⟩

/-- `b_B ≤ r` when `M.eRank ≤ r`. -/
theorem greedy_strongCertificateSize_le_rank (hM : M.E = univ) {r : ℕ} (hr : M.eRank ≤ r) :
    strongCertificateSize (greedy M) ≤ r :=
  strongCertificateSize_le (hasStrongCertificateBound_greedy hM hr)

/-- **`b_B = r` for a matroid of rank `r`** on a finite linearly ordered type: a basis of `E`
is independent, so its only strong certificate is itself. -/
theorem greedy_strongCertificateSize_eq_rank [Finite E] (hM : M.E = univ) {r : ℕ}
    (hr : M.eRank = r) : strongCertificateSize (greedy M) = r := by
  refine (greedy_strongCertificateSize_le_rank hM hr.le).antisymm ?_
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hBfin : B.Finite := Set.toFinite B
  set F : Finset E := hBfin.toFinset with hF
  have hFB : (↑F : Set E) = B := hBfin.coe_toFinset
  have hFcard : F.card = r := by
    have h := hB.encard_eq_eRank.trans hr
    rw [← hFB, Set.encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  have hFind : M.Indep ↑F := by
    rw [hFB]
    exact hB.indep
  refine le_strongCertificateSize F fun C hC => ?_
  have hCind : M.Indep ↑C := hFind.subset (Finset.coe_subset.mpr hC.1)
  have hCF := (extensionEquiv_greedy_iff hM).mp hC.2
  rw [greedy_eq_self_of_indep hCind, greedy_eq_self_of_indep hFind] at hCF
  rw [hCF, hFcard]

/-! ## The extension monoid of the greedy-basis map -/

open GreedyBasisMonoid in
/-- **The extension monoid of the greedy-basis map is the greedy-basis monoid**
(`prop:matroid-greedy-monoid`): `[S] ↦ B(S)` is a monoid isomorphism `M_B ≃* H`. -/
noncomputable def extensionMonoidGreedyMulEquiv (hM : M.E = univ) :
    ExtensionMonoid (greedy M) ≃* GreedyBasisMonoid M hM where
  toFun := Quotient.lift (ofGreedy hM) fun _ _ h =>
    GreedyBasisMonoid.ext ((extensionEquiv_greedy_iff hM).mp h)
  invFun A := ExtensionMonoid.mk (greedy M) A.val
  left_inv a := by
    induction a using ExtensionMonoid.ind with | _ S =>
    exact ExtensionMonoid.mk_eq_mk.mpr ((extensionEquiv_greedy_iff hM).mpr (greedy_greedy hM S))
  right_inv A := ofGreedy_val A
  map_mul' a b := by
    induction a using ExtensionMonoid.ind with | _ S =>
    induction b using ExtensionMonoid.ind with | _ T =>
    exact (ofGreedy_mul_ofGreedy S T).symm

@[simp] theorem extensionMonoidGreedyMulEquiv_mk (hM : M.E = univ) (S : Finset E) :
    extensionMonoidGreedyMulEquiv hM (ExtensionMonoid.mk (greedy M) S) =
      GreedyBasisMonoid.ofGreedy hM S :=
  rfl

/-- The independent set attached to a class is its readout. -/
@[simp] theorem val_extensionMonoidGreedyMulEquiv (hM : M.E = univ)
    (a : ExtensionMonoid (greedy M)) :
    (extensionMonoidGreedyMulEquiv hM a).val = ExtensionMonoid.readout (greedy M) a := by
  induction a using ExtensionMonoid.ind with | _ S =>
  rfl

/-- The alphabet `A_B` of `thm:certificate-breadth` goes to the alphabet
`G = {∅} ∪ {B({e}) : e ∈ E}` of `prop:matroid-greedy-monoid`. -/
theorem extensionMonoidGreedyMulEquiv_extensionLetter (hM : M.E = univ) (o : Option E) :
    extensionMonoidGreedyMulEquiv hM (extensionLetter (greedy M) o) = greedyBasisLetter M hM o :=
  rfl

end Greedy

/-! ## Labelled records -/

section Records

variable {ι E W : Type*} [LinearOrder ι] [LinearOrder E] [LinearOrder W] {M : _root_.Matroid E}

/-- The canonical basis records are a strong certificate for the labelled input records, with
respect to the greedy-basis map of the record matroid. -/
theorem basisRecords_isStrongCertificate (hM : M.E = univ) (x : ι → Option (E × W))
    (T : Finset ι) :
    IsStrongCertificate (greedy (recordMatroid M)) (basisRecords M x T) (records x T) :=
  greedy_isStrongCertificate (recordMatroid_ground hM) _

/-- **The certificate bound for the record matroid** (`thm:matroid-basis-query`): its greedy
bases have at most `r` elements when `M.eRank ≤ r`. -/
theorem hasStrongCertificateBound_recordMatroid (hM : M.E = univ) {r : ℕ} (hr : M.eRank ≤ r) :
    HasStrongCertificateBound (greedy (recordMatroid (ι := ι) (W := W) M)) r :=
  hasStrongCertificateBound_greedy (recordMatroid_ground hM) (eRank_recordMatroid_le.trans hr)

/-- `b_B ≤ r` for the greedy-basis map of the record matroid. -/
theorem recordMatroid_strongCertificateSize_le (hM : M.E = univ) {r : ℕ} (hr : M.eRank ≤ r) :
    strongCertificateSize (greedy (recordMatroid (ι := ι) (W := W) M)) ≤ r :=
  strongCertificateSize_le (hasStrongCertificateBound_recordMatroid hM hr)

end Records

/-! ## `thm:matroid-basis-query` through the certificate theorem -/

section Query

variable {E W : Type} [Fintype E] [LinearOrder E] [Fintype W] [LinearOrder W]
  {M : _root_.Matroid E}

/-- **Position tagging**, a public position-dependent encoding: the record `(e, w)` at position
`i` is encoded as the labelled record `(e, w, i)`, and a null record as nothing. -/
def tagEncoding (n : ℕ) (i : Fin n) (o : Option (E × W)) : Option (WeightedRecord (Fin n) E W) :=
  o.map (tagRecord i)

omit [Fintype E] [Fintype W] in
/-- The encoded set of the position tagging is the set of labelled input records. -/
theorem encodedSet_tagEncoding {n : ℕ} (x : Fin n → Option (E × W)) :
    encodedSet (tagEncoding n) x = records x Finset.univ :=
  rfl

/-- **`thm:matroid-basis-query` from `cor:certificate-queries`**: for `M.eRank ≤ r`, computing
the canonical basis records of `x : Fin n → Option (E × W)` costs
`Q_{1/3} ≤ min{n, 2^18·√(n·r)}`, via the strong-certificate bound `r` of the record matroid. -/
theorem matroidBasisRecords_qQuery_le_min_sqrt_of_certificates (hM : M.E = univ) {r : ℕ}
    (hr : M.eRank ≤ r) (n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) => basisRecords M x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * r)) := by
  have h := encodedCertificate_qQuery_le_min_sqrt_of_bound (tagEncoding n)
    (hasStrongCertificateBound_recordMatroid (ι := Fin n) (W := W) hM hr)
  rw [Fintype.card_fin] at h
  exact h

/-- The same bound for the canonical basis positions, by postprocessing the certificates. -/
theorem matroidBasisIndices_qQuery_le_min_sqrt_of_certificates (hM : M.E = univ) {r : ℕ}
    (hr : M.eRank ≤ r) (n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) => basisIndices M x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * r)) := by
  have h := encodedCertificate_qQuery_le_min_sqrt_of_bound (tagEncoding n)
    ((hasStrongCertificateBound_recordMatroid (ι := Fin n) (W := W) hM hr).postcomp
      (Finset.image WeightedRecord.index))
  rw [Fintype.card_fin] at h
  exact h

/-- Rank zero, through certificates: the certificate size is zero, so the canonical basis
records need no query. -/
theorem matroidBasisRecords_qQuery_eq_zero_of_certificates (hM : M.E = univ) (hr : M.eRank = 0)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → Option (E × W) => basisRecords M x Finset.univ) ε = 0 :=
  encodedCertificate_qQuery_eq_zero (tagEncoding n)
    (Nat.le_zero.mp (recordMatroid_strongCertificateSize_le (ι := Fin n) (W := W) hM (r := 0)
      (by rw [hr]; rfl))) hε

end Query

end MonoidProduct.Matroid
