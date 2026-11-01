import MonoidProduct.Certificates.Basic
set_option linter.style.header false

/-!
# Sparse yes-instances

`monoid.tex`, section `sec:graph-certificates`, `prop:sparse-certificates`.  A Boolean property
whose yes-instances are small has small strong certificates.  No closure or monotonicity
assumption is needed.

* `hasStrongCertificateBound_of_sparseYes`: suppose every `S` with `P S = true` has at most `L`
  elements.  Then every set has a strong certificate of at most `L + 1` elements.
  * A set of at most `L` elements certifies itself.
  * A larger set is certified by any `L + 1` of its elements.  Every extension of either set
    then has more than `L` elements, so `P` is `false` on both.
* `sparseYes_strongCertificateSize_le`: `b_P ≤ min(#U, L + 1)`, combining this bound with
  self-certification.  No assumption `L < #U` is needed.  The certificates themselves:
  `hasStrongCertificateBound_min_of_sparseYes`.

The graph form of `prop:sparse-certificates` is `Graph.sparseYes_strongCertificateSize_le`.
-/

namespace MonoidProduct.Certificates

variable {U : Type*} [DecidableEq U] {P : Finset U → Bool} {L : ℕ}

omit [DecidableEq U] in
/-- A set with more than `L` elements fails a property whose yes-instances have at most `L`
elements. -/
theorem eq_false_of_sparseYes (hP : ∀ S, P S = true → S.card ≤ L) {T : Finset U}
    (hT : L < T.card) : P T = false := by
  cases h : P T with
  | false => rfl
  | true => exact absurd (hP T h) (Nat.not_le.mpr hT)

/-- **Sparse yes-instances have small certificates.**  If every yes-instance of `P` has at most
`L` elements, then every set has a strong certificate of at most `L + 1` elements. -/
theorem hasStrongCertificateBound_of_sparseYes (hP : ∀ S, P S = true → S.card ≤ L) :
    HasStrongCertificateBound P (L + 1) := by
  intro S
  by_cases hS : S.card ≤ L
  · exact ⟨S, isStrongCertificate_self P S, Nat.le_succ_of_le hS⟩
  · obtain ⟨C, hCS, hC⟩ := Finset.exists_subset_card_eq (Nat.not_le.mp hS)
    refine ⟨C, ⟨hCS, fun K => ?_⟩, hC.le⟩
    have hCK := Finset.card_le_card (Finset.subset_union_left (s₁ := C) (s₂ := K))
    have hSK := Finset.card_le_card (Finset.subset_union_left (s₁ := S) (s₂ := K))
    rw [eq_false_of_sparseYes hP (T := C ∪ K) (by omega),
      eq_false_of_sparseYes hP (T := S ∪ K) (by omega)]

/-- **`prop:sparse-certificates`, for any finite universe.**  If every yes-instance of `P` has at
most `L` elements, then `b_P ≤ min(#U, L + 1)`.  No closure or monotonicity assumption on `P`
is needed, and no assumption on `L`. -/
theorem sparseYes_strongCertificateSize_le [Fintype U] (hP : ∀ S, P S = true → S.card ≤ L) :
    strongCertificateSize P ≤ min (Fintype.card U) (L + 1) :=
  le_min (strongCertificateSize_le_card P)
    (strongCertificateSize_le (hasStrongCertificateBound_of_sparseYes hP))

/-- **Certificates for `prop:sparse-certificates`, with the finite-universe cap**: every set
has a strong certificate of at most `min(#U, L + 1)` elements. -/
theorem hasStrongCertificateBound_min_of_sparseYes [Fintype U]
    (hP : ∀ S, P S = true → S.card ≤ L) :
    HasStrongCertificateBound P (min (Fintype.card U) (L + 1)) :=
  hasStrongCertificateBound_iff_size_le.mpr (sparseYes_strongCertificateSize_le hP)

end MonoidProduct.Certificates
