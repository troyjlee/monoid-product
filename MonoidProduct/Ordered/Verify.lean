import MonoidProduct.Ordered.Root
import QuantumQueryComplexity.Quantum.PostQuery

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# Certifying every output record

The core algorithms of the ordered-product theorems return a good record with probability at
least `9/10`; on the failure branches their output is arbitrary.  The **verification wrapper**
`QAlg.postQuery` (`QuantumQueryComplexity/Quantum/PostQuery.lean`) fixes this with `b` extra
classical queries: from the raw record `K`

1. keep the original positions of its support (`retained`; padding positions carry the
   identity letter, so dropping them preserves the product);
2. if more than `b` remain, select nothing (the output is the empty record);
3. otherwise select them in order (`selRec`), query each, and write the queried letters
   (`decRec`).

`verified_truthful`, `verified_card_le`, `verified_supp_lt` hold for **every** raw record, so
every output of positive probability is truthful, has at most `b` positions, all original
(`exists_verified_of_core`); `verified_goodRec` sends good records to good records, so the
`9/10` guarantee survives.  The cost is exactly `Q + b`.
-/

namespace MonoidProduct

open Finset QuantumQueryComplexity

section Verify

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) (n : ℕ) {L : ℕ} (b : ℕ)

/-! ## The selection and the verified record -/

/-- The original positions of a raw record. -/
abbrev retained (K : Record (2 ^ L) (Option σ)) : Finset (Fin (2 ^ L)) :=
  K.supp.filter fun i => (i : ℕ) < n

lemma card_retained_le (K : Record (2 ^ L) (Option σ)) : (retained n K).card ≤ K.supp.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- The `m`-th retained position, as an original position; `none` when there are more than
`b` retained positions (or fewer than `m + 1`). -/
noncomputable def selRec (K : Record (2 ^ L) (Option σ)) (m : Fin b) : Option (Fin n) :=
  if h : (m : ℕ) < (retained n K).card ∧ (retained n K).card ≤ b then
    some ⟨(retained n K).orderEmbOfFin rfl ⟨m, h.1⟩,
      (Finset.mem_filter.1 ((retained n K).orderEmbOfFin_mem rfl ⟨m, h.1⟩)).2⟩
  else none

lemma selRec_mem {K : Record (2 ^ L) (Option σ)} {m : Fin b} {j : Fin n}
    (h : selRec n b K m = some j) : ∃ i ∈ retained n K, (i : ℕ) = j := by
  unfold selRec at h
  split_ifs at h with hc
  · refine ⟨(retained n K).orderEmbOfFin rfl ⟨m, hc.1⟩,
      (retained n K).orderEmbOfFin_mem rfl ⟨m, hc.1⟩, ?_⟩
    rw [← Option.some_inj.1 h]

lemma exists_selRec {K : Record (2 ^ L) (Option σ)} (hcard : (retained n K).card ≤ b)
    {i : Fin (2 ^ L)} (hi : i ∈ retained n K) :
    ∃ m : Fin b, selRec n b K m = some ⟨i, (Finset.mem_filter.1 hi).2⟩ := by
  have hr : i ∈ Set.range ((retained n K).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hi
  obtain ⟨m', hm'⟩ := hr
  refine ⟨⟨m', lt_of_lt_of_le m'.isLt hcard⟩, ?_⟩
  unfold selRec
  rw [dif_pos ⟨m'.isLt, hcard⟩]
  congr 1
  apply Fin.ext
  show (((retained n K).orderEmbOfFin rfl ⟨m', m'.isLt⟩ : Fin (2 ^ L)) : ℕ) = i
  rw [← hm']

/-- The verified record: the selected positions, with the queried letters. -/
noncomputable def decRec (K : Record (2 ^ L) (Option σ)) (ans : Fin b → Option σ) :
    Record (2 ^ L) (Option σ) :=
  fun i => if hi : (i : ℕ) < n then
    (if h : ∃ m : Fin b, selRec n b K m = some ⟨i, hi⟩ then (ans h.choose).map some else none)
  else none

variable (x : Fin n → σ) (K : Record (2 ^ L) (Option σ))

/-- The output of the wrapper on input `x` when the raw record is `K`. -/
noncomputable abbrev verified : Record (2 ^ L) (Option σ) :=
  decRec n b K (fun m => Option.map x (selRec n b K m))

/-! ## Every output is certified -/

theorem verified_truthful : (verified n b x K).Truthful (pad (L := L) x) := by
  intro i c hc
  unfold verified decRec at hc
  split_ifs at hc with hi h
  · simp only [h.choose_spec, Option.map_some] at hc
    rw [pad, dif_pos hi]
    exact Option.some_inj.1 hc

theorem verified_supp_lt : ∀ i ∈ (verified n b x K).supp, (i : ℕ) < n := by
  intro i hi
  simp only [Record.supp, mem_optSupp] at hi
  by_contra hlt
  unfold verified decRec at hi
  rw [dif_neg hlt] at hi
  exact absurd hi (by simp)

theorem verified_card_le : (verified n b x K).supp.card ≤ b := by
  have hsub : (verified n b x K).supp.image (fun i : Fin (2 ^ L) => (some (i : ℕ) : Option ℕ))
      ⊆ Finset.univ.image (fun m : Fin b => (selRec n b K m).map (fun j : Fin n => (j : ℕ))) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    simp only [Record.supp, mem_optSupp] at hi
    unfold verified decRec at hi
    split_ifs at hi with hlt h
    · refine Finset.mem_image.2 ⟨h.choose, Finset.mem_univ _, ?_⟩
      rw [h.choose_spec, Option.map_some]
    all_goals exact absurd hi (by simp)
  calc (verified n b x K).supp.card
      = ((verified n b x K).supp.image (fun i : Fin (2 ^ L) => (some (i : ℕ) : Option ℕ))).card :=
        (Finset.card_image_of_injective _ fun i j h =>
          Fin.ext (Option.some_inj.1 h)).symm
    _ ≤ (Finset.univ.image
          (fun m : Fin b => (selRec n b K m).map (fun j : Fin n => (j : ℕ)))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := Finset.card_fin b

/-! ## Good records stay good -/

theorem verified_supp_eq (hK : K.supp.card ≤ b) : (verified n b x K).supp = retained n K := by
  have hcard : (retained n K).card ≤ b := (card_retained_le n K).trans hK
  ext i
  simp only [Record.supp, mem_optSupp]
  constructor
  · intro hi
    unfold verified decRec at hi
    split_ifs at hi with hlt h
    · obtain ⟨i', hi', hval⟩ := selRec_mem n b h.choose_spec
      have : i' = i := Fin.ext hval
      rw [← this]; exact hi'
    all_goals exact absurd hi (by simp)
  · intro hi
    obtain ⟨m, hm⟩ := exists_selRec n b hcard hi
    have hex : ∃ m : Fin b, selRec n b K m = some ⟨i, (Finset.mem_filter.1 hi).2⟩ := ⟨m, hm⟩
    unfold verified decRec
    rw [dif_pos (Finset.mem_filter.1 hi).2, dif_pos hex]
    simp only [hex.choose_spec, Option.map_some, Option.isSome_some]

theorem verified_goodRec (hK : GoodRec letter b x K) : GoodRec letter b x (verified n b x K) := by
  obtain ⟨htr, hcard, hprod⟩ := hK
  refine ⟨verified_truthful n b x K, verified_card_le n b x K, ?_⟩
  rw [← hprod, Record.prod_of_truthful _ htr, Record.prod_of_truthful _ (verified_truthful n b x K),
    verified_supp_eq n b x K hcard, subwordProd_eq_orderedProd_maskWord,
    subwordProd_eq_orderedProd_maskWord]
  congr 1
  funext j
  simp only [maskWord, Finset.mem_filter]
  by_cases hj : j ∈ K.supp
  · by_cases hlt : (j : ℕ) < n
    · rw [if_pos ⟨hj, hlt⟩, if_pos hj]
    · rw [if_neg (fun h => hlt h.2), if_pos hj, pad_of_not_lt x j hlt]
      rfl
  · rw [if_neg (fun h => hj h.1), if_neg hj]

/-! ## The wrapped algorithm -/

open Classical in
/-- **The verification wrapper for core algorithms**: `b` more queries, every output truthful
with at most `b` original positions, and the good-record probability not decreased. -/
theorem exists_verified_of_core {W : Type} [Fintype W] [DecidableEq W]
    (B : QAlg (Fin n) σ (Record (2 ^ L) (Option σ)) W) (Q : ℕ)
    (hgood : ∀ x : Fin n → σ,
      9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (B' : QAlg (Fin n) σ (Record (2 ^ L) (Option σ)) W'),
      (∀ (x : Fin n → σ) (K : Record (2 ^ L) (Option σ)), 0 < B'.prob x (Q + b) K →
        K.Truthful (pad (L := L) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B'.prob x (Q + b) K := by
  refine ⟨_, inferInstance, inferInstance, B.postQuery (selRec n b) Q (decRec n b),
    fun x K hK => ?_, fun x => ?_⟩
  · obtain ⟨K₀, rfl⟩ := postQuery_exists_of_pos B (selRec n b) Q (decRec n b) x K hK
    exact ⟨verified_truthful n b x K₀, verified_card_le n b x K₀, verified_supp_lt n b x K₀⟩
  · exact (hgood x).trans (sum_prob_le_postQuery B (selRec n b) Q (decRec n b) x _ _
      fun K hK => Finset.mem_filter.2
        ⟨Finset.mem_univ _, verified_goodRec letter n b x K (Finset.mem_filter.1 hK).2⟩)

end Verify

end MonoidProduct
