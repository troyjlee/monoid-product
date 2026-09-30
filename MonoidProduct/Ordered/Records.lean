import MonoidProduct.Width.StableOrder

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Algebra of masked subword products, and records

Everything here is about `subwordProd letter x U`, the product of the scattered
subword of `x` on the mask `U` (letters off `U` replaced by `1`):

* `orderedProd_comp_orderEmb` — a word that is `1` off the range of an order
  embedding has the product of its pull-back; hence a mask can be **enumerated
  in reading order** (`subwordProd_map_maskEmb`, `wordProd_comp_maskEmb`);
* `isBreadthBound_letterOpt` — **identity padding**: the breadth bound survives
  extending the alphabet by a letter `none ↦ 1`;
* `exists_compress` — **compression inside a mask**: `∃ D ⊆ U, |D| ≤ b, p(D) = p(U)`;
* `subwordProd_eq_of_sandwich` — **sandwich**: `D ⊆ U ⊆ V, p(D) = p(V) ⇒ p(U) = p(V)`
  (stable order);
* `card_essential_le` — **at most `b` members of any list are essential**
  (`lem:beta-essential-subword-list`);
* `subwordProd_union_of_sep` — **separated concatenation**: `p(U ∪ V) = p(U)·p(V)`
  when every position of `U` precedes every position of `V`;
* records `Fin n → Option σ`: support, truthfulness on `x`, product, first-wins
  union, restriction, and a deterministic `compress` with `compress_spec`.
-/

namespace MonoidProduct

open Finset

/-! ## Restriction along an order embedding -/

section OrderEmb

variable {M : Type} [Monoid M]

lemma rangeProd_eq_one_of_padAt {n : ℕ} {y : Fin n → M} {lo hi : ℕ}
    (h : ∀ i, lo ≤ i → i < hi → padAt y i = 1) : rangeProd y lo hi = 1 := by
  rw [rangeProd]
  refine List.prod_eq_one fun a ha => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
  rw [List.mem_range] at hk
  exact h _ (by omega) (by omega)

/-- **A word vanishing off an order embedding has the product of its pull-back.** -/
theorem orderedProd_comp_orderEmb :
    ∀ {m n : ℕ} (e : Fin m ↪o Fin n) (y : Fin n → M),
      (∀ i, i ∉ Set.range e → y i = 1) → orderedProd (y ∘ e) = orderedProd y
  | 0, n, e, y, h => by
    rw [orderedProd_eq_one_of_forall (x := y ∘ e) (fun i => i.elim0)]
    exact (orderedProd_eq_one_of_forall fun i => h i (by rintro ⟨j, _⟩; exact j.elim0)).symm
  | m + 1, n, e, y, h => by
    have hlt : ∀ i : Fin m, (e (Fin.castSucc i) : ℕ) < e (Fin.last m) :=
      fun i => e.strictMono (Fin.castSucc_lt_last i)
    have hjn : ((e (Fin.last m) : Fin n) : ℕ) ≤ n := (e (Fin.last m)).isLt.le
    let e' : Fin m ↪o Fin (e (Fin.last m)) :=
      OrderEmbedding.ofStrictMono (fun i => ⟨e (Fin.castSucc i), hlt i⟩)
        (fun a b hab => by
          show ((e (Fin.castSucc a) : Fin n) : ℕ) < e (Fin.castSucc b)
          exact e.strictMono (Fin.castSucc_lt_castSucc_iff.2 hab))
    let y' : Fin (e (Fin.last m)) → M := fun i => y (Fin.castLE hjn i)
    have hy' : ∀ i, i ∉ Set.range e' → y' i = 1 := by
      intro i hi
      apply h
      rintro ⟨k, hk⟩
      apply hi
      by_cases hkm : (k : ℕ) < m
      · refine ⟨⟨k, hkm⟩, ?_⟩
        apply Fin.ext
        show ((e (Fin.castSucc ⟨k, hkm⟩) : Fin n) : ℕ) = i
        rw [show Fin.castSucc ⟨k, hkm⟩ = k from Fin.ext rfl, hk]
        rfl
      · exfalso
        have hk' : k = Fin.last m := Fin.ext (by have := k.isLt; simp; omega)
        rw [hk'] at hk
        have := congrArg Fin.val hk
        simp only [Fin.coe_castLE] at this
        have := i.isLt
        omega
    have ih := orderedProd_comp_orderEmb e' y' hy'
    -- the pull-back splits off its last letter
    have h1 : orderedProd (y ∘ e) = orderedProd (y' ∘ e') * y (e (Fin.last m)) := by
      rw [orderedProd_eq_rangeProd, orderedProd_eq_rangeProd,
        rangeProd_succ_right _ (Nat.zero_le m), padAt_of_lt _ (Nat.lt_succ_self m)]
      congr 1
      refine rangeProd_congr fun i _ hi => ?_
      rw [padAt_of_lt (y ∘ e) (by omega), padAt_of_lt (y' ∘ e') hi]
      rfl
    -- the word splits at the last image
    have h2 : orderedProd y = orderedProd y' * y (e (Fin.last m)) := by
      rw [orderedProd_eq_rangeProd, orderedProd_eq_rangeProd,
        ← rangeProd_split y (Nat.zero_le _) hjn,
        ← rangeProd_split y (Nat.le_succ ((e (Fin.last m) : Fin n) : ℕ))
          (Nat.succ_le_of_lt (e (Fin.last m)).isLt),
        rangeProd_singleton y (e (Fin.last m)).isLt]
      have h3 : rangeProd y ((e (Fin.last m) : Fin n) + 1) n = 1 := by
        refine rangeProd_eq_one_of_padAt fun i hi1 hi2 => ?_
        rw [padAt_of_lt _ hi2]
        apply h
        rintro ⟨k, hk⟩
        have hle : e k ≤ e (Fin.last m) := e.monotone (Fin.le_last k)
        rw [hk] at hle
        have := Fin.le_def.1 hle
        simp at this
        omega
      rw [h3, mul_one]
      congr 1
      refine rangeProd_congr fun i _ hi => ?_
      rw [padAt_of_lt _ hi, padAt_of_lt _ (hi.trans_le hjn)]
      rfl
    rw [h1, h2, ih]

end OrderEmb

/-! ## Masks enumerated in reading order -/

section Mask

variable {σ M : Type} [Monoid M] (letter : σ → M) {n : ℕ}

/-- The masked word: letters off `u` replaced by `1`. -/
def maskWord (x : Fin n → σ) (u : Finset (Fin n)) : Fin n → M :=
  fun i => if i ∈ u then letter (x i) else 1

lemma subwordProd_eq_orderedProd_maskWord (x : Fin n → σ) (u : Finset (Fin n)) :
    subwordProd letter x u = orderedProd (maskWord letter x u) := by
  rw [subwordProd, orderedProd_eq_prod_ofFn]; rfl

/-- The union of a family without its `j`-th member. -/
def unionExcept {J : Type} [Fintype J] [DecidableEq J] (U : J → Finset (Fin n)) (j : J) :
    Finset (Fin n) :=
  (Finset.univ.erase j).biUnion U

/-- The order-preserving enumeration of a mask. -/
noncomputable def maskEmb (U : Finset (Fin n)) : Fin U.card ↪o Fin n := U.orderEmbOfFin rfl

lemma maskEmb_mem (U : Finset (Fin n)) (j : Fin U.card) : maskEmb U j ∈ U :=
  U.orderEmbOfFin_mem rfl j

lemma mem_range_maskEmb {U : Finset (Fin n)} {i : Fin n} :
    i ∈ Set.range (maskEmb U) ↔ i ∈ U := by
  rw [maskEmb, U.range_orderEmbOfFin rfl, Finset.mem_coe]

lemma map_univ_maskEmb (U : Finset (Fin n)) :
    Finset.univ.map (maskEmb U).toEmbedding = U := by
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  rw [← mem_range_maskEmb]
  rfl

/-- **A subword of the enumerated mask is the subword of the transported mask.** -/
theorem subwordProd_map_maskEmb (x : Fin n → σ) (U : Finset (Fin n)) (u : Finset (Fin U.card)) :
    subwordProd letter (x ∘ maskEmb U) u
      = subwordProd letter x (u.map (maskEmb U).toEmbedding) := by
  rw [subwordProd_eq_orderedProd_maskWord, subwordProd_eq_orderedProd_maskWord]
  have hcomp : maskWord letter (x ∘ maskEmb U) u
      = maskWord letter x (u.map (maskEmb U).toEmbedding) ∘ maskEmb U := by
    funext j
    simp only [maskWord, Function.comp_apply]
    have hm : (maskEmb U) j ∈ u.map (maskEmb U).toEmbedding ↔ j ∈ u :=
      Finset.mem_map' (maskEmb U).toEmbedding
    by_cases hj : j ∈ u
    · rw [if_pos hj, if_pos (hm.2 hj)]
    · rw [if_neg hj, if_neg (fun h => hj (hm.1 h))]
  rw [hcomp]
  refine orderedProd_comp_orderEmb _ _ fun i hi => ?_
  simp only [maskWord]
  rw [if_neg]
  intro hmem
  obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hmem
  exact hi ⟨j, rfl⟩

theorem wordProd_comp_maskEmb (x : Fin n → σ) (U : Finset (Fin n)) :
    wordProd letter (x ∘ maskEmb U) = subwordProd letter x U := by
  rw [← subwordProd_univ, subwordProd_map_maskEmb, map_univ_maskEmb]

end Mask

/-! ## Identity padding and compression -/

section Compress

variable {σ M : Type} [Monoid M] (letter : σ → M) {n : ℕ}

/-- The alphabet extended by an identity letter. -/
def letterOpt : Option σ → M := fun o => o.elim 1 letter

@[simp] lemma letterOpt_none : letterOpt letter none = 1 := rfl
@[simp] lemma letterOpt_some (s : σ) : letterOpt letter (some s) = letter s := rfl

/-- The support of an `Option`-word. -/
def optSupp (y : Fin n → Option σ) : Finset (Fin n) := Finset.univ.filter fun i => (y i).isSome

lemma mem_optSupp {y : Fin n → Option σ} {i : Fin n} : i ∈ optSupp y ↔ (y i).isSome := by
  simp [optSupp]

lemma wordProd_letterOpt_eq_subwordProd (y : Fin n → Option σ) :
    wordProd (letterOpt letter) y = subwordProd (letterOpt letter) y (optSupp y) := by
  rw [← subwordProd_univ, subwordProd_eq_orderedProd_maskWord,
    subwordProd_eq_orderedProd_maskWord]
  congr 1
  funext i
  simp only [maskWord, Finset.mem_univ, if_true]
  by_cases h : i ∈ optSupp y
  · rw [if_pos h]
  · rw [if_neg h]
    rw [mem_optSupp, Option.isSome_iff_exists] at h
    push Not at h
    cases hy : y i with
    | none => rfl
    | some s => exact absurd hy (h s)

/-- **Identity padding**: the breadth bound survives the letter `none ↦ 1`. -/
theorem isBreadthBound_letterOpt {b : ℕ} (hb : IsBreadthBound letter b) :
    IsBreadthBound (letterOpt letter) b := by
  intro n y
  classical
  set U := optSupp y with hUdef
  have hU : ∀ j : Fin U.card, (y (maskEmb U j)).isSome := fun j =>
    mem_optSupp.1 (maskEmb_mem U j)
  let x' : Fin U.card → σ := fun j => (y (maskEmb U j)).get (hU j)
  obtain ⟨u, hu, hcore⟩ := hb U.card x'
  refine ⟨u.map (maskEmb U).toEmbedding, by rw [Finset.card_map]; exact hu, ?_⟩
  rw [IsCore, ← subwordProd_map_maskEmb, wordProd_letterOpt_eq_subwordProd, ← hUdef,
    ← wordProd_comp_maskEmb (letterOpt letter) y U]
  have hx' : ∀ j, letterOpt letter (y (maskEmb U j)) = letter (x' j) := fun j => by
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (hU j)
    simp only [x']
    rw [Option.get_of_mem (hU j) hs, hs]
    rfl
  have e1 : subwordProd (letterOpt letter) (y ∘ maskEmb U) u = subwordProd letter x' u := by
    rw [subwordProd_eq_orderedProd_maskWord, subwordProd_eq_orderedProd_maskWord]
    congr 1
    funext j
    simp only [maskWord, Function.comp_apply, hx']
  have e2 : wordProd (letterOpt letter) (y ∘ maskEmb U) = wordProd letter x' := by
    rw [← subwordProd_univ, ← subwordProd_univ, subwordProd_eq_orderedProd_maskWord,
      subwordProd_eq_orderedProd_maskWord]
    congr 1
    funext j
    simp only [maskWord, Function.comp_apply, hx']
  rw [e1, e2]
  exact hcore

/-- A mask beyond the support of an `Option`-word can be trimmed. -/
lemma subwordProd_letterOpt_inter (y : Fin n → Option σ) (D : Finset (Fin n)) :
    subwordProd (letterOpt letter) y D = subwordProd (letterOpt letter) y (D ∩ optSupp y) := by
  rw [subwordProd_eq_orderedProd_maskWord, subwordProd_eq_orderedProd_maskWord]
  congr 1
  funext i
  simp only [maskWord, Finset.mem_inter]
  by_cases hD : i ∈ D
  · by_cases hS : i ∈ optSupp y
    · rw [if_pos hD, if_pos ⟨hD, hS⟩]
    · rw [if_pos hD, if_neg (fun h => hS h.2)]
      rw [mem_optSupp, Option.isSome_iff_exists] at hS
      push Not at hS
      cases hy : y i with
      | none => rfl
      | some s => exact absurd hy (hS s)
  · rw [if_neg hD, if_neg (fun h => hD h.1)]

/-- The `Option`-word of `x` on the mask `U`. -/
def maskOpt (x : Fin n → σ) (U : Finset (Fin n)) : Fin n → Option σ :=
  fun i => if i ∈ U then some (x i) else none

lemma optSupp_maskOpt (x : Fin n → σ) (U : Finset (Fin n)) : optSupp (maskOpt x U) = U := by
  ext i
  simp only [mem_optSupp, maskOpt]
  split_ifs with h <;> simp [h]

lemma subwordProd_maskOpt (x : Fin n → σ) {U V : Finset (Fin n)} (hVU : V ⊆ U) :
    subwordProd (letterOpt letter) (maskOpt x U) V = subwordProd letter x V := by
  rw [subwordProd_eq_orderedProd_maskWord, subwordProd_eq_orderedProd_maskWord]
  congr 1
  funext i
  simp only [maskWord, maskOpt]
  by_cases hV : i ∈ V
  · rw [if_pos hV, if_pos hV, if_pos (hVU hV)]; rfl
  · rw [if_neg hV, if_neg hV]

/-- **Compression inside a mask**: `∃ D ⊆ U, |D| ≤ b, p(D) = p(U)`. -/
theorem exists_compress {b : ℕ} (hb : IsBreadthBound letter b) (x : Fin n → σ)
    (U : Finset (Fin n)) :
    ∃ D ⊆ U, D.card ≤ b ∧ subwordProd letter x D = subwordProd letter x U := by
  classical
  obtain ⟨D', hD', hcore⟩ := isBreadthBound_letterOpt letter hb n (maskOpt x U)
  refine ⟨D' ∩ U, Finset.inter_subset_right, (Finset.card_le_card Finset.inter_subset_left).trans hD',
    ?_⟩
  rw [IsCore, wordProd_letterOpt_eq_subwordProd, subwordProd_letterOpt_inter, optSupp_maskOpt,
    subwordProd_maskOpt letter x Finset.inter_subset_right,
    subwordProd_maskOpt letter x (Finset.Subset.refl U)] at hcore
  exact hcore

end Compress

/-! ## Sandwich and essential members -/

section Stable

variable {σ M : Type} [Monoid M] [PartialOrder M] [DecidableEq M] (hst : IsStableOrder M)
  (letter : σ → M) {n : ℕ} (x : Fin n → σ)
include hst

/-- **Sandwich**: `D ⊆ U ⊆ V` and `p(D) = p(V)` force `p(U) = p(V)`. -/
theorem subwordProd_eq_of_sandwich {D U V : Finset (Fin n)} (hDU : D ⊆ U) (hUV : U ⊆ V)
    (h : subwordProd letter x D = subwordProd letter x V) :
    subwordProd letter x U = subwordProd letter x V :=
  le_antisymm (hst.subwordProd_mono letter x hUV) (h ▸ hst.subwordProd_mono letter x hDU)

/-- **At most `b` members of any list are essential** (`lem:beta-essential-subword-list`). -/
theorem card_essential_le {b : ℕ} (hb : IsBreadthBound letter b) {J : Type} [Fintype J]
    [DecidableEq J] (U : J → Finset (Fin n)) :
    (Finset.univ.filter fun j =>
        subwordProd letter x (unionExcept U j) ≠ subwordProd letter x (Finset.univ.biUnion U)).card
      ≤ b := by
  classical
  obtain ⟨D, hDW, hDb, hD⟩ := exists_compress letter hb x (Finset.univ.biUnion U)
  have hmem : ∀ d ∈ D, ∃ j, d ∈ U j := fun d hd => by
    have := hDW hd
    rw [Finset.mem_biUnion] at this
    obtain ⟨j, -, hj⟩ := this
    exact ⟨j, hj⟩
  choose c hc using hmem
  set I : Finset J := D.attach.image (fun d => c d.1 d.2) with hI
  have hIb : I.card ≤ b := by
    rw [hI]
    exact Finset.card_image_le.trans (by rw [Finset.card_attach]; exact hDb)
  refine le_trans (Finset.card_le_card ?_) hIb
  intro j hj
  rw [Finset.mem_filter] at hj
  by_contra hjim
  apply hj.2
  refine subwordProd_eq_of_sandwich hst letter x (D := D) ?_ ?_ hD
  · intro d hd
    rw [unionExcept, Finset.mem_biUnion]
    refine ⟨c d hd, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩, hc d hd⟩
    intro hcj
    apply hjim
    rw [hI, Finset.mem_image]
    exact ⟨⟨d, hd⟩, Finset.mem_attach _ _, hcj⟩
  · intro i hi
    rw [unionExcept, Finset.mem_biUnion] at hi
    obtain ⟨k, -, hk⟩ := hi
    exact Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hk⟩

end Stable

/-! ## Separated concatenation -/

section Sep

variable {σ M : Type} [Monoid M] (letter : σ → M) {n : ℕ} (x : Fin n → σ)

lemma padAt_maskWord (u : Finset (Fin n)) (i : ℕ) :
    padAt (maskWord letter x u) i
      = if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ u then letter (x ⟨i, h⟩) else 1) else 1 := by
  simp only [padAt, maskWord]

/-- **Separated concatenation**: `p(U ∪ V) = p(U)·p(V)` when `U` precedes `V`. -/
theorem subwordProd_union_of_sep {U V : Finset (Fin n)} (h : ∀ i ∈ U, ∀ j ∈ V, i < j) :
    subwordProd letter x (U ∪ V) = subwordProd letter x U * subwordProd letter x V := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hU
  · rw [Finset.empty_union, subwordProd_empty, one_mul]
  set c : ℕ := (U.max' hU : Fin n) + 1 with hc
  have hcn : c ≤ n := (U.max' hU).isLt
  have hUc : ∀ i ∈ U, (i : ℕ) < c := fun i hi => by
    have := U.le_max' i hi; rw [hc]; omega
  have hVc : ∀ j ∈ V, c ≤ (j : ℕ) := fun j hj => by
    have := h _ (U.max'_mem hU) j hj; rw [hc]; omega
  simp only [subwordProd_eq_orderedProd_maskWord, orderedProd_eq_rangeProd]
  rw [← rangeProd_split (maskWord letter x (U ∪ V)) (Nat.zero_le c) hcn,
    ← rangeProd_split (maskWord letter x U) (Nat.zero_le c) hcn,
    ← rangeProd_split (maskWord letter x V) (Nat.zero_le c) hcn]
  have e1 : rangeProd (maskWord letter x (U ∪ V)) 0 c = rangeProd (maskWord letter x U) 0 c := by
    refine rangeProd_congr fun i _ hi => ?_
    rw [padAt_maskWord, padAt_maskWord]
    split_ifs with h1 h2 h3 h3
    · rfl
    · exact absurd ((Finset.mem_union.1 h2).resolve_left h3) (fun hV => by
        have := hVc _ hV; simp at this; omega)
    · exact absurd (Finset.mem_union_left V h3) h2
    · rfl
    · rfl
  have e2 : rangeProd (maskWord letter x U) c n = 1 := by
    refine rangeProd_eq_one_of_padAt fun i hi1 hi2 => ?_
    rw [padAt_maskWord, dif_pos hi2, if_neg]
    intro hU'
    have := hUc _ hU'
    simp at this; omega
  have e3 : rangeProd (maskWord letter x (U ∪ V)) c n = rangeProd (maskWord letter x V) c n := by
    refine rangeProd_congr fun i hi1 hi2 => ?_
    rw [padAt_maskWord, padAt_maskWord, dif_pos hi2, dif_pos hi2]
    by_cases h2 : (⟨i, hi2⟩ : Fin n) ∈ V
    · rw [if_pos (Finset.mem_union_right U h2), if_pos h2]
    · rw [if_neg h2, if_neg]
      intro hUV
      have hU' := (Finset.mem_union.1 hUV).resolve_right h2
      have := hUc _ hU'
      simp at this; omega
  have e4 : rangeProd (maskWord letter x V) 0 c = 1 := by
    refine rangeProd_eq_one_of_padAt fun i _ hi2 => ?_
    rw [padAt_maskWord, dif_pos (hi2.trans_le hcn), if_neg]
    intro hV'
    have := hVc _ hV'
    simp at this; omega
  rw [e1, e2, e3, e4, mul_one, one_mul]

end Sep

/-! ## Records -/

section Records

variable {σ : Type} {n : ℕ}

/-- A record: a partial assignment of letters to positions. -/
abbrev Record (n : ℕ) (σ : Type) := Fin n → Option σ

namespace Record

/-- The support. -/
def supp (r : Record n σ) : Finset (Fin n) := optSupp r

/-- `r` is truthful on `x`: every stored letter is the letter of `x` there. -/
def Truthful (x : Fin n → σ) (r : Record n σ) : Prop := ∀ i s, r i = some s → x i = s

/-- First-wins union. -/
def union (r r' : Record n σ) : Record n σ := fun i => (r i).orElse (fun _ => r' i)

/-- Restriction to a mask. -/
def restrict (r : Record n σ) (D : Finset (Fin n)) : Record n σ :=
  fun i => if i ∈ D then r i else none

/-- The record of `x` on a mask. -/
def ofMask (x : Fin n → σ) (U : Finset (Fin n)) : Record n σ := maskOpt x U

variable {M : Type} [Monoid M] (letter : σ → M)

/-- The product of a record. -/
def prod (r : Record n σ) : M := wordProd (letterOpt letter) r

lemma prod_eq_subwordProd (r : Record n σ) :
    r.prod letter = subwordProd (letterOpt letter) r r.supp :=
  wordProd_letterOpt_eq_subwordProd letter r

lemma supp_union (r r' : Record n σ) : (r.union r').supp = r.supp ∪ r'.supp := by
  ext i
  simp only [supp, mem_optSupp, union, Finset.mem_union]
  cases r i <;> simp

lemma supp_restrict (r : Record n σ) (D : Finset (Fin n)) : (r.restrict D).supp = r.supp ∩ D := by
  ext i
  simp only [supp, mem_optSupp, restrict, Finset.mem_inter]
  split_ifs with h <;> simp [h]

lemma supp_ofMask (x : Fin n → σ) (U : Finset (Fin n)) : (ofMask x U).supp = U :=
  optSupp_maskOpt x U

lemma truthful_union {x : Fin n → σ} {r r' : Record n σ} (h : Truthful x r) (h' : Truthful x r') :
    Truthful x (r.union r') := by
  intro i s hs
  simp only [union] at hs
  cases hr : r i with
  | none => rw [hr] at hs; exact h' i s hs
  | some t => rw [hr] at hs; exact h i s (hr.trans hs)

lemma truthful_restrict {x : Fin n → σ} {r : Record n σ} (h : Truthful x r) (D : Finset (Fin n)) :
    Truthful x (r.restrict D) := by
  intro i s hs
  simp only [restrict] at hs
  split_ifs at hs with hD
  exact h i s hs

lemma truthful_ofMask (x : Fin n → σ) (U : Finset (Fin n)) : Truthful x (ofMask x U) := by
  intro i s hs
  simp only [ofMask, maskOpt] at hs
  split_ifs at hs with hU
  exact Option.some.inj hs

/-- **A truthful record is the record of `x` on its support**, so its product is the
masked subword product of `x`. -/
lemma eq_ofMask_of_truthful {x : Fin n → σ} {r : Record n σ} (h : Truthful x r) :
    r = ofMask x r.supp := by
  funext i
  simp only [ofMask, maskOpt, supp, mem_optSupp]
  cases hr : r i with
  | none => simp
  | some s => rw [h i s hr]; simp

lemma prod_of_truthful {x : Fin n → σ} {r : Record n σ} (h : Truthful x r) :
    r.prod letter = subwordProd letter x r.supp := by
  rw [prod_eq_subwordProd, eq_ofMask_of_truthful h, supp_ofMask]
  rw [ofMask]
  exact subwordProd_maskOpt letter x (Finset.Subset.refl _)

lemma prod_restrict (r : Record n σ) (D : Finset (Fin n)) :
    (r.restrict D).prod letter = subwordProd (letterOpt letter) r (r.supp ∩ D) := by
  rw [prod_eq_subwordProd, supp_restrict, subwordProd_eq_orderedProd_maskWord,
    subwordProd_eq_orderedProd_maskWord]
  congr 1
  funext i
  simp only [maskWord, restrict, Finset.mem_inter]
  by_cases hD : i ∈ D
  · by_cases hS : i ∈ r.supp
    · simp [hD, hS]
    · have : r i = none := by
        rw [supp, mem_optSupp, Option.not_isSome_iff_eq_none] at hS
        exact hS
      simp [hD, hS, this]
  · simp [hD]

open Classical in
/-- **Deterministic compression** of a record to at most `b` positions with the same
product, as a function of the record alone. -/
noncomputable def compress (b : ℕ) (r : Record n σ) : Record n σ :=
  if h : ∃ D ⊆ r.supp, D.card ≤ b ∧ (r.restrict D).prod letter = r.prod letter
  then r.restrict (Classical.choose h) else r

theorem compress_spec {b : ℕ} (hb : IsBreadthBound letter b) (r : Record n σ) :
    (compress letter b r).supp ⊆ r.supp ∧ (compress letter b r).supp.card ≤ b
      ∧ (compress letter b r).prod letter = r.prod letter := by
  have hex : ∃ D ⊆ r.supp, D.card ≤ b ∧ (r.restrict D).prod letter = r.prod letter := by
    obtain ⟨D, hDs, hDb, hD⟩ := exists_compress (letterOpt letter)
      (isBreadthBound_letterOpt letter hb) r r.supp
    refine ⟨D, hDs, hDb, ?_⟩
    rw [prod_restrict, prod_eq_subwordProd, Finset.inter_eq_right.2 hDs]
    exact hD
  rw [compress, dif_pos hex]
  obtain ⟨hDs, hDb, hD⟩ := Classical.choose_spec hex
  refine ⟨?_, ?_, hD⟩
  · rw [supp_restrict]; exact Finset.inter_subset_left
  · rw [supp_restrict]
    exact (Finset.card_le_card Finset.inter_subset_right).trans hDb

lemma truthful_compress {x : Fin n → σ} {r : Record n σ} (h : Truthful x r) (b : ℕ) :
    Truthful x (compress letter b r) := by
  rw [compress]
  split_ifs
  · exact truthful_restrict h _
  · exact h

end Record

end Records

end MonoidProduct
