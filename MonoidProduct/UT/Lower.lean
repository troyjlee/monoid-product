import MonoidProduct.UT.Defs
import MonoidProduct.Aperiodic.EqProd
import MonoidProduct.Tropical.Lower
import QuantumQueryComplexity.Promise.Post
import QuantumQueryComplexity.Promise.Transport
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The `UT_k(𝔹)` product: the lower bound `√(n·min{n, ⌊k²/4⌋}/2)`

`monoid.tex` Theorem `thm:boolean-unitriangular`, lower half.  Split the
states into `A = {0, …, ⌊k/2⌋ − 1}` and `B` the rest.  A **cross edge** runs
from `A` to `B`; no two cross edges compose, so the matrices
`X_R = 1 + R` for `R ⊆ A × B` multiply by union, `X_R X_S = X_{R∪S}`
(`bmul_unionMat`) — a free union semilattice of rank `⌊k²/4⌋` inside
`UT_k(𝔹)`.

The rest is the disjoint-search machinery of `Tropical/Lower.lean`,
reused **verbatim**: `d ≤ ⌊k²/4⌋` cross edges, `d` balanced blocks of
positions, the promise "each block is the identity except for at most one
edge letter", and the parity of the marked blocks as a Boolean
postprocessing of the product (`bslotParity_wordProd_dsRead`).  The
certificate `dsTheta_le_advPMOn_dsFun` then gives `√(nd/2)` on the
promise, which transfers to the total product over the full alphabet
`UT_k(𝔹)` along the injective letter interpretation.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open Finset

variable {k : ℕ}

/-! ## Cross edges -/

/-- A cross edge runs from the first `⌊k/2⌋` states to the rest. -/
def IsCross (k : ℕ) (e : Fin k × Fin k) : Prop :=
  (e.1 : ℕ) < k / 2 ∧ k / 2 ≤ (e.2 : ℕ)

lemma IsCross.lt {e : Fin k × Fin k} (h : IsCross k e) : e.1 < e.2 := by
  obtain ⟨h1, h2⟩ := h
  rw [Fin.lt_def]
  omega

/-- **Cross edges do not compose**: the head of one is never the tail of
another. -/
lemma IsCross.ne_fst {e e' : Fin k × Fin k} (h : IsCross k e)
    (h' : IsCross k e') : e.2 ≠ e'.1 := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  intro heq
  have := congrArg Fin.val heq
  omega

/-! ## Union matrices -/

/-- The identity plus a set of edges. -/
def unionMat (R : Finset (Fin k × Fin k)) : BMat k :=
  fun s t => decide (s = t ∨ (s, t) ∈ R)

lemma unionMat_apply (R : Finset (Fin k × Fin k)) (s t : Fin k) :
    unionMat R s t = true ↔ s = t ∨ (s, t) ∈ R := by
  simp [unionMat]

lemma unionMat_empty : unionMat (∅ : Finset (Fin k × Fin k)) = bone k := by
  funext s t
  simp [unionMat, bone]

lemma isBUtri_unionMat {R : Finset (Fin k × Fin k)}
    (hR : ∀ e ∈ R, e.1 < e.2) : IsBUtri (unionMat R) where
  diag s := by simp [unionMat]
  below s t hts := by
    simp only [unionMat, decide_eq_false_iff_not, not_or]
    exact ⟨ne_of_gt hts, fun hmem => absurd (hR _ hmem) (not_lt.mpr hts.le)⟩

/-- **Cross-edge union matrices multiply by union.** -/
lemma bmul_unionMat {R S : Finset (Fin k × Fin k)}
    (hR : ∀ e ∈ R, IsCross k e) (hS : ∀ e ∈ S, IsCross k e) :
    bmul (unionMat R) (unionMat S) = unionMat (R ∪ S) := by
  funext s t
  simp only [bmul, unionMat, decide_eq_true_eq]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨v, hsv, hvt⟩
    rcases hsv with rfl | hsv
    · rcases hvt with rfl | hvt
      · exact Or.inl rfl
      · exact Or.inr (mem_union_right _ hvt)
    · rcases hvt with rfl | hvt
      · exact Or.inr (mem_union_left _ hsv)
      · exact absurd rfl ((hR _ hsv).ne_fst (hS _ hvt))
  · rintro (rfl | h)
    · exact ⟨s, Or.inl rfl, Or.inl rfl⟩
    · rcases mem_union.mp h with h | h
      · exact ⟨t, Or.inr h, Or.inl rfl⟩
      · exact ⟨s, Or.inl rfl, Or.inr h⟩

/-! ## The promise letters -/

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- The letter of the promise: the identity for `none`, the identity plus
the edge `edge c` for `some c`. -/
def optBLetter (edge : ρ → Fin k × Fin k) (hcross : ∀ c, IsCross k (edge c)) :
    Option ρ → BUT k
  | none => 1
  | some c => Subtype.mk (unionMat {edge c})
      (isBUtri_unionMat fun e he => by
        rw [mem_singleton] at he
        subst he
        exact (hcross c).lt)

variable (edge : ρ → Fin k × Fin k) (hcross : ∀ c, IsCross k (edge c))

@[simp] lemma optBLetter_none : optBLetter edge hcross none = 1 := rfl

@[simp] lemma mat_optBLetter_some (c : ρ) :
    (optBLetter edge hcross (some c)).mat = unionMat {edge c} := rfl

/-- The letter interpretation is injective. -/
lemma optBLetter_injective (hinj : Function.Injective edge) :
    Function.Injective (optBLetter edge hcross) := by
  intro o o' h
  have hmat := congrArg BUT.mat h
  have hedge : ∀ c : ρ, unionMat {edge c} (edge c).1 (edge c).2 = true :=
    fun c => (unionMat_apply _ _ _).mpr (Or.inr (by simp))
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some c' =>
        exfalso
        rw [optBLetter_none, BUT.mat_one, mat_optBLetter_some] at hmat
        have h1 := hedge c'
        rw [← hmat, bone_apply] at h1
        exact absurd h1 (ne_of_lt (hcross c').lt)
  | some c =>
    cases o' with
    | none =>
        exfalso
        rw [optBLetter_none, BUT.mat_one, mat_optBLetter_some] at hmat
        have h1 := hedge c
        rw [hmat, bone_apply] at h1
        exact absurd h1 (ne_of_lt (hcross c).lt)
    | some c' =>
        rw [mat_optBLetter_some, mat_optBLetter_some] at hmat
        have h1 := hedge c
        rw [hmat, unionMat_apply] at h1
        rcases h1 with h1 | h1
        · exact absurd h1 (ne_of_lt (hcross c).lt)
        · rw [mem_singleton] at h1
          exact congrArg some (hinj h1)

/-! ## The product of promise letters -/

variable {n : ℕ}

/-- The edges used by the first `t` letters of a word. -/
def usedEdges (w : Fin n → Option ρ) (t : ℕ) : Finset (Fin k × Fin k) :=
  univ.filter fun e => ∃ i : Fin n, (i : ℕ) < t ∧ ∃ c, w i = some c ∧ edge c = e

lemma mem_usedEdges (w : Fin n → Option ρ) (t : ℕ) (e : Fin k × Fin k) :
    e ∈ usedEdges edge w t
      ↔ ∃ i : Fin n, (i : ℕ) < t ∧ ∃ c, w i = some c ∧ edge c = e := by
  simp [usedEdges]

lemma usedEdges_cross (hcross : ∀ c, IsCross k (edge c)) (w : Fin n → Option ρ)
    (t : ℕ) : ∀ e ∈ usedEdges edge w t, IsCross k e := by
  intro e he
  rw [mem_usedEdges] at he
  obtain ⟨i, -, c, -, rfl⟩ := he
  exact hcross c

lemma usedEdges_zero (w : Fin n → Option ρ) : usedEdges edge w 0 = ∅ := by
  ext e
  simp [mem_usedEdges]

lemma usedEdges_succ_of_le (w : Fin n → Option ρ) {t : ℕ} (h : n ≤ t) :
    usedEdges edge w (t + 1) = usedEdges edge w t := by
  ext e
  simp only [mem_usedEdges]
  constructor
  · rintro ⟨i, -, hc⟩
    exact ⟨i, by have := i.isLt; omega, hc⟩
  · rintro ⟨i, hi, hc⟩
    exact ⟨i, by omega, hc⟩

lemma usedEdges_succ_none (w : Fin n → Option ρ) {t : ℕ} (h : t < n)
    (hw : w ⟨t, h⟩ = none) :
    usedEdges edge w (t + 1) = usedEdges edge w t := by
  ext e
  simp only [mem_usedEdges]
  constructor
  · rintro ⟨i, hi, c, hwi, he⟩
    refine ⟨i, ?_, c, hwi, he⟩
    by_contra hlt
    have hit : i = ⟨t, h⟩ := Fin.ext (show (i : ℕ) = t by omega)
    rw [hit, hw] at hwi
    exact (Option.some_ne_none c).symm hwi
  · rintro ⟨i, hi, hc⟩
    exact ⟨i, by omega, hc⟩

lemma usedEdges_succ_some (w : Fin n → Option ρ) {t : ℕ} (h : t < n) {c₀ : ρ}
    (hw : w ⟨t, h⟩ = some c₀) :
    usedEdges edge w (t + 1) = usedEdges edge w t ∪ {edge c₀} := by
  ext e
  simp only [mem_usedEdges, mem_union, mem_singleton]
  constructor
  · rintro ⟨i, hi, c, hwi, he⟩
    by_cases hlt : (i : ℕ) < t
    · exact Or.inl ⟨i, hlt, c, hwi, he⟩
    · have hit : i = ⟨t, h⟩ := Fin.ext (show (i : ℕ) = t by omega)
      rw [hit, hw] at hwi
      rw [← he, Option.some_injective _ hwi]
      exact Or.inr rfl
  · rintro (⟨i, hi, hc⟩ | rfl)
    · exact ⟨i, by omega, hc⟩
    · exact ⟨⟨t, h⟩, by simp, c₀, hw, rfl⟩

/-- **The product of promise letters is the union matrix of the edges
used.** -/
lemma mat_rangeProd_optBLetter (w : Fin n → Option ρ) :
    ∀ t, (rangeProd (fun i => optBLetter edge hcross (w i)) 0 t).mat
      = unionMat (usedEdges edge w t)
  | 0 => by
      rw [rangeProd_self, BUT.mat_one, usedEdges_zero, unionMat_empty]
  | t + 1 => by
      rw [rangeProd_succ_right _ (Nat.zero_le t), BUT.mat_mul,
        mat_rangeProd_optBLetter w t]
      by_cases h : t < n
      · rw [padAt_of_lt _ h]
        cases hw : w ⟨t, h⟩ with
        | none =>
            rw [optBLetter_none, BUT.mat_one, ← unionMat_empty,
              bmul_unionMat (usedEdges_cross edge hcross w t) (by simp),
              union_empty, usedEdges_succ_none edge w h hw]
        | some c =>
            rw [mat_optBLetter_some,
              bmul_unionMat (usedEdges_cross edge hcross w t) (by
                intro e he
                rw [mem_singleton] at he
                subst he
                exact hcross c),
              usedEdges_succ_some edge w h hw]
      · rw [padAt_of_le _ (by omega), BUT.mat_one, ← unionMat_empty,
          bmul_unionMat (usedEdges_cross edge hcross w t) (by simp),
          union_empty, usedEdges_succ_of_le edge w (by omega)]

lemma mat_wordProd_optBLetter (w : Fin n → Option ρ) :
    (wordProd (optBLetter edge hcross) w).mat = unionMat (usedEdges edge w n) :=
  mat_rangeProd_optBLetter edge hcross w n

/-- **The entry of the product at a cross edge** is `true` exactly when
some letter carries that edge. -/
lemma wordProd_optBLetter_edge (hinj : Function.Injective edge)
    (w : Fin n → Option ρ) (c : ρ) :
    (wordProd (optBLetter edge hcross) w).mat (edge c).1 (edge c).2 = true
      ↔ ∃ i, w i = some c := by
  rw [mat_wordProd_optBLetter, unionMat_apply]
  constructor
  · rintro (h | h)
    · exact absurd h (ne_of_lt (hcross c).lt)
    · rw [mem_usedEdges] at h
      obtain ⟨i, -, c', hw, he⟩ := h
      have hc : c' = c := hinj (by rw [he])
      exact ⟨i, hc ▸ hw⟩
  · rintro ⟨i, hw⟩
    exact Or.inr ((mem_usedEdges edge w n _).mpr ⟨i, i.isLt, c, hw, rfl⟩)

/-! ## The parity postprocessing -/

/-- The Boolean postprocessing: the parity of the number of designated
cross-edge entries that are `true`. -/
def bslotParity (P : BUT k) : Bool :=
  decide ((univ.filter fun c : ρ => P.mat (edge c).1 (edge c).2 = true).card
    % 2 = 1)

/-- On the promise, the designated entry of block `c` is `true` exactly when
the block is marked. -/
lemma wordProd_dsRead_edge (hinj : Function.Injective edge) {blk : Fin n → ρ}
    (x : DsMarks blk) (c : ρ) :
    (wordProd (optBLetter edge hcross) (dsRead blk x)).mat (edge c).1 (edge c).2
        = true
      ↔ (x c).isSome := by
  rw [wordProd_optBLetter_edge edge hcross hinj]
  constructor
  · rintro ⟨i, hi⟩
    rw [dsRead] at hi
    by_cases hm : x (blk i) = some ⟨i, rfl⟩
    · rw [if_pos hm] at hi
      have hbc : blk i = c := Option.some_injective _ hi
      subst hbc
      rw [hm]
      rfl
    · rw [if_neg hm] at hi
      exact absurd hi (Option.some_ne_none c).symm
  · intro hx
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨i, hi⟩ := a
    subst hi
    refine ⟨i, ?_⟩
    rw [dsRead, if_pos ha]

/-- **The parity of the marked blocks is a Boolean postprocessing of the
promise product.** -/
lemma bslotParity_wordProd_dsRead (hinj : Function.Injective edge)
    {blk : Fin n → ρ} (x : DsMarks blk) :
    bslotParity edge (wordProd (optBLetter edge hcross) (dsRead blk x))
      = dsFun blk x := by
  rw [bslotParity, dsFun]
  have hset : (univ.filter fun c : ρ =>
        (wordProd (optBLetter edge hcross) (dsRead blk x)).mat (edge c).1 (edge c).2
          = true)
      = univ.filter fun c => (x c).isSome :=
    filter_congr fun c _ => wordProd_dsRead_edge edge hcross hinj x c
  rw [hset]

/-! ## The lower bound on the promise -/

/-- **The abstract disjoint-search lower bound for the `UT_k(𝔹)` product**:
on the promise "block `c` is the identity except for at most one edge
letter", the promise product has `advPMOn ≥ ∑_c √|B_c|`. -/
theorem dsTheta_le_advPMOn_wordProd_but {blk : Fin n → ρ}
    (hsurj : Function.Surjective blk) (hinj : Function.Injective edge) :
    dsTheta blk ≤ advPMOn (dsRead blk)
      (fun x => wordProd (optBLetter edge hcross) (dsRead blk x)) := by
  refine (dsTheta_le_advPMOn_dsFun blk hsurj).trans ?_
  have hdet : ∀ x y : DsMarks blk, dsRead blk x = dsRead blk y →
      wordProd (optBLetter edge hcross) (dsRead blk x)
        = wordProd (optBLetter edge hcross) (dsRead blk y) := by
    intro x y h
    rw [h]
  have hcomp := advPMOn_comp_le
    (f := fun x => wordProd (optBLetter edge hcross) (dsRead blk x))
    hdet (bslotParity edge)
  rwa [show (fun x => bslotParity edge
        (wordProd (optBLetter edge hcross) (dsRead blk x))) = dsFun blk from
    funext fun x => bslotParity_wordProd_dsRead edge hcross hinj x] at hcomp

/-! ## The cross-edge enumeration -/

/-- `⌊k/2⌋·(k − ⌊k/2⌋)` cross edges, enumerated by division and remainder. -/
def crossEdge (k d : ℕ) (hd : d ≤ k / 2 * (k - k / 2)) (c : Fin d) :
    Fin k × Fin k :=
  have hb : 0 < k - k / 2 := Nat.pos_of_ne_zero fun h => by
    rw [h, mul_zero] at hd
    have := c.isLt
    omega
  (⟨(c : ℕ) / (k - k / 2), by
      have h1 : (c : ℕ) / (k - k / 2) < k / 2 :=
        (Nat.div_lt_iff_lt_mul hb).mpr (lt_of_lt_of_le c.isLt hd)
      omega⟩,
   ⟨k / 2 + (c : ℕ) % (k - k / 2), by
      have := Nat.mod_lt (c : ℕ) hb
      omega⟩)

lemma crossEdge_cross (k d : ℕ) (hd : d ≤ k / 2 * (k - k / 2)) (c : Fin d) :
    IsCross k (crossEdge k d hd c) := by
  have hb : 0 < k - k / 2 := Nat.pos_of_ne_zero fun h => by
    rw [h, mul_zero] at hd
    have := c.isLt
    omega
  refine ⟨?_, ?_⟩
  · show (c : ℕ) / (k - k / 2) < k / 2
    exact (Nat.div_lt_iff_lt_mul hb).mpr (lt_of_lt_of_le c.isLt hd)
  · show k / 2 ≤ k / 2 + (c : ℕ) % (k - k / 2)
    omega

lemma crossEdge_injective (k d : ℕ) (hd : d ≤ k / 2 * (k - k / 2)) :
    Function.Injective (crossEdge k d hd) := by
  intro c c' h
  have h1 : (c : ℕ) / (k - k / 2) = (c' : ℕ) / (k - k / 2) :=
    congrArg Fin.val (congrArg Prod.fst h)
  have h2 : k / 2 + (c : ℕ) % (k - k / 2) = k / 2 + (c' : ℕ) % (k - k / 2) :=
    congrArg Fin.val (congrArg Prod.snd h)
  have h2' : (c : ℕ) % (k - k / 2) = (c' : ℕ) % (k - k / 2) := by omega
  apply Fin.ext
  calc (c : ℕ) = (k - k / 2) * ((c : ℕ) / (k - k / 2)) + (c : ℕ) % (k - k / 2) :=
        (Nat.div_add_mod _ _).symm
    _ = (k - k / 2) * ((c' : ℕ) / (k - k / 2)) + (c' : ℕ) % (k - k / 2) := by
        rw [h1, h2']
    _ = (c' : ℕ) := Nat.div_add_mod _ _

/-! ## The parametric and total forms -/

/-- **The disjoint-search lower bound for `UT_k(𝔹)`, parametric form**: for
every `0 < d ≤ n` with `d ≤ ⌊k/2⌋·(k − ⌊k/2⌋)` cross edges, the promise
product has `advPMOn ≥ √(nd/2)`. -/
theorem sqrt_le_advPMOn_wordProd_but {k n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hdk : d ≤ k / 2 * (k - k / 2)) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPMOn (dsRead (modBlk n d hd))
          (fun x => wordProd (optBLetter (crossEdge k d hdk) (crossEdge_cross k d hdk))
            (dsRead (modBlk n d hd) x)) :=
  (sqrt_le_dsTheta hd hdn).trans
    (dsTheta_le_advPMOn_wordProd_but _ _ (modBlk_surjective hd hdn)
      (crossEdge_injective k d hdk))

/-- The promise certificate on the **full alphabet** `UT_k(𝔹)`: reading the
promise through the injective letter interpretation costs nothing. -/
theorem sqrt_le_advPMOn_wordProd_but_full {k n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hdk : d ≤ k / 2 * (k - k / 2)) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPMOn (fun x i => optBLetter (crossEdge k d hdk) (crossEdge_cross k d hdk)
            (dsRead (modBlk n d hd) x i))
          (fun x => wordProd (id : BUT k → BUT k)
            fun i => optBLetter (crossEdge k d hdk) (crossEdge_cross k d hdk)
              (dsRead (modBlk n d hd) x i)) := by
  rw [advPMOn_comp_injective
    (optBLetter_injective _ _ (crossEdge_injective k d hdk))]
  exact sqrt_le_advPMOn_wordProd_but hd hdn hdk

/-- **The total `UT_k(𝔹)` product is hard**: `ADV±(Prod_{UT_k(𝔹),n}) ≥
√(nd/2)` for every `0 < d ≤ min{n, ⌊k/2⌋·(k − ⌊k/2⌋)}`. -/
theorem sqrt_le_advPM_wordProd_but {k n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hdk : d ≤ k / 2 * (k - k / 2)) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPM (fun w : Fin n → BUT k => wordProd id w) :=
  (sqrt_le_advPMOn_wordProd_but_full hd hdn hdk).trans
    (advPMOn_le_advPM_of_injective
      (fun x y h => dsRead_injective _ (funext fun i =>
        optBLetter_injective _ _ (crossEdge_injective k d hdk)
          (congrFun h i)))
      fun _ => rfl)

/-- `⌊k/2⌋·(k − ⌊k/2⌋) = ⌊k²/4⌋`. -/
lemma half_mul_sub_half (k : ℕ) : k / 2 * (k - k / 2) = k ^ 2 / 4 := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have h1 : 2 * m / 2 = m := by omega
    have h2 : (2 * m) ^ 2 = 4 * (m * m) := by ring
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
    have : 2 * m - m = m := by omega
    rw [this]
  · have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    rw [h1, h2, Nat.mul_add_div (by norm_num : 0 < 4)]
    have : 2 * m + 1 - m = m + 1 := by omega
    rw [this]
    norm_num

/-- **Theorem `thm:boolean-unitriangular` of `monoid.tex`, lower half**: for
`k ≥ 2`, `n ≥ 1` and `d = min{n, ⌊k²/4⌋}`,
`ADV±(Prod_{UT_k(𝔹),n}) ≥ √(nd/2) = Ω(min{n, k√n})`. -/
theorem ut_lower_advPM {k n d : ℕ} (hk : 2 ≤ k) (hn : 0 < n)
    (hd : d = min n (k ^ 2 / 4)) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPM (fun w : Fin n → BUT k => wordProd id w) := by
  have hprod : 1 ≤ k / 2 * (k - k / 2) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [← half_mul_sub_half] at hd
  exact sqrt_le_advPM_wordProd_but (by omega) (by omega) (by omega)

end MonoidProduct
