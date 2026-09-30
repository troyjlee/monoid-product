import MonoidProduct.UT.Defs
import QuantumQueryComplexity.Scan.Bounded
import MonoidProduct.Aperiodic.EqProd
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The `UT_k(𝔹)` product: the upper bound `8√(n·min{n, C(k,2)})`

`monoid.tex` Theorem `thm:boolean-unitriangular`, upper half.  The prefix
products `pᵢ = x₁ ⋯ xᵢ` form a sequential summary of the full product, and
because every letter is reflexive they are **entrywise monotone**:
`pᵢ ≤ pᵢ₊₁`.  A Boolean entry can therefore improve only once, the diagonal
and the lower triangle never move, so the prefix state changes at most
`C(k,2)` times — and trivially at most `n` times.  The bounded-change scan
(`hasDual_scan`) then gives an explicit dual of cost
`8√(n·min{n, C(k,2)})`, uniformly in the letter alphabet.

The change bound is an injection: every change step flips some strict-upper
entry from `false` to `true` (`exists_flip`), and monotonicity makes the
chosen entries distinct across steps (`changeCount_le_choose`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

open Finset

variable {k : ℕ}

/-! ## Entrywise order -/

/-- Multiplying by a reflexive matrix on the right only adds entries. -/
lemma le_bmul_of_diag (M N : BMat k) (hN : ∀ t, N t t = true) :
    M ≤ bmul M N := by
  intro s t
  rw [Bool.le_iff_imp]
  intro h
  exact (bmul_apply M N s t).mpr ⟨t, h, hN t⟩

/-- The number of strict-upper positions is at most `C(k,2)`. -/
lemma card_upper_pairs_le (k : ℕ) :
    (univ.filter fun p : Fin k × Fin k => p.1 < p.2).card ≤ k.choose 2 := by
  have h := card_le_card_of_injOn
    (fun p : Fin k × Fin k => ({p.1, p.2} : Finset (Fin k)))
    (s := univ.filter fun p : Fin k × Fin k => p.1 < p.2)
    (t := powersetCard 2 univ) ?_ ?_
  · rwa [card_powersetCard, card_univ, Fintype.card_fin] at h
  · intro p hp
    have hp' := mem_filter.mp (mem_coe.mp hp)
    exact mem_coe.mpr (mem_powersetCard.mpr
      ⟨subset_univ _, card_pair (ne_of_lt hp'.2)⟩)
  · intro p hp q hq hpq
    have hp' := mem_filter.mp (mem_coe.mp hp)
    have hq' := mem_filter.mp (mem_coe.mp hq)
    have hpq' : ({p.1, p.2} : Finset (Fin k)) = {q.1, q.2} := hpq
    have h1 : p.1 ∈ ({q.1, q.2} : Finset (Fin k)) := by
      rw [← hpq']
      exact mem_insert_self _ _
    have h2 : p.2 ∈ ({q.1, q.2} : Finset (Fin k)) := by
      rw [← hpq']
      exact mem_insert_of_mem (mem_singleton_self _)
    rw [mem_insert, mem_singleton] at h1 h2
    have hlp := Fin.lt_def.mp hp'.2
    have hlq := Fin.lt_def.mp hq'.2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      rw [Fin.ext_iff] at h1 h2
      omega
    · exact Prod.ext h1 h2
    · exfalso
      rw [Fin.ext_iff] at h1 h2
      omega
    · exfalso
      rw [Fin.ext_iff] at h1 h2
      omega

/-! ## The prefix-product summary -/

variable {σ : Type} [Fintype σ] [DecidableEq σ] {n : ℕ}

/-- The summary step: multiply the next letter on the right. -/
def butStep (letter : σ → BUT k) : Fin n → BUT k → σ → BUT k :=
  fun _ q a => q * letter a

variable (letter : σ → BUT k)

/-- The prefix product after `t` letters. -/
def prefixProd (x : Fin n → σ) (t : ℕ) : BUT k :=
  scanState (1 : BUT k) (butStep letter) x t

/-- The prefix products are the ordered range products. -/
lemma prefixProd_eq_rangeProd (x : Fin n → σ) (t : ℕ) :
    prefixProd letter x t = rangeProd (fun i => letter (x i)) 0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [rangeProd_succ_right _ (Nat.zero_le t)]
      by_cases h : t < n
      · have : prefixProd letter x (t + 1)
            = prefixProd letter x t * letter (x ⟨t, h⟩) := by
          simp only [prefixProd, scanState, dif_pos h, butStep]
        rw [this, ih, padAt_of_lt _ h]
      · have : prefixProd letter x (t + 1) = prefixProd letter x t := by
          simp only [prefixProd, scanState, dif_neg h]
        rw [this, ih, padAt_of_le _ (by omega), mul_one]

/-- The full prefix product is the word product. -/
lemma prefixProd_n (x : Fin n → σ) :
    prefixProd letter x n = wordProd letter x :=
  prefixProd_eq_rangeProd letter x n

/-- **Entrywise monotonicity**: every letter is reflexive. -/
lemma mat_prefixProd_mono (x : Fin n → σ) :
    Monotone fun t => (prefixProd letter x t).mat := by
  refine monotone_nat_of_le_succ fun t => ?_
  by_cases h : t < n
  · have : prefixProd letter x (t + 1)
        = prefixProd letter x t * letter (x ⟨t, h⟩) := by
      simp only [prefixProd, scanState, dif_pos h, butStep]
    rw [this, BUT.mat_mul]
    exact le_bmul_of_diag _ _ (letter (x ⟨t, h⟩)).isBUtri_mat.diag
  · have : prefixProd letter x (t + 1) = prefixProd letter x t := by
      simp only [prefixProd, scanState, dif_neg h]
    rw [this]

/-- The entrywise form of monotonicity. -/
lemma mat_prefixProd_le (x : Fin n → σ) {a b : ℕ} (h : a ≤ b) (s t : Fin k) :
    (prefixProd letter x a).mat s t ≤ (prefixProd letter x b).mat s t :=
  mat_prefixProd_mono letter x h s t

/-! ## The change bound -/

/-- **Every change step flips a strict-upper entry** from `false` to `true`:
the diagonal and the lower triangle never move, and monotonicity forbids
`true → false`. -/
lemma exists_flip (x : Fin n → σ) {i : Fin n}
    (hi : scanCol (1 : BUT k) (butStep letter) x i = true) :
    ∃ p : Fin k × Fin k, p.1 < p.2
      ∧ (prefixProd letter x (i : ℕ)).mat p.1 p.2 = false
      ∧ (prefixProd letter x ((i : ℕ) + 1)).mat p.1 p.2 = true := by
  have hne : prefixProd letter x ((i : ℕ) + 1) ≠ prefixProd letter x (i : ℕ) :=
    of_decide_eq_true hi
  have hmat : (prefixProd letter x ((i : ℕ) + 1)).mat
      ≠ (prefixProd letter x (i : ℕ)).mat := fun h => hne (BUT.ext h)
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hmat
  obtain ⟨t, hst⟩ := Function.ne_iff.mp hs
  have hle := mat_prefixProd_le letter x (Nat.le_succ (i : ℕ)) s t
  have hflip : (prefixProd letter x (i : ℕ)).mat s t = false
      ∧ (prefixProd letter x ((i : ℕ) + 1)).mat s t = true := by
    rcases hA : (prefixProd letter x (i : ℕ)).mat s t with _ | _ <;>
      rcases hB : (prefixProd letter x ((i : ℕ) + 1)).mat s t with _ | _ <;>
      rw [hA, hB] at hle hst
    · exact absurd rfl hst
    · exact ⟨rfl, rfl⟩
    · exact absurd hle (by decide)
    · exact absurd rfl hst
  refine ⟨(s, t), ?_, hflip.1, hflip.2⟩
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact hlt
  · exfalso
    subst heq
    have := (prefixProd letter x (i : ℕ)).isBUtri_mat.diag s
    rw [hflip.1] at this
    exact Bool.false_ne_true this
  · exfalso
    have := (prefixProd letter x ((i : ℕ) + 1)).isBUtri_mat.below s t hgt
    rw [hflip.2] at this
    exact absurd this (by decide)

/-- **At most `C(k,2)` changes**: the flipped entries are distinct across
change steps. -/
lemma changeCount_le_choose (x : Fin n → σ) :
    changeCount (1 : BUT k) (butStep letter) x ≤ k.choose 2 := by
  classical
  let S : Finset (Fin n) := univ.filter fun i =>
    scanCol (1 : BUT k) (butStep letter) x i = true
  let T : Finset (Fin k × Fin k) := univ.filter fun p => p.1 < p.2
  let flip : Fin n → Option (Fin k × Fin k) := fun i =>
    if h : ∃ p : Fin k × Fin k, p.1 < p.2
        ∧ (prefixProd letter x (i : ℕ)).mat p.1 p.2 = false
        ∧ (prefixProd letter x ((i : ℕ) + 1)).mat p.1 p.2 = true
    then some (Classical.choose h) else none
  have hflip : ∀ i (hi : i ∈ S), flip i = some (Classical.choose
      (exists_flip letter x (mem_filter.mp hi).2)) := by
    intro i hi
    exact dif_pos _
  have hmaps : ∀ i ∈ S, flip i ∈ T.image some := by
    intro i hi
    rw [hflip i hi, mem_image]
    refine ⟨_, ?_, rfl⟩
    rw [mem_filter]
    exact ⟨mem_univ _, (Classical.choose_spec (exists_flip letter x
      (mem_filter.mp hi).2)).1⟩
  have hinj : Set.InjOn flip ↑S := by
    intro i hi j hj hij
    rw [mem_coe] at hi hj
    rw [hflip i hi, hflip j hj, Option.some.injEq] at hij
    have hi' := Classical.choose_spec (exists_flip letter x (mem_filter.mp hi).2)
    have hj' := Classical.choose_spec (exists_flip letter x (mem_filter.mp hj).2)
    set p := Classical.choose (exists_flip letter x (mem_filter.mp hi).2) with hp
    rw [← hij] at hj'
    by_contra hne
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hne (Fin.ext h)) with hlt | hgt
    · -- `i < j`: the entry is `true` after step `i`, hence at time `j`
      have hmono := mat_prefixProd_le letter x
        (show (i : ℕ) + 1 ≤ (j : ℕ) from hlt) p.1 p.2
      rw [hi'.2.2, hj'.2.1] at hmono
      exact absurd hmono (by decide)
    · have hmono := mat_prefixProd_le letter x
        (show (j : ℕ) + 1 ≤ (i : ℕ) from hgt) p.1 p.2
      rw [hj'.2.2, hi'.2.1] at hmono
      exact absurd hmono (by decide)
  calc changeCount (1 : BUT k) (butStep letter) x = S.card := rfl
    _ ≤ (T.image some).card := card_le_card_of_injOn flip hmaps hinj
    _ = T.card := card_image_of_injective _ (Option.some_injective _)
    _ ≤ k.choose 2 := card_upper_pairs_le k

/-- At most `n` changes, trivially. -/
lemma changeCount_le_length (x : Fin n → σ) :
    changeCount (1 : BUT k) (butStep letter) x ≤ n := by
  refine (card_filter_le _ _).trans_eq ?_
  simp

/-! ## The upper bound -/

/-- **The `UT_k(𝔹)` product has an explicit dual of cost
`8√(n·min{n, C(k,2)})`**, uniformly in the letter alphabet
(`monoid.tex` Theorem `thm:boolean-unitriangular`, upper half). -/
theorem hasDual_wordProd_but :
    HasDual (fun x : Fin n → σ => wordProd letter x)
      (8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ))) := by
  have h := hasDual_scan (n := n) (1 : BUT k) (butStep letter) (id : BUT k → BUT k)
    (C := min n (k.choose 2)) fun x =>
      le_min (changeCount_le_length letter x) (changeCount_le_choose letter x)
  exact h.ofEq fun x => by
    show prefixProd letter x n = wordProd letter x
    exact prefixProd_n letter x

end MonoidProduct
