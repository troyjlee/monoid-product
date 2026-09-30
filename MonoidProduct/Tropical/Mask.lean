import MonoidProduct.Tropical.LinProd
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Masking a tropical word, and the requested entries

The maximal-support refinement of the unitriangular breadth bound
(`cor:unitriangular-beta`) compares the product of a word with the
product of the word **retained on a set of positions** `S`: the letters
outside `S` are replaced by the tropical identity.  Everything the
refinement needs from the tropical layer is *monotonicity*:

* tropical multiplication is entrywise monotone (`tmul_mono`);
* every unitriangular letter dominates the identity entrywise
  (`tone_le_of_isUtri` — the diagonal is `0` on both, the rest of the
  identity is `-∞`);
* hence the product is monotone in the word (`linProd_mono`), retaining
  more positions can only increase every entry (`linProd_mask_mono`), and
  the fully retained word is the original (`linProd_mask_le`).

The paper phrases the same facts with paths: a path through the retained
subword pads to a path through the whole word by zero-weight diagonal
loops.  No paths appear here.

The **requested entries** `E` are read off in a fixed order into a vector
`Lex (Fin m → Trop)`, so that "`F_E(z) = max_M φ_M(z)`" is a maximum in a
genuine `LinearOrder` (the lexicographic order), as the scan duals
require; `entries_mono` transfers entrywise domination to it.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {k : ℕ}

/-! ## The entrywise order on `U_k(T)` -/

/-- Tropical multiplication is entrywise monotone. -/
lemma tmul_mono {M M' N N' : TMat k} (hM : M ≤ M') (hN : N ≤ N') :
    tmul M N ≤ tmul M' N' := by
  intro s t
  simp only [tmul]
  refine Finset.sup_le fun v _ => ?_
  calc M s v + N v t ≤ M' s v + N' v t := add_le_add (hM s v) (hN v t)
    _ ≤ _ := Finset.le_sup (f := fun v => M' s v + N' v t) (Finset.mem_univ v)

/-- Every unitriangular matrix dominates the identity entrywise. -/
lemma tone_le_of_isUtri {M : TMat k} (hM : IsUtri M) : tone k ≤ M := by
  intro s t
  by_cases h : s = t
  · subst h
    rw [hM.diag]
    simp [tone]
  · simp [tone, h]

variable {τ : Type} [Fintype τ] [DecidableEq τ]

/-- The product is monotone in the word, letter by letter. -/
lemma linProd_mono (letter : τ → TMat k) {n : ℕ} {w w' : Fin n → τ}
    (h : ∀ i, letter (w i) ≤ letter (w' i)) :
    linProd letter n w ≤ linProd letter n w' := by
  induction n with
  | zero => exact le_rfl
  | succ m ih =>
      rw [linProd_succ, linProd_succ]
      exact tmul_mono (ih fun i => h i.castSucc) (h (Fin.last m))

/-! ## Masking -/

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Retain the letters at the positions in `S`; every other position becomes
the identity (`none`, read through `optLetter`). -/
def mask {n : ℕ} (S : Finset (Fin n)) (w : Fin n → σ) : Fin n → Option σ :=
  fun i => if i ∈ S then some (w i) else none

@[simp] lemma mask_apply {n : ℕ} (S : Finset (Fin n)) (w : Fin n → σ) (i : Fin n) :
    mask S w i = if i ∈ S then some (w i) else none := rfl

lemma mask_univ {n : ℕ} (w : Fin n → σ) :
    mask Finset.univ w = fun i => some (w i) := by
  funext i
  simp [mask]

lemma mask_empty {n : ℕ} (w : Fin n → σ) : mask ∅ w = fun _ => none := by
  funext i
  simp [mask]

/-- Naming the identity changes nothing on the original letters. -/
lemma linProd_optLetter_some (letter : σ → TMat k) (n : ℕ) (w : Fin n → σ) :
    linProd (optLetter letter) n (fun i => some (w i)) = linProd letter n w := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [linProd_succ, linProd_succ]
      congr 1
      exact ih _

/-- **Retaining more positions can only increase the product.** -/
lemma linProd_mask_mono {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    {n : ℕ} {S T : Finset (Fin n)} (hST : S ⊆ T) (w : Fin n → σ) :
    linProd (optLetter letter) n (mask S w)
      ≤ linProd (optLetter letter) n (mask T w) := by
  refine linProd_mono _ fun i => ?_
  by_cases hi : i ∈ S
  · have hT : i ∈ T := hST hi
    simp [mask, hi, hT]
  · by_cases hT : i ∈ T
    · simp only [mask, hi, hT, if_true, if_false]
      exact tone_le_of_isUtri (hL _)
    · simp [mask, hi, hT]

/-- **The retained word never exceeds the original.** -/
lemma linProd_mask_le {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    {n : ℕ} (S : Finset (Fin n)) (w : Fin n → σ) :
    linProd (optLetter letter) n (mask S w) ≤ linProd letter n w := by
  have h := linProd_mask_mono hL (Finset.subset_univ S) w
  rwa [mask_univ, linProd_optLetter_some] at h

/-! ## The requested entries -/

/-- The requested entries `E`, read off in order into a lexicographically
ordered vector. -/
def entries {m : ℕ} (E : Fin m → Fin k × Fin k) (M : TMat k) : Lex (Fin m → Trop) :=
  toLex fun j => M (E j).1 (E j).2

lemma entries_mono {m : ℕ} (E : Fin m → Fin k × Fin k) {M N : TMat k} (h : M ≤ N) :
    entries E M ≤ entries E N :=
  Pi.toLex_monotone fun _ => h _ _

end MonoidProduct
