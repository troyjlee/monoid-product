import MonoidProduct.Tropical.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The ordered tropical product and the named identity

The basic vocabulary shared by the tropical modules:

* the monoid laws of `U_k(T)`: `tmul_assoc`, `tmul_tone`, `tone_tmul`;
* `linProd letter n x = x₀ ⊗ ⋯ ⊗ x_{n-1}`, the left-to-right product of `n` letters
  in `U_k(T)` (`linProd_zero`, `linProd_succ`);
* `optLetter letter`, the letters with a name (`none`) adjoined for the identity
  `tone k`, and `isUtri_optLetter`.

(Split out of `Tropical/Assoc.lean` and `Tropical/Pad.lean`, whose statements are
unchanged, so that the masking and lower-bound modules need not import the
`(c·k·log n)^k·√n` upper-bound development.)
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {k : ℕ}

/-! ## Adding distributes over finite suprema -/

private lemma sup_add_right (x y b : Trop) : (x ⊔ y) + b = (x + b) ⊔ (y + b) := by
  rcases le_total x y with h | h
  · have h' : x + b ≤ y + b := add_le_add h (le_refl b)
    rw [sup_eq_right.2 h, sup_eq_right.2 h']
  · have h' : y + b ≤ x + b := add_le_add h (le_refl b)
    rw [sup_eq_left.2 h, sup_eq_left.2 h']

private lemma finsetSup_add {α : Type*} (s : Finset α) (f : α → Trop) (b : Trop) :
    s.sup f + b = s.sup fun a => f a + b := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s _ ih
    rw [Finset.sup_insert, Finset.sup_insert, ← ih, sup_add_right]

private lemma add_finsetSup {α : Type*} (s : Finset α) (f : α → Trop) (b : Trop) :
    b + s.sup f = s.sup fun a => b + f a := by
  rw [add_comm, finsetSup_add]
  exact Finset.sup_congr rfl fun a _ => add_comm _ _

/-! ## The monoid laws -/

/-- **Tropical matrix multiplication is associative.**  Both sides are the same
double supremum `⨆_{v,w} (M s v + N v w + P w t)`. -/
theorem tmul_assoc (M N P : TMat k) : tmul (tmul M N) P = tmul M (tmul N P) := by
  funext s t
  simp only [tmul]
  rw [Finset.sup_congr rfl fun w (_ : w ∈ Finset.univ) =>
      finsetSup_add Finset.univ (fun v => M s v + N v w) (P w t),
    Finset.sup_congr rfl fun v (_ : v ∈ Finset.univ) =>
      add_finsetSup Finset.univ (fun w => N v w + P w t) (M s v),
    Finset.sup_comm]
  exact Finset.sup_congr rfl fun v _ =>
    Finset.sup_congr rfl fun w _ => add_assoc _ _ _

/-- `tone` is a right identity: the only walk that ends by standing still is the
one that has already arrived. -/
@[simp] theorem tmul_tone (M : TMat k) : tmul M (tone k) = M := by
  funext s t
  simp only [tmul, tone]
  refine le_antisymm (Finset.sup_le fun v _ => ?_) ?_
  · by_cases h : v = t
    · subst h
      rw [if_pos rfl, add_zero]
    · rw [if_neg h, WithBot.add_bot]
      exact bot_le
  · refine le_trans (le_of_eq ?_)
      (Finset.le_sup (f := fun v => M s v + if v = t then (0 : Trop) else ⊥)
        (Finset.mem_univ t))
    rw [if_pos rfl, add_zero]

/-- `tone` is a left identity. -/
@[simp] theorem tone_tmul (M : TMat k) : tmul (tone k) M = M := by
  funext s t
  simp only [tmul, tone]
  refine le_antisymm (Finset.sup_le fun v _ => ?_) ?_
  · by_cases h : s = v
    · subst h
      rw [if_pos rfl, zero_add]
    · rw [if_neg h, WithBot.bot_add]
      exact bot_le
  · refine le_trans (le_of_eq ?_)
      (Finset.le_sup (f := fun v => (if s = v then (0 : Trop) else ⊥) + M v t)
        (Finset.mem_univ s))
    rw [if_pos rfl, zero_add]

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## The ordered product of `n` letters -/

/-- The product `x₀ ⊗ ⋯ ⊗ x_{n-1}`. -/
noncomputable def linProd (letter : σ → TMat k) : (n : ℕ) → (Fin n → σ) → TMat k
  | 0, _ => tone k
  | m + 1, x =>
      tmul (linProd letter m fun i => x i.castSucc) (letter (x (Fin.last m)))

@[simp] lemma linProd_zero (letter : σ → TMat k) (x : Fin 0 → σ) :
    linProd letter 0 x = tone k := rfl

lemma linProd_succ (letter : σ → TMat k) (m : ℕ) (x : Fin (m + 1) → σ) :
    linProd letter (m + 1) x
      = tmul (linProd letter m fun i => x i.castSucc) (letter (x (Fin.last m))) :=
  rfl

/-! ## Naming the identity -/

/-- The letters, with a name adjoined for the identity of `U_k(T)`. -/
noncomputable def optLetter (letter : σ → TMat k) : Option σ → TMat k
  | none => tone k
  | some a => letter a

lemma isUtri_optLetter {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a)) :
    ∀ a : Option σ, IsUtri (optLetter letter a)
  | none => isUtri_tone
  | some a => hL a

end MonoidProduct
