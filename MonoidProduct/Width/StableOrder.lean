import MonoidProduct.Width.Breadth
set_option linter.style.header false

/-!
# Stable orders with least identity (`def:stable-least-order`)

A partial order on a monoid is *stable* if `a ≤ b → c·a·d ≤ c·b·d`, and its
identity is *least* if `1 ≤ a` for every `a`.  Under such an order, replacing
letters of a word by `1` can only decrease the product, so every masked
subword product is at most the word product (`subwordProd_le_wordProd`) and
the subword product is monotone in the mask (`subwordProd_mono`).  These are
the order-theoretic inputs of the stock core (`Stock/Beta.lean`) and of the
ordered product theorem (`thm:ordered-beta-product`).
-/

namespace MonoidProduct

/-- A stable partial order with least identity. -/
structure IsStableOrder (M : Type) [Monoid M] [PartialOrder M] : Prop where
  mul_le_mul_left : ∀ {a b : M} (c : M), a ≤ b → c * a ≤ c * b
  mul_le_mul_right : ∀ {a b : M} (c : M), a ≤ b → a * c ≤ b * c
  one_le : ∀ a : M, 1 ≤ a

namespace IsStableOrder

variable {M : Type} [Monoid M] [PartialOrder M] (h : IsStableOrder M)
include h

/-- `def:stable-least-order`: `a ≤ b → c·a·d ≤ c·b·d`. -/
lemma stable {a b : M} (c d : M) (hab : a ≤ b) : c * a * d ≤ c * b * d :=
  h.mul_le_mul_right d (h.mul_le_mul_left c hab)

lemma mul_le_mul {a b c d : M} (hab : a ≤ b) (hcd : c ≤ d) : a * c ≤ b * d :=
  (h.mul_le_mul_right c hab).trans (h.mul_le_mul_left b hcd)

/-- A product dominates its left factor. -/
lemma le_mul_right (a b : M) : a ≤ a * b := by
  simpa using h.mul_le_mul_left a (h.one_le b)

/-- A product dominates its right factor. -/
lemma le_mul_left (a b : M) : b ≤ a * b := by
  simpa using h.mul_le_mul_right b (h.one_le a)

/-- A word product is monotone in the letters. -/
lemma list_prod_le_list_prod : ∀ {l l' : List M}, List.Forall₂ (· ≤ ·) l l' → l.prod ≤ l'.prod
  | [], [], _ => le_rfl
  | _ :: _, _ :: _, List.Forall₂.cons hab hl => by
      rw [List.prod_cons, List.prod_cons]
      exact h.mul_le_mul hab (list_prod_le_list_prod hl)

variable {σ : Type} (letter : σ → M) {n : ℕ} (x : Fin n → σ)

/-- The masked subword product is monotone in the mask. -/
lemma subwordProd_mono {u v : Finset (Fin n)} (huv : u ⊆ v) :
    subwordProd letter x u ≤ subwordProd letter x v := by
  unfold subwordProd
  apply h.list_prod_le_list_prod
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  split_ifs with hu hv hv
  · exact le_rfl
  · exact absurd (huv hu) hv
  · exact h.one_le _
  · exact le_rfl

/-- Every masked subword product is at most the word product. -/
lemma subwordProd_le_wordProd (u : Finset (Fin n)) :
    subwordProd letter x u ≤ wordProd letter x := by
  rw [← subwordProd_univ]
  exact h.subwordProd_mono letter x (Finset.subset_univ u)

end IsStableOrder

end MonoidProduct
