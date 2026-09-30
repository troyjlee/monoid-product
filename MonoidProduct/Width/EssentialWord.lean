import MonoidProduct.Width.Breadth

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# All-essential words of every length up to the breadth

The commutative lower bound needs, for each `r ≤ β`, a word `a` of length `r` in which
deleting any single position changes the product.  `exists_card_prodEss_eq_breadth` gives a
word with `β` essential positions; any `r` of them stay essential in the product restricted
to them (`prodEss_eq_self_of_subset_prodEss`: a deletion that preserved the restricted product
would, multiplied by the fixed context, preserve the full product — commutativity, no
cancellation), and `restrictWord` transports the restriction to a word of length `r`
(`exists_all_essential_word`).  In such a word no letter is the identity
(`ne_one_of_mem_prodEss`).
-/

namespace MonoidProduct

open Finset

section EssentialWord

variable {σ : Type} {M : Type} [CommMonoid M] [DecidableEq M]

/-- Reindexing along an equivalence preserves essentiality. -/
lemma mem_prodEss_comp_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (m : σ → M) (w : κ → σ) (e : ι ≃ κ) (i : ι) :
    i ∈ prodEss m (w ∘ e) Finset.univ ↔ e i ∈ prodEss m w Finset.univ := by
  rw [mem_prodEss', mem_prodEss']
  simp only [Finset.mem_univ, true_and, Function.comp]
  have h1 : ∏ j, m (w (e j)) = ∏ k, m (w k) := Fintype.prod_equiv e _ _ fun j => rfl
  have h2 : ∏ j ∈ Finset.univ.erase i, m (w (e j)) = ∏ k ∈ Finset.univ.erase (e i), m (w k) :=
    Finset.prod_equiv e (fun j => by simp [e.injective.eq_iff]) (fun j _ => rfl)
  rw [h1, h2]

/-- **Essential positions stay essential in any sub-product containing them.** -/
lemma prodEss_eq_self_of_subset_prodEss {ι : Type} [Fintype ι] [DecidableEq ι] (m : σ → M)
    (x : ι → σ) {T : Finset ι} (hT : T ⊆ prodEss m x Finset.univ) :
    prodEss m x T = T := by
  refine Finset.Subset.antisymm (prodEss_subset' m x T) fun i hi => ?_
  refine mem_prodEss'.mpr ⟨hi, fun heq => ?_⟩
  obtain ⟨-, hne⟩ := mem_prodEss'.mp (hT hi)
  apply hne
  have hsub : T ⊆ Finset.univ := Finset.subset_univ T
  have hsub' : T.erase i ⊆ Finset.univ.erase i := Finset.erase_subset_erase i hsub
  have hsd : Finset.univ.erase i \ T.erase i = Finset.univ \ T := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨hji, h⟩
      exact fun hjT => h ⟨hji, hjT⟩
    · intro h
      refine ⟨fun hji => ?_, fun h' => h h'.2⟩
      subst hji
      exact h hi
  calc ∏ j, m (x j) = (∏ j ∈ Finset.univ \ T, m (x j)) * ∏ j ∈ T, m (x j) :=
        (Finset.prod_sdiff hsub).symm
    _ = (∏ j ∈ Finset.univ \ T, m (x j)) * ∏ j ∈ T.erase i, m (x j) := by rw [heq]
    _ = (∏ j ∈ Finset.univ.erase i \ T.erase i, m (x j)) * ∏ j ∈ T.erase i, m (x j) := by
        rw [hsd]
    _ = ∏ j ∈ Finset.univ.erase i, m (x j) := Finset.prod_sdiff hsub'

/-- An essential letter is not the identity. -/
lemma ne_one_of_mem_prodEss {ι : Type} [Fintype ι] [DecidableEq ι] (m : σ → M) (a : ι → σ)
    {j : ι} (hj : j ∈ prodEss m a Finset.univ) : m (a j) ≠ 1 := by
  obtain ⟨-, hne⟩ := mem_prodEss'.mp hj
  intro h1
  apply hne
  rw [← Finset.mul_prod_erase Finset.univ (fun i => m (a i)) (Finset.mem_univ j), h1, one_mul]

/-- **All-essential words of every length up to the breadth.** -/
theorem exists_all_essential_word [Fintype σ] [DecidableEq σ] [Fintype M] [IsAperiodicMonoid M]
    (m : σ → M) {r : ℕ} (hr : r ≤ breadth m) :
    ∃ a : Fin r → σ, prodEss m a Finset.univ = Finset.univ := by
  obtain ⟨n, x, hx⟩ := exists_card_prodEss_eq_breadth m
  obtain ⟨T, hTE, hTc⟩ := Finset.exists_subset_card_eq
    (show r ≤ (prodEss m x Finset.univ).card by rw [hx]; exact hr)
  have hT : prodEss m x T = T := prodEss_eq_self_of_subset_prodEss m x hTE
  have hres : prodEss m (restrictWord x T) Finset.univ = Finset.univ := by
    apply Finset.map_injective (restrictEmb T)
    rw [prodEss_restrictWord, hT, map_univ_restrictEmb]
  refine ⟨restrictWord x T ∘ finCongr hTc.symm, ?_⟩
  ext i
  rw [mem_prodEss_comp_equiv, hres]
  simp

end EssentialWord

end MonoidProduct
