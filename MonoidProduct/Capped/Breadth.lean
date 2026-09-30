import MonoidProduct.Width.Breadth
import MonoidProduct.Capped.Width
import MonoidProduct.Capped.Lower
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Capped counters attain their breadth: `β(M_{k,r}) = k·r`

`monoid.tex` Theorem `thm:capped-counter-product`, the breadth clause.  For
`M_{k,r} = Capped k ^ ρ` (`r = |ρ|`) over the full alphabet:

* `β ≤ k·r` is the width bound `card_prodEss_le_capped` read through
  `breadth_le_of_width`;
* `k·r ≤ β` is witnessed by the **unit word** — `k` copies of each unit vector
  — whose only core is the whole word: a proper subword misses some copy of
  some unit vector `e_c`, so its coordinate `c` is at most `k − 1 < k`.

Together, `breadth_capped_eq : β(M_{k,r}) = k·r`, which is the paper's
"the dependence on `β` itself is sharp" against `advPM_cappedProd_sandwich`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ] {k : ℕ}

/-! ## The upper bound -/

/-- The capped width bound, for words of every length. -/
lemma card_prodEss_le_capped' {σ : Type} [Fintype σ] [DecidableEq σ]
    (m : σ → ρ → Capped k) {n : ℕ} (x : Fin n → σ) (T : Finset (Fin n)) :
    (prodEss m x T).card ≤ Fintype.card ρ * k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h : (prodEss m x T).card ≤ Fintype.card (Fin 0) :=
      (Finset.card_le_card (prodEss_subset' m x T)).trans (Finset.card_le_univ T)
    rw [Fintype.card_fin] at h
    omega
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact card_prodEss_le_capped m x T

/-- **`β ≤ k·r`** for any alphabet in `M_{k,r}`. -/
theorem breadth_le_capped {σ : Type} [Fintype σ] [DecidableEq σ]
    (m : σ → ρ → Capped k) : breadth m ≤ Fintype.card ρ * k :=
  breadth_le (isBreadthBound_of_width fun _ x T => card_prodEss_le_capped' m x T)

/-! ## The unit word -/

/-- The index set of the unit word: one position per (coordinate, copy). -/
noncomputable def unitEquiv (ρ : Type) [Fintype ρ] (k : ℕ) :
    Fin (Fintype.card (ρ × Fin k)) ≃ ρ × Fin k :=
  (Fintype.equivFin (ρ × Fin k)).symm

/-- **The unit word**: `k` copies of each unit vector `e_c`. -/
noncomputable def unitWord (ρ : Type) [Fintype ρ] [DecidableEq ρ] (k : ℕ) :
    Fin (Fintype.card (ρ × Fin k)) → (ρ → Capped k) :=
  fun j => cappedUnit k (unitEquiv ρ k j).1

lemma gen_val_of_pos (hk : 0 < k) : (Capped.gen : Capped k).val = 1 := by
  change min 1 k = 1
  omega

lemma unitWord_apply_val (hk : 0 < k) (j : Fin (Fintype.card (ρ × Fin k))) (c : ρ) :
    (unitWord ρ k j c).val = if c = (unitEquiv ρ k j).1 then 1 else 0 := by
  unfold unitWord cappedUnit
  split_ifs <;> simp [gen_val_of_pos hk]

lemma sum_unitWord_val (hk : 0 < k) (u : Finset (Fin (Fintype.card (ρ × Fin k)))) (c : ρ) :
    ∑ j ∈ u, (unitWord ρ k j c).val
      = (u.filter fun j => c = (unitEquiv ρ k j).1).card := by
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun j _ => unitWord_apply_val hk j c

/-- Each coordinate is hit by exactly `k` positions of the unit word. -/
lemma card_fiber_unitEquiv (c : ρ) :
    (Finset.univ.filter fun j => c = (unitEquiv ρ k j).1).card = k := by
  have hinj : Function.Injective fun i : Fin k => (unitEquiv ρ k).symm (c, i) := by
    intro a b h
    exact (Prod.ext_iff.mp ((unitEquiv ρ k).symm.injective h)).2
  have hmap : (Finset.univ.filter fun j => c = (unitEquiv ρ k j).1)
      = Finset.univ.image fun i : Fin k => (unitEquiv ρ k).symm (c, i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hc
      refine ⟨(unitEquiv ρ k j).2, ?_⟩
      rw [show (c, (unitEquiv ρ k j).2) = unitEquiv ρ k j from Prod.ext hc rfl,
        Equiv.symm_apply_apply]
    · rintro ⟨i, rfl⟩
      simp
  rw [hmap, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- The coordinate `c` of a subword product of the unit word counts the
retained copies of `e_c`, capped at `k`. -/
lemma val_prod_unitWord (hk : 0 < k) (u : Finset (Fin (Fintype.card (ρ × Fin k)))) (c : ρ) :
    ((∏ j ∈ u, unitWord ρ k j) c).val
      = min (u.filter fun j => c = (unitEquiv ρ k j).1).card k := by
  rw [Finset.prod_apply, Capped.val_prod, sum_unitWord_val hk]

/-! ## The lower bound and the equality -/

/-- **`k·r ≤ β`** over the full alphabet: the unit word's only core is the
whole word. -/
theorem card_mul_le_breadth_capped (hk : 0 < k) :
    Fintype.card ρ * k ≤ breadth (id : (ρ → Capped k) → (ρ → Capped k)) := by
  have hb : ∃ b, IsBreadthBound (id : (ρ → Capped k) → (ρ → Capped k)) b :=
    ⟨_, isBreadthBound_of_width fun _ x T => card_prodEss_le_capped' id x T⟩
  refine le_breadth_of_forall_core hb (unitWord ρ k) fun u hu => ?_
  rw [isCore_iff] at hu
  simp only [id] at hu
  by_contra hlt
  push Not at hlt
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ ∉ u := by
    by_contra h
    push Not at h
    have huniv : u = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [huniv, Finset.card_univ, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin] at hlt
    omega
  set c := (unitEquiv ρ k j₀).1 with hc
  have h1 : ((∏ j ∈ u, unitWord ρ k j) c).val = ((∏ j, unitWord ρ k j) c).val := by
    rw [hu]
  rw [val_prod_unitWord hk, val_prod_unitWord hk, card_fiber_unitEquiv, min_self] at h1
  have hsub : (u.filter fun j => c = (unitEquiv ρ k j).1)
      ⊂ Finset.univ.filter fun j => c = (unitEquiv ρ k j).1 := by
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset_filter _ (Finset.subset_univ u), fun heq => hj₀ ?_⟩
    have : j₀ ∈ u.filter fun j => c = (unitEquiv ρ k j).1 := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    exact (Finset.mem_filter.mp this).1
  have hlt' := Finset.card_lt_card hsub
  rw [card_fiber_unitEquiv] at hlt'
  omega

/-- **`β(M_{k,r}) = k·r`** (`thm:capped-counter-product`, breadth clause). -/
theorem breadth_capped_eq (hk : 0 < k) :
    breadth (id : (ρ → Capped k) → (ρ → Capped k)) = Fintype.card ρ * k :=
  le_antisymm (breadth_le_capped id) (card_mul_le_breadth_capped hk)

end MonoidProduct
