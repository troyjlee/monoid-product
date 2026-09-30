import MonoidProduct.Width.Product
import MonoidProduct.Capped.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Capped-counter products: the width upper bound (`thm:capped-counter-product`)

For `M_{k,r} = Capped k ^ r` (the `r`-fold power of the capped counter), the
essential set of the subset-product summary has at most `k·r` elements: each
essential position is charged to a coordinate whose capped sum its deletion
changes, and `Capped.card_filter_capped_ne_le` caps every coordinate's charge
at `k`.  Together with the trivial bound `κ ≤ n` and the essential-width
theorem this gives

  `ADV±(Prod_{M_{k,r},n}) ≤ 16·√(n·min{n, k·r})`,

the upper half of the paper's `Θ(√(n·min{n,kr}))`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- **The width bound `κ ≤ k·r`** for the capped-counter power
`M_{k,r} = Capped k ^ r`: charge each essential position to a coordinate its
deletion changes; no coordinate absorbs more than `k` charges. -/
theorem card_prodEss_le_capped {k : ℕ}
    (m : σ → ρ → Capped k) (x : ι → σ) (T : Finset ι) :
    (prodEss m x T).card ≤ Fintype.card ρ * k := by
  classical
  have hsub : prodEss m x T ⊆ Finset.univ.biUnion fun c : ρ =>
      T.filter fun i =>
        ∏ j ∈ T, m (x j) c ≠ ∏ j ∈ T.erase i, m (x j) c := by
    intro i hi
    obtain ⟨hiT, hne⟩ := mem_prodEss.mp hi
    obtain ⟨c, hc⟩ := Function.ne_iff.mp hne
    refine Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_univ c, Finset.mem_filter.mpr ⟨hiT, ?_⟩⟩
    intro heq
    refine hc ?_
    calc (∏ j ∈ T, m (x j)) c
        = ∏ j ∈ T, m (x j) c :=
          map_prod (Pi.evalMonoidHom (fun _ : ρ => Capped k) c) _ T
      _ = ∏ j ∈ T.erase i, m (x j) c := heq
      _ = (∏ j ∈ T.erase i, m (x j)) c :=
          (map_prod (Pi.evalMonoidHom (fun _ : ρ => Capped k) c) _ _).symm
  calc (prodEss m x T).card
      ≤ (Finset.univ.biUnion fun c : ρ =>
          T.filter fun i =>
            ∏ j ∈ T, m (x j) c ≠ ∏ j ∈ T.erase i, m (x j) c).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ c : ρ, (T.filter fun i =>
          ∏ j ∈ T, m (x j) c ≠ ∏ j ∈ T.erase i, m (x j) c).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _c : ρ, k :=
        Finset.sum_le_sum fun c _ =>
          Capped.card_filter_capped_ne_le T fun j => m (x j) c
    _ = Fintype.card ρ * k := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **The capped-counter upper bound** (`thm:capped-counter-product`, upper half):
`ADV±(Prod_{M_{k,r},n}) ≤ 16·√(n·min{n, k·r})` where `r = |ρ|`. -/
theorem advPM_prodFun_le_capped {k : ℕ} (hk : 0 < k) [Nonempty ρ]
    (m : σ → ρ → Capped k) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * (min (Fintype.card ι) (Fintype.card ρ * k) : ℕ)) := by
  refine advPM_prodFun_le_of_width m ?_ ?_
  · exact lt_min_iff.mpr ⟨Fintype.card_pos, Nat.mul_pos Fintype.card_pos hk⟩
  · intro x T
    exact le_min (Finset.card_le_univ _) (card_prodEss_le_capped m x T)

end MonoidProduct
