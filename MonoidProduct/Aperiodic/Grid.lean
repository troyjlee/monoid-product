import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Cut grids and dyadic scales

The cut grid of the infix search (`lem:infix` in the paper), with no adversary
content: pure arithmetic about where the infix search is allowed to cut.

The search guesses a *scale* `ℓ = 2^t` for the length of the forbidden infix and
a *cut* inside it.  It cannot afford to try every cut, so it tries only the
multiples of `gridStep ℓ = max 1 (ℓ/4)`.  Two facts make that work:

* `exists_mem_cutGrid` — the grid meets every block of `gridStep ℓ` consecutive
  positions, and an infix of length in `[ℓ, 2ℓ]` offers at least that many
  legal cuts;
* `card_cutGrid_mul_le` — `|grid| · ℓ ≤ 16 n`, so the `√|grid|` of a square-root
  search over cuts cancels the `√ℓ` of a window of width `4ℓ`, leaving `√n`.

The second is stated multiplicatively, in `ℕ`, precisely because that is the
form that combines with square roots without a floor-heavy real division.
-/

namespace MonoidProduct

/-! ## The grid -/

/-- The spacing of the cut grid at scale `ℓ`.  The `max 1` is what makes the
smallest scale `ℓ = 2` legal. -/
def gridStep (ℓ : ℕ) : ℕ := max 1 (ℓ / 4)

lemma gridStep_pos (ℓ : ℕ) : 0 < gridStep ℓ := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)

lemma gridStep_le_self {ℓ : ℕ} (h : 1 ≤ ℓ) : gridStep ℓ ≤ ℓ :=
  max_le h (Nat.div_le_self ℓ 4)

lemma le_four_mul_gridStep (ℓ : ℕ) : ℓ ≤ 4 * gridStep ℓ + 3 := by
  have h : ℓ / 4 ≤ gridStep ℓ := le_max_right _ _
  have := Nat.div_add_mod ℓ 4
  have hmod : ℓ % 4 < 4 := Nat.mod_lt _ (by norm_num)
  omega

/-- At a legal scale the spacing fits inside the scale with room to spare: an
infix of length at least `ℓ` offers at least `gridStep ℓ` legal cuts. -/
lemma gridStep_le_sub_one {ℓ : ℕ} (h : 2 ≤ ℓ) : gridStep ℓ ≤ ℓ - 1 := by
  have hdm := Nat.div_add_mod ℓ 4
  have hmod : ℓ % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h4 : ℓ / 4 ≤ ℓ - 1 := by omega
  exact max_le (by omega) h4

/-- The cut grid at scale `ℓ`: the multiples of `gridStep ℓ` up to `n`. -/
def cutGrid (n ℓ : ℕ) : Finset ℕ :=
  (Finset.range (n / gridStep ℓ + 1)).image fun k => k * gridStep ℓ

lemma le_of_mem_cutGrid {n ℓ g : ℕ} (h : g ∈ cutGrid n ℓ) : g ≤ n := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
  rw [Finset.mem_range] at hk
  calc k * gridStep ℓ ≤ (n / gridStep ℓ) * gridStep ℓ :=
        Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 hk)
    _ ≤ n := Nat.div_mul_le_self _ _

lemma card_cutGrid_le (n ℓ : ℕ) : (cutGrid n ℓ).card ≤ n / gridStep ℓ + 1 :=
  le_trans (Finset.card_image_le) (le_of_eq (Finset.card_range _))

/-- **The grid meets every block of `gridStep ℓ` consecutive positions.** -/
lemma exists_mem_cutGrid {n ℓ s e : ℕ} (hse : s + gridStep ℓ ≤ e + 1)
    (hen : e ≤ n) : ∃ g ∈ cutGrid n ℓ, s ≤ g ∧ g ≤ e := by
  have hdpos : 0 < gridStep ℓ := gridStep_pos ℓ
  set d := gridStep ℓ with hd
  set k := (s + d - 1) / d with hk
  have hdm : d * k + (s + d - 1) % d = s + d - 1 := Nat.div_add_mod _ _
  have hmod : (s + d - 1) % d < d := Nat.mod_lt _ hdpos
  have hcomm : k * d = d * k := Nat.mul_comm k d
  obtain ⟨rr, hrr⟩ : ∃ rr, (s + d - 1) % d = rr := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, d * k = P := ⟨_, rfl⟩
  rw [hrr, hP] at hdm
  rw [hrr] at hmod
  rw [hP] at hcomm
  have hs : s ≤ k * d := by omega
  have he : k * d ≤ e := by omega
  refine ⟨k * d, ?_, hs, he⟩
  rw [cutGrid, Finset.mem_image]
  exact ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le
    ((Nat.le_div_iff_mul_le hdpos).2 (le_trans he hen))), rfl⟩

/-- **The grid is small compared to the scale.**  This is the multiplicative
statement, the one that combines with square roots. -/
lemma card_cutGrid_mul_le {n ℓ : ℕ} (h2 : 2 ≤ ℓ) (hln : ℓ ≤ n) :
    (cutGrid n ℓ).card * ℓ ≤ 16 * n := by
  have hdpos : 0 < gridStep ℓ := gridStep_pos ℓ
  have hld : ℓ ≤ 4 * gridStep ℓ + 3 := le_four_mul_gridStep ℓ
  have hdl : gridStep ℓ ≤ ℓ := gridStep_le_self (by omega)
  have hDd : (n / gridStep ℓ) * gridStep ℓ ≤ n := Nat.div_mul_le_self _ _
  have hDn : n / gridStep ℓ ≤ n := Nat.div_le_self _ _
  have hcard := card_cutGrid_le n ℓ
  obtain ⟨d, hd⟩ : ∃ d, gridStep ℓ = d := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, n / gridStep ℓ = D := ⟨_, rfl⟩
  rw [hd] at hld hdl
  rw [hD, hd] at hDd
  rw [hD] at hDn hcard
  calc (cutGrid n ℓ).card * ℓ ≤ (D + 1) * (4 * d + 3) := Nat.mul_le_mul hcard hld
    _ = 4 * (D * d) + 3 * D + 4 * d + 3 := by ring
    _ ≤ 16 * n := by
        have h4 : 4 * (D * d) ≤ 4 * n := Nat.mul_le_mul_left 4 hDd
        have h3 : 3 * D ≤ 3 * n := Nat.mul_le_mul_left 3 hDn
        have h2' : 4 * d ≤ 4 * n := Nat.mul_le_mul_left 4 (le_trans hdl hln)
        obtain ⟨P, hP⟩ : ∃ P, D * d = P := ⟨_, rfl⟩
        rw [hP] at h4 ⊢
        omega

/-! ## The dyadic scales -/

/-- The scales the infix search tries: `2, 4, 8, …` up to `n`. -/
def scales (n : ℕ) : Finset ℕ := (Finset.Icc 1 (Nat.log 2 n)).image fun t => 2 ^ t

lemma card_scales_le (n : ℕ) : (scales n).card ≤ Nat.log 2 n :=
  le_trans Finset.card_image_le (by simp [Nat.card_Icc])

lemma two_le_of_mem_scales {n ℓ : ℕ} (h : ℓ ∈ scales n) : 2 ≤ ℓ := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
  rw [Finset.mem_Icc] at ht
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht.1

lemma le_of_mem_scales {n ℓ : ℕ} (h : ℓ ∈ scales n) : ℓ ≤ n := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
  rw [Finset.mem_Icc] at ht
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at ht; omega
  · exact le_trans (Nat.pow_le_pow_right (by norm_num) ht.2)
      (Nat.pow_log_le_self 2 (by omega))

/-- **Every legal infix length has a scale.**  A witness of length `L` is caught
by the scale `2 ^ ⌊log₂ L⌋`. -/
lemma exists_mem_scales {n L : ℕ} (h2 : 2 ≤ L) (hLn : L ≤ n) :
    ∃ ℓ ∈ scales n, ℓ ≤ L ∧ L ≤ 2 * ℓ := by
  refine ⟨2 ^ Nat.log 2 L, Finset.mem_image.2 ⟨Nat.log 2 L, ?_, rfl⟩, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    exact ⟨Nat.log_pos (by norm_num) h2, Nat.log_mono_right hLn⟩
  · exact Nat.pow_log_le_self 2 (by omega)
  · have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) L
    rw [pow_succ] at this
    omega

end MonoidProduct
