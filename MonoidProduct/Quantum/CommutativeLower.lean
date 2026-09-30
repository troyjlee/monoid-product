import MonoidProduct.Width.Deletion
import MonoidProduct.Quantum.WidthApplications
import QuantumQueryComplexity.Quantum.LowerBound.MainBool
import QuantumQueryComplexity.Quantum.OneHotTransport

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The commutative lower bound (`thm:commutative-beta`, lower half)

For a finite commutative aperiodic monoid `M`, a finite alphabet `σ` with a letter map
`m : σ → M` and an identity symbol `s0`, and `1 ≤ n`, `1 ≤ β = breadth m`:

    √(n·min{n, β}) / 72  ≤  Q_{1/3}(x ↦ ∏ᵢ m(xᵢ))                (`commutative_qQuery_lower`).

Route: with `r = min{β, ⌊(n+1)/2⌋}` take an all-essential core word of length `r`
(`exists_all_essential_word`); the deletion promise of `Width/Deletion.lean` has adversary
value `θ = √(r(n−r+1))` (`sqrt_le_advPMOn_coreDeletion`); the Boolean adversary bound gives
`θ/36 ≤ Q_{1/3}` of the promise output, which is the free postprocessing `decide (· = p)` of
the product (`prod_isHigh`, `prod_isLow_ne`), so `θ/36 ≤ Q_{1/3}` of the total product
(`qQueryOn_postcomp_le`, `qQueryOn_comp_read_le_qQuery`); finally `n·min{n,β} ≤ 4r(n−r+1)`.

Also: the full alphabet `σ = M`, `m = id` (`commutative_qQuery_lower_total`, with
`one_le_breadth_id` for a nontrivial monoid), the `wordProd` form, the one-hot oracle
(`commutative_oneHotQQuery_lower`, constant `1/144`), and the sandwich with the existing
upper bound: `√(n·min{n,β})/72 ≤ Q_{1/3} ≤ min{n, 2^18·√(n·min{n,β})}`
(`commutative_qQuery_sandwich`), i.e. `Q_{1/3} = Θ(min{n, √(nβ)})`.
-/

namespace MonoidProduct

open QuantumQueryComplexity Finset

section Lower

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Fintype M] [DecidableEq M] [CommMonoid M]

/-- **The promise lower bound for a fixed all-essential core word**: `θ/36 ≤ Q_{1/3}`. -/
theorem qQuery_lower_of_core (m : σ → M) (s0 : σ) (hs0 : m s0 = 1) {r n : ℕ} (a : Fin r → σ)
    (hall : prodEss m a Finset.univ = Finset.univ) (hrn : r ≤ n) (hr1 : 1 ≤ r) :
    (1 / 36 : ℝ) * delTheta r n ≤ (qQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ) := by
  classical
  have ha : ∀ j, a j ≠ s0 := fun j h =>
    ne_one_of_mem_prodEss m a (by rw [hall]; exact Finset.mem_univ j) (by rw [h, hs0])
  have : Nonempty M := ⟨1⟩
  have hdet := separates_of_injective (delRead_injective s0 a ha) (delOut s0 a (n := n))
  have hpar := mul_advPMOn_le_qQueryOn_of_error_third (read := delRead s0 a (n := n))
    (f := delOut s0 a) hdet
  -- the promise output is a Boolean test on the product
  have hout : delOut s0 a (n := n)
      = fun z => decide (∏ i, m (delRead s0 a z i) = ∏ j, m (a j)) := by
    funext z
    cases z with
    | inl x => simp [delOut, delRead, prod_isHigh s0 a m hs0 x.2]
    | inr y => simp [delOut, delRead, prod_isLow_ne s0 a m hs0 hall y.2]
  have hne1 : (QueryCounts (delRead s0 a (n := n))
      (fun z => ∏ i, m (delRead s0 a z i)) (1 / 3)).Nonempty :=
    queryCounts_nonempty (fun z z' h => by simp only [h]) (by norm_num)
  have hpost := qQueryOn_postcomp_le (read := delRead s0 a (n := n))
    (f := fun z => ∏ i, m (delRead s0 a z i)) (ε := 1 / 3)
    (fun v : M => decide (v = ∏ j, m (a j))) hne1
  have hne2 : (QueryCounts (X := Fin n → σ) id (fun x => ∏ i, m (x i)) (1 / 3)).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [show x = y from h]) (by norm_num)
  have hres := qQueryOn_comp_read_le_qQuery (delRead s0 a (n := n)) (fun x => ∏ i, m (x i)) hne2
  calc (1 / 36 : ℝ) * delTheta r n
      ≤ (1 / 36) * advPMOn (delRead s0 a (n := n)) (delOut s0 a) :=
        mul_le_mul_of_nonneg_left (sqrt_le_advPMOn_coreDeletion s0 a ha hrn hr1) (by norm_num)
    _ ≤ (qQueryOn (delRead s0 a (n := n)) (delOut s0 a) (1 / 3) : ℝ) := hpar
    _ = (qQueryOn (delRead s0 a (n := n))
          (fun z => decide (∏ i, m (delRead s0 a z i) = ∏ j, m (a j))) (1 / 3) : ℝ) := by
        rw [hout]
    _ ≤ (qQueryOn (delRead s0 a (n := n)) (fun z => ∏ i, m (delRead s0 a z i)) (1 / 3) : ℝ) := by
        exact_mod_cast hpost
    _ ≤ _ := by exact_mod_cast hres

/-! ## The arithmetic -/

/-- `√(n·min{n,b}) ≤ 2·√(r(n−r+1))` for `r = min{b, ⌊(n+1)/2⌋}`. -/
lemma sqrt_nmin_le_two_delTheta {n b : ℕ} (_hn : 1 ≤ n) (hb : 1 ≤ b) :
    Real.sqrt ((n * min n b : ℕ) : ℝ) ≤ 2 * delTheta (min b ((n + 1) / 2)) n := by
  have h1 : min n b ≤ 2 * min b ((n + 1) / 2) := by omega
  have h2 : n ≤ 2 * (n - min b ((n + 1) / 2) + 1) := by omega
  have hnat : n * min n b ≤ 4 * (min b ((n + 1) / 2) * (n - min b ((n + 1) / 2) + 1)) := by
    calc n * min n b ≤ (2 * (n - min b ((n + 1) / 2) + 1)) * (2 * min b ((n + 1) / 2)) :=
          Nat.mul_le_mul h2 h1
      _ = 4 * (min b ((n + 1) / 2) * (n - min b ((n + 1) / 2) + 1)) := by ring
  unfold delTheta
  have h4 : ∀ Y : ℝ, 0 ≤ Y → (2 : ℝ) * Real.sqrt Y = Real.sqrt (4 * Y) := by
    intro Y hY
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [h4 _ (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  exact_mod_cast hnat

/-! ## The theorem -/

variable [IsAperiodicMonoid M]

/-- **The commutative lower bound** (`thm:commutative-beta`, lower half): for every finite
commutative aperiodic monoid, alphabet `σ` with letter map `m` and identity symbol `s0`,
`√(n·min{n, β})/72 ≤ Q_{1/3}(∏ᵢ m(xᵢ))` whenever `n, β ≥ 1`. -/
theorem commutative_qQuery_lower (m : σ → M) (s0 : σ) (hs0 : m s0 = 1) {n : ℕ} (hn : 1 ≤ n)
    (hb : 1 ≤ breadth m) :
    Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 72
      ≤ (qQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ) := by
  set r := min (breadth m) ((n + 1) / 2) with hr
  have hrb : r ≤ breadth m := min_le_left _ _
  have hrn : r ≤ n := by omega
  have hr1 : 1 ≤ r := by omega
  obtain ⟨a, hall⟩ := exists_all_essential_word m hrb
  have h := qQuery_lower_of_core m s0 hs0 a hall hrn hr1
  have h2 := sqrt_nmin_le_two_delTheta hn hb
  rw [← hr] at h2
  calc Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 72
      = (1 / 36) * (Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 2) := by ring
    _ ≤ (1 / 36) * delTheta r n := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        linarith
    _ ≤ _ := h

/-- A nontrivial monoid has breadth at least `1` over its full alphabet. -/
lemma one_le_breadth_id [Nontrivial M] : 1 ≤ breadth (id : M → M) := by
  by_contra h
  have h0 : breadth (id : M → M) = 0 := by omega
  have hb : IsBreadthBound (id : M → M) 0 := by
    have := isBreadthBound_breadth (exists_isBreadthBound (id : M → M))
    rwa [h0] at this
  obtain ⟨u, v, huv⟩ := exists_pair_ne M
  have hone : ∀ g : M, g = 1 := fun g => by
    have := wordProd_eq_one_of_isBreadthBound_zero hb ![g]
    rw [wordProd_eq_prod] at this
    simpa using this
  exact huv ((hone u).trans (hone v).symm)

/-- **The full alphabet**: `σ = M`, every element a letter. -/
theorem commutative_qQuery_lower_total [Nontrivial M] {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt ((n * min n (breadth (id : M → M)) : ℕ) : ℝ) / 72
      ≤ (qQuery (fun x : Fin n → M => ∏ i, x i) (1 / 3) : ℝ) :=
  commutative_qQuery_lower (id : M → M) 1 rfl hn one_le_breadth_id

/-- The full alphabet, in the `wordProd` form of the other paper-facing endpoints. -/
theorem commutative_qQuery_lower_wordProd [Nontrivial M] {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt ((n * min n (breadth (id : M → M)) : ℕ) : ℝ) / 72
      ≤ (qQuery (fun x : Fin n → M => wordProd (id : M → M) x) (1 / 3) : ℝ) := by
  have e : (fun x : Fin n → M => wordProd (id : M → M) x) = fun x => ∏ i, x i :=
    funext fun x => wordProd_eq_prod id x
  rw [e]
  exact commutative_qQuery_lower_total hn

/-- **The one-hot oracle**: the safe constant `1/144`. -/
theorem commutative_oneHotQQuery_lower (m : σ → M) (s0 : σ) (hs0 : m s0 = 1) {n : ℕ}
    (hn : 1 ≤ n) (hb : 1 ≤ breadth m) :
    Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 144
      ≤ (oneHotQQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ) := by
  have h := half_le_oneHotQQueryOn_of_le_qQueryOn (read := (id : (Fin n → σ) → Fin n → σ))
    (f := fun x : Fin n → σ => ∏ i, m (x i)) (fun x y h => by rw [show x = y from h])
    (by norm_num) (commutative_qQuery_lower m s0 hs0 hn hb)
  calc Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 144
      = Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 72 / 2 := by ring
    _ ≤ _ := h

/-- **The sandwich** (`thm:commutative-beta`): `√(n·min{n,β})/72 ≤ Q_{1/3} ≤ min{n,
2^18·√(n·min{n,β})}` for `n, β ≥ 1`; that is, `Q_{1/3}(Prod_{M,G,n}) = Θ(min{n, √(nβ)})`. -/
theorem commutative_qQuery_sandwich (m : σ → M) (s0 : σ) (hs0 : m s0 = 1) {n : ℕ} (hn : 1 ≤ n)
    (hb : 1 ≤ breadth m) :
    Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ) / 72
        ≤ (qQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ∧ (qQuery (fun x : Fin n → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n * min n (breadth m) : ℕ) : ℝ)) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨commutative_qQuery_lower m s0 hs0 hn hb, le_min ?_ ?_⟩
  · have := prodFun_qQuery_upper_length (ι := Fin n) m
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  · have hB : 0 < min n (breadth m) := lt_min hn hb
    have hw : ∀ (x : Fin n → σ) (T : Finset (Fin n)), (prodEss m x T).card ≤ min n (breadth m) :=
      fun x T => le_min ((Finset.card_le_card (prodEss_subset' m x T)).trans
        ((Finset.card_le_univ T).trans_eq (Fintype.card_fin n)))
        (card_prodEss_le_breadth m x T)
    have h := width_qQuery_upper (ι := Fin n) m hB hw
    rw [Fintype.card_fin] at h
    have hcast : ((n * min n (breadth m) : ℕ) : ℝ) = (n : ℝ) * ((min n (breadth m) : ℕ) : ℝ) :=
      Nat.cast_mul _ _
    have hX : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * ((min n (breadth m) : ℕ) : ℝ)) := by
      refine Real.one_le_sqrt.2 ?_
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h2 : (1 : ℝ) ≤ ((min n (breadth m) : ℕ) : ℝ) := by exact_mod_cast hB
      nlinarith
    rw [hcast]
    refine h.trans ?_
    rw [uniformExtractionConstant]
    nlinarith

end Lower

end MonoidProduct
