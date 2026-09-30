import MonoidProduct.Quantum.OrderedLogApplications
import MonoidProduct.Ordered.Verify

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The core algorithms with every output certified

The verification wrapper `exists_verified_of_core` applied to the ordered-product core
algorithms.  For every breadth bound `b` and length `n` there is a quantum algorithm with

    Q ≤ min { n, X } + b,          X the product bound (exponent `5b/2`, or the paper's form),

such that **every** output of positive probability is truthful for the padded word, has at
most `b` positions, all of them original, and a good record (the word's product) is returned
with probability at least `9/10`.  The `+ b` is the exact cost of the verification; the
product constants `2^27` and `2^17` are untouched.  The degenerate cases: `b = 0` uses the
zero-query constant algorithm announcing the empty record; `n ≤ b` and the lengths below the
numerics use the exact read-all algorithm, wrapped.
-/

namespace MonoidProduct

open QuantumQueryComplexity Finset

/-! ## The constant algorithm's outcomes -/

lemma constAlg_prob {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [DecidableEq O] (c : O) (a : ι → σ) (t : ℕ) (o : O) :
    (constAlg ι σ c).prob a t o = if c = o then 1 else 0 := by
  have h := (constAlg ι σ c).state_isQState a t
  rw [QAlg.prob, qProb]
  have hr : ∀ p, (constAlg ι σ c).readout p = c := fun _ => rfl
  simp only [hr]
  rw [Finset.sum_ite_irrel]
  split_ifs
  · exact h
  · simp

section Verified

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M)

open Classical in
/-- **Breadth `0`**: the empty record, announced without queries, is good on every branch. -/
theorem exists_verified_core_zero (hb : IsBreadthBound letter 0) (n : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W),
      (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x 0 K →
        K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ 0 ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter 0 x), B.prob x 0 K := by
  have hgood : ∀ x : Fin n → σ, GoodRec letter 0 x (emptyRec : Record (2 ^ logLen n) (Option σ)) := by
    intro x
    refine ⟨truthful_emptyRec _, by rw [supp_emptyRec, Finset.card_empty], ?_⟩
    rw [Record.prod_of_truthful _ (truthful_emptyRec (pad (L := logLen n) x)), supp_emptyRec,
      subwordProd_empty]
    obtain ⟨D, hD, hcore⟩ := hb n x
    unfold IsCore at hcore
    rw [← hcore, Finset.card_eq_zero.1 (Nat.le_zero.1 hD), subwordProd_empty]
  refine ⟨Unit, inferInstance, inferInstance, constAlg (Fin n) σ emptyRec, fun x K hK => ?_,
    fun x => ?_⟩
  · rw [constAlg_prob] at hK
    have hKe : (emptyRec : Record (2 ^ logLen n) (Option σ)) = K := by
      by_contra hne
      rw [if_neg hne] at hK
      exact lt_irrefl _ hK
    subst hKe
    exact ⟨truthful_emptyRec _, by rw [supp_emptyRec, Finset.card_empty], fun i hi => by
      rw [supp_emptyRec] at hi; exact absurd hi (Finset.notMem_empty _)⟩
  · simp only [constAlg_prob]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgood x⟩)]
    norm_num

variable (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
include hst hb

open Classical in
/-- **The wrapped algorithm from a bound**: either reading everything is within `X`, or some
core algorithm is; the verified algorithm then costs at most `min {n, X} + b`. -/
theorem exists_verified_core_of (hb1 : 1 ≤ b) {n : ℕ} {X : ℝ}
    (hX : (n : ℝ) ≤ X ∨ ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ X ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ min (n : ℝ) X + b
      ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x Q K →
          K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  -- the read-all fallback, wrapped
  have hread : ∀ (hnX : (n : ℝ) ≤ X), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ min (n : ℝ) X + b
      ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x Q K →
          K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
    intro hnX
    obtain ⟨W, hW, hW', B, hgood⟩ := exists_exact_core_alg letter hst hb hb1 (le_two_pow_logLen n)
    letI := hW; letI := hW'
    obtain ⟨W', hW'1, hW'2, B', hall, hgood'⟩ := exists_verified_of_core letter n b B n hgood
    refine ⟨W', hW'1, hW'2, B', n + b, ?_, hall, hgood'⟩
    rw [min_eq_left hnX]
    push_cast
    exact le_rfl
  rcases hX with hnX | ⟨W, hW, hW', B, Q, hQ, hgood⟩
  · exact hread hnX
  · by_cases hXn : X ≤ n
    · letI := hW; letI := hW'
      obtain ⟨W', hW'1, hW'2, B', hall, hgood'⟩ := exists_verified_of_core letter n b B Q hgood
      refine ⟨W', hW'1, hW'2, B', Q + b, ?_, hall, hgood'⟩
      rw [min_eq_right hXn]
      push_cast
      linarith
    · exact hread (le_of_not_ge hXn)

/-! ## The endpoints -/

open Classical in
/-- **The certified core algorithm, exponent `5b/2`**: for every `b` and `n`, at most
`min {n, (2^27·b)^b·√n·L_n^{5b/2}} + b` queries; every output is a truthful record of at most
`b` original positions; a good record with probability at least `9/10`. -/
theorem ordered_exists_verified_core_alg_five_halves (n : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ min (n : ℝ) ((2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n
          * orderedLogFactor (logLen n) ^ b) + b
      ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x Q K →
          K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · obtain ⟨W, hW, hW', B, hall, hgood⟩ := exists_verified_core_zero letter hb n
    refine ⟨W, hW, hW', B, 0, ?_, hall, hgood⟩
    have hF := orderedLogFactor_nonneg (logLen n)
    simp only [Nat.cast_zero, add_zero]
    exact le_min (by positivity) (by positivity)
  · refine exists_verified_core_of letter hst hb hb1 ?_
    by_cases hbn : b < n
    · exact Or.inr (ordered_exists_core_alg_five_halves letter hst hb hb1 hbn)
    · left
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · have hF := orderedLogFactor_nonneg (logLen 0)
        simp only [Nat.cast_zero]
        positivity
      · have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
        have hnb : (n : ℝ) ≤ b := by exact_mod_cast (not_lt.1 hbn)
        exact le_orderedBound' hn1 hb1 (by linarith)
          (one_le_pow₀ (one_le_orderedLogFactor (one_le_logLen hn1)))

end Verified

/-! ## The quasipolynomial form -/

lemma quasipolyBound_nonneg (b n : ℕ) : 0 ≤ quasipolyBound b n := by
  unfold quasipolyBound quasipolyConstant
  have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast Nat.zero_le b
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)

/-- Reading everything is within the discrete bound when `n ≤ 3` or `n ≤ b`. -/
lemma le_logRankBound {n b : ℕ} (hn1 : 1 ≤ n) (hb1 : 1 ≤ b) (hnb : n ≤ 3 ∨ n ≤ b) :
    (n : ℝ) ≤ logRankBound b n := by
  unfold logRankBound
  have hY1 := one_le_logRankBase (b := b) hn1
  have hL' : (1 : ℝ) ≤ logLen n := by exact_mod_cast one_le_logLen hn1
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hY2 : 2 ^ 15 * ((b : ℝ) + 2) ≤ 2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL')
  have hsn : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hsY : Real.sqrt n ≤ 2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4 := by
    rcases hnb with h | h
    · have : (n : ℝ) ≤ 3 := by exact_mod_cast h
      linarith
    · have : (n : ℝ) ≤ b := by exact_mod_cast h
      linarith
  have hY' : 2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4
      ≤ (2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4) ^ (Nat.clog 2 (b + 2) + 2) :=
    le_self_pow₀ hY1 (by omega)
  calc (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt (by positivity)).symm
    _ ≤ (2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4) * Real.sqrt n :=
        mul_le_mul_of_nonneg_right hsY (Real.sqrt_nonneg _)
    _ ≤ (2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4) ^ (Nat.clog 2 (b + 2) + 2)
          * Real.sqrt n := mul_le_mul_of_nonneg_right hY' (Real.sqrt_nonneg _)

section VerifiedQuasipoly

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
include hst hb

open Classical in
/-- **The certified core algorithm within the paper's bound**: for every `b` and `n`, at most
`min {n, √(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)}} + b` queries with `C = 2^17`; every output is
a truthful record of at most `b` original positions; a good record with probability at least
`9/10`. -/
theorem ordered_exists_verified_core_alg_quasipoly (n : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ min (n : ℝ) (quasipolyBound b n) + b
      ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x Q K →
          K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · obtain ⟨W, hW, hW', B, hall, hgood⟩ := exists_verified_core_zero letter hb n
    refine ⟨W, hW, hW', B, 0, ?_, hall, hgood⟩
    simp only [Nat.cast_zero, add_zero]
    exact le_min (by positivity) (quasipolyBound_nonneg 0 n)
  · refine exists_verified_core_of letter hst hb hb1 ?_
    by_cases hbn : b < n
    · exact Or.inr (ordered_exists_core_alg_quasipoly letter hst hb hb1 hbn)
    · left
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · simp only [Nat.cast_zero]
        exact quasipolyBound_nonneg b 0
      · exact (le_logRankBound hn1 hb1 (Or.inr (not_lt.1 hbn))).trans
          (logRankBound_le_quasipolyBound b n)

end VerifiedQuasipoly

end MonoidProduct
