import MonoidProduct.Quantum.OrderedVerified

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# All-branch truthfulness within the displayed bound
(`thm:ordered-beta-log-product`, `thm:ordered-beta-product`)

`monoid.tex`, `thm:ordered-beta-log-product`: *"The algorithm also returns a
preserving subword of at most `β` positions, with success probability at least `9/10`. Its
returned record is truthful on every branch. The constant is independent of `M`, `G`, and
`β`."*

`ordered_exists_verified_core_alg_quasipoly` (`Quantum/OrderedVerified.lean`) gives all-branch
truthfulness at cost `min {n, X} + b`, the `+ b` being the verification wrapper.  Here the
`+ b` is absorbed into the displayed bound:

* the **truthful read-all algorithm** (`exists_truthful_readAll`) reads every letter and
  outputs, deterministically, the verified compression of the full record: `n` queries, every
  branch truthful with at most `b` original positions, and always good;
* `exists_truthful_of_absorb`: if `X + b ≤ X'` whenever reading everything exceeds `X'`,
  then the verified algorithm (when `X' < n`) or the read-all algorithm (when `n ≤ X'`)
  costs at most `min {n, X'}`;
* for the paper's form, doubling the constant `2^17 ↦ 2^18` gives `X + b ≤ 2X ≤ X'`
  (`quasipolyBound_add_le`); for the exponent-`5b/2` form, `2^27 ↦ 2^28`
  (`fiveHalves_add_le`).

The endpoints `ordered_truthful_core_alg_quasipoly` and `ordered_truthful_core_alg_five_halves`
state, with the constant quantified before `M`, `G`, `b` and `n` and in the statement style of
`FollowupAcceptance.acceptance_verified_core_quasipoly`: an algorithm with at most
`min {n, √(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)}}` queries, every output of positive probability
a truthful record of at most `b` positions, all original, and a good (product-preserving)
record with probability at least `9/10`.
-/

namespace MonoidProduct

open QuantumQueryComplexity Finset

/-- An outcome of an algorithm that has probability at least one is its only outcome of
positive probability. -/
lemma qalg_eq_of_one_le_prob {ι σ O W : Type} [Fintype σ] [DecidableEq σ] [Fintype ι]
    [DecidableEq ι] [Fintype O] [DecidableEq O] [Fintype W] [DecidableEq W] (A : QAlg ι σ O W)
    (a : ι → σ) (t : ℕ)
    {o₀ o : O} (h₀ : 1 ≤ A.prob a t o₀) (h : 0 < A.prob a t o) : o = o₀ := by
  by_contra hne
  have hsub : ({o₀, o} : Finset O) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun o' _ _ => A.prob_nonneg a t o')
  have hsum : ∑ o', A.prob a t o' = 1 := by
    show (∑ o', qProb A.readout (A.state a t) o') = 1
    rw [sum_qProb, A.state_isQState]
  rw [Finset.sum_pair (Ne.symm hne), hsum] at hle
  linarith

section Truthful

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) {b : ℕ} (hb : IsBreadthBound letter b)
include hb

open Classical in
/-- **The truthful read-all algorithm**: `n` queries; the output is a deterministic function
of the input, the verified compression of the full record, so every output of positive
probability is truthful with at most `b` original positions, and it is always good. -/
theorem exists_truthful_readAll (n : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W),
      (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x n K →
        K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x n K := by
  have hn := le_two_pow_logLen n
  have hb' : IsBreadthBound (letterOpt letter) b := isBreadthBound_letterOpt letter hb
  let full : (Fin n → σ) → Record (2 ^ logLen n) (Option σ) :=
    fun x j => some (pad (L := logLen n) x j)
  have hfull : ∀ x, (full x).Truthful (pad (L := logLen n) x) :=
    fun x i s h => Option.some.inj h
  have hsupp : ∀ x, (full x).supp = Finset.univ := fun x => by
    ext i; simp [Record.supp, mem_optSupp, full]
  let f : (Fin n → σ) → Record (2 ^ logLen n) (Option σ) := fun x =>
    Record.compress (letterOpt letter) b (full x)
  have hgood : ∀ x, GoodRec letter b x (f x) := fun x =>
    ⟨Record.truthful_compress (letterOpt letter) (hfull x) b,
      (Record.compress_spec (letterOpt letter) hb' _).2.1, by
        change (Record.compress (letterOpt letter) b (full x)).prod (letterOpt letter) = _
        rw [(Record.compress_spec (letterOpt letter) hb' _).2.2,
          Record.prod_of_truthful (letterOpt letter) (hfull x), hsupp x, subwordProd_univ,
          wordProd_pad letter hn]⟩
  let g : (Fin n → σ) → Record (2 ^ logLen n) (Option σ) := fun x => verified n b x (f x)
  obtain ⟨A, hA⟩ := exists_computesWithErrorOn (read := (id : (Fin n → σ) → Fin n → σ))
    (f := g) (fun x y h => congrArg g h) (le_refl (0 : ℝ))
  rw [Fintype.card_fin] at hA
  have h1 : ∀ x, 1 ≤ A.prob x n (g x) := fun x => by
    have := hA x; simp only [id, sub_zero] at this; exact this
  refine ⟨_, inferInstance, inferInstance, A, fun x K hK => ?_, fun x => ?_⟩
  · rw [qalg_eq_of_one_le_prob A x n (h1 x) hK]
    exact ⟨verified_truthful n b x _, verified_card_le n b x _, verified_supp_lt n b x _⟩
  · calc (9 / 10 : ℝ) ≤ 1 := by norm_num
      _ ≤ A.prob x n (g x) := h1 x
      _ ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), A.prob x n K :=
          Finset.single_le_sum (f := fun K => A.prob x n K) (fun K _ => A.prob_nonneg x n K)
            (Finset.mem_filter.2 ⟨Finset.mem_univ _,
              verified_goodRec letter n b x (f x) (hgood x)⟩)

open Classical in
/-- **Absorbing the verification cost.**  From a verified algorithm within `min {n, X} + b`
and a bound `X'` with `X + b ≤ X'` whenever `X' < n`, an algorithm within `min {n, X'}` with
the same all-branch guarantee (the read-all algorithm when `n ≤ X'`). -/
theorem exists_truthful_of_absorb {n : ℕ} {X X' : ℝ}
    (habs : X' < n → X + b ≤ X')
    (hver : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ min (n : ℝ) X + b
      ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x Q K →
          K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ min (n : ℝ) X'
      ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x Q K →
          K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  by_cases hnX : (n : ℝ) ≤ X'
  · obtain ⟨W, hW, hW', B, hall, hgood⟩ := exists_truthful_readAll letter hb n
    exact ⟨W, hW, hW', B, n, by rw [min_eq_left hnX], hall, hgood⟩
  · push Not at hnX
    obtain ⟨W, hW, hW', B, Q, hQ, hall, hgood⟩ := hver
    refine ⟨W, hW, hW', B, Q, ?_, hall, hgood⟩
    have h1 := habs hnX
    have h2 : min (n : ℝ) X ≤ X := min_le_right _ _
    rw [min_eq_right hnX.le]
    linarith

end Truthful

/-! ## The bound comparisons -/

/-- The paper's bound with an arbitrary constant. -/
noncomputable def truthfulQuasipolyBound (C : ℝ) (b n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) + 1)
    * (C * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ (C * Real.log ((b : ℝ) + 2))

/-- **Doubling the constant absorbs `+ b`**: for `n ≥ 1`,
`quasipolyBound b n + b ≤` the paper's bound with constant `2·2^17`. -/
theorem quasipolyBound_add_le {b n : ℕ} (hn : 1 ≤ n) :
    quasipolyBound b n + b ≤ truthfulQuasipolyBound (2 * quasipolyConstant) b n := by
  unfold quasipolyBound truthfulQuasipolyBound
  set C := quasipolyConstant with hCdef
  have hC : C = 2 ^ 17 := rfl
  have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast Nat.zero_le b
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ : 1 / 2 ≤ Real.log ((n : ℝ) + 2) :=
    half_le_log_two.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlb : Real.log 2 ≤ Real.log ((b : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hl2 := half_le_log_two
  set Y := C * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2) with hY
  set e := C * Real.log ((b : ℝ) + 2) with he
  have hY1 : (b : ℝ) + 1 ≤ Y := by
    rw [hY, hC]
    nlinarith [mul_le_mul_of_nonneg_left hℓ (by positivity : (0 : ℝ) ≤ 2 ^ 17 * ((b : ℝ) + 2))]
  have hYge : (1 : ℝ) ≤ Y := by linarith
  have he1 : (1 : ℝ) ≤ e := by rw [he, hC]; nlinarith
  have hs : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
  -- `Y ≤ Y^e` and `2·Y^e ≤ (2Y)^{2e}`
  have hYe : Y ≤ Y ^ e := by
    calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
      _ ≤ Y ^ e := Real.rpow_le_rpow_of_exponent_le hYge he1
  have h2e : (2 : ℝ) ≤ 2 ^ e := by
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ 2 ^ e := Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
  have hdouble : 2 * Y ^ e ≤ (2 * C * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2))
      ^ (2 * C * Real.log ((b : ℝ) + 2)) := by
    have hbase : 2 * C * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2) = 2 * Y := by rw [hY]; ring
    have hexp : 2 * C * Real.log ((b : ℝ) + 2) = 2 * e := by rw [he]; ring
    rw [hbase, hexp]
    have hYpos : (0 : ℝ) ≤ Y ^ e := Real.rpow_nonneg (by linarith) e
    calc 2 * Y ^ e ≤ 2 ^ e * Y ^ e := mul_le_mul_of_nonneg_right h2e hYpos
      _ = (2 * Y) ^ e := (Real.mul_rpow (by norm_num) (by linarith)).symm
      _ ≤ (2 * Y) ^ (2 * e) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hYe0 : (0 : ℝ) ≤ Y ^ e := Real.rpow_nonneg (by linarith) e
  have hsn : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  calc Real.sqrt ((n : ℝ) + 1) * Y ^ e + b
      ≤ Real.sqrt ((n : ℝ) + 1) * Y ^ e + Real.sqrt ((n : ℝ) + 1) * Y ^ e := by
        have : (b : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) * Y ^ e := by nlinarith
        linarith
    _ = Real.sqrt ((n : ℝ) + 1) * (2 * Y ^ e) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdouble hsn

/-- **Doubling the constant absorbs `+ b`**, exponent `5b/2`: for `n ≥ 1`,
`(2^27 b)^b √n F^b + b ≤ (2^28 b)^b √n F^b`. -/
theorem fiveHalves_add_le {b n : ℕ} (hn : 1 ≤ n) :
    (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * orderedLogFactor (logLen n) ^ b + b
      ≤ (2 ^ 28 * (b : ℝ)) ^ b * Real.sqrt n * orderedLogFactor (logLen n) ^ b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · simp
  have hF : 1 ≤ orderedLogFactor (logLen n) ^ b :=
    one_le_pow₀ (one_le_orderedLogFactor (one_le_logLen hn))
  have hs : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; exact_mod_cast hn
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  set P := (2 ^ 27 * (b : ℝ)) ^ b with hP
  have hP1 : (b : ℝ) ≤ P := by
    calc (b : ℝ) ≤ 2 ^ 27 * b := by nlinarith
      _ = (2 ^ 27 * (b : ℝ)) ^ 1 := (pow_one _).symm
      _ ≤ P := pow_le_pow_right₀ (by nlinarith) hb1
  have h2 : (2 ^ 28 * (b : ℝ)) ^ b = 2 ^ b * P := by
    rw [hP, ← mul_pow]; ring_nf
  have h2b : (2 : ℝ) ≤ 2 ^ b := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hb1
  have hSF : 1 ≤ Real.sqrt n * orderedLogFactor (logLen n) ^ b := by nlinarith
  rw [h2]
  have hP0 : 0 ≤ P := by linarith
  have hX : (b : ℝ) ≤ P * Real.sqrt n * orderedLogFactor (logLen n) ^ b := by
    rw [mul_assoc]; nlinarith
  have : 2 * (P * Real.sqrt n * orderedLogFactor (logLen n) ^ b)
      ≤ 2 ^ b * P * Real.sqrt n * orderedLogFactor (logLen n) ^ b := by
    have hX0 : 0 ≤ P * Real.sqrt n * orderedLogFactor (logLen n) ^ b := by linarith
    nlinarith
  linarith

/-! ## The endpoints -/

section Endpoints

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
include hst hb

open Classical in
/-- **`thm:ordered-beta-log-product`, algorithmic form within the displayed bound**: at most
`min {n, √(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)}}` queries with `C = 2^18`; every output of
positive probability is a truthful record of at most `b` original positions; a good record
with probability at least `9/10`. -/
theorem ordered_truthful_quasipoly_of (n : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ min (n : ℝ) (truthfulQuasipolyBound (2 * quasipolyConstant) b n)
      ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x Q K →
          K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  refine exists_truthful_of_absorb letter hb (X := quasipolyBound b n) (fun hlt => ?_)
    (ordered_exists_verified_core_alg_quasipoly letter hst hb n)
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    have : 0 ≤ truthfulQuasipolyBound (2 * quasipolyConstant) b 0 := by
      unfold truthfulQuasipolyBound quasipolyConstant
      simp only [Nat.cast_zero, zero_add]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by
        have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity) _)
    simp only [Nat.cast_zero] at hlt
    linarith
  exact quasipolyBound_add_le hn

open Classical in
/-- **`thm:ordered-beta-product`, algorithmic form within the displayed bound**: at most
`min {n, (2^28 b)^b·√n·L_n^{5b/2}}` queries; every output of positive probability is a
truthful record of at most `b` original positions; a good record with probability at
least `9/10`. -/
theorem ordered_truthful_five_halves_of (n : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ min (n : ℝ) ((2 ^ 28 * (b : ℝ)) ^ b * Real.sqrt n
          * orderedLogFactor (logLen n) ^ b)
      ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ logLen n) (Option σ)), 0 < B.prob x Q K →
          K.Truthful (pad (L := logLen n) x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  refine exists_truthful_of_absorb letter hb
    (X := (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * orderedLogFactor (logLen n) ^ b)
    (fun hlt => ?_) (ordered_exists_verified_core_alg_five_halves letter hst hb n)
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_mul, lt_self_iff_false] at hlt
  exact fiveHalves_add_le hn

end Endpoints

/-! ## Statement pins in the style of `FollowupAcceptance.acceptance_verified_core_quasipoly` -/

open Classical in
/-- **`thm:ordered-beta-log-product`, all-branch truthfulness within the displayed bound.**
One absolute constant `C` (`= 2^18`), chosen before the monoid, the letters, `b` and `n`:
an algorithm with at most `min {n, √(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)}}` queries whose
**every** output of positive probability is a truthful record of at most `b` original
positions, and which returns a product-preserving record with probability at least `9/10`. -/
theorem ordered_truthful_core_alg_quasipoly :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → ∀ b : ℕ, IsBreadthBound letter b → ∀ n : ℕ,
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
          (B : QAlg (Fin n) σ (Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)) W) (Q : ℕ),
          (Q : ℝ) ≤ min (n : ℝ) (Real.sqrt ((n : ℝ) + 1)
              * (C * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ (C * Real.log ((b : ℝ) + 2)))
          ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)),
              0 < B.prob x Q K →
                K.Truthful (pad x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
          ∧ ∀ x : Fin n → σ,
              9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K :=
  ⟨2 * quasipolyConstant, by unfold quasipolyConstant; norm_num,
    fun letter hst _b hb n => ordered_truthful_quasipoly_of letter hst hb n⟩

open Classical in
/-- **`thm:ordered-beta-product`, all-branch truthfulness within the displayed bound**
(exponent `5b/2`, constant `2^28`). -/
theorem ordered_truthful_core_alg_five_halves :
    ∃ C : ℝ, C = 2 ^ 28 ∧
      ∀ {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
        (letter : σ → M), IsStableOrder M → ∀ b : ℕ, IsBreadthBound letter b → ∀ n : ℕ,
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
          (B : QAlg (Fin n) σ (Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)) W) (Q : ℕ),
          (Q : ℝ) ≤ min (n : ℝ) ((C * b) ^ b * Real.sqrt n
              * orderedLogFactor (Nat.clog 2 (n + 1)) ^ b)
          ∧ (∀ (x : Fin n → σ) (K : Record (2 ^ Nat.clog 2 (n + 1)) (Option σ)),
              0 < B.prob x Q K →
                K.Truthful (pad x) ∧ K.supp.card ≤ b ∧ ∀ i ∈ K.supp, (i : ℕ) < n)
          ∧ ∀ x : Fin n → σ,
              9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K :=
  ⟨2 ^ 28, rfl, fun letter hst _b hb n => ordered_truthful_five_halves_of letter hst hb n⟩

end MonoidProduct
