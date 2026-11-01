import MonoidProduct.Quantum.OrderedApplications

set_option linter.style.header false

/-!
# A short subword dominating almost all samples (`lem:beta-sampling`)

The paper's `lem:beta-sampling` in its displayed form, assembled from the seeded merger
(`Ordered/MergeSeeded.lean`) at the standard parameters `Pstd` of
`Quantum/OrderedApplications.lean`.

The ambient length is `N = 2^L` with `L ≥ 1`, so the paper's `L = 1 + ⌈log₂ N⌉` is `L + 1`
here.  A finite seed `ω`, drawn from a weight `ν`, specifies a truthful record `cand ω x` of
the input `x`; the paper's law `μ` of `U_ω(x)` is the pushforward `pushW ν (cand · x)`, and
every `cand ω` has a dual of cost `T`.  For `1 ≤ h ≤ 2^L` put `(R, k) = Pstd b L h`:

  `R = ⌈log₂(400·2^L·h)⌉`,  `k = 2h·ℓ`,  `ℓ = ⌈log₂(400·2^L·b·(9+2L))⌉`.

The seed `θ` (`BetaSeed`) fills each of the `k` proposal slots of each of the `2b` draws of
each of the `R` rounds with an independent seed `ω`, and `K_θ(x)` (`betaSampleK`) is the
merger's compressed output on the candidates `cand (θ ρ i t) x`.  Then
(`beta_sampling_explicit`):

* every `K_θ(x)` is a truthful record of at most `b` positions;
* every `K_θ` has a dual of cost `768·b·T·√h·(L+1)^{3/2}`;
* for every input `x`, with probability at most `1/(100·2^L)` over `θ` the candidate mass
  `Pr_{U∼μ}{p(U) ≰ p(K_θ(x))}` is at least `1/(2h)`; that is, `eq:beta-small-mass` holds
  with probability at least `1 − 1/(100N)`.

`beta_sampling` is the paper's existential form: some finite seed space with some weight
carries records `K_θ(x)` with the three properties.

**Hypotheses.**  The paper's records `U_ω(x)` have at most `β` positions; the statements here
do not need this, and the hypothesis is omitted.  A record of `x` is a subword of `x`, which
is the truthfulness hypothesis `(cand ω x).Truthful x`.  The paper's `T ≥ 1` enters only as
`T ≥ 0`.  The hypotheses `N ≥ 2` and `β ≤ N` enter only the cost bound, through
`R, ℓ = O(L)`.

**Constant ledger.**  For a fixed `θ` the merger has a dual of cost `2·R·8·T·2b·√k`
(`hasDual_mergeK_seeded_fin`), the bound `O(T·D·√k)` of `lem:beta-rejection-dual` for its
`D = 2bR` draws.  For `L ≥ 1` and `b ≤ 2^L`, `R ≤ 9 + 2L ≤ 6(L+1)` (`Pstd_fst_le`) and
`ℓ ≤ 3L + 12 ≤ 8(L+1)` (`ellStd_le_eight_mul`), so `√k = √h·√(2ℓ) ≤ 4·√h·√(L+1)` and the
cost is at most `32·b·T·6(L+1)·4·√h·√(L+1) = 768·b·T·√h·(L+1)^{3/2}`
(`mergeCost_Pstd_le`).  The probability clause is `seeded_small_mass` at threshold
`a = 1/(2h)`, where `2^{−R}/a + 2bR(1−a)^k ≤ 1/(100·2^L)` is `goodParams_Pstd`.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

/-! ## The parameter arithmetic -/

/-- `ℓ = ⌈log₂(400·2^L·b·(9+2L))⌉ ≤ 8(L+1)` for `L ≥ 1` and `b ≤ 2^L`. -/
lemma ellStd_le_eight_mul {b L : ℕ} (hL : 1 ≤ L) (hbN : b ≤ 2 ^ L) :
    ellStd b L ≤ 8 * (L + 1) := by
  unfold ellStd
  calc Nat.clog 2 (400 * 2 ^ L * b * (9 + 2 * L)) ≤ Nat.clog 2 (2 ^ (8 * (L + 1))) := by
        refine Nat.clog_mono_right 2 ?_
        have h1 : 9 + 2 * L ≤ 2 ^ (L + 3) := by
          have := Nat.lt_two_pow_self (n := L)
          rw [pow_add]
          omega
        calc 400 * 2 ^ L * b * (9 + 2 * L) ≤ 2 ^ 9 * 2 ^ L * 2 ^ L * 2 ^ (L + 3) :=
              Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) hbN) h1
          _ = 2 ^ (3 * L + 12) := by
              rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
          _ ≤ 2 ^ (8 * (L + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 8 * (L + 1) := Nat.clog_pow 2 _ (by norm_num)

/-- **The cost arithmetic**: at the standard parameters `(R, k) = Pstd b L h`, the seeded
merger's cost `2·R·8·T·2b·√k` is at most `768·b·T·√h·(L+1)^{3/2}`. -/
lemma mergeCost_Pstd_le {b L h : ℕ} (hL : 1 ≤ L) (hbN : b ≤ 2 ^ L) {T : ℝ} (hT : 0 ≤ T)
    (hh1 : 1 ≤ h) (hhN : h ≤ 2 ^ L) :
    2 * ((Pstd b L h).1 * (8 * T * ((2 * b : ℕ) : ℝ) * Real.sqrt (Pstd b L h).2))
      ≤ 768 * b * T * Real.sqrt h * ((L + 1) * Real.sqrt (L + 1)) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hR : ((Pstd b L h).1 : ℝ) ≤ 6 * ((L : ℝ) + 1) := by
    have := Pstd_fst_le b L h hh1 hhN
    linarith
  have hℓ : 2 * (ellStd b L : ℝ) ≤ 4 ^ 2 * ((L : ℝ) + 1) := by
    have : (ellStd b L : ℝ) ≤ 8 * ((L : ℝ) + 1) := by
      exact_mod_cast ellStd_le_eight_mul hL hbN
    linarith
  have hk : Real.sqrt (Pstd b L h).2 ≤ 4 * (Real.sqrt h * Real.sqrt ((L : ℝ) + 1)) := by
    have e : (((Pstd b L h).2 : ℕ) : ℝ) = h * (2 * ellStd b L) := by
      change ((2 * h * ellStd b L : ℕ) : ℝ) = _
      push_cast
      ring
    have h4 : Real.sqrt (2 * (ellStd b L : ℝ)) ≤ 4 * Real.sqrt ((L : ℝ) + 1) := by
      calc Real.sqrt (2 * (ellStd b L : ℝ)) ≤ Real.sqrt (4 ^ 2 * ((L : ℝ) + 1)) :=
            Real.sqrt_le_sqrt hℓ
        _ = 4 * Real.sqrt ((L : ℝ) + 1) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [e, Real.sqrt_mul (Nat.cast_nonneg _)]
    calc Real.sqrt h * Real.sqrt (2 * (ellStd b L : ℝ))
        ≤ Real.sqrt h * (4 * Real.sqrt ((L : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
      _ = 4 * (Real.sqrt h * Real.sqrt ((L : ℝ) + 1)) := by ring
  have hbT : (0 : ℝ) ≤ 32 * b * T := mul_nonneg (by positivity) hT
  calc 2 * ((Pstd b L h).1 * (8 * T * ((2 * b : ℕ) : ℝ) * Real.sqrt (Pstd b L h).2))
      = 32 * b * T * ((Pstd b L h).1 * Real.sqrt (Pstd b L h).2) := by
        push_cast
        ring
    _ ≤ 32 * b * T * (6 * ((L : ℝ) + 1) * (4 * (Real.sqrt h * Real.sqrt ((L : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hR hk (Real.sqrt_nonneg _) (by positivity)) hbT
    _ = 768 * b * T * Real.sqrt h * ((L + 1) * Real.sqrt (L + 1)) := by ring

/-! ## The construction -/

section BetaSampling

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable [DecidableLE M] (letter : σ → M)

/-- **The seed `θ` of `lem:beta-sampling`**: a candidate seed `ω : Ω` for every proposal
slot `t < k` of every draw `i < 2b` of every round `ρ < R`, where `(R, k) = Pstd b L h`.
Its law is the i.i.d. weight `tupleW (tupleW (tupleW ν))`. -/
abbrev BetaSeed (Ω : Type) (b L h : ℕ) : Type :=
  Fin (Pstd b L h).1 → Fin (2 * b) → Fin (Pstd b L h).2 → Ω

/-- **The record `K_θ(x)` of `lem:beta-sampling`**: the seeded merger `mergeK` at the
standard parameters `(R, k) = Pstd b L h`, run on the candidates `cand (θ ρ i t) x`.  It makes
`R` rounds of `2b` draws; a draw returns the first of its `k` proposals that is still marked,
a completed round saves the union of its batch with the previous saved union, and a failed
draw stops the run.  The output is a compression of the final saved union to at most `b`
positions with the same product. -/
noncomputable def betaSampleK {n : ℕ} {Ω : Type} (b L h : ℕ)
    (cand : Ω → (Fin n → σ) → Record n σ) (θ : BetaSeed Ω b L h) (x : Fin n → σ) :
    Record n σ :=
  mergeK letter b (Pstd b L h).1 (fun ρ i t => cand (θ ρ i t) x)

/-! ## The lemma -/

/-- **`lem:beta-sampling`, explicit form.**  Let `N = 2^L` with `L ≥ 1` and `b ≤ 2^L`, let
`ν` be a weight on a finite seed space `Ω`, and let every seed `ω` give a truthful record
`cand ω x` whose map `x ↦ cand ω x` has a dual of cost `T ≥ 0`.  For `1 ≤ h ≤ 2^L`, with
i.i.d. seeds `θ : BetaSeed Ω b L h` and `K_θ = betaSampleK letter b L h cand θ`:

* every `K_θ(x)` is a truthful record of at most `b` positions;
* every `K_θ` has a dual of cost `768·b·T·√h·(L+1)^{3/2}` (the paper's `O(βT√h·L^{3/2})`
  with its `L = 1 + log₂ N = L + 1`);
* for every input `x`, the probability over `θ` that the candidate law `pushW ν (cand · x)`
  puts mass at least `1/(2h)` on records `U` with `p(U) ≰ p(K_θ(x))` is at most
  `1/(100·2^L)` (`eq:beta-small-mass` fails with probability at most `1/(100N)`).

The candidates need not have at most `b` positions. -/
theorem beta_sampling_explicit (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    (hb1 : 1 ≤ b) {n L : ℕ} (hL : 1 ≤ L) (hbN : b ≤ 2 ^ L) {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] {ν : Ω → ℝ} (hν : IsWeight ν) (cand : Ω → (Fin n → σ) → Record n σ)
    (hcT : ∀ ω x, (cand ω x).Truthful x) {T : ℝ} (hT : 0 ≤ T) (hc : ∀ ω, HasDual (cand ω) T)
    {h : ℕ} (hh1 : 1 ≤ h) (hhN : h ≤ 2 ^ L) :
    (∀ (θ : BetaSeed Ω b L h) (x : Fin n → σ), (betaSampleK letter b L h cand θ x).Truthful x
        ∧ (betaSampleK letter b L h cand θ x).supp.card ≤ b)
    ∧ (∀ θ : BetaSeed Ω b L h, HasDual (betaSampleK letter b L h cand θ)
        (768 * b * T * Real.sqrt h * ((L + 1) * Real.sqrt (L + 1))))
    ∧ ∀ x : Fin n → σ, ∑ θ : BetaSeed Ω b L h, tupleW (tupleW (tupleW ν)) θ
        * (if 1 / (2 * (h : ℝ)) ≤ ∑ U, pushW ν (fun ω => cand ω x) U
            * (if U.prod letter ≤ (betaSampleK letter b L h cand θ x).prod letter then 0 else 1)
          then 1 else 0)
      ≤ 1 / (100 * 2 ^ L) := by
  have hΩ : Nonempty Ω := by
    obtain ⟨ω, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by rw [hν.sum_one]; exact one_ne_zero : ∑ ω, ν ω ≠ 0)
    exact ⟨ω⟩
  refine ⟨fun θ x => mergeK_spec letter hb hb1 x _ _ fun ρ i t => hcT _ x, fun θ => ?_,
    fun x => ?_⟩
  · exact (hasDual_mergeK_seeded_fin letter hb1 (Pstd_snd_pos hb1 h hh1) cand hT hc _ θ).mono
      (mergeCost_Pstd_le hL hbN hT hh1 hhN)
  · have hh : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    have ha : (0 : ℝ) < 1 / (2 * (h : ℝ)) := one_div_pos.2 (by linarith)
    have ha1 : 1 / (2 * (h : ℝ)) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    refine (seeded_small_mass letter hst hb hb1 hν cand hcT x ha ha1 (k := (Pstd b L h).2)
      (Pstd b L h).1).trans ?_
    have hP := goodParams_Pstd (L := L) hb1 h hh1 hhN
    push_cast at hP
    exact hP

omit [DecidableEq M] in
/-- **`lem:beta-sampling`.**  Let `N = 2^L` with `L ≥ 1` and `b ≤ 2^L`, let `ν` be a weight on
a finite seed space `Ω`, and let every seed `ω` give a truthful record `cand ω x` whose map
`x ↦ cand ω x` has a dual of cost `T ≥ 0`.  Then for every `1 ≤ h ≤ 2^L` there are a finite
seed space `Θ` with a weight `θw` and records `K θ x` such that every `K θ x` is a truthful
record of at most `b` positions, every `K θ` has a dual of cost `768·b·T·√h·(L+1)^{3/2}`,
and, for every input `x`, with probability at most `1/(100·2^L)` over `θ` the candidate law
`pushW ν (cand · x)` puts mass at least `1/(2h)` on records `U` with `p(U) ≰ p(K θ x)`; that
is, `eq:beta-small-mass` holds with probability at least `1 − 1/(100N)`.  The construction
is `beta_sampling_explicit`; the candidates need not have at most `b` positions. -/
theorem beta_sampling (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    (hb1 : 1 ≤ b) {n L : ℕ} (hL : 1 ≤ L) (hbN : b ≤ 2 ^ L) {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] {ν : Ω → ℝ} (hν : IsWeight ν) (cand : Ω → (Fin n → σ) → Record n σ)
    (hcT : ∀ ω x, (cand ω x).Truthful x) {T : ℝ} (hT : 0 ≤ T) (hc : ∀ ω, HasDual (cand ω) T)
    {h : ℕ} (hh1 : 1 ≤ h) (hhN : h ≤ 2 ^ L) :
    ∃ (Θ : Type) (_ : Fintype Θ) (_ : DecidableEq Θ) (θw : Θ → ℝ)
      (K : Θ → (Fin n → σ) → Record n σ),
      IsWeight θw
      ∧ (∀ θ x, (K θ x).Truthful x ∧ (K θ x).supp.card ≤ b)
      ∧ (∀ θ, HasDual (K θ) (768 * b * T * Real.sqrt h * ((L + 1) * Real.sqrt (L + 1))))
      ∧ ∀ x : Fin n → σ, ∑ θ, θw θ
          * (if 1 / (2 * (h : ℝ)) ≤ ∑ U, pushW ν (fun ω => cand ω x) U
              * (if U.prod letter ≤ (K θ x).prod letter then 0 else 1)
            then 1 else 0)
        ≤ 1 / (100 * 2 ^ L) := by
  classical
  obtain ⟨h1, h2, h3⟩ :=
    beta_sampling_explicit letter hst hb hb1 hL hbN hν cand hcT hT hc hh1 hhN
  exact ⟨BetaSeed Ω b L h, inferInstance, inferInstance, tupleW (tupleW (tupleW ν)),
    betaSampleK letter b L h cand, isWeight_tupleW (isWeight_tupleW (isWeight_tupleW hν _) _) _,
    h1, h2, h3⟩

end BetaSampling

end MonoidProduct
