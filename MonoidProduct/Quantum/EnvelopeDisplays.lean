import MonoidProduct.Quantum.DyckNearLinear
import MonoidProduct.Quantum.DyckLanguageLower
import MonoidProduct.Dyck.Breadth
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The envelope and Dyck displays, as stated (`monoid.tex`, `thm:aperiodic-envelope`,
`cor:dyck`)

`Quantum/Envelope.lean` proves both halves of `thm:aperiodic-envelope` in Lean-native
vocabulary: the upper half through `cubeExponentMax`, the lower half at even lengths
with the regime `4·8^{envLevel N} ≤ n`.  This file restates them as the manuscript
displays them, and removes the parity restriction by identity padding
(`dyckNL_qQuery_ge_advPM`).

**Upper half** (`L(n) = paperLog n = 2 + log₂(n+2)`, natural `log`, `C = 2^18`):

* `envD_aperiodicEnvelope_le_final` —
  `𝒬_ap(N,n) ≤ min{n, √n·L(n)^{C·(N·log(N+2))^{1/3}}}` for all `N ≥ 1` and all `n`;
* `envD_aperiodicEnvelope_le_display` — the displayed form
  `𝒬_ap(N,n) ≤ min{n, √n·2^{C N^{1/3}}·L(n)^{C N^{1/3} log^{1/3}(N+2)}}`.

**Lower half, every length** (witness `M_k = DyckNF k`, base `c = 2^{1/20}`):

* `envD_dyck_qQuery_two_pow` — for `1 ≤ k` and `2^k ≤ n` (any parity),
  `(7/11008)·2^{k/20}·√n ≤ Q_{1/3}(Prod_{M_k,n})`;
* `envD_aperiodicEnvelope_lower_explicit` — for `N ≥ 27` and `N ≤ log³(n+2)/8`,
  `7/(11008·2^{3/20})·√n·2^{N^{1/3}/20} ≤ 𝒬_ap(N,n)`;
* `envD_aperiodicEnvelope_lower_paper` — the paper's constant-free form:
  `2^27 ≤ N ≤ log³(n+2)/8 ⇒ √n·2^{N^{1/3}/40} ≤ 𝒬_ap(N,n)`;
* `envD_aperiodic_envelope` — `thm:aperiodic-envelope` with its quantifiers:
  `∃ C > 0` (upper) and `∃ N₀, a, b > 0` (lower).

**`cor:dyck`**:

* `envD_dyck_qQuery_lower` — the main display at every `n`:
  `1 ≤ k ≤ log₂ n ⇒ c₀·c^{d_J(M_k)}·√n ≤ Q_{1/3}(Prod_{M_k,n})`, `c = 2^{1/20}`,
  `c₀ = 7/(11008·2^{1/20})`, `d_J(M_k) = k + 1` (`jDepth_dyckNF`);
  `envD_dyck_qQuery_lower_log` with natural `log`, and `envD_dyck_qQuery_lower_exists`;
* `envD_dyck_qQuery_lower_card` — the second equality, `2^{Ω(|M_k|^{1/3})}`:
  `7/(11008·2^{1/10})·2^{|M_k|^{1/3}/20}·√n ≤ Q_{1/3}(Prod_{M_k,n})`;
* `envD_dyck_no_subexp_bound` — clause (i): if `Q_{1/3}(Prod_{M,n}) ≤ f(|M|)·√n` for
  every finite aperiodic `M` and every `n ≥ 1`, then `f(N) = exp(o(N^{1/3}))` fails:
  it is not true that for every `ε > 0` eventually `f(N) ≤ 2^{ε N^{1/3}}`.

Deviations: `k ≥ 1` (at `k = 0` the binary Dyck product is not the witness), and
`k ≤ log₂ n` (implied by the paper's `k ≤ log n` for either reading of `log`).  The
condition `N ≥ N₀` in the paper form is `N ≥ 2^27`, with `a = 1/8` and `b = 1/40`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## The upper half, displayed -/

/-- The cube-root exponent argument `(s·log(s+2))^{1/3}` is monotone in `s`. -/
lemma envD_exp_mono {s N : ℕ} (hsN : s ≤ N) :
    ((s : ℝ) * Real.log ((s : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)
      ≤ ((N : ℝ) * Real.log ((N : ℝ) + 2)) ^ ((3 : ℝ)⁻¹) := by
  have hs : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.log ((s : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hl : Real.log ((s : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  exact Real.rpow_le_rpow (mul_nonneg hs0 hl0) (mul_le_mul hs hl hl0 (by linarith))
    (by norm_num)

/-- **`thm:aperiodic-envelope`, upper half, `eq:ags-cuberoot-final` form**: for `N ≥ 1`
and every `n`,
`𝒬_ap(N,n) ≤ min{n, √n·L(n)^{2^18·(N·log(N+2))^{1/3}}}`, `L(n) = 2 + log₂(n+2)`. -/
theorem envD_aperiodicEnvelope_le_final {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    aperiodicEnvelope N n
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ) * paperLog n
          ^ (262144 * (((N : ℝ) * Real.log ((N : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)))) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have h := aperiodicEnvelope_le_length hN 0
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, min_self] at h ⊢
    exact h
  refine csSup_le (envelopeSet_nonempty hN n) ?_
  rintro q ⟨M, _, _, _, _, hM, rfl⟩
  refine (aperiodic_qQuery_final_exact (M' := M) hn).trans
    (min_le_min le_rfl (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)))
  have hP : (1 : ℝ) ≤ paperLog n := by linarith [three_le_paperLog n]
  exact Real.rpow_le_rpow_of_exponent_le hP
    (mul_le_mul_of_nonneg_left (envD_exp_mono hM) (by norm_num))

/-- **`thm:aperiodic-envelope`, upper half, as displayed**: for `N ≥ 1` and every `n`,

  `𝒬_ap(N,n) ≤ min{n, √n·2^{C N^{1/3}}·L(n)^{C N^{1/3} log^{1/3}(N+2)}}`,

with `C = 2^18`, `L(n) = 2 + log₂(n+2)` and the natural logarithm. -/
theorem envD_aperiodicEnvelope_le_display {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    aperiodicEnvelope N n
      ≤ min (n : ℝ) (Real.sqrt (n : ℝ)
          * (2 : ℝ) ^ (262144 * (N : ℝ) ^ ((1 : ℝ) / 3))
          * paperLog n ^ (262144 * (N : ℝ) ^ ((1 : ℝ) / 3)
              * Real.log ((N : ℝ) + 2) ^ ((1 : ℝ) / 3))) := by
  refine (envD_aperiodicEnvelope_le_final hN n).trans (min_le_min le_rfl ?_)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hsplit : 262144 * (((N : ℝ) * Real.log ((N : ℝ) + 2)) ^ ((3 : ℝ)⁻¹))
      = 262144 * (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log ((N : ℝ) + 2) ^ ((1 : ℝ) / 3) := by
    rw [Real.mul_rpow hN0 hl0, one_div]
    ring
  rw [hsplit]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (262144 * (N : ℝ) ^ ((1 : ℝ) / 3)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hP : 0 ≤ paperLog n ^ (262144 * (N : ℝ) ^ ((1 : ℝ) / 3)
      * Real.log ((N : ℝ) + 2) ^ ((1 : ℝ) / 3)) :=
    Real.rpow_nonneg (by linarith [three_le_paperLog n]) _
  have hs := Real.sqrt_nonneg (n : ℝ)
  calc Real.sqrt (n : ℝ) * paperLog n ^ (262144 * (N : ℝ) ^ ((1 : ℝ) / 3)
          * Real.log ((N : ℝ) + 2) ^ ((1 : ℝ) / 3))
      = Real.sqrt (n : ℝ) * 1 * paperLog n ^ (262144 * (N : ℝ) ^ ((1 : ℝ) / 3)
          * Real.log ((N : ℝ) + 2) ^ ((1 : ℝ) / 3)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hs) hP

/-! ## The Dyck lower bound at every length -/

/-- The Dyck product at even length `w`, `1 ≤ k`, `2^k ≤ w`:
`2^{k/20}·√w/(4√2) ≤ ADV±(dyckProduct k w)`. -/
lemma envD_advPM_dyckProduct {k w : ℕ} (hk : 1 ≤ k) (heven : Even w) (hkw : 2 ^ k ≤ w) :
    (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt w / (4 * Real.sqrt 2)
      ≤ advPM (dyckProduct k w) := by
  refine le_trans ?_ (advPM_dyck_le_product k w)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsw := Real.sqrt_nonneg (w : ℝ)
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · have hadv := dyckLB_sqrt_le_advPM k w hk heven
    have hcast : ((w / 2 : ℕ) : ℝ) = (w : ℝ) / 2 := by
      obtain ⟨a, ha⟩ := heven
      rw [show w / 2 = a by omega, ha]
      push_cast
      ring
    rw [hcast, Real.sqrt_div (Nat.cast_nonneg w)] at hadv
    have hpow : (2 : ℝ) ^ ((k : ℝ) / 20) ≤ 2 := by
      calc (2 : ℝ) ^ ((k : ℝ) / 20) ≤ 2 ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have : (k : ℝ) ≤ 3 := by exact_mod_cast (by omega : k ≤ 3)
            linarith
        _ = 2 := Real.rpow_one 2
    refine le_trans ?_ hadv
    rw [div_le_div_iff₀ (by positivity) hs2]
    have h0 : 0 ≤ (2 : ℝ) ^ ((k : ℝ) / 20) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hpow hsw]
  · set ℓ := (k - 4) / 10 with hℓ
    have hfit : 4 * 8 ^ ℓ ≤ w := by
      calc 4 * 8 ^ ℓ = 2 ^ (3 * ℓ + 2) := by rw [pow_add, pow_mul]; norm_num; ring
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ w := hkw
    have hadv := sqrt_mul_sqrt_two_pow_le_advPM_dyck ℓ w k heven hfit (by omega)
    have hpow := dyckLB_rpow_le_sqrt_pow k
    rw [← hℓ] at hpow
    rw [div_le_iff₀ (by positivity)]
    have h1 : (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt w
        ≤ 2 * Real.sqrt 2 ^ ℓ * Real.sqrt w := mul_le_mul_of_nonneg_right hpow hsw
    have h2 : 2 * Real.sqrt 2 ^ ℓ * Real.sqrt w
        ≤ 2 * (2 * Real.sqrt 2 * advPM (dyck k w)) := by nlinarith
    nlinarith

/-- **The Dyck product lower bound at every length**: for `1 ≤ k` and `2^k ≤ n`
(either parity),
`(7/11008)·2^{k/20}·√n ≤ Q_{1/3}(Prod_{DyckNF k, n})`.  Odd `n` pads the even length
`n − 1` with the identity. -/
theorem envD_dyck_qQuery_two_pow {k n : ℕ} (hk : 1 ≤ k) (hkn : 2 ^ k ≤ n) :
    7 / 11008 * (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt n
      ≤ (qQuery (fun v : Fin n → DyckNF k => wordProd (id : DyckNF k → DyckNF k) v)
          (1 / 3) : ℝ) := by
  set w := 2 * (n / 2) with hw
  have heven : Even w := ⟨n / 2, by omega⟩
  have hwn : w ≤ n := by omega
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hkw : 2 ^ k ≤ w := by omega
  have hn2 : 2 ≤ n := le_trans (by rw [h2k]; have := Nat.one_le_two_pow (n := k - 1); omega)
    hkn
  have hQ := dyckNL_qQuery_ge_advPM (k := k) (w := w) (n := n) hk hwn
  have hadv := envD_advPM_dyckProduct hk heven hkw
  have hnw : (n : ℝ) / 2 ≤ (w : ℝ) := by
    have : n ≤ 2 * w := by omega
    have : (n : ℝ) ≤ 2 * (w : ℝ) := by exact_mod_cast this
    linarith
  have hsq : Real.sqrt n / Real.sqrt 2 ≤ Real.sqrt w := by
    rw [← Real.sqrt_div (Nat.cast_nonneg n)]
    exact Real.sqrt_le_sqrt hnw
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hpos : 0 ≤ (2 : ℝ) ^ ((k : ℝ) / 20) := by positivity
  have hstep : (2 : ℝ) ^ ((k : ℝ) / 20) * (Real.sqrt n / Real.sqrt 2) / (4 * Real.sqrt 2)
      ≤ (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt w / (4 * Real.sqrt 2) := by
    gcongr
  calc 7 / 11008 * (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt n
      = (7 / 1376 : ℝ) * ((2 : ℝ) ^ ((k : ℝ) / 20) * (Real.sqrt n / Real.sqrt 2)
          / (4 * Real.sqrt 2)) := by
        field_simp
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
    _ ≤ (7 / 1376 : ℝ) * advPM (dyckProduct k w) :=
        mul_le_mul_of_nonneg_left (hstep.trans hadv) (by norm_num)
    _ ≤ _ := hQ

/-- `(2^{1/20})^{k+1} = 2^{1/20}·2^{k/20}`. -/
lemma envD_base_pow (k : ℕ) :
    ((2 : ℝ) ^ ((1 : ℝ) / 20)) ^ (k + 1)
      = (2 : ℝ) ^ ((1 : ℝ) / 20) * (2 : ℝ) ^ ((k : ℝ) / 20) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

/-- **`cor:dyck`, main display, every length**: for `1 ≤ k ≤ log₂ n`,

  `7/(11008·2^{1/20}) · (2^{1/20})^{d_J(M_k)} · √n ≤ Q_{1/3}(Prod_{M_k,n})`,

with `M_k = DyckNF k` over its full alphabet and `d_J(M_k) = k + 1`. -/
theorem envD_dyck_qQuery_lower {k n : ℕ} (hk : 1 ≤ k) (hlog : (k : ℝ) ≤ Real.logb 2 n) :
    7 / (11008 * (2 : ℝ) ^ ((1 : ℝ) / 20))
        * ((2 : ℝ) ^ ((1 : ℝ) / 20)) ^ jDepth (DyckNF k) * Real.sqrt n
      ≤ (qQuery (fun v : Fin n → DyckNF k => wordProd (id : DyckNF k → DyckNF k) v)
          (1 / 3) : ℝ) := by
  have h := envD_dyck_qQuery_two_pow hk (dyckLB_two_pow_le_of_le_logb hk hlog)
  rw [jDepth_dyckNF, envD_base_pow]
  have hc : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 20) := by positivity
  calc 7 / (11008 * (2 : ℝ) ^ ((1 : ℝ) / 20))
        * ((2 : ℝ) ^ ((1 : ℝ) / 20) * (2 : ℝ) ^ ((k : ℝ) / 20)) * Real.sqrt n
      = 7 / 11008 * (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt n := by
        field_simp
    _ ≤ _ := h

/-- `k ≤ ln n` implies `k ≤ log₂ n`. -/
lemma envD_le_logb_of_le_log {k : ℕ} {n : ℕ} (hk : 1 ≤ k) (hlog : (k : ℝ) ≤ Real.log n) :
    (k : ℝ) ≤ Real.logb 2 n := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl2 := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [Real.logb, le_div_iff₀ hl2p]
  nlinarith

/-- **`cor:dyck`, main display, natural logarithm**: for `1 ≤ k ≤ ln n`, the same
bound. -/
theorem envD_dyck_qQuery_lower_log {k n : ℕ} (hk : 1 ≤ k) (hlog : (k : ℝ) ≤ Real.log n) :
    7 / (11008 * (2 : ℝ) ^ ((1 : ℝ) / 20))
        * ((2 : ℝ) ^ ((1 : ℝ) / 20)) ^ jDepth (DyckNF k) * Real.sqrt n
      ≤ (qQuery (fun v : Fin n → DyckNF k => wordProd (id : DyckNF k → DyckNF k) v)
          (1 / 3) : ℝ) :=
  envD_dyck_qQuery_lower hk (envD_le_logb_of_le_log hk hlog)

/-- **`cor:dyck`, main display, with its quantifiers**: there are `c > 1` and `c₀ > 0`
such that `c₀·c^{d_J(M_k)}·√n ≤ Q_{1/3}(Prod_{M_k,n})` for every `n` and every
`1 ≤ k ≤ log n`. -/
theorem envD_dyck_qQuery_lower_exists :
    ∃ c : ℝ, 1 < c ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k n : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.log n →
      c₀ * c ^ jDepth (DyckNF k) * Real.sqrt n
        ≤ (qQuery (fun v : Fin n → DyckNF k => wordProd (id : DyckNF k → DyckNF k) v)
            (1 / 3) : ℝ) :=
  ⟨(2 : ℝ) ^ ((1 : ℝ) / 20), Real.one_lt_rpow (by norm_num) (by norm_num),
    7 / (11008 * (2 : ℝ) ^ ((1 : ℝ) / 20)), by positivity,
    fun _ _ hk hlog => envD_dyck_qQuery_lower_log hk hlog⟩

/-- `|M|^{1/3} ≤ k + 2` from `|M| ≤ (k+2)³`. -/
lemma envD_rpow_third_le {s k : ℕ} (h : s ≤ (k + 2) ^ 3) :
    (s : ℝ) ^ ((1 : ℝ) / 3) ≤ (k : ℝ) + 2 := by
  have h' : (s : ℝ) ≤ ((k : ℝ) + 2) ^ (3 : ℕ) := by exact_mod_cast h
  calc (s : ℝ) ^ ((1 : ℝ) / 3) ≤ (((k : ℝ) + 2) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h' (by norm_num)
    _ = (k : ℝ) + 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-- **`cor:dyck`, second equality** (`2^{Ω(|M_k|^{1/3})}`): for `1 ≤ k ≤ log₂ n`,
`7/(11008·2^{1/10})·2^{|M_k|^{1/3}/20}·√n ≤ Q_{1/3}(Prod_{M_k,n})`. -/
theorem envD_dyck_qQuery_lower_card {k n : ℕ} (hk : 1 ≤ k)
    (hlog : (k : ℝ) ≤ Real.logb 2 n) :
    7 / (11008 * (2 : ℝ) ^ ((1 : ℝ) / 10))
        * (2 : ℝ) ^ ((Fintype.card (DyckNF k) : ℝ) ^ ((1 : ℝ) / 3) / 20) * Real.sqrt n
      ≤ (qQuery (fun v : Fin n → DyckNF k => wordProd (id : DyckNF k → DyckNF k) v)
          (1 / 3) : ℝ) := by
  have h := envD_dyck_qQuery_two_pow hk (dyckLB_two_pow_le_of_le_logb hk hlog)
  have hc := envD_rpow_third_le (card_dyckNF_le_cube k)
  have hpow : (2 : ℝ) ^ ((Fintype.card (DyckNF k) : ℝ) ^ ((1 : ℝ) / 3) / 20)
      ≤ (2 : ℝ) ^ ((k : ℝ) / 20) * (2 : ℝ) ^ ((1 : ℝ) / 10) := by
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h10 : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 10) := by positivity
  refine le_trans ?_ h
  have hs := Real.sqrt_nonneg (n : ℝ)
  calc 7 / (11008 * (2 : ℝ) ^ ((1 : ℝ) / 10))
        * (2 : ℝ) ^ ((Fintype.card (DyckNF k) : ℝ) ^ ((1 : ℝ) / 3) / 20) * Real.sqrt n
      ≤ 7 / (11008 * (2 : ℝ) ^ ((1 : ℝ) / 10))
        * ((2 : ℝ) ^ ((k : ℝ) / 20) * (2 : ℝ) ^ ((1 : ℝ) / 10)) * Real.sqrt n := by
        gcongr
    _ = 7 / 11008 * (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt n := by
        field_simp

/-! ## The lower half of the envelope, every length -/

/-- **`thm:aperiodic-envelope`, lower half, parametric, every length**: for `1 ≤ k`,
`2^k ≤ n` and `(k+2)³ ≤ N`, `(7/11008)·2^{k/20}·√n ≤ 𝒬_ap(N,n)`. -/
theorem envD_aperiodicEnvelope_lower_two_pow {k n N : ℕ} (hk : 1 ≤ k) (hkn : 2 ^ k ≤ n)
    (hN : (k + 2) ^ 3 ≤ N) :
    7 / 11008 * (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt n ≤ aperiodicEnvelope N n :=
  (envD_dyck_qQuery_two_pow hk hkn).trans
    (le_aperiodicEnvelope ((card_dyckNF_le_cube k).trans hN))

/-- `N^{1/3} < cubeDepth N + 3`. -/
lemma envD_rpow_third_lt_cubeDepth (N : ℕ) :
    (N : ℝ) ^ ((1 : ℝ) / 3) < (cubeDepth N : ℝ) + 3 := by
  have h' : (N : ℝ) < ((cubeDepth N : ℝ) + 3) ^ (3 : ℕ) := by
    exact_mod_cast lt_cubeDepth_succ_cube N
  calc (N : ℝ) ^ ((1 : ℝ) / 3) < (((cubeDepth N : ℝ) + 3) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
        Real.rpow_lt_rpow (Nat.cast_nonneg _) h' (by norm_num)
    _ = (cubeDepth N : ℝ) + 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-- In the regime `N ≤ log³(n+2)/8`, the Dyck depth `k = cubeDepth N ≥ 1` fits:
`2^k ≤ n`. -/
lemma envD_two_pow_cubeDepth_le {n N : ℕ} (hN : 27 ≤ N)
    (hreg : (N : ℝ) ≤ Real.log ((n : ℝ) + 2) ^ 3 / 8) :
    1 ≤ cubeDepth N ∧ 2 ^ cubeDepth N ≤ n := by
  set k := cubeDepth N with hkdef
  have hk1 : 1 ≤ k :=
    Nat.le_findGreatest (P := fun k => (k + 2) ^ 3 ≤ N) (by omega) (by norm_num; omega)
  refine ⟨hk1, ?_⟩
  set L := Real.log ((n : ℝ) + 2) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  have hcube : ((k : ℝ) + 2) ^ 3 ≤ (L / 2) ^ 3 := by
    have h1 : (((k + 2) ^ 3 : ℕ) : ℝ) ≤ N := by exact_mod_cast cubeDepth_spec (by omega)
    push_cast at h1
    nlinarith
  have hkL : (k : ℝ) + 2 ≤ L / 2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 hcube
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h2k : (2 : ℝ) ^ k ≤ Real.exp k := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) he1 k
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hexp : Real.exp (k : ℝ) * Real.exp 2 ≤ (n : ℝ) + 2 := by
    rw [← Real.exp_add, show (n : ℝ) + 2 = Real.exp L from
      (Real.exp_log (by positivity)).symm]
    exact Real.exp_le_exp.2 (by linarith)
  have hk2 : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  have hfin : (2 : ℝ) ^ k ≤ n := by
    have h4 : 4 * (2 : ℝ) ^ k ≤ (n : ℝ) + 2 := by
      have := mul_le_mul h2k he2 (by norm_num) (Real.exp_pos _).le
      nlinarith
    linarith
  exact_mod_cast hfin

/-- **`thm:aperiodic-envelope`, lower half, explicit, every length**: for `N ≥ 27` and
`N ≤ log³(n+2)/8`,

  `7/(11008·2^{3/20}) · √n · 2^{N^{1/3}/20} ≤ 𝒬_ap(N,n)`. -/
theorem envD_aperiodicEnvelope_lower_explicit {n N : ℕ} (hN : 27 ≤ N)
    (hreg : (N : ℝ) ≤ Real.log ((n : ℝ) + 2) ^ 3 / 8) :
    7 / (11008 * (2 : ℝ) ^ ((3 : ℝ) / 20)) * Real.sqrt n
        * (2 : ℝ) ^ ((N : ℝ) ^ ((1 : ℝ) / 3) / 20)
      ≤ aperiodicEnvelope N n := by
  obtain ⟨hk1, hkn⟩ := envD_two_pow_cubeDepth_le hN hreg
  have H := envD_aperiodicEnvelope_lower_two_pow hk1 hkn (cubeDepth_spec (by omega))
  have hlt := envD_rpow_third_lt_cubeDepth N
  have hpow : (2 : ℝ) ^ ((N : ℝ) ^ ((1 : ℝ) / 3) / 20)
      ≤ (2 : ℝ) ^ ((cubeDepth N : ℝ) / 20) * (2 : ℝ) ^ ((3 : ℝ) / 20) := by
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (0 : ℝ) < (2 : ℝ) ^ ((3 : ℝ) / 20) := by positivity
  refine le_trans ?_ H
  have hs := Real.sqrt_nonneg (n : ℝ)
  calc 7 / (11008 * (2 : ℝ) ^ ((3 : ℝ) / 20)) * Real.sqrt n
        * (2 : ℝ) ^ ((N : ℝ) ^ ((1 : ℝ) / 3) / 20)
      ≤ 7 / (11008 * (2 : ℝ) ^ ((3 : ℝ) / 20)) * Real.sqrt n
        * ((2 : ℝ) ^ ((cubeDepth N : ℝ) / 20) * (2 : ℝ) ^ ((3 : ℝ) / 20)) := by
        gcongr
    _ = 7 / 11008 * (2 : ℝ) ^ ((cubeDepth N : ℝ) / 20) * Real.sqrt n := by
        field_simp

/-- `c·2^{x/40} ≥ 1` once `x ≥ 480`, for the leading constant `c = 7/(11008·2^{3/20})`. -/
lemma envD_absorb {x : ℝ} (hx : 480 ≤ x) :
    1 ≤ 7 / (11008 * (2 : ℝ) ^ ((3 : ℝ) / 20)) * (2 : ℝ) ^ (x / 40) := by
  have h12 : (4096 : ℝ) ≤ (2 : ℝ) ^ (x / 40) := by
    calc (4096 : ℝ) = (2 : ℝ) ^ (12 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ ((3 : ℝ) / 20) ≤ 2 := by
    calc (2 : ℝ) ^ ((3 : ℝ) / 20) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h3p : (0 : ℝ) < (2 : ℝ) ^ ((3 : ℝ) / 20) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- **`thm:aperiodic-envelope`, lower half, the paper's form, every length**: for
`2^27 ≤ N ≤ log³(n+2)/8`, `√n·2^{N^{1/3}/40} ≤ 𝒬_ap(N,n)` — no leading constant, the
paper's `N₀ = 2^27`, `a = 1/8`, `b = 1/40`. -/
theorem envD_aperiodicEnvelope_lower_paper {n N : ℕ} (hN : 2 ^ 27 ≤ N)
    (hreg : (N : ℝ) ≤ Real.log ((n : ℝ) + 2) ^ 3 / 8) :
    Real.sqrt n * (2 : ℝ) ^ ((N : ℝ) ^ ((1 : ℝ) / 3) / 40) ≤ aperiodicEnvelope N n := by
  have H := envD_aperiodicEnvelope_lower_explicit (by omega) hreg
  set x := (N : ℝ) ^ ((1 : ℝ) / 3) with hx
  have hx512 : 512 ≤ x := by
    have h' : ((512 : ℝ)) ^ (3 : ℕ) ≤ (N : ℝ) := by
      have : ((2 ^ 27 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
      norm_num at this ⊢
      linarith
    calc (512 : ℝ) = ((512 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ x := Real.rpow_le_rpow (by positivity) h' (by norm_num)
  have hab := envD_absorb (x := x) (by linarith)
  have hsplit : (2 : ℝ) ^ (x / 20) = (2 : ℝ) ^ (x / 40) * (2 : ℝ) ^ (x / 40) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  refine le_trans ?_ H
  rw [hsplit]
  have hs := Real.sqrt_nonneg (n : ℝ)
  have hp : 0 ≤ (2 : ℝ) ^ (x / 40) := by positivity
  have := mul_le_mul_of_nonneg_left hab (mul_nonneg hs hp)
  nlinarith

/-- **`thm:aperiodic-envelope`, both halves, with the paper's quantifiers**: there is
`C > 0` with

  `𝒬_ap(N,n) ≤ min{n, √n·2^{C N^{1/3}}·L(n)^{C N^{1/3} log^{1/3}(N+2)}}`

for all `N, n ≥ 1`; and there are an integer `N₀` and `a, b > 0` with
`√n·2^{b N^{1/3}} ≤ 𝒬_ap(N,n)` whenever `N₀ ≤ N ≤ a·log³(n+2)`. -/
theorem envD_aperiodic_envelope :
    (∃ C : ℝ, 0 < C ∧ ∀ N n : ℕ, 1 ≤ N → 1 ≤ n →
      aperiodicEnvelope N n
        ≤ min (n : ℝ) (Real.sqrt (n : ℝ) * (2 : ℝ) ^ (C * (N : ℝ) ^ ((1 : ℝ) / 3))
            * paperLog n ^ (C * (N : ℝ) ^ ((1 : ℝ) / 3)
                * Real.log ((N : ℝ) + 2) ^ ((1 : ℝ) / 3)))) ∧
    (∃ N₀ : ℕ, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ n N : ℕ, N₀ ≤ N →
      (N : ℝ) ≤ a * Real.log ((n : ℝ) + 2) ^ 3 →
        Real.sqrt n * (2 : ℝ) ^ (b * (N : ℝ) ^ ((1 : ℝ) / 3)) ≤ aperiodicEnvelope N n) := by
  refine ⟨⟨262144, by norm_num, fun N n hN _ => envD_aperiodicEnvelope_le_display hN n⟩,
    ⟨2 ^ 27, 1 / 8, 1 / 40, by norm_num, by norm_num, fun n N hN hreg => ?_⟩⟩
  have h := envD_aperiodicEnvelope_lower_paper (n := n) hN (by linarith)
  have he : (1 / 40 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 3) = (N : ℝ) ^ ((1 : ℝ) / 3) / 40 := by
    ring
  rwa [he]

/-! ## `cor:dyck` (i): no `exp(o(|M|^{1/3}))·√n` bound -/

/-- Along the Dyck family, any valid bound `Q ≤ f(|M|)·√n` has
`(7/11008)·2^{k/20} ≤ f(|M_k|)` for every `k ≥ 1`. -/
lemma envD_dyck_le_of_bound (f : ℕ → ℝ)
    (hf : ∀ (M : Type) [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
      (n : ℕ), 1 ≤ n →
        (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ)
          ≤ f (Fintype.card M) * Real.sqrt n)
    {k : ℕ} (hk : 1 ≤ k) :
    7 / 11008 * (2 : ℝ) ^ ((k : ℝ) / 20) ≤ f (Fintype.card (DyckNF k)) := by
  have hn : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h1 := envD_dyck_qQuery_two_pow hk (le_refl (2 ^ k))
  have h2 := hf (DyckNF k) (2 ^ k) hn
  have hs : 0 < Real.sqrt ((2 ^ k : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < 2 ^ k))
  have := h1.trans h2
  exact le_of_mul_le_mul_right (by linarith) hs

/-- **`cor:dyck` (i)**: if `Q_{1/3}(Prod_{M,n}) ≤ f(|M|)·√n` for every finite aperiodic
monoid `M` and every `n ≥ 1`, then `f(N) = exp(o(N^{1/3}))` is impossible: it is not the
case that for every `ε > 0`, eventually `f(N) ≤ 2^{ε N^{1/3}}`.  (In particular no
`poly(|M|)·√n` bound exists.) -/
theorem envD_dyck_no_subexp_bound (f : ℕ → ℝ)
    (hf : ∀ (M : Type) [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
      (n : ℕ), 1 ≤ n →
        (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ)
          ≤ f (Fintype.card M) * Real.sqrt n) :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      f N ≤ (2 : ℝ) ^ (ε * (N : ℝ) ^ ((1 : ℝ) / 3)) := by
  intro h
  obtain ⟨N₁, hN₁⟩ := h (1 / 40) (by norm_num)
  set k := 3 * N₁ + 482 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hlow := envD_dyck_le_of_bound f hf hk1
  have hcard : N₁ ≤ Fintype.card (DyckNF k) := by
    have h1 := card_dyckNF_cube_lower k
    have h2 : k + 1 ≤ (k + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hup := hN₁ _ hcard
  have hc := envD_rpow_third_le (card_dyckNF_le_cube k)
  have hup' : f (Fintype.card (DyckNF k)) ≤ (2 : ℝ) ^ (((k : ℝ) + 2) / 40) :=
    hup.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have hk482 : (482 : ℝ) ≤ k := by exact_mod_cast (by omega : 482 ≤ k)
  have hsplit : (2 : ℝ) ^ ((k : ℝ) / 20)
      = (2 : ℝ) ^ (((k : ℝ) + 2) / 40) * (2 : ℝ) ^ (((k : ℝ) - 2) / 40) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have h12 : (4096 : ℝ) ≤ (2 : ℝ) ^ (((k : ℝ) - 2) / 40) := by
    calc (4096 : ℝ) = (2 : ℝ) ^ (12 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hp : 0 < (2 : ℝ) ^ (((k : ℝ) + 2) / 40) := by positivity
  have hfin := hlow.trans hup'
  rw [hsplit] at hfin
  set A := (2 : ℝ) ^ (((k : ℝ) + 2) / 40) with hA
  set B := (2 : ℝ) ^ (((k : ℝ) - 2) / 40) with hB
  have hlt : A * 1 < A * (7 / 11008 * B) :=
    mul_lt_mul_of_pos_left (by linarith) hp
  have heq : 7 / 11008 * (A * B) = A * (7 / 11008 * B) := by ring
  linarith

end MonoidProduct
