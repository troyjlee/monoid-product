import MonoidProduct.Quantum.OrderedApplications
import MonoidProduct.Ordered.LogRankCost
import MonoidProduct.Ordered.LogRankRoot

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The quasipolynomial ordered product theorem (`thm:ordered-beta-log-product`)

The stage recursion of `LogRank.lean` at the standard parameters: the merger
parameters `Pstd b L` of the polynomial theorem (`thm:ordered-beta-product`),
copy count `L + 2`, thinning rounds `L + 11`, and `⌈log₂ b⌉` stages,
so that the root summary has rank `2^{⌈log₂ b⌉} ≥ b`.

* `costB_std_le`: `costB s j ≤ (2^15·b·L^4)^{s+1}·√2^j` (`costB_le` with the rank-`1` base
  `costA b (Pstd b L) 1 j ≤ 2·2^12·b·L³·√2^j`).
* `ordered_exists_core_alg_logrank`, `ordered_qQuery_le_logrank_main`: the product-and-core
  algorithm and the `Q_{1/10}` bound `(2^15·b·L_n^4)^{⌈log₂ b⌉+2}·√n` for `4 ≤ n`, `1 ≤ b < n`.
* `ordered_qQuery_le_logrank`: the discrete form
  `min { n, (2^15·(b+2)·L_n^4)^{⌈log₂(b+2)⌉+2}·√n }` for every `n` and `b`.
* `ordered_qQuery_le_quasipoly`, `ordered_qQuery_third_le_quasipoly`: the paper's form
  `min { n, √(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)} }` with natural logarithms, real exponent
  and the universal constant `C = 2^17`, in both error conventions; plus the `breadth`
  specialisation.  The endpoints of the polynomial theorem are unchanged.
-/

namespace MonoidProduct

open QuantumQueryComplexity Finset FiniteProb

/-! ## Numerics of the stage-`0` cost -/

/-- The rank-`1` cost factor at the standard parameters is at most `2^12·b·L³`. -/
lemma pstd_factor_le {b L : ℕ} (hb1 : 1 ≤ b) (hL : 3 ≤ L) (hbL : b ≤ 2 ^ L) :
    512 * (b : ℝ) * (9 + 2 * L) * Real.sqrt ((ellStd b L : ℝ) / 2) * L
      ≤ 2 ^ 12 * (b : ℝ) * (L : ℝ) ^ 3 := by
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  -- `ℓ ≤ 3L + 11`, so `ℓ/2 ≤ 4L`
  have hℓle : (ellStd b L : ℝ) / 2 ≤ 4 * L := by
    have hnat : ellStd b L ≤ 3 * L + 11 := by
      unfold ellStd
      calc Nat.clog 2 (400 * 2 ^ L * b * (9 + 2 * L)) ≤ Nat.clog 2 (2 ^ (3 * L + 11)) := by
            refine Nat.clog_mono_right 2 ?_
            have h1 : 9 + 2 * L ≤ 2 ^ (L + 2) := by
              have := Nat.lt_two_pow_self (n := L)
              rw [pow_add]
              omega
            calc 400 * 2 ^ L * b * (9 + 2 * L) ≤ 2 ^ 9 * 2 ^ L * 2 ^ L * 2 ^ (L + 2) :=
                  Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) hbL) h1
              _ = 2 ^ (3 * L + 11) := by
                  rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
        _ = 3 * L + 11 := Nat.clog_pow 2 _ (by norm_num)
    have : (ellStd b L : ℝ) ≤ 3 * L + 11 := by exact_mod_cast hnat
    linarith
  have hsqrtℓ : Real.sqrt ((ellStd b L : ℝ) / 2) ≤ 2 * Real.sqrt L := by
    calc Real.sqrt ((ellStd b L : ℝ) / 2) ≤ Real.sqrt (4 * L) := Real.sqrt_le_sqrt hℓle
      _ = 2 * Real.sqrt L := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hK : 512 * (b : ℝ) * (9 + 2 * L) * Real.sqrt ((ellStd b L : ℝ) / 2) * L
      ≤ 5120 * (b : ℝ) * orderedLogFactor L := by
    have h1 : (9 + 2 * (L : ℝ)) ≤ 5 * L := by linarith
    have hs0 : 0 ≤ Real.sqrt ((ellStd b L : ℝ) / 2) := Real.sqrt_nonneg _
    have hA : 512 * (b : ℝ) * (9 + 2 * L) ≤ 512 * (b : ℝ) * (5 * L) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hAB : 512 * (b : ℝ) * (9 + 2 * L) * Real.sqrt ((ellStd b L : ℝ) / 2)
        ≤ 512 * (b : ℝ) * (5 * L) * (2 * Real.sqrt L) := mul_le_mul hA hsqrtℓ hs0 (by positivity)
    have hABL := mul_le_mul_of_nonneg_right hAB (by positivity : (0 : ℝ) ≤ L)
    calc 512 * (b : ℝ) * (9 + 2 * L) * Real.sqrt ((ellStd b L : ℝ) / 2) * L
        ≤ 512 * (b : ℝ) * (5 * L) * (2 * Real.sqrt L) * L := hABL
      _ = 5120 * (b : ℝ) * orderedLogFactor L := by unfold orderedLogFactor; ring
  -- `5√L ≤ 4L` for `L ≥ 3`
  have hs : (5 : ℝ) / 4 ≤ Real.sqrt L := by
    rw [show (5 : ℝ) / 4 = Real.sqrt ((5 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsqL : 5 * Real.sqrt L ≤ 4 * L := by
    have h0 : (0 : ℝ) ≤ L := by linarith
    nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (L : ℝ)]
  have hK' : 5120 * (b : ℝ) * orderedLogFactor L ≤ 2 ^ 12 * (b : ℝ) * (L : ℝ) ^ 3 := by
    unfold orderedLogFactor
    have h0 : (0 : ℝ) ≤ (b : ℝ) * (L : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 4 * L - 5 * Real.sqrt L)]
  exact hK.trans hK'

/-- The rank-`1` cost at every depth: `costA b (Pstd b L) 1 j ≤ 2·2^12·b·L³·√2^j`. -/
theorem costA_Pstd_one_le {b L : ℕ} (hb1 : 1 ≤ b) (hL : 3 ≤ L) (hbL : b ≤ 2 ^ L) :
    ∀ j, j ≤ L →
      costA b (Pstd b L) 1 j ≤ 2 * (2 ^ 12 * (b : ℝ) * (L : ℝ) ^ 3) * Real.sqrt 2 ^ j := by
  intro j hj
  have hℓ2 : (2 : ℝ) ≤ ellStd b L := by exact_mod_cast two_le_ellStd (L := L) hb1
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have h := costA_le hb1 (Pstd b L) (R₀ := 9 + 2 * L) (ℓ := (ellStd b L : ℝ) / 2) (by linarith)
    (by linarith) (by omega) (Pstd_fst_le b L) (Pstd_snd_le b L) 1 j hj
  rw [pow_one, sqrt_two_pow] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pstd_factor_le hb1 hL hbL) (by norm_num)) (by positivity)

/-! ## The standard parameters -/

/-- The base of the stage cost: `2^15·b·L^4`. -/
noncomputable def KStd (b L : ℕ) : ℝ := 2 ^ 15 * b * (L : ℝ) ^ 4

lemma two_pow_fifteen_le_KStd {b L : ℕ} (hb1 : 1 ≤ b) (hL1 : 1 ≤ L) : (2 : ℝ) ^ 15 ≤ KStd b L := by
  unfold KStd
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have := one_le_pow₀ (n := 4) hL'
  nlinarith

lemma two_le_KStd {b L : ℕ} (hb1 : 1 ≤ b) (hL1 : 1 ≤ L) : (2 : ℝ) ≤ KStd b L :=
  le_trans (by norm_num) (two_pow_fifteen_le_KStd hb1 hL1)

/-- **The stage costs at the standard parameters**: `costB s j ≤ (2^15·b·L^4)^{s+1}·√2^j`. -/
theorem costB_std_le {b L : ℕ} (hb1 : 1 ≤ b) (hL : 3 ≤ L) (hbL : b ≤ 2 ^ L) :
    ∀ s j, j ≤ L →
      costB b (Pstd b L) (L + 2) (L + 11) s j ≤ KStd b L ^ (s + 1) * Real.sqrt 2 ^ j := by
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  refine costB_le b (Pstd b L) (L + 2) (L + 11) (by omega) (two_le_KStd hb1 (by omega)) ?_ ?_ ?_ ?_
  · unfold KStd
    have h0 : (0 : ℝ) ≤ (b : ℝ) * (L : ℝ) ^ 4 := by positivity
    nlinarith
  · push_cast; linarith
  · push_cast; linarith
  · intro j hj
    unfold costB
    have h := costA_Pstd_one_le hb1 hL hbL j hj
    have hA0 := costA_nonneg b (Pstd b L) 1 j
    push_cast
    unfold KStd
    calc 2 * (((L : ℝ) + 2) * costA b (Pstd b L) 1 j)
        ≤ 2 * ((2 * L) * (2 * (2 ^ 12 * (b : ℝ) * (L : ℝ) ^ 3) * Real.sqrt 2 ^ j)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (by linarith) h hA0 (by positivity)) (by norm_num)
      _ = 2 ^ 15 * (b : ℝ) * (L : ℝ) ^ 4 * Real.sqrt 2 ^ j := by ring

/-- The copy count `L + 2` makes every child failure `≤ 1/400` after the union bound. -/
lemma hc_std (L : ℕ) : ∀ J : ℕ, 2 ^ J ≤ 2 ^ L →
    ((2 : ℝ) ^ (J + 2)) * (1 / 100) ^ (L + 2) ≤ 1 / 400 := by
  intro J hJ
  have hJL : J ≤ L := (Nat.pow_le_pow_iff_right (by norm_num)).1 hJ
  calc (2 : ℝ) ^ (J + 2) * (1 / 100) ^ (L + 2) ≤ 2 ^ (L + 2) * (1 / 100) ^ (L + 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    _ = (1 / 50) ^ (L + 2) := by rw [← mul_pow]; norm_num
    _ ≤ (1 / 50) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ 1 / 400 := by norm_num

/-- The thinning rounds `L + 11` make every thinning failure `≤ 1/400` after the union bound. -/
lemma hR_std (L : ℕ) : ∀ J : ℕ, 2 ^ J ≤ 2 ^ L →
    ((2 : ℝ) ^ (J + 2)) * (1 / 2) ^ (L + 11) ≤ 1 / 400 := by
  intro J hJ
  have hJL : J ≤ L := (Nat.pow_le_pow_iff_right (by norm_num)).1 hJ
  calc (2 : ℝ) ^ (J + 2) * (1 / 2) ^ (L + 11) ≤ 2 ^ (L + 2) * (1 / 2) ^ (L + 11) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    _ = (1 / 2) ^ 9 := by
        rw [show L + 11 = (L + 2) + 9 by ring, pow_add ((1 : ℝ) / 2) (L + 2) 9, ← mul_assoc,
          ← mul_pow]
        norm_num
    _ ≤ 1 / 400 := by norm_num

/-! ## The root cost -/

/-- The root cost at the standard parameters: `8192·(1 + costB) ≤ (2^15·b·L_n^4)^{⌈log₂ b⌉+2}·√n`
(`n ≥ 4`, `1 ≤ b < n`). -/
theorem logrank_root_cost_le {b n : ℕ} (hb1 : 1 ≤ b) (hn4 : 4 ≤ n) (hbn : b < n) :
    uniformExtractionConstant * (1 + costB b (Pstd b (logLen n)) (logLen n + 2) (logLen n + 11)
        (Nat.clog 2 b) (logLen n))
      ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 2) * Real.sqrt n := by
  have hn1 : 1 ≤ n := by omega
  have hL := three_le_logLen hn4
  have hbL : b ≤ 2 ^ logLen n := le_trans hbn.le (le_two_pow_logLen n)
  have hcost := costB_std_le hb1 hL hbL (Nat.clog 2 b) (logLen n) le_rfl
  have hK15 : (2 : ℝ) ^ 15 ≤ KStd b (logLen n) := two_pow_fifteen_le_KStd hb1 (by omega)
  have hK1 : (1 : ℝ) ≤ KStd b (logLen n) := by linarith
  have hKs0 : 0 ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 1) := by positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsqN : Real.sqrt 2 ^ logLen n ≤ Real.sqrt 2 * Real.sqrt n := by
    rw [← sqrt_two_pow]
    have h2 : ((2 : ℝ) ^ logLen n) ≤ 2 * n := by exact_mod_cast two_pow_logLen_le hn1
    calc Real.sqrt ((2 : ℝ) ^ logLen n) ≤ Real.sqrt (2 * n) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt 2 * Real.sqrt n := Real.sqrt_mul (by norm_num) _
  have hsqrt2 : Real.sqrt 2 ≤ 1.415 := by
    rw [show (1.415 : ℝ) = Real.sqrt (1.415 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.2 hn'
  have hKs : (2 : ℝ) ^ 15 ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 1) :=
    hK15.trans (le_self_pow₀ hK1 (by omega))
  have hXn : (2 : ℝ) ^ 15 ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 1) * Real.sqrt n :=
    calc (2 : ℝ) ^ 15 ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 1) := hKs
      _ = KStd b (logLen n) ^ (Nat.clog 2 b + 1) * 1 := (mul_one _).symm
      _ ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 1) * Real.sqrt n :=
          mul_le_mul_of_nonneg_left hsq1 hKs0
  have hcost' : costB b (Pstd b (logLen n)) (logLen n + 2) (logLen n + 11) (Nat.clog 2 b) (logLen n)
      ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 1) * (1.415 * Real.sqrt n) :=
    hcost.trans (mul_le_mul_of_nonneg_left
      (hsqN.trans (mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _))) hKs0)
  calc uniformExtractionConstant * (1 + costB b (Pstd b (logLen n)) (logLen n + 2) (logLen n + 11)
          (Nat.clog 2 b) (logLen n))
      ≤ 8192 * (1 + KStd b (logLen n) ^ (Nat.clog 2 b + 1) * (1.415 * Real.sqrt n)) := by
        rw [uniformExtractionConstant]
        gcongr
    _ ≤ 12288 * (KStd b (logLen n) ^ (Nat.clog 2 b + 1) * Real.sqrt n) := by linarith
    _ ≤ KStd b (logLen n) * (KStd b (logLen n) ^ (Nat.clog 2 b + 1) * Real.sqrt n) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = KStd b (logLen n) ^ (Nat.clog 2 b + 2) * Real.sqrt n := by rw [pow_succ]; ring

/-! ## The theorem -/

section Main

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M)

/-- The bounded-error convention `ε = 1/3` from `ε = 1/10`, for any bound. -/
theorem ordered_qQuery_third_le_of {n : ℕ} {X : ℝ}
    (h : (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ) ≤ X) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ) ≤ X := by
  refine le_trans ?_ h
  have hne : (QueryCounts (X := Fin n → σ) id (fun x => wordProd letter x) (1 / 10)).Nonempty := by
    obtain ⟨A, hA⟩ := exists_computesWithErrorOn (read := (id : (Fin n → σ) → Fin n → σ))
      (f := fun x => wordProd letter x) (fun x y h => congrArg (fun z => wordProd letter z) h)
      (by norm_num : (0 : ℝ) ≤ 1 / 10)
    exact ⟨_, mem_queryCounts hA⟩
  exact_mod_cast qQueryOn_mono (by norm_num) hne

variable (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
include hst hb

open Classical in
/-- **The root summary is correct with probability at least `99/100`**, as a rank-`b` summary
(the rank is `2^{⌈log₂ b⌉} ≥ b`). -/
theorem logrank_hcorr (hb1 : 1 ≤ b) (L : ℕ) {n : ℕ} (x : Fin n → σ) :
    ∑ ω, unifW (Ω2 b (Pstd b L) (L + 2) (L + 11) (Nat.clog 2 b) L) ω
        * (if IsSummary (letterOpt letter) (pad (L := L) x) b b L 0
            (summary2 (letterOpt letter) b (Pstd b L) (L + 2) (L + 11) (Nat.clog 2 b) L 0 ω
              (pad (L := L) x)) then 0 else 1)
      ≤ 1 / 100 := by
  have hb' : IsBreadthBound (letterOpt letter) b := isBreadthBound_letterOpt letter hb
  have h := summary2_correct (letterOpt letter) b hst hb' hb1 (Pstd b L) (L + 2) (L + 11)
    (goodParams_Pstd hb1) (hc_std L) (hR_std L) (Nat.clog 2 b) L 0 (by simp) (pad (L := L) x)
  unfold failMass2 at h
  have hrank : b ≤ 2 ^ Nat.clog 2 b := Nat.le_pow_clog (by norm_num) b
  calc ∑ ω, unifW (Ω2 b (Pstd b L) (L + 2) (L + 11) (Nat.clog 2 b) L) ω
        * (if IsSummary (letterOpt letter) (pad (L := L) x) b b L 0
            (summary2 (letterOpt letter) b (Pstd b L) (L + 2) (L + 11) (Nat.clog 2 b) L 0 ω
              (pad (L := L) x)) then 0 else 1)
      ≤ ∑ ω, unifW (Ω2 b (Pstd b L) (L + 2) (L + 11) (Nat.clog 2 b) L) ω
        * (if IsSummary (letterOpt letter) (pad (L := L) x) b (2 ^ Nat.clog 2 b) L 0
            (summary2 (letterOpt letter) b (Pstd b L) (L + 2) (L + 11) (Nat.clog 2 b) L 0 ω
              (pad (L := L) x)) then 0 else 1) := by
        refine Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left ?_ ((isWeight_unifW _).nonneg ω)
        by_cases h1 : IsSummary (letterOpt letter) (pad (L := L) x) b b L 0
            (summary2 (letterOpt letter) b (Pstd b L) (L + 2) (L + 11) (Nat.clog 2 b) L 0 ω
              (pad (L := L) x))
        · rw [if_pos h1]; split_ifs <;> norm_num
        · rw [if_neg h1, if_neg fun h2 => h1 (IsSummary.mono_rank (letterOpt letter) b h2 hrank)]
    _ ≤ (1 / 100) ^ (L + 2) := h
    _ ≤ (1 / 100) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 100 := pow_one _

open Classical in
/-- **The product-and-core algorithm, quasipolynomial in the breadth**: for `1 ≤ b < n`, a
quantum algorithm with at most `(2^15·b·L_n^4)^{⌈log₂ b⌉+2}·√n` queries returns, with
probability at least `9/10`, a record that is truthful for the (padded) word, has at most `b`
positions and has the word's product. -/
theorem ordered_exists_core_alg_logrank (hb1 : 1 ≤ b) {n : ℕ} (hbn : b < n) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 2) * Real.sqrt n
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · -- `n ≤ 3`: read everything
    obtain ⟨W, hW, hW', B, hgood⟩ := exists_exact_core_alg letter hst hb hb1 (le_two_pow_logLen n)
    refine ⟨W, hW, hW', B, n, ?_, hgood⟩
    have hn1 : 1 ≤ n := by omega
    have hK15 : (2 : ℝ) ^ 15 ≤ KStd b (logLen n) := two_pow_fifteen_le_KStd hb1 (one_le_logLen hn1)
    have hn' : (n : ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
    have hsq1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn1)
    have hKp : (2 : ℝ) ^ 15 ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 2) :=
      hK15.trans (le_self_pow₀ (by linarith) (by omega))
    have h0 : (0 : ℝ) ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 2) := by linarith
    nlinarith
  · obtain ⟨W, hW, hW', B, Q, hQ, hgood⟩ := exists_root_alg_of letter hst hb (le_two_pow_logLen n)
      (fun ω => summary2 (letterOpt letter) b (Pstd b (logLen n)) (logLen n + 2) (logLen n + 11)
        (Nat.clog 2 b) (logLen n) 0 ω)
      (costB_nonneg b (Pstd b (logLen n)) (logLen n + 2) (logLen n + 11) (Nat.clog 2 b) (logLen n))
      (fun ω => hasDual_summary2 (letterOpt letter) b (Pstd b (logLen n)) (logLen n + 2)
        (logLen n + 11) hb1 (Pstd_snd_pos hb1) (Nat.clog 2 b) (logLen n) 0 ω)
      (logrank_hcorr letter hst hb hb1 (logLen n))
    exact ⟨W, hW, hW', B, Q, hQ.trans (logrank_root_cost_le hb1 hn4 hbn), hgood⟩

open Classical in
/-- The main case `1 ≤ b < n`, `n ≥ 4`, of the quasipolynomial product bound. -/
theorem ordered_qQuery_le_logrank_main (hb1 : 1 ≤ b) {n : ℕ} (hn4 : 4 ≤ n) (hbn : b < n) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ KStd b (logLen n) ^ (Nat.clog 2 b + 2) * Real.sqrt n :=
  (qQuery_wordProd_le_root_of letter hst hb (le_two_pow_logLen n)
    (fun ω => summary2 (letterOpt letter) b (Pstd b (logLen n)) (logLen n + 2) (logLen n + 11)
      (Nat.clog 2 b) (logLen n) 0 ω)
    (costB_nonneg b (Pstd b (logLen n)) (logLen n + 2) (logLen n + 11) (Nat.clog 2 b) (logLen n))
    (fun ω => hasDual_summary2 (letterOpt letter) b (Pstd b (logLen n)) (logLen n + 2)
      (logLen n + 11) hb1 (Pstd_snd_pos hb1) (Nat.clog 2 b) (logLen n) 0 ω)
    (logrank_hcorr letter hst hb hb1 (logLen n))).trans (logrank_root_cost_le hb1 hn4 hbn)

end Main

/-! ## The discrete bound for every `n` and `b` -/

/-- The quasipolynomial bound in discrete form: `(2^15·(b+2)·L_n^4)^{⌈log₂(b+2)⌉+2}·√n`. -/
noncomputable def logRankBound (b n : ℕ) : ℝ :=
  (2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4) ^ (Nat.clog 2 (b + 2) + 2) * Real.sqrt n

lemma one_le_logRankBase {b n : ℕ} (hn1 : 1 ≤ n) :
    (1 : ℝ) ≤ 2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4 := by
  have hL' : (1 : ℝ) ≤ logLen n := by exact_mod_cast one_le_logLen hn1
  have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast Nat.zero_le b
  have := one_le_pow₀ (n := 4) hL'
  nlinarith

/-- The main-case bound is at most the discrete bound. -/
lemma KStd_pow_le_logRankBound {b n : ℕ} (hn1 : 1 ≤ n) :
    KStd b (logLen n) ^ (Nat.clog 2 b + 2) * Real.sqrt n ≤ logRankBound b n := by
  unfold logRankBound
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  have hY1 := one_le_logRankBase (b := b) hn1
  have hKY : KStd b (logLen n) ≤ 2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4 := by
    unfold KStd
    have h0 : (0 : ℝ) ≤ (logLen n : ℝ) ^ 4 := by positivity
    nlinarith
  have hK0 : 0 ≤ KStd b (logLen n) := by unfold KStd; positivity
  calc KStd b (logLen n) ^ (Nat.clog 2 b + 2)
      ≤ (2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4) ^ (Nat.clog 2 b + 2) :=
        pow_le_pow_left₀ hK0 hKY _
    _ ≤ (2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4) ^ (Nat.clog 2 (b + 2) + 2) :=
        pow_le_pow_right₀ hY1 (by
          have := Nat.clog_mono_right 2 (by omega : b ≤ b + 2); omega)

section Discrete

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
include hst hb

/-- **The quasipolynomial product bound, discrete form**:
`Q_{1/10}(wordProd) ≤ min { n, (2^15·(b+2)·L_n^4)^{⌈log₂(b+2)⌉+2}·√n }` for every `n`, `b`. -/
theorem ordered_qQuery_le_logrank (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) (logRankBound b n) := by
  have hread := qQuery_wordProd_le_length letter n (by norm_num : (0 : ℝ) ≤ 1 / 10)
  refine le_min (by exact_mod_cast hread) ?_
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · rw [qQuery_wordProd_zero_breadth letter hb n (by norm_num)]
    unfold logRankBound
    push_cast
    positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [qQuery_wordProd_zero_length letter (by norm_num)]
    simp only [Nat.cast_zero]
    unfold logRankBound
    positivity
  by_cases hmain : 4 ≤ n ∧ b < n
  · exact (ordered_qQuery_le_logrank_main letter hst hb hb1 hmain.1 hmain.2).trans
      (KStd_pow_le_logRankBound hn1)
  · -- `n ≤ 3` or `n ≤ b`: reading everything is within the bound
    refine le_trans (b := (n : ℝ)) (by exact_mod_cast hread) ?_
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
      have hnb : n ≤ 3 ∨ n ≤ b := by omega
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

end Discrete

/-! ## The paper's form: natural logarithms, real exponent, one constant -/

lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at this ⊢
  linarith

/-- `⌈log₂ m⌉ ≤ 4·log m` for `m ≥ 2`. -/
lemma clog_two_le_four_log {m : ℕ} (hm : 2 ≤ m) : (Nat.clog 2 m : ℝ) ≤ 4 * Real.log m := by
  have hk1 : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num) (by omega)
  have hlt : 2 ^ (Nat.clog 2 m - 1) < m := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := m) (by omega)
    rwa [Nat.pred_eq_sub_one] at this
  have hlt' : (2 : ℝ) ^ (Nat.clog 2 m - 1) < m := by exact_mod_cast hlt
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : ((Nat.clog 2 m : ℝ) - 1) * Real.log 2 < Real.log m := by
    have := Real.log_lt_log (by positivity) hlt'
    rw [Real.log_pow] at this
    have hcast : ((Nat.clog 2 m - 1 : ℕ) : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
      rw [Nat.cast_sub hk1]; simp
    rwa [hcast] at this
  have hlogm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm'
  have h2 := half_le_log_two
  have hk' : (1 : ℝ) ≤ Nat.clog 2 m := by exact_mod_cast hk1
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (Nat.clog 2 m : ℝ) - 1)
    (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 2)]

/-- **The universal constant of the quasipolynomial bound**: `2^17`. -/
def quasipolyConstant : ℝ := 2 ^ 17

/-- The paper's bound `√(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)}` with `C = 2^17`. -/
noncomputable def quasipolyBound (b n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) + 1)
    * (quasipolyConstant * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2))
      ^ (quasipolyConstant * Real.log ((b : ℝ) + 2))

/-- **The discrete bound is at most the paper's bound.** -/
theorem logRankBound_le_quasipolyBound (b n : ℕ) : logRankBound b n ≤ quasipolyBound b n := by
  unfold logRankBound quasipolyBound quasipolyConstant
  have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast Nat.zero_le b
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hlogn : (logLen n : ℝ) ≤ 4 * Real.log ((n : ℝ) + 2) := by
    have h1 : (logLen n : ℝ) ≤ (Nat.clog 2 (n + 2) : ℝ) := by
      exact_mod_cast Nat.clog_mono_right 2 (by omega : n + 1 ≤ n + 2)
    have h2 := clog_two_le_four_log (m := n + 2) (by omega)
    push_cast at h2
    linarith
  have hlogb : (Nat.clog 2 (b + 2) : ℝ) ≤ 4 * Real.log ((b : ℝ) + 2) := by
    have := clog_two_le_four_log (m := b + 2) (by omega)
    push_cast at this
    exact this
  have hlog2b : (1 : ℝ) / 2 ≤ Real.log ((b : ℝ) + 2) :=
    half_le_log_two.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlog2n : (1 : ℝ) / 2 ≤ Real.log ((n : ℝ) + 2) :=
    half_le_log_two.trans (Real.log_le_log (by norm_num) (by linarith))
  have hB1 : (1 : ℝ) ≤ 2 ^ 17 * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2) := by nlinarith
  have hL0 : (0 : ℝ) ≤ logLen n := by positivity
  have hA1 : (1 : ℝ) ≤ 2 ^ 15 * ((b : ℝ) + 2) := by nlinarith
  have h1 : (2 : ℝ) ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ)
      ≤ 2 ^ 17 * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2) := by
    calc (2 : ℝ) ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ)
        ≤ 2 ^ 15 * ((b : ℝ) + 2) * (4 * Real.log ((n : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hlogn (by positivity)
      _ = 2 ^ 17 * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2) := by ring
  have hY : 2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4
      ≤ (2 ^ 17 * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ 4 := by
    calc 2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4
        ≤ (2 ^ 15 * ((b : ℝ) + 2)) ^ 4 * (logLen n : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right (le_self_pow₀ hA1 (by norm_num)) (by positivity)
      _ = (2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ)) ^ 4 := by ring
      _ ≤ (2 ^ 17 * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) h1 4
  have hexp : ((4 * (Nat.clog 2 (b + 2) + 2) : ℕ) : ℝ) ≤ 2 ^ 17 * Real.log ((b : ℝ) + 2) := by
    push_cast
    nlinarith
  have hsq : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  calc (2 ^ 15 * ((b : ℝ) + 2) * (logLen n : ℝ) ^ 4) ^ (Nat.clog 2 (b + 2) + 2) * Real.sqrt n
      ≤ ((2 ^ 17 * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ^ 4) ^ (Nat.clog 2 (b + 2) + 2)
          * Real.sqrt ((n : ℝ) + 1) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hY _) hsq (Real.sqrt_nonneg _)
          (by positivity)
    _ = (2 ^ 17 * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2))
          ^ (((4 * (Nat.clog 2 (b + 2) + 2) : ℕ) : ℝ)) * Real.sqrt ((n : ℝ) + 1) := by
        rw [Real.rpow_natCast, ← pow_mul]
    _ ≤ (2 ^ 17 * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2))
          ^ (2 ^ 17 * Real.log ((b : ℝ) + 2)) * Real.sqrt ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hB1 hexp)
          (Real.sqrt_nonneg _)
    _ = Real.sqrt ((n : ℝ) + 1) * (2 ^ 17 * ((b : ℝ) + 2) * Real.log ((n : ℝ) + 2))
          ^ (2 ^ 17 * Real.log ((b : ℝ) + 2)) := mul_comm _ _

section Quasipoly

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
include hst hb

/-- **The quasipolynomial ordered product theorem** (`thm:ordered-beta-log-product`):
`Q_{1/10}(wordProd) ≤ min { n, √(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)} }` with `C = 2^17`. -/
theorem ordered_qQuery_le_quasipoly (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) (quasipolyBound b n) :=
  (ordered_qQuery_le_logrank letter hst hb n).trans
    (min_le_min_left _ (logRankBound_le_quasipolyBound b n))

/-- The bounded-error convention `ε = 1/3`. -/
theorem ordered_qQuery_third_le_quasipoly (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (quasipolyBound b n) :=
  ordered_qQuery_third_le_of letter (ordered_qQuery_le_quasipoly letter hst hb n)

/-- The discrete form in the convention `ε = 1/3`. -/
theorem ordered_qQuery_third_le_logrank (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (logRankBound b n) :=
  ordered_qQuery_third_le_of letter (ordered_qQuery_le_logrank letter hst hb n)

open Classical in
/-- **The product-and-core algorithm within the paper's bound**: for `1 ≤ b < n`, at most
`√(n+1)·(C(b+2)·log(n+2))^{C·log(b+2)}` queries, a good record with probability `≥ 9/10`. -/
theorem ordered_exists_core_alg_quasipoly (hb1 : 1 ≤ b) {n : ℕ} (hbn : b < n) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ quasipolyBound b n
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  obtain ⟨W, hW, hW', B, Q, hQ, hgood⟩ := ordered_exists_core_alg_logrank letter hst hb hb1 hbn
  exact ⟨W, hW, hW', B, Q, hQ.trans ((KStd_pow_le_logRankBound (by omega)).trans
    (logRankBound_le_quasipolyBound b n)), hgood⟩

end Quasipoly

/-- **The `breadth` form**: with `b = β(letter)` whenever some breadth bound exists. -/
theorem ordered_qQuery_le_quasipoly_breadth {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M]
    [PartialOrder M] [DecidableEq M] (letter : σ → M) (hst : IsStableOrder M)
    (hex : ∃ b, IsBreadthBound letter b) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (quasipolyBound (breadth letter) n) :=
  ordered_qQuery_third_le_quasipoly letter hst (isBreadthBound_breadth hex) n

end MonoidProduct
