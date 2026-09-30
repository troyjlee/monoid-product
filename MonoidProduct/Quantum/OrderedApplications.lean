import MonoidProduct.Ordered.Root
import QuantumQueryComplexity.Quantum.ReadAll
import Mathlib.Analysis.Complex.Exponential

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The ordered product theorem (`monoid.tex` `thm:ordered-beta-product`)

For a finite alphabet `σ`, a monoid `M` with a stable partial order (`IsStableOrder M`)
and a breadth bound `b` (`IsBreadthBound letter b`), the ordered product of a word of
length `n` has bounded-error quantum query complexity

  `Q_{1/10}(wordProd) ≤ min { n, (2^27·b)^b · √n · L_n^(3b) }`,  `L_n = ⌈log₂(n+1)⌉`

(`ordered_qQuery_le`), and with the square root of the recurrence retained

  `Q_{1/10}(wordProd) ≤ min { n, (2^27·b)^b · √n · L_n^(5b/2) }`

(`ordered_qQuery_le_five_halves`, `L_n^(5b/2)` written `(L_n²·√L_n)^b =: orderedLogFactor`;
real-power form `ordered_qQuery_le_rpow`); a quantum algorithm with that many queries returns, with
probability at least `9/10`, a truthful record of at most `b` positions whose product is
the word's product (`ordered_exists_core_alg`).  The constant is universal: it is fixed
before the alphabet, the monoid, the order, `b` and `n`.

The merger parameters are `⌈log₂(400·2^L·h)⌉` rounds and `2·h·⌈log₂(400·2^L·b·(9+2L))⌉`
proposals per draw at node count `h` (`Pstd`); `goodParams_Pstd` discharges the
small-mass hypothesis at threshold `1/(2h)` with base-`2` estimates only
(`(1 − 1/(2h))^(2h) ≤ e^{−1} ≤ 1/2`), and `costA_Pstd_le` bounds the solved recurrence by
`2·(2^12·b·L^3)^b·√(2^L)` for `L ≥ 3`.  Lengths `n ≤ 3` use the exact read-all algorithm.

Constant ledger (`b ≥ 1`, `L ≥ 3`): per rank `512·b·(9+2L)·√(ℓ/2)·L ≤ 5120·b·L²√L`
(`≤ 2^12·b·L^3` after `5√L ≤ 4L`); at the root `8192·(1 + 2·X·√(2^L)) ≤ 23185·X·√n` with
`2^L ≤ 2n`; and `23185·5120 ≤ 2^27`, so both exponents share the constant `2^27`.  `2^26`
fails at `b = 1` by a fraction of a percent.

Specialisations: `breadth` (`ordered_qQuery_le_breadth`, `_five_halves`).  The strict
stock instance is `Quantum/StrictStockApplications.lean`.
-/

namespace MonoidProduct

open Finset QuantumQueryComplexity

/-! ## Ceiling logarithms -/

/-- `clog₂ x > y` as soon as `x > 2^y`. -/
lemma lt_clog_of_pow_lt {x y : ℕ} (h : 2 ^ y < x) : y < Nat.clog 2 x := by
  by_contra hc
  push_neg at hc
  have h1 := Nat.le_pow_clog (b := 2) (by norm_num) x
  have h2 : 2 ^ Nat.clog 2 x ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) hc
  omega

/-! ## The standard parameters -/

/-- `ℓ_L = ⌈log₂(400·2^L·b·(9+2L))⌉`. -/
def ellStd (b L : ℕ) : ℕ := Nat.clog 2 (400 * 2 ^ L * b * (9 + 2 * L))

/-- **The standard merger parameters** at length `2^L`: `⌈log₂(400·2^L·h)⌉` rounds and
`2·h·ℓ_L` proposals per draw at node count `h`. -/
def Pstd (b L : ℕ) : MParams := fun h => (Nat.clog 2 (400 * 2 ^ L * h), 2 * h * ellStd b L)

lemma two_le_ellStd {b L : ℕ} (hb1 : 1 ≤ b) : 2 ≤ ellStd b L := by
  unfold ellStd
  have h1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have h2 : 400 * 1 * 1 * 9 ≤ 400 * 2 ^ L * b * (9 + 2 * L) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) hb1) (by omega)
  exact lt_clog_of_pow_lt (by omega)

lemma Pstd_snd_pos {b L : ℕ} (hb1 : 1 ≤ b) : ∀ h, 1 ≤ h → 1 ≤ (Pstd b L h).2 := by
  intro h hh
  show 1 ≤ 2 * h * ellStd b L
  have := two_le_ellStd (L := L) hb1
  nlinarith

lemma Pstd_fst_le (b L : ℕ) : ∀ h, 1 ≤ h → h ≤ 2 ^ L → ((Pstd b L h).1 : ℝ) ≤ 9 + 2 * L := by
  intro h _ hh
  show ((Nat.clog 2 (400 * 2 ^ L * h) : ℕ) : ℝ) ≤ 9 + 2 * L
  have hle : Nat.clog 2 (400 * 2 ^ L * h) ≤ 9 + 2 * L := by
    calc Nat.clog 2 (400 * 2 ^ L * h) ≤ Nat.clog 2 (2 ^ (9 + 2 * L)) := by
          refine Nat.clog_mono_right 2 ?_
          calc 400 * 2 ^ L * h ≤ 2 ^ 9 * 2 ^ L * 2 ^ L :=
                Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) hh
            _ = 2 ^ (9 + 2 * L) := by rw [← pow_add, ← pow_add]; congr 1; ring
      _ = 9 + 2 * L := Nat.clog_pow 2 _ (by norm_num)
  exact_mod_cast hle

/-- The proposal count in the form `4·h·ℓ'` with `ℓ' = ℓ_L/2`. -/
lemma Pstd_snd_le (b L : ℕ) :
    ∀ h, 1 ≤ h → h ≤ 2 ^ L → ((Pstd b L h).2 : ℝ) ≤ 4 * (h : ℝ) * ((ellStd b L : ℝ) / 2) := by
  intro h _ _
  show ((2 * h * ellStd b L : ℕ) : ℝ) ≤ _
  push_cast
  exact le_of_eq (by ring)

/-- **The parameter hypothesis holds** for the standard parameters. -/
theorem goodParams_Pstd {b L : ℕ} (hb1 : 1 ≤ b) : GoodParams b (2 ^ L) (Pstd b L) := by
  intro h hh1 hhN
  push_cast
  have hN : (0 : ℝ) < 2 ^ L := by positivity
  have hh : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hb : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hRdef : (Pstd b L h).1 = Nat.clog 2 (400 * 2 ^ L * h) := rfl
  have hkdef : (Pstd b L h).2 = 2 * h * ellStd b L := rfl
  rw [hRdef, hkdef]
  -- the first term: `2h / 2^R ≤ 1/(200·2^L)`
  have h2R : (400 * 2 ^ L * h : ℝ) ≤ 2 ^ Nat.clog 2 (400 * 2 ^ L * h) := by
    have := Nat.le_pow_clog (b := 2) (by norm_num) (400 * 2 ^ L * h)
    exact_mod_cast this
  have ht1 : (1 / 2 : ℝ) ^ Nat.clog 2 (400 * 2 ^ L * h) / (1 / (2 * (h : ℝ)))
      ≤ 1 / (200 * (2 : ℝ) ^ L) := by
    have e : (1 / 2 : ℝ) ^ Nat.clog 2 (400 * 2 ^ L * h) / (1 / (2 * (h : ℝ)))
        = 2 * h / 2 ^ Nat.clog 2 (400 * 2 ^ L * h) := by
      rw [one_div_pow]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  -- the second term: `R·2b·(1 − 1/(2h))^(2hℓ) ≤ 1/(200·2^L)`
  have hR0 : ((Nat.clog 2 (400 * 2 ^ L * h) : ℕ) : ℝ) ≤ 9 + 2 * L := Pstd_fst_le b L h hh1 hhN
  have hbase0 : (0 : ℝ) ≤ 1 - 1 / (2 * (h : ℝ)) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have hbase : (1 - 1 / (2 * (h : ℝ))) ^ (2 * h) ≤ 1 / 2 := by
    have h1 := Real.one_sub_div_pow_le_exp_neg (n := 2 * h) (t := 1) (by push_cast; linarith)
    push_cast at h1
    refine h1.trans ?_
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp 1])
  have h2ℓ : (400 * 2 ^ L * b * (9 + 2 * L) : ℝ) ≤ 2 ^ ellStd b L := by
    have := Nat.le_pow_clog (b := 2) (by norm_num) (400 * 2 ^ L * b * (9 + 2 * L))
    unfold ellStd
    exact_mod_cast this
  have hpow : (1 - 1 / (2 * (h : ℝ))) ^ (2 * h * ellStd b L) ≤ 1 / 2 ^ ellStd b L := by
    rw [pow_mul, ← one_div_pow]
    exact pow_le_pow_left₀ (pow_nonneg hbase0 _) hbase _
  have ht2 : ((Nat.clog 2 (400 * 2 ^ L * h) : ℕ) : ℝ) * (2 * (b : ℝ))
      * (1 - 1 / (2 * (h : ℝ))) ^ (2 * h * ellStd b L) ≤ 1 / (200 * (2 : ℝ) ^ L) := by
    have hA : ((Nat.clog 2 (400 * 2 ^ L * h) : ℕ) : ℝ) * (2 * (b : ℝ))
        ≤ (9 + 2 * L) * (2 * (b : ℝ)) := mul_le_mul_of_nonneg_right hR0 (by positivity)
    have hB : (1 - 1 / (2 * (h : ℝ))) ^ (2 * h * ellStd b L)
        ≤ 1 / (400 * 2 ^ L * b * (9 + 2 * L) : ℝ) :=
      hpow.trans (one_div_le_one_div_of_le (by positivity) h2ℓ)
    calc ((Nat.clog 2 (400 * 2 ^ L * h) : ℕ) : ℝ) * (2 * (b : ℝ))
          * (1 - 1 / (2 * (h : ℝ))) ^ (2 * h * ellStd b L)
        ≤ (9 + 2 * L) * (2 * (b : ℝ)) * (1 / (400 * 2 ^ L * b * (9 + 2 * L) : ℝ)) :=
          mul_le_mul hA hB (pow_nonneg hbase0 _) (by positivity)
      _ = 1 / (200 * (2 : ℝ) ^ L) := by field_simp; ring
  have hsum : (1 : ℝ) / (200 * (2 : ℝ) ^ L) + 1 / (200 * (2 : ℝ) ^ L) = 1 / (100 * (2 : ℝ) ^ L) := by
    field_simp; ring
  linarith

/-! ## The solved recurrence at the standard parameters -/

/-- `L^{5/2}` without real powers: `L² · √L`. -/
noncomputable def orderedLogFactor (L : ℕ) : ℝ := (L : ℝ) ^ 2 * Real.sqrt L

lemma orderedLogFactor_nonneg (L : ℕ) : 0 ≤ orderedLogFactor L := by
  unfold orderedLogFactor; positivity

lemma nine_le_orderedLogFactor {L : ℕ} (hL : 3 ≤ L) : 9 ≤ orderedLogFactor L := by
  unfold orderedLogFactor
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hs : (1 : ℝ) ≤ Real.sqrt L := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  nlinarith

lemma one_le_orderedLogFactor {L : ℕ} (hL : 1 ≤ L) : 1 ≤ orderedLogFactor L := by
  unfold orderedLogFactor
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hs : (1 : ℝ) ≤ Real.sqrt L := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL'
  nlinarith

/-- `(L² √L)^b = L^{5b/2}` for `L > 0`; the exponent is a real number. -/
lemma orderedLogFactor_pow_eq_rpow {L : ℕ} (hL : 0 < L) (b : ℕ) :
    orderedLogFactor L ^ b = (L : ℝ) ^ ((5 : ℝ) * b / 2) := by
  have hx : (0 : ℝ) < L := by exact_mod_cast hL
  have h1 : orderedLogFactor L = (L : ℝ) ^ ((5 : ℝ) / 2) := by
    unfold orderedLogFactor
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hx]
    norm_num
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- `(L² √L)^4 = L^10`. -/
lemma orderedLogFactor_pow_four (L : ℕ) : orderedLogFactor L ^ 4 = (L : ℝ) ^ 10 := by
  unfold orderedLogFactor
  have h0 : (0 : ℝ) ≤ L := by positivity
  have hs : Real.sqrt (L : ℝ) ^ 4 = (L : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt h0]
  rw [mul_pow, hs]
  ring

/-- **The solved recurrence with the square root retained**:
`costA ≤ 2·(5120·b·L²√L)^b·√(2^L)` whenever `3 ≤ L` and `b ≤ 2^L`. -/
theorem costA_Pstd_le_sqrt {b L : ℕ} (hb1 : 1 ≤ b) (hL : 3 ≤ L) (hbL : b ≤ 2 ^ L) :
    costA b (Pstd b L) b L
      ≤ 2 * (5120 * (b : ℝ) * orderedLogFactor L) ^ b * Real.sqrt ((2 : ℝ) ^ L) := by
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hℓ2 : (2 : ℝ) ≤ ellStd b L := by exact_mod_cast two_le_ellStd (L := L) hb1
  have h := costA_le hb1 (Pstd b L) (R₀ := 9 + 2 * L) (ℓ := (ellStd b L : ℝ) / 2) (by linarith)
    (by linarith) (by omega) (Pstd_fst_le b L) (Pstd_snd_le b L) b L le_rfl
  refine h.trans ?_
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
  have hK0 : (0 : ℝ) ≤ 512 * (b : ℝ) * (9 + 2 * L) * Real.sqrt ((ellStd b L : ℝ) / 2) * L := by
    positivity
  have hs2 : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ L) := Real.sqrt_nonneg _
  have hp := pow_le_pow_left₀ hK0 hK b
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hs2

/-- `costA ≤ 2·(2^12·b·L^3)^b·√(2^L)` whenever `3 ≤ L` and `b ≤ 2^L` (the cubic form, from
`5√L ≤ 4L`). -/
theorem costA_Pstd_le {b L : ℕ} (hb1 : 1 ≤ b) (hL : 3 ≤ L) (hbL : b ≤ 2 ^ L) :
    costA b (Pstd b L) b L
      ≤ 2 * (2 ^ 12 * (b : ℝ) * (L : ℝ) ^ 3) ^ b * Real.sqrt ((2 : ℝ) ^ L) := by
  refine (costA_Pstd_le_sqrt hb1 hL hbL).trans ?_
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  -- `5√L ≤ 4L` for `L ≥ 3` (indeed for `L ≥ 25/16`)
  have hs : (5 : ℝ) / 4 ≤ Real.sqrt L := by
    rw [show (5 : ℝ) / 4 = Real.sqrt ((5 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsqL : 5 * Real.sqrt L ≤ 4 * L := by
    have h0 : (0 : ℝ) ≤ L := by linarith
    nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (L : ℝ)]
  have hK : 5120 * (b : ℝ) * orderedLogFactor L ≤ 2 ^ 12 * (b : ℝ) * (L : ℝ) ^ 3 := by
    unfold orderedLogFactor
    have h0 : (0 : ℝ) ≤ (b : ℝ) * (L : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 4 * L - 5 * Real.sqrt L)]
  have hK0 : (0 : ℝ) ≤ 5120 * (b : ℝ) * orderedLogFactor L := by
    have := orderedLogFactor_nonneg L; positivity
  have hs2 : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ L) := Real.sqrt_nonneg _
  have hp := pow_le_pow_left₀ hK0 hK b
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hs2

/-! ## The length parameter -/

/-- `L_n = ⌈log₂(n+1)⌉`, so that `n < 2^{L_n} ≤ 2n`. -/
abbrev logLen (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

lemma one_le_logLen {n : ℕ} (hn : 1 ≤ n) : 1 ≤ logLen n :=
  Nat.clog_pos (by norm_num) (by omega)

lemma three_le_logLen {n : ℕ} (hn : 4 ≤ n) : 3 ≤ logLen n :=
  lt_clog_of_pow_lt (by omega)

lemma le_two_pow_logLen (n : ℕ) : n ≤ 2 ^ logLen n :=
  le_trans (Nat.le_succ n) (Nat.le_pow_clog (by norm_num) (n + 1))

lemma two_pow_logLen_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ logLen n ≤ 2 * n := by
  have h : 2 ^ (logLen n - 1) < n + 1 := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n + 1) (by omega)
    rwa [Nat.pred_eq_sub_one] at this
  have hL := one_le_logLen hn
  have e : 2 ^ logLen n = 2 * 2 ^ (logLen n - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- The bound is at least `2^27·b`, hence at least any `n ≤ 2^27·b` (`n, b ≥ 1`). -/
lemma le_orderedBound {n b : ℕ} (hn1 : 1 ≤ n) (hb1 : 1 ≤ b) (h : (n : ℝ) ≤ 2 ^ 27 * b) :
    (n : ℝ) ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * (logLen n : ℝ) ^ (3 * b) := by
  have hL' : (1 : ℝ) ≤ logLen n := by exact_mod_cast one_le_logLen hn1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have h1 : (2 ^ 27 * (b : ℝ)) ≤ (2 ^ 27 * (b : ℝ)) ^ b := le_self_pow₀ (by linarith) (by omega)
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn'
  have hL3 : (1 : ℝ) ≤ (logLen n : ℝ) ^ (3 * b) := one_le_pow₀ hL'
  have hX0 : (0 : ℝ) ≤ (2 ^ 27 * (b : ℝ)) ^ b := by positivity
  calc (n : ℝ) ≤ (2 ^ 27 * (b : ℝ)) ^ b := by linarith
    _ = (2 ^ 27 * (b : ℝ)) ^ b * 1 * 1 := by ring
    _ ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * (logLen n : ℝ) ^ (3 * b) := by gcongr

/-- The fallback estimate with any factor `G ≥ 1`. -/
lemma le_orderedBound' {n b : ℕ} (hn1 : 1 ≤ n) (hb1 : 1 ≤ b) (h : (n : ℝ) ≤ 2 ^ 27 * b)
    {G : ℝ} (hG : 1 ≤ G) :
    (n : ℝ) ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * G := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have h1 : (2 ^ 27 * (b : ℝ)) ≤ (2 ^ 27 * (b : ℝ)) ^ b := le_self_pow₀ (by linarith) (by omega)
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn'
  have hX0 : (0 : ℝ) ≤ (2 ^ 27 * (b : ℝ)) ^ b := by positivity
  calc (n : ℝ) ≤ (2 ^ 27 * (b : ℝ)) ^ b := by linarith
    _ = (2 ^ 27 * (b : ℝ)) ^ b * 1 * 1 := by ring
    _ ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * G := by gcongr

/-! ## The theorem -/

section Main

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M)

/-- Reading every letter: `Q_ε(wordProd) ≤ n`. -/
theorem qQuery_wordProd_le_length (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → σ => wordProd letter x) ε ≤ n := by
  have h := qQueryOn_le_card (read := (id : (Fin n → σ) → Fin n → σ))
    (f := fun x => wordProd letter x) (fun x y h => congrArg (fun z => wordProd letter z) h) hε
  rwa [Fintype.card_fin] at h

/-- Zero letters: no queries. -/
theorem qQuery_wordProd_zero_length {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin 0 → σ => wordProd letter x) ε = 0 :=
  qQueryOn_const_eq_zero id (c := wordProd letter (fun i : Fin 0 => i.elim0))
    (fun x => congrArg _ (funext fun i => i.elim0)) hε

/-- Breadth bound `0`: the product is the identity and no queries are needed. -/
theorem qQuery_wordProd_zero_breadth (hb : IsBreadthBound letter 0) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → σ => wordProd letter x) ε = 0 :=
  qQueryOn_const_eq_zero id (c := 1) (fun x => by
    obtain ⟨D, hD, hcore⟩ := hb n x
    rw [← hcore, Finset.card_eq_zero.1 (Nat.le_zero.1 hD), subwordProd_empty]) hε

variable (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
include hst hb

/-- The root cost at the standard parameters, in the paper's shape (`n ≥ 4`). -/
theorem root_cost_le (hb1 : 1 ≤ b) {n : ℕ} (hn4 : 4 ≤ n) (hbn : b < n) :
    uniformExtractionConstant * (1 + costA b (Pstd b (logLen n)) b (logLen n))
      ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * (logLen n : ℝ) ^ (3 * b) := by
  have hn1 : 1 ≤ n := by omega
  have hL := three_le_logLen hn4
  have hbL : b ≤ 2 ^ logLen n := le_trans hbn.le (le_two_pow_logLen n)
  have hc := costA_Pstd_le hb1 hL hbL
  have hL' : (1 : ℝ) ≤ logLen n := by exact_mod_cast one_le_logLen hn1
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  -- `√(2^L) ≤ √2·√n`
  have hsqN : Real.sqrt ((2 : ℝ) ^ logLen n) ≤ Real.sqrt 2 * Real.sqrt n := by
    have h2 : ((2 : ℝ) ^ logLen n) ≤ 2 * n := by exact_mod_cast two_pow_logLen_le hn1
    calc Real.sqrt ((2 : ℝ) ^ logLen n) ≤ Real.sqrt (2 * n) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt 2 * Real.sqrt n := Real.sqrt_mul (by norm_num) _
  have hsqrt2 : Real.sqrt 2 ≤ 1.415 := by
    rw [show (1.415 : ℝ) = Real.sqrt (1.415 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hX : (4096 : ℝ) ≤ (2 ^ 12 * (b : ℝ) * (logLen n : ℝ) ^ 3) ^ b := by
    have h1 : (4096 : ℝ) ≤ 2 ^ 12 * (b : ℝ) * (logLen n : ℝ) ^ 3 := by
      have := one_le_pow₀ (n := 3) hL'
      nlinarith
    exact le_trans h1 (le_self_pow₀ (by linarith) (by omega))
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn'
  have hX0 : (0 : ℝ) ≤ (2 ^ 12 * (b : ℝ) * (logLen n : ℝ) ^ 3) ^ b := by positivity
  have hXs : (2 ^ 12 * (b : ℝ) * (logLen n : ℝ) ^ 3) ^ b * Real.sqrt ((2 : ℝ) ^ logLen n)
      ≤ (2 ^ 12 * (b : ℝ) * (logLen n : ℝ) ^ 3) ^ b * (1.415 * Real.sqrt n) :=
    mul_le_mul_of_nonneg_left (hsqN.trans (mul_le_mul_of_nonneg_right hsqrt2 (by positivity)))
      hX0
  have h1X : (4096 : ℝ) ≤ (2 ^ 12 * (b : ℝ) * (logLen n : ℝ) ^ 3) ^ b * Real.sqrt n := by
    nlinarith
  calc uniformExtractionConstant * (1 + costA b (Pstd b (logLen n)) b (logLen n))
      ≤ 8192 * (1 + 2 * (2 ^ 12 * (b : ℝ) * (logLen n : ℝ) ^ 3) ^ b
          * Real.sqrt ((2 : ℝ) ^ logLen n)) := by
        rw [uniformExtractionConstant]
        gcongr
    _ ≤ 8192 * (4 * ((2 ^ 12 * (b : ℝ) * (logLen n : ℝ) ^ 3) ^ b * Real.sqrt n)) := by
        nlinarith
    _ = 2 ^ 15 * (2 ^ 12 * (b : ℝ)) ^ b * (logLen n : ℝ) ^ (3 * b) * Real.sqrt n := by
        rw [mul_pow, ← pow_mul]; ring
    _ ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * (logLen n : ℝ) ^ (3 * b) := by
        have e : ((2 : ℝ) ^ 27 * b) ^ b = (2 ^ 15) ^ b * (2 ^ 12 * (b : ℝ)) ^ b := by
          rw [← mul_pow]; congr 1; ring
        have h15 : ((2 : ℝ) ^ 15) ≤ ((2 : ℝ) ^ 15) ^ b := le_self_pow₀ (by norm_num) (by omega)
        rw [e]
        have hpos : 0 ≤ (2 ^ 12 * (b : ℝ)) ^ b * (logLen n : ℝ) ^ (3 * b) * Real.sqrt n := by
          positivity
        nlinarith

/-- **The root cost with the square root retained**: `≤ (2^27·b)^b·√n·L^{5b/2}` (`n ≥ 4`).
Ledger: `8192·(1 + 2X√(2^L)) ≤ 8192·(2·1.415 + 2^{-13})·X√n ≤ 23185·X√n` and
`23185·5120 ≤ 2^27`. -/
theorem root_cost_le_five_halves (hb1 : 1 ≤ b) {n : ℕ} (hn4 : 4 ≤ n) (hbn : b < n) :
    uniformExtractionConstant * (1 + costA b (Pstd b (logLen n)) b (logLen n))
      ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * orderedLogFactor (logLen n) ^ b := by
  have hn1 : 1 ≤ n := by omega
  have hL := three_le_logLen hn4
  have hbL : b ≤ 2 ^ logLen n := le_trans hbn.le (le_two_pow_logLen n)
  have hc := costA_Pstd_le_sqrt hb1 hL hbL
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hF9 : (9 : ℝ) ≤ orderedLogFactor (logLen n) := nine_le_orderedLogFactor hL
  have hsqN : Real.sqrt ((2 : ℝ) ^ logLen n) ≤ Real.sqrt 2 * Real.sqrt n := by
    have h2 : ((2 : ℝ) ^ logLen n) ≤ 2 * n := by exact_mod_cast two_pow_logLen_le hn1
    calc Real.sqrt ((2 : ℝ) ^ logLen n) ≤ Real.sqrt (2 * n) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt 2 * Real.sqrt n := Real.sqrt_mul (by norm_num) _
  have hsqrt2 : Real.sqrt 2 ≤ 1.415 := by
    rw [show (1.415 : ℝ) = Real.sqrt (1.415 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hX : (8192 : ℝ) ≤ (5120 * (b : ℝ) * orderedLogFactor (logLen n)) ^ b := by
    have h1 : (8192 : ℝ) ≤ 5120 * (b : ℝ) * orderedLogFactor (logLen n) := by nlinarith
    exact le_trans h1 (le_self_pow₀ (by linarith) (by omega))
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn'
  have hX0 : (0 : ℝ) ≤ (5120 * (b : ℝ) * orderedLogFactor (logLen n)) ^ b := by
    have := orderedLogFactor_nonneg (logLen n); positivity
  have hXs : (5120 * (b : ℝ) * orderedLogFactor (logLen n)) ^ b * Real.sqrt ((2 : ℝ) ^ logLen n)
      ≤ (5120 * (b : ℝ) * orderedLogFactor (logLen n)) ^ b * (1.415 * Real.sqrt n) :=
    mul_le_mul_of_nonneg_left (hsqN.trans (mul_le_mul_of_nonneg_right hsqrt2 (by positivity)))
      hX0
  have h1X : (8192 : ℝ) ≤ (5120 * (b : ℝ) * orderedLogFactor (logLen n)) ^ b * Real.sqrt n := by
    nlinarith
  have h5120 : (23185 : ℝ) * 5120 ^ b ≤ ((2 : ℝ) ^ 27) ^ b := by
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
    have hm : (5120 : ℝ) ^ m ≤ ((2 : ℝ) ^ 27) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    calc (23185 : ℝ) * 5120 ^ (m + 1) = (23185 * 5120) * 5120 ^ m := by ring
      _ ≤ 2 ^ 27 * ((2 : ℝ) ^ 27) ^ m := mul_le_mul (by norm_num) hm (by positivity) (by norm_num)
      _ = ((2 : ℝ) ^ 27) ^ (m + 1) := by ring
  calc uniformExtractionConstant * (1 + costA b (Pstd b (logLen n)) b (logLen n))
      ≤ 8192 * (1 + 2 * (5120 * (b : ℝ) * orderedLogFactor (logLen n)) ^ b
          * Real.sqrt ((2 : ℝ) ^ logLen n)) := by
        rw [uniformExtractionConstant]
        gcongr
    _ ≤ 23185 * ((5120 * (b : ℝ) * orderedLogFactor (logLen n)) ^ b * Real.sqrt n) := by
        nlinarith
    _ = 23185 * 5120 ^ b * ((b : ℝ) ^ b * orderedLogFactor (logLen n) ^ b * Real.sqrt n) := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ ((2 : ℝ) ^ 27) ^ b * ((b : ℝ) ^ b * orderedLogFactor (logLen n) ^ b * Real.sqrt n) :=
        mul_le_mul_of_nonneg_right h5120 (by
          have := orderedLogFactor_nonneg (logLen n); positivity)
    _ = (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * orderedLogFactor (logLen n) ^ b := by
        rw [mul_pow]; ring

open Classical in
/-- **The product-and-core algorithm** (`thm:ordered-beta-product`, algorithmic form): for
`1 ≤ b < n`, a quantum algorithm with at most `(2^27·b)^b·√n·L_n^(3b)` queries returns,
with probability at least `9/10`, a record that is truthful for the (padded) word, has at
most `b` positions and has the word's product. -/
theorem ordered_exists_core_alg (hb1 : 1 ≤ b) {n : ℕ} (hbn : b < n) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * (logLen n : ℝ) ^ (3 * b)
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · -- `n ≤ 3`: read everything
    obtain ⟨W, hW, hW', B, hgood⟩ := exists_exact_core_alg letter hst hb hb1 (le_two_pow_logLen n)
    refine ⟨W, hW, hW', B, n, le_orderedBound (by omega) hb1 ?_, hgood⟩
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hn' : (n : ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
    linarith
  · obtain ⟨W, hW, hW', B, Q, hQ, hgood⟩ := exists_root_alg letter hst hb hb1 (le_two_pow_logLen n)
      (Pstd b (logLen n)) (goodParams_Pstd hb1) (Pstd_snd_pos hb1)
    exact ⟨W, hW, hW', B, Q, hQ.trans (root_cost_le letter hst hb hb1 hn4 hbn), hgood⟩

/-- The main case `1 ≤ b < n`, `n ≥ 4`, of the product bound. -/
theorem ordered_qQuery_le_main (hb1 : 1 ≤ b) {n : ℕ} (hn4 : 4 ≤ n) (hbn : b < n) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * (logLen n : ℝ) ^ (3 * b) :=
  (qQuery_wordProd_le_root letter hst hb hb1 (le_two_pow_logLen n) (Pstd b (logLen n))
    (goodParams_Pstd hb1) (Pstd_snd_pos hb1)).trans (root_cost_le letter hst hb hb1 hn4 hbn)

/-- **`thm:ordered-beta-product`**: `Q_{1/10}(wordProd) ≤ min { n, (2^27·b)^b·√n·L_n^(3b) }`
for every `n` and every breadth bound `b`, with `L_n = ⌈log₂(n+1)⌉`; the bound is `0` when
`n = 0` or `b = 0`. -/
theorem ordered_qQuery_le (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * (logLen n : ℝ) ^ (3 * b)) := by
  have hread := qQuery_wordProd_le_length letter n (by norm_num : (0 : ℝ) ≤ 1 / 10)
  refine le_min (by exact_mod_cast hread) ?_
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · -- `b = 0`: the product is constant
    rw [qQuery_wordProd_zero_breadth letter hb n (by norm_num)]
    push_cast
    positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [qQuery_wordProd_zero_length letter (by norm_num)]
    simp only [Nat.cast_zero]
    positivity
  by_cases hmain : 4 ≤ n ∧ b < n
  · exact ordered_qQuery_le_main letter hst hb hb1 hmain.1 hmain.2
  · -- `n ≤ 3` or `n ≤ b`: reading everything is within the bound
    refine le_trans (b := (n : ℝ)) (by exact_mod_cast hread) (le_orderedBound hn1 hb1 ?_)
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hnb : n ≤ 3 ∨ n ≤ b := by omega
    rcases hnb with h | h
    · have : (n : ℝ) ≤ 3 := by exact_mod_cast h
      linarith
    · have : (n : ℝ) ≤ b := by exact_mod_cast h
      linarith

/-- The bounded-error convention `ε = 1/3`. -/
theorem ordered_qQuery_third_le (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * (logLen n : ℝ) ^ (3 * b)) := by
  refine le_trans ?_ (ordered_qQuery_le letter hst hb n)
  have hne : (QueryCounts (X := Fin n → σ) id (fun x => wordProd letter x) (1 / 10)).Nonempty := by
    obtain ⟨A, hA⟩ := exists_computesWithErrorOn (read := (id : (Fin n → σ) → Fin n → σ))
      (f := fun x => wordProd letter x) (fun x y h => congrArg (fun z => wordProd letter z) h)
      (by norm_num : (0 : ℝ) ≤ 1 / 10)
    exact ⟨_, mem_queryCounts hA⟩
  exact_mod_cast qQueryOn_mono (by norm_num) hne

/-! ## The exponent `5b/2` -/

open Classical in
/-- **The product-and-core algorithm with exponent `5b/2`**: for `1 ≤ b < n`, at most
`(2^27·b)^b·√n·L_n^{5b/2}` queries. -/
theorem ordered_exists_core_alg_five_halves (hb1 : 1 ≤ b) {n : ℕ} (hbn : b < n) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (B : QAlg (Fin n) σ (Record (2 ^ logLen n) (Option σ)) W) (Q : ℕ),
      (Q : ℝ) ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * orderedLogFactor (logLen n) ^ b
      ∧ ∀ x : Fin n → σ,
        9 / 10 ≤ ∑ K ∈ Finset.univ.filter (GoodRec letter b x), B.prob x Q K := by
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · obtain ⟨W, hW, hW', B, hgood⟩ := exists_exact_core_alg letter hst hb hb1 (le_two_pow_logLen n)
    refine ⟨W, hW, hW', B, n, le_orderedBound' (by omega) hb1 ?_
      (one_le_pow₀ (one_le_orderedLogFactor (one_le_logLen (by omega)))), hgood⟩
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hn' : (n : ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
    linarith
  · obtain ⟨W, hW, hW', B, Q, hQ, hgood⟩ := exists_root_alg letter hst hb hb1 (le_two_pow_logLen n)
      (Pstd b (logLen n)) (goodParams_Pstd hb1) (Pstd_snd_pos hb1)
    exact ⟨W, hW, hW', B, Q, hQ.trans (root_cost_le_five_halves letter hst hb hb1 hn4 hbn), hgood⟩

/-- The main case `1 ≤ b < n`, `n ≥ 4`, with exponent `5b/2`. -/
theorem ordered_qQuery_le_main_five_halves (hb1 : 1 ≤ b) {n : ℕ} (hn4 : 4 ≤ n) (hbn : b < n) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ (2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * orderedLogFactor (logLen n) ^ b :=
  (qQuery_wordProd_le_root letter hst hb hb1 (le_two_pow_logLen n) (Pstd b (logLen n))
    (goodParams_Pstd hb1) (Pstd_snd_pos hb1)).trans
    (root_cost_le_five_halves letter hst hb hb1 hn4 hbn)

/-- **`thm:ordered-beta-product` with exponent `5b/2`**:
`Q_{1/10}(wordProd) ≤ min { n, (2^27·b)^b·√n·L_n^{5b/2} }` for every `n` and every breadth
bound `b`, where `L_n^{5b/2}` is written `(L_n² √L_n)^b`. -/
theorem ordered_qQuery_le_five_halves (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ min (n : ℝ)
          ((2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * orderedLogFactor (logLen n) ^ b) := by
  have hread := qQuery_wordProd_le_length letter n (by norm_num : (0 : ℝ) ≤ 1 / 10)
  refine le_min (by exact_mod_cast hread) ?_
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · rw [qQuery_wordProd_zero_breadth letter hb n (by norm_num)]
    push_cast
    have := orderedLogFactor_nonneg (logLen n)
    positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [qQuery_wordProd_zero_length letter (by norm_num)]
    simp only [Nat.cast_zero]
    have := orderedLogFactor_nonneg (logLen 0)
    positivity
  by_cases hmain : 4 ≤ n ∧ b < n
  · exact ordered_qQuery_le_main_five_halves letter hst hb hb1 hmain.1 hmain.2
  · refine le_trans (b := (n : ℝ)) (by exact_mod_cast hread) (le_orderedBound' hn1 hb1 ?_
      (one_le_pow₀ (one_le_orderedLogFactor (one_le_logLen hn1))))
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hnb : n ≤ 3 ∨ n ≤ b := by omega
    rcases hnb with h | h
    · have : (n : ℝ) ≤ 3 := by exact_mod_cast h
      linarith
    · have : (n : ℝ) ≤ b := by exact_mod_cast h
      linarith

/-- The bounded-error convention `ε = 1/3`, exponent `5b/2`. -/
theorem ordered_qQuery_third_le_five_halves (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
          ((2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * orderedLogFactor (logLen n) ^ b) := by
  refine le_trans ?_ (ordered_qQuery_le_five_halves letter hst hb n)
  have hne : (QueryCounts (X := Fin n → σ) id (fun x => wordProd letter x) (1 / 10)).Nonempty := by
    obtain ⟨A, hA⟩ := exists_computesWithErrorOn (read := (id : (Fin n → σ) → Fin n → σ))
      (f := fun x => wordProd letter x) (fun x y h => congrArg (fun z => wordProd letter z) h)
      (by norm_num : (0 : ℝ) ≤ 1 / 10)
    exact ⟨_, mem_queryCounts hA⟩
  exact_mod_cast qQueryOn_mono (by norm_num) hne

/-- The real-power presentation `L_n^{(5/2)·b}` (`n ≥ 1`, so `L_n > 0`). -/
theorem ordered_qQuery_le_rpow {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ min (n : ℝ)
          ((2 ^ 27 * (b : ℝ)) ^ b * Real.sqrt n * (logLen n : ℝ) ^ ((5 : ℝ) * b / 2)) := by
  rw [← orderedLogFactor_pow_eq_rpow (one_le_logLen hn)]
  exact ordered_qQuery_le_five_halves letter hst hb n

end Main

/-! ## Specialisations -/

/-- **The `breadth` form**: with `b = β(letter)` whenever some breadth bound exists. -/
theorem ordered_qQuery_le_breadth {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M]
    [PartialOrder M] [DecidableEq M] (letter : σ → M) (hst : IsStableOrder M)
    (hex : ∃ b, IsBreadthBound letter b) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 27 * (breadth letter : ℝ)) ^ breadth letter * Real.sqrt n
          * (logLen n : ℝ) ^ (3 * breadth letter)) :=
  ordered_qQuery_le letter hst (isBreadthBound_breadth hex) n

/-- **The `breadth` form with exponent `5β/2`.** -/
theorem ordered_qQuery_le_breadth_five_halves {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M]
    [PartialOrder M] [DecidableEq M] (letter : σ → M) (hst : IsStableOrder M)
    (hex : ∃ b, IsBreadthBound letter b) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 27 * (breadth letter : ℝ)) ^ breadth letter * Real.sqrt n
          * orderedLogFactor (logLen n) ^ breadth letter) :=
  ordered_qQuery_le_five_halves letter hst (isBreadthBound_breadth hex) n

end MonoidProduct
