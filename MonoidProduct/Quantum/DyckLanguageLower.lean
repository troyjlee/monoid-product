import MonoidProduct.Dyck.Lower
import QuantumQueryComplexity.Quantum.Plurality
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The depth-bounded Dyck lower bound of Ambainis et al. (`thm:dyck-lb`)

The paper cites `thm:dyck-lb` from Ambainis et al. [ABIKPSSV20]: there is `c > 1` with
`Q_{1/3}(Dyck_{k,n}) = Ω(c^k √n)` for `k ≤ log n`, and for `k = c'·log n`,
`Q_{1/3}(Dyck_{k,n}) = Ω(n^(1-ε))` for every fixed `ε > 0`.  This file proves it
from the recursive block encodings (`MonoidProduct/Dyck`), through the plurality
`7/1376` adversary-to-query extraction `mul_advPM_le_qQuery_third_finiteOutput`.

## Corrections to the literal statement

* **Even lengths.**  At odd `n` no word is balanced (`dyck_eq_false_of_odd`), so
  `dyck k n` is constant and `Q = 0`; both parts assume `Even n`.
* **Depth `k ≥ 1` in part (1).**  `dyck 0 n` accepts only the empty word, so it
  is constant for `n ≥ 1`; part (1) assumes `1 ≤ k`.
* **`c'` depends on `ε` in part (2).**  The exponent `1 - 1/q` needs branching
  `m = 2^q`, and the block depth `2 + 2ℓ(m+1)` then costs `c' = 2^(q+1) + 6`
  with `q = ⌈1/ε⌉`; the quantifiers are `∀ ε, ∃ c', ∃ c₀`.  Part (2) holds for
  every depth `k ≥ c'·log₂ n` (not only `k = c'·log n`) and every even `n ≥ 2`.

## Depth monotonicity

The block encoding rejects on **total balance** (`2` instead of `0`) while all
prefix heights stay in `[0, blockHeight m ℓ]` (`encodeWord_invariant`), and the
`ud` padding adds at most a transient `+1`.  So raising the depth cap changes no
output, which is why `sqrt_mul_pow_le_advPM_dyck` holds at every `k ≥
blockHeight m ℓ + 2`; used at `r = 1` it is the padded single-block bound at
every even length.  No separate monotonicity-in-`k` lemma is needed.

## Contents

* `dyckLB_sqrt_le_advPM`: `√(n/2) ≤ ADV±(dyck k n)` for every `k ≥ 1` — the
  promised-AND star encoded as `(ud)^(n/2)` against one block turned into `uu`
  (the fixed-base exponential-in-depth bound needs `k ≥ 4`, so depths `1..3`
  need this floor);
* `dyckLB_qQuery_exp`: part (1) with `c = 2^(1/20)`, `c₀ = 7/(5504·√2)`;
* `dyckLB_qQuery_nearLinear_int`: `7/(11008·2^q) · n^(q/(q+1)) ≤ Q_{1/3}` for
  every even `n ≥ 2` and `k ≥ (2^(q+1)+6)·log₂ n`, choosing the largest block
  `blockWidth (2^q) ℓ ≤ n` and padding it with `ud`s;
* `dyckLB_qQuery_nearLinear`, `dyckLB_qQuery`: the paper's two parts.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## A `√n` lower bound at every depth cap `k ≥ 1` -/

/-- `r` two-letter blocks: `true ↦ ud`, `false ↦ uu`. -/
def dyckLB_starWord {r : ℕ} (x : AndStarDom r) : Fin (r * 2) → Bool :=
  concatW 2 r fun i => encodeBit (x.1 i)

/-- The star word at the requested length. -/
def dyckLB_starRead (r n : ℕ) (hn : r * 2 = n) (x : AndStarDom r) : Fin n → Bool :=
  wcast hn (dyckLB_starWord x)

lemma dyckLB_encodeBit_true : encodeBit true = ud := by
  funext j
  fin_cases j <;> rfl

lemma dyckLB_starOut_eq (r n : ℕ) (hn : r * 2 = n) (k : ℕ) (hk : 1 ≤ k)
    (x : AndStarDom r) : andStarOut r x = dyck k n (dyckLB_starRead r n hn x) := by
  have htot : totalBalance (dyckLB_starWord x) = 2 * (falseCount x.1 : ℤ) := by
    rw [dyckLB_starWord, totalBalance_concatW]
    simp only [totalBalance_encodeBit]
    exact sum_ite_eq_two_mul_falseCount x.1
  rcases x.2 with hc | hc
  · have hall : ∀ i, x.1 i = true := by
      intro i
      by_contra hi
      have hmem : i ∈ zeroSet x.1 := by simpa using hi
      rw [falseCount, Finset.card_eq_zero] at hc
      rw [hc] at hmem
      exact absurd hmem (Finset.notMem_empty i)
    have hout : andStarOut r x = true := by simp [andStarOut, hc]
    rw [hout, eq_comm, dyck_eq_true, dyckLB_starRead, isDyck_wcast, isDyck_iff]
    refine ⟨by rw [htot, hc]; norm_num, fun t => ?_⟩
    have hb := prefixBalance_concatW_bounds 2 (h := 1) (by norm_num) r
      (fun i => encodeBit (x.1 i))
      (fun i t => (prefixBalance_encodeBit_bounds _ t).1)
      (fun i t => by rw [hall i, dyckLB_encodeBit_true]; exact (prefixBalance_ud_bounds t).2)
      t
    have hsum : (∑ i, totalBalance (encodeBit (x.1 i))) = 0 := by
      simp [hall]
    rw [hsum, zero_add] at hb
    exact ⟨hb.1, hb.2.trans (by exact_mod_cast hk)⟩
  · have hout : andStarOut r x = false := by simp [andStarOut, hc]
    rw [hout, eq_comm, Bool.eq_false_iff]
    intro hd
    rw [dyck_eq_true, dyckLB_starRead, isDyck_wcast, isDyck_iff] at hd
    have := hd.1
    rw [htot, hc] at this
    norm_num at this

lemma dyckLB_starRead_local (r n : ℕ) (hn : r * 2 = n) (j : Fin n) :
    IsLocalCoord (andStarRead (r := r)) (dyckLB_starRead r n hn) j := by
  obtain ⟨i, s, hs⟩ := concatW_local (w := 2) r (Fin.cast hn.symm j)
  have hval : ∀ x : AndStarDom r, dyckLB_starRead r n hn x j = encodeBit (x.1 i) s :=
    fun x => hs fun i => encodeBit (x.1 i)
  by_cases h1 : (s : ℕ) = 1
  · exact Or.inl ⟨i, fun x => by rw [hval x, encodeBit_apply, if_pos h1]; rfl⟩
  · exact Or.inr fun x y => by rw [hval x, hval y, encodeBit_apply, encodeBit_apply,
      if_neg h1, if_neg h1]

lemma dyckLB_starRead_injective (r n : ℕ) (hn : r * 2 = n) :
    Function.Injective (dyckLB_starRead r n hn) := by
  intro x y hxy
  refine Subtype.ext (funext fun i => ?_)
  obtain ⟨p, hp⟩ := concatW_locate (w := 2) r i ⟨1, by norm_num⟩
  have hread : ∀ z : AndStarDom r,
      dyckLB_starRead r n hn z (Fin.cast hn p) = z.1 i := by
    intro z
    show concatW 2 r (fun i => encodeBit (z.1 i)) _ = _
    rw [show Fin.cast hn.symm (Fin.cast hn p) = p from Fin.ext rfl, hp]
    rfl
  rw [← hread x, ← hread y, hxy]

/-- **The `√n` floor at every depth cap `k ≥ 1`**: for even `n`,
`√(n/2) ≤ ADV±(dyck k n)`, from the promised-AND star encoded as
`(ud)^(n/2)` against one block turned into `uu`. -/
theorem dyckLB_sqrt_le_advPM (k n : ℕ) (hk : 1 ≤ k) (heven : Even n) :
    Real.sqrt ((n / 2 : ℕ) : ℝ) ≤ advPM (dyck k n) := by
  set r := n / 2 with hr
  have hn : r * 2 = n := by obtain ⟨a, ha⟩ := heven; omega
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.sqrt_zero]
    exact advPM_nonneg _
  have hdetEnc : ∀ x y : AndStarDom r,
      dyckLB_starRead r n hn x = dyckLB_starRead r n hn y →
        andStarOut r x = andStarOut r y :=
    fun x y h => by rw [dyckLB_starRead_injective r n hn h]
  calc Real.sqrt (r : ℝ)
      ≤ advPMOn (andStarRead (r := r)) (andStarOut r) := sqrt_le_advPMOn_andStar r hpos
    _ ≤ advPMOn (dyckLB_starRead r n hn) (andStarOut r) :=
        advPMOn_mono_of_local hdetEnc (dyckLB_starRead_local r n hn)
    _ ≤ advPM (dyck k n) :=
        advPMOn_le_advPM_of_injective (dyckLB_starRead_injective r n hn)
          (dyckLB_starOut_eq r n hn k hk)

/-! ## Part (1): exponential in the depth, for `k ≤ log₂ n` -/

/-- The quantum form of the `√n` floor: for even `n` and `k ≥ 1`,
`7·√n/(1376·√2) ≤ Q_{1/3}(dyck k n)`. -/
theorem dyckLB_qQuery_sqrt (k n : ℕ) (hk : 1 ≤ k) (heven : Even n) :
    7 * Real.sqrt n / (1376 * Real.sqrt 2) ≤ (qQuery (dyck k n) (1 / 3) : ℝ) := by
  have hadv := dyckLB_sqrt_le_advPM k n hk heven
  have hcast : ((n / 2 : ℕ) : ℝ) = (n : ℝ) / 2 := by
    obtain ⟨a, ha⟩ := heven
    rw [show n / 2 = a by omega, ha]
    push_cast
    ring
  rw [hcast, Real.sqrt_div (Nat.cast_nonneg n)] at hadv
  have hQ := mul_advPM_le_qQuery_third_finiteOutput (dyck k n)
  calc 7 * Real.sqrt n / (1376 * Real.sqrt 2)
      = (7 / 1376 : ℝ) * (Real.sqrt n / Real.sqrt 2) := by ring
    _ ≤ (7 / 1376 : ℝ) * advPM (dyck k n) :=
        mul_le_mul_of_nonneg_left hadv (by norm_num)
    _ ≤ _ := hQ

/-- `k ≤ log₂ n` with `k ≥ 1` forces `2^k ≤ n`. -/
lemma dyckLB_two_pow_le_of_le_logb {n k : ℕ} (hk : 1 ≤ k)
    (hlog : (k : ℝ) ≤ Real.logb 2 n) : 2 ^ k ≤ n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h
    · rw [h0, Nat.cast_zero, Real.logb_zero] at hlog
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    · exact h
  rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hn),
    Real.rpow_natCast] at hlog
  exact_mod_cast hlog

/-- `2^(k/20) ≤ 2·√2^((k-4)/10)`: the rounding loss of the depth-first
instantiation of the fixed-base exponential-in-depth bound. -/
lemma dyckLB_rpow_le_sqrt_pow (k : ℕ) :
    (2 : ℝ) ^ ((k : ℝ) / 20) ≤ 2 * Real.sqrt 2 ^ ((k - 4) / 10) := by
  set ℓ := (k - 4) / 10 with hℓ
  have hkℓ : k ≤ 10 * ℓ + 20 := by omega
  have hsq : Real.sqrt 2 ^ ℓ = (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_mul_natCast (by norm_num)]
  rw [hsq, ← Real.rpow_one_add' (by norm_num) (by positivity)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (k : ℝ) ≤ 10 * ℓ + 20 := by exact_mod_cast hkℓ
  linarith

/-- **`thm:dyck-lb` (1), explicit form.**  For even `n` and every depth
`1 ≤ k ≤ log₂ n`,

  `7/(5504·√2) · 2^(k/20) · √n ≤ Q_{1/3}(dyck k n)`.

Depths `k ≥ 4` use the fixed-base exponential-in-depth bound at recursion depth `ℓ = (k-4)/10` (the
hypothesis `4·8^ℓ ≤ n` follows from `2^k ≤ n`); depths `1 ≤ k ≤ 3` use the
`√n` star floor `dyckLB_sqrt_le_advPM`. -/
theorem dyckLB_qQuery_exp (n k : ℕ) (heven : Even n) (hk : 1 ≤ k)
    (hlog : (k : ℝ) ≤ Real.logb 2 n) :
    7 / (5504 * Real.sqrt 2) * (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt n
      ≤ (qQuery (dyck k n) (1 / 3) : ℝ) := by
  have h2k := dyckLB_two_pow_le_of_le_logb hk hlog
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hQ := mul_advPM_le_qQuery_third_finiteOutput (dyck k n)
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · have hsmall := dyckLB_qQuery_sqrt k n hk heven
    have hpow : (2 : ℝ) ^ ((k : ℝ) / 20) ≤ 2 := by
      calc (2 : ℝ) ^ ((k : ℝ) / 20) ≤ 2 ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have : (k : ℝ) ≤ 3 := by exact_mod_cast (by omega : k ≤ 3)
            linarith
        _ = 2 := Real.rpow_one 2
    calc 7 / (5504 * Real.sqrt 2) * (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt n
        ≤ 7 / (5504 * Real.sqrt 2) * 2 * Real.sqrt n := by gcongr
      _ ≤ 7 * Real.sqrt n / (1376 * Real.sqrt 2) := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith [Real.sqrt_nonneg (n : ℝ)]
      _ ≤ _ := hsmall
  · set ℓ := (k - 4) / 10 with hℓ
    have hfit : 4 * 8 ^ ℓ ≤ n := by
      calc 4 * 8 ^ ℓ = 2 ^ (3 * ℓ + 2) := by rw [pow_add, pow_mul]; norm_num; ring
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ n := h2k
    have hadv := sqrt_mul_sqrt_two_pow_le_advPM_dyck ℓ n k heven hfit (by omega)
    have hpow := dyckLB_rpow_le_sqrt_pow k
    rw [← hℓ] at hpow
    calc 7 / (5504 * Real.sqrt 2) * (2 : ℝ) ^ ((k : ℝ) / 20) * Real.sqrt n
        ≤ 7 / (5504 * Real.sqrt 2) * (2 * Real.sqrt 2 ^ ℓ) * Real.sqrt n := by gcongr
      _ = (7 / 1376 : ℝ) * ((Real.sqrt n * Real.sqrt 2 ^ ℓ) / (2 * Real.sqrt 2)) := by
          field_simp
          ring
      _ ≤ (7 / 1376 : ℝ) * advPM (dyck k n) := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          linarith
      _ ≤ _ := hQ

/-- **`thm:dyck-lb` (1)**, in the paper's shape: there are `c > 1` and
`c₀ > 0` with `c₀ · c^k · √n ≤ Q_{1/3}(dyck k n)` for every even `n` and every
depth `1 ≤ k ≤ log₂ n` (here `c = 2^(1/20)`, `c₀ = 7/(5504·√2)`). -/
theorem dyckLB_qQuery_exp_exists :
    ∃ c : ℝ, 1 < c ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n k : ℕ, Even n → 1 ≤ k →
      (k : ℝ) ≤ Real.logb 2 n →
        c₀ * c ^ k * Real.sqrt n ≤ (qQuery (dyck k n) (1 / 3) : ℝ) := by
  refine ⟨(2 : ℝ) ^ ((1 : ℝ) / 20), Real.one_lt_rpow (by norm_num) (by norm_num),
    7 / (5504 * Real.sqrt 2), by positivity, fun n k heven hk hlog => ?_⟩
  have h := dyckLB_qQuery_exp n k heven hk hlog
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div_mul_eq_div]

/-! ## Part (2): near-linear at logarithmic depth -/

/-- Block widths grow at least like `2^(ℓ+1)`. -/
lemma dyckLB_two_pow_le_blockWidth (m : ℕ) (hm : 1 ≤ m) (ℓ : ℕ) :
    2 ^ (ℓ + 1) ≤ blockWidth m ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      rw [blockWidth_succ, pow_succ]
      calc 2 ^ (ℓ + 1) * 2 ≤ blockWidth m ℓ * 2 := Nat.mul_le_mul_right _ ih
        _ ≤ 2 * m * (blockWidth m ℓ + 1) := by nlinarith

/-- **Every even length, integer exponent.**  For every `q`, even `n ≥ 2` and
every depth `k ≥ (2^(q+1)+6)·log₂ n`,

  `7/(11008·2^q) · n^(q/(q+1)) ≤ Q_{1/3}(dyck k n)`.

Take the largest `ℓ` with `w = blockWidth (2^q) ℓ ≤ n`, pad the block to length
`n` with `ud`s (`sqrt_mul_pow_le_advPM_dyck` at `r = 1`), and use
`n < blockWidth (2^q) (ℓ+1) ≤ 8·2^q·2^((q+1)ℓ)` against the gain `2^(qℓ)`. -/
theorem dyckLB_qQuery_nearLinear_int (q n k : ℕ) (heven : Even n) (hn : 2 ≤ n)
    (hk : ((2 ^ (q + 1) + 6 : ℕ) : ℝ) * Real.logb 2 n ≤ k) :
    7 / (11008 * 2 ^ q) * (n : ℝ) ^ ((q : ℝ) / (q + 1))
      ≤ (qQuery (dyck k n) (1 / 3) : ℝ) := by
  set m := 2 ^ q with hmdef
  have hm : 1 ≤ m := Nat.one_le_two_pow
  -- the largest block that fits
  have hex : ∃ ℓ, n < blockWidth m (ℓ + 1) :=
    ⟨n, lt_of_lt_of_le (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num)
      (by omega))) (dyckLB_two_pow_le_blockWidth m hm (n + 1))⟩
  classical
  set ℓ := Nat.find hex with hℓ
  have hbig : n < blockWidth m (ℓ + 1) := Nat.find_spec hex
  have hlen : blockWidth m ℓ ≤ n := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · rw [h0, blockWidth_zero]; exact hn
    · have := Nat.find_min hex (show ℓ - 1 < ℓ by omega)
      rw [show ℓ - 1 + 1 = ℓ by omega] at this
      omega
  -- the depth hypothesis
  have hℓlog : ((ℓ + 1 : ℕ) : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast (by omega : 0 < n)),
      Real.rpow_natCast]
    exact_mod_cast (dyckLB_two_pow_le_blockWidth m hm ℓ).trans hlen
  have hkk : blockHeight m ℓ + 2 ≤ k := by
    have h1 : ((blockHeight m ℓ + 2 : ℕ) : ℝ)
        ≤ ((2 ^ (q + 1) + 6 : ℕ) : ℝ) * ((ℓ + 1 : ℕ) : ℝ) := by
      rw [blockHeight_eq]
      push_cast
      rw [hmdef]
      push_cast
      rw [pow_succ]
      nlinarith [(by positivity : (0 : ℝ) ≤ 2 ^ q), (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
    have h2 := mul_le_mul_of_nonneg_left hℓlog
      (Nat.cast_nonneg (2 ^ (q + 1) + 6 : ℕ) : (0 : ℝ) ≤ _)
    exact_mod_cast h1.trans (h2.trans hk)
  -- the adversary bound
  have hadv := sqrt_mul_pow_le_advPM_dyck m ℓ 1 n k (by omega) one_pos
    (by rw [one_mul]; exact hlen) heven hkk
  rw [Nat.cast_one, Real.sqrt_one, one_mul] at hadv
  -- the length against the gain
  have hwidth : n ≤ 8 * m * 2 ^ ((q + 1) * ℓ) := by
    have h := blockWidth_add_two_le m hm ℓ
    rw [blockWidth_succ] at hbig
    have h2m : (2 * m) ^ ℓ = 2 ^ ((q + 1) * ℓ) := by
      rw [hmdef, ← pow_succ', pow_mul]
    rw [h2m] at h
    calc n ≤ 2 * m * (blockWidth m ℓ + 1) := hbig.le
      _ ≤ 2 * m * (4 * 2 ^ ((q + 1) * ℓ)) := Nat.mul_le_mul_left _ (by omega)
      _ = 8 * m * 2 ^ ((q + 1) * ℓ) := by ring
  set e : ℝ := (q : ℝ) / (q + 1) with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by rw [he, div_le_one (by positivity)]; linarith
  have hm8 : (1 : ℝ) ≤ 8 * (m : ℝ) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hgain : (n : ℝ) ^ e ≤ 8 * (m : ℝ) * (m : ℝ) ^ ℓ := by
    have hcast : (n : ℝ) ≤ 8 * (m : ℝ) * (2 : ℝ) ^ ((q + 1) * ℓ) := by
      exact_mod_cast hwidth
    have hpow : ((2 : ℝ) ^ ((q + 1) * ℓ)) ^ e = (m : ℝ) ^ ℓ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hmdef]
      push_cast
      rw [← pow_mul, ← Real.rpow_natCast]
      congr 1
      push_cast
      rw [he]
      field_simp
    calc (n : ℝ) ^ e ≤ (8 * (m : ℝ) * (2 : ℝ) ^ ((q + 1) * ℓ)) ^ e :=
          Real.rpow_le_rpow (Nat.cast_nonneg n) hcast he0
      _ = (8 * (m : ℝ)) ^ e * ((2 : ℝ) ^ ((q + 1) * ℓ)) ^ e :=
          Real.mul_rpow (by positivity) (by positivity)
      _ ≤ 8 * (m : ℝ) * (m : ℝ) ^ ℓ := by
          rw [hpow]
          gcongr
          calc (8 * (m : ℝ)) ^ e ≤ (8 * (m : ℝ)) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hm8 he1
            _ = 8 * (m : ℝ) := Real.rpow_one _
  have hQ := mul_advPM_le_qQuery_third_finiteOutput (dyck k n)
  have hmpos : (0 : ℝ) < m := by positivity
  have hmq : ((2 : ℝ) ^ q) = (m : ℝ) := by rw [hmdef]; push_cast; rfl
  rw [hmq]
  calc 7 / (11008 * (m : ℝ)) * (n : ℝ) ^ e
      ≤ 7 / (11008 * (m : ℝ)) * (8 * (m : ℝ) * (m : ℝ) ^ ℓ) := by gcongr
    _ = (7 / 1376 : ℝ) * (m : ℝ) ^ ℓ := by field_simp; ring
    _ ≤ (7 / 1376 : ℝ) * advPM (dyck k n) := by gcongr
    _ ≤ _ := hQ

/-- **`thm:dyck-lb` (2).**  For every fixed `ε > 0` there are `c' > 0` and
`c₀ > 0` (both depending on `ε`) such that for every even `n ≥ 2` and every
depth `k ≥ c'·log₂ n`, `c₀ · n^(1-ε) ≤ Q_{1/3}(dyck k n)`.  Explicitly
`q = ⌈1/ε⌉`, `c' = 2^(q+1)+6`, `c₀ = 7/(11008·2^q)`. -/
theorem dyckLB_qQuery_nearLinear (ε : ℝ) (hε : 0 < ε) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, Even n → 2 ≤ n → ∀ k : ℕ,
      c' * Real.logb 2 n ≤ k →
        c₀ * (n : ℝ) ^ (1 - ε) ≤ (qQuery (dyck k n) (1 / 3) : ℝ) := by
  set q := ⌈1 / ε⌉₊ with hq
  refine ⟨((2 ^ (q + 1) + 6 : ℕ) : ℝ), by positivity, 7 / (11008 * 2 ^ q), by positivity,
    fun n heven hn k hk => ?_⟩
  have hmain := dyckLB_qQuery_nearLinear_int q n k heven hn hk
  have hεq : 1 ≤ ε * q := by
    have h := Nat.le_ceil (1 / ε)
    rw [← hq, div_le_iff₀ hε] at h
    linarith
  have hexp : 1 - ε ≤ (q : ℝ) / (q + 1) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  calc 7 / (11008 * 2 ^ q) * (n : ℝ) ^ (1 - ε)
      ≤ 7 / (11008 * 2 ^ q) * (n : ℝ) ^ ((q : ℝ) / (q + 1)) := by
        gcongr
    _ ≤ _ := hmain

/-! ## The two parts together -/

/-- **`thm:dyck-lb`** (Ambainis et al.), corrected to even lengths and, in
part (1), to depths `k ≥ 1`; in part (2) the depth constant `c'` depends on
`ε`. -/
theorem dyckLB_qQuery :
    (∃ c : ℝ, 1 < c ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n k : ℕ, Even n → 1 ≤ k →
      (k : ℝ) ≤ Real.logb 2 n →
        c₀ * c ^ k * Real.sqrt n ≤ (qQuery (dyck k n) (1 / 3) : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ c' : ℝ, 0 < c' ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, Even n → 2 ≤ n → ∀ k : ℕ,
        c' * Real.logb 2 n ≤ k →
          c₀ * (n : ℝ) ^ (1 - ε) ≤ (qQuery (dyck k n) (1 / 3) : ℝ)) :=
  ⟨dyckLB_qQuery_exp_exists, dyckLB_qQuery_nearLinear⟩

end MonoidProduct
