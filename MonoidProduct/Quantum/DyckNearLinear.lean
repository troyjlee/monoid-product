import MonoidProduct.Quantum.Envelope
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Near-linear lower bounds from polylogarithmic-size aperiodic monoids
(the paper's `cor:dyck` (iii), `cor:aperiodic-envelope-transition`, first clause)

`cor:dyck` (iii): taking the Dyck height `k = Θ(log n)`, the aperiodic monoid
`M_k = DyckNF k` of order `O(log³ n)` has a product problem needing
`Ω(n^{1−ε})` queries.  `cor:aperiodic-envelope-transition`, first clause: for
every fixed `ε ∈ (0,1)` there is `C_ε` with
`N ≥ C_ε (log(n+2))³ ⇒ 𝒬_ap(N, n) = Ω_ε(n^{1−ε})`.  The paper derives both
from the Dyck lower
bound of Ambainis et al. [ABIKPSSV20]; here they are derived from the
special-length block bound `dyckMonoid_product_lower_nearLinear`.

* `dyckNL_qQuery_ge_advPM` — padding: the binary Dyck product of length `w ≤ n`
  embeds into the total length-`n` product over `DyckNF k` by an injective
  letter relabelling followed by identity padding (a query-local encoding), so
  `(7/1376)·ADV±(dyckProduct k w) ≤ Q_{1/3}(Prod_{DyckNF k, n})`.
* `dyckNL_level m n` — the largest `ℓ` with `blockWidth m ℓ ≤ n`;
  `dyckNL_height q n = blockHeight (2^q) (dyckNL_level (2^q) n)`.
* `dyckNL_qQuery_lower_pow` — the integer-exponent form: for `q ≥ 1`, `n ≥ 2`,
  `7/(22016·2^q) · n^{1−1/q} ≤ Q_{1/3}(Prod_{DyckNF (dyckNL_height q n), n})`,
  with `dyckNL_height q n ≤ (2^{q+1}+6)·log₂(n+2)` and
  `|DyckNF (dyckNL_height q n)| ≤ (2^{q+1}+6)³·log₂(n+2)³`.
* `dyckNL_nearLinear_lower` — `cor:dyck` (iii) at `q = ⌈1/ε⌉`.
* `dyckNL_aperiodicEnvelope_nearLinear` (`log₂`) and
  `dyckNL_aperiodicEnvelope_nearLinear_log` (natural `log`, the paper's form) —
  the first clause of `cor:aperiodic-envelope-transition`.

Deviation from the paper: the height is not `⌊c_ε log n⌋` but the block height
at the largest fitting block level, which is `≤ C_ε log₂(n+2)`; odd and
non-special lengths are handled by identity padding rather than by the
`thm:dyck-lb` interpolation.  The constants are explicit
(`q = ⌈1/ε⌉`, `c = 7/(22016·2^q)`, `C = (2^{q+1}+6)³`, and `8C` for natural log).
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## Identity padding -/

/-- A binary word of length `w`, relabelled into `DyckNF k` and padded with the
identity up to length `n`. -/
def dyckNL_pad (k w n : ℕ) (x : Fin w → Bool) : Fin n → DyckNF k :=
  fun j => padAt (fun i => dyckLetter k (x i)) (j : ℕ)

lemma dyckNL_wordProd_pad {k w n : ℕ} (hwn : w ≤ n) (x : Fin w → Bool) :
    wordProd (id : DyckNF k → DyckNF k) (dyckNL_pad k w n x) = dyckProduct k w x := by
  set y : Fin w → DyckNF k := fun i => dyckLetter k (x i) with hy
  have h1 : wordProd (id : DyckNF k → DyckNF k) (dyckNL_pad k w n x) = rangeProd y 0 n := by
    unfold wordProd orderedProd
    refine rangeProd_congr fun i _ hi => ?_
    rw [padAt_of_lt _ hi]
    rfl
  have h2 : rangeProd y w n = 1 := by
    unfold rangeProd
    refine List.prod_eq_one fun a ha => ?_
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 ha
    exact padAt_of_le y (by omega)
  rw [h1, ← rangeProd_split y (Nat.zero_le w) hwn, h2, mul_one]
  rfl

/-- **Padding transfer**: for `1 ≤ k` and `w ≤ n`, the binary Dyck product of
length `w` lower-bounds the total length-`n` product over `DyckNF k`. -/
theorem dyckNL_qQuery_ge_advPM {k w n : ℕ} (hk1 : 1 ≤ k) (hwn : w ≤ n) :
    (7 / 1376 : ℝ) * advPM (dyckProduct k w)
      ≤ (qQuery (fun v : Fin n → DyckNF k => wordProd (id : DyckNF k → DyckNF k) v)
          (1 / 3) : ℝ) := by
  have : Nonempty (DyckNF k) := ⟨1⟩
  let read : (Fin w → Bool) → Fin w → DyckNF k := fun x j => dyckLetter k (x j)
  let enc : (Fin w → Bool) → Fin n → DyckNF k := dyckNL_pad k w n
  have hF : (fun x => wordProd (id : DyckNF k → DyckNF k) (enc x)) = dyckProduct k w :=
    funext fun x => dyckNL_wordProd_pad hwn x
  have hcomp : advPMOn read (dyckProduct k w) = advPM (dyckProduct k w) :=
    advPMOn_comp_injective (dyckLetter_injective hk1)
      (id : (Fin w → Bool) → Fin w → Bool) (dyckProduct k w)
  have hloc : ∀ j, IsLocalCoord read enc j := by
    intro j
    by_cases hj : (j : ℕ) < w
    · exact Or.inl ⟨⟨j, hj⟩, fun x => by
        simp only [enc, dyckNL_pad, padAt_of_lt _ hj, read]⟩
    · exact Or.inr fun x y => by
        simp only [enc, dyckNL_pad, padAt_of_le _ (not_lt.1 hj)]
  have hdet : ∀ x y, enc x = enc y → dyckProduct k w x = dyckProduct k w y := by
    intro x y h
    rw [← hF]
    simp only [h]
  have hmono : advPMOn read (dyckProduct k w) ≤ advPMOn enc (dyckProduct k w) :=
    advPMOn_mono_of_local hdet hloc
  have hpar := mul_advPMOn_le_qQueryOn_third_finiteOutput (read := enc)
    (f := dyckProduct k w) hdet
  have hQ := qQueryOn_comp_read_le_qQuery enc
    (fun v : Fin n → DyckNF k => wordProd (id : DyckNF k → DyckNF k) v)
    (queryCounts_nonempty (read := (id : (Fin n → DyckNF k) → Fin n → DyckNF k))
      (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3))
  rw [hF] at hQ
  calc (7 / 1376 : ℝ) * advPM (dyckProduct k w)
      = (7 / 1376 : ℝ) * advPMOn read (dyckProduct k w) := by rw [hcomp]
    _ ≤ (7 / 1376 : ℝ) * advPMOn enc (dyckProduct k w) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ ≤ (qQueryOn enc (dyckProduct k w) (1 / 3) : ℝ) := hpar
    _ ≤ _ := by exact_mod_cast hQ

/-! ## The fitting block level -/

lemma dyckNL_two_pow_le_blockWidth {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) :
    2 ^ (ℓ + 1) ≤ blockWidth m ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      rw [blockWidth_succ, pow_succ]
      nlinarith

lemma dyckNL_blockWidth_succ_le {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) :
    blockWidth m (ℓ + 1) ≤ 4 * m * blockWidth m ℓ := by
  have h := blockWidth_pos m ℓ hm
  rw [blockWidth_succ]
  nlinarith

/-- The largest block level whose width fits in length `n`. -/
def dyckNL_level (m n : ℕ) : ℕ := Nat.findGreatest (fun ℓ => blockWidth m ℓ ≤ n) n

lemma dyckNL_level_spec (m : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    blockWidth m (dyckNL_level m n) ≤ n :=
  Nat.findGreatest_spec (P := fun ℓ => blockWidth m ℓ ≤ n) (Nat.zero_le n)
    (by simpa using hn)

lemma dyckNL_lt_blockWidth_level_succ {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    n < blockWidth m (dyckNL_level m n + 1) := by
  by_contra h
  have h' : blockWidth m (dyckNL_level m n + 1) ≤ n := Nat.le_of_not_lt h
  have hle : dyckNL_level m n + 1 ≤ n := by
    have h2 := dyckNL_two_pow_le_blockWidth hm (dyckNL_level m n + 1)
    have h3 : dyckNL_level m n + 1 < 2 ^ (dyckNL_level m n + 1 + 1) :=
      Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
    omega
  exact Nat.findGreatest_is_greatest (P := fun ℓ => blockWidth m ℓ ≤ n)
    (Nat.lt_succ_self _) hle h'

/-- The fitting level is at most `log₂ (n+2)`. -/
lemma dyckNL_level_le_logb {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : 2 ≤ n) :
    (dyckNL_level m n : ℝ) ≤ Real.logb 2 ((n : ℝ) + 2) := by
  have h1 : 2 ^ dyckNL_level m n ≤ n := by
    have := dyckNL_two_pow_le_blockWidth hm (dyckNL_level m n)
    have := dyckNL_level_spec m hn
    rw [pow_succ] at *
    omega
  have h2 : ((2 : ℝ) ^ dyckNL_level m n) ≤ (n : ℝ) + 2 := by
    have : ((2 ^ dyckNL_level m n : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    push_cast at this
    linarith
  calc (dyckNL_level m n : ℝ) = Real.logb 2 ((2 : ℝ) ^ dyckNL_level m n) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    _ ≤ Real.logb 2 ((n : ℝ) + 2) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) h2

lemma dyckNL_one_le_logb (n : ℕ) : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The Dyck height used at length `n` and exponent parameter `q`. -/
def dyckNL_height (q n : ℕ) : ℕ := blockHeight (2 ^ q) (dyckNL_level (2 ^ q) n)

/-- The height is `O_q(log n)`: `dyckNL_height q n + 2 ≤ (2^{q+1}+6)·log₂(n+2)`. -/
theorem dyckNL_height_add_two_le (q : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (dyckNL_height q n : ℝ) + 2 ≤ (2 * 2 ^ q + 6) * Real.logb 2 ((n : ℝ) + 2) := by
  have hl := dyckNL_level_le_logb (Nat.one_le_two_pow (n := q)) hn
  have h1 := dyckNL_one_le_logb n
  have hm : (0 : ℝ) ≤ 2 ^ q := by positivity
  unfold dyckNL_height
  rw [blockHeight_eq]
  push_cast
  nlinarith

/-- The monoid is `O_q(log³ n)`:
`|DyckNF (dyckNL_height q n)| ≤ (2^{q+1}+6)³·log₂(n+2)³`. -/
theorem dyckNL_card_le (q : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (Fintype.card (DyckNF (dyckNL_height q n)) : ℝ)
      ≤ (2 * 2 ^ q + 6) ^ 3 * Real.logb 2 ((n : ℝ) + 2) ^ 3 := by
  have hc : (Fintype.card (DyckNF (dyckNL_height q n)) : ℝ)
      ≤ ((dyckNL_height q n : ℝ) + 2) ^ 3 := by
    exact_mod_cast card_dyckNF_le_cube (dyckNL_height q n)
  refine hc.trans ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (dyckNL_height_add_two_le q hn) 3

/-! ## The integer-exponent lower bound -/

/-- From `w^{q-1} ≤ 4^{q-1}·A^q` to `w^{1-1/q}/4 ≤ A`. -/
lemma dyckNL_root_le {q : ℕ} (hq : 1 ≤ q) {W A : ℝ} (hW : 0 ≤ W) (hA : 0 ≤ A)
    (h : W ^ (q - 1) ≤ 4 ^ (q - 1) * A ^ q) :
    W ^ (1 - 1 / (q : ℝ)) / 4 ≤ A := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hB : 0 ≤ W ^ (1 - 1 / (q : ℝ)) / 4 := by positivity
  have hpow : (W ^ (1 - 1 / (q : ℝ))) ^ q = W ^ (q - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW, ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub hq]
    field_simp
    push_cast
    ring
  have h4 : (4 : ℝ) ^ q = 4 * 4 ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine (pow_le_pow_iff_left₀ hB hA (by omega : q ≠ 0)).1 ?_
  rw [div_pow, hpow, h4]
  have h41 : (0 : ℝ) < 4 ^ (q - 1) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have hWq : 0 ≤ W ^ (q - 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)]

/-- **`cor:dyck` (iii), integer-exponent form.**  For `q ≥ 1` and `n ≥ 2`, the
total product over `DyckNF (dyckNL_height q n)` (height `O_q(log n)`, order
`O_q(log³ n)`) needs `7/(22016·2^q)·n^{1−1/q}` queries at error `1/3`. -/
theorem dyckNL_qQuery_lower_pow {q : ℕ} (hq : 1 ≤ q) {n : ℕ} (hn : 2 ≤ n) :
    7 / (22016 * 2 ^ q) * (n : ℝ) ^ (1 - 1 / (q : ℝ))
      ≤ (qQuery (fun v : Fin n → DyckNF (dyckNL_height q n) =>
          wordProd (id : DyckNF (dyckNL_height q n) → DyckNF (dyckNL_height q n)) v)
          (1 / 3) : ℝ) := by
  set m : ℕ := 2 ^ q with hmdef
  have hm : 1 ≤ m := Nat.one_le_two_pow
  set ℓ := dyckNL_level m n with hℓ
  set W : ℕ := blockWidth m ℓ with hW
  have hWn : W ≤ n := dyckNL_level_spec m hn
  have hnW : n < 4 * m * W :=
    (dyckNL_lt_blockWidth_level_succ hm n).trans_le (dyckNL_blockWidth_succ_le hm ℓ)
  have hk1 : 1 ≤ dyckNL_height q n := by
    unfold dyckNL_height; rw [blockHeight_eq]; omega
  have hQ := dyckNL_qQuery_ge_advPM (w := W) hk1 hWn
  have hnl := dyckMonoid_product_lower_nearLinear m q ℓ (by omega)
    (two_pow_nearLinear_hyp q)
  have hA := dyckNL_root_le hq (Nat.cast_nonneg W) (advPM_nonneg _) hnl
  -- `n^{p} ≤ 4m·W^{p}` with `p = 1 − 1/q ∈ [0,1]`
  have hp0 : 0 ≤ 1 - 1 / (q : ℝ) := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have hp1 : 1 - 1 / (q : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn4 : (n : ℝ) ^ (1 - 1 / (q : ℝ))
      ≤ 4 * m * (W : ℝ) ^ (1 - 1 / (q : ℝ)) := by
    have hnW' : (n : ℝ) ≤ 4 * m * W := by exact_mod_cast hnW.le
    calc (n : ℝ) ^ (1 - 1 / (q : ℝ)) ≤ (4 * m * W : ℝ) ^ (1 - 1 / (q : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg n) hnW' hp0
      _ = (4 * m : ℝ) ^ (1 - 1 / (q : ℝ)) * (W : ℝ) ^ (1 - 1 / (q : ℝ)) :=
          Real.mul_rpow (by positivity) (Nat.cast_nonneg W)
      _ ≤ (4 * m : ℝ) * (W : ℝ) ^ (1 - 1 / (q : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (4 * m : ℝ) ^ (1 - 1 / (q : ℝ)) ≤ (4 * m : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) hp1
            _ = 4 * m := Real.rpow_one _
  have hmq : (m : ℝ) = 2 ^ q := by rw [hmdef]; push_cast; rfl
  have hWp : 0 ≤ (W : ℝ) ^ (1 - 1 / (q : ℝ)) := by positivity
  calc 7 / (22016 * 2 ^ q) * (n : ℝ) ^ (1 - 1 / (q : ℝ))
      ≤ 7 / (22016 * 2 ^ q) * (4 * m * (W : ℝ) ^ (1 - 1 / (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hn4 (by positivity)
    _ = (7 / 1376 : ℝ) * ((W : ℝ) ^ (1 - 1 / (q : ℝ)) / 4) := by
        rw [hmq]; field_simp; ring
    _ ≤ (7 / 1376 : ℝ) * advPM (dyckProduct (blockHeight m ℓ) W) :=
        mul_le_mul_of_nonneg_left hA (by norm_num)
    _ ≤ _ := hQ

/-! ## The `ε` forms -/

/-- The exponent parameter `q = ⌈1/ε⌉₊`: `q ≥ 1` and `1/q ≤ ε`. -/
lemma dyckNL_ceil_spec {ε : ℝ} (hε0 : 0 < ε) :
    1 ≤ ⌈1 / ε⌉₊ ∧ 1 / (⌈1 / ε⌉₊ : ℝ) ≤ ε := by
  have hpos : 0 < 1 / ε := by positivity
  have h1 : 1 / ε ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨Nat.one_le_iff_ne_zero.2 fun h => ?_, ?_⟩
  · rw [h, Nat.cast_zero] at h1; linarith
  · have hq : (0 : ℝ) < ⌈1 / ε⌉₊ := hpos.trans_le h1
    rw [div_le_iff₀ hq]
    rw [div_le_iff₀ hε0] at h1
    linarith

lemma dyckNL_rpow_mono {n : ℕ} (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b) :
    (n : ℝ) ^ a ≤ (n : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hab

/-- **`cor:dyck` (iii).**  For every `ε ∈ (0,1)` there are `C, c > 0` and a
height function `k(n)` with, for every `n ≥ 2`, `k(n) ≤ C·log₂(n+2)`,
`|DyckNF (k n)| ≤ C·log₂(n+2)³`, and
`c·n^{1−ε} ≤ Q_{1/3}(Prod_{DyckNF (k n), n})`.  Explicitly `q = ⌈1/ε⌉₊`,
`k = dyckNL_height q`, `C = (2^{q+1}+6)³`, `c = 7/(22016·2^q)`. -/
theorem dyckNL_nearLinear_lower {ε : ℝ} (hε0 : 0 < ε) (_hε1 : ε < 1) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ k : ℕ → ℕ, ∀ n : ℕ, 2 ≤ n →
      (k n : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + 2)
        ∧ (Fintype.card (DyckNF (k n)) : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + 2) ^ 3
        ∧ c * (n : ℝ) ^ (1 - ε)
            ≤ (qQuery (fun w : Fin n → DyckNF (k n) =>
                wordProd (id : DyckNF (k n) → DyckNF (k n)) w) (1 / 3) : ℝ) := by
  obtain ⟨hq, hqε⟩ := dyckNL_ceil_spec hε0
  set q := ⌈1 / ε⌉₊
  refine ⟨(2 * 2 ^ q + 6) ^ 3, by positivity, 7 / (22016 * 2 ^ q), by positivity,
    dyckNL_height q, fun n hn => ⟨?_, dyckNL_card_le q hn, ?_⟩⟩
  · have h := dyckNL_height_add_two_le q hn
    have hL := dyckNL_one_le_logb n
    have hb : (1 : ℝ) ≤ 2 * 2 ^ q + 6 := by
      have : (0 : ℝ) ≤ 2 ^ q := by positivity
      linarith
    have hcube : (2 * 2 ^ q + 6 : ℝ) ≤ (2 * 2 ^ q + 6) ^ 3 :=
      le_self_pow₀ hb (by norm_num)
    have : (2 * 2 ^ q + 6 : ℝ) * Real.logb 2 ((n : ℝ) + 2)
        ≤ (2 * 2 ^ q + 6) ^ 3 * Real.logb 2 ((n : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right hcube (by linarith)
    linarith
  · refine le_trans ?_ (dyckNL_qQuery_lower_pow hq hn)
    exact mul_le_mul_of_nonneg_left (dyckNL_rpow_mono (by omega) (by linarith))
      (by positivity)

/-- **`cor:aperiodic-envelope-transition`, first clause, `log₂` form.**  For
every `ε ∈ (0,1)` there are `C, c > 0` such that for all `n ≥ 2` and all `N`,
`C·log₂(n+2)³ ≤ N ⇒ c·n^{1−ε} ≤ 𝒬_ap(N, n)`.  Explicitly
`C = (2^{q+1}+6)³`, `c = 7/(22016·2^q)`, `q = ⌈1/ε⌉₊`. -/
theorem dyckNL_aperiodicEnvelope_nearLinear_logb {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ n : ℕ, 2 ≤ n → ∀ N : ℕ,
      C * Real.logb 2 ((n : ℝ) + 2) ^ 3 ≤ N →
        c * (n : ℝ) ^ (1 - ε) ≤ aperiodicEnvelope N n := by
  obtain ⟨C, hC, c, hc, k, hk⟩ := dyckNL_nearLinear_lower hε0 hε1
  refine ⟨C, hC, c, hc, fun n hn N hN => ?_⟩
  obtain ⟨-, hcard, hQ⟩ := hk n hn
  have hcardN : Fintype.card (DyckNF (k n)) ≤ N := by
    exact_mod_cast hcard.trans hN
  exact hQ.trans (le_aperiodicEnvelope hcardN)

lemma dyckNL_logb_le_two_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Real.logb 2 x ≤ 2 * Real.log x := by
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

/-- **`cor:aperiodic-envelope-transition`, first clause** (natural logarithm, as in
the paper).  For every `ε ∈ (0,1)` there are `C, c > 0` and `n₀` such that for
all `n ≥ n₀` and all `N`, `C·(log(n+2))³ ≤ N ⇒ c·n^{1−ε} ≤ 𝒬_ap(N, n)`.
Explicitly `n₀ = 2`, `C = 8·(2^{q+1}+6)³`, `c = 7/(22016·2^q)`, `q = ⌈1/ε⌉₊`. -/
theorem dyckNL_aperiodicEnvelope_nearLinear {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ N : ℕ,
      C * Real.log ((n : ℝ) + 2) ^ 3 ≤ N →
        c * (n : ℝ) ^ (1 - ε) ≤ aperiodicEnvelope N n := by
  obtain ⟨C, hC, c, hc, h⟩ := dyckNL_aperiodicEnvelope_nearLinear_logb hε0 hε1
  refine ⟨8 * C, by positivity, c, hc, 2, fun n hn N hN => h n hn N ?_⟩
  have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hb := dyckNL_logb_le_two_mul_log hx
  have h0 : 0 ≤ Real.logb 2 ((n : ℝ) + 2) := by
    have := dyckNL_one_le_logb n; linarith
  have h3 : Real.logb 2 ((n : ℝ) + 2) ^ 3 ≤ 8 * Real.log ((n : ℝ) + 2) ^ 3 := by
    calc Real.logb 2 ((n : ℝ) + 2) ^ 3 ≤ (2 * Real.log ((n : ℝ) + 2)) ^ 3 :=
          pow_le_pow_left₀ h0 hb 3
      _ = 8 * Real.log ((n : ℝ) + 2) ^ 3 := by ring
  calc C * Real.logb 2 ((n : ℝ) + 2) ^ 3 ≤ C * (8 * Real.log ((n : ℝ) + 2) ^ 3) :=
        mul_le_mul_of_nonneg_left h3 hC.le
    _ = 8 * C * Real.log ((n : ℝ) + 2) ^ 3 := by ring
    _ ≤ N := hN


end MonoidProduct
