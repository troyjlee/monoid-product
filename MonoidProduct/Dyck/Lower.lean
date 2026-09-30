import MonoidProduct.Dyck.Amplify
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The fixed-base exponential-in-depth Dyck lower bound

The first bound of `thm:dyck-lb` (Ambainis et al. [ABIKPSSV20]), in adversary
form.

Fix `m = 4`.  The exact-count branching factor is `8`, the per-level gain is
`4`, and `blockHeight 4 ℓ + 2 = 4 + 10ℓ`.  Choosing `r = n / blockWidth 4 ℓ`
blocks in the block amplification and bounding the width by
`blockWidth 4 ℓ + 2 ≤ 4·8^ℓ` gives, for every even `n ≥ 4·8^ℓ` and every depth
cap `k ≥ 4 + 10ℓ`,

  `√n · √2^ℓ ≤ 2√2 · ADV±(dyck k n)`,

with the constant cleared to the right-hand side.  The floor loss
of `r = ⌊n/w⌋` is paid by `n ≤ 2rw` (true as soon as `r ≥ 1`), and the width
loss by `w ≤ 4·8^ℓ`; together they cost the factor `√8 = 2√2`.

Everything is in natural-number parameters; no logarithm appears.  The
`ℓ := (k−4)/10` instantiation is the paper's "choose the recursion depth from
the requested Dyck depth" step, giving `2^(Ω(k))` at fixed even lengths.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

/-! ## Width bounds -/

/-- The block width grows at most like `4·(2m)^ℓ`; the slack `+2` is exactly
what the recurrence `w ↦ 2m(w+1)` regenerates each step, so it is the
statement that closes the induction. -/
theorem blockWidth_add_two_le (m : ℕ) (hm : 1 ≤ m) (ℓ : ℕ) :
    blockWidth m ℓ + 2 ≤ 4 * (2 * m) ^ ℓ := by
  induction ℓ with
  | zero => rw [blockWidth_zero, pow_zero]; omega
  | succ ℓ ih =>
      rw [blockWidth_succ]
      calc 2 * m * (blockWidth m ℓ + 1) + 2
          ≤ 2 * m * (blockWidth m ℓ + 1) + 2 * m := by omega
        _ = 2 * m * (blockWidth m ℓ + 2) := by ring
        _ ≤ 2 * m * (4 * (2 * m) ^ ℓ) := Nat.mul_le_mul_left _ ih
        _ = 4 * (2 * m) ^ (ℓ + 1) := by ring

lemma blockWidth_pos (m ℓ : ℕ) (hm : 1 ≤ m) : 0 < blockWidth m ℓ := by
  cases ℓ with
  | zero => rw [blockWidth_zero]; omega
  | succ ℓ =>
      rw [blockWidth_succ]
      exact Nat.mul_pos (by omega) (Nat.succ_pos _)

/-! ## The fixed-base theorem -/

/-- **The fixed-base bound (`thm:dyck-lb`).**  The fixed-base exponential-in-depth lower bound at
`m = 4`: for even `n` of size at least `4·8^ℓ` and any depth cap
`k ≥ 4 + 10ℓ`,

  `√n · √2^ℓ ≤ 2√2 · ADV±(dyck k n)`. -/
theorem sqrt_mul_sqrt_two_pow_le_advPM_dyck (ℓ n k : ℕ)
    (heven : Even n) (hfit : 4 * 8 ^ ℓ ≤ n) (hk : 4 + 10 * ℓ ≤ k) :
    Real.sqrt n * Real.sqrt 2 ^ ℓ
      ≤ 2 * Real.sqrt 2 * advPM (dyck k n) := by
  -- the block count and the two integer inequalities it satisfies
  set w := blockWidth 4 ℓ with hwdef
  have hw4 : w + 2 ≤ 4 * 8 ^ ℓ := by
    have h := blockWidth_add_two_le 4 (by norm_num) ℓ
    norm_num at h
    exact h
  have hw0 : 0 < w := blockWidth_pos 4 ℓ (by norm_num)
  have hwn : w ≤ n := by omega
  set r := n / w with hrdef
  have hr : 0 < r := Nat.div_pos hwn hw0
  have hlen : r * w ≤ n := Nat.div_mul_le_self n w
  have hn2rw : n ≤ 2 * (r * w) := by
    have hmod := Nat.div_add_mod n w
    rw [← hrdef] at hmod
    have hlt : n % w < w := Nat.mod_lt _ hw0
    calc n = w * r + n % w := by omega
      _ ≤ w * r + w := by omega
      _ = w * (r + 1) := by ring
      _ ≤ w * (2 * r) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (r * w) := by ring
  have hn16 : n ≤ 8 * r * 8 ^ ℓ := by
    calc n ≤ 2 * (r * w) := hn2rw
      _ ≤ 2 * (r * (4 * 8 ^ ℓ)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = 8 * r * 8 ^ ℓ := by ring
  -- the amplified adversary bound at depth cap `k`
  have hkk : blockHeight 4 ℓ + 2 ≤ k := by
    rw [blockHeight_eq]
    omega
  have hmain := sqrt_mul_pow_le_advPM_dyck 4 ℓ r n k (by norm_num) hr hlen
    heven hkk
  push_cast at hmain
  -- compare the squares: `n·2^ℓ ≤ 8r·8^ℓ·2^ℓ`
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hL : (Real.sqrt n * Real.sqrt 2 ^ ℓ) ^ 2 = (n : ℝ) * 2 ^ ℓ := by
    calc (Real.sqrt n * Real.sqrt 2 ^ ℓ) ^ 2
        = Real.sqrt n ^ 2 * (Real.sqrt 2 ^ 2) ^ ℓ := by
          rw [mul_pow, pow_right_comm]
      _ = (n : ℝ) * 2 ^ ℓ := by rw [h2, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hR : (2 * Real.sqrt 2 * (Real.sqrt r * 4 ^ ℓ)) ^ 2
      = 8 * (r : ℝ) * (8 ^ ℓ * 2 ^ ℓ) := by
    have h4 : (((4 : ℝ) ^ ℓ)) ^ 2 = 8 ^ ℓ * 2 ^ ℓ := by
      rw [pow_right_comm, ← mul_pow]
      norm_num
    calc (2 * Real.sqrt 2 * (Real.sqrt r * 4 ^ ℓ)) ^ 2
        = 2 ^ 2 * Real.sqrt 2 ^ 2 * (Real.sqrt r ^ 2 * ((4 : ℝ) ^ ℓ) ^ 2) := by
          ring
      _ = 8 * (r : ℝ) * (8 ^ ℓ * 2 ^ ℓ) := by
          rw [h2, h4, Real.sq_sqrt (Nat.cast_nonneg r)]
          ring
  have hsq_ineq : (n : ℝ) * 2 ^ ℓ ≤ 8 * (r : ℝ) * (8 ^ ℓ * 2 ^ ℓ) := by
    have hcast : (n : ℝ) ≤ 8 * (r : ℝ) * 8 ^ ℓ := by exact_mod_cast hn16
    calc (n : ℝ) * 2 ^ ℓ ≤ 8 * (r : ℝ) * 8 ^ ℓ * 2 ^ ℓ :=
          mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = 8 * (r : ℝ) * (8 ^ ℓ * 2 ^ ℓ) := by ring
  have hle : Real.sqrt n * Real.sqrt 2 ^ ℓ
      ≤ 2 * Real.sqrt 2 * (Real.sqrt r * 4 ^ ℓ) := by
    have hsq2 : (Real.sqrt n * Real.sqrt 2 ^ ℓ) ^ 2
        ≤ (2 * Real.sqrt 2 * (Real.sqrt r * 4 ^ ℓ)) ^ 2 := by
      rw [hL, hR]
      exact hsq_ineq
    have h := Real.sqrt_le_sqrt hsq2
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h
  calc Real.sqrt n * Real.sqrt 2 ^ ℓ
      ≤ 2 * Real.sqrt 2 * (Real.sqrt r * 4 ^ ℓ) := hle
    _ ≤ 2 * Real.sqrt 2 * advPM (dyck k n) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

/-- **The fixed-base bound (`thm:dyck-lb`)**, depth-first form: for a requested depth `k ≥ 4`, run the
reduction at recursion depth `ℓ = (k−4)/10`.  The gain is `√2^((k-4)/10)`,
i.e. `2^(Ω(k))`, at every even length `n ≥ 4·8^((k−4)/10)`. -/
theorem sqrt_mul_sqrt_two_pow_le_advPM_dyck_of_depth (k n : ℕ)
    (heven : Even n) (hfit : 4 * 8 ^ ((k - 4) / 10) ≤ n) (h4 : 4 ≤ k) :
    Real.sqrt n * Real.sqrt 2 ^ ((k - 4) / 10)
      ≤ 2 * Real.sqrt 2 * advPM (dyck k n) :=
  sqrt_mul_sqrt_two_pow_le_advPM_dyck _ n k heven hfit (by omega)

/-! ## The integer-exponent near-linear regime

The second bound of `thm:dyck-lb`, at integer exponents.

For an integer `q`, any `m` with `(2m)^(q-1) ≤ m^q` turns the special-length
bound `m^ℓ ≤ ADV±` into `w^(q-1) ≤ 4^(q-1) · ADV±^q` at the encoding lengths
`w = blockWidth m ℓ` — the exact statement corresponding to exponent
`1 − 1/q`, with the depth `blockHeight m ℓ = 2 + 2ℓ(m+1) = Θ_m(log w)`.
`m = 2^q` always qualifies, since `(2^(q+1))^(q-1) = 2^(q²-1) ≤ 2^(q²)`.
No real exponent or logarithm appears; the `n^(1-ε)` reading is documentation.
-/

/-- The combinatorial core, in `ℕ`: the width to the `q−1` against the gain to
the `q`. -/
lemma blockWidth_pow_le (m q ℓ : ℕ) (hm : 1 ≤ m)
    (hmq : (2 * m) ^ (q - 1) ≤ m ^ q) :
    blockWidth m ℓ ^ (q - 1) ≤ 4 ^ (q - 1) * (m ^ ℓ) ^ q := by
  have hw : blockWidth m ℓ ≤ 4 * (2 * m) ^ ℓ := by
    have := blockWidth_add_two_le m hm ℓ
    omega
  calc blockWidth m ℓ ^ (q - 1)
      ≤ (4 * (2 * m) ^ ℓ) ^ (q - 1) := Nat.pow_le_pow_left hw _
    _ = 4 ^ (q - 1) * ((2 * m) ^ (q - 1)) ^ ℓ := by
        rw [mul_pow, pow_right_comm]
    _ ≤ 4 ^ (q - 1) * (m ^ q) ^ ℓ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmq ℓ)
    _ = 4 ^ (q - 1) * (m ^ ℓ) ^ q := by rw [pow_right_comm]

/-- **The near-linear bound (`thm:dyck-lb`).**  The integer-exponent near-linear lower bound at the
encoding lengths: if `(2m)^(q-1) ≤ m^q` then

  `w^(q-1) ≤ 4^(q-1) · ADV±(dyck (blockHeight m ℓ) w)^q`,  `w = blockWidth m ℓ`.

The depth is `2 + 2ℓ(m+1)`, logarithmic in `w` for fixed `m`. -/
theorem advPM_dyck_nearLinear_int (m q ℓ : ℕ) (hm : 0 < m)
    (hmq : (2 * m) ^ (q - 1) ≤ m ^ q) :
    (blockWidth m ℓ : ℝ) ^ (q - 1)
      ≤ 4 ^ (q - 1)
        * advPM (dyck (blockHeight m ℓ) (blockWidth m ℓ)) ^ q := by
  have hblock := pow_le_advPM_dyck_block m ℓ hm
  have hcast : (blockWidth m ℓ : ℝ) ^ (q - 1)
      ≤ 4 ^ (q - 1) * ((m : ℝ) ^ ℓ) ^ q := by
    exact_mod_cast blockWidth_pow_le m q ℓ hm hmq
  refine hcast.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact pow_le_pow_left₀ (by positivity) hblock q

/-- `m = 2^q` satisfies the near-linear hypothesis for every `q`. -/
lemma two_pow_nearLinear_hyp (q : ℕ) :
    (2 * 2 ^ q) ^ (q - 1) ≤ (2 ^ q) ^ q := by
  have hexp : (q + 1) * (q - 1) ≤ q * q := by
    cases q with
    | zero => omega
    | succ s =>
        have hs : s + 1 - 1 = s := rfl
        rw [hs]
        calc (s + 1 + 1) * s = s * s + 2 * s := by ring
          _ ≤ s * s + 2 * s + 1 := Nat.le_succ _
          _ = (s + 1) * (s + 1) := by ring
  calc (2 * 2 ^ q) ^ (q - 1) = 2 ^ ((q + 1) * (q - 1)) := by
        rw [← pow_succ', ← pow_mul]
    _ ≤ 2 ^ (q * q) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = (2 ^ q) ^ q := by rw [← pow_mul]

/-- **The near-linear bound (`thm:dyck-lb`)**, instantiated at `m = 2^q`: for every integer `q` there
is a concrete family with exponent `1 − 1/q` and depth `Θ_q(log w)`. -/
theorem advPM_dyck_nearLinear_int' (q ℓ : ℕ) :
    (blockWidth (2 ^ q) ℓ : ℝ) ^ (q - 1)
      ≤ 4 ^ (q - 1)
        * advPM (dyck (blockHeight (2 ^ q) ℓ) (blockWidth (2 ^ q) ℓ)) ^ q :=
  advPM_dyck_nearLinear_int (2 ^ q) q ℓ (pow_pos (by norm_num) q)
    (two_pow_nearLinear_hyp q)

/-! ## Finite sanity checks -/

example : blockWidth 4 1 = 24 := by decide
example : blockWidth 4 2 = 200 := by decide
example : blockWidth 4 2 + 2 ≤ 4 * 8 ^ 2 := by decide
example : blockHeight 4 2 + 2 = 4 + 10 * 2 := by decide

end MonoidProduct
