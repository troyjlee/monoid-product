import MonoidProduct.Aperiodic.CubeRoot.Assembly
import MonoidProduct.Aperiodic.CubeRoot.MunnPackage
import MonoidProduct.Aperiodic.CubeRoot.Recurrence
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The strong induction, and the cube-root factor

The carrier recurrence, run over monoid *types*: every finite aperiodic
monoid `M'` of order at most `s` satisfies the alphabet-uniform word-product
contract at `(B^K)^(t + (m/t² + 1)·Λ)`, where `B = s·L(n₀)` is the base,
`t = cubeThreshold s` the size threshold, `Λ = ⌈log₂(s+2)⌉` the layers one
peel costs, and `m` the strong-induction measure on the carrier.  The step is
`Assembly.lean`'s `hasWordProdDualPoly_step` at `munnPackage`; the descent
into the Rees quotients is priced by `exponent_step`; the normalization at
the top is `pow_recurrenceExponent_le_cubeRootFactor`.  **`K` is chosen here:
`K = 256`**, from the majorants below — each constant of the development is
bounded by an explicit power of `B`, with deliberate slack at every step, and
the two budget lines are the base case (`small ≤ B^(130·t) ≤ (B^K)^t`) and
the descent (`tower · combine ≤ B^(100·Λ) ≤ (B^K)^Λ`).

Endpoint: `hasWordProdDualPoly_cubeRootFactor` — for every finite aperiodic
monoid, `HasWordProdDualPoly M n₀ (cubeRootFactor 256 |M| n₀)`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open LocallyThin ApexAdapter

/-- The per-layer base of the assembly, `B = s · L(n₀)`. -/
noncomputable def assemblyBase (s n₀ : ℕ) : ℝ := (s : ℝ) * cubeLog n₀

/-! ## Majorants

Every constant of the development, bounded by an explicit power of `B`.
The exponents are deliberately generous: the point is that each bound is a
one-line `nlinarith`/`gcongr` away, not that it is tight. -/

section Majorants

variable {s n₀ : ℕ}

lemma three_le_cubeLog (n : ℕ) : 3 ≤ cubeLog n := by
  have h : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by norm_num) (by omega)
  unfold cubeLog
  omega

lemma three_le_assemblyBase (hs : 1 ≤ s) : (3 : ℝ) ≤ assemblyBase s n₀ := by
  have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have h3 : (3 : ℝ) ≤ (cubeLog n₀ : ℝ) := by exact_mod_cast three_le_cubeLog n₀
  calc (3 : ℝ) = 1 * 3 := by norm_num
    _ ≤ (s : ℝ) * cubeLog n₀ := mul_le_mul h1 h3 (by norm_num) (by linarith)

lemma one_le_assemblyBase (hs : 1 ≤ s) : (1 : ℝ) ≤ assemblyBase s n₀ :=
  le_trans (by norm_num) (three_le_assemblyBase hs)

lemma two_le_assemblyBase (hs : 1 ≤ s) : (2 : ℝ) ≤ assemblyBase s n₀ :=
  le_trans (by norm_num) (three_le_assemblyBase hs)

lemma cast_le_assemblyBase (_hs : 1 ≤ s) : (s : ℝ) ≤ assemblyBase s n₀ := by
  have h3 : (1 : ℝ) ≤ (cubeLog n₀ : ℝ) := by
    have := three_le_cubeLog n₀
    exact_mod_cast by omega
  calc (s : ℝ) = s * 1 := (mul_one _).symm
    _ ≤ (s : ℝ) * cubeLog n₀ := by
        exact mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)

lemma cubeLog_le_assemblyBase (hs : 1 ≤ s) :
    (cubeLog n₀ : ℝ) ≤ assemblyBase s n₀ := by
  have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  calc (cubeLog n₀ : ℝ) = 1 * cubeLog n₀ := (one_mul _).symm
    _ ≤ (s : ℝ) * cubeLog n₀ :=
        mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)

lemma one_le_assemblyBase_pow (hs : 1 ≤ s) (k : ℕ) :
    (1 : ℝ) ≤ assemblyBase s n₀ ^ k :=
  one_le_pow₀ (one_le_assemblyBase hs)

lemma assemblyBase_pow_le_pow (hs : 1 ≤ s) {a b : ℕ} (h : a ≤ b) :
    assemblyBase s n₀ ^ a ≤ assemblyBase s n₀ ^ b :=
  pow_le_pow_right₀ (one_le_assemblyBase hs) h

/-- Products of `B`-power bounds. -/
lemma mul_le_assemblyBase_pow (hs : 1 ≤ s) {x y : ℝ} {a b : ℕ}
    (hx : x ≤ assemblyBase s n₀ ^ a) (hy : y ≤ assemblyBase s n₀ ^ b)
    (hy0 : 0 ≤ y) : x * y ≤ assemblyBase s n₀ ^ (a + b) := by
  rw [pow_add]
  exact mul_le_mul hx hy hy0
    (le_trans zero_le_one (one_le_assemblyBase_pow hs a))

/-- Numerals: `c ≤ 2^k` puts `c` under `B^k`. -/
lemma numeral_le_assemblyBase_pow (hs : 1 ≤ s) {c : ℝ} {k : ℕ}
    (hc : c ≤ 2 ^ k) : c ≤ assemblyBase s n₀ ^ k :=
  le_trans hc (pow_le_pow_left₀ (by norm_num) (two_le_assemblyBase hs) k)

/-- **The shifted-horizon logarithm**: `⌈log₂(n₀ + j)⌉ ≤ ⌈log₂(n₀ + 2)⌉ + j`,
since `n₀ + j ≤ (n₀ + 2) · 2^j`. -/
lemma clog_add_le (n₀ j : ℕ) :
    Nat.clog 2 (n₀ + j) ≤ Nat.clog 2 (n₀ + 2) + j := by
  refine Nat.clog_le_of_le_pow ?_
  have h1 : n₀ + 2 ≤ 2 ^ Nat.clog 2 (n₀ + 2) := Nat.le_pow_clog (by norm_num) _
  have h2 : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
  have h3 : 2 ^ (Nat.clog 2 (n₀ + 2) + j) = 2 ^ Nat.clog 2 (n₀ + 2) * 2 ^ j :=
    pow_add 2 _ _
  have h4 : (n₀ + 2) * 2 ^ j ≤ 2 ^ Nat.clog 2 (n₀ + 2) * 2 ^ j :=
    Nat.mul_le_mul_right _ h1
  have h5 : n₀ + j ≤ (n₀ + 2) * 2 ^ j := by
    have h6 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    nlinarith
  omega

/-- All shifted logarithmic factors sit under `B²`. -/
lemma clogfac_le_sq (hs : 1 ≤ s) {j : ℕ} (hj : j ≤ 2 * s + 4) :
    (Nat.clog 2 (n₀ + j) : ℝ) + 2 ≤ assemblyBase s n₀ ^ 2 := by
  have hB3 := three_le_assemblyBase (n₀ := n₀) hs
  have hnat : Nat.clog 2 (n₀ + j) + 2 ≤ cubeLog n₀ + j := by
    have := clog_add_le n₀ j
    unfold cubeLog
    omega
  have hreal : (Nat.clog 2 (n₀ + j) : ℝ) + 2 ≤ (cubeLog n₀ : ℝ) + j := by
    exact_mod_cast hnat
  have hj' : (j : ℝ) ≤ 2 * (s : ℝ) + 4 := by exact_mod_cast hj
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have h3L : (3 : ℝ) ≤ (cubeLog n₀ : ℝ) := by exact_mod_cast three_le_cubeLog n₀
  have h7 : (cubeLog n₀ : ℝ) + j ≤ 3 * assemblyBase s n₀ := by
    unfold assemblyBase
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (cubeLog n₀ : ℝ) - 3)
      (by linarith : (0 : ℝ) ≤ 3 * (s : ℝ) - 1)]
  have h8 : 3 * assemblyBase s n₀ ≤ assemblyBase s n₀ ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ assemblyBase s n₀)
      (by linarith : (0 : ℝ) ≤ assemblyBase s n₀ - 3)]
  linarith

/-- One plus a carrier bound sits under `B²`. -/
lemma card_add_one_le_sq (hs : 1 ≤ s) {N : ℕ} (hN : N ≤ s) :
    (N : ℝ) + 1 ≤ assemblyBase s n₀ ^ 2 := by
  have hB2 := two_le_assemblyBase (n₀ := n₀) hs
  have hsB := cast_le_assemblyBase (n₀ := n₀) hs
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have h1 : (N : ℝ) + 1 ≤ 2 * (s : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hN
    linarith
  calc (N : ℝ) + 1 ≤ 2 * (s : ℝ) := h1
    _ ≤ assemblyBase s n₀ * assemblyBase s n₀ :=
        mul_le_mul hB2 hsB (Nat.cast_nonneg _) (by linarith)
    _ = assemblyBase s n₀ ^ 2 := (sq (assemblyBase s n₀)).symm

/-- `agsStep`, at any shifted horizon and any carrier under `s`. -/
lemma agsStep_le_pow (hs : 1 ≤ s) (T : Type) [Fintype T]
    (hT : Fintype.card T ≤ s) {j : ℕ} (hj : j ≤ 2 * s + 3) :
    agsStep (n₀ + j) T ≤ assemblyBase s n₀ ^ 64 := by
  have hcard := card_add_one_le_sq (n₀ := n₀) hs hT
  have hclog : (Nat.clog 2 (n₀ + j + 1) : ℝ) + 2 ≤ assemblyBase s n₀ ^ 2 :=
    clogfac_le_sq hs (j := j + 1) (by omega)
  rw [agsStep]
  have h1 : ((Fintype.card T : ℝ) + 1) ^ 5 ≤ assemblyBase s n₀ ^ 10 := by
    calc ((Fintype.card T : ℝ) + 1) ^ 5 ≤ (assemblyBase s n₀ ^ 2) ^ 5 :=
          pow_le_pow_left₀ (by positivity) hcard 5
      _ = assemblyBase s n₀ ^ 10 := by rw [← pow_mul]
  have h2 : ((Nat.clog 2 (n₀ + j + 1) : ℝ) + 2) ^ 2 ≤ assemblyBase s n₀ ^ 4 := by
    calc ((Nat.clog 2 (n₀ + j + 1) : ℝ) + 2) ^ 2 ≤ (assemblyBase s n₀ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hclog 2
      _ = assemblyBase s n₀ ^ 4 := by rw [← pow_mul]
  have h40 : (2 : ℝ) ^ 40 ≤ assemblyBase s n₀ ^ 40 :=
    numeral_le_assemblyBase_pow hs le_rfl
  calc (2 : ℝ) ^ 40 * ((Fintype.card T : ℝ) + 1) ^ 5
        * ((Nat.clog 2 (n₀ + j + 1) : ℝ) + 2) ^ 2
      ≤ assemblyBase s n₀ ^ (40 + 10 + 4) := by
        refine mul_le_assemblyBase_pow hs
          (mul_le_assemblyBase_pow hs h40 h1 (by positivity)) h2 (by positivity)
    _ ≤ assemblyBase s n₀ ^ 64 := assemblyBase_pow_le_pow hs (by norm_num)

/-- `axisStep`, likewise. -/
lemma axisStep_le_pow (hs : 1 ≤ s) (T : Type) [Fintype T]
    (hT : Fintype.card T ≤ s) {j : ℕ} (hj : j ≤ 2 * s + 3) :
    axisStep (n₀ + j) T ≤ assemblyBase s n₀ ^ 80 := by
  have hags := agsStep_le_pow (n₀ := n₀) hs T hT hj
  have hcard := card_add_one_le_sq (n₀ := n₀) hs hT
  have hclog : (Nat.clog 2 (n₀ + j + 1) : ℝ) + 2 ≤ assemblyBase s n₀ ^ 2 :=
    clogfac_le_sq hs (j := j + 1) (by omega)
  have hclog' : (Nat.clog 2 (n₀ + j + 1) : ℝ) ≤ assemblyBase s n₀ ^ 2 := by linarith
  have hsqrt : Real.sqrt ((Fintype.card T : ℝ) + 1) ≤ assemblyBase s n₀ ^ 2 := by
    refine le_trans (Real.sqrt_le_self_iff.2 (Or.inr ?_)) hcard
    have : (0 : ℝ) ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
    linarith
  have h24 : (24 : ℝ) ≤ assemblyBase s n₀ ^ 5 :=
    numeral_le_assemblyBase_pow hs (by norm_num)
  have hcardB : (Fintype.card T : ℝ) ≤ assemblyBase s n₀ ^ 1 := by
    have h1 := card_add_one_le_sq (n₀ := n₀) hs hT
    have h2 := cast_le_assemblyBase (n₀ := n₀) hs
    have h3 := (Nat.cast_le (α := ℝ)).2 hT
    rw [pow_one]
    linarith
  have hparen : (Nat.clog 2 (n₀ + j + 1) : ℝ)
        * (24 * Real.sqrt ((Fintype.card T : ℝ) + 1)) + 2 * (Fintype.card T : ℝ)
      ≤ assemblyBase s n₀ ^ 10 := by
    have hterm1 : (Nat.clog 2 (n₀ + j + 1) : ℝ)
        * (24 * Real.sqrt ((Fintype.card T : ℝ) + 1))
        ≤ assemblyBase s n₀ ^ 9 := by
      have hin : (24 : ℝ) * Real.sqrt ((Fintype.card T : ℝ) + 1)
          ≤ assemblyBase s n₀ ^ 7 :=
        mul_le_assemblyBase_pow hs h24 hsqrt (Real.sqrt_nonneg _)
      calc (Nat.clog 2 (n₀ + j + 1) : ℝ)
            * (24 * Real.sqrt ((Fintype.card T : ℝ) + 1))
          ≤ assemblyBase s n₀ ^ (2 + 7) :=
            mul_le_assemblyBase_pow hs hclog' hin
              (by positivity)
        _ = assemblyBase s n₀ ^ 9 := by norm_num
    have hterm2 : 2 * (Fintype.card T : ℝ) ≤ assemblyBase s n₀ ^ 2 := by
      have h2B : (2 : ℝ) ≤ assemblyBase s n₀ ^ 1 := by
        rw [pow_one]; exact two_le_assemblyBase hs
      calc 2 * (Fintype.card T : ℝ) ≤ assemblyBase s n₀ ^ (1 + 1) :=
            mul_le_assemblyBase_pow hs h2B hcardB (Nat.cast_nonneg _)
        _ = assemblyBase s n₀ ^ 2 := by norm_num
    have h9le : assemblyBase s n₀ ^ 9 + assemblyBase s n₀ ^ 2
        ≤ 2 * assemblyBase s n₀ ^ 9 := by
      have := assemblyBase_pow_le_pow (n₀ := n₀) hs (show 2 ≤ 9 by norm_num)
      linarith
    have h2pow : 2 * assemblyBase s n₀ ^ 9 ≤ assemblyBase s n₀ ^ 10 := by
      have hB2 := two_le_assemblyBase (n₀ := n₀) hs
      have hp : (0 : ℝ) ≤ assemblyBase s n₀ ^ 9 := by positivity
      calc 2 * assemblyBase s n₀ ^ 9 ≤ assemblyBase s n₀ * assemblyBase s n₀ ^ 9 :=
            mul_le_mul_of_nonneg_right hB2 hp
        _ = assemblyBase s n₀ ^ 10 := by ring
    linarith
  rw [axisStep]
  have h2B : (2 : ℝ) ≤ assemblyBase s n₀ ^ 1 := by
    rw [pow_one]; exact two_le_assemblyBase hs
  calc 2 * agsStep (n₀ + j) T
        * ((Nat.clog 2 (n₀ + j + 1) : ℝ)
            * (24 * Real.sqrt ((Fintype.card T : ℝ) + 1))
          + 2 * (Fintype.card T : ℝ))
      ≤ assemblyBase s n₀ ^ (1 + 64 + 10) := by
        refine mul_le_assemblyBase_pow hs
          (mul_le_assemblyBase_pow hs h2B hags (le_trans zero_le_one (one_le_agsStep _ _)))
          hparen ?_
        have hc := Real.sqrt_nonneg ((Fintype.card T : ℝ) + 1)
        have hcl : (0 : ℝ) ≤ (Nat.clog 2 (n₀ + j + 1) : ℝ) := Nat.cast_nonneg _
        have hcd : (0 : ℝ) ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
        positivity
    _ ≤ assemblyBase s n₀ ^ 80 := assemblyBase_pow_le_pow hs (by norm_num)

/-- Absorbing a bound into a higher power. -/
lemma le_assemblyBase_pow_mono (hs : 1 ≤ s) {x : ℝ} {a b : ℕ}
    (hx : x ≤ assemblyBase s n₀ ^ a) (hab : a ≤ b) : x ≤ assemblyBase s n₀ ^ b :=
  le_trans hx (assemblyBase_pow_le_pow hs hab)

/-- A numeral times a power, absorbed: `c ≤ 2^k` gives
`c · x ≤ B^(k+a)` from `x ≤ B^a`. -/
lemma numeral_mul_le_assemblyBase_pow (hs : 1 ≤ s) {c x : ℝ} {k a : ℕ}
    (hc : c ≤ 2 ^ k) (hx : x ≤ assemblyBase s n₀ ^ a) (hx0 : 0 ≤ x) :
    c * x ≤ assemblyBase s n₀ ^ (k + a) :=
  mul_le_assemblyBase_pow hs (numeral_le_assemblyBase_pow hs hc) hx hx0

/-- Sums absorb into one higher power: `x ≤ B^a` and `y ≤ B^a` give
`x + y ≤ B^(a+1)`. -/
lemma add_le_assemblyBase_pow (hs : 1 ≤ s) {x y : ℝ} {a : ℕ}
    (hx : x ≤ assemblyBase s n₀ ^ a) (hy : y ≤ assemblyBase s n₀ ^ a) :
    x + y ≤ assemblyBase s n₀ ^ (a + 1) := by
  have hB2 := two_le_assemblyBase (n₀ := n₀) hs
  have hp : (0 : ℝ) ≤ assemblyBase s n₀ ^ a := by positivity
  calc x + y ≤ 2 * assemblyBase s n₀ ^ a := by linarith
    _ ≤ assemblyBase s n₀ * assemblyBase s n₀ ^ a :=
        mul_le_mul_of_nonneg_right hB2 hp
    _ = assemblyBase s n₀ ^ (a + 1) := by ring

/-- `axisConst`, likewise. -/
lemma axisConst_le_pow (hs : 1 ≤ s) (T : Type) [Fintype T]
    (hT : Fintype.card T ≤ s) {j : ℕ} (hj : j ≤ 2 * s + 2) :
    axisConst (n₀ + j) T ≤ assemblyBase s n₀ ^ 85 := by
  have hclog : (Nat.clog 2 (n₀ + j + 1) : ℝ) + 2 ≤ assemblyBase s n₀ ^ 2 :=
    clogfac_le_sq hs (j := j + 1) (by omega)
  have hclog' : (Nat.clog 2 (n₀ + j + 1) : ℝ) ≤ assemblyBase s n₀ ^ 2 := by linarith
  rw [axisConst]
  refine max_le ?_ ?_
  · rw [axisBase]
    have hin : (48 : ℝ) * (Nat.clog 2 (n₀ + j + 1) : ℝ) + 2
        ≤ assemblyBase s n₀ ^ 9 := by
      have hmul : (48 : ℝ) * (Nat.clog 2 (n₀ + j + 1) : ℝ)
          ≤ assemblyBase s n₀ ^ (6 + 2) :=
        numeral_mul_le_assemblyBase_pow hs (by norm_num) hclog' (Nat.cast_nonneg _)
      have h2 : (2 : ℝ) ≤ assemblyBase s n₀ ^ 8 :=
        numeral_le_assemblyBase_pow hs (by norm_num)
      exact add_le_assemblyBase_pow hs hmul h2
    have h96 : (96 : ℝ) * ((48 : ℝ) * (Nat.clog 2 (n₀ + j + 1) : ℝ) + 2)
        ≤ assemblyBase s n₀ ^ (7 + 9) := by
      refine numeral_mul_le_assemblyBase_pow hs (by norm_num) hin ?_
      have : (0 : ℝ) ≤ (Nat.clog 2 (n₀ + j + 1) : ℝ) := Nat.cast_nonneg _
      linarith
    exact le_assemblyBase_pow_mono hs h96 (by norm_num)
  · have hstep := axisStep_le_pow (n₀ := n₀) hs T hT (j := j + 1) (by omega)
    have hcardB : (Fintype.card T : ℝ) ≤ assemblyBase s n₀ ^ 1 := by
      rw [pow_one]
      exact le_trans ((Nat.cast_le (α := ℝ)).2 hT) (cast_le_assemblyBase hs)
    have h6 : (6 : ℝ) * axisStep (n₀ + j + 1) T ≤ assemblyBase s n₀ ^ (3 + 80) :=
      numeral_mul_le_assemblyBase_pow hs (by norm_num) hstep (axisStep_nonneg _ _)
    have hfull : (6 : ℝ) * axisStep (n₀ + j + 1) T * (Fintype.card T : ℝ)
        ≤ assemblyBase s n₀ ^ (3 + 80 + 1) :=
      mul_le_assemblyBase_pow hs h6 hcardB (Nat.cast_nonneg _)
    exact le_assemblyBase_pow_mono hs hfull (by norm_num)

/-- The tower's per-layer coefficient at cost zero. -/
lemma thinStep_zero_add_one_le (hs : 1 ≤ s) {N : ℕ} (hN : N ≤ s) :
    LocallyThin.thinStep n₀ N 0 + 1 ≤ assemblyBase s n₀ ^ 11 := by
  have hcard := card_add_one_le_sq (n₀ := n₀) hs hN
  have hL : ((Nat.clog 2 (n₀ + 2) : ℝ) + 2) ≤ assemblyBase s n₀ := by
    have h1 : ((Nat.clog 2 (n₀ + 2) : ℝ) + 2) = (cubeLog n₀ : ℝ) := by
      unfold cubeLog
      push_cast
      ring
    rw [h1]
    exact cubeLog_le_assemblyBase hs
  rw [LocallyThin.thinStep]
  have h1 : ((N : ℝ) + 1) ^ 4 ≤ assemblyBase s n₀ ^ 8 := by
    calc ((N : ℝ) + 1) ^ 4 ≤ (assemblyBase s n₀ ^ 2) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hcard 4
      _ = assemblyBase s n₀ ^ 8 := by rw [← pow_mul]
  have h2 : ((Nat.clog 2 (n₀ + 2) : ℝ) + 2) ^ 2 ≤ assemblyBase s n₀ ^ 2 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (Nat.clog 2 (n₀ + 2) : ℝ) + 2) hL 2
    simpa using hpow
  have hmul : ((N : ℝ) + 1) ^ 4 * ((Nat.clog 2 (n₀ + 2) : ℝ) + 2) ^ 2
      ≤ assemblyBase s n₀ ^ 10 := by
    have := mul_le_assemblyBase_pow hs h1 h2 (by positivity)
    simpa using this
  have hone : (1 : ℝ) ≤ assemblyBase s n₀ ^ 10 := one_le_assemblyBase_pow hs 10
  have hx : ((N : ℝ) + 1) ^ 4 * ((Nat.clog 2 (n₀ + 2) : ℝ) + 2) ^ 2 * (0 + 1)
      ≤ assemblyBase s n₀ ^ 10 := by
    rw [zero_add, mul_one]
    exact hmul
  exact add_le_assemblyBase_pow hs hx hone

/-- The peel's coefficient, linearized: `apexStep n₀ M' D ≤ B^85 · D`. -/
lemma apexStep_le_pow (hs : 1 ≤ s) (M' : Type) [Fintype M']
    (hM : Fintype.card M' ≤ s) {D : ℝ} (hD : 1 ≤ D) :
    ApexAdapter.apexStep n₀ M' D ≤ assemblyBase s n₀ ^ 85 * D := by
  have hstep : axisStep n₀ M' ≤ assemblyBase s n₀ ^ 80 := by
    have := axisStep_le_pow (n₀ := n₀) hs M' hM (j := 0) (by omega)
    simpa using this
  have hX0 : 0 ≤ axisStep n₀ M' := axisStep_nonneg _ _
  have hP80 : (1 : ℝ) ≤ assemblyBase s n₀ ^ 80 := one_le_assemblyBase_pow hs 80
  rw [ApexAdapter.apexStep]
  have h1 : 10 * D + 4 + 4 * D * axisStep n₀ M'
      ≤ 18 * D * assemblyBase s n₀ ^ 80 := by
    have h4D : 4 * D * axisStep n₀ M' ≤ 4 * D * assemblyBase s n₀ ^ 80 :=
      mul_le_mul_of_nonneg_left hstep (by linarith)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 14 * D)
      (by linarith : (0 : ℝ) ≤ assemblyBase s n₀ ^ 80 - 1)]
  have h18 : (18 : ℝ) * assemblyBase s n₀ ^ 80 ≤ assemblyBase s n₀ ^ 85 := by
    have h18' : (18 : ℝ) ≤ assemblyBase s n₀ ^ 5 :=
      numeral_le_assemblyBase_pow hs (by norm_num)
    have := mul_le_assemblyBase_pow hs h18' (le_refl (assemblyBase s n₀ ^ 80))
      (by positivity)
    simpa using this
  calc 10 * D + 4 + 4 * D * axisStep n₀ M'
      ≤ 18 * D * assemblyBase s n₀ ^ 80 := h1
    _ = D * (18 * assemblyBase s n₀ ^ 80) := by ring
    _ ≤ D * assemblyBase s n₀ ^ 85 := by
        exact mul_le_mul_of_nonneg_left h18 (by linarith)
    _ = assemblyBase s n₀ ^ 85 * D := mul_comm _ _

end Majorants

/-! ## Carrier bounds for the package data -/

section Cards

/-- The image of a finite monoid is no larger. -/
lemma card_mrange_le {M N : Type} [Monoid M] [Fintype M] [Monoid N] (f : M →* N)
    [Fintype ↥(MonoidHom.mrange f)] :
    Fintype.card ↥(MonoidHom.mrange f) ≤ Fintype.card M :=
  Fintype.card_le_of_surjective (MonoidHom.mrangeRestrict f)
    (MonoidHom.mrangeRestrict_surjective f)

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- A coordinate's degree is at most the carrier. -/
lemma ApexCoordinate.degree_le_card (c : ApexCoordinate M) :
    c.degree ≤ Fintype.card M := by
  have h := c.degree_sq_le
  have h2 : (jClass M c.apex).card ≤ Fintype.card M := by
    calc (jClass M c.apex).card ≤ Finset.univ.card := Finset.card_le_univ _
      _ = Fintype.card M := Finset.card_univ
  exact le_trans (Nat.le_self_pow (by norm_num) _) (le_trans h h2)

/-- The Munn package lists at most one coordinate per idempotent. -/
lemma count_munnPackage_le [IsAperiodicMonoid M] :
    (PrincipalFactor.munnPackage M).count ≤ Fintype.card M := by
  calc (PrincipalFactor.idemIdeals M).card
      ≤ (Finset.univ.filter fun e : M => e * e = e).card := Finset.card_image_le
    _ ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = Fintype.card M := Finset.card_univ

end Cards

/-! ## The assembled step bound -/

section StepBound

variable {s n₀ : ℕ}
variable {M' : Type} [Monoid M'] [Fintype M'] [DecidableEq M'] [IsAperiodicMonoid M']

open LocallyThin

/-- The dichotomy's cost is nonnegative. -/
lemma coordCost_nonneg (Pk : ApexPackage M') (n₀ t : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (k : Fin Pk.count) : 0 ≤ Pk.coordCost n₀ t D k := by
  rw [ApexPackage.coordCost]
  split_ifs
  · have : Nonempty M' := ⟨1⟩
    exact ApexAdapter.apexStep_nonneg n₀ M' hD
  · have h1 : (0 : ℝ) ≤ axisConst (n₀ + (Pk.coord k).degree)
        ↥(repImage (Pk.coord k).rep) :=
      le_trans zero_le_one (one_le_axisConst _ _)
    have h2 : (0 : ℝ) ≤ (Fintype.card ↥(repImage (Pk.coord k).rep) : ℝ) :=
      Nat.cast_nonneg _
    positivity

/-- **The dichotomy, bounded uniformly**: with the incoming certificate at
least `B^(130·t)`, both branches sit under `B^85 · D`. -/
lemma coordCost_le_pow (hs : 1 ≤ s) (Pk : ApexPackage M')
    (hcard : Fintype.card M' ≤ s) {t : ℕ} (ht : 2 ≤ t) {D : ℝ} (hD : 1 ≤ D)
    (hDt : assemblyBase s n₀ ^ (130 * t) ≤ D) (k : Fin Pk.count) :
    Pk.coordCost n₀ t D k ≤ assemblyBase s n₀ ^ 85 * D := by
  rw [ApexPackage.coordCost]
  split_ifs with hdeg
  · exact apexStep_le_pow hs M' hcard hD
  · rw [not_lt] at hdeg
    have hcardT : Fintype.card ↥(repImage (Pk.coord k).rep) ≤ s :=
      le_trans (card_mrange_le _) hcard
    have hdegs : (Pk.coord k).degree ≤ s :=
      le_trans (Pk.coord k).degree_le_card hcard
    have hconst : axisConst (n₀ + (Pk.coord k).degree) ↥(repImage (Pk.coord k).rep)
        ≤ assemblyBase s n₀ ^ 85 :=
      axisConst_le_pow hs _ hcardT (by omega)
    have hpow : axisConst (n₀ + (Pk.coord k).degree) ↥(repImage (Pk.coord k).rep)
          ^ ((Pk.coord k).degree + 1)
        ≤ assemblyBase s n₀ ^ (85 * (t + 1)) := by
      calc axisConst (n₀ + (Pk.coord k).degree) ↥(repImage (Pk.coord k).rep)
            ^ ((Pk.coord k).degree + 1)
          ≤ (assemblyBase s n₀ ^ 85) ^ ((Pk.coord k).degree + 1) :=
            pow_le_pow_left₀ (le_trans zero_le_one (one_le_axisConst _ _)) hconst _
        _ = assemblyBase s n₀ ^ (85 * ((Pk.coord k).degree + 1)) := by
            rw [← pow_mul]
        _ ≤ assemblyBase s n₀ ^ (85 * (t + 1)) :=
            assemblyBase_pow_le_pow hs (Nat.mul_le_mul_left _ (by omega))
    have h2small : (2 : ℝ) ≤ assemblyBase s n₀ ^ (85 * (t + 1)) := by
      refine le_trans (two_le_assemblyBase (n₀ := n₀) hs) ?_
      calc assemblyBase s n₀ = assemblyBase s n₀ ^ 1 := (pow_one _).symm
        _ ≤ assemblyBase s n₀ ^ (85 * (t + 1)) :=
            assemblyBase_pow_le_pow hs (by omega)
    have hplus : axisConst (n₀ + (Pk.coord k).degree) ↥(repImage (Pk.coord k).rep)
          ^ ((Pk.coord k).degree + 1) + 2
        ≤ assemblyBase s n₀ ^ (85 * (t + 1) + 1) :=
      add_le_assemblyBase_pow hs hpow h2small
    have h2card : (2 : ℝ) * (Fintype.card ↥(repImage (Pk.coord k).rep) : ℝ)
        ≤ assemblyBase s n₀ ^ 2 := by
      have h2B : (2 : ℝ) ≤ assemblyBase s n₀ ^ 1 := by
        rw [pow_one]; exact two_le_assemblyBase hs
      have hcB : (Fintype.card ↥(repImage (Pk.coord k).rep) : ℝ)
          ≤ assemblyBase s n₀ ^ 1 := by
        rw [pow_one]
        exact le_trans ((Nat.cast_le (α := ℝ)).2 hcardT) (cast_le_assemblyBase hs)
      have := mul_le_assemblyBase_pow hs h2B hcB (Nat.cast_nonneg _)
      simpa using this
    have htotal : 2 * (Fintype.card ↥(repImage (Pk.coord k).rep) : ℝ)
          * (axisConst (n₀ + (Pk.coord k).degree) ↥(repImage (Pk.coord k).rep)
              ^ ((Pk.coord k).degree + 1) + 2)
        ≤ assemblyBase s n₀ ^ (2 + (85 * (t + 1) + 1)) := by
      refine mul_le_assemblyBase_pow hs h2card hplus ?_
      have h1 : (0 : ℝ) ≤ axisConst (n₀ + (Pk.coord k).degree)
          ↥(repImage (Pk.coord k).rep) ^ ((Pk.coord k).degree + 1) := by
        have := one_le_axisConst (n₀ + (Pk.coord k).degree)
          ↥(repImage (Pk.coord k).rep)
        positivity
      linarith
    have hsmallD : assemblyBase s n₀ ^ (2 + (85 * (t + 1) + 1)) ≤ D :=
      le_trans (assemblyBase_pow_le_pow hs (by omega)) hDt
    have hfinal : 2 * (Fintype.card ↥(repImage (Pk.coord k).rep) : ℝ)
          * (axisConst (n₀ + (Pk.coord k).degree) ↥(repImage (Pk.coord k).rep)
              ^ ((Pk.coord k).degree + 1) + 2) ≤ D :=
      le_trans htotal hsmallD
    refine le_trans hfinal ?_
    exact le_mul_of_one_le_left (by linarith) (one_le_assemblyBase_pow hs 85)

/-- The combined coordinate cost of the Munn package. -/
lemma two_sum_coordCost_le (hs : 1 ≤ s) (hcard : Fintype.card M' ≤ s) {t : ℕ}
    (ht : 2 ≤ t) {D : ℝ} (hD : 1 ≤ D)
    (hDt : assemblyBase s n₀ ^ (130 * t) ≤ D) :
    2 * ∑ k, (PrincipalFactor.munnPackage M').coordCost n₀ t D k
      ≤ assemblyBase s n₀ ^ 88 * D := by
  have hB85D : (0 : ℝ) ≤ assemblyBase s n₀ ^ 85 * D :=
    mul_nonneg (le_trans zero_le_one (one_le_assemblyBase_pow hs 85)) (by linarith)
  have hsum : ∑ k, (PrincipalFactor.munnPackage M').coordCost n₀ t D k
      ≤ (Fintype.card M' : ℝ) * (assemblyBase s n₀ ^ 85 * D) := by
    have hb := Finset.sum_le_card_nsmul Finset.univ
      (fun k => (PrincipalFactor.munnPackage M').coordCost n₀ t D k)
      (assemblyBase s n₀ ^ 85 * D)
      (fun k _ => coordCost_le_pow hs _ hcard ht hD hDt k)
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
    refine le_trans hb ?_
    have hcount : ((PrincipalFactor.munnPackage M').count : ℝ)
        ≤ (Fintype.card M' : ℝ) := by
      exact_mod_cast count_munnPackage_le
    exact mul_le_mul_of_nonneg_right hcount hB85D
  have h2c : (2 : ℝ) * (Fintype.card M' : ℝ) ≤ assemblyBase s n₀ ^ 2 := by
    have h2B : (2 : ℝ) ≤ assemblyBase s n₀ ^ 1 := by
      rw [pow_one]; exact two_le_assemblyBase hs
    have hcB : (Fintype.card M' : ℝ) ≤ assemblyBase s n₀ ^ 1 := by
      rw [pow_one]
      exact le_trans ((Nat.cast_le (α := ℝ)).2 hcard) (cast_le_assemblyBase hs)
    have := mul_le_assemblyBase_pow hs h2B hcB (Nat.cast_nonneg _)
    simpa using this
  calc 2 * ∑ k, (PrincipalFactor.munnPackage M').coordCost n₀ t D k
      ≤ 2 * ((Fintype.card M' : ℝ) * (assemblyBase s n₀ ^ 85 * D)) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (2 * (Fintype.card M' : ℝ)) * (assemblyBase s n₀ ^ 85 * D) := by ring
    _ ≤ assemblyBase s n₀ ^ 2 * (assemblyBase s n₀ ^ 85 * D) :=
        mul_le_mul_of_nonneg_right h2c hB85D
    _ = assemblyBase s n₀ ^ 87 * D := by ring
    _ ≤ assemblyBase s n₀ ^ 88 * D := by
        refine mul_le_mul_of_nonneg_right
          (assemblyBase_pow_le_pow hs (by norm_num)) (by linarith)

/-- **The whole per-monoid step, bounded**: tower and combination together sit
under `B^(100·Λ) · D`. -/
lemma step_cost_le_pow (hs : 1 ≤ s) (hcard : Fintype.card M' ≤ s) {t : ℕ}
    (ht : 2 ≤ t) {D : ℝ} (hD : 1 ≤ D)
    (hDt : assemblyBase s n₀ ^ (130 * t) ≤ D) :
    (thinStep n₀ (Fintype.card M'))^[Nat.clog 2 (Fintype.card M')]
        (2 * ∑ k, (PrincipalFactor.munnPackage M').coordCost n₀ t D k)
      ≤ assemblyBase s n₀ ^ (100 * Nat.clog 2 (s + 2)) * D := by
  have hΛ1 : 1 ≤ Nat.clog 2 (s + 2) := Nat.clog_pos (by norm_num) (by omega)
  have hx0 : 0 ≤ 2 * ∑ k, (PrincipalFactor.munnPackage M').coordCost n₀ t D k := by
    have := Finset.sum_nonneg
      (fun k (_ : k ∈ Finset.univ) =>
        coordCost_nonneg (PrincipalFactor.munnPackage M') n₀ t (D := D) (by linarith) k)
    linarith
  have hiter := iterate_thinStep_add_one_le n₀ (Fintype.card M') hx0
    (Nat.clog 2 (Fintype.card M'))
  have hts := thinStep_zero_add_one_le (n₀ := n₀) hs hcard
  have hk : Nat.clog 2 (Fintype.card M') ≤ Nat.clog 2 (s + 2) :=
    Nat.clog_mono_right _ (by omega)
  have hts0 : (0 : ℝ) ≤ thinStep n₀ (Fintype.card M') 0 + 1 := by
    have := thinStep_nonneg n₀ (Fintype.card M') (le_refl (0 : ℝ))
    linarith
  have hpow1 : (thinStep n₀ (Fintype.card M') 0 + 1)
        ^ Nat.clog 2 (Fintype.card M')
      ≤ (assemblyBase s n₀ ^ 11) ^ Nat.clog 2 (s + 2) := by
    calc (thinStep n₀ (Fintype.card M') 0 + 1) ^ Nat.clog 2 (Fintype.card M')
        ≤ (assemblyBase s n₀ ^ 11) ^ Nat.clog 2 (Fintype.card M') :=
          pow_le_pow_left₀ hts0 hts _
      _ ≤ (assemblyBase s n₀ ^ 11) ^ Nat.clog 2 (s + 2) :=
          pow_le_pow_right₀ (one_le_assemblyBase_pow hs 11) hk
  have hxb := two_sum_coordCost_le (n₀ := n₀) hs hcard ht hD hDt
  have hx1 : 2 * ∑ k, (PrincipalFactor.munnPackage M').coordCost n₀ t D k + 1
      ≤ assemblyBase s n₀ ^ 89 * D := by
    have h88 : (1 : ℝ) ≤ assemblyBase s n₀ ^ 88 * D := by
      have ha := one_le_assemblyBase_pow (n₀ := n₀) hs 88
      nlinarith
    have hdbl : assemblyBase s n₀ ^ 88 * D + assemblyBase s n₀ ^ 88 * D
        ≤ assemblyBase s n₀ ^ 89 * D := by
      have hB2 := two_le_assemblyBase (n₀ := n₀) hs
      have hnn : (0 : ℝ) ≤ assemblyBase s n₀ ^ 88 * D :=
        mul_nonneg (le_trans zero_le_one (one_le_assemblyBase_pow hs 88))
          (by linarith)
      have h89 : assemblyBase s n₀ ^ 89 * D
          = assemblyBase s n₀ * (assemblyBase s n₀ ^ 88 * D) := by ring
      rw [h89]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ assemblyBase s n₀ - 2) hnn]
    linarith
  have hchain : (thinStep n₀ (Fintype.card M'))^[Nat.clog 2 (Fintype.card M')]
        (2 * ∑ k, (PrincipalFactor.munnPackage M').coordCost n₀ t D k)
      ≤ (assemblyBase s n₀ ^ 11) ^ Nat.clog 2 (s + 2)
          * (assemblyBase s n₀ ^ 89 * D) := by
    have hstep1 : (thinStep n₀ (Fintype.card M'))^[Nat.clog 2 (Fintype.card M')]
          (2 * ∑ k, (PrincipalFactor.munnPackage M').coordCost n₀ t D k)
        ≤ (thinStep n₀ (Fintype.card M') 0 + 1) ^ Nat.clog 2 (Fintype.card M')
            * (2 * ∑ k, (PrincipalFactor.munnPackage M').coordCost n₀ t D k + 1) := by
      linarith
    refine le_trans hstep1 ?_
    refine mul_le_mul hpow1 hx1 (by linarith)
      (pow_nonneg (le_trans zero_le_one (one_le_assemblyBase_pow hs 11)) _)
  refine le_trans hchain ?_
  have hexp : (assemblyBase s n₀ ^ 11) ^ Nat.clog 2 (s + 2)
        * (assemblyBase s n₀ ^ 89 * D)
      = assemblyBase s n₀ ^ (11 * Nat.clog 2 (s + 2) + 89) * D := by
    rw [← pow_mul]
    ring
  rw [hexp]
  refine mul_le_mul_of_nonneg_right
    (assemblyBase_pow_le_pow hs (by omega)) (by linarith)

end StepBound

/-! ## The strong induction, and the endpoint -/

/-- **The carrier recurrence over monoid types.**  Every finite aperiodic
monoid of order at most `s` (and at most the induction measure `m`) satisfies
the alphabet-uniform contract at `(B^256)^(t + (m/t² + 1)·Λ)` — the
exponent of the paper's recurrence (`prop:ags-cuberoot-recurrence`), with
floor division.  The descent applies
the per-monoid step at the Munn package, pricing the above-threshold
coordinates by the induction hypothesis at the Rees quotients; the base case
has no above-threshold coordinate at all, since a degree above `t` would
charge more than `t² > m` elements. -/
theorem hasWordProdDualPoly_rec (s n₀ : ℕ) (hs : 1 ≤ s) (m : ℕ) :
    ∀ (M' : Type) [Monoid M'] [Fintype M'] [DecidableEq M'] [IsAperiodicMonoid M'],
      Fintype.card M' ≤ s → Fintype.card M' ≤ m →
      HasWordProdDualPoly M' n₀
        ((assemblyBase s n₀ ^ 256)
          ^ (cubeThreshold s
              + (m / cubeThreshold s ^ 2 + 1) * Nat.clog 2 (s + 2))) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro M' _ _ _ _ hcs hcm
    have ht2 : 2 ≤ cubeThreshold s := two_le_cubeThreshold s
    have htsq : 4 ≤ cubeThreshold s ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ cubeThreshold s ^ 2 := Nat.pow_le_pow_left ht2 2
    have hΛ1 : 0 < Nat.clog 2 (s + 2) := Nat.clog_pos (by norm_num) (by omega)
    by_cases hm : cubeThreshold s ^ 2 ≤ m
    · -- the descent
      have hD1 : (1 : ℝ) ≤ (assemblyBase s n₀ ^ 256)
          ^ (cubeThreshold s
              + ((m - cubeThreshold s ^ 2) / cubeThreshold s ^ 2 + 1)
                * Nat.clog 2 (s + 2)) :=
        one_le_pow₀ (one_le_assemblyBase_pow hs 256)
      have hDt : assemblyBase s n₀ ^ (130 * cubeThreshold s)
          ≤ (assemblyBase s n₀ ^ 256)
            ^ (cubeThreshold s
                + ((m - cubeThreshold s ^ 2) / cubeThreshold s ^ 2 + 1)
                  * Nat.clog 2 (s + 2)) := by
        rw [← pow_mul]
        refine assemblyBase_pow_le_pow hs ?_
        refine le_trans (Nat.mul_le_mul_right _ (by norm_num : 130 ≤ 256)) ?_
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      have hquot : ∀ (k : Fin (PrincipalFactor.munnPackage M').count)
          (hc : ((PrincipalFactor.munnPackage M').coord k).IsProper),
          cubeThreshold s < ((PrincipalFactor.munnPackage M').coord k).degree →
          HasWordProdDualPoly
            (ReesQuot (ReesQuot.apexIdeal
              ((PrincipalFactor.munnPackage M').coord k) hc)) n₀
            ((assemblyBase s n₀ ^ 256)
              ^ (cubeThreshold s
                  + ((m - cubeThreshold s ^ 2) / cubeThreshold s ^ 2 + 1)
                    * Nat.clog 2 (s + 2))) := by
        intro k hc hdeg
        have hdrop := ReesQuot.card_reesQuot_add_sq_le
          ((PrincipalFactor.munnPackage M').coord k) hc hdeg
        have hcard0 : Fintype.card (ReesQuot (ReesQuot.apexIdeal
              ((PrincipalFactor.munnPackage M').coord k) hc))
            ≤ Fintype.card M' :=
          le_trans (Nat.le_add_right _ _) hdrop
        have hlt : m - cubeThreshold s ^ 2 < m :=
          Nat.sub_lt (by omega) (by omega)
        refine ih (m - cubeThreshold s ^ 2) hlt _ (le_trans hcard0 hcs) ?_
        exact Nat.le_sub_of_add_le (le_trans hdrop hcm)
      have hstep := (PrincipalFactor.munnPackage M').hasWordProdDualPoly_step
        n₀ (cubeThreshold s) ht2 hD1 hquot
      refine hstep.mono_cost (le_trans (step_cost_le_pow hs hcs ht2 hD1 hDt) ?_)
      rw [← pow_mul, ← pow_add, ← pow_mul]
      refine assemblyBase_pow_le_pow hs ?_
      have hexp : Nat.clog 2 (s + 2)
            + (cubeThreshold s
                + ((m - cubeThreshold s ^ 2) / cubeThreshold s ^ 2 + 1)
                  * Nat.clog 2 (s + 2))
          ≤ cubeThreshold s
              + (m / cubeThreshold s ^ 2 + 1) * Nat.clog 2 (s + 2) :=
        exponent_step (by omega)
          (le_of_eq (Nat.sub_add_cancel hm))
      calc 100 * Nat.clog 2 (s + 2)
            + 256 * (cubeThreshold s
                + ((m - cubeThreshold s ^ 2) / cubeThreshold s ^ 2 + 1)
                  * Nat.clog 2 (s + 2))
          ≤ 256 * Nat.clog 2 (s + 2)
            + 256 * (cubeThreshold s
                + ((m - cubeThreshold s ^ 2) / cubeThreshold s ^ 2 + 1)
                  * Nat.clog 2 (s + 2)) :=
            Nat.add_le_add_right (Nat.mul_le_mul_right _ (by norm_num)) _
        _ = 256 * (Nat.clog 2 (s + 2)
              + (cubeThreshold s
                + ((m - cubeThreshold s ^ 2) / cubeThreshold s ^ 2 + 1)
                  * Nat.clog 2 (s + 2))) := by ring
        _ ≤ 256 * (cubeThreshold s
              + (m / cubeThreshold s ^ 2 + 1) * Nat.clog 2 (s + 2)) :=
            Nat.mul_le_mul_left _ hexp
    · -- the base: a degree above the threshold would charge more than `m`
      have hD1 : (1 : ℝ) ≤ assemblyBase s n₀ ^ (256 * cubeThreshold s) :=
        one_le_assemblyBase_pow hs _
      have hDt : assemblyBase s n₀ ^ (130 * cubeThreshold s)
          ≤ assemblyBase s n₀ ^ (256 * cubeThreshold s) :=
        assemblyBase_pow_le_pow hs (Nat.mul_le_mul_right _ (by norm_num))
      have hquot : ∀ (k : Fin (PrincipalFactor.munnPackage M').count)
          (hc : ((PrincipalFactor.munnPackage M').coord k).IsProper),
          cubeThreshold s < ((PrincipalFactor.munnPackage M').coord k).degree →
          HasWordProdDualPoly
            (ReesQuot (ReesQuot.apexIdeal
              ((PrincipalFactor.munnPackage M').coord k) hc)) n₀
            (assemblyBase s n₀ ^ (256 * cubeThreshold s)) := by
        intro k hc hdeg
        exfalso
        have hsq := ((PrincipalFactor.munnPackage M').coord k).degree_sq_le
        have hjc : (jClass M' ((PrincipalFactor.munnPackage M').coord k).apex).card
            ≤ Fintype.card M' := by
          calc (jClass M' ((PrincipalFactor.munnPackage M').coord k).apex).card
              ≤ Finset.univ.card := Finset.card_le_univ _
            _ = Fintype.card M' := Finset.card_univ
        have hlt : cubeThreshold s ^ 2
            < ((PrincipalFactor.munnPackage M').coord k).degree ^ 2 :=
          Nat.pow_lt_pow_left hdeg (by norm_num)
        exact hm (le_trans hlt.le (le_trans hsq (le_trans hjc hcm)))
      have hstep := (PrincipalFactor.munnPackage M').hasWordProdDualPoly_step
        n₀ (cubeThreshold s) ht2 hD1 hquot
      refine hstep.mono_cost (le_trans (step_cost_le_pow hs hcs ht2 hD1 hDt) ?_)
      rw [← pow_add, ← pow_mul]
      refine assemblyBase_pow_le_pow hs ?_
      have h1 : Nat.clog 2 (s + 2)
          ≤ (m / cubeThreshold s ^ 2 + 1) * Nat.clog 2 (s + 2) :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      calc 100 * Nat.clog 2 (s + 2) + 256 * cubeThreshold s
          ≤ 256 * ((m / cubeThreshold s ^ 2 + 1) * Nat.clog 2 (s + 2))
            + 256 * cubeThreshold s :=
            Nat.add_le_add_right
              (le_trans (Nat.mul_le_mul_right _ (by norm_num))
                (Nat.mul_le_mul_left _ h1)) _
        _ = 256 * (cubeThreshold s
              + (m / cubeThreshold s ^ 2 + 1) * Nat.clog 2 (s + 2)) := by ring

/-- **Headline: the cube-root factor is achieved.**  Every finite
aperiodic monoid satisfies the alphabet-uniform word-product contract at
`cubeRootFactor K |M| n₀`, with the universal exponent multiplier chosen:
`K = 256`. -/
theorem hasWordProdDualPoly_cubeRootFactor (M : Type) [Monoid M] [Fintype M]
    [DecidableEq M] [IsAperiodicMonoid M] (n₀ : ℕ) :
    HasWordProdDualPoly M n₀ (cubeRootFactor 256 (Fintype.card M) n₀) := by
  have hne : Nonempty M := ⟨1⟩
  have hs : 1 ≤ Fintype.card M := Fintype.card_pos
  have h := hasWordProdDualPoly_rec (Fintype.card M) n₀ hs (Fintype.card M)
    M le_rfl le_rfl
  refine h.mono_cost ?_
  rw [← pow_mul]
  exact pow_recurrenceExponent_le_cubeRootFactor hs

end MonoidProduct
