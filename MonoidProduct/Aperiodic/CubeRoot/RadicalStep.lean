import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The doubling transition of a nilpotent two-sided ideal

The radical tower (`RadicalTower.lean`) moves through the quotients

    A ⧸ K^(2r) → A ⧸ K^r,     r = 1, 2, 4, …

of a ring `A` by the powers of a two-sided nilpotent ideal `K`.  This file
fixes the API: Mathlib's `Ideal A` with the `Ideal.IsTwoSided` class
supplies the noncommutative quotient ring, the powers with their two-sided
instances, `Ideal.pow_le_pow_right`, and the factor map
`Ideal.Quotient.factor`.  Nothing from `TwoSidedIdeal` is needed.

Proved here:

* `doublingMap K r : A ⧸ K^(2r) →+* A ⧸ K^r`, the factor map;
* **its kernel is square-zero** (`doublingMap_ker_mul`): two elements of
  the kernel lift into `K^r`, and `K^r · K^r = K^(2r)`;
* the **layer count**: from a quantitative exponent `K^e = ⊥` the tower
  reaches `⊥` after `Nat.clog 2 e` doublings (`pow_two_pow_clog_eq_bot`);
* the **square-zero loop formula** that the local-thinness argument
  (`LocallyThin.lean`) rests on: if `(s − 1)² = 0` then `s^ℓ = 1 + ℓ·(s − 1)`, hence
  `x·s^ℓ·y − x·y = ℓ·(x·(s − 1)·y)`.
-/

namespace MonoidProduct

section Doubling

variable {A : Type} [Ring A] (K : Ideal A) [K.IsTwoSided]

/-- The doubling transition `A ⧸ K^(2r) → A ⧸ K^r`. -/
def doublingMap (r : ℕ) : A ⧸ K ^ (2 * r) →+* A ⧸ K ^ r :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : r ≤ 2 * r))

@[simp] lemma doublingMap_mk (r : ℕ) (x : A) :
    doublingMap K r (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x :=
  Ideal.Quotient.factor_mk _ x

lemma doublingMap_surjective (r : ℕ) : Function.Surjective (doublingMap K r) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ x, doublingMap_mk K r x⟩

/-- **The kernel of the doubling transition is square-zero.** -/
theorem doublingMap_ker_mul (r : ℕ) {x y : A ⧸ K ^ (2 * r)}
    (hx : x ∈ RingHom.ker (doublingMap K r)) (hy : y ∈ RingHom.ker (doublingMap K r)) :
    x * y = 0 := by
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, doublingMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, two_mul, Ideal.IsTwoSided.pow_add]
  exact Ideal.mul_mem_mul hx hy

/-- A power of a nilpotent ideal beyond its exponent is still `⊥`. -/
lemma pow_eq_bot_of_le {e f : ℕ} (he : K ^ e = ⊥) (hef : e ≤ f) : K ^ f = ⊥ :=
  le_bot_iff.mp (he ▸ Ideal.pow_le_pow_right hef)

/-- **The layer count**: from `K^e = ⊥`, the doubling tower `K, K², K⁴, …`
reaches `⊥` after `Nat.clog 2 e` doublings. -/
theorem pow_two_pow_clog_eq_bot {e : ℕ} (he : K ^ e = ⊥) :
    K ^ (2 ^ Nat.clog 2 e) = ⊥ :=
  pow_eq_bot_of_le K he (Nat.le_pow_clog (by norm_num) e)

end Doubling

/-! ## The square-zero loop formula -/

section SquareZero

variable {A : Type} [Ring A]

/-- If `(s − 1)² = 0` then `s^ℓ = 1 + ℓ·(s − 1)`. -/
theorem pow_eq_of_sq_sub_one_eq_zero {s : A} (hs : (s - 1) * (s - 1) = 0) (ℓ : ℕ) :
    s ^ ℓ = 1 + (ℓ : ℤ) • (s - 1) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      rw [pow_succ, ih]
      have h0 : (ℓ : ℤ) • (s - 1) * (s - 1) = 0 := by
        rw [smul_mul_assoc, hs, smul_zero]
      calc (1 + (ℓ : ℤ) • (s - 1)) * s
          = (1 + (ℓ : ℤ) • (s - 1)) * ((s - 1) + 1) := by rw [sub_add_cancel]
        _ = (s - 1) + 1 + ((ℓ : ℤ) • (s - 1) * (s - 1) + (ℓ : ℤ) • (s - 1)) := by
            rw [add_mul, one_mul, mul_add, mul_one]
        _ = 1 + ((ℓ + 1 : ℕ) : ℤ) • (s - 1) := by
            rw [h0, zero_add]
            push_cast
            rw [add_smul, one_smul]
            abel

/-- **The square-zero loop formula**: `x·s^ℓ·y − x·y = ℓ·(x·(s − 1)·y)`. -/
theorem mul_pow_mul_sub_eq {s : A} (hs : (s - 1) * (s - 1) = 0) (x y : A) (ℓ : ℕ) :
    x * s ^ ℓ * y - x * y = (ℓ : ℤ) • (x * (s - 1) * y) := by
  rw [pow_eq_of_sq_sub_one_eq_zero hs ℓ, mul_add, mul_one, add_mul, mul_smul_comm,
    smul_mul_assoc]
  abel

/-- **The contextual loop formula** (the form local thinness uses):
it suffices that the *left* difference `x·(s − 1)` and the *right*
difference `(s − 1)·y` lie in a square-zero two-sided ideal `J`; then
`x·s^ℓ·y − x·y = ℓ·(x·(s − 1)·y)`.  Each step `x·s^k·(s − 1)·y` equals
`x·(s − 1)·y` because their difference is
`(x·(s − 1))·(∑ sⁱ)·((s − 1)·y) ∈ J·J = 0`. -/
theorem mul_pow_mul_sub_eq_of_mem {J : Ideal A} [J.IsTwoSided]
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = 0) {x s y : A}
    (hx : x * (s - 1) ∈ J) (hy : (s - 1) * y ∈ J) (ℓ : ℕ) :
    x * s ^ ℓ * y - x * y = (ℓ : ℤ) • (x * (s - 1) * y) := by
  have hkey : ∀ k : ℕ, x * s ^ k * (s - 1) * y = x * (s - 1) * y := by
    intro k
    have hgeom : s ^ k - 1 = (s - 1) * ∑ i ∈ Finset.range k, s ^ i := (mul_geom_sum s k).symm
    have h0 : x * (s ^ k - 1) * (s - 1) * y = 0 := by
      rw [hgeom]
      have : x * ((s - 1) * ∑ i ∈ Finset.range k, s ^ i) * (s - 1) * y
          = (x * (s - 1)) * ((∑ i ∈ Finset.range k, s ^ i) * ((s - 1) * y)) := by
        simp only [mul_assoc]
      rw [this]
      exact hJ _ hx _ (J.mul_mem_left _ hy)
    have hsplit : x * s ^ k * (s - 1) * y
        = x * (s ^ k - 1) * (s - 1) * y + x * (s - 1) * y := by
      simp only [mul_sub, sub_mul, mul_one, mul_assoc]
      abel
    rw [hsplit, h0, zero_add]
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      have hstep : x * s ^ (ℓ + 1) * y - x * y
          = (x * s ^ ℓ * y - x * y) + x * s ^ ℓ * (s - 1) * y := by
        rw [pow_succ]
        simp only [mul_sub, sub_mul, mul_one, mul_assoc]
        abel
      rw [hstep, hkey, ih]
      push_cast
      rw [add_smul, one_smul]

end SquareZero

/-! ## Rational cancellation -/

section Rational

variable {A : Type} [Ring A] [Algebra ℚ A]

/-- In a rational algebra a nonzero integer cancels: `n • x = 0 → x = 0`.
This is the cancellation the local-thinness argument performs; the quotient layers of the radical
tower are rational algebras too (`Ideal.Quotient.algebra`). -/
theorem eq_zero_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {x : A} (h : n • x = 0) : x = 0 := by
  have hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  calc x = ((n : ℚ)⁻¹ * (n : ℚ)) • x := by rw [inv_mul_cancel₀ hq, one_smul]
    _ = (n : ℚ)⁻¹ • ((n : ℚ) • x) := by rw [mul_smul]
    _ = (n : ℚ)⁻¹ • (n • x) := by rw [Int.cast_smul_eq_zsmul]
    _ = 0 := by rw [h, smul_zero]

/-- The quotient layers of the tower are rational algebras. -/
example (K : Ideal A) [K.IsTwoSided] : Algebra ℚ (A ⧸ K) := inferInstance

end Rational

end MonoidProduct
