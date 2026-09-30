import MonoidProduct.Ordered.Correct

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The cost recurrence and the rank-`b` summary

With at most `R₀` merger rounds and at most `4·h·ℓ` proposals per draw at every node
count `h`, the cost recurrence `costA` solves to

  `costA b P r j ≤ 2 · (512 · b · R₀ · √ℓ · L)^r · √(2^j)`  for `j ≤ L`

(`costA_le`): at every depth the product `√(2^d)·√(2^(j−d)) = √(2^j)` is
depth-independent, so the sum over the `j+1 ≤ L` depths costs one factor `L`.
This is the cost recursion in the proof of the paper's `thm:ordered-beta-product`,
with the merger parameters left abstract.

A rank-`b` summary of an interval covering all positions has the product of the
whole word (`prod_eq_wordProd_of_isSummary`): it dominates a core of at most `b`
positions and is dominated by the word.
-/

namespace MonoidProduct

open Finset

section Cost

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) {N : ℕ}

/-- One depth term of the recurrence, bounded factor by factor. -/
lemma term_le {Rd k A R₀ Bk B b2 : ℝ} (hA0 : 0 ≤ A) (hAB : A ≤ B) (hRd : 0 ≤ Rd) (hRR : Rd ≤ R₀)
    (hkk : Real.sqrt k ≤ Bk) (hb2 : 0 ≤ b2) :
    2 * (Rd * (8 * (2 * (A + A)) * b2 * Real.sqrt k))
      ≤ 2 * (R₀ * (8 * (2 * (B + B)) * b2 * Bk)) := by
  have hB0 : 0 ≤ B := hA0.trans hAB
  have hk0 := Real.sqrt_nonneg k
  have h1 : 8 * (2 * (A + A)) * b2 ≤ 8 * (2 * (B + B)) * b2 :=
    mul_le_mul_of_nonneg_right (by linarith) hb2
  have h2 : 8 * (2 * (A + A)) * b2 * Real.sqrt k ≤ 8 * (2 * (B + B)) * b2 * Bk :=
    mul_le_mul h1 hkk hk0 (by positivity)
  have h3 : Rd * (8 * (2 * (A + A)) * b2 * Real.sqrt k) ≤ R₀ * (8 * (2 * (B + B)) * b2 * Bk) :=
    mul_le_mul hRR h2 (by positivity) (hRd.trans hRR)
  linarith

/-- **The solved recurrence `(B)`.** -/
theorem costA_le {b : ℕ} (hb1 : 1 ≤ b) (P : MParams) {R₀ ℓ : ℝ} (hR₀ : 1 ≤ R₀) (hℓ : 1 ≤ ℓ)
    {L : ℕ} (hL : 1 ≤ L) (hR : ∀ h : ℕ, 1 ≤ h → h ≤ 2 ^ L → ((P h).1 : ℝ) ≤ R₀)
    (hk : ∀ h : ℕ, 1 ≤ h → h ≤ 2 ^ L → ((P h).2 : ℝ) ≤ 4 * (h : ℝ) * ℓ) :
    ∀ r j, j ≤ L →
      costA b P r j ≤ 2 * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ r * Real.sqrt ((2 : ℝ) ^ j)
  | 0, j, _ => by
    have h1 : (1 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ j) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num))
    cases j with
    | zero => unfold costA; linarith
    | succ j => unfold costA; positivity
  | r + 1, 0, _ => by
    unfold costA
    have hK : (1 : ℝ) ≤ 512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L := by
      have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
      have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hs : (1 : ℝ) ≤ Real.sqrt ℓ := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hℓ
      have h1 : (1 : ℝ) ≤ 512 * (b : ℝ) := by linarith
      have h2 : (1 : ℝ) ≤ 512 * (b : ℝ) * R₀ := by nlinarith
      have h3 : (1 : ℝ) ≤ 512 * (b : ℝ) * R₀ * Real.sqrt ℓ := by nlinarith
      nlinarith
    rw [pow_zero, Real.sqrt_one, mul_one]
    have := one_le_pow₀ (n := r + 1) hK
    linarith
  | r + 1, j + 1, hj => by
    have hK0 : (0 : ℝ) ≤ 512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L := by positivity
    have hterm : ∀ d : Fin (j + 1),
        2 * (((P (2 ^ (d : ℕ))).1 : ℝ) * (8 * (2 * (costA b P r (j - d) + costA b P r (j - d)))
          * ((2 * b : ℕ) : ℝ) * Real.sqrt ((P (2 ^ (d : ℕ))).2)))
        ≤ 512 * (b : ℝ) * R₀ * Real.sqrt ℓ * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ r
            * Real.sqrt ((2 : ℝ) ^ j) := by
      intro d
      have hA := costA_le hb1 P hR₀ hℓ hL hR hk r (j - d) (by omega)
      have hdL : 2 ^ (d : ℕ) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hRd := hR (2 ^ (d : ℕ)) Nat.one_le_two_pow hdL
      have hkd : Real.sqrt (((P (2 ^ (d : ℕ))).2 : ℕ) : ℝ)
          ≤ 2 * Real.sqrt ((2 : ℝ) ^ (d : ℕ)) * Real.sqrt ℓ := by
        calc Real.sqrt (((P (2 ^ (d : ℕ))).2 : ℕ) : ℝ)
            ≤ Real.sqrt (4 * ((2 ^ (d : ℕ) : ℕ) : ℝ) * ℓ) :=
              Real.sqrt_le_sqrt (hk (2 ^ (d : ℕ)) Nat.one_le_two_pow hdL)
          _ = 2 * Real.sqrt ((2 : ℝ) ^ (d : ℕ)) * Real.sqrt ℓ := by
              push_cast
              rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
                show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      calc 2 * (((P (2 ^ (d : ℕ))).1 : ℝ) * (8 * (2 * (costA b P r (j - d) + costA b P r (j - d)))
            * ((2 * b : ℕ) : ℝ) * Real.sqrt ((P (2 ^ (d : ℕ))).2)))
          ≤ 2 * (R₀ * (8 * (2 * (2 * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ r
                * Real.sqrt ((2 : ℝ) ^ (j - d))
              + 2 * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ r * Real.sqrt ((2 : ℝ) ^ (j - d))))
            * ((2 * b : ℕ) : ℝ) * (2 * Real.sqrt ((2 : ℝ) ^ (d : ℕ)) * Real.sqrt ℓ))) :=
            term_le (costA_nonneg b P r (j - d)) hA (by positivity) hRd hkd (by positivity)
        _ = 512 * (b : ℝ) * R₀ * Real.sqrt ℓ * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ r
              * (Real.sqrt ((2 : ℝ) ^ (j - d)) * Real.sqrt ((2 : ℝ) ^ (d : ℕ))) := by
            push_cast; ring
        _ = 512 * (b : ℝ) * R₀ * Real.sqrt ℓ * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ r
              * Real.sqrt ((2 : ℝ) ^ j) := by
            rw [← Real.sqrt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.1 d.2)]
    have hsq : Real.sqrt ((2 : ℝ) ^ j) ≤ Real.sqrt ((2 : ℝ) ^ (j + 1)) :=
      Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) (Nat.le_succ j))
    have hjL : ((j : ℝ) + 1) ≤ L := by exact_mod_cast hj
    calc costA b P (r + 1) (j + 1)
        = 2 * ∑ d : Fin (j + 1),
            2 * (((P (2 ^ (d : ℕ))).1 : ℝ) * (8 * (2 * (costA b P r (j - d) + costA b P r (j - d)))
              * ((2 * b : ℕ) : ℝ) * Real.sqrt ((P (2 ^ (d : ℕ))).2))) := rfl
      _ ≤ 2 * ∑ _d : Fin (j + 1), 512 * (b : ℝ) * R₀ * Real.sqrt ℓ
            * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ r * Real.sqrt ((2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun d _ => hterm d) (by norm_num)
      _ = 2 * ((j : ℝ) + 1) * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ
            * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ r * Real.sqrt ((2 : ℝ) ^ j)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 2 * (L : ℝ) * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ
            * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ r * Real.sqrt ((2 : ℝ) ^ (j + 1))) := by
          gcongr
      _ = 2 * (512 * (b : ℝ) * R₀ * Real.sqrt ℓ * L) ^ (r + 1) * Real.sqrt ((2 : ℝ) ^ (j + 1)) := by
          rw [pow_succ]; ring

/-- **A rank-`b` summary of the whole word has the word's product.** -/
theorem prod_eq_wordProd_of_isSummary (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    {x : Fin N → σ} {j q : ℕ} {K : Record N σ} (hK : IsSummary letter x b b j q K)
    (hall : ∀ i, i ∈ ivl (N := N) j q) : K.prod letter = wordProd letter x := by
  obtain ⟨D, hD, hcore⟩ := hb N x
  apply le_antisymm
  · rw [Record.prod_of_truthful letter hK.truthful]
    exact hst.subwordProd_le_wordProd letter x _
  · rw [← hcore]
    exact hK.dom D (fun i _ => hall i) hD

end Cost

end MonoidProduct
