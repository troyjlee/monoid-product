import MonoidProduct.Dyck.AndStar
import MonoidProduct.Dyck.Blocks
import QuantumQueryComplexity.Promise.Compose
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The promised-AND √r amplification

Compose the promised-AND star (outer, `Fin r`) with the depth-`ℓ` iterated
exact-count promise (inner) and encode the result as `r` hard blocks in a row,
padded to any larger even length with copies of `ud`:

  `ampWord = B₁ B₂ ⋯ B_r (ud)^p`.

On the outer promise either every block is balanced — so the word is Dyck — or
exactly one block has total balance `2`, so the total is `2` and the word is not
Dyck.  The exceptional block raises the running baseline by at most `2`, so the
depth grows by exactly `2`:

```lean
theorem sqrt_mul_pow_le_advPM_dyck (hm : 0 < m) (hr : 0 < r)
    (hlen : r * blockWidth m ℓ ≤ n) (heven : Even n)
    (hk : blockHeight m ℓ + 2 ≤ k) :
    Real.sqrt r * (m : ℝ) ^ ℓ ≤ advPM (dyck k n)
```

The depth cap is any `k ≥ blockHeight m ℓ + 2`: the encoded words never exceed
that depth and rejection is on total balance alone, so raising the cap changes
no output (`dyck_ampRead`).  The final Dyck lower bound needs this slack to
round the requested depth down to the reduction's own depth.

## Padding needs only parity

`blockWidth m ℓ` is even (`even_blockWidth`), so `n - r * blockWidth m ℓ` is even
as soon as `n` is, and the padding length `p = (n - r·w)/2` exists with no
divisibility hypothesis.  The padding is a
concatenation of `ud`s, hence query-free, and contributes nothing to the balance
except a transient `+1`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

/-! ## Padding -/

lemma prefixBalance_ud_bounds (t : ℕ) :
    0 ≤ prefixBalance ud t ∧ prefixBalance ud t ≤ 1 := by
  match t with
  | 0 => simp
  | 1 => rw [prefixBalance_ud_one]; exact ⟨by norm_num, le_refl 1⟩
  | (t + 2) =>
      rw [prefixBalance_of_ge _ (by omega), totalBalance_ud]
      exact ⟨le_refl 0, by norm_num⟩

/-- `p` copies of `ud`. -/
def padWord (p : ℕ) : Fin (p * 2) → Bool := concatW 2 p fun _ => ud

@[simp] lemma totalBalance_padWord (p : ℕ) : totalBalance (padWord p) = 0 := by
  rw [padWord, totalBalance_concatW]
  simp

lemma prefixBalance_padWord_bounds (p t : ℕ) :
    0 ≤ prefixBalance (padWord p) t ∧ prefixBalance (padWord p) t ≤ 1 := by
  have h := prefixBalance_concatW_bounds 2 (h := 1) (by norm_num) p
    (fun _ => ud) (fun _ t => (prefixBalance_ud_bounds t).1)
    (fun _ t => (prefixBalance_ud_bounds t).2) t
  simpa [padWord] using h

lemma even_blockWidth (m ℓ : ℕ) : Even (blockWidth m ℓ) := by
  cases ℓ with
  | zero => exact ⟨1, rfl⟩
  | succ ℓ => exact ⟨m * (blockWidth m ℓ + 1), by rw [blockWidth_succ]; ring⟩

/-! ## Counting `false` answers -/

lemma sum_ite_eq_two_mul_falseCount {n : ℕ} (v : Fin n → Bool) :
    (∑ i, (if v i then (0 : ℤ) else 2)) = 2 * (falseCount v : ℤ) := by
  classical
  have hstep : ∀ i, (if v i then (0 : ℤ) else 2)
      = if v i = false then (2 : ℤ) else 0 := by
    intro i
    cases h : v i <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.sum_filter,
    show (Finset.univ.filter fun i => v i = false) = zeroSet v from rfl,
    Finset.sum_const, falseCount, nsmul_eq_mul]
  ring

/-! ## The amplified word -/

/-- The outer promise: `r` blocks, at most one of them unbalanced. -/
abbrev AmpDom (m ℓ r : ℕ) : Type :=
  ComposeDom (andStarRead (r := r)) (iterOut m ℓ)

/-- `r` blocks in a row, then `p` copies of `ud`. -/
def ampWord (m ℓ r p : ℕ) (ys : Fin r → IterDom m ℓ) :
    Fin (r * blockWidth m ℓ + p * 2) → Bool :=
  wordAppend
    (concatW (blockWidth m ℓ) r fun i => encodeWord m ℓ (ys i).1)
    (padWord p)

/-- The number of `false` block answers. -/
noncomputable def ampFalse (m ℓ r : ℕ) (ys : AmpDom m ℓ r) : ℕ :=
  falseCount fun i => iterOut m ℓ (ys.1 i)

lemma ampFalse_le_one (m ℓ r : ℕ) (ys : AmpDom m ℓ r) :
    ampFalse m ℓ r ys = 0 ∨ ampFalse m ℓ r ys = 1 := by
  obtain ⟨x, hx⟩ := ys.2
  have : x.1 = fun i => iterOut m ℓ (ys.1 i) := hx
  rw [ampFalse, ← this]
  exact x.2

lemma ampOut_eq (m ℓ r : ℕ) (ys : AmpDom m ℓ r) :
    composeOutOn (andStarRead (r := r)) (iterOut m ℓ) (andStarOut r) ys
      = decide (ampFalse m ℓ r ys = 0) := by
  obtain ⟨x, hx⟩ := ys.2
  rw [composeOutOn_eq andStarRead_injective (andStarOut r) ys hx, andStarOut,
    show x.1 = fun i => iterOut m ℓ (ys.1 i) from hx]
  rfl

lemma sum_totalBalance_blocks (m ℓ r : ℕ) (ys : AmpDom m ℓ r) :
    (∑ i, totalBalance (encodeWord m ℓ (ys.1 i).1))
      = 2 * (ampFalse m ℓ r ys : ℤ) := by
  rw [Finset.sum_congr rfl fun i _ =>
    encodeWord_total m ℓ (ys.1 i).1 (ys.1 i).2]
  exact sum_ite_eq_two_mul_falseCount _

/-! ## The block invariant for the amplified word -/

theorem ampWord_invariant (m ℓ r p : ℕ) (ys : AmpDom m ℓ r) :
    (∀ t, 0 ≤ prefixBalance (ampWord m ℓ r p ys.1) t) ∧
      (∀ t, prefixBalance (ampWord m ℓ r p ys.1) t
        ≤ ((blockHeight m ℓ + 2 : ℕ) : ℤ)) ∧
      totalBalance (ampWord m ℓ r p ys.1) = 2 * (ampFalse m ℓ r ys : ℤ) := by
  have hh0 : (0 : ℤ) ≤ ((blockHeight m ℓ : ℕ) : ℤ) := Int.natCast_nonneg _
  have hbh : (2 : ℤ) ≤ ((blockHeight m ℓ : ℕ) : ℤ) := by
    have h2 : 2 ≤ blockHeight m ℓ := by
      rw [blockHeight_eq]
      exact Nat.le_add_right 2 _
    exact_mod_cast h2
  have hnn : ∀ i t, 0 ≤ prefixBalance (encodeWord m ℓ (ys.1 i).1) t :=
    fun i => encodeWord_nonneg m ℓ (ys.1 i).1 (ys.1 i).2
  have hle : ∀ i t, prefixBalance (encodeWord m ℓ (ys.1 i).1) t
      ≤ ((blockHeight m ℓ : ℕ) : ℤ) :=
    fun i => encodeWord_le m ℓ (ys.1 i).1 (ys.1 i).2
  have hsum := sum_totalBalance_blocks m ℓ r ys
  have hcat := prefixBalance_concatW_bounds (blockWidth m ℓ) hh0 r
    (fun i => encodeWord m ℓ (ys.1 i).1) hnn hle
  have htot : totalBalance
      (concatW (blockWidth m ℓ) r fun i => encodeWord m ℓ (ys.1 i).1)
      = 2 * (ampFalse m ℓ r ys : ℤ) := by
    rw [totalBalance_concatW, hsum]
  have hfc : (0 : ℤ) ≤ (ampFalse m ℓ r ys : ℤ)
      ∧ (ampFalse m ℓ r ys : ℤ) ≤ 1 := by
    rcases ampFalse_le_one m ℓ r ys with hc | hc <;> rw [hc] <;>
      constructor <;> norm_num
  refine ⟨fun t => ?_, fun t => ?_, ?_⟩
  · rw [ampWord]
    rcases Nat.lt_or_ge t (r * blockWidth m ℓ) with ht | ht
    · rw [prefixBalance_wordAppend_left _ _ (le_of_lt ht)]
      exact (hcat t).1
    · obtain ⟨s, rfl⟩ : ∃ s, t = r * blockWidth m ℓ + s :=
        ⟨t - r * blockWidth m ℓ, by omega⟩
      rw [prefixBalance_wordAppend_right, htot]
      have := (prefixBalance_padWord_bounds p s).1
      linarith [hfc.1]
  · rw [ampWord]
    push_cast
    rcases Nat.lt_or_ge t (r * blockWidth m ℓ) with ht | ht
    · rw [prefixBalance_wordAppend_left _ _ (le_of_lt ht)]
      have h2 := (hcat t).2
      rw [hsum] at h2
      linarith [hfc.2]
    · obtain ⟨s, rfl⟩ : ∃ s, t = r * blockWidth m ℓ + s :=
        ⟨t - r * blockWidth m ℓ, by omega⟩
      rw [prefixBalance_wordAppend_right, htot]
      have := (prefixBalance_padWord_bounds p s).2
      linarith [hfc.2, hbh]
  · rw [ampWord, totalBalance_wordAppend, htot, totalBalance_padWord, add_zero]

/-! ## Language correctness -/

lemma isDyck_wcast {a b k : ℕ} (h : a = b) (x : Fin a → Bool) :
    IsDyck k (wcast h x) ↔ IsDyck k x := by
  subst h
  exact Iff.rfl

/-- The observation map: the amplified word at the requested length. -/
def ampRead (m ℓ r p n : ℕ) (hn : r * blockWidth m ℓ + p * 2 = n)
    (ys : AmpDom m ℓ r) : Fin n → Bool :=
  wcast hn (ampWord m ℓ r p ys.1)

/-- Language correctness of the amplified word, at every depth cap `k` from
`blockHeight m ℓ + 2` up: the words never exceed that depth, and a rejected
word is rejected on total balance alone, so raising the cap changes nothing. -/
theorem dyck_ampRead (m ℓ r p n : ℕ) (hn : r * blockWidth m ℓ + p * 2 = n)
    (k : ℕ) (hk : blockHeight m ℓ + 2 ≤ k) (ys : AmpDom m ℓ r) :
    composeOutOn (andStarRead (r := r)) (iterOut m ℓ) (andStarOut r) ys
      = dyck k n (ampRead m ℓ r p n hn ys) := by
  have hinv := ampWord_invariant m ℓ r p ys
  rw [ampOut_eq, ampRead]
  rcases ampFalse_le_one m ℓ r ys with hc | hc
  · rw [hc]
    have : dyck k n
        (wcast hn (ampWord m ℓ r p ys.1)) = true := by
      rw [dyck_eq_true, isDyck_wcast, isDyck_iff]
      refine ⟨?_, fun t =>
        ⟨hinv.1 t, (hinv.2.1 t).trans (by exact_mod_cast hk)⟩⟩
      rw [hinv.2.2, hc]
      norm_num
    rw [this]
    rfl
  · rw [hc]
    have : dyck k n
        (wcast hn (ampWord m ℓ r p ys.1)) = false := by
      rw [Bool.eq_false_iff]
      intro hd
      rw [dyck_eq_true, isDyck_wcast, isDyck_iff] at hd
      rw [hinv.2.2, hc] at hd
      exact absurd hd.1 (by norm_num)
    rw [this]
    rfl

/-! ## Query locality and injectivity -/

theorem ampRead_local (m ℓ r p n : ℕ) (hn : r * blockWidth m ℓ + p * 2 = n)
    (j : Fin n) :
    IsLocalCoord
      (composeReadOn (andStarRead (r := r)) (iterOut m ℓ)
        (iterRead (m := m) (ℓ := ℓ)))
      (ampRead m ℓ r p n hn) j := by
  set q : Fin (r * blockWidth m ℓ + p * 2) := Fin.cast hn.symm j with hq
  have hval : ∀ ys : AmpDom m ℓ r,
      ampRead m ℓ r p n hn ys j = ampWord m ℓ r p ys.1 q := fun _ => rfl
  by_cases hlt : (q : ℕ) < r * blockWidth m ℓ
  · obtain ⟨i₀, s, hs⟩ :=
      concatW_local (w := blockWidth m ℓ) r ⟨(q : ℕ), hlt⟩
    have hblk : ∀ ys : AmpDom m ℓ r,
        ampRead m ℓ r p n hn ys j = encodeWord m ℓ (ys.1 i₀).1 s := by
      intro ys
      rw [hval ys, ampWord,
        wordAppend_apply_left' _ _ ⟨(q : ℕ), hlt⟩ q rfl]
      exact hs _
    rcases encodeWord_local m ℓ s with ⟨i₁, hi₁⟩ | hconst
    · refine Or.inl ⟨(i₀, i₁), fun ys => ?_⟩
      rw [hblk ys, hi₁ (ys.1 i₀).1]
      rfl
    · exact Or.inr fun ys zs => by
        rw [hblk ys, hblk zs]
        exact hconst _ _
  · refine Or.inr fun ys zs => ?_
    rw [hval ys, hval zs, ampWord, ampWord,
      wordAppend_apply_right _ _ q hlt, wordAppend_apply_right _ _ q hlt]

theorem ampRead_injective (m ℓ r p n : ℕ)
    (hn : r * blockWidth m ℓ + p * 2 = n) :
    Function.Injective (ampRead m ℓ r p n hn) := by
  intro ys zs hyz
  refine Subtype.ext (funext fun i => Subtype.ext (funext fun i₁ => ?_))
  obtain ⟨p₁, hp₁⟩ := encodeWord_locate m ℓ i₁
  obtain ⟨k, hk⟩ := concatW_locate (w := blockWidth m ℓ) r i p₁
  have hread : ∀ us : AmpDom m ℓ r,
      ampRead m ℓ r p n hn us (Fin.cast hn (Fin.castAdd (p * 2) k))
        = (us.1 i).1 i₁ := by
    intro us
    show ampWord m ℓ r p us.1 _ = _
    rw [ampWord, wordAppend_apply_left' _ _ k _ rfl,
      hk (fun i => encodeWord m ℓ (us.1 i).1), hp₁ (us.1 i).1]
  rw [← hread ys, ← hread zs, hyz]

/-! ## The amplified lower bound -/

/-- **The `√r` amplification.**  The `√r` amplification of the block bound, at every
sufficiently large even length and every depth cap `k ≥ blockHeight m ℓ + 2`. -/
theorem sqrt_mul_pow_le_advPM_dyck (m ℓ r n k : ℕ) (hm : 0 < m) (hr : 0 < r)
    (hlen : r * blockWidth m ℓ ≤ n) (heven : Even n)
    (hk : blockHeight m ℓ + 2 ≤ k) :
    Real.sqrt r * (m : ℝ) ^ ℓ ≤ advPM (dyck k n) := by
  -- the padding length exists by parity alone
  obtain ⟨a, ha⟩ := heven
  obtain ⟨b, hb⟩ := (even_blockWidth m ℓ).mul_left r
  have hn : r * blockWidth m ℓ + (a - b) * 2 = n := by omega
  set p := a - b with hp
  have hdetEnc : ∀ ys zs : AmpDom m ℓ r,
      ampRead m ℓ r p n hn ys = ampRead m ℓ r p n hn zs →
        composeOutOn (andStarRead (r := r)) (iterOut m ℓ) (andStarOut r) ys
          = composeOutOn (andStarRead (r := r)) (iterOut m ℓ) (andStarOut r) zs :=
    fun ys zs h => by rw [ampRead_injective m ℓ r p n hn h]
  calc Real.sqrt r * (m : ℝ) ^ ℓ
      ≤ advPMOn (andStarRead (r := r)) (andStarOut r)
          * advPMOn (iterRead (m := m) (ℓ := ℓ)) (iterOut m ℓ) :=
        mul_le_mul (sqrt_le_advPMOn_andStar r hr)
          (pow_le_advPMOn_iterExact m hm ℓ) (by positivity)
          (advPMOn_nonneg (separates_of_injective andStarRead_injective _))
    _ ≤ advPMOn
          (composeReadOn (andStarRead (r := r)) (iterOut m ℓ)
            (iterRead (m := m) (ℓ := ℓ)))
          (composeOutOn (andStarRead (r := r)) (iterOut m ℓ) (andStarOut r)) :=
        advPMOn_mul_le_advPMOn_compose andStarRead_injective iterRead_injective
    _ ≤ advPMOn (ampRead m ℓ r p n hn)
          (composeOutOn (andStarRead (r := r)) (iterOut m ℓ) (andStarOut r)) :=
        advPMOn_mono_of_local hdetEnc (ampRead_local m ℓ r p n hn)
    _ ≤ advPM (dyck k n) :=
        advPMOn_le_advPM_of_injective (ampRead_injective m ℓ r p n hn)
          (dyck_ampRead m ℓ r p n hn k hk)

end MonoidProduct
