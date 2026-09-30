import MonoidProduct.Dyck.Concat
import MonoidProduct.Dyck.IterExact
import QuantumQueryComplexity.Promise.Transport
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The recursive block encoding and the special-length bound

Appendix E of Ambainis et al.: a depth-`ℓ` iterated exact-count input is encoded
as a parenthesis word — a *block* — whose total balance is `0` exactly when the
answer is `true`, and whose prefix balances stay in `[0, blockHeight m ℓ]`.

* base: a bit `b` becomes `uu` (balance `2`, meaning `false`) or `ud`
  (balance `0`, meaning `true`);
* successor: `B' = B₁ ⋯ B_{2m} d^{2m}`.

The exact-count promise is what makes this work: the children contribute total
balance `2·(number of false answers) ∈ {2m, 2m+2}`, so the closing run of `2m`
brings the total to `0` or `2` and never drops below zero.

Combining with `pow_le_advPMOn_iterExact` gives the special-length bound,

  `pow_le_advPM_dyck_block : (m : ℝ) ^ ℓ ≤ ADV±(dyck (blockHeight m ℓ) (blockWidth m ℓ))`,

the exact adversary analogue of Ambainis et al. Theorem 4.

## The encoder is defined on the cube, not on the promise

`encodeWord` takes an arbitrary `IterIdx m ℓ → Bool`; the promise `IterOk`
appears only as a hypothesis of the invariant.  That keeps proofs out of the
definition, so `encodeWord` never needs `Subtype` plumbing and the locality
statements below quantify over raw words.

The special-length bound is kept here, next to the encoding, so that the
encoding and its first consumer build in one step.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

/-! ## Widths and heights -/

/-- Width of a depth-`ℓ` block. -/
def blockWidth (m : ℕ) : ℕ → ℕ
  | 0 => 2
  | ℓ + 1 => 2 * m * (blockWidth m ℓ + 1)

/-- Height (maximal nesting depth) of a depth-`ℓ` block. -/
def blockHeight (m : ℕ) : ℕ → ℕ
  | 0 => 2
  | ℓ + 1 => blockHeight m ℓ + 2 * (m + 1)

@[simp] lemma blockWidth_zero (m : ℕ) : blockWidth m 0 = 2 := rfl
@[simp] lemma blockHeight_zero (m : ℕ) : blockHeight m 0 = 2 := rfl

lemma blockWidth_succ (m ℓ : ℕ) :
    blockWidth m (ℓ + 1) = 2 * m * (blockWidth m ℓ + 1) := rfl

lemma blockHeight_succ (m ℓ : ℕ) :
    blockHeight m (ℓ + 1) = blockHeight m ℓ + 2 * (m + 1) := rfl

/-- The closed height formula. -/
theorem blockHeight_eq (m ℓ : ℕ) : blockHeight m ℓ = 2 + 2 * ℓ * (m + 1) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih => rw [blockHeight_succ, ih]; ring

lemma blockWidth_succ_eq (m ℓ : ℕ) :
    2 * m * blockWidth m ℓ + 2 * m = blockWidth m (ℓ + 1) := by
  rw [blockWidth_succ]; ring

/-! ## The base encoding -/

/-- `false ↦ uu` (balance `2`), `true ↦ ud` (balance `0`). -/
def encodeBit (b : Bool) : Fin 2 → Bool := fun j => if (j : ℕ) = 1 then b else false

@[simp] lemma encodeBit_apply (b : Bool) (j : Fin 2) :
    encodeBit b j = if (j : ℕ) = 1 then b else false := rfl

lemma iterIdx_zero_eq (m : ℕ) (i : IterIdx m 0) : i = (() : Unit) := rfl

@[simp] lemma stepAt_encodeBit_zero (b : Bool) : stepAt (encodeBit b) 0 = 1 := by
  rw [stepAt_of_lt _ (by omega)]
  rfl

@[simp] lemma stepAt_encodeBit_one (b : Bool) :
    stepAt (encodeBit b) 1 = parenStep b := by
  rw [stepAt_of_lt _ (by omega)]
  rfl

lemma prefixBalance_encodeBit (b : Bool) (t : ℕ) :
    prefixBalance (encodeBit b) t
      = if t = 0 then 0 else if t = 1 then 1 else 1 + parenStep b := by
  match t with
  | 0 => simp
  | 1 => rw [prefixBalance_succ, prefixBalance_zero, stepAt_encodeBit_zero]; simp
  | (t + 2) =>
      rw [prefixBalance_of_ge _ (by omega), totalBalance, prefixBalance_succ,
        prefixBalance_succ, prefixBalance_zero, stepAt_encodeBit_zero,
        stepAt_encodeBit_one]
      simp

@[simp] lemma totalBalance_encodeBit (b : Bool) :
    totalBalance (encodeBit b) = if b then 0 else 2 := by
  rw [totalBalance, prefixBalance_encodeBit]
  cases b <;> simp <;> rfl

lemma prefixBalance_encodeBit_bounds (b : Bool) (t : ℕ) :
    0 ≤ prefixBalance (encodeBit b) t ∧ prefixBalance (encodeBit b) t ≤ 2 := by
  rw [prefixBalance_encodeBit]
  split_ifs
  · exact ⟨le_refl 0, by norm_num⟩
  · exact ⟨by norm_num, by norm_num⟩
  · cases b <;> norm_num

/-! ## The encoder -/

/-- The block word of a (not necessarily promised) input. -/
def encodeWord (m : ℕ) :
    (ℓ : ℕ) → (IterIdx m ℓ → Bool) → Fin (blockWidth m ℓ) → Bool
  | 0, x => encodeBit (x ())
  | ℓ + 1, x =>
      wcast (blockWidth_succ_eq m ℓ)
        (wordAppend
          (concatW (blockWidth m ℓ) (2 * m) fun i => encodeWord m ℓ (child x i))
          (dRun (2 * m)))

lemma encodeWord_zero (m : ℕ) (x : IterIdx m 0 → Bool) :
    encodeWord m 0 x = encodeBit (x ()) := rfl

lemma encodeWord_succ (m ℓ : ℕ) (x : IterIdx m (ℓ + 1) → Bool) :
    encodeWord m (ℓ + 1) x
      = wcast (blockWidth_succ_eq m ℓ)
        (wordAppend
          (concatW (blockWidth m ℓ) (2 * m) fun i => encodeWord m ℓ (child x i))
          (dRun (2 * m))) := rfl

/-! ## The block invariant -/

/-- The children's total balances add up to twice the number of `false`
answers. -/
lemma sum_totalBalance_children (m ℓ : ℕ) (x : IterIdx m (ℓ + 1) → Bool)
    (hval : ∀ i, totalBalance (encodeWord m ℓ (child x i))
      = if iterVal m ℓ (child x i) then 0 else 2) :
    (∑ i, totalBalance (encodeWord m ℓ (child x i)))
      = 2 * (falseCount (fun i => iterVal m ℓ (child x i)) : ℤ) := by
  classical
  rw [Finset.sum_congr rfl fun i _ => hval i]
  have hstep : ∀ i : Fin (2 * m),
      (if iterVal m ℓ (child x i) then (0 : ℤ) else 2)
        = if iterVal m ℓ (child x i) = false then (2 : ℤ) else 0 := by
    intro i
    cases h : iterVal m ℓ (child x i) <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.sum_filter]
  rw [show (Finset.univ.filter fun i => iterVal m ℓ (child x i) = false)
      = zeroSet (fun i => iterVal m ℓ (child x i)) from rfl]
  rw [Finset.sum_const, falseCount, nsmul_eq_mul]
  ring

/-- **The simultaneous induction for the block invariant.** -/
theorem encodeWord_invariant (m : ℕ) :
    ∀ (ℓ : ℕ) (x : IterIdx m ℓ → Bool), IterOk m ℓ x →
      (∀ t, 0 ≤ prefixBalance (encodeWord m ℓ x) t) ∧
        (∀ t, prefixBalance (encodeWord m ℓ x) t ≤ (blockHeight m ℓ : ℤ)) ∧
        totalBalance (encodeWord m ℓ x) = if iterVal m ℓ x then 0 else 2
  | 0, x, _ => by
      refine ⟨fun t => (prefixBalance_encodeBit_bounds (x ()) t).1, fun t => ?_, ?_⟩
      · rw [blockHeight_zero]
        exact_mod_cast (prefixBalance_encodeBit_bounds (x ()) t).2
      · exact totalBalance_encodeBit (x ())
  | ℓ + 1, x, hx => by
      classical
      set w := blockWidth m ℓ with hw
      set h := blockHeight m ℓ with hh
      set B : Fin (2 * m) → Fin w → Bool :=
        fun i => encodeWord m ℓ (child x i) with hB
      have hchild := fun i => encodeWord_invariant m ℓ (child x i) (hx.1 i)
      have hnn : ∀ i t, 0 ≤ prefixBalance (B i) t := fun i => (hchild i).1
      have hle : ∀ i t, prefixBalance (B i) t ≤ (h : ℤ) := fun i => (hchild i).2.1
      have hsum : (∑ i, totalBalance (B i))
          = 2 * (falseCount (fun i => iterVal m ℓ (child x i)) : ℤ) :=
        sum_totalBalance_children m ℓ x fun i => (hchild i).2.2
      -- the promise bounds the number of `false` children
      have hcount : (m : ℤ) ≤ (falseCount (fun i => iterVal m ℓ (child x i)) : ℤ)
          ∧ (falseCount (fun i => iterVal m ℓ (child x i)) : ℤ) ≤ (m : ℤ) + 1 := by
        rcases hx.2 with hc | hc <;> rw [hc] <;> constructor <;> push_cast <;> omega
      have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
      have hcat := prefixBalance_concatW_bounds w hh0 (2 * m) B hnn hle
      have htotcat : totalBalance (concatW w (2 * m) B)
          = 2 * (falseCount (fun i => iterVal m ℓ (child x i)) : ℤ) := by
        rw [totalBalance_concatW, hsum]
      refine ⟨fun t => ?_, fun t => ?_, ?_⟩
      · rw [encodeWord_succ, prefixBalance_wcast]
        rcases Nat.lt_or_ge t (2 * m * w) with ht | ht
        · rw [prefixBalance_wordAppend_left _ _ (le_of_lt ht)]
          exact (hcat t).1
        · obtain ⟨s, rfl⟩ : ∃ s, t = 2 * m * w + s := ⟨t - 2 * m * w, by omega⟩
          rw [prefixBalance_wordAppend_right, htotcat, prefixBalance_dRun]
          have : ((min s (2 * m) : ℕ) : ℤ) ≤ 2 * (m : ℤ) := by
            have : min s (2 * m) ≤ 2 * m := Nat.min_le_right _ _
            push_cast
            omega
          linarith [hcount.1]
      · rw [encodeWord_succ, prefixBalance_wcast, blockHeight_succ]
        push_cast
        rcases Nat.lt_or_ge t (2 * m * w) with ht | ht
        · rw [prefixBalance_wordAppend_left _ _ (le_of_lt ht)]
          have := (hcat t).2
          rw [hsum] at this
          linarith [hcount.2]
        · obtain ⟨s, rfl⟩ : ∃ s, t = 2 * m * w + s := ⟨t - 2 * m * w, by omega⟩
          rw [prefixBalance_wordAppend_right, htotcat, prefixBalance_dRun]
          have hmin : (0 : ℤ) ≤ ((min s (2 * m) : ℕ) : ℤ) := Int.natCast_nonneg _
          linarith [hcount.2]
      · rw [encodeWord_succ, totalBalance_wcast, totalBalance_wordAppend,
          htotcat, totalBalance_dRun]
        show _ = if decide (falseCount (fun i => iterVal m ℓ (child x i)) = m)
          then (0 : ℤ) else 2
        rcases hx.2 with hc | hc
        · rw [hc]
          simp
        · rw [hc, if_neg (by simp)]
          push_cast
          ring

theorem encodeWord_nonneg (m ℓ : ℕ) (x : IterIdx m ℓ → Bool) (hx : IterOk m ℓ x)
    (t : ℕ) : 0 ≤ prefixBalance (encodeWord m ℓ x) t :=
  (encodeWord_invariant m ℓ x hx).1 t

theorem encodeWord_le (m ℓ : ℕ) (x : IterIdx m ℓ → Bool) (hx : IterOk m ℓ x)
    (t : ℕ) : prefixBalance (encodeWord m ℓ x) t ≤ (blockHeight m ℓ : ℤ) :=
  (encodeWord_invariant m ℓ x hx).2.1 t

theorem encodeWord_total (m ℓ : ℕ) (x : IterIdx m ℓ → Bool) (hx : IterOk m ℓ x) :
    totalBalance (encodeWord m ℓ x) = if iterVal m ℓ x then 0 else 2 :=
  (encodeWord_invariant m ℓ x hx).2.2

/-- **Language correctness**: the encoded word is Dyck exactly when the tree
answers `true`. -/
theorem dyck_encodeWord (m ℓ : ℕ) (x : IterIdx m ℓ → Bool) (hx : IterOk m ℓ x) :
    dyck (blockHeight m ℓ) (blockWidth m ℓ) (encodeWord m ℓ x) = iterVal m ℓ x := by
  have hinv := encodeWord_invariant m ℓ x hx
  cases hv : iterVal m ℓ x
  · -- answer `false`: total balance is `2`, so not Dyck
    rw [Bool.eq_false_iff]
    intro hd
    rw [dyck_eq_true, isDyck_iff] at hd
    have := hinv.2.2
    rw [hv, if_neg (by simp), hd.1] at this
    exact absurd this (by norm_num)
  · rw [dyck_eq_true, isDyck_iff]
    refine ⟨?_, fun t => ⟨hinv.1 t, hinv.2.1 t⟩⟩
    have := hinv.2.2
    rwa [hv, if_pos rfl] at this

/-! ## Query locality and injectivity -/

/-- Every position of the encoded word is one fixed leaf, or is constant. -/
theorem encodeWord_local (m : ℕ) :
    ∀ (ℓ : ℕ) (j : Fin (blockWidth m ℓ)),
      (∃ i : IterIdx m ℓ, ∀ x : IterIdx m ℓ → Bool, encodeWord m ℓ x j = x i)
        ∨ (∀ x y : IterIdx m ℓ → Bool, encodeWord m ℓ x j = encodeWord m ℓ y j)
  | 0, j => by
      by_cases hj : (j : ℕ) = 1
      · exact Or.inl ⟨(), fun x => by
          show (if (j : ℕ) = 1 then x () else false) = x ()
          rw [if_pos hj]⟩
      · refine Or.inr fun x y => ?_
        show (if (j : ℕ) = 1 then x () else false)
          = (if (j : ℕ) = 1 then y () else false)
        rw [if_neg hj, if_neg hj]
  | ℓ + 1, j => by
      obtain ⟨p, rfl⟩ : ∃ p : Fin (2 * m * blockWidth m ℓ + 2 * m),
          j = Fin.cast (blockWidth_succ_eq m ℓ) p :=
        ⟨Fin.cast (blockWidth_succ_eq m ℓ).symm j, Fin.ext (by simp)⟩
      have hsplit : ∀ x : IterIdx m (ℓ + 1) → Bool,
          encodeWord m (ℓ + 1) x (Fin.cast (blockWidth_succ_eq m ℓ) p)
            = wordAppend
                (concatW (blockWidth m ℓ) (2 * m)
                  fun i => encodeWord m ℓ (child x i))
                (dRun (2 * m)) p := fun x => rfl
      by_cases hlt : (p : ℕ) < 2 * m * blockWidth m ℓ
      · obtain ⟨i₀, s, hs⟩ :=
          concatW_local (w := blockWidth m ℓ) (2 * m) ⟨(p : ℕ), hlt⟩
        have hval : ∀ x : IterIdx m (ℓ + 1) → Bool,
            encodeWord m (ℓ + 1) x (Fin.cast (blockWidth_succ_eq m ℓ) p)
              = encodeWord m ℓ (child x i₀) s := by
          intro x
          rw [hsplit x, wordAppend_apply_left' _ _ ⟨(p : ℕ), hlt⟩ p rfl]
          exact hs _
        rcases encodeWord_local m ℓ s with ⟨i₁, hi₁⟩ | hconst
        · exact Or.inl ⟨(i₀, i₁), fun x => by rw [hval x, hi₁ (child x i₀)]; rfl⟩
        · exact Or.inr fun x y => by rw [hval x, hval y]; exact hconst _ _
      · refine Or.inr fun x y => ?_
        rw [hsplit x, hsplit y,
          wordAppend_apply_right _ _ p hlt, wordAppend_apply_right _ _ p hlt]

/-- Every leaf is read at some position. -/
theorem encodeWord_locate (m : ℕ) :
    ∀ (ℓ : ℕ) (i : IterIdx m ℓ),
      ∃ p : Fin (blockWidth m ℓ),
        ∀ x : IterIdx m ℓ → Bool, encodeWord m ℓ x p = x i
  | 0, i => ⟨⟨1, by simp⟩, fun x => by
      show (if ((⟨1, by simp⟩ : Fin 2) : ℕ) = 1 then x () else false) = x i
      rw [if_pos rfl, iterIdx_zero_eq m i]⟩
  | ℓ + 1, i => by
      obtain ⟨p₁, hp₁⟩ := encodeWord_locate m ℓ i.2
      obtain ⟨k, hk⟩ := concatW_locate (w := blockWidth m ℓ) (2 * m) i.1 p₁
      refine ⟨Fin.cast (blockWidth_succ_eq m ℓ) (Fin.castAdd (2 * m) k),
        fun x => ?_⟩
      have hsplit : encodeWord m (ℓ + 1) x
            (Fin.cast (blockWidth_succ_eq m ℓ) (Fin.castAdd (2 * m) k))
          = wordAppend
              (concatW (blockWidth m ℓ) (2 * m)
                fun i => encodeWord m ℓ (child x i))
              (dRun (2 * m)) (Fin.castAdd (2 * m) k) := rfl
      rw [hsplit, wordAppend_apply_left' _ _ k _ rfl,
        hk (fun i => encodeWord m ℓ (child x i)), hp₁ (child x i.1)]
      rfl

/-! ## The special-length lower bound -/

/-- The block encoder, as an observation map on the promise domain. -/
def blockRead (m ℓ : ℕ) (x : IterDom m ℓ) : Fin (blockWidth m ℓ) → Bool :=
  encodeWord m ℓ x.1

theorem blockRead_injective (m ℓ : ℕ) :
    Function.Injective (blockRead m ℓ) := by
  intro x y hxy
  refine Subtype.ext (funext fun i => ?_)
  obtain ⟨p, hp⟩ := encodeWord_locate m ℓ i
  rw [← hp x.1, ← hp y.1]
  exact congrFun hxy p

theorem dyck_blockRead (m ℓ : ℕ) (x : IterDom m ℓ) :
    iterOut m ℓ x
      = dyck (blockHeight m ℓ) (blockWidth m ℓ) (blockRead m ℓ x) :=
  (dyck_encodeWord m ℓ x.1 x.2).symm

/-- **The special-length lower bound** (Ambainis et al. Theorem 4, adversary
form). -/
theorem pow_le_advPM_dyck_block (m ℓ : ℕ) (hm : 0 < m) :
    (m : ℝ) ^ ℓ ≤ advPM (dyck (blockHeight m ℓ) (blockWidth m ℓ)) := by
  have hdetEnc : ∀ x y : IterDom m ℓ,
      blockRead m ℓ x = blockRead m ℓ y → iterOut m ℓ x = iterOut m ℓ y :=
    fun x y h => by rw [blockRead_injective m ℓ h]
  have hloc : ∀ j, IsLocalCoord (iterRead (m := m) (ℓ := ℓ)) (blockRead m ℓ) j := by
    intro j
    rcases encodeWord_local m ℓ j with ⟨i, hi⟩ | hconst
    · exact Or.inl ⟨i, fun x => hi x.1⟩
    · exact Or.inr fun x y => hconst x.1 y.1
  calc (m : ℝ) ^ ℓ
      ≤ advPMOn (iterRead (m := m) (ℓ := ℓ)) (iterOut m ℓ) :=
        pow_le_advPMOn_iterExact m hm ℓ
    _ ≤ advPMOn (blockRead m ℓ) (iterOut m ℓ) :=
        advPMOn_mono_of_local hdetEnc hloc
    _ ≤ advPM (dyck (blockHeight m ℓ) (blockWidth m ℓ)) :=
        advPMOn_le_advPM_of_injective (blockRead_injective m ℓ) (dyck_blockRead m ℓ)

/-! ## Finite checks

The recurrences at small parameters, and an exhaustive check: enumerate the
*entire* promise at `(m, ℓ) = (1,1)` and `(1,2)` and check the reduction
`dyck_encodeWord` by evaluation. -/

example : blockWidth 1 1 = 6 := by decide
example : blockHeight 1 1 = 6 := by decide
example : blockWidth 1 2 = 14 := by decide
example : blockHeight 1 2 = 10 := by decide
example : blockWidth 4 1 = 24 := by decide

example : ∀ x : IterDom 1 1,
    dyck (blockHeight 1 1) (blockWidth 1 1) (encodeWord 1 1 x.1)
      = iterVal 1 1 x.1 := by decide

example : ∀ x : IterDom 1 2,
    dyck (blockHeight 1 2) (blockWidth 1 2) (encodeWord 1 2 x.1)
      = iterVal 1 2 x.1 := by decide

end MonoidProduct
