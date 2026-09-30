import MonoidProduct.Aperiodic.Infix
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Infix search: the windows are the prefix and suffix searches

Infix search (`lem:infix`), first half.  The two halves of a marked cut are
*literally* the searches of `MonoidProduct/Aperiodic/Prefix.lean` and `Suffix.lean`,
run on a word of the window's length:

  `leftMark  letter a p ℓ c x = suffixEvent letter a p` on `[c-4ℓ, c)`,
  `rightMark letter q b ℓ c x = prefixEvent letter q b` on `[c, min n (c+4ℓ))`,

so `HasDual.pullback` — which charges nothing for an injective inclusion of
coordinates — hands over the prefix and suffix search bounds at a cost governed by the
*window's* length, not the word's.  That is the whole point of having made the
equality-test interface uniform in the length.

The strict-inclusion hypotheses those searches need come from
`MonoidProduct/Aperiodic/Split.lean`, and the values they test at all sit at or
above `p` (resp. `q`) in the `J`-order, hence strictly below the target — so the
recursion the cost is charged to is a legitimate one.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The two identifications -/

private lemma letter_winEmb (letter : σ → M) {n : ℕ} (x : Fin n → σ)
    {lo len : ℕ} (hle : lo + len ≤ n) (k : Fin len) :
    letter (x (winEmb lo len hle k))
      = padAt (fun t => letter (x t)) (lo + (k : ℕ)) := by
  rw [padAt_of_lt _ (show lo + (k : ℕ) < n by have := k.isLt; omega)]
  rfl

/-- **A window search is a suffix search on the window.** -/
theorem suffixEvent_winEmb (letter : σ → M) (a p : M) {n lo len : ℕ}
    (hle : lo + len ≤ n) (x : Fin n → σ) :
    suffixEvent letter a p (fun t => x (winEmb lo len hle t))
      = decide (∃ i ∈ Finset.Ico lo (lo + len),
          padAt (fun t => letter (x t)) i = a ∧
            winProd letter x (i + 1) (lo + len) = p) := by
  rw [Bool.eq_iff_iff, suffixEvent]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨k, hlet, hp⟩
    have hk := k.isLt
    refine ⟨lo + (k : ℕ), Finset.mem_Ico.2 ⟨by omega, by omega⟩, ?_, ?_⟩
    · rw [← letter_winEmb letter x hle k]
      exact hlet
    · rw [show lo + (k : ℕ) + 1 = lo + ((k : ℕ) + 1) from by omega,
        ← winProd_winEmb letter x hle (show (k : ℕ) + 1 ≤ len by omega)
          (le_refl len)]
      exact hp
  · rintro ⟨i, hi, hlet, hp⟩
    rw [Finset.mem_Ico] at hi
    refine ⟨⟨i - lo, by omega⟩, ?_, ?_⟩
    · rw [letter_winEmb letter x hle ⟨i - lo, by omega⟩,
        show lo + (i - lo) = i from by omega]
      exact hlet
    · rw [winProd_winEmb letter x hle (show i - lo + 1 ≤ len by omega)
        (le_refl len), show lo + (i - lo + 1) = i + 1 from by omega]
      exact hp

/-- **A window search is a prefix search on the window.** -/
theorem prefixEvent_winEmb (letter : σ → M) (q b : M) {n lo len : ℕ}
    (hle : lo + len ≤ n) (x : Fin n → σ) :
    prefixEvent letter q b (fun t => x (winEmb lo len hle t))
      = decide (∃ j ∈ Finset.Ico lo (lo + len),
          winProd letter x lo j = q ∧ padAt (fun t => letter (x t)) j = b) := by
  rw [Bool.eq_iff_iff, prefixEvent]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨k, hp, hlet⟩
    have hk := k.isLt
    have hw := winProd_winEmb letter x hle (Nat.zero_le (k : ℕ))
      (show (k : ℕ) ≤ len from le_of_lt hk)
    rw [Nat.add_zero] at hw
    refine ⟨lo + (k : ℕ), Finset.mem_Ico.2 ⟨by omega, by omega⟩, ?_, ?_⟩
    · rw [← hw]; exact hp
    · rw [← letter_winEmb letter x hle k]; exact hlet
  · rintro ⟨j, hj, hp, hlet⟩
    rw [Finset.mem_Ico] at hj
    have hw := winProd_winEmb letter x hle (Nat.zero_le (j - lo))
      (show j - lo ≤ len by omega)
    rw [Nat.add_zero, show lo + (j - lo) = j from by omega] at hw
    refine ⟨⟨j - lo, by omega⟩, ?_, ?_⟩
    · rw [hw]; exact hp
    · rw [letter_winEmb letter x hle ⟨j - lo, by omega⟩,
        show lo + (j - lo) = j from by omega]
      exact hlet

/-- The left half of a marked cut, as a suffix search. -/
theorem leftMark_eq (letter : σ → M) (a p : M) {n ℓ c : ℕ} (hc : c ≤ n)
    (x : Fin n → σ) :
    leftMark letter a p ℓ c x
      = suffixEvent letter a p
          (fun t => x (winEmb (c - 4 * ℓ) (c - (c - 4 * ℓ))
            (show c - 4 * ℓ + (c - (c - 4 * ℓ)) ≤ n by omega) t)) := by
  rw [suffixEvent_winEmb, Bool.eq_iff_iff, leftMark_eq_true]
  rw [show c - 4 * ℓ + (c - (c - 4 * ℓ)) = c from by omega]
  simp only [decide_eq_true_eq]

/-- The right half of a marked cut, as a prefix search. -/
theorem rightMark_eq (letter : σ → M) (q b : M) {n ℓ c : ℕ} (hc : c ≤ n)
    (x : Fin n → σ) :
    rightMark letter q b ℓ c x
      = prefixEvent letter q b
          (fun t => x (winEmb c (min n (c + 4 * ℓ) - c)
            (show c + (min n (c + 4 * ℓ) - c) ≤ n by omega) t)) := by
  rw [prefixEvent_winEmb, Bool.eq_iff_iff, rightMark_eq_true]
  rw [show c + (min n (c + 4 * ℓ) - c) = min n (c + 4 * ℓ) from by omega]
  simp only [decide_eq_true_eq]

end

/-! ## The windowed duals -/

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **The left half of a marked cut, with its exact recursive support.**
The suffix search can query equality only at elements of `leftAbove p`; no
global `J`-level hypothesis is needed at this interface. -/
theorem hasDual_leftMark_above (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s ∈ leftAbove p, ∀ len ≤ c - (c - 4 * ℓ),
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => leftMark letter a p ℓ c x)
      (2 * ((Nat.clog 2 (c - (c - 4 * ℓ) + 1) : ℝ) + 2)
        * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) := by
  have hle : c - 4 * ℓ + (c - (c - 4 * ℓ)) ≤ n := by omega
  have hsuf := hasDual_suffixEvent (σ := σ) letter
    (leftIdeal_lt_of_mem_setG hG hpq) (n := c - (c - 4 * ℓ)) hQ hrec
  exact (hsuf.pullback (winEmb_injective hle)).ofEq fun x => by
    rw [pullbackFun_apply, ← leftMark_eq letter a p hc x]

/-- **The left half of a marked cut, priced.**  The window has length
`c - (c - 4ℓ) ≤ min (4ℓ) n`, and the equality tests are run only at values in
`leftAbove p`, every one of which is strictly below the target. -/
theorem hasDual_leftMark_strict (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s : M, twoIdeal m ⊂ twoIdeal s →
      ∀ len ≤ c - (c - 4 * ℓ), HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => leftMark letter a p ℓ c x)
      (2 * ((Nat.clog 2 (c - (c - 4 * ℓ) + 1) : ℝ) + 2)
        * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) :=
  hasDual_leftMark_above letter hG hpq hc hQ fun s hs len hlen =>
    hrec s (lt_of_lt_of_le (twoIdeal_lt_of_split_left hG hpq)
      (twoIdeal_subset_of_mem_leftAbove hs)) len hlen

/-- The numeric `jLevel` form: a specialization of the localized one, since a
strict containment lowers the level. -/
theorem hasDual_leftMark (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s : M, jLevel s < jLevel m →
      ∀ len ≤ c - (c - 4 * ℓ), HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => leftMark letter a p ℓ c x)
      (2 * ((Nat.clog 2 (c - (c - 4 * ℓ) + 1) : ℝ) + 2)
        * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) :=
  hasDual_leftMark_strict letter hG hpq hc hQ fun s hs => hrec s (jLevel_lt_of_ssubset hs)

/-- **The right half of a marked cut, with its exact recursive support.** -/
theorem hasDual_rightMark_above (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s ∈ rightAbove q, ∀ len ≤ min n (c + 4 * ℓ) - c,
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => rightMark letter q b ℓ c x)
      (2 * ((Nat.clog 2 (min n (c + 4 * ℓ) - c + 1) : ℝ) + 2)
        * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) := by
  have hle : c + (min n (c + 4 * ℓ) - c) ≤ n := by omega
  have hpre := hasDual_prefixEvent (σ := σ) letter
    (rightIdeal_lt_of_mem_setG hG hpq) (n := min n (c + 4 * ℓ) - c) hQ hrec
  exact (hpre.pullback (winEmb_injective hle)).ofEq fun x => by
    rw [pullbackFun_apply, ← rightMark_eq letter q b hc x]

/-- **The right half of a marked cut, priced.** -/
theorem hasDual_rightMark_strict (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s : M, twoIdeal m ⊂ twoIdeal s →
      ∀ len ≤ min n (c + 4 * ℓ) - c, HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => rightMark letter q b ℓ c x)
      (2 * ((Nat.clog 2 (min n (c + 4 * ℓ) - c + 1) : ℝ) + 2)
        * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) :=
  hasDual_rightMark_above letter hG hpq hc hQ fun s hs len hlen =>
    hrec s (lt_of_lt_of_le (twoIdeal_lt_of_split_right hG hpq)
      (twoIdeal_subset_of_mem_rightAbove hs)) len hlen

/-- The numeric `jLevel` form, a specialization of the localized one. -/
theorem hasDual_rightMark (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s : M, jLevel s < jLevel m →
      ∀ len ≤ min n (c + 4 * ℓ) - c, HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => rightMark letter q b ℓ c x)
      (2 * ((Nat.clog 2 (min n (c + 4 * ℓ) - c + 1) : ℝ) + 2)
        * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) :=
  hasDual_rightMark_strict letter hG hpq hc hQ fun s hs => hrec s (jLevel_lt_of_ssubset hs)

end


/-! ## The assembly

Infix search (`lem:infix`), second half.  Three square-root searches, one
per existential of `badInfixFor_iff`: over split pairs, over grid cuts, and over
scales.  The middle one is where the cost is decided — a window of width `4ℓ`
costs `√(4ℓ)`, a search over the cuts at scale `ℓ` costs `√|grid|`, and
`card_cutGrid_mul_le` says `|grid| ℓ ≤ 16 n`, so the product is `√(68 n)`
whatever the scale.  Only after that cancellation is the bound uniform in `ℓ`
and the outer search over scales can be taken. -/

section Assembly

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- The three existentials of `badInfixFor_iff` as a `Finset.sup`, which is the
form `HasDual.finsetSup` consumes. -/
theorem badInfixFor_sup (letter : σ → M) (a r b : M) {n : ℕ} (x : Fin n → σ) :
    badInfixFor letter a r b x
      = (scales n).sup fun ℓ => (cutGrid n ℓ).sup fun c =>
          (splitPairs r).sup fun pq => markedAt letter a pq.1 pq.2 b ℓ c x := by
  rw [Bool.eq_iff_iff, badInfixFor_iff, sup_bool_eq_true]
  constructor
  · rintro ⟨ℓ, hℓ, c, hc, pq, hpq, hm⟩
    refine ⟨ℓ, hℓ, ?_⟩
    rw [sup_bool_eq_true]
    refine ⟨c, hc, ?_⟩
    rw [sup_bool_eq_true]
    exact ⟨pq, hpq, hm⟩
  · rintro ⟨ℓ, hℓ, h1⟩
    rw [sup_bool_eq_true] at h1
    obtain ⟨c, hc, h2⟩ := h1
    rw [sup_bool_eq_true] at h2
    obtain ⟨pq, hpq, hm⟩ := h2
    exact ⟨ℓ, hℓ, c, hc, pq, hpq, hm⟩

/-- **The square-root cancellation.** -/
lemma sqrt_win_mul_grid_le {n ℓ : ℕ} (h2 : 2 ≤ ℓ) (hln : ℓ ≤ n) :
    Real.sqrt (4 * (ℓ : ℝ)) * Real.sqrt (((cutGrid n ℓ).card : ℝ) + 1)
      ≤ Real.sqrt (68 * (n : ℝ)) := by
  have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have h1 : ((cutGrid n ℓ).card : ℝ) * (ℓ : ℝ) ≤ 16 * (n : ℝ) := by
    exact_mod_cast card_cutGrid_mul_le h2 hln
  have h2' : (ℓ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hln
  nlinarith

lemma sqrt_grid_le (n ℓ : ℕ) :
    Real.sqrt (((cutGrid n ℓ).card : ℝ) + 1) ≤ Real.sqrt ((n : ℝ) + 2) := by
  refine Real.sqrt_le_sqrt ?_
  have h : ((cutGrid n ℓ).card : ℝ) ≤ (n : ℝ) + 1 := by
    have := card_cutGrid_le n ℓ
    have hd : n / gridStep ℓ ≤ n := Nat.div_le_self _ _
    have : (cutGrid n ℓ).card ≤ n + 1 := le_trans this (by omega)
    exact_mod_cast this
  linarith

/-- **One marked cut with two independent recursive prices.**  The left and
right searches retain their actual clipped window lengths and expose only the
values they can query: `leftAbove p` on the left and `rightAbove q` on the
right.  Thus `HasDual.combine₂` charges exactly twice the sum of the two
side costs, without first replacing them by a common worst-case price. -/
theorem hasDual_markedAt_split (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {BL BR : ℝ} (hBL : 0 ≤ BL) (hBR : 0 ≤ BR)
    (hrecL : ∀ s ∈ leftAbove p, ∀ len ≤ c - (c - 4 * ℓ),
      HasDual (eqProd (n := len) letter s) (BL * Real.sqrt (len : ℝ)))
    (hrecR : ∀ s ∈ rightAbove q, ∀ len ≤ min n (c + 4 * ℓ) - c,
      HasDual (eqProd (n := len) letter s) (BR * Real.sqrt (len : ℝ))) :
    HasDual (fun x : Fin n → σ => markedAt letter a p q b ℓ c x)
      (2 *
        (2 * ((Nat.clog 2 (c - (c - 4 * ℓ) + 1) : ℝ) + 2)
            * (BL * Real.sqrt ((c - (c - 4 * ℓ) : ℕ) : ℝ)
                * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
          + 2 * ((Nat.clog 2 (min n (c + 4 * ℓ) - c + 1) : ℝ) + 2)
            * (BR * Real.sqrt ((min n (c + 4 * ℓ) - c : ℕ) : ℝ)
                * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2))) := by
  classical
  have hQL : (0 : ℝ) ≤ BL * Real.sqrt ((c - (c - 4 * ℓ) : ℕ) : ℝ) := by
    positivity
  have hQR : (0 : ℝ) ≤ BR * Real.sqrt ((min n (c + 4 * ℓ) - c : ℕ) : ℝ) := by
    positivity
  have hL : HasDual (fun x : Fin n → σ => leftMark letter a p ℓ c x)
      (2 * ((Nat.clog 2 (c - (c - 4 * ℓ) + 1) : ℝ) + 2)
        * (BL * Real.sqrt ((c - (c - 4 * ℓ) : ℕ) : ℝ)
            * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) := by
    refine hasDual_leftMark_above letter hG hpq hc hQL ?_
    intro s hs len hlen
    refine (hrecL s hs len hlen).mono ?_
    have hsqrt : Real.sqrt (len : ℝ)
        ≤ Real.sqrt ((c - (c - 4 * ℓ) : ℕ) : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      exact_mod_cast hlen
    nlinarith [Real.sqrt_nonneg (len : ℝ)]
  have hR : HasDual (fun x : Fin n → σ => rightMark letter q b ℓ c x)
      (2 * ((Nat.clog 2 (min n (c + 4 * ℓ) - c + 1) : ℝ) + 2)
        * (BR * Real.sqrt ((min n (c + 4 * ℓ) - c : ℕ) : ℝ)
            * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) := by
    refine hasDual_rightMark_above letter hG hpq hc hQR ?_
    intro s hs len hlen
    refine (hrecR s hs len hlen).mono ?_
    have hsqrt : Real.sqrt (len : ℝ)
        ≤ Real.sqrt ((min n (c + 4 * ℓ) - c : ℕ) : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      exact_mod_cast hlen
    nlinarith [Real.sqrt_nonneg (len : ℝ)]
  have hCL : (0 : ℝ) ≤
      2 * ((Nat.clog 2 (c - (c - 4 * ℓ) + 1) : ℝ) + 2)
        * (BL * Real.sqrt ((c - (c - 4 * ℓ) : ℕ) : ℝ)
            * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2) := by positivity
  have hCR : (0 : ℝ) ≤
      2 * ((Nat.clog 2 (min n (c + 4 * ℓ) - c + 1) : ℝ) + 2)
        * (BR * Real.sqrt ((min n (c + 4 * ℓ) - c : ℕ) : ℝ)
            * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2) := by positivity
  exact (HasDual.combine₂ (fun u v : Bool => u && v) hCL hCR hL hR).ofEq fun x => rfl

/-- One marked cut, priced uniformly in the cut position, **with its exact
recursive support**: the two sides ask only for values in `leftAbove p` and
`rightAbove q`. -/
theorem hasDual_markedAt_above (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {B : ℝ} (hB : 0 ≤ B)
    (hrecL : ∀ s ∈ leftAbove p, ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ)))
    (hrecR : ∀ s ∈ rightAbove q, ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (fun x : Fin n → σ => markedAt letter a p q b ℓ c x)
      (4 * (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
        * (B * Real.sqrt (4 * (ℓ : ℝ))
            * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2))) := by
  have hsplit := hasDual_markedAt_split letter hG hpq (n := n) (ℓ := ℓ) (c := c) hc hB hB
    (fun s hs len hlen => hrecL s hs len (by omega))
    (fun s hs len hlen => hrecR s hs len (by omega))
  refine hsplit.mono ?_
  -- A side's true window is at most both `n` and `4ℓ`.
  have hside : ∀ w : ℕ, w ≤ n → w ≤ 4 * ℓ →
      2 * ((Nat.clog 2 (w + 1) : ℝ) + 2)
          * (B * Real.sqrt (w : ℝ)
              * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
        ≤ 2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
          * (B * Real.sqrt (4 * (ℓ : ℝ))
              * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2) := by
    intro w hwn hwℓ
    have hlog : (Nat.clog 2 (w + 1) : ℝ) ≤ (Nat.clog 2 (n + 1) : ℝ) := by
      exact_mod_cast Nat.clog_mono_right 2 (by omega)
    have hsqrt : Real.sqrt (w : ℝ) ≤ Real.sqrt (4 * (ℓ : ℝ)) := by
      refine Real.sqrt_le_sqrt ?_
      exact_mod_cast hwℓ
    have hmul := mul_le_mul_of_nonneg_left hsqrt
      (show (0 : ℝ) ≤ B * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) by
        positivity)
    have hinner : B * Real.sqrt (w : ℝ)
          * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2
        ≤ B * Real.sqrt (4 * (ℓ : ℝ))
          * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2 := by
      nlinarith
    exact mul_le_mul (by nlinarith :
        2 * ((Nat.clog 2 (w + 1) : ℝ) + 2)
          ≤ 2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)) hinner
      (by positivity) (by positivity)
  have hL := hside (c - (c - 4 * ℓ)) (by omega) (by omega)
  have hR := hside (min n (c + 4 * ℓ) - c) (by omega) (by omega)
  calc
    2 *
          (2 * ((Nat.clog 2 (c - (c - 4 * ℓ) + 1) : ℝ) + 2)
                * (B * Real.sqrt ((c - (c - 4 * ℓ) : ℕ) : ℝ)
                    * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
            + 2 * ((Nat.clog 2 (min n (c + 4 * ℓ) - c + 1) : ℝ) + 2)
                * (B * Real.sqrt ((min n (c + 4 * ℓ) - c : ℕ) : ℝ)
                    * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2))
        ≤ 2 *
          (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
                * (B * Real.sqrt (4 * (ℓ : ℝ))
                    * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
            + 2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
                * (B * Real.sqrt (4 * (ℓ : ℝ))
                    * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hL hR) (by norm_num)
    _ = 4 * (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
          * (B * Real.sqrt (4 * (ℓ : ℝ))
              * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) := by ring

/-- **The localized form** (as in `lem:ags-local-step`): every recursive target carries its explicit
strict two-sided containment `MmM ⊊ MsM`. -/
theorem hasDual_markedAt_strict (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {B : ℝ} (hB : 0 ≤ B)
    (hrec : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (fun x : Fin n → σ => markedAt letter a p q b ℓ c x)
      (4 * (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
        * (B * Real.sqrt (4 * (ℓ : ℝ))
            * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2))) :=
  hasDual_markedAt_above letter hG hpq hc hB
    (fun s hs len hlen => hrec s (lt_of_lt_of_le (twoIdeal_lt_of_split_left hG hpq)
      (twoIdeal_subset_of_mem_leftAbove hs)) len hlen)
    (fun s hs len hlen => hrec s (lt_of_lt_of_le (twoIdeal_lt_of_split_right hG hpq)
      (twoIdeal_subset_of_mem_rightAbove hs)) len hlen)

/-- One marked cut, priced, in the numeric `jLevel` form: a specialization of
the localized one. -/
theorem hasDual_markedAt (letter : σ → M) {m a r b p q : M}
    (hG : (a, r, b) ∈ setG m) (hpq : p * q = r) {n ℓ c : ℕ} (hc : c ≤ n)
    {B : ℝ} (hB : 0 ≤ B)
    (hrec : ∀ s : M, jLevel s < jLevel m → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (fun x : Fin n → σ => markedAt letter a p q b ℓ c x)
      (4 * (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
        * (B * Real.sqrt (4 * (ℓ : ℝ))
            * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2))) :=
  hasDual_markedAt_strict letter hG hpq hc hB fun s hs => hrec s (jLevel_lt_of_ssubset hs)


/-! ### The three searches -/

/-- The cost of one marked cut at scale `ℓ`. -/
noncomputable def cutCost (n : ℕ) (M : Type) [Fintype M] (B : ℝ) (ℓ : ℕ) : ℝ :=
  8 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
    * (B * Real.sqrt (4 * (ℓ : ℝ))
        * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)

lemma cutCost_nonneg (n : ℕ) (M : Type) [Fintype M] {B : ℝ} (hB : 0 ≤ B)
    (ℓ : ℕ) : 0 ≤ cutCost n M B ℓ := by
  rw [cutCost]; positivity

/-- **The cost of the infix search.**  Reading the factors: the binary-search
depth of each window; the cancellation `√(4ℓ)·√|grid| ≤ √(68 n)` of the window
width against the number of cuts; the square-root search over the `≤ |M|²` split
pairs; and the square-root search over the `≤ log₂ n` scales. -/
noncomputable def infixCost (n : ℕ) (M : Type) [Fintype M] (B : ℝ) : ℝ :=
  8 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
      * (24 * (B * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
          * Real.sqrt (68 * (n : ℝ)) + 2 * Real.sqrt ((n : ℝ) + 2)))
      * (24 * Real.sqrt ((Fintype.card M : ℝ) ^ 2 + 1))
    * (24 * Real.sqrt ((Nat.log 2 n : ℝ) + 1))

/-- **Infix search (`lem:infix`).**  The forbidden-infix test for one triple `(a,r,b) ∈ G m`,
priced in recursive equality tests that are all run strictly below `m`. -/
theorem hasDual_badInfixFor_of_markedAt (letter : σ → M) {a r b : M}
    {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hmark : ∀ p q : M, p * q = r → ∀ ℓ c : ℕ, c ≤ n →
      HasDual (fun x : Fin n → σ => markedAt letter a p q b ℓ c x)
        (4 * (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
          * (B * Real.sqrt (4 * (ℓ : ℝ))
              * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)))) :
    HasDual (fun x : Fin n → σ => badInfixFor letter a r b x)
      (infixCost n M B) := by
  classical
  -- over split pairs
  have h1 : ∀ ℓ c : ℕ, c ≤ n →
      HasDual (fun x : Fin n → σ => (splitPairs r).sup fun pq =>
          markedAt letter a pq.1 pq.2 b ℓ c x)
        (cutCost n M B ℓ
          * (24 * Real.sqrt (((splitPairs r).card : ℝ) + 1))) := by
    intro ℓ c hc
    refine HasDual.finsetSup _ (cutCost_nonneg n M hB ℓ) fun pq hpq => ?_
    exact (hmark pq.1 pq.2 (Finset.mem_filter.1 hpq).2 ℓ c hc).mono
      (le_of_eq (by rw [cutCost]; ring))
  -- over grid cuts: this is where the scale cancels
  have h2 : ∀ ℓ ∈ scales n,
      HasDual (fun x : Fin n → σ => (cutGrid n ℓ).sup fun c =>
          (splitPairs r).sup fun pq => markedAt letter a pq.1 pq.2 b ℓ c x)
        (8 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
            * (24 * (B * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
                * Real.sqrt (68 * (n : ℝ)) + 2 * Real.sqrt ((n : ℝ) + 2)))
            * (24 * Real.sqrt ((Fintype.card M : ℝ) ^ 2 + 1))) := by
    intro ℓ hℓ
    have h2ℓ := two_le_of_mem_scales hℓ
    have hℓn := le_of_mem_scales hℓ
    refine (HasDual.finsetSup (cutGrid n ℓ)
      (mul_nonneg (cutCost_nonneg n M hB ℓ) (by positivity))
      fun c hc => h1 ℓ c (le_of_mem_cutGrid hc)).mono ?_
    have hA : (B * Real.sqrt (4 * (ℓ : ℝ))
          * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
        * (24 * Real.sqrt (((cutGrid n ℓ).card : ℝ) + 1))
        ≤ 24 * (B * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
            * Real.sqrt (68 * (n : ℝ)) + 2 * Real.sqrt ((n : ℝ) + 2)) := by
      have hc1 := sqrt_win_mul_grid_le h2ℓ hℓn
      have hc2 := sqrt_grid_le n ℓ
      have hBS : (0 : ℝ) ≤ B * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) := by
        positivity
      have key := mul_le_mul_of_nonneg_left hc1 hBS
      nlinarith [key, hc2]
    have hB2 : Real.sqrt (((splitPairs r).card : ℝ) + 1)
        ≤ Real.sqrt ((Fintype.card M : ℝ) ^ 2 + 1) := by
      refine Real.sqrt_le_sqrt ?_
      have : ((splitPairs r).card : ℝ) ≤ (Fintype.card M : ℝ) ^ 2 := by
        exact_mod_cast card_splitPairs_le r
      linarith
    calc cutCost n M B ℓ * (24 * Real.sqrt (((splitPairs r).card : ℝ) + 1))
            * (24 * Real.sqrt (((cutGrid n ℓ).card : ℝ) + 1))
        = 8 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
            * ((B * Real.sqrt (4 * (ℓ : ℝ))
                  * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
                * (24 * Real.sqrt (((cutGrid n ℓ).card : ℝ) + 1)))
            * (24 * Real.sqrt (((splitPairs r).card : ℝ) + 1)) := by
          rw [cutCost]; ring
      _ ≤ 8 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
            * (24 * (B * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
                * Real.sqrt (68 * (n : ℝ)) + 2 * Real.sqrt ((n : ℝ) + 2)))
            * (24 * Real.sqrt ((Fintype.card M : ℝ) ^ 2 + 1)) := by
          have hnn : (0 : ℝ) ≤ 8 * ((Nat.clog 2 (n + 1) : ℝ) + 2) := by positivity
          refine mul_le_mul (mul_le_mul_of_nonneg_left hA hnn) ?_
            (by positivity) (by positivity)
          linarith
  -- over scales
  refine ((HasDual.finsetSup (scales n) (by positivity) h2).ofEq
    fun x => (badInfixFor_sup letter a r b x).symm).mono ?_
  rw [infixCost]
  have hsc : Real.sqrt (((scales n).card : ℝ) + 1)
      ≤ Real.sqrt ((Nat.log 2 n : ℝ) + 1) := by
    refine Real.sqrt_le_sqrt ?_
    have : ((scales n).card : ℝ) ≤ (Nat.log 2 n : ℝ) := by
      exact_mod_cast card_scales_le n
    linarith
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **Infix search (`lem:infix`), localized**: the recursive equality tests are run only at
values `s` with `MmM ⊊ MsM`, and each carries that proof. -/
theorem hasDual_badInfixFor_strict (letter : σ → M) {m a r b : M}
    (hG : (a, r, b) ∈ setG m) {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hrec : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (fun x : Fin n → σ => badInfixFor letter a r b x)
      (infixCost n M B) :=
  hasDual_badInfixFor_of_markedAt letter hB fun _ _ hpq _ _ hc =>
    hasDual_markedAt_strict letter hG hpq hc hB hrec

/-- **Infix search (`lem:infix`)**, in the numeric `jLevel` form: a specialization of the
localized one. -/
theorem hasDual_badInfixFor (letter : σ → M) {m a r b : M}
    (hG : (a, r, b) ∈ setG m) {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hrec : ∀ s : M, jLevel s < jLevel m → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (fun x : Fin n → σ => badInfixFor letter a r b x)
      (infixCost n M B) :=
  hasDual_badInfixFor_strict letter hG hB fun s hs => hrec s (jLevel_lt_of_ssubset hs)

end Assembly

end MonoidProduct
