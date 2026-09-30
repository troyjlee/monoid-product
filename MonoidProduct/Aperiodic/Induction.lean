import MonoidProduct.Aperiodic.InfixCost
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The main induction

The induction behind `thm:main-ags`.  The decomposition theorem (`thm:decomp`)
rewrites the target test `eqProd m` as a conjunction of four conditions, and
the prefix and infix searches (`lem:prefix`, `lem:infix`) price each of them
in equality tests run *strictly below* `m` in the `J`-order.  That is a
recurrence, and this file solves it.

The four conditions become four `Finset.sup`s — over `E m`, `F m`, the letter
positions, and `G m` — and `HasDual.combine'` assembles them.  Every recursive
call is at a level `< jLevel m`, so a strong induction on `jLevel m` closes the
loop, with one multiplier `agsStep` charged per level.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The four conditions as Booleans -/

/-- `(U)`: some pair of `E m` has its prefix event. -/
noncomputable def uTest (letter : σ → M) (m : M) {n : ℕ} (x : Fin n → σ) : Bool :=
  (setE m).sup fun p => prefixEvent letter p.1 p.2 x

/-- `(V)`: some pair of `F m` has its suffix event. -/
noncomputable def vTest (letter : σ → M) (m : M) {n : ℕ} (x : Fin n → σ) : Bool :=
  (setF m).sup fun p => suffixEvent letter p.1 p.2 x

/-- The negation of `(C)`: some letter is forbidden. -/
noncomputable def cTest (letter : σ → M) (m : M) {n : ℕ} (x : Fin n → σ) : Bool :=
  (Finset.univ : Finset (Fin n)).sup fun i => decide (letter (x i) ∈ setC m)

/-- The negation of `(W)`: some triple of `G m` has its forbidden infix. -/
noncomputable def wTest (letter : σ → M) (m : M) {n : ℕ} (x : Fin n → σ) : Bool :=
  (setG m).sup fun t => badInfixFor letter t.1 t.2.1 t.2.2 x

lemma uTest_eq_true {letter : σ → M} {m : M} {n : ℕ} {x : Fin n → σ} :
    uTest letter m x = true ↔ ∃ p ∈ setE m, prefixEvent letter p.1 p.2 x = true :=
  sup_bool_eq_true _ _

lemma vTest_eq_true {letter : σ → M} {m : M} {n : ℕ} {x : Fin n → σ} :
    vTest letter m x = true ↔ ∃ p ∈ setF m, suffixEvent letter p.1 p.2 x = true :=
  sup_bool_eq_true _ _

lemma cTest_eq_true {letter : σ → M} {m : M} {n : ℕ} {x : Fin n → σ} :
    cTest letter m x = true ↔ ∃ i : Fin n, letter (x i) ∈ setC m := by
  rw [cTest, sup_bool_eq_true]
  simp

lemma wTest_eq_true {letter : σ → M} {m : M} {n : ℕ} {x : Fin n → σ} :
    wTest letter m x = true
      ↔ ∃ t ∈ setG m, badInfixFor letter t.1 t.2.1 t.2.2 x = true :=
  sup_bool_eq_true _ _

end

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **`thm:decomp` in `Bool`.**  This is the equation the induction rewrites
along. -/
theorem eqProd_eq_tests (letter : σ → M) {m : M} (hm : m ≠ 1) {n : ℕ}
    (x : Fin n → σ) :
    eqProd letter m x
      = (uTest letter m x && vTest letter m x
          && !(cTest letter m x) && !(wTest letter m x)) := by
  rw [Bool.eq_iff_iff, eqProd_eq_true, wordProd,
    orderedProd_eq_iff hm (fun i => letter (x i))]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  rw [uEvent_iff, vEvent_iff, badInfix_iff]
  constructor
  · rintro ⟨hu, hv, hc, hw⟩
    refine ⟨⟨⟨uTest_eq_true.2 hu, vTest_eq_true.2 hv⟩, ?_⟩, ?_⟩
    · rw [← Bool.not_eq_true]
      exact fun h => hc (cTest_eq_true.1 h)
    · rw [← Bool.not_eq_true]
      exact fun h => hw (wTest_eq_true.1 h)
  · rintro ⟨⟨⟨hu, hv⟩, hc⟩, hw⟩
    refine ⟨uTest_eq_true.1 hu, vTest_eq_true.1 hv, ?_, ?_⟩
    · rw [← Bool.not_eq_true] at hc
      exact fun h => hc (cTest_eq_true.2 h)
    · rw [← Bool.not_eq_true] at hw
      exact fun h => hw (wTest_eq_true.2 h)

/-! ## The strict inclusions the searches need -/

lemma rightIdeal_lt_of_mem_setE {m r a : M} (h : (r, a) ∈ setE m) :
    rightIdeal (r * a) ⊂ rightIdeal r := by
  obtain ⟨heq, hne⟩ := mem_setE.1 h
  exact lt_of_le_of_ne (rightIdeal_mul_subset r a) (by rw [heq]; exact fun hc => hne hc.symm)

lemma leftIdeal_lt_of_mem_setF {m a r : M} (h : (a, r) ∈ setF m) :
    leftIdeal (a * r) ⊂ leftIdeal r := by
  obtain ⟨heq, hne⟩ := mem_setF.1 h
  exact lt_of_le_of_ne (leftIdeal_mul_subset a r) (by rw [heq]; exact fun hc => hne hc.symm)


/-! ## The cost of each condition -/

/-- One bound covering all four conditions: the `(U)`/`(V)` shape with the
worst-case `|M|²` index set, the `(C)` scan, and the `(W)` infix search with the
worst-case `|M|³` index set. -/
noncomputable def stepBound (n : ℕ) (M : Type) [Fintype M] (B : ℝ) : ℝ :=
  2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
      * (B * Real.sqrt (n : ℝ) * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
      * (24 * Real.sqrt ((Fintype.card M : ℝ) ^ 2 + 1))
    + 2 * (24 * Real.sqrt ((n : ℝ) + 1))
    + infixCost n M B * (24 * Real.sqrt ((Fintype.card M : ℝ) ^ 3 + 1))

lemma stepBound_nonneg (n : ℕ) (M : Type) [Fintype M] {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ stepBound n M B := by rw [stepBound, infixCost]; positivity

/-- `(C)` is a square-root search over the positions. -/
theorem hasDual_cTest (letter : σ → M) (m : M) {n : ℕ} :
    HasDual (fun x : Fin n → σ => cTest letter m x)
      (2 * (24 * Real.sqrt (((Finset.univ : Finset (Fin n)).card : ℝ) + 1))) :=
  HasDual.finsetSup (ι := Fin n) (σ := σ) (A := Bool) Finset.univ
    (by norm_num) fun i _ =>
      hasDual_ofCoord (σ := σ) i fun cc => decide (letter cc ∈ setC m)

/-- `(U)` is a square-root search over `E m` of prefix searches, **localized**
(`lem:ags-local-step`): each recursive target `s` carries `MmM ⊊ MsM`, obtained from
`MmM ⊊ MrM` at the pair `(r, a) ∈ E m` and `MrM ⊆ MsM` for `s ∈ rightAbove r`. -/
theorem hasDual_uTest_strict (letter : σ → M) {m : M} {n : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hIH : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => uTest letter m x)
      (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
          * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
        * (24 * Real.sqrt (((setE m).card : ℝ) + 1))) := by
  refine HasDual.finsetSup _ (by positivity) fun p hp => ?_
  obtain ⟨r, a⟩ := p
  exact hasDual_prefixEvent letter (rightIdeal_lt_of_mem_setE hp) hQ
    fun s hs len hlen => hIH s (lt_of_lt_of_le (twoIdeal_lt_of_mem_setE hp)
      (twoIdeal_subset_of_mem_rightAbove hs)) len hlen

/-- `(U)` in the numeric `jLevel` form. -/
theorem hasDual_uTest (letter : σ → M) {m : M} {n : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hIH : ∀ s : M, jLevel s < jLevel m → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => uTest letter m x)
      (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
          * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
        * (24 * Real.sqrt (((setE m).card : ℝ) + 1))) :=
  hasDual_uTest_strict letter hQ fun s hs => hIH s (jLevel_lt_of_ssubset hs)

/-- `(V)` is the mirror, **localized** (`lem:ags-local-step`). -/
theorem hasDual_vTest_strict (letter : σ → M) {m : M} {n : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hIH : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => vTest letter m x)
      (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
          * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
        * (24 * Real.sqrt (((setF m).card : ℝ) + 1))) := by
  refine HasDual.finsetSup _ (by positivity) fun p hp => ?_
  obtain ⟨a, r⟩ := p
  exact hasDual_suffixEvent letter (leftIdeal_lt_of_mem_setF hp) hQ
    fun s hs len hlen => hIH s (lt_of_lt_of_le (twoIdeal_lt_of_mem_setF hp)
      (twoIdeal_subset_of_mem_leftAbove hs)) len hlen

/-- `(V)` in the numeric `jLevel` form. -/
theorem hasDual_vTest (letter : σ → M) {m : M} {n : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hIH : ∀ s : M, jLevel s < jLevel m → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => vTest letter m x)
      (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
          * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
        * (24 * Real.sqrt (((setF m).card : ℝ) + 1))) :=
  hasDual_vTest_strict letter hQ fun s hs => hIH s (jLevel_lt_of_ssubset hs)

/-- `(W)` is a square-root search over `G m` of infix searches, **localized**
(`lem:ags-local-step`). -/
theorem hasDual_wTest_strict (letter : σ → M) {m : M} {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hIH : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (fun x : Fin n → σ => wTest letter m x)
      (infixCost n M B * (24 * Real.sqrt (((setG m).card : ℝ) + 1))) := by
  refine HasDual.finsetSup _ (by rw [infixCost]; positivity) fun t ht => ?_
  obtain ⟨a, r, b⟩ := t
  exact hasDual_badInfixFor_strict letter ht hB hIH

/-- `(W)` in the numeric `jLevel` form. -/
theorem hasDual_wTest (letter : σ → M) {m : M} {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hIH : ∀ s : M, jLevel s < jLevel m → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (fun x : Fin n → σ => wTest letter m x)
      (infixCost n M B * (24 * Real.sqrt (((setG m).card : ℝ) + 1))) :=
  hasDual_wTest_strict letter hB fun s hs => hIH s (jLevel_lt_of_ssubset hs)

/-- **The inductive step, localized** (`lem:ags-local-step`).  The four conditions, each bounded
by `stepBound` and assembled by three binary `HasDual.combine'`s.  The
recursion is asked only for the **strict two-sided parents** of `m`: every
recursive `(U)`, `(V)` and `(W)` target carries its own proof of
`MmM ⊊ MsM`.  This is strictly stronger than the numeric `jLevel` form below —
a smaller `J`-level does not imply strict containment — and it is the form the
cube-root peel consumes, where the recursion runs inside a fixed apex rather
than down a level counter. -/
theorem hasDual_eqProd_step_strict (letter : σ → M) {m : M} (hm : m ≠ 1) {n : ℕ}
    {B : ℝ} (hB : 0 ≤ B)
    (hIH : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (eqProd (n := n) letter m) (16 * stepBound n M B) := by
  classical
  have hQ : (0 : ℝ) ≤ B * Real.sqrt (n : ℝ) := by positivity
  have hSB : (0 : ℝ) ≤ stepBound n M B := stepBound_nonneg n M hB
  have hp1 : (0 : ℝ) ≤ 2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
      * (B * Real.sqrt (n : ℝ) * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2) := by
    positivity
  have hp1' : (0 : ℝ) ≤ 2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
      * (B * Real.sqrt (n : ℝ) * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)
      * (24 * Real.sqrt ((Fintype.card M : ℝ) ^ 2 + 1)) := by positivity
  have hp2 : (0 : ℝ) ≤ 2 * (24 * Real.sqrt ((n : ℝ) + 1)) := by positivity
  have hp3 : (0 : ℝ) ≤ infixCost n M B
      * (24 * Real.sqrt ((Fintype.card M : ℝ) ^ 3 + 1)) := by
    rw [infixCost]; positivity
  have hIH' : ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (n : ℝ)) := by
    intro s hs len hlen
    refine (hIH s hs len hlen).mono ?_
    have h : Real.sqrt (len : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hlen)
    nlinarith [Real.sqrt_nonneg (len : ℝ)]
  -- the four, all bounded by `stepBound`
  have hU : HasDual (fun x : Fin n → σ => uTest letter m x) (stepBound n M B) := by
    refine (hasDual_uTest_strict letter hQ hIH').mono ?_
    rw [stepBound]
    have h1 : (24 : ℝ) * Real.sqrt (((setE m).card : ℝ) + 1)
        ≤ 24 * Real.sqrt ((Fintype.card M : ℝ) ^ 2 + 1) := by
      have : ((setE m).card : ℝ) ≤ (Fintype.card M : ℝ) ^ 2 := by
        exact_mod_cast card_setE_le m
      have := Real.sqrt_le_sqrt (show ((setE m).card : ℝ) + 1
        ≤ (Fintype.card M : ℝ) ^ 2 + 1 by linarith)
      linarith
    have := mul_le_mul_of_nonneg_left h1 hp1
    linarith
  have hV : HasDual (fun x : Fin n → σ => vTest letter m x) (stepBound n M B) := by
    refine (hasDual_vTest_strict letter hQ hIH').mono ?_
    rw [stepBound]
    have h1 : (24 : ℝ) * Real.sqrt (((setF m).card : ℝ) + 1)
        ≤ 24 * Real.sqrt ((Fintype.card M : ℝ) ^ 2 + 1) := by
      have : ((setF m).card : ℝ) ≤ (Fintype.card M : ℝ) ^ 2 := by
        exact_mod_cast card_setF_le m
      have := Real.sqrt_le_sqrt (show ((setF m).card : ℝ) + 1
        ≤ (Fintype.card M : ℝ) ^ 2 + 1 by linarith)
      linarith
    have := mul_le_mul_of_nonneg_left h1 hp1
    linarith
  have hC : HasDual (fun x : Fin n → σ => cTest letter m x) (stepBound n M B) := by
    refine (hasDual_cTest letter m).mono ?_
    rw [stepBound, Finset.card_univ, Fintype.card_fin]
    linarith
  have hW : HasDual (fun x : Fin n → σ => wTest letter m x) (stepBound n M B) := by
    refine (hasDual_wTest_strict letter hB hIH).mono ?_
    rw [stepBound]
    have h1 : (24 : ℝ) * Real.sqrt (((setG m).card : ℝ) + 1)
        ≤ 24 * Real.sqrt ((Fintype.card M : ℝ) ^ 3 + 1) := by
      have : ((setG m).card : ℝ) ≤ (Fintype.card M : ℝ) ^ 3 := by
        exact_mod_cast card_setG_le m
      have := Real.sqrt_le_sqrt (show ((setG m).card : ℝ) + 1
        ≤ (Fintype.card M : ℝ) ^ 3 + 1 by linarith)
      linarith
    have hic : (0 : ℝ) ≤ infixCost n M B := by rw [infixCost]; positivity
    have := mul_le_mul_of_nonneg_left h1 hic
    linarith
  -- `(U) ∧ (V)`
  have hUV : HasDual (fun x : Fin n → σ => uTest letter m x && vTest letter m x)
      (4 * stepBound n M B) := by
    have hcomb := HasDual.combine' (ι := Fin n) (σ := σ) (Pi := Bool) (V := Bool)
      (O' := Bool) (fun f => f true && f false)
      (g := fun t x => if t then uTest letter m x else vTest letter m x)
      (c := fun _ => stepBound n M B) (fun _ => hSB)
      (fun t => by
        cases t with
        | false => simpa using hV
        | true => simpa using hU)
    refine (hcomb.ofEq fun x => rfl).mono (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_bool]
    ring
  -- `¬(C) ∧ ¬(W)`
  have hCW : HasDual (fun x : Fin n → σ =>
      !(cTest letter m x) && !(wTest letter m x)) (4 * stepBound n M B) := by
    have hcomb := HasDual.combine' (ι := Fin n) (σ := σ) (Pi := Bool) (V := Bool)
      (O' := Bool) (fun f => !(f true) && !(f false))
      (g := fun t x => if t then cTest letter m x else wTest letter m x)
      (c := fun _ => stepBound n M B) (fun _ => hSB)
      (fun t => by
        cases t with
        | false => simpa using hW
        | true => simpa using hC)
    refine (hcomb.ofEq fun x => rfl).mono (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_bool]
    ring
  -- and the two halves
  have hcomb := HasDual.combine' (ι := Fin n) (σ := σ) (Pi := Bool) (V := Bool)
    (O' := Bool) (fun f => f true && f false)
    (g := fun t x => if t then uTest letter m x && vTest letter m x
      else !(cTest letter m x) && !(wTest letter m x))
    (c := fun _ => 4 * stepBound n M B) (fun _ => by linarith)
    (fun t => by
      cases t with
      | false => simpa using hCW
      | true => simpa using hUV)
  refine (hcomb.ofEq fun x => ?_).mono (le_of_eq ?_)
  · simp only []
    rw [eqProd_eq_tests letter hm x]
    simp [Bool.and_assoc]
  · rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_bool]
    ring

/-- **The inductive step**, in the numeric `jLevel` form: the specialization of
`hasDual_eqProd_step_strict` along `jLevel_lt_of_ssubset`.  This is the
statement the global AGS recurrence below consumes, unchanged. -/
theorem hasDual_eqProd_step (letter : σ → M) {m : M} (hm : m ≠ 1) {n : ℕ}
    {B : ℝ} (hB : 0 ≤ B)
    (hIH : ∀ s : M, jLevel s < jLevel m → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (eqProd (n := n) letter m) (16 * stepBound n M B) :=
  hasDual_eqProd_step_strict letter hm hB fun s hs => hIH s (jLevel_lt_of_ssubset hs)


/-! ## Solving the recurrence -/

/-- The multiplier the recurrence gains per `J`-level.  Generous by design:
the aim is a stable exact theorem, not an optimised constant. -/
noncomputable def agsStep (N : ℕ) (M : Type) [Fintype M] : ℝ :=
  2 ^ 40 * ((Fintype.card M : ℝ) + 1) ^ 5 * ((Nat.clog 2 (N + 1) : ℝ) + 2) ^ 2

lemma one_le_agsStep (N : ℕ) (M : Type) [Fintype M] : 1 ≤ agsStep N M := by
  rw [agsStep]
  have h1 : (1 : ℝ) ≤ ((Fintype.card M : ℝ) + 1) ^ 5 := by
    refine one_le_pow₀ ?_
    have : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 : (1 : ℝ) ≤ ((Nat.clog 2 (N + 1) : ℝ) + 2) ^ 2 := by
    refine one_le_pow₀ ?_
    have : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := Nat.cast_nonneg _
    linarith
  nlinarith

/-! ### The recurrence closes

The inequality below is pure real arithmetic, and it is stated with every square
root replaced by an opaque variable bounded above.  That is deliberate: with the
roots left in place `nlinarith` has to reason about degree-six products of
`Real.sqrt` applications and times out, whereas here every step is a single
`mul_le_mul` between named quantities. -/

set_option maxHeartbeats 1000000 in
private lemma step_arith {K L R B Lam s1 s2 s3 s4 s5 s6 s7 : ℝ}
    (hK : 2 ≤ K) (hL : 2 ≤ L) (hR : 1 ≤ R) (hB : 1 ≤ B)
    (hLam0 : 0 ≤ Lam) (hLam : Lam ≤ L)
    (h1 : 0 ≤ s1) (h1' : s1 ≤ K) (h2 : 0 ≤ s2) (h2' : s2 ≤ K)
    (h3 : 0 ≤ s3) (h3' : s3 ≤ K ^ 2) (h4 : 0 ≤ s4) (h4' : s4 ≤ 2 * R)
    (h5 : 0 ≤ s5) (h5' : s5 ≤ 9 * R) (h6 : 0 ≤ s6) (h6' : s6 ≤ 2 * R)
    (h7 : 0 ≤ s7) (h7' : s7 ≤ L) :
    16 * (2 * Lam * (B * R * (24 * s1) + 2) * (24 * s2) + 2 * (24 * s4)
        + 8 * Lam * (24 * (B * (24 * s1) * s5 + 2 * s6)) * (24 * s2) * (24 * s7)
          * (24 * s3))
      ≤ B * (2 ^ 40 * K ^ 5 * L ^ 2) * R := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hP : (1 : ℝ) ≤ B * R := by nlinarith
  have hP0 : (0 : ℝ) ≤ B * R := by linarith
  -- the `(U)`/`(V)` term
  have hmidA : B * R * (24 * s1) + 2 ≤ 26 * K * (B * R) := by
    nlinarith [mul_le_mul_of_nonneg_left h1'
      (show (0 : ℝ) ≤ 24 * (B * R) by linarith)]
  have hmidA0 : (0 : ℝ) ≤ B * R * (24 * s1) + 2 := by nlinarith
  have hAnn : (0 : ℝ) ≤ 2 * L * (26 * K * (B * R)) := by nlinarith
  have hA : 2 * Lam * (B * R * (24 * s1) + 2) * (24 * s2)
      ≤ 1248 * (L * K ^ 2 * (B * R)) := by
    calc 2 * Lam * (B * R * (24 * s1) + 2) * (24 * s2)
        ≤ 2 * L * (26 * K * (B * R)) * (24 * K) :=
          mul_le_mul (mul_le_mul (by linarith) hmidA hmidA0 (by linarith))
            (by linarith) (by linarith) hAnn
      _ = 1248 * (L * K ^ 2 * (B * R)) := by ring
  -- the `(C)` term
  have hBt : 2 * (24 * s4) ≤ 96 * (B * R) := by nlinarith
  -- the `(W)` term
  have hmidC : 24 * (B * (24 * s1) * s5 + 2 * s6) ≤ 5280 * (K * (B * R)) := by
    have e1 : B * (24 * s1) * s5 ≤ 216 * (K * (B * R)) := by
      nlinarith [mul_le_mul_of_nonneg_left h1'
          (show (0 : ℝ) ≤ 24 * B * s5 by nlinarith),
        mul_le_mul_of_nonneg_left h5'
          (show (0 : ℝ) ≤ 24 * B * K by nlinarith)]
    have e2 : 2 * s6 ≤ 4 * (K * (B * R)) := by nlinarith
    linarith
  have hmidC0 : (0 : ℝ) ≤ 24 * (B * (24 * s1) * s5 + 2 * s6) := by
    have hprod : (0 : ℝ) ≤ B * (24 * s1) * s5 :=
      mul_nonneg (mul_nonneg hB0 (by linarith)) h5
    linarith
  have hn1 : (0 : ℝ) ≤ 8 * L * (5280 * (K * (B * R))) := by nlinarith
  have hn2 : (0 : ℝ) ≤ 8 * L * (5280 * (K * (B * R))) * (24 * K) := by nlinarith
  have hIC : 8 * Lam * (24 * (B * (24 * s1) * s5 + 2 * s6)) * (24 * s2) * (24 * s7)
      ≤ 24330240 * (L ^ 2 * K ^ 2 * (B * R)) := by
    calc 8 * Lam * (24 * (B * (24 * s1) * s5 + 2 * s6)) * (24 * s2) * (24 * s7)
        ≤ 8 * L * (5280 * (K * (B * R))) * (24 * K) * (24 * L) :=
          mul_le_mul (mul_le_mul
            (mul_le_mul (by linarith) hmidC hmidC0 (by linarith))
            (by linarith) (by linarith) hn1)
            (by linarith) (by linarith) hn2
      _ = 24330240 * (L ^ 2 * K ^ 2 * (B * R)) := by ring
  have hICnn : (0 : ℝ) ≤ 24330240 * (L ^ 2 * K ^ 2 * (B * R)) := by nlinarith
  have hC : 8 * Lam * (24 * (B * (24 * s1) * s5 + 2 * s6)) * (24 * s2) * (24 * s7)
        * (24 * s3)
      ≤ 583925760 * (L ^ 2 * K ^ 4 * (B * R)) := by
    calc 8 * Lam * (24 * (B * (24 * s1) * s5 + 2 * s6)) * (24 * s2) * (24 * s7)
          * (24 * s3)
        ≤ 24330240 * (L ^ 2 * K ^ 2 * (B * R)) * (24 * K ^ 2) :=
          mul_le_mul hIC (by linarith) (by linarith) hICnn
      _ = 583925760 * (L ^ 2 * K ^ 4 * (B * R)) := by ring
  -- collect
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hKK : K ^ 2 ≤ K ^ 4 := by
    have h : (0 : ℝ) ≤ K ^ 2 * (K ^ 2 - 1) :=
      mul_nonneg (sq_nonneg K) (by nlinarith)
    nlinarith [h]
  have hLK2 : L * K ^ 2 ≤ L ^ 2 * K ^ 4 :=
    mul_le_mul hLL hKK (by positivity) (by positivity)
  have hLK : L * K ^ 2 * (B * R) ≤ L ^ 2 * K ^ 4 * (B * R) :=
    mul_le_mul_of_nonneg_right hLK2 hP0
  have hone : B * R ≤ L ^ 2 * K ^ 4 * (B * R) := by
    have h1 : (1 : ℝ) ≤ L ^ 2 * K ^ 4 := by nlinarith
    nlinarith
  have htot : 2 * Lam * (B * R * (24 * s1) + 2) * (24 * s2) + 2 * (24 * s4)
        + 8 * Lam * (24 * (B * (24 * s1) * s5 + 2 * s6)) * (24 * s2) * (24 * s7)
          * (24 * s3)
      ≤ 583927104 * (L ^ 2 * K ^ 4 * (B * R)) := by linarith
  have hnn : (0 : ℝ) ≤ K ^ 4 * L ^ 2 * (B * R) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) hP0
  have hbase : (9342833664 : ℝ) ≤ 2 ^ 40 * K := by nlinarith
  have hfin := mul_le_mul_of_nonneg_right hbase hnn
  nlinarith [htot, hfin]

/-- **The recurrence closes**: one `J`-level costs `agsStep` times the level
below. -/
lemma stepBound_le (M : Type) [Fintype M] [Nonempty M] {n N : ℕ} (hn1 : 1 ≤ n)
    (hnN : n ≤ N) {B : ℝ} (hB : 1 ≤ B) :
    16 * stepBound n M B ≤ B * agsStep N M * Real.sqrt (n : ℝ) := by
  have hcard : (1 : ℝ) ≤ (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hR : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt hn
    rwa [Real.sqrt_one] at h
  have hRsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have hsq_le : ∀ a b : ℝ, 0 ≤ b → a ≤ b ^ 2 → Real.sqrt a ≤ b := by
    intro a b hb hab
    have h := Real.sqrt_le_sqrt hab
    rwa [Real.sqrt_sq hb] at h
  rw [stepBound, infixCost, agsStep]
  refine step_arith (K := (Fintype.card M : ℝ) + 1)
    (L := (Nat.clog 2 (N + 1) : ℝ) + 2) (R := Real.sqrt (n : ℝ)) (B := B)
    (Lam := (Nat.clog 2 (n + 1) : ℝ) + 2) (by linarith) ?_ hR hB ?_ ?_
    (Real.sqrt_nonneg _) ?_ (Real.sqrt_nonneg _) ?_ (Real.sqrt_nonneg _) ?_
    (Real.sqrt_nonneg _) ?_ (Real.sqrt_nonneg _) ?_ (Real.sqrt_nonneg _) ?_
    (Real.sqrt_nonneg _) ?_
  · have : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := Nat.cast_nonneg _
    linarith
  · have : (0 : ℝ) ≤ (Nat.clog 2 (n + 1) : ℝ) := Nat.cast_nonneg _
    linarith
  · have h : Nat.clog 2 (n + 1) ≤ Nat.clog 2 (N + 1) :=
      Nat.clog_mono_right 2 (by omega)
    have : (Nat.clog 2 (n + 1) : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := by
      exact_mod_cast h
    linarith
  · exact hsq_le _ _ (by linarith) (by nlinarith)
  · exact hsq_le _ _ (by linarith) (by nlinarith)
  · exact hsq_le _ _ (by nlinarith) (by nlinarith)
  · exact hsq_le _ _ (by linarith) (by nlinarith)
  · exact hsq_le _ _ (by linarith) (by nlinarith)
  · exact hsq_le _ _ (by linarith) (by nlinarith)
  · refine hsq_le _ _ (by
      have : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := Nat.cast_nonneg _
      linarith) ?_
    have h : Nat.log 2 n ≤ Nat.clog 2 (N + 1) :=
      le_trans (Nat.log_le_clog 2 n) (Nat.clog_mono_right 2 (by omega))
    have hc : (Nat.log 2 n : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := by exact_mod_cast h
    have h0 : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := Nat.cast_nonneg _
    nlinarith


/-! ## The induction -/

/-- The base case: the ordered product is `1` exactly when every letter is, a
single square-root search over the positions. -/
theorem hasDual_eqProd_unit (letter : σ → M) {n : ℕ} :
    HasDual (eqProd (n := n) letter 1)
      (2 * (24 * Real.sqrt (((Finset.univ : Finset (Fin n)).card : ℝ) + 1))) := by
  classical
  have hsup := HasDual.finsetSup (ι := Fin n) (σ := σ) (A := Bool)
    (Finset.univ : Finset (Fin n))
    (g := fun i x => decide (letter (x i) ≠ 1)) (by norm_num)
    (fun i _ => hasDual_ofCoord (σ := σ) i fun cc => decide (letter cc ≠ 1))
  have hneg : HasDual (fun x : Fin n → σ =>
      !((Finset.univ : Finset (Fin n)).sup fun i => decide (letter (x i) ≠ 1)))
      (2 * (24 * Real.sqrt (((Finset.univ : Finset (Fin n)).card : ℝ) + 1))) :=
    hsup.ofKer fun u v => by simp
  refine hneg.ofEq fun x => ?_
  rw [Bool.eq_iff_iff, eqProd_eq_true, wordProd, orderedProd_eq_one_iff]
  constructor
  · intro h i
    by_contra hc
    have hs : ((Finset.univ : Finset (Fin n)).sup
        fun i => decide (letter (x i) ≠ 1)) = true := by
      rw [sup_bool_eq_true]
      exact ⟨i, Finset.mem_univ i, by simpa using hc⟩
    rw [hs] at h
    exact absurd h (by simp)
  · intro h
    have hs : ((Finset.univ : Finset (Fin n)).sup
        fun i => decide (letter (x i) ≠ 1)) = false := by
      by_contra hc
      rw [Bool.not_eq_false, sup_bool_eq_true] at hc
      obtain ⟨i, -, hi⟩ := hc
      exact absurd (h i) (by simpa using hi)
    rw [hs]
    rfl

lemma ninetySix_le_agsStep (N : ℕ) (M : Type) [Fintype M] [Nonempty M] :
    (96 : ℝ) ≤ agsStep N M := by
  rw [agsStep]
  have hcard : (1 : ℝ) ≤ (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  have hL : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := Nat.cast_nonneg _
  have h1 : (32 : ℝ) ≤ ((Fintype.card M : ℝ) + 1) ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ ((Fintype.card M : ℝ) + 1) ^ 5 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 5
  have h2 : (4 : ℝ) ≤ ((Nat.clog 2 (N + 1) : ℝ) + 2) ^ 2 := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ ((Nat.clog 2 (N + 1) : ℝ) + 2) ^ 2 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 2
  nlinarith

/-- **The main induction** (`thm:main-ags`).  Testing `orderedProd = m` on a word
of length `n ≤ N` costs `agsStep ^ (jLevel m + 1) · √n`. -/
theorem hasDual_eqProd (letter : σ → M) (N : ℕ) :
    ∀ (k : ℕ) (m : M), jLevel m = k → ∀ n ≤ N,
      HasDual (eqProd (n := n) letter m)
        (agsStep N M ^ (k + 1) * Real.sqrt (n : ℝ)) := by
  classical
  haveI : Nonempty M := ⟨1⟩
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m hm n hn
    have hstep1 : (1 : ℝ) ≤ agsStep N M := one_le_agsStep N M
    have hpow1 : (1 : ℝ) ≤ agsStep N M ^ k := one_le_pow₀ hstep1
    have hpk : agsStep N M ≤ agsStep N M ^ (k + 1) := by
      calc agsStep N M = agsStep N M ^ 1 := (pow_one _).symm
        _ ≤ agsStep N M ^ (k + 1) := pow_le_pow_right₀ hstep1 (by omega)
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · exact (hasDual_eqProd_zero letter m).mono (by simp)
    by_cases hm1 : m = 1
    · subst hm1
      refine (hasDual_eqProd_unit letter (n := n)).mono ?_
      rw [Finset.card_univ, Fintype.card_fin]
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hR : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have h := Real.sqrt_le_sqrt hn'
        rwa [Real.sqrt_one] at h
      have hs4 : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt (n : ℝ) := by
        have h := Real.sqrt_le_sqrt (show (n : ℝ) + 1 ≤ (2 * Real.sqrt (n : ℝ)) ^ 2 by
          rw [mul_pow, Real.sq_sqrt (by linarith)]; linarith)
        rwa [Real.sqrt_sq (by linarith)] at h
      have h96 : (96 : ℝ) ≤ agsStep N M := ninetySix_le_agsStep N M
      nlinarith
    · have hIH : ∀ s : M, jLevel s < jLevel m → ∀ len ≤ n,
          HasDual (eqProd (n := len) letter s)
            (agsStep N M ^ k * Real.sqrt (len : ℝ)) := by
        intro s hs len hlen
        refine (ih (jLevel s) (by omega) s rfl len (by omega)).mono ?_
        have hp : agsStep N M ^ (jLevel s + 1) ≤ agsStep N M ^ k :=
          pow_le_pow_right₀ hstep1 (by omega)
        nlinarith [Real.sqrt_nonneg (len : ℝ)]
      refine (hasDual_eqProd_step letter hm1 (by linarith) hIH).mono ?_
      calc 16 * stepBound n M (agsStep N M ^ k)
          ≤ agsStep N M ^ k * agsStep N M * Real.sqrt (n : ℝ) :=
            stepBound_le M hn1 hn hpow1
        _ = agsStep N M ^ (k + 1) * Real.sqrt (n : ℝ) := by rw [pow_succ]

/-- The same, indexed by the target rather than by a level. -/
theorem hasDual_eqProd' (letter : σ → M) (N : ℕ) (m : M) {n : ℕ} (hn : n ≤ N) :
    HasDual (eqProd (n := n) letter m)
      (agsStep N M ^ (jLevel m + 1) * Real.sqrt (n : ℝ)) :=
  hasDual_eqProd letter N (jLevel m) m rfl n hn

/-! ## The whole product

Evaluate every target test and feed the Boolean vector to an
outer function that reads off the unique accepting target.  `HasDual.combine'`
costs twice the sum, and no amplification factor appears anywhere: every target
test and the assembly are exact dual solutions. -/

/-- **The AGS upper bound.**  The monoid-valued ordered product of a word of
length `n ≤ N`. -/
theorem hasDual_wordProd (letter : σ → M) (N : ℕ) {n : ℕ} (hn : n ≤ N) :
    HasDual (fun x : Fin n → σ => wordProd letter x)
      (2 * ((Fintype.card M : ℝ)
        * (agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ)))) := by
  classical
  have hstep1 : (1 : ℝ) ≤ agsStep N M := one_le_agsStep N M
  have hc : ∀ m : M, (0 : ℝ)
      ≤ agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ) := by
    intro m; positivity
  have hg : ∀ m : M, HasDual (fun x : Fin n → σ => eqProd letter m x)
      (agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ)) := by
    intro m
    refine (hasDual_eqProd' letter N m hn).mono ?_
    have hp : agsStep N M ^ (jLevel m + 1) ≤ agsStep N M ^ (jDepth M + 1) :=
      pow_le_pow_right₀ hstep1 (by have := jLevel_le_jDepth m; omega)
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hcomb := HasDual.combine' (ι := Fin n) (σ := σ) (Pi := M) (V := Bool)
    (O' := M) (fun f => valueOf f)
    (g := fun m x => eqProd letter m x) (c := fun _ =>
      agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ)) hc hg
  refine (hcomb.ofEq fun x => ?_).mono (le_of_eq ?_)
  · exact valueOf_spec fun s => by rw [eqProd_eq_true]; exact eq_comm
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Weak duality**: the adversary bound of the ordered product. -/
theorem advPM_wordProd_le (letter : σ → M) (N : ℕ) {n : ℕ} (hn : n ≤ N) :
    advPM (fun x : Fin n → σ => wordProd letter x)
      ≤ 2 * ((Fintype.card M : ℝ)
        * (agsStep N M ^ (jDepth M + 1) * Real.sqrt (n : ℝ))) := by
  have h1 : (1 : ℝ) ≤ agsStep N M := one_le_agsStep N M
  refine advPM_le_of_hasDual ?_ (hasDual_wordProd letter N hn)
  have : (0 : ℝ) ≤ agsStep N M ^ (jDepth M + 1) := by positivity
  positivity


end

end MonoidProduct