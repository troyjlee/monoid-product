import MonoidProduct.Aperiodic.CubeRoot.Basic
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The localized strict-parent AGS step, and the fixed-left-context test

The AGS inductive step of `Aperiodic/Induction.lean` is naturally stated with a
**numeric** induction hypothesis: dual certificates for every `s` with
`jLevel s < jLevel m`.  The cube-root peel cannot supply that — its recursion
runs inside a fixed apex, against a Rees quotient, and what it can produce is
a certificate for every **strict two-sided parent** of the target, `MmM ⊊ MsM`.
That is genuinely weaker information: a smaller `J`-level does *not* imply
strict containment (incomparable classes can share a level), so the numeric
hypothesis quantifies over strictly more elements than the step ever uses.

`Aperiodic/Induction.lean` carries the localized statement
`hasDual_eqProd_step_strict` as the primary theorem, with the numeric
`hasDual_eqProd_step` recovered from it by `jLevel_lt_of_ssubset`; the same
split runs through `(U)`, `(V)`, `(W)` (`hasDual_uTest_strict`,
`hasDual_vTest_strict`, `hasDual_wTest_strict`) and, in
`Aperiodic/InfixCost.lean`, through the marked-cut chain
(`hasDual_markedAt_strict`, `hasDual_badInfixFor_strict`).  Every recursive
target carries its own strict containment, built from the two facts already
in the development:

* `twoIdeal_lt_of_mem_setE/F/G` — the pair or triple drops the ideal strictly;
* `twoIdeal_subset_of_mem_rightAbove/leftAbove` — the equality tests are run
  only at values above the dropped one.

This file records the `StrictParentIH`-flavoured statement and adds the
**fixed-left-context** test that the killed axes run: with a
context `a` fixed, `x ↦ [a · (x₁⋯xₙ) = m]`.

The paper prices that test by **prepending `a` as a known coordinate**
(proof of `prop:ags-axis-recurrence`: the predicate `c[w] = s` is the
ordinary product-equality predicate `P_s` after prepending the known letter
`c`, and the known coordinate costs no query), and then applying the localized step to the *prepended* problem.  That is
`hasDual_eqProdLeft_of_prepend` and `hasDual_eqProdLeft_of_strictParentIH`
below: the recursion is over the strict parents of `m` for the augmented
alphabet, never over the fibre `{v : a·v = m}`.

The fibre decomposition is kept as an auxiliary result, but it is **not**
the adapter: its premise "every fibre element is a strict parent of `m`"
fails on exactly the axes it would be wanted for.  With `e` any nonidentity
idempotent and `a = v = m = e` we have `a · v = m` while
`twoIdeal m = twoIdeal v`, so the containment is not strict — the
two-element semilattice already witnesses this, and no amount of Green
stability repairs it (stability promotes a one-sided containment *within* a
`J`-class to an `R`/`L` equivalence; it cannot make a same-class element a
strict `J`-parent).  The counterexample is machine-checked in
`Aperiodic/Examples.lean`, at the right zero `e₂` of `U₂`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-! ## The step, against `StrictParentIH` -/

/-- **The localized AGS step**, stated against the `StrictParentIH`
contract of `CubeRoot/Basic.lean`: certificates for the strict two-sided
parents of `m`, at every horizon `≤ n`, price the target test of `m`. -/
theorem hasDual_eqProd_step_of_strictParentIH (letter : σ → M) {m : M} (hm : m ≠ 1)
    {n : ℕ} {D : ℝ} (hD : 0 ≤ D) (hIH : StrictParentIH letter m n D) :
    HasDual (eqProd (n := n) letter m) (16 * stepBound n M D) :=
  hasDual_eqProd_step_strict letter hm hD hIH

/-- The regression, in the other direction: the numeric hypothesis is stronger,
so the existing `jLevel` step is a specialization.  (This is the wrapper that
`Aperiodic/Induction.lean` uses to define `hasDual_eqProd_step`.) -/
example (letter : σ → M) {m : M} (hm : m ≠ 1) {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hIH : ∀ s : M, jLevel s < jLevel m → ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) (B * Real.sqrt (len : ℝ))) :
    HasDual (eqProd (n := n) letter m) (16 * stepBound n M B) :=
  hasDual_eqProd_step_of_strictParentIH letter hm hB
    (strictParentIH_of_jLevel hIH)

/-! ## The fixed-left-context test -/

/-- **The target test with a fixed left context**: does the word's product,
multiplied on the left by the fixed `a`, equal `m`?  This is the test a killed
axis runs while it tracks the action of the word on a fixed state. -/
def eqProdLeft (letter : σ → M) (a m : M) {n : ℕ} (x : Fin n → σ) : Bool :=
  decide (a * wordProd letter x = m)

@[simp] lemma eqProdLeft_eq_true {letter : σ → M} {a m : M} {n : ℕ} {x : Fin n → σ} :
    eqProdLeft letter a m x = true ↔ a * wordProd letter x = m := by
  simp [eqProdLeft]

/-- The fibre of the left context: the ordinary targets the fixed-context test
decomposes into. -/
def leftFiber (a m : M) : Finset M := Finset.univ.filter fun v => a * v = m

@[simp] lemma mem_leftFiber {a m v : M} : v ∈ leftFiber a m ↔ a * v = m := by
  simp [leftFiber]

/-- **The decomposition**: the fixed-context test is the disjunction of the
ordinary target tests over the fibre. -/
theorem eqProdLeft_eq_sup (letter : σ → M) (a m : M) {n : ℕ} (x : Fin n → σ) :
    eqProdLeft letter a m x = (leftFiber a m).sup fun v => eqProd letter v x := by
  rw [Bool.eq_iff_iff, eqProdLeft_eq_true, sup_bool_eq_true]
  constructor
  · intro h
    exact ⟨wordProd letter x, mem_leftFiber.2 h, eqProd_eq_true.2 rfl⟩
  · rintro ⟨v, hv, hx⟩
    rw [eqProd_eq_true.1 hx]
    exact mem_leftFiber.1 hv

/-- **The fixed-left-context test, priced by its fibre.**  A square-root search
over the at most `|M|` ordinary targets `v` with `a·v = m`. -/
theorem hasDual_eqProdLeft (letter : σ → M) (a m : M) {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : M, a * v = m → HasDual (eqProd (n := n) letter v) c) :
    HasDual (fun x : Fin n → σ => eqProdLeft letter a m x)
      (c * (24 * Real.sqrt (((leftFiber a m).card : ℝ) + 1))) :=
  (HasDual.finsetSup (leftFiber a m) hc fun v hv => h v (mem_leftFiber.1 hv)).ofEq
    fun x => (eqProdLeft_eq_sup letter a m x).symm

/-- **The fibre test priced by the localized induction hypothesis** — an
auxiliary result, *not* the killed-axis adapter.

The premise `hfib` says every fibre element is a strict two-sided parent of
`m`.  That is unavailable on the regular axes this would be wanted for: for
any nonidentity idempotent `e`, taking `a = v = m = e` gives `a · v = m`
with `twoIdeal m = twoIdeal v`, so the containment is not strict (the
two-element semilattice is already a counterexample), and Green stability
cannot repair it.  The genuine adapter prepends the context instead; see
`hasDual_eqProdLeft_of_strictParentIH`. -/
theorem hasDual_eqProdLeft_of_strictFibre (letter : σ → M) (a m : M) {n : ℕ} {D : ℝ}
    (hD : 0 ≤ D) (hfib : ∀ v : M, a * v = m → twoIdeal m ⊂ twoIdeal v)
    (hIH : StrictParentIH letter m n D) :
    HasDual (fun x : Fin n → σ => eqProdLeft letter a m x)
      (D * Real.sqrt (n : ℝ) * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))) := by
  refine (hasDual_eqProdLeft letter a m (by positivity)
    (fun v hv => hIH v (hfib v hv) n le_rfl)).mono ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcard : (((leftFiber a m).card : ℝ)) ≤ (Fintype.card M : ℝ) := by
    exact_mod_cast (leftFiber a m).card_le_univ.trans_eq Finset.card_univ
  have := Real.sqrt_le_sqrt (show ((leftFiber a m).card : ℝ) + 1
    ≤ (Fintype.card M : ℝ) + 1 by linarith)
  linarith

/-! ## The virtual prepend: the killed-axis adapter

The paper prices the fixed-context predicate by making the known factor a
*coordinate of the word* rather than a case split on the product.  Over the
augmented alphabet `Option σ`, with `none` interpreted as the context `a`,
the fixed-context test at length `n` **is** the ordinary target test at
length `n + 1`, read at a word whose first coordinate is frozen.  Freezing a
coordinate costs nothing (`HasDual.restrict`), so the localized AGS step
applies to the prepended problem and transfers back unchanged. -/

/-- The letters, with a name adjoined for the fixed left context. -/
def prependLetter (letter : σ → M) (a : M) : Option σ → M
  | none => a
  | some s => letter s

@[simp] lemma prependLetter_none (letter : σ → M) (a : M) :
    prependLetter letter a none = a := rfl

@[simp] lemma prependLetter_some (letter : σ → M) (a : M) (s : σ) :
    prependLetter letter a (some s) = letter s := rfl

/-- The word with the context's coordinate prepended. -/
def prependWord {n : ℕ} (x : Fin n → σ) : Fin (n + 1) → Option σ :=
  Fin.cons none fun i => some (x i)

@[simp] lemma prependWord_zero {n : ℕ} (x : Fin n → σ) : prependWord x 0 = none :=
  Fin.cons_zero _ _

@[simp] lemma prependWord_succ {n : ℕ} (x : Fin n → σ) (i : Fin n) :
    prependWord x i.succ = some (x i) := Fin.cons_succ _ _ _

/-- The ordered product of a cons. -/
lemma orderedProd_cons (a : M) {n : ℕ} (z : Fin n → M) :
    orderedProd (Fin.cons a z) = a * orderedProd z := by
  rw [orderedProd_eq_prod_ofFn, orderedProd_eq_prod_ofFn, List.ofFn_succ]
  simp

/-- **Prepending the context is multiplying by it.** -/
lemma wordProd_prependWord (letter : σ → M) (a : M) {n : ℕ} (x : Fin n → σ) :
    wordProd (prependLetter letter a) (prependWord x) = a * wordProd letter x := by
  have hfun : (fun j => prependLetter letter a (prependWord x j))
      = Fin.cons a fun i => letter (x i) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp
  rw [wordProd, hfun, orderedProd_cons, wordProd]

/-- **The fixed-context test is the ordinary target test on the prepended
word.** -/
lemma eqProd_prependWord (letter : σ → M) (a m : M) {n : ℕ} (x : Fin n → σ) :
    eqProd (prependLetter letter a) m (prependWord x) = eqProdLeft letter a m x := by
  rw [Bool.eq_iff_iff, eqProd_eq_true, eqProdLeft_eq_true, wordProd_prependWord]

/-- **The adapter**: freezing the context's coordinate costs nothing, so
the fixed-left-context test at length `n` is priced by the ordinary target
test at length `n + 1` over the augmented alphabet. -/
theorem hasDual_eqProdLeft_of_prepend (letter : σ → M) (a m : M) {n : ℕ} {c : ℝ}
    (h : HasDual (eqProd (n := n + 1) (prependLetter letter a) m) c) :
    HasDual (fun x : Fin n → σ => eqProdLeft letter a m x) c := by
  refine (h.restrict (e := Fin.succ) (Fin.succ_injective n)
    (Φ := fun x => prependWord x) ?_ ?_).ofEq fun x => ?_
  · intro x y i
    rw [prependWord_succ, prependWord_succ, Option.some_inj]
  · intro x y j hj
    revert hj
    refine Fin.cases ?_ (fun i hj => absurd rfl (hj i)) j
    intro _
    rw [prependWord_zero, prependWord_zero]
  · exact eqProd_prependWord letter a m x

/-- **The killed-axis endpoint**, as the paper states it: with the
context prepended as a known coordinate, the localized AGS step prices the
fixed-context predicate from certificates for the **strict two-sided parents
of `m` over the augmented alphabet** — never from a search over
`{v : a·v = m}`. -/
theorem hasDual_eqProdLeft_of_strictParentIH (letter : σ → M) (a : M) {m : M}
    (hm : m ≠ 1) {n : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hIH : StrictParentIH (prependLetter letter a) m (n + 1) D) :
    HasDual (fun x : Fin n → σ => eqProdLeft letter a m x)
      (16 * stepBound (n + 1) M D) :=
  hasDual_eqProdLeft_of_prepend letter a m
    (hasDual_eqProd_step_of_strictParentIH (prependLetter letter a) hm hD hIH)

end

end MonoidProduct
