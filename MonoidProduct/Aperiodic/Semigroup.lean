import MonoidProduct.Aperiodic.Induction
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# From monoids to semigroups

The AGS theorem (`thm:main-ags`) is stated here for a monoid, but the
paper's object is a finite aperiodic *semigroup*.  Mathlib's `WithOne S` is
`Option S` with a `Monoid` instance for any `Semigroup S`, so the hypothesis is
declared through the unitisation and the theorem transports.

The transport is one application of `HasDual.ofKer`.  A dual solution sees only
the partition of inputs into level sets, and `WithOne.coe` is injective, so the
`S`-valued product and its image in `WithOne S` induce the *same* partition and
therefore have the same dual solutions at the same cost.  Nothing is paid for
the adapter.

`WithOne S` carries no `Fintype` or `DecidableEq` instance in Mathlib — it is an
opaque `def` — so both are supplied here by `inferInstanceAs`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## Instances for the unitisation -/

instance instFintypeWithOne {S : Type} [Fintype S] : Fintype (WithOne S) :=
  inferInstanceAs (Fintype (Option S))

instance instDecidableEqWithOne {S : Type} [DecidableEq S] :
    DecidableEq (WithOne S) :=
  inferInstanceAs (DecidableEq (Option S))

/-- The unitisation adds exactly one element. -/
@[simp] lemma card_withOne (S : Type) [Fintype S] :
    Fintype.card (WithOne S) = Fintype.card S + 1 :=
  Fintype.card_option (α := S)

/-! ## Aperiodic semigroups -/

/-- A finite semigroup is aperiodic when its unitisation is.  For finite `S`
this is equivalent to eventual stabilisation of positive powers inside `S`; the proof does not need the equivalence. -/
class IsAperiodicSemigroup (S : Type*) [Semigroup S] : Prop where
  /-- The unitisation is an aperiodic monoid. -/
  withOne : IsAperiodicMonoid (WithOne S)

instance instIsAperiodicMonoidWithOne {S : Type*} [Semigroup S]
    [IsAperiodicSemigroup S] : IsAperiodicMonoid (WithOne S) :=
  IsAperiodicSemigroup.withOne

/-! ## The semigroup-valued ordered product -/

section
variable {S : Type} [Semigroup S]

/-- The ordered product of a *nonempty* word of semigroup elements. -/
def semigroupProd : (n : ℕ) → (Fin (n + 1) → S) → S
  | 0, x => x 0
  | n + 1, x => semigroupProd n (fun i => x i.castSucc) * x (Fin.last (n + 1))

/-- **The adapter.**  The `S`-valued product is the monoid product of the
coerced word. -/
lemma coe_semigroupProd (n : ℕ) (x : Fin (n + 1) → S) :
    ((semigroupProd n x : S) : WithOne S)
      = orderedProd fun i => ((x i : S) : WithOne S) := by
  induction n with
  | zero =>
      rw [semigroupProd, orderedProd_eq_rangeProd]
      have h : rangeProd (fun i : Fin 1 => ((x i : S) : WithOne S)) 0 1
          = padAt (fun i : Fin 1 => ((x i : S) : WithOne S)) 0 :=
        rangeProd_eq_padAt _ 0
      rw [h, padAt_of_lt _ Nat.one_pos]
      rfl
  | succ n ih =>
      have hy : ∀ i : ℕ, 0 ≤ i → i < n + 1 →
          padAt (fun j : Fin (n + 1 + 1) => ((x j : S) : WithOne S)) i
            = padAt (fun j : Fin (n + 1) =>
                ((x j.castSucc : S) : WithOne S)) i := by
        intro i _ hi
        rw [padAt_of_lt _ (show i < n + 1 + 1 by omega), padAt_of_lt _ hi]
        rfl
      rw [semigroupProd, WithOne.coe_mul, ih, orderedProd_eq_rangeProd,
        orderedProd_eq_rangeProd, rangeProd_succ_right _ (Nat.zero_le (n + 1)),
        rangeProd_congr hy, padAt_of_lt _ (show n + 1 < n + 1 + 1 by omega)]
      rfl

end

/-! ## The theorem -/

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {S : Type} [Semigroup S] [Fintype S] [DecidableEq S]
  [IsAperiodicSemigroup S]

/-- **The AGS upper bound for a finite aperiodic semigroup.**  The adapter costs
nothing: `HasDual.ofKer` transports the monoid solution because the coercion is
injective, so the two products have the same level sets. -/
theorem hasDual_semigroupProd (sletter : σ → S) (N : ℕ) {n : ℕ}
    (hn : n + 1 ≤ N) :
    HasDual (fun x : Fin (n + 1) → σ => semigroupProd n fun i => sletter (x i))
      (2 * (((Fintype.card S : ℝ) + 1)
        * (agsStep N (WithOne S) ^ (jDepth (WithOne S) + 1)
            * Real.sqrt ((n + 1 : ℕ) : ℝ)))) := by
  have hbase := hasDual_wordProd (σ := σ) (M := WithOne S)
    (fun c => ((sletter c : S) : WithOne S)) N (n := n + 1) hn
  refine (hbase.ofKer fun u v => ?_).mono (le_of_eq ?_)
  · rw [wordProd, wordProd, ← coe_semigroupProd, ← coe_semigroupProd]
    exact WithOne.coe_inj
  · rw [card_withOne]
    push_cast
    ring

/-- **Weak duality**: the adversary bound of the semigroup product. -/
theorem advPM_semigroupProd_le (sletter : σ → S) (N : ℕ) {n : ℕ}
    (hn : n + 1 ≤ N) :
    advPM (fun x : Fin (n + 1) → σ => semigroupProd n fun i => sletter (x i))
      ≤ 2 * (((Fintype.card S : ℝ) + 1)
        * (agsStep N (WithOne S) ^ (jDepth (WithOne S) + 1)
            * Real.sqrt ((n + 1 : ℕ) : ℝ))) := by
  have h1 : (1 : ℝ) ≤ agsStep N (WithOne S) := one_le_agsStep N (WithOne S)
  refine advPM_le_of_hasDual ?_ (hasDual_semigroupProd sletter N hn)
  have h2 : (0 : ℝ) ≤ agsStep N (WithOne S) ^ (jDepth (WithOne S) + 1) := by
    positivity
  have h3 : (0 : ℝ) ≤ (Fintype.card S : ℝ) := Nat.cast_nonneg _
  positivity

end

end MonoidProduct
