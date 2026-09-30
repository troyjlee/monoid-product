import QuantumQueryComplexity.Scan.Join
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Critical occurrences and the `log |L|` budget

Call a position `j` of a finite set `T` of positions **critical** when its value
is not already implied by the others:

  `¬ (x j ≤ ⋁_{k ∈ T \ {j}} x k)`.

Criticality is a property of *positions*, not of values: a `Finset ι` keeps
repeated occurrences apart, which is what the counting below needs.

The whole combinatorial content of the semilattice bound is that a set cannot
have many critical positions:

  `2 ^ |C(x,T)| ≤ |L| + 1`.

The proof is one injection.  Send a subset `U ⊆ C(x,T)` to `⋁_{j ∈ U} x j`,
taken in `WithBot L` so that `U = ∅` is allowed.  If `U ≠ V`, pick
`j ∈ U \ V`; then `x j ≤ Φ U`, while every member of `V` lies in `T \ {j}` and
so `Φ V ≤ ⋁_{k ∈ T \ {j}} x k`.  Equality of the two joins would put `x j`
below that, contradicting the criticality of `j`.  The domain has
`2 ^ |C(x,T)|` elements and `WithBot L` has `|L| + 1`.

Taking the **floor** binary logarithm is the exact conclusion of `2 ^ c ≤ |L|+1`;
this is why `Nat.log` appears here where `Nat.clog` appears in the padding
arguments elsewhere in this development.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [Fintype A] [SemilatticeSup A]

/-- The join of the values at a set of positions; `⊥` when the set is empty.
Adjoining a bottom is only a device for the empty join — the semilattice being
measured is still `A`, which is why the count below is `|A| + 1`. -/
def joinOn (x : ι → A) (T : Finset ι) : WithBot A :=
  T.sup fun i => (x i : WithBot A)

lemma le_joinOn {x : ι → A} {T : Finset ι} {j : ι} (hj : j ∈ T) :
    (x j : WithBot A) ≤ joinOn x T :=
  Finset.le_sup (f := fun i => (x i : WithBot A)) hj

lemma joinOn_mono (x : ι → A) {T U : Finset ι} (h : T ⊆ U) :
    joinOn x T ≤ joinOn x U :=
  Finset.sup_mono h

open scoped Classical in
/-- The positions of `T` whose value is not implied by the others. -/
noncomputable def criticalSet (x : ι → A) (T : Finset ι) : Finset ι :=
  T.filter fun j => ¬ (x j : WithBot A) ≤ joinOn x (T.erase j)

lemma mem_criticalSet {x : ι → A} {T : Finset ι} {j : ι} :
    j ∈ criticalSet x T
      ↔ j ∈ T ∧ ¬ (x j : WithBot A) ≤ joinOn x (T.erase j) := by
  classical
  simp [criticalSet]

lemma criticalSet_subset (x : ι → A) (T : Finset ι) : criticalSet x T ⊆ T :=
  fun _ hj => (mem_criticalSet.1 hj).1

/-! ## The powerset injection -/

/-- If the join of one subset of critical positions is below that of another,
the first subset is contained in the second. -/
lemma subset_of_joinOn_le {x : ι → A} {T U V : Finset ι}
    (hU : U ⊆ criticalSet x T) (hV : V ⊆ criticalSet x T)
    (h : joinOn x U ≤ joinOn x V) : U ⊆ V := by
  intro j hj
  by_contra hjV
  -- every member of `V` lies in `T \ {j}`
  have hVsub : V ⊆ T.erase j := by
    intro k hk
    refine Finset.mem_erase.2 ⟨fun hkj => hjV (hkj ▸ hk), ?_⟩
    exact criticalSet_subset x T (hV hk)
  have hcrit := (mem_criticalSet.1 (hU hj)).2
  exact hcrit (le_trans (le_joinOn hj) (le_trans h (joinOn_mono x hVsub)))

/-- **Distinct subsets of the critical positions have distinct joins.** -/
lemma joinOn_injOn (x : ι → A) (T : Finset ι) :
    ∀ U ∈ (criticalSet x T).powerset, ∀ V ∈ (criticalSet x T).powerset,
      joinOn x U = joinOn x V → U = V := by
  intro U hU V hV h
  rw [Finset.mem_powerset] at hU hV
  exact Finset.Subset.antisymm
    (subset_of_joinOn_le hU hV h.le) (subset_of_joinOn_le hV hU h.ge)

/-- **The criticality bound**: a set of positions has at most `log₂(|A|+1)`
critical ones. -/
theorem two_pow_card_criticalSet_le (x : ι → A) (T : Finset ι) :
    2 ^ (criticalSet x T).card ≤ Fintype.card A + 1 := by
  classical
  have hcard : (Finset.univ : Finset (WithBot A)).card = Fintype.card A + 1 := by
    rw [Finset.card_univ]
    exact Fintype.card_option
  calc 2 ^ (criticalSet x T).card = ((criticalSet x T).powerset).card :=
        (Finset.card_powerset _).symm
    _ ≤ (Finset.univ : Finset (WithBot A)).card :=
        Finset.card_le_card_of_injOn (fun U => joinOn x U)
          (fun U _ => Finset.mem_univ _) (joinOn_injOn x T)
    _ = Fintype.card A + 1 := hcard

/-! ## The budget -/

/-- `⌊log₂(|A|+1)⌋`, the number of critical occurrences a set of positions can
have.  The floor logarithm is the exact conclusion of `2 ^ c ≤ |A| + 1`. -/
def joinBits (A : Type*) [Fintype A] : ℕ := Nat.log 2 (Fintype.card A + 1)

theorem card_criticalSet_le (x : ι → A) (T : Finset ι) :
    (criticalSet x T).card ≤ joinBits A :=
  Nat.le_log_of_pow_le (by norm_num) (two_pow_card_criticalSet_le x T)

lemma joinBits_pos [Nonempty A] : 0 < joinBits A := by
  have h1 : 1 ≤ Fintype.card A := Fintype.card_pos
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  simpa using h1

end MonoidProduct
