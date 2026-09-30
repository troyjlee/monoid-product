import QuantumQueryComplexity.Scan.Dual
import QuantumQueryComplexity.Scan.Max
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Order-independent incremental summaries and their scans

The abstraction behind the essential-width theorem (`thm:essential-width`):
the answer is determined by an **exact
state updated under insertions**, and the state of a revealed set does not
depend on the order in which it was revealed.

Order-independence is the *indexing*: `state` takes a `Finset`, so there is
nothing to prove.  Two further design choices keep the structure minimal.

* **Determinism replaces the update maps.**  The paper carries maps
  `δᵢ : Q × σ → Q` with `s_x(T ∪ {i}) = δᵢ(s_x(T), xᵢ)`.  Every proof uses
  only the consequence: *equal old states and equal symbols give equal new
  states*.  Stating that directly (`state_insert`) is weaker, and easier to
  instantiate.
* **Readout congruence replaces the readout map.**  `out_congr` says the final
  state determines the output, which is all the scan's `out_eq` needs — no
  `g : Q → O` has to be produced.

A summary and a scan order yield a `Scan` (`QuantumQueryComplexity/Scan/Defs.lean`), whose
attached dual (`QuantumQueryComplexity/Scan/Dual.lean`) is already summary-agnostic.  The
branch at `i` is the state of the coordinates scanned so far *including* `i`;
a branch is red when the state changed.  The three `Scan` laws all reduce to
one observation, `state_beforeSet_congr`: **the state on the before-set is the
branch at the last-scanned coordinate**, so equal branch prefixes force equal
before-states with no induction — the same device as
`runBefore_eq_sup_runAfter` in the maximum scan.

`essentialSet x T` is the set of positions of `T` whose deletion changes the
state.  Its cardinality bound is the *only* input-specific hypothesis of the
essential-width theorem; the identification of the scan's red event with
essentiality at the top of the prefix is in `MonoidProduct/Width/Incidence.lean`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **An order-independent incremental summary**: a `Finset`-indexed state with
a deterministic insertion law, whose final state determines the output. -/
structure IncrementalSummary (ι σ O Q : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The state of a revealed set of coordinates. -/
  state : (ι → σ) → Finset ι → Q
  /-- The output. -/
  out : (ι → σ) → O
  /-- The empty state does not depend on the input. -/
  state_empty : ∀ x y : ι → σ, state x ∅ = state y ∅
  /-- **Determinism**: equal old states and equal symbols give equal new
  states. -/
  state_insert : ∀ (x y : ι → σ) (T : Finset ι) (i : ι), i ∉ T →
    state x T = state y T → x i = y i → state x (insert i T) = state y (insert i T)
  /-- The final state determines the output. -/
  out_congr : ∀ x y : ι → σ, state x Finset.univ = state y Finset.univ →
    out x = out y

namespace IncrementalSummary

/-- **The essential positions** of a revealed set: those whose deletion changes
the state (`def:essential-width`); the essential *width* is a uniform bound on
its cardinality. -/
def essentialSet (S : IncrementalSummary ι σ O Q) (x : ι → σ) (T : Finset ι) :
    Finset ι :=
  T.filter fun i => S.state x T ≠ S.state x (T.erase i)

lemma mem_essentialSet {S : IncrementalSummary ι σ O Q} {x : ι → σ}
    {T : Finset ι} {i : ι} :
    i ∈ S.essentialSet x T ↔ i ∈ T ∧ S.state x T ≠ S.state x (T.erase i) := by
  simp [essentialSet]

lemma essentialSet_subset (S : IncrementalSummary ι σ O Q) (x : ι → σ)
    (T : Finset ι) : S.essentialSet x T ⊆ T :=
  Finset.filter_subset _ _

/-- **Width zero means the function is constant**: deleting elements one at a
time never changes the state, so every state is the empty state. -/
theorem out_const_of_essentialSet_eq_empty (S : IncrementalSummary ι σ O Q)
    (h : ∀ (x : ι → σ) (T : Finset ι), S.essentialSet x T = ∅) (x y : ι → σ) :
    S.out x = S.out y := by
  have hstate : ∀ (x : ι → σ) (T : Finset ι), S.state x T = S.state x ∅ := by
    intro x T
    induction T using Finset.strongInduction with
    | _ T ih =>
      rcases Finset.eq_empty_or_nonempty T with rfl | ⟨i, hi⟩
      · rfl
      · have hess : S.state x T = S.state x (T.erase i) := by
          by_contra hne
          have : i ∈ S.essentialSet x T := mem_essentialSet.mpr ⟨hi, hne⟩
          rw [h x T] at this
          exact absurd this (Finset.notMem_empty i)
        rw [hess, ih _ (Finset.erase_ssubset hi)]
  refine S.out_congr x y ?_
  rw [hstate x, hstate y, S.state_empty]

/-! ## The scan attached to a summary

The order is a ranking `rk : ι → Fin (card ι)`; `beforeSet rk i` (from
`QuantumQueryComplexity/Scan/Max.lean`, order-free despite its home) is the set of
coordinates scanned strictly before `i`. -/

/-! ### Width zero, in the form the callers use -/

/-- A width bound of `0` means every essential set is empty. -/
lemma essentialSet_eq_empty_of_width_zero (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0)
    (x : ι → σ) (T : Finset ι) : S.essentialSet x T = ∅ :=
  Finset.card_eq_zero.mp (Nat.le_zero.mp (hwidth x T))

/-- **Width zero means the output is constant** (`thm:essential-width`, the zero case): only
the reachable output is constrained, nothing is assumed about `Q` or `O`. -/
theorem out_const_of_width_zero (S : IncrementalSummary ι σ O Q)
    (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ 0)
    (x y : ι → σ) : S.out x = S.out y :=
  S.out_const_of_essentialSet_eq_empty (S.essentialSet_eq_empty_of_width_zero hwidth) x y

/-- The coordinates scanned up to and including `i`. -/
def upToSet (rk : ι → Fin (Fintype.card ι)) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => rk j ≤ rk i

lemma mem_upToSet {rk : ι → Fin (Fintype.card ι)} {i j : ι} :
    j ∈ upToSet rk i ↔ rk j ≤ rk i := by simp [upToSet]

lemma notMem_beforeSet_self (rk : ι → Fin (Fintype.card ι)) (i : ι) :
    i ∉ beforeSet rk i := by
  simp [beforeSet]

lemma upToSet_eq_insert {rk : ι → Fin (Fintype.card ι)}
    (hrk : Function.Injective rk) (i : ι) :
    upToSet rk i = insert i (beforeSet rk i) := by
  ext j
  simp only [mem_upToSet, Finset.mem_insert, beforeSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl (hrk heq)
  · rintro (rfl | hlt)
    · exact le_rfl
    · exact le_of_lt hlt

variable (S : IncrementalSummary ι σ O Q)

/-- **The state on the before-set is the branch at the last-scanned
coordinate.**  Stated as a congruence: equal branch prefixes give equal
before-states.  The single case split — is the before-set empty? — replaces an
induction on the scan order. -/
lemma state_beforeSet_congr (rk : ι → Fin (Fintype.card ι)) {x y : ι → σ}
    {i : ι}
    (h : ∀ j, rk j < rk i → S.state x (upToSet rk j) = S.state y (upToSet rk j)) :
    S.state x (beforeSet rk i) = S.state y (beforeSet rk i) := by
  rcases Finset.eq_empty_or_nonempty (beforeSet rk i) with hemp | hne
  · rw [hemp]
    exact S.state_empty x y
  · obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image (beforeSet rk i) rk hne
    have hj₀lt : rk j₀ < rk i := by
      have := hj₀
      simp only [beforeSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hset : beforeSet rk i = upToSet rk j₀ := by
      ext j
      simp only [beforeSet, Finset.mem_filter, Finset.mem_univ, true_and,
        mem_upToSet]
      constructor
      · intro hj
        exact hmax j (by simp [beforeSet, hj])
      · intro hj
        exact lt_of_le_of_lt hj hj₀lt
    rw [hset]
    exact h j₀ hj₀lt

/-- **The scan attached to a summary and an order.**  The branch at `i` is the
state up to and including `i`; the colour is red when the state changed. -/
def toScan (rk : ι → Fin (Fintype.card ι)) (hrk : Function.Injective rk) :
    Scan ι σ O Q where
  rank := rk
  rank_inj := hrk
  br x i := S.state x (upToSet rk i)
  col x i := decide (S.state x (upToSet rk i) ≠ S.state x (beforeSet rk i))
  out := S.out
  br_ne x y i hpre hbr := by
    intro hxy
    refine hbr ?_
    rw [upToSet_eq_insert hrk]
    exact S.state_insert x y (beforeSet rk i) i (notMem_beforeSet_self rk i)
      (S.state_beforeSet_congr rk hpre) hxy
  out_eq x y h := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset ι) with hemp | hne
    · refine S.out_congr x y ?_
      rw [hemp]
      exact S.state_empty x y
    · obtain ⟨j₁, _, hmax⟩ := Finset.exists_max_image Finset.univ rk hne
      have huniv : (Finset.univ : Finset ι) = upToSet rk j₁ := by
        ext j
        simp only [Finset.mem_univ, mem_upToSet, true_iff]
        exact hmax j (Finset.mem_univ j)
      refine S.out_congr x y ?_
      rw [huniv]
      exact h j₁
  black_unique x y i hx hy hpre := by
    rw [decide_eq_false_iff_not, not_not] at hx hy
    rw [hx, hy]
    exact S.state_beforeSet_congr rk hpre

@[simp] lemma toScan_br (rk : ι → Fin (Fintype.card ι))
    (hrk : Function.Injective rk) (x : ι → σ) (i : ι) :
    (S.toScan rk hrk).br x i = S.state x (upToSet rk i) := rfl

@[simp] lemma toScan_out (rk : ι → Fin (Fintype.card ι))
    (hrk : Function.Injective rk) (x : ι → σ) :
    (S.toScan rk hrk).out x = S.out x := rfl

lemma toScan_col_eq_true_iff (rk : ι → Fin (Fintype.card ι))
    (hrk : Function.Injective rk) (x : ι → σ) (i : ι) :
    (S.toScan rk hrk).col x i = true
      ↔ S.state x (upToSet rk i) ≠ S.state x (beforeSet rk i) := by
  simp [toScan]

end IncrementalSummary

end MonoidProduct
