import MonoidProduct.Width.Main
import QuantumQueryComplexity.Promise.HasDual
import QuantumQueryComplexity.Promise.Basic
import QuantumQueryComplexity.Promise.PredictionTreeCompose
import QuantumQueryComplexity.Quantum.UniformHasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The essential-width theorem on a promise domain

`monoid.tex`, `def:essential-width` and `thm:essential-width` (with the weighted form
`eq:weighted-width`), as stated in the paper: `f : D → O` on a **promise domain**
`D ⊆ Σ^I`, an incremental summary whose laws are only asked of inputs in `D`, and
essential width `B` measured over `D` only.  Conclusion: `ADV±_D(f) ≤ 16·√(nB)`, and `f` is
constant on `D` when `B = 0`.

`MonoidProduct/Width/Summary.lean` and `Main.lean` prove the total-input case
(`IncrementalSummary`, `advPM_le_of_summary_nonneg`).  A promise summary does **not** in
general extend to a total one: the insertion law can force two different states on one
input outside `D` (for `D = {00, 11}` and a summary of the first bit that forgets both
coordinates on singletons, the word `10` is forced to the states of both `00` and `11`).
So the promise theorem is proved directly, but still by reusing the scan engine.

## The construction

A promise is presented as in `QuantumQueryComplexity/Promise/Defs.lean`: a finite type `X`
with an observation map `read : X → ι → σ` (the paper's `D ⊆ Σ^I` is `X = D`,
`read = Subtype.val`).  `PromiseSummary read O Q` is `IncrementalSummary` with every law
quantified over `X` and the letter test `read x i = read y i`; `PromiseSummary.ofMaps`
builds one from the paper's data `(q_∅, δ_i, g, s_x)`.

For a fixed scan order `e`, the summary's decision tree is extended to **all** inputs
`ι → σ` as a deterministic automaton on `Option Q` (`PromiseSummary.run`): from the node
state `q` at time `t`, letter `a` leads to the state of any promise input with the same
node state and letter `a` at the scanned coordinate — well defined by the insertion law —
and to the absorbing junk state `none` if there is none.  The extension is order-dependent
(which is why no total summary exists), but for a *fixed* order it is a genuine total
`Scan` (`PromiseSummary.extScan`): `br_ne` and `black_unique` are determinism of the
automaton, `out_eq` is determinism of the final readout.  On promise inputs the automaton
runs through the true summary states (`run_read`), so the colours there are the summary's
colours and the red event at time `t` is essentiality at the top of the prefix
(`pCol_symm_iff`).

The scan's total dual (`Scan.dual`) is restricted to the promise
(`DualPair.restrictTo`) — only the masses **on the promise** are charged, so the junk
branch costs nothing — recoded to `f` (`DualPairOn.ofKer`), and averaged over all orders
(`dualPairOnAvg`, the promise mirror of `DualPair.averageUnif`).  The cost accounting is
`Main.lean`'s verbatim (`bWeight`, `bTerm`, `bBase`), with the incidence count
`card_essEvent_mul_le_of_bound` applied to the promise essential sets.

## Results

* `PromiseSummary.exists_dualPairOn_isWeightedCostLe` — `eq:weighted-width` on the
  promise, `B ≥ 1`: a promise dual of `c`-weighted cost `16·√B·(∑ cᵢ²)^{1/2}`;
  `PromiseSummary.exists_weightedDualOn` for every `B ≥ 0`.
* `PromiseSummary.hasDualOn_of_width` — `HasDualOn read f (16·√(nB))`, every `B ≥ 0`.
* `PromiseSummary.advPMOn_le_of_width` — the boxed `ADV±_D(f) ≤ 16·√(nB)`.
* `PromiseSummary.out_const_of_width_zero`, `advPMOn_eq_zero_of_width_zero`,
  `qQueryOn_eq_zero_of_width_zero` — the `B = 0` case.
* `PromiseSummary.qQueryOn_third_le_of_width` — `Q_{1/3}(f) = O(√(nB))` on the promise.
* `PromiseSummary.advPM_le_of_ofTotal` — sanity: the total theorem is the case
  `X = ι → σ`, `read = id` (`PromiseSummary.ofTotal`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {O : Type} [Fintype O] [DecidableEq O]
variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-! ## Promise summaries -/

/-- **An order-independent incremental summary on a promise** (`def:essential-width`):
the laws of `IncrementalSummary`, asked only of promise inputs `x : X`, whose letters are
read through `read`. -/
structure PromiseSummary {ι σ X : Type} [Fintype ι] [DecidableEq ι]
    (read : X → ι → σ) (O Q : Type) where
  /-- The state `s_x(T)` of a revealed set of coordinates. -/
  state : X → Finset ι → Q
  /-- The function `f` on the promise. -/
  out : X → O
  /-- `s_x(∅) = q_∅` for every promise input. -/
  state_empty : ∀ x y : X, state x ∅ = state y ∅
  /-- **Determinism**: equal old states and equal letters give equal new states. -/
  state_insert : ∀ (x y : X) (T : Finset ι) (i : ι), i ∉ T →
    state x T = state y T → read x i = read y i →
    state x (insert i T) = state y (insert i T)
  /-- The final state determines the output. -/
  out_congr : ∀ x y : X, state x Finset.univ = state y Finset.univ → out x = out y

namespace PromiseSummary

variable {read : X → ι → σ}

/-- **The paper's data** `(q_∅, δᵢ, g, s_x)` give a promise summary for `f`:
`s_x(∅) = q_∅`, `s_x(T ∪ {i}) = δᵢ(s_x(T), xᵢ)` for `i ∉ T`, and `f(x) = g(s_x(I))`. -/
def ofMaps (q₀ : Q) (δ : ι → Q → σ → Q) (g : Q → O) (s : X → Finset ι → Q) (f : X → O)
    (hs₀ : ∀ x, s x ∅ = q₀)
    (hsδ : ∀ x T i, i ∉ T → s x (insert i T) = δ i (s x T) (read x i))
    (hf : ∀ x, f x = g (s x Finset.univ)) : PromiseSummary read O Q where
  state := s
  out := f
  state_empty x y := by rw [hs₀, hs₀]
  state_insert x y T i hi hT hxy := by rw [hsδ x T i hi, hsδ y T i hi, hT, hxy]
  out_congr x y h := by rw [hf, hf, h]

/-- A total summary is a promise summary on the full cube. -/
def ofTotal (S : IncrementalSummary ι σ O Q) : PromiseSummary (id : (ι → σ) → ι → σ) O Q where
  state := S.state
  out := S.out
  state_empty := S.state_empty
  state_insert := S.state_insert
  out_congr := S.out_congr

variable (S : PromiseSummary read O Q)

/-- **The essential positions** `Ess_x(T)`: those whose deletion changes the state. -/
def essentialSet (x : X) (T : Finset ι) : Finset ι :=
  T.filter fun i => S.state x T ≠ S.state x (T.erase i)

lemma mem_essentialSet {x : X} {T : Finset ι} {i : ι} :
    i ∈ S.essentialSet x T ↔ i ∈ T ∧ S.state x T ≠ S.state x (T.erase i) := by
  simp [essentialSet]

lemma essentialSet_subset (x : X) (T : Finset ι) : S.essentialSet x T ⊆ T :=
  Finset.filter_subset _ _

@[simp] lemma ofTotal_essentialSet (S : IncrementalSummary ι σ O Q) (x : ι → σ)
    (T : Finset ι) : (ofTotal S).essentialSet x T = S.essentialSet x T := rfl

/-- **Width zero means `f` is constant on the promise** (`thm:essential-width`, zero case):
deleting one element at a time never changes the state. -/
theorem out_const_of_width_zero
    (hwidth : ∀ (x : X) (T : Finset ι), (S.essentialSet x T).card ≤ 0) (x y : X) :
    S.out x = S.out y := by
  have hstate : ∀ (x : X) (T : Finset ι), S.state x T = S.state x ∅ := by
    intro x T
    induction T using Finset.strongInduction with
    | _ T ih =>
      rcases Finset.eq_empty_or_nonempty T with rfl | ⟨i, hi⟩
      · rfl
      · have hess : S.state x T = S.state x (T.erase i) := by
          by_contra hne
          have hmem : i ∈ S.essentialSet x T := S.mem_essentialSet.mpr ⟨hi, hne⟩
          rw [Finset.card_eq_zero.mp (Nat.le_zero.mp (hwidth x T))] at hmem
          exact absurd hmem (Finset.notMem_empty i)
        rw [hess, ih _ (Finset.erase_ssubset hi)]
  refine S.out_congr x y ?_
  rw [hstate x, hstate y, S.state_empty]

/-! ## The total automaton attached to a scan order -/

/-- The coordinates scanned at positions `< t`. -/
def preSet (e : Order ι) (t : ℕ) : Finset ι :=
  Finset.univ.filter fun j => ((e j : ℕ) < t)

lemma mem_preSet {e : Order ι} {t : ℕ} {j : ι} : j ∈ preSet e t ↔ (e j : ℕ) < t := by
  simp [preSet]

lemma preSet_zero (e : Order ι) : preSet e 0 = ∅ := by
  ext j
  simp [mem_preSet]

lemma preSet_card (e : Order ι) : preSet e (Fintype.card ι) = Finset.univ := by
  ext j
  simp [mem_preSet, (e j).2]

lemma notMem_preSet_symm (e : Order ι) {t : ℕ} (ht : t < Fintype.card ι) :
    e.symm ⟨t, ht⟩ ∉ preSet e t := by
  simp [mem_preSet]

lemma preSet_succ (e : Order ι) {t : ℕ} (ht : t < Fintype.card ι) :
    preSet e (t + 1) = insert (e.symm ⟨t, ht⟩) (preSet e t) := by
  ext j
  simp only [mem_preSet, Finset.mem_insert]
  constructor
  · intro hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact Or.inr h
    · left
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
  · rintro (rfl | h)
    · simp
    · omega

/-- The positions `< t + 1` form the prefix set of `Record.lean`. -/
lemma preSet_succ_eq_prefixSet [Nonempty ι] (e : Order ι) (t : Fin (Fintype.card ι)) :
    preSet e ((t : ℕ) + 1) = prefixSet e t := by
  ext j
  rw [mem_preSet, mem_prefixSet, Fin.le_iff_val_le_val]
  omega

/-- The positions `< e i` are the before-set of `i`. -/
lemma preSet_rank_eq_beforeSet (e : Order ι) (i : ι) :
    preSet e (e i : ℕ) = beforeSet (⇑e) i := by
  ext j
  simp only [mem_preSet, beforeSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]

open scoped Classical in
/-- The initial node state: `q_∅`, or junk if the promise is empty. -/
noncomputable def initSt : Option Q :=
  if h : Nonempty X then some (S.state h.some ∅) else none

open scoped Classical in
/-- **One step of the extended automaton**: from node state `q` at time `t`, scanning `i`
with letter `a`, go to the state of any promise input with node state `q` and letter `a`
at `i`; if there is none, to the junk state. -/
noncomputable def step (e : Order ι) (t : ℕ) (i : ι) (oq : Option Q) (a : σ) : Option Q :=
  oq.bind fun q =>
    if h : ∃ x : X, S.state x (preSet e t) = q ∧ read x i = a then
      some (S.state h.choose (insert i (preSet e t)))
    else none

/-- **The extended automaton** on an arbitrary word, run for the first `t` scan steps. -/
noncomputable def run (e : Order ι) (z : ι → σ) : ℕ → Option Q
  | 0 => S.initSt
  | t + 1 =>
    if h : t < Fintype.card ι then
      S.step e t (e.symm ⟨t, h⟩) (run e z t) (z (e.symm ⟨t, h⟩))
    else run e z t

/-- **On promise inputs the automaton runs through the summary states.** -/
theorem run_read (e : Order ι) (x : X) :
    ∀ t, t ≤ Fintype.card ι → S.run e (read x) t = some (S.state x (preSet e t))
  | 0, _ => by
      have hX : Nonempty X := ⟨x⟩
      show S.initSt = _
      rw [initSt, dif_pos hX, preSet_zero, S.state_empty]
  | t + 1, ht => by
      have hlt : t < Fintype.card ι := by omega
      set i := e.symm ⟨t, hlt⟩ with hi
      have hex : ∃ y : X, S.state y (preSet e t) = S.state x (preSet e t)
          ∧ read y i = read x i := ⟨x, rfl, rfl⟩
      rw [run, dif_pos hlt, ← hi, run_read e x t (by omega), step, Option.bind_some,
        dif_pos hex, preSet_succ e hlt, ← hi]
      congr 1
      exact S.state_insert _ _ _ _ (hi ▸ notMem_preSet_symm e hlt)
        hex.choose_spec.1 hex.choose_spec.2

/-- The step at coordinate `i` is taken at time `e i`. -/
lemma run_rank_succ (e : Order ι) (z : ι → σ) (i : ι) :
    S.run e z ((e i : ℕ) + 1) = S.step e (e i) i (S.run e z (e i)) (z i) := by
  rw [run, dif_pos (e i).2]
  simp only [Fin.eta, Equiv.symm_apply_apply]

/-- **Equal branch prefixes give equal node states.** -/
lemma run_rank_congr (e : Order ι) {z w : ι → σ} {i : ι}
    (h : ∀ j, e j < e i → S.run e z ((e j : ℕ) + 1) = S.run e w ((e j : ℕ) + 1)) :
    S.run e z (e i) = S.run e w (e i) := by
  by_cases h0 : (e i : ℕ) = 0
  · rw [h0]
    rfl
  · have hk : (e i : ℕ) - 1 < Fintype.card ι := by have := (e i).2; omega
    set j := e.symm ⟨(e i : ℕ) - 1, hk⟩ with hj
    have hej : ((e j : ℕ)) = (e i : ℕ) - 1 := by rw [hj, Equiv.apply_symm_apply]
    have hlt : e j < e i := by rw [Fin.lt_def, hej]; omega
    have hsucc : (e j : ℕ) + 1 = (e i : ℕ) := by omega
    have := h j hlt
    rwa [hsucc] at this

open scoped Classical in
/-- The final readout of the automaton: the output of a promise input with that final
state, or junk. -/
noncomputable def readOut (oq : Option Q) : Option O :=
  oq.bind fun q =>
    if h : ∃ x : X, S.state x Finset.univ = q then some (S.out h.choose) else none

lemma readOut_run_read (e : Order ι) (x : X) :
    S.readOut (S.run e (read x) (Fintype.card ι)) = some (S.out x) := by
  have hex : ∃ y : X, S.state y Finset.univ = S.state x Finset.univ := ⟨x, rfl⟩
  rw [S.run_read e x _ le_rfl, preSet_card, readOut, Option.bind_some, dif_pos hex]
  exact congrArg some (S.out_congr _ _ hex.choose_spec)

variable [Nonempty ι]

/-- **The total scan attached to a promise summary and an order.**  The branch at `i` is
the automaton state after scanning `i`; red means the state changed. -/
noncomputable def extScan (e : Order ι) : Scan ι σ (Option O) (Option Q) where
  rank := ⇑e
  rank_inj := e.injective
  br z i := S.run e z ((e i : ℕ) + 1)
  col z i := decide (S.run e z ((e i : ℕ) + 1) ≠ S.run e z (e i))
  out z := S.readOut (S.run e z (Fintype.card ι))
  br_ne z w i hpre hbr hzw := by
    refine hbr ?_
    rw [S.run_rank_succ e z i, S.run_rank_succ e w i, S.run_rank_congr e hpre, hzw]
  out_eq z w h := by
    have hn : Fintype.card ι - 1 < Fintype.card ι := by
      have := Fintype.card_pos (α := ι); omega
    set j := e.symm ⟨Fintype.card ι - 1, hn⟩ with hj
    have hej : (e j : ℕ) + 1 = Fintype.card ι := by
      rw [hj, Equiv.apply_symm_apply]
      have := Fintype.card_pos (α := ι)
      show Fintype.card ι - 1 + 1 = Fintype.card ι
      omega
    have := h j
    rw [hej] at this
    rw [this]
  black_unique z w i hz hw hpre := by
    simp only [decide_eq_false_iff_not, not_not] at hz hw
    show S.run e z ((e i : ℕ) + 1) = S.run e w ((e i : ℕ) + 1)
    rw [hz, hw]
    exact S.run_rank_congr e hpre

/-- The summary's own colour of a promise input: did scanning `i` change the state? -/
def pCol (e : Order ι) (x : X) (i : ι) : Bool :=
  decide (S.state x (preSet e ((e i : ℕ) + 1)) ≠ S.state x (preSet e (e i)))

lemma extScan_col_read (e : Order ι) (x : X) (i : ι) :
    (S.extScan e).col (read x) i = S.pCol e x i := by
  show decide (S.run e (read x) ((e i : ℕ) + 1) ≠ S.run e (read x) (e i)) = _
  rw [S.run_read e x _ (by have := (e i).2; omega), S.run_read e x _ (e i).2.le, pCol]
  simp only [ne_eq, Option.some.injEq]

/-- **The red event is essentiality at the top of the prefix.** -/
lemma pCol_symm_iff (e : Order ι) (x : X) (t : Fin (Fintype.card ι)) :
    S.pCol e x (e.symm t) = true ↔ e.symm t ∈ S.essentialSet x (prefixSet e t) := by
  rw [pCol, decide_eq_true_iff, S.mem_essentialSet, Equiv.apply_symm_apply,
    preSet_succ_eq_prefixSet, ← beforeSet_eq_erase,
    ← preSet_rank_eq_beforeSet, Equiv.apply_symm_apply]
  have hmem : e.symm t ∈ prefixSet e t := by
    rw [mem_prefixSet, Equiv.apply_symm_apply]
  exact ⟨fun h => ⟨hmem, h⟩, fun h => h.2⟩

/-- **The red count on the promise**: at most a `B/(t+1)` fraction of orders are red at
time `t`, for every promise input of essential width at most `B`. -/
theorem card_red_mul_le_of_bound {B : ℕ} (x : X)
    (hB : ∀ T : Finset ι, (S.essentialSet x T).card ≤ B) (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) * (Finset.univ.filter fun e : Order ι =>
        S.pCol e x (e.symm t) = true).card
      ≤ B * Fintype.card (Order ι) := by
  classical
  have hset : (Finset.univ.filter fun e : Order ι => S.pCol e x (e.symm t) = true)
      = essEvent (S.essentialSet x) t t := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_essEvent]
    exact S.pCol_symm_iff e x t
  rw [hset]
  exact card_essEvent_mul_le_of_bound (S.essentialSet x)
    (fun T => S.essentialSet_subset x T) hB t

end PromiseSummary

/-! ## Averaging promise duals -/

section Average

variable {read : X → ι → σ} {f : X → O} {Z K : Type} [Fintype Z] [Nonempty Z] [Fintype K]

/-- **The uniform average of promise dual solutions for the same function** (the promise
mirror of `DualPair.averageUnif`). -/
noncomputable def dualPairOnAvg (P : Z → DualPairOn read K f) : DualPairOn read (Z × K) f where
  u x i zk := Real.sqrt (Fintype.card Z : ℝ)⁻¹ * (P zk.1).u x i zk.2
  v y i zk := Real.sqrt (Fintype.card Z : ℝ)⁻¹ * (P zk.1).v y i zk.2
  constraint x y := by
    set N : ℝ := (Fintype.card Z : ℝ) with hN
    have hN0 : (0 : ℝ) ≤ N⁻¹ := by positivity
    have hpt : ∀ i : ι,
        (∑ zk : Z × K, (Real.sqrt N⁻¹ * (P zk.1).u x i zk.2) *
          (Real.sqrt N⁻¹ * (P zk.1).v y i zk.2))
        = ∑ z : Z, N⁻¹ * ∑ k : K, (P z).u x i k * (P z).v y i k := by
      intro i
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (Real.sqrt N⁻¹ * (P z).u x i k) * (Real.sqrt N⁻¹ * (P z).v y i k)
          = (Real.sqrt N⁻¹ * Real.sqrt N⁻¹) * ((P z).u x i k * (P z).v y i k) from by
            ring, Real.mul_self_sqrt hN0]
    have hmask : ∀ i : ι,
        (if read x i = read y i then (0 : ℝ)
          else ∑ z : Z, N⁻¹ * ∑ k : K, (P z).u x i k * (P z).v y i k)
        = ∑ z : Z, N⁻¹ * (if read x i = read y i then (0 : ℝ)
            else ∑ k : K, (P z).u x i k * (P z).v y i k) := by
      intro i
      by_cases h : read x i = read y i
      · rw [if_pos h]
        exact (Finset.sum_eq_zero fun z _ => by rw [if_pos h, mul_zero]).symm
      · rw [if_neg h]
        exact Finset.sum_congr rfl fun z _ => by rw [if_neg h]
    simp only [hpt, hmask]
    rw [Finset.sum_comm]
    have hz : ∀ z : Z, (∑ i : ι, N⁻¹ * (if read x i = read y i then (0 : ℝ)
        else ∑ k : K, (P z).u x i k * (P z).v y i k))
        = N⁻¹ * (if f x = f y then 0 else 1) := by
      intro z
      rw [← Finset.mul_sum, (P z).constraint x y]
    rw [Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) => hz z, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hN,
      mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

/-- The averaged weighted squared mass is the average of the weighted squared masses. -/
lemma sum_dualPairOnAvg_sq (U : Z → X → ι → K → ℝ) (c : ι → ℝ) (x : X) :
    (∑ i : ι, c i * ∑ zk : Z × K,
        (Real.sqrt (Fintype.card Z : ℝ)⁻¹ * U zk.1 x i zk.2)
          * (Real.sqrt (Fintype.card Z : ℝ)⁻¹ * U zk.1 x i zk.2))
      = (Fintype.card Z : ℝ)⁻¹ * ∑ z : Z, ∑ i : ι, c i * ∑ k : K, U z x i k * U z x i k := by
  have hN0 : (0 : ℝ) ≤ (Fintype.card Z : ℝ)⁻¹ := by positivity
  have hcoord : ∀ i : ι, (∑ zk : Z × K,
        (Real.sqrt (Fintype.card Z : ℝ)⁻¹ * U zk.1 x i zk.2)
          * (Real.sqrt (Fintype.card Z : ℝ)⁻¹ * U zk.1 x i zk.2))
      = ∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * ∑ k : K, U z x i k * U z x i k := by
    intro i
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Real.sqrt (Fintype.card Z : ℝ)⁻¹ * U z x i k)
          * (Real.sqrt (Fintype.card Z : ℝ)⁻¹ * U z x i k)
        = (Real.sqrt (Fintype.card Z : ℝ)⁻¹ * Real.sqrt (Fintype.card Z : ℝ)⁻¹)
          * (U z x i k * U z x i k) from by ring, Real.mul_self_sqrt hN0]
  simp only [hcoord, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Average

/-! ## The essential-width theorem on a promise -/

namespace PromiseSummary

variable [Nonempty ι] {read : X → ι → σ} (S : PromiseSummary read O Q)

/-- The scan dual of one order, restricted to the promise and recoded to `f`. -/
noncomputable def orderDual (c : ι → ℝ) (B : ℕ) (hc : ∀ i, 0 < c i) (hB : 0 < B)
    (e : Order ι) : DualPairOn read (ScanDim ι (Option O) (Option Q)) S.out :=
  (((S.extScan e).dual (bWeight c B e) (bWeight_pos c B hc hB e)).restrictTo read).ofKer
    fun x y => by
      show S.readOut (S.run e (read x) _) = S.readOut (S.run e (read y) _) ↔ _
      rw [S.readOut_run_read e x, S.readOut_run_read e y, Option.some.injEq]

/-- The `u`-mass of one order's dual at a promise input and coordinate. -/
lemma orderDual_u_sq (c : ι → ℝ) (B : ℕ) (hc : ∀ i, 0 < c i) (hB : 0 < B) (e : Order ι)
    (x : X) (i : ι) :
    (∑ k, (S.orderDual c B hc hB e).u x i k * (S.orderDual c B hc hB e).u x i k)
      = 4 * (bWeight c B e i (S.pCol e x i))⁻¹ := by
  rw [← S.extScan_col_read e x i]
  exact (S.extScan e).sum_dual_u_sq_coord (bWeight c B e) (bWeight_pos c B hc hB e)
    (read x) i

/-- The `v`-mass of one order's dual at a promise input and coordinate. -/
lemma orderDual_v_sq (c : ι → ℝ) (B : ℕ) (hc : ∀ i, 0 < c i) (hB : 0 < B) (e : Order ι)
    (x : X) (i : ι) :
    (∑ k, (S.orderDual c B hc hB e).v x i k * (S.orderDual c B hc hB e).v x i k)
      = 4 * (bWeight c B e i true
          + if S.pCol e x i then bWeight c B e i false else 0) := by
  rw [← S.extScan_col_read e x i]
  exact (S.extScan e).sum_dual_v_sq_coord (bWeight c B e) (bWeight_pos c B hc hB e)
    (read x) i

/-- **The record term averages to at most `bBase`** on the promise. -/
lemma sum_orders_pRecTerm_le (c : ι → ℝ) (B : ℕ) (hc : ∀ i, 0 < c i) (hB : 0 < B) (x : X)
    (hwidth : ∀ T : Finset ι, (S.essentialSet x T).card ≤ B)
    (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, if S.pCol e x (e.symm t) then bScale c B ((t : ℕ)) else 0)
      ≤ (Fintype.card (Order ι) : ℝ) * bBase c B ((t : ℕ)) := by
  classical
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  set R := (Finset.univ.filter fun e : Order ι => S.pCol e x (e.symm t) = true).card
    with hRdef
  have hsplit : (∑ e : Order ι, if S.pCol e x (e.symm t) then bScale c B ((t : ℕ)) else 0)
      = (R : ℝ) * bScale c B ((t : ℕ)) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, add_zero,
      hRdef]
  have hcount : (((t : ℕ) : ℝ) + 1) * (R : ℝ) ≤ (B : ℝ) * (Fintype.card (Order ι) : ℝ) := by
    exact_mod_cast S.card_red_mul_le_of_bound x hwidth t
  rw [hsplit]
  refine le_of_mul_le_mul_left ?_ hBpos
  calc (B : ℝ) * ((R : ℝ) * bScale c B ((t : ℕ)))
      = (R : ℝ) * ((B : ℝ) * bScale c B ((t : ℕ))) := by ring
    _ = (R : ℝ) * ((((t : ℕ) : ℝ) + 1) * bBase c B ((t : ℕ))) := by
        rw [bScale_mul_budget c B hB]
    _ = ((((t : ℕ) : ℝ) + 1) * (R : ℝ)) * bBase c B ((t : ℕ)) := by ring
    _ ≤ ((B : ℝ) * (Fintype.card (Order ι) : ℝ)) * bBase c B ((t : ℕ)) :=
        mul_le_mul_of_nonneg_right hcount (bBase_nonneg c B hc _)
    _ = (B : ℝ) * ((Fintype.card (Order ι) : ℝ) * bBase c B ((t : ℕ))) := by ring

/-- The total, over all orders, of the per-coordinate bound (∗) at one promise input. -/
lemma sum_orders_bTerm_le (c : ι → ℝ) (B : ℕ) (hc : ∀ i, 0 < c i) (hB : 0 < B) (x : X)
    (hwidth : ∀ T : Finset ι, (S.essentialSet x T).card ≤ B) :
    (∑ e : Order ι, ∑ i : ι, bTerm c B i ((e i : ℕ)) (S.pCol e x i))
      ≤ (Fintype.card (Order ι) : ℝ) * (4 * (Real.sqrt B * costNorm c)) := by
  set N : ℝ := (Fintype.card (Order ι) : ℝ) with hNdef
  have hswap : ∀ e : Order ι,
      (∑ i : ι, bTerm c B i ((e i : ℕ)) (S.pCol e x i))
        = ∑ t : Fin (Fintype.card ι), bTerm c B (e.symm t) ((t : ℕ))
            (S.pCol e x (e.symm t)) := by
    intro e
    refine Fintype.sum_equiv e _ _ fun i => ?_
    rw [Equiv.symm_apply_apply]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hswap e, Finset.sum_comm]
  have hper : ∀ t : Fin (Fintype.card ι),
      (∑ e : Order ι, bTerm c B (e.symm t) ((t : ℕ)) (S.pCol e x (e.symm t)))
        ≤ N * (2 * bBase c B ((t : ℕ))) := by
    intro t
    simp only [bTerm]
    rw [Finset.sum_add_distrib, sum_orders_bCoordTerm c B hc hB t]
    have := S.sum_orders_pRecTerm_le c B hc hB x hwidth t
    rw [hNdef]
    linarith
  calc (∑ t : Fin (Fintype.card ι), ∑ e : Order ι,
        bTerm c B (e.symm t) ((t : ℕ)) (S.pCol e x (e.symm t)))
      ≤ ∑ t : Fin (Fintype.card ι), N * (2 * bBase c B ((t : ℕ))) :=
        Finset.sum_le_sum fun t _ => hper t
    _ = N * 2 * ∑ t : Fin (Fintype.card ι), bBase c B ((t : ℕ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    _ ≤ N * 2 * (2 * (Real.sqrt B * costNorm c)) :=
        mul_le_mul_of_nonneg_left (sum_bBase_le c B hc) (by positivity)
    _ = N * (4 * (Real.sqrt B * costNorm c)) := by ring

set_option maxHeartbeats 1000000 in
/-- **`thm:essential-width` on a promise, weighted** (`eq:weighted-width`): a promise
summary of essential width at most `B ≥ 1` on the promise gives a promise dual of
`c`-weighted cost at most `16·√B·(∑ᵢ cᵢ²)^{1/2}`. -/
theorem exists_dualPairOn_isWeightedCostLe {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : X) (T : Finset ι), (S.essentialSet x T).card ≤ B)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ P : DualPairOn read (Order ι × ScanDim ι (Option O) (Option Q)) S.out,
      P.IsWeightedCostLe c (16 * (Real.sqrt B * costNorm c)) := by
  have : Nonempty (Order ι) := ⟨Fintype.equivFin ι⟩
  set N : ℝ := (Fintype.card (Order ι) : ℝ) with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef, Nat.cast_pos]; exact Fintype.card_pos
  have hN' : N ≠ 0 := ne_of_gt hNpos
  set P : Order ι → DualPairOn read (ScanDim ι (Option O) (Option Q)) S.out :=
    S.orderDual c B hc hB with hPdef
  refine ⟨dualPairOnAvg P, ?_, ?_⟩
  · intro x
    have hmass : ∀ e : Order ι,
        (∑ i : ι, c i * ∑ k, (P e).u x i k * (P e).u x i k)
          ≤ 4 * ∑ i : ι, bTerm c B i ((e i : ℕ)) (S.pCol e x i) := by
      intro e
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hPdef, S.orderDual_u_sq c B hc hB e x i]
      rw [show c i * (4 * (bWeight c B e i (S.pCol e x i))⁻¹)
          = 4 * (c i * (bWeight c B e i (S.pCol e x i))⁻¹) from by ring]
      exact mul_le_mul_of_nonneg_left (bTerm_u_le c B hc hB e _ i) (by norm_num)
    show (∑ i : ι, c i * ∑ zk : Order ι × ScanDim ι (Option O) (Option Q),
        (Real.sqrt N⁻¹ * (P zk.1).u x i zk.2) * (Real.sqrt N⁻¹ * (P zk.1).u x i zk.2))
      ≤ _
    rw [sum_dualPairOnAvg_sq (fun e => (P e).u) c x]
    calc N⁻¹ * ∑ e : Order ι, (∑ i : ι, c i * ∑ k, (P e).u x i k * (P e).u x i k)
        ≤ N⁻¹ * ∑ e : Order ι, 4 * ∑ i : ι, bTerm c B i ((e i : ℕ)) (S.pCol e x i) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => hmass e) ?_
          positivity
      _ = N⁻¹ * (4 * ∑ e : Order ι, ∑ i : ι, bTerm c B i ((e i : ℕ)) (S.pCol e x i)) := by
          rw [← Finset.mul_sum]
      _ ≤ N⁻¹ * (4 * (N * (4 * (Real.sqrt B * costNorm c)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (S.sum_orders_bTerm_le c B hc hB x (hwidth x))
            (by norm_num)
      _ = 16 * (Real.sqrt B * costNorm c) := by
          rw [show N⁻¹ * (4 * (N * (4 * (Real.sqrt B * costNorm c))))
              = (N⁻¹ * N) * (16 * (Real.sqrt B * costNorm c)) from by ring,
            inv_mul_cancel₀ hN', one_mul]
  · intro y
    have hmass : ∀ e : Order ι,
        (∑ i : ι, c i * ∑ k, (P e).v y i k * (P e).v y i k)
          = 4 * ∑ i : ι, bTerm c B i ((e i : ℕ)) (S.pCol e y i) := by
      intro e
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hPdef, S.orderDual_v_sq c B hc hB e y i]
      rw [show c i * (4 * (bWeight c B e i true
            + if S.pCol e y i then bWeight c B e i false else 0))
          = 4 * (c i * (bWeight c B e i true
            + if S.pCol e y i then bWeight c B e i false else 0)) from by ring]
      rw [bTerm_v_eq c B hc hB e _ i]
    show (∑ i : ι, c i * ∑ zk : Order ι × ScanDim ι (Option O) (Option Q),
        (Real.sqrt N⁻¹ * (P zk.1).v y i zk.2) * (Real.sqrt N⁻¹ * (P zk.1).v y i zk.2))
      ≤ _
    rw [sum_dualPairOnAvg_sq (fun e => (P e).v) c y]
    calc N⁻¹ * ∑ e : Order ι, (∑ i : ι, c i * ∑ k, (P e).v y i k * (P e).v y i k)
        = N⁻¹ * ∑ e : Order ι, 4 * ∑ i : ι, bTerm c B i ((e i : ℕ)) (S.pCol e y i) := by
          rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hmass e]
      _ = N⁻¹ * (4 * ∑ e : Order ι, ∑ i : ι, bTerm c B i ((e i : ℕ)) (S.pCol e y i)) := by
          rw [← Finset.mul_sum]
      _ ≤ N⁻¹ * (4 * (N * (4 * (Real.sqrt B * costNorm c)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (S.sum_orders_bTerm_le c B hc hB y (hwidth y))
            (by norm_num)
      _ = 16 * (Real.sqrt B * costNorm c) := by
          rw [show N⁻¹ * (4 * (N * (4 * (Real.sqrt B * costNorm c))))
              = (N⁻¹ * N) * (16 * (Real.sqrt B * costNorm c)) from by ring,
            inv_mul_cancel₀ hN', one_mul]

/-- **`eq:weighted-width` on a promise, every budget `B ≥ 0`**: at `B = 0` the function is
constant on the promise and the zero solution has weighted cost `0`. -/
theorem exists_weightedDualOn {B : ℕ}
    (hwidth : ∀ (x : X) (T : Finset ι), (S.essentialSet x T).card ≤ B)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ (K : Type) (_ : Fintype K) (P : DualPairOn read K S.out),
      P.IsWeightedCostLe c (16 * (Real.sqrt B * costNorm c)) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · refine ⟨Empty, inferInstance,
      DualPairOn.const read S.out (S.out_const_of_width_zero hwidth), ?_, ?_⟩ <;>
    · intro x
      simp
  · obtain ⟨P, hP⟩ := S.exists_dualPairOn_isWeightedCostLe hB hwidth c hc
    exact ⟨_, inferInstance, P, hP⟩

/-- **`thm:essential-width` on a promise, unit costs, `B ≥ 1`**: `16·√(nB)`. -/
theorem exists_dualPairOn_isCostLe {B : ℕ} (hB : 0 < B)
    (hwidth : ∀ (x : X) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    ∃ P : DualPairOn read (Order ι × ScanDim ι (Option O) (Option Q)) S.out,
      P.IsCostLe (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) := by
  obtain ⟨P, hP⟩ := S.exists_dualPairOn_isWeightedCostLe hB hwidth
    (fun _ => 1) (fun _ => one_pos)
  have hnorm : costNorm (fun _ : ι => (1 : ℝ)) = Real.sqrt (Fintype.card ι) := by
    rw [costNorm]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hval : 16 * (Real.sqrt B * costNorm (fun _ : ι => (1 : ℝ)))
      = 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) := by
    rw [hnorm, Real.sqrt_mul (Nat.cast_nonneg _)]
    ring
  rw [hval] at hP
  exact ⟨P, fun x => by simpa using hP.1 x, fun y => by simpa using hP.2 y⟩

/-- **`thm:essential-width` on a promise, bundled, every `B ≥ 0`**:
`HasDualOn read f (16·√(nB))`. -/
theorem hasDualOn_of_width {B : ℕ}
    (hwidth : ∀ (x : X) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    HasDualOn read S.out (16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · exact (hasDualOn_of_const read (S.out_const_of_width_zero hwidth)).mono (by positivity)
  · obtain ⟨P, hP⟩ := S.exists_dualPairOn_isCostLe hB hwidth
    exact hasDualOn_of_dualPairOn P hP

/-- **The boxed `ADV±_D(f) ≤ 16·√(nB)`** (`thm:essential-width` on the promise domain),
every `B ≥ 0`. -/
theorem advPMOn_le_of_width {B : ℕ}
    (hwidth : ∀ (x : X) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    advPMOn read S.out ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) :=
  advPMOn_le_of_hasDualOn (by positivity) (S.hasDualOn_of_width hwidth)

/-- **Width zero: `ADV±_D(f) = 0`.** -/
theorem advPMOn_eq_zero_of_width_zero
    (hwidth : ∀ (x : X) (T : Finset ι), (S.essentialSet x T).card ≤ 0) :
    advPMOn read S.out = 0 := by
  refine le_antisymm ?_ (advPMOn_nonneg fun x y _ => S.out_const_of_width_zero hwidth x y)
  simpa using S.advPMOn_le_of_width hwidth

/-- **Width zero: zero queries on the promise** (the constant algorithm). -/
theorem qQueryOn_eq_zero_of_width_zero [Nonempty O]
    (hwidth : ∀ (x : X) (T : Finset ι), (S.essentialSet x T).card ≤ 0)
    {ε : ℝ} (hε : 0 ≤ ε) : qQueryOn read S.out ε = 0 := by
  by_cases h : Nonempty X
  · obtain ⟨x₀⟩ := h
    exact qQueryOn_const_eq_zero read (c := S.out x₀)
      (fun x => S.out_const_of_width_zero hwidth x x₀) hε
  · exact qQueryOn_const_eq_zero read (c := Classical.arbitrary O)
      (fun x => absurd ⟨x⟩ h) hε

/-- **`Q_{1/3}(f) = O(√(nB))` on the promise**: `Q_{1/3} ≤ 8192·(1 + 16·√(nB))` through the
cardinality-free extraction. -/
theorem qQueryOn_third_le_of_width [Nonempty O] {B : ℕ}
    (hwidth : ∀ (x : X) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    (qQueryOn read S.out (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + 16 * Real.sqrt ((Fintype.card ι : ℝ) * B)) :=
  qQueryOn_third_le_of_hasDualOn_uniform (S.hasDualOn_of_width hwidth) (by positivity)

end PromiseSummary

/-! ## The paper's `D ⊆ Σ^I`, and the total case -/

/-- **`thm:essential-width` for a promise set `D ⊆ Σ^I`** literally: the promise is the
subtype of `D`, read by inclusion. -/
theorem advPMOn_subtype_le_of_promiseSummary [Nonempty ι] {D : Finset (ι → σ)}
    (S : PromiseSummary (fun x : D => (x : ι → σ)) O Q) {B : ℕ}
    (hwidth : ∀ (x : D) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    advPMOn (fun x : D => (x : ι → σ)) S.out
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) :=
  S.advPMOn_le_of_width hwidth

/-- **Sanity: the total theorem is the case `D = Σ^I`.**  `advPM_le_of_summary_nonneg`
(`Width/Main.lean`) re-derived from the promise theorem through `PromiseSummary.ofTotal`. -/
theorem PromiseSummary.advPM_le_of_ofTotal [Nonempty ι] (S : IncrementalSummary ι σ O Q)
    {B : ℕ} (hwidth : ∀ (x : ι → σ) (T : Finset ι), (S.essentialSet x T).card ≤ B) :
    advPM S.out ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) := by
  have h := (PromiseSummary.ofTotal S).advPMOn_le_of_width (B := B) fun x T => by
    rw [ofTotal_essentialSet]
    exact hwidth x T
  exact h

end MonoidProduct
