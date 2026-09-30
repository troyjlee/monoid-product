import MonoidProduct.Aperiodic.CubeRoot.FiniteAction
import QuantumQueryComplexity.Adaptive
import MonoidProduct.Aperiodic.EqProd
import QuantumQueryComplexity.BinarySearch
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Axis packets: the exact endpoint and the first death

An **axis packet**, from a supplied live start state, returns
either the exact final live state or the first position at which the
trajectory dies, together with its exact live predecessor.  One output
carries both branches: the **greatest live cut** `k` together with the state
there.  `k = n` says the run survived and the state is the endpoint; `k < n`
says letter `k` killed it and the state is the exact live predecessor.

Everything is assembled from **one** supplied primitive: for each cut `j` and
each live state `s`, a dual for the equality test

    `x ↦ [state after the first j letters = s]`.

Two disciplines shape the assembly, and both are forced at the dual level
rather than the algorithmic one:

* **The endpoint is the whole one-hot family, never a single test.**  One
  equality test cannot produce an exact endpoint.  The family over all
  `s : S` can, and `HasDual.combine'` composes it with the decoding map in
  one step.
* **The live-prefix predicate is built directly as the Boolean OR of the
  same tests**, never by postprocessing the endpoint — deadness is then its
  negation, taken in `cutThreshold`.  Postcomposition is *not* free for
  `HasDual`: a dual for `f` is not a dual for `g ∘ f` when `g` merges two
  `f`-values, and "is the state live" merges every live state into `true`.
  (It becomes free only after extraction, as operational postprocessing.)
  So `liveAt` is compiled by `HasDual.finsetSup` from the tests themselves.

The supplied primitive is exactly what the action compiler (`ActionCompiler`,
`ActionTarget`, `AxisRecurrence`) produces recursively, through the target
action and the regular-height drop.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Cuts

variable {σ M S : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [Fintype S] [DecidableEq S]
variable (A : RightAction M (Option S)) (start : S) (letter : σ → M)

/-! ## The trajectory, cut by cut -/

/-- The state after the first `j` letters, from the supplied start. -/
def cutState {n : ℕ} (x : Fin n → σ) (j : ℕ) : Option S :=
  A.act (some start) (winProd letter x 0 j)

@[simp] lemma cutState_zero {n : ℕ} (x : Fin n → σ) :
    cutState A start letter x 0 = some start := by
  rw [cutState, winProd, rangeProd_eq_one_of_le _ le_rfl, A.act_one]

/-- **Death is permanent along the cuts**, given an absorbing dead state —
which is what the killed and target actions provide. -/
lemma cutState_eq_none_of_le (hnone : ∀ a, A.act none a = none) {n : ℕ}
    (x : Fin n → σ) {j j' : ℕ} (hj : j ≤ j')
    (h : cutState A start letter x j = none) :
    cutState A start letter x j' = none := by
  rw [cutState, winProd, ← rangeProd_split _ (Nat.zero_le j) hj, ← A.act_mul]
  rw [cutState, winProd] at h
  rw [h, hnone]

/-- The cuts at which the run is still live. -/
def liveSet {n : ℕ} (x : Fin n → σ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun j => (cutState A start letter x j).isSome

lemma mem_liveSet {n : ℕ} {x : Fin n → σ} {j : ℕ} :
    j ∈ liveSet A start letter x ↔ j ≤ n ∧ (cutState A start letter x j).isSome := by
  simp [liveSet]

lemma liveSet_nonempty {n : ℕ} (x : Fin n → σ) : (liveSet A start letter x).Nonempty :=
  ⟨0, (mem_liveSet A start letter).2 ⟨Nat.zero_le n, by rw [cutState_zero]; rfl⟩⟩

/-- **The greatest live cut.**

For a general action this is only what its name says: the largest `j ≤ n` at
which the run is live.  The **first-death** reading — every earlier cut live,
the next one dead — needs the dead state to be absorbing (`hnone`), which is
the standing hypothesis of `hasDual_axisPacket` and holds for both the killed
and the target action.  `cutState_isSome_of_le` and
`cutState_succ_eq_none` below are those two semantic halves. -/
noncomputable def liveCut {n : ℕ} (x : Fin n → σ) : ℕ :=
  (liveSet A start letter x).max' (liveSet_nonempty A start letter x)

lemma liveCut_le {n : ℕ} (x : Fin n → σ) : liveCut A start letter x ≤ n :=
  ((mem_liveSet A start letter).1
    ((liveSet A start letter x).max'_mem (liveSet_nonempty A start letter x))).1

lemma liveCut_isSome {n : ℕ} (x : Fin n → σ) :
    (cutState A start letter x (liveCut A start letter x)).isSome :=
  ((mem_liveSet A start letter).1
    ((liveSet A start letter x).max'_mem (liveSet_nonempty A start letter x))).2

lemma cutState_eq_none_of_gt {n : ℕ} (x : Fin n → σ) {j : ℕ}
    (hj : liveCut A start letter x < j) (hjn : j ≤ n) :
    cutState A start letter x j = none := by
  by_contra h
  have hmem : j ∈ liveSet A start letter x :=
    (mem_liveSet A start letter).2 ⟨hjn, Option.isSome_iff_ne_none.2 h⟩
  have hle : j ≤ liveCut A start letter x :=
    (liveSet A start letter x).le_max' j hmem
  omega

/-- **Under absorption, every earlier cut is live.** -/
lemma cutState_isSome_of_le (hnone : ∀ a, A.act none a = none) {n : ℕ}
    (x : Fin n → σ) {j : ℕ} (hj : j ≤ liveCut A start letter x) :
    (cutState A start letter x j).isSome := by
  by_contra h
  have hdead := cutState_eq_none_of_le A start letter hnone x hj
    (Option.not_isSome_iff_eq_none.1 h)
  have hlive := liveCut_isSome A start letter x
  rw [hdead] at hlive
  exact absurd hlive (by simp)

/-- **And the next one is dead**, when there is one. -/
lemma cutState_succ_eq_none {n : ℕ} (x : Fin n → σ)
    (h : liveCut A start letter x < n) :
    cutState A start letter x (liveCut A start letter x + 1) = none :=
  cutState_eq_none_of_gt A start letter x (Nat.lt_succ_self _) (by omega)

/-- **The threshold characterization of the cut**: `liveCut x ≤ q` exactly
when the run is already dead one step past `q`, or `q` is past the end. -/
lemma liveCut_le_iff (hnone : ∀ a, A.act none a = none) {n : ℕ} (x : Fin n → σ)
    (q : ℕ) : liveCut A start letter x ≤ q
      ↔ (n ≤ q ∨ cutState A start letter x (q + 1) = none) := by
  constructor
  · intro h
    by_cases hq : n ≤ q
    · exact Or.inl hq
    · exact Or.inr (cutState_eq_none_of_gt A start letter x (by omega) (by omega))
  · rintro (hq | hq)
    · exact le_trans (liveCut_le A start letter x) hq
    · by_contra hc
      have hdead := cutState_eq_none_of_le A start letter hnone x
        (show q + 1 ≤ liveCut A start letter x by omega) hq
      have hlive := liveCut_isSome A start letter x
      rw [hdead] at hlive
      exact absurd hlive (by simp)

/-! ## The supplied primitive, and the two things built from it -/

/-- The equality test at cut `j` against the live state `s`. -/
def cutTest {n : ℕ} (x : Fin n → σ) (j : ℕ) (s : S) : Bool :=
  decide (cutState A start letter x j = some s)

/-- Decoding a one-hot vector of tests back to a state. -/
noncomputable def decodeOneHot (v : S → Bool) : Option S :=
  if h : ∃ s, v s = true then some h.choose else none

lemma decodeOneHot_cutTest {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    decodeOneHot (cutTest A start letter x j) = cutState A start letter x j := by
  rw [decodeOneHot]
  by_cases h : ∃ s, cutTest A start letter x j s = true
  · rw [dif_pos h]
    have := h.choose_spec
    rw [cutTest, decide_eq_true_eq] at this
    exact this.symm
  · rw [dif_neg h]
    cases hc : cutState A start letter x j with
    | none => rfl
    | some s => exact absurd ⟨s, by rw [cutTest, hc]; simp⟩ h

/-- **Step 2: the exact state at a cut**, assembled from the whole one-hot
family of equality tests at that cut. -/
theorem hasDual_cutState {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (j : ℕ)
    (htest : ∀ s : S, HasDual (fun x : Fin n → σ => cutTest A start letter x j s) c) :
    HasDual (fun x : Fin n → σ => cutState A start letter x j)
      (2 * ((Fintype.card S : ℝ) * c)) := by
  have h := HasDual.combine' (ι := Fin n) (σ := σ) (Pi := S) (V := Bool)
    (O' := Option S) decodeOneHot (g := fun s x => cutTest A start letter x j s)
    (c := fun _ => c) (fun _ => hc) htest
  refine (h.ofEq fun x => decodeOneHot_cutTest A start letter x j).mono (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Is the run still live after `j` letters?  **Step 3**: the Boolean OR of
the very same tests, compiled by `finsetSup` — not a postprocessing of the
state, which would merge level sets. -/
noncomputable def liveAt {n : ℕ} (x : Fin n → σ) (j : ℕ) : Bool :=
  (Finset.univ : Finset S).sup fun s => cutTest A start letter x j s

lemma liveAt_eq_true_iff {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    liveAt A start letter x j = true ↔ (cutState A start letter x j).isSome := by
  rw [liveAt, sup_bool_eq_true]
  constructor
  · rintro ⟨s, -, hs⟩
    rw [cutTest, decide_eq_true_eq] at hs
    rw [hs]
    rfl
  · intro h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
    exact ⟨s, Finset.mem_univ s, by rw [cutTest, hs]; simp⟩

/-- **Step 3, priced.** -/
theorem hasDual_liveAt {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (j : ℕ)
    (htest : ∀ s : S, HasDual (fun x : Fin n → σ => cutTest A start letter x j s) c) :
    HasDual (fun x : Fin n → σ => liveAt A start letter x j)
      (c * (24 * Real.sqrt ((Fintype.card S : ℝ) + 1))) := by
  have h := HasDual.finsetSup (ι := Fin n) (σ := σ) (A := Bool)
    (Finset.univ : Finset S) hc fun s _ => htest s
  rw [Finset.card_univ] at h
  exact h

/-! ## Step 4: the greatest live cut, by threshold search

`liveCut` is the threshold of an antitone predicate, so binary search finds
it in `⌈log₂(n+1)⌉` tests.  The threshold test at `q` is *not* derived from
the cut — it is the dead-prefix predicate one step past `q`, compiled
directly from the equality tests. -/

/-- The threshold test of the cut: `[liveCut x ≤ q]`. -/
noncomputable def cutThreshold {n : ℕ} (q : ℕ) (x : Fin n → σ) : Bool :=
  if n ≤ q then true else !(liveAt A start letter x (q + 1))

lemma cutThreshold_eq (hnone : ∀ a, A.act none a = none) {n : ℕ} (q : ℕ)
    (x : Fin n → σ) :
    cutThreshold A start letter q x = decide (liveCut A start letter x ≤ q) := by
  rw [cutThreshold]
  by_cases hq : n ≤ q
  · rw [if_pos hq, eq_comm, decide_eq_true_eq]
    exact le_trans (liveCut_le A start letter x) hq
  · rw [if_neg hq]
    rcases hlive : liveAt A start letter x (q + 1) with _ | _
    · have hnone' : cutState A start letter x (q + 1) = none := by
        rcases hc : cutState A start letter x (q + 1) with _ | s
        · rfl
        · exact absurd ((liveAt_eq_true_iff A start letter x (q + 1)).2
            (by rw [hc]; rfl)) (by rw [hlive]; simp)
      simp only [Bool.not_false]
      exact (decide_eq_true
        ((liveCut_le_iff A start letter hnone x q).2 (Or.inr hnone'))).symm
    · simp only [Bool.not_true]
      refine (decide_eq_false ?_).symm
      intro hle
      rcases (liveCut_le_iff A start letter hnone x q).1 hle with h | h
      · exact hq h
      · have hs := (liveAt_eq_true_iff A start letter x (q + 1)).1 hlive
        rw [h] at hs
        exact absurd hs (by simp)

theorem hasDual_cutThreshold {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (q : ℕ)
    (htest : ∀ j, j ≤ n → ∀ s : S,
      HasDual (fun x : Fin n → σ => cutTest A start letter x j s) c) :
    HasDual (fun x : Fin n → σ => cutThreshold A start letter q x)
      (c * (24 * Real.sqrt ((Fintype.card S : ℝ) + 1))) := by
  by_cases hq : n ≤ q
  · have heq : ∀ x : Fin n → σ, cutThreshold A start letter q x = true := fun x => by
      simp only [cutThreshold, if_pos hq]
    exact (hasDual_const (f := fun x : Fin n → σ => cutThreshold A start letter q x)
      fun x y => by rw [heq, heq]).mono (by positivity)
  · have heq : ∀ x : Fin n → σ,
        cutThreshold A start letter q x = !(liveAt A start letter x (q + 1)) := fun x => by
      simp only [cutThreshold, if_neg hq]
    exact (hasDual_liveAt A start letter hc (q + 1)
        (htest (q + 1) (by omega))).ofKer
      fun x y => by
        rw [heq, heq]
        cases liveAt A start letter x (q + 1) <;>
          cases liveAt A start letter y (q + 1) <;> simp

/-- **Step 4.**  The greatest live cut costs `⌈log₂(n+1)⌉` dead-prefix
tests. -/
theorem hasDual_liveCut (hnone : ∀ a, A.act none a = none) {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ}
    (htest : ∀ j, j ≤ n → ∀ s : S,
      HasDual (fun x : Fin n → σ => cutTest A start letter x j s) c) :
    HasDual (fun x : Fin n → σ => liveCut A start letter x)
      ((Nat.clog 2 (n + 1) : ℝ) * (c * (24 * Real.sqrt ((Fintype.card S : ℝ) + 1)))) := by
  refine HasDual.of_hasDualOn_id (hasDualOn_thresholdSearch
    (L := Nat.clog 2 (n + 1)) (ans := fun x => liveCut A start letter x)
    (test := fun q x => cutThreshold A start letter q x) ?_ ?_ ?_)
  · intro x
    exact lt_of_le_of_lt (liveCut_le A start letter x)
      (lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_pow_clog (by norm_num) _))
  · intro q x
    exact cutThreshold_eq A start letter hnone q x
  · intro q
    exact (hasDual_cutThreshold A start letter hc q htest).hasDualOn

/-! ## Step 5: the packet — the cut together with the state there

An adaptive call: the descriptor is the cut, and the branch at cut `j` is the
exact state at `j`.  Only the branch actually taken is paid for, so the state
costs one family, not `n` of them. -/

/-- The cut, as an index into `Fin (n+1)`. -/
noncomputable def liveCutIdx {n : ℕ} (x : Fin n → σ) : Fin (n + 1) :=
  ⟨liveCut A start letter x, Nat.lt_succ_of_le (liveCut_le A start letter x)⟩

@[simp] lemma liveCutIdx_val {n : ℕ} (x : Fin n → σ) :
    (liveCutIdx A start letter x : ℕ) = liveCut A start letter x := rfl

/-- **The axis packet.**  From the supplied live start, the greatest live cut
together with the exact state there: the endpoint when the cut is `n`, the
first-death position with its exact live predecessor when it is smaller. -/
theorem hasDual_axisPacket (hnone : ∀ a, A.act none a = none) {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ}
    (htest : ∀ j, j ≤ n → ∀ s : S,
      HasDual (fun x : Fin n → σ => cutTest A start letter x j s) c) :
    HasDual (fun x : Fin n → σ =>
        (liveCutIdx A start letter x,
          cutState A start letter x (liveCut A start letter x)))
      ((Nat.clog 2 (n + 1) : ℝ) * (c * (24 * Real.sqrt ((Fintype.card S : ℝ) + 1)))
        + 2 * ((Fintype.card S : ℝ) * c)) := by
  have hD : HasDual (fun x : Fin n → σ => liveCutIdx A start letter x)
      ((Nat.clog 2 (n + 1) : ℝ)
        * (c * (24 * Real.sqrt ((Fintype.card S : ℝ) + 1)))) :=
    (hasDual_liveCut A start letter hnone hc htest).ofKer fun x y => by
      constructor
      · intro h; exact Fin.ext h
      · intro h; exact congrArg Fin.val h
  exact HasDual.adaptiveCall
    (T := fun (j : Fin (n + 1)) (x : Fin n → σ) => cutState A start letter x (j : ℕ)) hD
    fun j => hasDual_cutState A start letter hc (j : ℕ)
      (htest (j : ℕ) (Nat.lt_succ_iff.1 j.isLt))

/-! ## Step 6: the zero-length packet -/

/-- On the empty word the run is the start state and the cut is `0`: no
queries at all. -/
@[simp] lemma liveCut_zero_length (x : Fin 0 → σ) : liveCut A start letter x = 0 :=
  Nat.le_zero.1 (liveCut_le A start letter x)

/-- The horizon-zero packet, in **the same shape** as `hasDual_axisPacket`,
so it discharges that case directly. -/
theorem hasDual_packet_zero_length :
    HasDual (fun x : Fin 0 → σ =>
        (liveCutIdx A start letter x,
          cutState A start letter x (liveCut A start letter x)))
      0 := by
  refine hasDual_const fun x y => ?_
  have h : ∀ z : Fin 0 → σ, liveCutIdx A start letter z = ⟨0, Nat.zero_lt_one⟩ :=
    fun z => Fin.ext (by rw [liveCutIdx_val, liveCut_zero_length])
  rw [h, h, liveCut_zero_length, liveCut_zero_length, cutState_zero, cutState_zero]

end Cuts

end MonoidProduct
