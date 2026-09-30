import MonoidProduct.Ordered.MergeSeeded

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# Rank summaries

The ambient word has length `N`; the dyadic interval `(j, q)` is
`[q·2^j, (q+1)·2^j)`.  A seeded procedure `summary r j q ω` returns a record:

* length-one intervals return the exact letter record at every rank;
* rank `0` on longer intervals returns the empty record;
* rank `r+1` on `(j+1, q)`: at every depth `d < j+1` the merger is run on the
  candidates "compress the union of the two rank-`r` child summaries of a node
  of depth `d`" (node and child seeds drawn from the seed table `ω d`), and the
  compression of the union of the depths' outputs is returned.

Every seed gives a truthful record of at most `b` positions inside the interval
(`summary_truthful`, `summary_supp_subset`, `summary_card_le`), and every seed's
function has a dual of cost `costA r j` (`hasDual_summary`), the cost recurrence
before its numerical solution (solved in `Cost.lean`).  Correctness with high
probability is `Correct.lean`.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

section Summary

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) {N : ℕ}

/-! ## Intervals -/

/-- The dyadic interval `(j, q)`. -/
def ivl (j q : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => q * 2 ^ j ≤ (i : ℕ) ∧ (i : ℕ) < (q + 1) * 2 ^ j

lemma mem_ivl {j q : ℕ} {i : Fin N} :
    i ∈ ivl (N := N) j q ↔ q * 2 ^ j ≤ (i : ℕ) ∧ (i : ℕ) < (q + 1) * 2 ^ j := by
  simp [ivl]

/-- The two children of a node of depth `d` inside `(j + 1, q)`. -/
lemma ivl_child_subset {j q d ν : ℕ} (hd : d ≤ j) (hν : ν < 2 ^ d) (c : ℕ) (hc : c < 2) :
    ivl (N := N) (j - d) (2 * (q * 2 ^ d + ν) + c) ⊆ ivl (j + 1) q := by
  intro i hi
  rw [mem_ivl] at hi ⊢
  have h2 : 2 ^ (j + 1) = 2 * 2 ^ d * 2 ^ (j - d) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (j - d) := by positivity
  constructor
  · nlinarith [hi.1]
  · nlinarith [hi.2]

/-- The positions of a length-one interval. -/
lemma ivl_zero (q : ℕ) (hq : q < N) : ivl (N := N) 0 q = {⟨q, hq⟩} := by
  ext i
  simp only [mem_ivl, pow_zero, mul_one, Finset.mem_singleton, Fin.ext_iff]
  omega

/-! ## Summaries -/

/-- **An `r`-summary of the interval `(j, q)`.** -/
structure IsSummary (x : Fin N → σ) (b r j q : ℕ) (K : Record N σ) : Prop where
  truthful : K.Truthful x
  supp_subset : K.supp ⊆ ivl j q
  card_le : K.supp.card ≤ b
  dom : ∀ U ⊆ ivl j q, U.card ≤ r → subwordProd letter x U ≤ K.prod letter

/-! ## Seed spaces -/

/-- Merger parameters at a depth with `h` nodes: rounds and proposals per draw. -/
abbrev MParams := ℕ → ℕ × ℕ

/-- **The seed spaces**, by rank: at rank `r + 1` on log-length `j + 1`, one merger
seed table per depth `d`, whose candidate seeds are a node and two rank-`r` seeds. -/
def Ω (b : ℕ) (P : MParams) : ℕ → ℕ → Type
  | 0, _ => Unit
  | _ + 1, 0 => Unit
  | r + 1, j + 1 => (d : Fin (j + 1)) →
      (Fin (P (2 ^ (d : ℕ))).1 → Fin (2 * b) → Fin (P (2 ^ (d : ℕ))).2
        → (Fin (2 ^ (d : ℕ)) × Ω b P r (j - d) × Ω b P r (j - d)))

def fintypeΩ (b : ℕ) (P : MParams) : ∀ r j, Fintype (Ω b P r j)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | _ + 1, 0 => inferInstanceAs (Fintype Unit)
  | r + 1, j + 1 =>
      letI : ∀ j', Fintype (Ω b P r j') := fun j' => fintypeΩ b P r j'
      inferInstanceAs (Fintype ((d : Fin (j + 1)) →
        (Fin (P (2 ^ (d : ℕ))).1 → Fin (2 * b) → Fin (P (2 ^ (d : ℕ))).2
          → (Fin (2 ^ (d : ℕ)) × Ω b P r (j - d) × Ω b P r (j - d)))))

def decEqΩ (b : ℕ) (P : MParams) : ∀ r j, DecidableEq (Ω b P r j)
  | 0, _ => inferInstanceAs (DecidableEq Unit)
  | _ + 1, 0 => inferInstanceAs (DecidableEq Unit)
  | r + 1, j + 1 =>
      letI : ∀ j', DecidableEq (Ω b P r j') := fun j' => decEqΩ b P r j'
      letI : ∀ j', Fintype (Ω b P r j') := fun j' => fintypeΩ b P r j'
      inferInstanceAs (DecidableEq ((d : Fin (j + 1)) →
        (Fin (P (2 ^ (d : ℕ))).1 → Fin (2 * b) → Fin (P (2 ^ (d : ℕ))).2
          → (Fin (2 ^ (d : ℕ)) × Ω b P r (j - d) × Ω b P r (j - d)))))

instance instFintypeΩ {b : ℕ} {P : MParams} {r j : ℕ} : Fintype (Ω b P r j) := fintypeΩ b P r j
instance instDecidableEqΩ {b : ℕ} {P : MParams} {r j : ℕ} : DecidableEq (Ω b P r j) :=
  decEqΩ b P r j

/-! ## The summary function -/

/-- The exact letter record of position `p`. -/
def letterRec (x : Fin N → σ) (p : Fin N) : Record N σ := fun i => if i = p then some (x i) else none

lemma letterRec_truthful (x : Fin N → σ) (p : Fin N) : (letterRec x p).Truthful x := by
  intro i s h
  simp only [letterRec] at h
  split_ifs at h with hi
  exact Option.some.inj h

lemma supp_letterRec (x : Fin N → σ) (p : Fin N) : (letterRec x p).supp = {p} := by
  ext i
  simp only [Record.supp, mem_optSupp, letterRec, Finset.mem_singleton]
  split_ifs with h <;> simp [h]

theorem hasDual_letterRec (p : Fin N) : HasDual (fun x : Fin N → σ => letterRec x p) 2 := by
  refine (hasDual_ofCoord p (fun s : σ => (fun i => if i = p then some s else none : Record N σ))).ofEq
    fun x => ?_
  funext i
  simp only [letterRec]
  split_ifs with h
  · rw [h]
  · rfl

/-- The record of the letter at the natural position `q` (empty if out of range). -/
def letterRecN (x : Fin N → σ) (q : ℕ) : Record N σ :=
  if h : q < N then letterRec x ⟨q, h⟩ else emptyRec

/-- **The seeded summary.** -/
noncomputable def summary (b : ℕ) (P : MParams) :
    ∀ (r j : ℕ), ℕ → Ω b P r j → (Fin N → σ) → Record N σ
  | _, 0, q, _, x => letterRecN x q
  | 0, _ + 1, _, _, _ => emptyRec
  | r + 1, j + 1, q, ω, x =>
      Record.compress letter b (unionList (List.ofFn fun d : Fin (j + 1) =>
        mergeK letter b (P (2 ^ (d : ℕ))).1 (fun ρ i t =>
          Record.compress letter b
            ((summary b P r (j - d) (2 * (q * 2 ^ (d : ℕ) + ((ω d ρ i t).1 : ℕ))) (ω d ρ i t).2.1 x).union
              (summary b P r (j - d) (2 * (q * 2 ^ (d : ℕ) + ((ω d ρ i t).1 : ℕ)) + 1) (ω d ρ i t).2.2 x)))))

/-! ## Batches and unions -/

/-- A union-closed property holding on a list holds on its union. -/
lemma unionList_forall (Q : Record N σ → Prop) (hQ0 : Q emptyRec)
    (hQu : ∀ A B, Q A → Q B → Q (A.union B)) :
    ∀ l : List (Record N σ), (∀ A ∈ l, Q A) → Q (unionList l)
  | [], _ => hQ0
  | A :: l, h => hQu _ _ (h A (List.mem_cons_self ..))
      (unionList_forall Q hQ0 hQu l fun B hB => h B (List.mem_cons_of_mem _ hB))

/-- Every saved record of a run inherits a union-closed property of the entries (the saved
records are accumulated unions, so the property must be closed under `union` and hold for
the empty record). -/
lemma mergeRun_forall_of_entries {b : ℕ} (hb1 : 1 ≤ b) {k : ℕ} (Q : Record N σ → Prop)
    (hQ : ∀ {m : ℕ} (y : Fin m → Record N σ), (∀ i, Q (y i)) → Q (unionTuple y))
    (hQ0 : Q emptyRec) (hQu : ∀ A B, Q A → Q B → Q (A.union B)) :
    ∀ (R : ℕ) (completed : List (Record N σ)), (∀ A ∈ completed, Q A) →
      ∀ tbl : Fin R → Fin (2 * b) → Fin k → Record N σ, (∀ ρ i t, Q (tbl ρ i t)) →
        ∀ A ∈ mergeRun letter b R completed tbl, Q A
  | 0, _, hc, _, _ => hc
  | R + 1, completed, hc, tbl, hent => by
    rw [← Fin.cons_self_tail tbl]
    by_cases hs : ∀ i, (firstLive (liveTest letter completed) (tbl 0 i)).isSome
    · have hy' : ∀ i, firstLive (liveTest letter completed) (tbl 0 i)
          = some ((firstLive (liveTest letter completed) (tbl 0 i)).get (hs i)) :=
        fun i => (Option.some_get (hs i)).symm
      rw [mergeRun_succ_of_some letter hb1 completed (tbl 0) _ _ hy']
      refine mergeRun_forall_of_entries hb1 Q hQ hQ0 hQu R _ ?_ _ (fun ρ i t => hent _ i t)
      intro A hA
      rw [saveBatch, List.mem_cons] at hA
      rcases hA with rfl | hA
      · refine hQu _ _ (hQ _ fun i => ?_) (unionList_forall Q hQ0 hQu completed hc)
        have hmem : ∀ {k' : ℕ} (row : Fin k' → Record N σ) (e : Record N σ),
            firstLive (liveTest letter completed) row = some e → ∃ t, row t = e := by
          intro k' row e h
          induction k' with
          | zero => simp at h
          | succ k' ih =>
            rw [← Fin.cons_self_tail row, firstLive_cons] at h
            split_ifs at h with hl
            · exact ⟨0, Option.some.inj h⟩
            · obtain ⟨t, ht⟩ := ih (Fin.tail row) h
              exact ⟨t.succ, ht⟩
        obtain ⟨t, ht⟩ := hmem (tbl 0 i) _ (hy' i)
        rw [← ht]
        exact hent 0 i t
      · exact hc A hA
    · have hnone : ∃ i, firstLive (liveTest letter completed) (tbl 0 i) = none := by
        push Not at hs
        obtain ⟨i, hi⟩ := hs
        exact ⟨i, Option.not_isSome_iff_eq_none.1 hi⟩
      rw [mergeRun_succ_of_none letter hb1 completed (tbl 0) _ hnone]
      exact hc

lemma supp_unionList_subset (l : List (Record N σ)) (S : Finset (Fin N))
    (h : ∀ A ∈ l, A.supp ⊆ S) : (unionList l).supp ⊆ S := by
  induction l with
  | nil => simp [unionList]
  | cons A l ih =>
    rw [unionList, Record.supp_union]
    exact Finset.union_subset (h A (List.mem_cons_self ..))
      (ih fun B hB => h B (List.mem_cons_of_mem _ hB))

lemma supp_unionTuple_subset {m : ℕ} (y : Fin m → Record N σ) (S : Finset (Fin N))
    (h : ∀ i, (y i).supp ⊆ S) : (unionTuple y).supp ⊆ S := by
  rw [supp_unionTuple]
  exact Finset.biUnion_subset.2 fun i _ => h i

lemma supp_mergeK_subset {b : ℕ} (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) (R : ℕ) {k : ℕ}
    (tbl : Fin R → Fin (2 * b) → Fin k → Record N σ) (S : Finset (Fin N))
    (hent : ∀ ρ i t, (tbl ρ i t).supp ⊆ S) : (mergeK letter b R tbl).supp ⊆ S :=
  (Record.compress_spec letter hb _).1.trans (supp_unionList_subset _ S
    (mergeRun_forall_of_entries letter hb1 (fun A => A.supp ⊆ S)
      (fun y hy => supp_unionTuple_subset y S hy) (by simp)
      (fun A B hA hB => by rw [Record.supp_union]; exact Finset.union_subset hA hB)
      R [] (fun A hA => by simp at hA) tbl hent))

/-! ## Invariants for every seed -/

section Invariants

variable {b : ℕ} (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) (P : MParams)
include hb hb1

/-- Every seed gives a truthful record. -/
theorem summary_truthful :
    ∀ (r j q : ℕ) (ω : Ω b P r j) (x : Fin N → σ), (summary letter b P r j q ω x).Truthful x
  | _, 0, q, _, x => by
    unfold summary letterRecN
    split_ifs
    · exact letterRec_truthful x _
    · exact truthful_emptyRec x
  | 0, _ + 1, _, _, x => truthful_emptyRec x
  | r + 1, j + 1, q, ω, x => by
    unfold summary
    refine Record.truthful_compress letter (truthful_unionList x fun A hA => ?_) b
    rw [List.mem_ofFn] at hA
    obtain ⟨d, rfl⟩ := hA
    exact (mergeK_spec letter hb hb1 x _ _ fun ρ i t =>
      Record.truthful_compress letter (Record.truthful_union
        (summary_truthful r (j - d) _ _ x) (summary_truthful r (j - d) _ _ x)) b).1

/-- Every seed gives a record of at most `b` positions. -/
theorem summary_card_le :
    ∀ (r j q : ℕ) (ω : Ω b P r j) (x : Fin N → σ), (summary letter b P r j q ω x).supp.card ≤ b
  | _, 0, q, _, x => by
    unfold summary letterRecN
    split_ifs
    · rw [supp_letterRec, Finset.card_singleton]; exact hb1
    · simp
  | 0, _ + 1, _, _, x => by simp [summary]
  | r + 1, j + 1, q, ω, x => (Record.compress_spec letter hb _).2.1

/-- Every seed gives a record inside the interval. -/
theorem summary_supp_subset :
    ∀ (r j q : ℕ) (ω : Ω b P r j) (x : Fin N → σ), (summary letter b P r j q ω x).supp ⊆ ivl j q
  | _, 0, q, _, x => by
    unfold summary letterRecN
    split_ifs with h
    · rw [supp_letterRec, ivl_zero q h]
    · simp
  | 0, _ + 1, _, _, x => by simp [summary]
  | r + 1, j + 1, q, ω, x => by
    unfold summary
    refine (Record.compress_spec letter hb _).1.trans (supp_unionList_subset _ _ fun A hA => ?_)
    rw [List.mem_ofFn] at hA
    obtain ⟨d, rfl⟩ := hA
    refine supp_mergeK_subset letter hb hb1 _ _ _ fun ρ i t => ?_
    refine (Record.compress_spec letter hb _).1.trans ?_
    rw [Record.supp_union]
    refine Finset.union_subset ?_ ?_
    · exact (summary_supp_subset r (j - d) _ _ x).trans
        (ivl_child_subset (by omega) (ω d ρ i t).1.isLt 0 (by omega))
    · exact (summary_supp_subset r (j - d) _ _ x).trans
        (ivl_child_subset (by omega) (ω d ρ i t).1.isLt 1 (by omega))

end Invariants

/-! ## The cost recurrence -/

/-- **The cost recurrence** `(B)` before its solution: a letter costs `2`; rank `0` costs
nothing; rank `r+1` on `(j+1, ·)` sums over depths the seeded merger's cost with candidate
cost `2·(A + A)` (`combine₂`), then doubles (`combine`). -/
noncomputable def costA (b : ℕ) (P : MParams) : ℕ → ℕ → ℝ
  | _, 0 => 2
  | 0, _ + 1 => 0
  | r + 1, j + 1 => 2 * ∑ d : Fin (j + 1),
      2 * (((P (2 ^ (d : ℕ))).1 : ℝ) * (8 * (2 * (costA b P r (j - d) + costA b P r (j - d)))
        * ((2 * b : ℕ) : ℝ) * Real.sqrt ((P (2 ^ (d : ℕ))).2)))

lemma costA_nonneg (b : ℕ) (P : MParams) : ∀ r j, 0 ≤ costA b P r j
  | _, 0 => by unfold costA; norm_num
  | 0, _ + 1 => by unfold costA; exact le_rfl
  | r + 1, j + 1 => by
    unfold costA
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => ?_)
    have h1 := costA_nonneg b P r (j - d)
    have := Real.sqrt_nonneg (((P (2 ^ (d : ℕ))).2 : ℕ) : ℝ)
    positivity

/-- Seed spaces are nonempty. -/
theorem nonemptyΩ (b : ℕ) (P : MParams) : ∀ r j, Nonempty (Ω b P r j)
  | 0, _ => ⟨()⟩
  | _ + 1, 0 => ⟨()⟩
  | r + 1, j + 1 => ⟨fun d _ _ _ => (⟨0, by positivity⟩, (nonemptyΩ b P r (j - d)).some,
      (nonemptyΩ b P r (j - d)).some)⟩

instance instNonemptyΩ {b : ℕ} {P : MParams} {r j : ℕ} : Nonempty (Ω b P r j) := nonemptyΩ b P r j

/-- The seeded merger's dual with a `Fin`-indexed seed table. -/
theorem hasDual_mergeK_seeded_fin {Ω' : Type} [Fintype Ω'] [DecidableEq Ω'] [Nonempty Ω']
    {b k : ℕ} (hb : 1 ≤ b) (hk : 1 ≤ k) (cand : Ω' → (Fin N → σ) → Record N σ) {T : ℝ}
    (hT : 0 ≤ T) (hc : ∀ ω, HasDual (cand ω) T) (R : ℕ) (ωs : Fin R → Fin (2 * b) → Fin k → Ω') :
    HasDual (fun x => mergeK letter b R (fun ρ i t => cand (ωs ρ i t) x))
      (2 * (R * (8 * T * ((2 * b : ℕ) : ℝ) * Real.sqrt k))) := by
  classical
  let ωs' : ℕ → Fin (2 * b) → Fin k → Ω' := fun ρ =>
    if h : ρ < R then ωs ⟨ρ, h⟩ else fun _ _ => Classical.arbitrary Ω'
  refine (hasDual_mergeK_seeded letter b hb hk cand hT hc R ωs').ofEq fun x => ?_
  simp only [ωs', Fin.is_lt, dif_pos, Fin.eta]

/-- **Every seed's summary has a dual of cost `costA r j`.** -/
theorem hasDual_summary {b : ℕ} (hb1 : 1 ≤ b) (P : MParams) (hk : ∀ h, 1 ≤ h → 1 ≤ (P h).2) :
    ∀ (r j q : ℕ) (ω : Ω b P r j),
      HasDual (fun x : Fin N → σ => summary letter b P r j q ω x) (costA b P r j)
  | r, 0, q, _ => by
    unfold summary letterRecN costA
    split_ifs with hq
    · exact hasDual_letterRec ⟨q, hq⟩
    · exact (hasDual_const fun _ _ => rfl).mono (by norm_num)
  | 0, _ + 1, _, _ => by
    unfold summary costA
    exact hasDual_const fun _ _ => rfl
  | r + 1, j + 1, q, ω => by
    unfold summary costA
    have hK : ∀ d : Fin (j + 1), HasDual (fun x : Fin N → σ => mergeK letter b (P (2 ^ (d : ℕ))).1 (fun ρ i t =>
        Record.compress letter b
          ((summary letter b P r (j - d) (2 * (q * 2 ^ (d : ℕ) + ((ω d ρ i t).1 : ℕ))) (ω d ρ i t).2.1 x).union
            (summary letter b P r (j - d) (2 * (q * 2 ^ (d : ℕ) + ((ω d ρ i t).1 : ℕ)) + 1) (ω d ρ i t).2.2 x))))
        (2 * (((P (2 ^ (d : ℕ))).1 : ℝ) * (8 * (2 * (costA b P r (j - d) + costA b P r (j - d)))
          * ((2 * b : ℕ) : ℝ) * Real.sqrt ((P (2 ^ (d : ℕ))).2)))) := by
      intro d
      refine hasDual_mergeK_seeded_fin letter hb1 (hk _ Nat.one_le_two_pow)
        (cand := fun s : Fin (2 ^ (d : ℕ)) × Ω b P r (j - d) × Ω b P r (j - d) => fun x =>
          Record.compress letter b
            ((summary letter b P r (j - d) (2 * (q * 2 ^ (d : ℕ) + (s.1 : ℕ))) s.2.1 x).union
              (summary letter b P r (j - d) (2 * (q * 2 ^ (d : ℕ) + (s.1 : ℕ)) + 1) s.2.2 x)))
        (by have := costA_nonneg b P r (j - d); positivity) (fun s => ?_) _ (ω d)
      exact HasDual.combine₂ (fun s₁ s₂ => Record.compress letter b (s₁.union s₂))
        (costA_nonneg b P r (j - d)) (costA_nonneg b P r (j - d))
        (hasDual_summary hb1 P hk r (j - d) _ s.2.1) (hasDual_summary hb1 P hk r (j - d) _ s.2.2)
    have hc : ∀ d : Fin (j + 1), (0 : ℝ) ≤ 2 * (((P (2 ^ (d : ℕ))).1 : ℝ)
        * (8 * (2 * (costA b P r (j - d) + costA b P r (j - d)))
          * ((2 * b : ℕ) : ℝ) * Real.sqrt ((P (2 ^ (d : ℕ))).2))) := by
      intro d
      have h1 := costA_nonneg b P r (j - d)
      have h2 := Real.sqrt_nonneg (((P (2 ^ (d : ℕ))).2 : ℕ) : ℝ)
      positivity
    exact HasDual.combine (fun K : Fin (j + 1) → Record N σ =>
        Record.compress letter b (unionList (List.ofFn K))) hc hK

end Summary

end MonoidProduct
