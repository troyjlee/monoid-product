import MonoidProduct.Ordered.Records
import MonoidProduct.Ordered.FiniteProb

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The merger (the paper's `lem:beta-sampling`)

Candidates are records.  The merger keeps a **saved history** `completed`, newest first:
after each completed batch `A` it saves the accumulated union `A ∪ K` of the batch with the
previous saved union `K` (`saveBatch`).  A candidate is **marked** (live) when inserting it
changes the product of every saved union (`liveTest`); since every saved union is retained,
a candidate once unmarked stays unmarked (`liveTest_saveBatch_of_false`).  This is the
accumulated-union marking rule of the paper (`lem:beta-sampling`): a candidate `V` is
unmarked once `p(K' ∪ V) = p(K')` for the current saved union `K'`.

One **round** of the merger is a rejection program of `2b` draws (`mergeProg`): each draw
accepts the first marked proposal, the marking is frozen during the round, and on the last
draw the batch is saved.  The round-level semantics is `roundResult_spec`; the
probabilistic heart is `halving_with_background`: for `2b` i.i.d. samples from the
conditional law, inserted into a fixed truthful background, the expected marked mass after
the round is at most `b/(2b+1)` times the mass before it — the exchangeability argument of
the paper through `card_essential_with_background_le` (the background is fixed, not an
extra sample: the denominator stays `2b+1`).  `halving_saveBatch` is the form for the
actual update; the raw-batch statement `halving` is kept as the empty-background case.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity

section Merger

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) {n : ℕ}

/-- The empty record. -/
def emptyRec : Record n σ := fun _ => none

@[simp] lemma supp_emptyRec : (emptyRec : Record n σ).supp = ∅ := by
  ext i; simp [Record.supp, mem_optSupp, emptyRec]

lemma emptyRec_union (r : Record n σ) : (emptyRec : Record n σ).union r = r := by
  funext i; rfl

lemma truthful_emptyRec (x : Fin n → σ) : Record.Truthful x (emptyRec : Record n σ) :=
  fun _ _ h => absurd h (by simp [emptyRec])

lemma union_assoc_rec (r s t : Record n σ) : (r.union s).union t = r.union (s.union t) := by
  funext i; simp only [Record.union]; cases r i <;> rfl

lemma union_self_rec (r : Record n σ) : r.union r = r := by
  funext i; simp only [Record.union]; cases r i <;> rfl

lemma union_emptyRec (r : Record n σ) : r.union (emptyRec : Record n σ) = r := by
  funext i; simp only [Record.union, emptyRec]; cases r i <;> rfl

/-- The union of a list of records. -/
def unionList : List (Record n σ) → Record n σ
  | [] => emptyRec
  | A :: l => A.union (unionList l)

lemma truthful_unionList (x : Fin n → σ) {l : List (Record n σ)} (h : ∀ A ∈ l, A.Truthful x) :
    (unionList l).Truthful x := by
  induction l with
  | nil => exact truthful_emptyRec x
  | cons A l ih =>
    exact Record.truthful_union (h A (List.mem_cons_self ..))
      (ih fun B hB => h B (List.mem_cons_of_mem _ hB))

lemma supp_subset_unionList {l : List (Record n σ)} {A : Record n σ} (hA : A ∈ l) :
    A.supp ⊆ (unionList l).supp := by
  induction l with
  | nil => simp at hA
  | cons B l ih =>
    rw [List.mem_cons] at hA
    rcases hA with rfl | hA
    · rw [unionList, Record.supp_union]; exact Finset.subset_union_left
    · rw [unionList, Record.supp_union]; exact (ih hA).trans Finset.subset_union_right

/-- **The marking test**: inserting `e` changes the product of every saved union. -/
def liveTest (completed : List (Record n σ)) (e : Record n σ) : Bool :=
  decide (∀ A ∈ completed, (A.union e).prod letter ≠ A.prod letter)

lemma liveTest_nil (e : Record n σ) : liveTest letter [] e = true := by simp [liveTest]

lemma liveTest_cons (A : Record n σ) (completed : List (Record n σ)) (e : Record n σ) :
    liveTest letter (A :: completed) e
      = (liveTest letter completed e && decide ((A.union e).prod letter ≠ A.prod letter)) := by
  simp only [liveTest, List.forall_mem_cons, Bool.decide_and]
  rw [Bool.and_comm]

/-! ## The saved history -/

/-- **Saving a completed batch**: the new saved record is the batch together with the previous
saved union, so the history `[K_r, …, K_1]` (newest first) consists of the accumulated unions
and every earlier test is retained. -/
def saveBatch (completed : List (Record n σ)) (A : Record n σ) : List (Record n σ) :=
  (A.union (unionList completed)) :: completed

lemma saveBatch_eq_cons (completed : List (Record n σ)) (A : Record n σ) :
    saveBatch completed A = (A.union (unionList completed)) :: completed := rfl

/-- The union of the new history is its newest record. -/
lemma unionList_saveBatch (completed : List (Record n σ)) (A : Record n σ) :
    unionList (saveBatch completed A) = A.union (unionList completed) := by
  show (A.union (unionList completed)).union (unionList completed) = _
  rw [union_assoc_rec, union_self_rec]

/-- The marking test after saving: the old test and the insertion test into the new saved
union. -/
lemma liveTest_saveBatch (completed : List (Record n σ)) (A e : Record n σ) :
    liveTest letter (saveBatch completed A) e
      = (liveTest letter completed e
          && decide (((A.union (unionList completed)).union e).prod letter
            ≠ (A.union (unionList completed)).prod letter)) :=
  liveTest_cons letter _ _ _

/-- **Permanent unmarking**: an unmarked candidate stays unmarked. -/
lemma liveTest_saveBatch_of_false {completed : List (Record n σ)} {e : Record n σ}
    (h : liveTest letter completed e = false) (A : Record n σ) :
    liveTest letter (saveBatch completed A) e = false := by
  rw [liveTest_saveBatch, h, Bool.false_and]

lemma truthful_saveBatch {x : Fin n → σ} {completed : List (Record n σ)}
    (hc : ∀ B ∈ completed, B.Truthful x) {A : Record n σ} (hA : A.Truthful x) :
    ∀ B ∈ saveBatch completed A, B.Truthful x := by
  intro B hB
  rw [saveBatch, List.mem_cons] at hB
  rcases hB with rfl | hB
  · exact Record.truthful_union hA (truthful_unionList x hc)
  · exact hc B hB

/-- The support of the new saved union. -/
lemma supp_saveBatch_head (completed : List (Record n σ)) (A : Record n σ) :
    (A.union (unionList completed)).supp = A.supp ∪ (unionList completed).supp :=
  Record.supp_union _ _

/-- Every earlier saved record lies inside the newest one. -/
lemma supp_subset_saveBatch_head {completed : List (Record n σ)} {B : Record n σ}
    (hB : B ∈ completed) (A : Record n σ) : B.supp ⊆ (A.union (unionList completed)).supp := by
  rw [Record.supp_union]
  exact (supp_subset_unionList hB).trans Finset.subset_union_right

/-- A still-marked truthful candidate strictly increases the product of every saved union. -/
lemma prod_lt_of_liveTest (hst : IsStableOrder M) {x : Fin n → σ} {completed : List (Record n σ)}
    {e : Record n σ} (he : e.Truthful x) (hl : liveTest letter completed e = true)
    {A : Record n σ} (hA : A ∈ completed) (hAt : A.Truthful x) :
    A.prod letter < (A.union e).prod letter := by
  have hne : (A.union e).prod letter ≠ A.prod letter := by
    simp only [liveTest, decide_eq_true_eq] at hl
    exact hl A hA
  refine lt_of_le_of_ne ?_ (Ne.symm hne)
  rw [Record.prod_of_truthful letter hAt, Record.prod_of_truthful letter (Record.truthful_union hAt he),
    Record.supp_union]
  exact hst.subwordProd_mono letter x Finset.subset_union_left

/-- **The merger's rejection program** for one round of `2b` draws. -/
def mergeProg (b : ℕ) : DrawProgram (List (Record n σ) × Record n σ) (Record n σ) where
  live s _ e := liveTest letter s.1 e
  accept s d e := if d + 1 = 2 * b then (saveBatch s.1 (s.2.union e), emptyRec) else (s.1, s.2.union e)

/-- Accumulating a tuple of records into `cur`, in order. -/
def accUnion : Record n σ → ∀ {m : ℕ}, (Fin m → Record n σ) → Record n σ
  | cur, 0, _ => cur
  | cur, _ + 1, y => accUnion (cur.union (y 0)) (Fin.tail y)

/-- The union of a tuple of records. -/
def unionTuple {m : ℕ} (y : Fin m → Record n σ) : Record n σ := accUnion emptyRec y

lemma accUnion_zero (cur : Record n σ) (y : Fin 0 → Record n σ) : accUnion cur y = cur := rfl

lemma accUnion_succ (cur : Record n σ) {m : ℕ} (y : Fin (m + 1) → Record n σ) :
    accUnion cur y = accUnion (cur.union (y 0)) (Fin.tail y) := rfl

lemma supp_accUnion (cur : Record n σ) :
    ∀ {m : ℕ} (y : Fin m → Record n σ),
      (accUnion cur y).supp = cur.supp ∪ Finset.univ.biUnion fun i => (y i).supp
  | 0, y => by simp [accUnion_zero]
  | m + 1, y => by
    rw [accUnion_succ, supp_accUnion _ (Fin.tail y), Record.supp_union, Finset.union_assoc]
    congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Fin.tail]
    constructor
    · rintro (h | ⟨j, hj⟩)
      · exact ⟨0, h⟩
      · exact ⟨j.succ, hj⟩
    · rintro ⟨j, hj⟩
      refine Fin.cases (fun h => Or.inl h) (fun j h => Or.inr ⟨j, h⟩) j hj

lemma truthful_accUnion {x : Fin n → σ} {cur : Record n σ} (hc : cur.Truthful x) :
    ∀ {m : ℕ} {y : Fin m → Record n σ}, (∀ i, (y i).Truthful x) → (accUnion cur y).Truthful x
  | 0, _, _ => hc
  | m + 1, y, hy => by
    rw [accUnion_succ]
    exact truthful_accUnion (Record.truthful_union hc (hy 0)) fun i => hy i.succ

lemma supp_unionTuple {m : ℕ} (y : Fin m → Record n σ) :
    (unionTuple y).supp = Finset.univ.biUnion fun i => (y i).supp := by
  rw [unionTuple, supp_accUnion, supp_emptyRec, Finset.empty_union]

lemma truthful_unionTuple {x : Fin n → σ} {m : ℕ} {y : Fin m → Record n σ}
    (hy : ∀ i, (y i).Truthful x) : (unionTuple y).Truthful x :=
  truthful_accUnion (truthful_emptyRec x) hy

/-! ## One round -/

variable {k : ℕ}

lemma mergeProg_live (b : ℕ) (c : List (Record n σ)) (cur : Record n σ) (d : ℕ) :
    (mergeProg letter b).live (c, cur) d = liveTest letter c := rfl

lemma mergeProg_accept (b : ℕ) (c : List (Record n σ)) (cur : Record n σ) (d : ℕ)
    (e : Record n σ) :
    (mergeProg letter b).accept (c, cur) d e
      = if d + 1 = 2 * b then (saveBatch c (cur.union e), emptyRec) else (c, cur.union e) := rfl

/-- One step of the merger's fold. -/
lemma foldRows_mergeProg_step (b : ℕ) (completed : List (Record n σ))
    (rows : Fin (2 * b) → Fin k → Record n σ) (j m : ℕ) (cur : Record n σ) (hj : j < 2 * b) :
    DrawProgram.foldRows (mergeProg letter b) rows j (m + 1) (completed, cur)
      = match firstLive (liveTest letter completed) (rows ⟨j, hj⟩) with
        | none => ((completed, cur), false)
        | some e => DrawProgram.foldRows (mergeProg letter b) rows (j + 1) m
            ((mergeProg letter b).accept (completed, cur) j e) := by
  rw [DrawProgram.foldRows_succ, dif_pos hj, mergeProg_live]
  cases firstLive (liveTest letter completed) (rows ⟨j, hj⟩) <;> rfl

/-- **The round semantics**: from draw `j` with `m ≥ 1` draws to go, the fold either
accepts every remaining draw (the accepted tuple `y`) and pushes the accumulated batch,
or fails with the saved batches unchanged. -/
theorem foldRows_mergeProg (b : ℕ) (completed : List (Record n σ))
    (rows : Fin (2 * b) → Fin k → Record n σ) :
    ∀ (m : ℕ), 1 ≤ m → ∀ (j : ℕ) (cur : Record n σ) (hjm : j + m = 2 * b),
      (∀ y : Fin m → Record n σ,
        (∀ i : Fin m, firstLive (liveTest letter completed) (rows ⟨j + i, by omega⟩) = some (y i)) →
        DrawProgram.foldRows (mergeProg letter b) rows j m (completed, cur)
          = ((saveBatch completed (accUnion cur y), emptyRec), true))
      ∧ ((∃ i : Fin m, firstLive (liveTest letter completed) (rows ⟨j + i, by omega⟩) = none) →
          (DrawProgram.foldRows (mergeProg letter b) rows j m (completed, cur)).1.1 = completed
          ∧ (DrawProgram.foldRows (mergeProg letter b) rows j m (completed, cur)).2 = false)
  | 0, h0, _, _, _ => absurd h0 (by omega)
  | m + 1, _, j, cur, hjm => by
    rw [foldRows_mergeProg_step letter b completed rows j m cur (by omega)]
    cases hfl : firstLive (liveTest letter completed) (rows ⟨j, by omega⟩) with
    | none =>
      constructor
      · intro y hy
        have h0 := hy 0
        rw [show (⟨j + ((0 : Fin (m + 1)) : ℕ), by omega⟩ : Fin (2 * b)) = ⟨j, by omega⟩ from
          Fin.ext (by simp)] at h0
        rw [hfl] at h0
        exact absurd h0 (by simp)
      · intro _
        exact ⟨rfl, rfl⟩
    | some e =>
      dsimp only
      rw [mergeProg_accept]
      constructor
      · intro y hy
        have h0 := hy 0
        rw [show (⟨j + ((0 : Fin (m + 1)) : ℕ), by omega⟩ : Fin (2 * b)) = ⟨j, by omega⟩ from
          Fin.ext (by simp)] at h0
        rw [hfl] at h0
        have hey : e = y 0 := Option.some.inj h0
        by_cases hm0 : m = 0
        · subst hm0
          rw [if_pos (by omega), DrawProgram.foldRows_zero, accUnion_succ, accUnion_zero, hey]
        · rw [if_neg (by omega)]
          have ih := (foldRows_mergeProg b completed rows m (by omega) (j + 1) (cur.union e)
            (by omega)).1 (Fin.tail y) (fun i => by
              have := hy i.succ
              rw [show (⟨j + ((i.succ : Fin (m + 1)) : ℕ), by omega⟩ : Fin (2 * b))
                = ⟨j + 1 + i, by omega⟩ from Fin.ext (by simp; omega)] at this
              exact this)
          rw [ih, accUnion_succ, hey]
      · rintro ⟨i, hi⟩
        refine Fin.cases ?_ ?_ i hi
        · intro hi
          rw [show (⟨j + ((0 : Fin (m + 1)) : ℕ), by omega⟩ : Fin (2 * b)) = ⟨j, by omega⟩ from
            Fin.ext (by simp)] at hi
          rw [hfl] at hi
          exact absurd hi (by simp)
        · intro i' hi
          by_cases hm0 : m = 0
          · subst hm0; exact i'.elim0
          · rw [if_neg (by omega)]
            refine (foldRows_mergeProg b completed rows m (by omega) (j + 1) (cur.union e)
              (by omega)).2 ⟨i', ?_⟩
            rw [show (⟨j + ((i'.succ : Fin (m + 1)) : ℕ), by omega⟩ : Fin (2 * b))
              = ⟨j + 1 + i', by omega⟩ from Fin.ext (by simp; omega)] at hi
            exact hi

/-- The result of one round: the saved batches and the success flag. -/
def roundResult (b : ℕ) (completed : List (Record n σ))
    (rows : Fin (2 * b) → Fin k → Record n σ) : List (Record n σ) × Bool :=
  let r := DrawProgram.foldRows (mergeProg letter b) rows 0 (2 * b) (completed, emptyRec)
  (r.1.1, r.2)

theorem roundResult_spec {b : ℕ} (hb : 1 ≤ b) (completed : List (Record n σ))
    (rows : Fin (2 * b) → Fin k → Record n σ) :
    (∀ y : Fin (2 * b) → Record n σ,
      (∀ i, firstLive (liveTest letter completed) (rows i) = some (y i)) →
      roundResult letter b completed rows = (saveBatch completed (unionTuple y), true))
    ∧ ((∃ i, firstLive (liveTest letter completed) (rows i) = none) →
        roundResult letter b completed rows = (completed, false)) := by
  have key := foldRows_mergeProg letter b completed rows (2 * b) (by omega) 0 emptyRec (by omega)
  have hrows : ∀ i : Fin (2 * b), (⟨0 + (i : ℕ), by omega⟩ : Fin (2 * b)) = i :=
    fun i => Fin.ext (by simp)
  constructor
  · intro y hy
    unfold roundResult
    rw [key.1 y (fun i => by rw [hrows]; exact hy i)]
    rfl
  · rintro ⟨i, hi⟩
    obtain ⟨h1, h2⟩ := key.2 ⟨i, by rw [hrows]; exact hi⟩
    unfold roundResult
    exact Prod.ext h1 h2

/-! ## Halving -/

section Halving

variable (x : Fin n → σ) (μ : Record n σ → ℝ)

lemma prod_union_truthful {r r' : Record n σ} (hr : r.Truthful x) (hr' : r'.Truthful x) :
    (r.union r').prod letter = subwordProd letter x (r.supp ∪ r'.supp) := by
  rw [Record.prod_of_truthful letter (Record.truthful_union hr hr'), Record.supp_union]

lemma liveMass_cons (A : Record n σ) (completed : List (Record n σ)) :
    liveMass μ (liveTest letter (A :: completed))
      = ∑ e, if liveTest letter completed e then
          μ e * (if (A.union e).prod letter ≠ A.prod letter then 1 else 0) else 0 := by
  unfold liveMass
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [liveTest_cons]
  by_cases h1 : liveTest letter completed e = true
  · by_cases h2 : (A.union e).prod letter ≠ A.prod letter
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

/-- The essential-index predicate on tuples of records. -/
def essIdx {m : ℕ} (z : Fin m → Record n σ) (i : Fin m) : Bool :=
  decide (subwordProd letter x (unionExcept (fun j => (z j).supp) i)
    ≠ subwordProd letter x (Finset.univ.biUnion fun j => (z j).supp))

lemma unionExcept_comp_perm {J : Type} [Fintype J] [DecidableEq J] (U : J → Finset (Fin n))
    (π : Equiv.Perm J) (i : J) :
    unionExcept (fun j => U (π j)) i = unionExcept U (π i) := by
  ext a
  simp only [unionExcept, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨j, hj, ha⟩
    exact ⟨π j, fun h => hj (π.injective h), ha⟩
  · rintro ⟨j', hj', ha⟩
    refine ⟨π.symm j', fun h => hj' ?_, by simpa using ha⟩
    rw [← h]; simp

lemma biUnion_comp_perm {J : Type} [Fintype J] [DecidableEq J] (U : J → Finset (Fin n))
    (π : Equiv.Perm J) :
    (Finset.univ.biUnion fun j => U (π j)) = Finset.univ.biUnion U := by
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨fun ⟨j, h⟩ => ⟨π j, h⟩, fun ⟨j, h⟩ => ⟨π.symm j, by simpa using h⟩⟩

lemma essIdx_comp_perm {m : ℕ} (π : Equiv.Perm (Fin m)) (z : Fin m → Record n σ) (i : Fin m) :
    essIdx letter x (z ∘ π) i = essIdx letter x z (π i) := by
  unfold essIdx
  rw [decide_eq_decide]
  have h1 : unionExcept (fun j => ((z ∘ π) j).supp) i = unionExcept (fun j => (z j).supp) (π i) :=
    unionExcept_comp_perm (fun j => (z j).supp) π i
  have h2 : (Finset.univ.biUnion fun j => ((z ∘ π) j).supp)
      = Finset.univ.biUnion fun j => (z j).supp :=
    biUnion_comp_perm (fun j => (z j).supp) π
  rw [h1, h2]

lemma card_essIdx_le (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b) {m : ℕ}
    (z : Fin m → Record n σ) :
    (Finset.univ.filter fun i => essIdx letter x z i = true).card ≤ b := by
  have := card_essential_le hst letter x hb (fun j => (z j).supp)
  convert this using 2
  ext i
  simp [essIdx]

lemma biUnion_fin_succ {m : ℕ} (U : Fin (m + 1) → Finset (Fin n)) :
    Finset.univ.biUnion U = U 0 ∪ Finset.univ.biUnion (fun j : Fin m => U j.succ) := by
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  exact Fin.exists_fin_succ

lemma unionExcept_zero {m : ℕ} (U : Fin (m + 1) → Finset (Fin n)) :
    unionExcept U 0 = Finset.univ.biUnion (fun j : Fin m => U j.succ) := by
  ext a
  simp only [unionExcept, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
  constructor
  · rintro ⟨j, hj, ha⟩
    refine Fin.cases (fun h => absurd rfl h) (fun j' _ ha => ⟨j', ha⟩) j hj ha
  · rintro ⟨j, ha⟩
    exact ⟨j.succ, Fin.succ_ne_zero j, ha⟩

/-- **The record identification**: for truthful records, the new live test on a tuple's
first entry is the essential-index predicate at index `0`. -/
lemma G_eq_essIdx {m : ℕ} {z : Fin (m + 1) → Record n σ} (hz : ∀ i, (z i).Truthful x) :
    (if ((unionTuple (Fin.tail z)).union (z 0)).prod letter ≠ (unionTuple (Fin.tail z)).prod letter
      then (1 : ℝ) else 0) = (if essIdx letter x z 0 then 1 else 0) := by
  have hA : (unionTuple (Fin.tail z)).Truthful x := truthful_unionTuple fun i => hz _
  rw [prod_union_truthful letter x hA (hz 0), Record.prod_of_truthful letter hA, supp_unionTuple,
    essIdx, unionExcept_zero, biUnion_fin_succ (fun j => (z j).supp)]
  refine if_congr ?_ rfl rfl
  rw [decide_eq_true_eq]
  have hX : (Finset.univ.biUnion fun i => (Fin.tail z i).supp)
      = Finset.univ.biUnion fun j : Fin m => (z j.succ).supp := rfl
  rw [hX, Finset.union_comm]
  exact ne_comm

/-! ### Halving against a fixed background -/

/-- The essential-index predicate on tuples of records, with a fixed background position
set `K`. -/
def essIdxK (K : Finset (Fin n)) {m : ℕ} (z : Fin m → Record n σ) (i : Fin m) : Bool :=
  decide (subwordProd letter x (K ∪ unionExcept (fun j => (z j).supp) i)
    ≠ subwordProd letter x (K ∪ Finset.univ.biUnion fun j => (z j).supp))

lemma essIdxK_comp_perm (K : Finset (Fin n)) {m : ℕ} (π : Equiv.Perm (Fin m))
    (z : Fin m → Record n σ) (i : Fin m) :
    essIdxK letter x K (z ∘ π) i = essIdxK letter x K z (π i) := by
  unfold essIdxK
  rw [decide_eq_decide]
  have h1 : unionExcept (fun j => ((z ∘ π) j).supp) i = unionExcept (fun j => (z j).supp) (π i) :=
    unionExcept_comp_perm (fun j => (z j).supp) π i
  have h2 : (Finset.univ.biUnion fun j => ((z ∘ π) j).supp)
      = Finset.univ.biUnion fun j => (z j).supp :=
    biUnion_comp_perm (fun j => (z j).supp) π
  rw [h1, h2]

/-- **At most `b` sampled sets are essential against a fixed background** (`K` is fixed, not
an extra sample: the bound stays `b`).  Proof: apply `card_essential_le` to the family on
`Option J` with `none ↦ K`. -/
theorem card_essential_with_background_le (hst : IsStableOrder M) {b : ℕ}
    (hb : IsBreadthBound letter b) (K : Finset (Fin n)) {J : Type} [Fintype J] [DecidableEq J]
    (U : J → Finset (Fin n)) :
    (Finset.univ.filter fun j => subwordProd letter x (K ∪ unionExcept U j)
        ≠ subwordProd letter x (K ∪ Finset.univ.biUnion U)).card ≤ b := by
  classical
  let V : Option J → Finset (Fin n) := fun o => o.elim K U
  have hV : Finset.univ.biUnion V = K ∪ Finset.univ.biUnion U := by
    ext a
    simp [V, Option.exists]
  have hVe : ∀ j : J, unionExcept V (some j) = K ∪ unionExcept U j := by
    intro j
    ext a
    simp [V, unionExcept, Option.exists]
  have h := card_essential_le hst letter x hb V
  refine le_trans ?_ h
  refine Finset.card_le_card_of_injOn (fun j => some j) ?_
    (fun a _ b _ h => Option.some_injective _ h)
  intro j hj
  rw [Finset.mem_coe, Finset.mem_filter] at hj
  rw [Finset.mem_coe, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [hVe, hV]
  exact hj.2

lemma card_essIdxK_le (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    (K : Finset (Fin n)) {m : ℕ} (z : Fin m → Record n σ) :
    (Finset.univ.filter fun i => essIdxK letter x K z i = true).card ≤ b := by
  have := card_essential_with_background_le letter x hst hb K (fun j => (z j).supp)
  convert this using 2
  ext i
  simp [essIdxK]

/-- **The record identification with a background**: for truthful samples and a truthful
background `S`, the insertion test of the sample `z 0` into `S ∪ (the other samples)` is
the background essential-index predicate at `0`. -/
lemma G_eq_essIdxK {S : Record n σ} (hS : S.Truthful x) {m : ℕ} {z : Fin (m + 1) → Record n σ}
    (hz : ∀ i, (z i).Truthful x) :
    (if (((unionTuple (Fin.tail z)).union S).union (z 0)).prod letter
        ≠ ((unionTuple (Fin.tail z)).union S).prod letter then (1 : ℝ) else 0)
      = (if essIdxK letter x S.supp z 0 then 1 else 0) := by
  have hA : (unionTuple (Fin.tail z)).Truthful x := truthful_unionTuple fun i => hz _
  have hAS : ((unionTuple (Fin.tail z)).union S).Truthful x := Record.truthful_union hA hS
  rw [prod_union_truthful letter x hAS (hz 0), Record.prod_of_truthful letter hAS,
    Record.supp_union, supp_unionTuple, essIdxK, unionExcept_zero,
    biUnion_fin_succ (fun j => (z j).supp)]
  refine if_congr ?_ rfl rfl
  rw [decide_eq_true_eq]
  have hX : (Finset.univ.biUnion fun i => (Fin.tail z i).supp)
      = Finset.univ.biUnion fun j : Fin m => (z j.succ).supp := rfl
  rw [hX]
  have e1 : (Finset.univ.biUnion fun j : Fin m => (z j.succ).supp) ∪ S.supp ∪ (z 0).supp
      = S.supp ∪ ((z 0).supp ∪ Finset.univ.biUnion fun j : Fin m => (z j.succ).supp) := by
    ext a; simp only [Finset.mem_union]; tauto
  have e2 : (Finset.univ.biUnion fun j : Fin m => (z j.succ).supp) ∪ S.supp
      = S.supp ∪ Finset.univ.biUnion fun j : Fin m => (z j.succ).supp := Finset.union_comm _ _
  rw [e1, e2]
  exact ne_comm

variable (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
  (hμ : IsWeight μ) (htr : ∀ e, μ e ≠ 0 → e.Truthful x)
include hst hb hμ htr

/-- **Halving** (`eq:beta-halving`): for a batch of `2b` i.i.d. conditional samples, the
expected live mass after the round is at most `b/(2b+1)` times the live mass before. -/
theorem halving (completed : List (Record n σ)) (hw : 0 < liveMass μ (liveTest letter completed)) :
    ∑ y : Fin (2 * b) → Record n σ, tupleW (condW μ (liveTest letter completed)) y
        * liveMass μ (liveTest letter (unionTuple y :: completed))
      ≤ ((b : ℝ) / (2 * b + 1)) * liveMass μ (liveTest letter completed) := by
  have hνw : IsWeight (condW μ (liveTest letter completed)) := isWeight_condW hμ hw
  have hνtr : ∀ e, condW μ (liveTest letter completed) e ≠ 0 → e.Truthful x := fun e he =>
    htr e (by intro h0; apply he; simp [condW, h0])
  have hw0 : 0 ≤ liveMass μ (liveTest letter completed) := hw.le
  -- Step A: the live mass after the round, through the conditional law
  have hA : ∀ y : Fin (2 * b) → Record n σ,
      liveMass μ (liveTest letter (unionTuple y :: completed))
        = liveMass μ (liveTest letter completed) * ∑ e, condW μ (liveTest letter completed) e
            * (if ((unionTuple y).union e).prod letter ≠ (unionTuple y).prod letter then 1 else 0) :=
    fun y => by rw [liveMass_cons, sum_live_eq_condW _ hw]
  simp only [hA]
  -- Step B: one tuple of `2b + 1` samples
  have hB : ∑ y : Fin (2 * b) → Record n σ, tupleW (condW μ (liveTest letter completed)) y
        * (liveMass μ (liveTest letter completed) * ∑ e, condW μ (liveTest letter completed) e
            * (if ((unionTuple y).union e).prod letter ≠ (unionTuple y).prod letter then 1 else 0))
      = liveMass μ (liveTest letter completed)
        * ∑ z : Fin (2 * b + 1) → Record n σ, tupleW (condW μ (liveTest letter completed)) z
          * (if ((unionTuple (Fin.tail z)).union (z 0)).prod letter
                ≠ (unionTuple (Fin.tail z)).prod letter then 1 else 0) := by
    rw [sum_pi_succ]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun y _ => ?_
    rw [tupleW_cons, Fin.tail_cons, Fin.cons_zero]
    ring
  rw [hB, mul_comm ((b : ℝ) / (2 * b + 1))]
  refine mul_le_mul_of_nonneg_left ?_ hw0
  -- Step C: identify with the essential-index predicate on the support of the law
  have hC : ∑ z : Fin (2 * b + 1) → Record n σ, tupleW (condW μ (liveTest letter completed)) z
        * (if ((unionTuple (Fin.tail z)).union (z 0)).prod letter
              ≠ (unionTuple (Fin.tail z)).prod letter then 1 else 0)
      = ∑ z : Fin (2 * b + 1) → Record n σ, tupleW (condW μ (liveTest letter completed)) z
        * (if essIdx letter x z 0 then 1 else 0) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : tupleW (condW μ (liveTest letter completed)) z = 0
    · rw [hz, zero_mul, zero_mul]
    · have htz : ∀ i, (z i).Truthful x := fun i =>
        hνtr _ (Finset.prod_ne_zero_iff.1 hz i (Finset.mem_univ _))
      rw [G_eq_essIdx letter x htz]
  rw [hC]
  -- Step D: exchangeability
  have hD := sum_tupleW_ess_le hνw (by omega : 0 < 2 * b + 1) (essIdx letter x)
    (essIdx_comp_perm letter x) (card_essIdx_le letter x hst hb) 0
  refine hD.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Halving against a fixed background** (`lem:beta-sampling`, accumulated-union form):
for `2b` i.i.d. samples from the law conditioned on the current marking, inserted together
with a fixed truthful background `S` as the new saved record, the expected marked mass after
the round is at most `b/(2b+1)` times the mass before it.  The background is held fixed:
there are `2b+1` samples in the exchangeability step (the `2b` draws and one test sample),
so the denominator is `2b+1`. -/
theorem halving_with_background (completed : List (Record n σ)) {S : Record n σ}
    (hS : S.Truthful x) (hw : 0 < liveMass μ (liveTest letter completed)) :
    ∑ y : Fin (2 * b) → Record n σ, tupleW (condW μ (liveTest letter completed)) y
        * liveMass μ (liveTest letter (((unionTuple y).union S) :: completed))
      ≤ ((b : ℝ) / (2 * b + 1)) * liveMass μ (liveTest letter completed) := by
  have hνw : IsWeight (condW μ (liveTest letter completed)) := isWeight_condW hμ hw
  have hνtr : ∀ e, condW μ (liveTest letter completed) e ≠ 0 → e.Truthful x := fun e he =>
    htr e (by intro h0; apply he; simp [condW, h0])
  have hw0 : 0 ≤ liveMass μ (liveTest letter completed) := hw.le
  have hA : ∀ y : Fin (2 * b) → Record n σ,
      liveMass μ (liveTest letter (((unionTuple y).union S) :: completed))
        = liveMass μ (liveTest letter completed) * ∑ e, condW μ (liveTest letter completed) e
            * (if (((unionTuple y).union S).union e).prod letter
                ≠ ((unionTuple y).union S).prod letter then 1 else 0) :=
    fun y => by rw [liveMass_cons, sum_live_eq_condW _ hw]
  simp only [hA]
  have hB : ∑ y : Fin (2 * b) → Record n σ, tupleW (condW μ (liveTest letter completed)) y
        * (liveMass μ (liveTest letter completed) * ∑ e, condW μ (liveTest letter completed) e
            * (if (((unionTuple y).union S).union e).prod letter
                ≠ ((unionTuple y).union S).prod letter then 1 else 0))
      = liveMass μ (liveTest letter completed)
        * ∑ z : Fin (2 * b + 1) → Record n σ, tupleW (condW μ (liveTest letter completed)) z
          * (if (((unionTuple (Fin.tail z)).union S).union (z 0)).prod letter
                ≠ ((unionTuple (Fin.tail z)).union S).prod letter then 1 else 0) := by
    rw [sum_pi_succ]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun y _ => ?_
    rw [tupleW_cons, Fin.tail_cons, Fin.cons_zero]
    ring
  rw [hB, mul_comm ((b : ℝ) / (2 * b + 1))]
  refine mul_le_mul_of_nonneg_left ?_ hw0
  have hC : ∑ z : Fin (2 * b + 1) → Record n σ, tupleW (condW μ (liveTest letter completed)) z
        * (if (((unionTuple (Fin.tail z)).union S).union (z 0)).prod letter
              ≠ ((unionTuple (Fin.tail z)).union S).prod letter then 1 else 0)
      = ∑ z : Fin (2 * b + 1) → Record n σ, tupleW (condW μ (liveTest letter completed)) z
        * (if essIdxK letter x S.supp z 0 then 1 else 0) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : tupleW (condW μ (liveTest letter completed)) z = 0
    · rw [hz, zero_mul, zero_mul]
    · have htz : ∀ i, (z i).Truthful x := fun i =>
        hνtr _ (Finset.prod_ne_zero_iff.1 hz i (Finset.mem_univ _))
      rw [G_eq_essIdxK letter x hS htz]
  rw [hC]
  have hD := sum_tupleW_ess_le hνw (by omega : 0 < 2 * b + 1) (essIdxK letter x S.supp)
    (essIdxK_comp_perm letter x S.supp) (card_essIdxK_le letter x hst hb S.supp) 0
  refine hD.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Halving for the saved-history update**: the background is the current saved union. -/
theorem halving_saveBatch (completed : List (Record n σ)) (hc : ∀ A ∈ completed, A.Truthful x)
    (hw : 0 < liveMass μ (liveTest letter completed)) :
    ∑ y : Fin (2 * b) → Record n σ, tupleW (condW μ (liveTest letter completed)) y
        * liveMass μ (liveTest letter (saveBatch completed (unionTuple y)))
      ≤ ((b : ℝ) / (2 * b + 1)) * liveMass μ (liveTest letter completed) :=
  halving_with_background letter x μ hst hb hμ htr completed (truthful_unionList x hc) hw

/-- The raw-batch bound `halving` is the empty-background case (a check). -/
theorem halving_of_empty_background (completed : List (Record n σ))
    (hw : 0 < liveMass μ (liveTest letter completed)) :
    ∑ y : Fin (2 * b) → Record n σ, tupleW (condW μ (liveTest letter completed)) y
        * liveMass μ (liveTest letter (unionTuple y :: completed))
      ≤ ((b : ℝ) / (2 * b + 1)) * liveMass μ (liveTest letter completed) := by
  have h := halving_with_background letter x μ hst hb hμ htr completed (truthful_emptyRec x) hw
  simpa only [union_emptyRec] using h

end Halving

/-! ## The run over rounds -/

section Run

variable (x : Fin n → σ) (μ : Record n σ → ℝ)

/-- **The merger over `R` rounds**: each round is `roundResult`; a failed round stops the
run with the batches saved so far. -/
def mergeRun (b : ℕ) :
    ∀ (R : ℕ), List (Record n σ) → (Fin R → Fin (2 * b) → Fin k → Record n σ) → List (Record n σ)
  | 0, completed, _ => completed
  | R + 1, completed, tbl =>
      let r := roundResult letter b completed (tbl 0)
      if r.2 then mergeRun b R r.1 (Fin.tail tbl) else completed

lemma mergeRun_zero (b : ℕ) (completed : List (Record n σ))
    (tbl : Fin 0 → Fin (2 * b) → Fin k → Record n σ) : mergeRun letter b 0 completed tbl = completed :=
  rfl

lemma mergeRun_succ_of_none {b : ℕ} (hb : 1 ≤ b) {R : ℕ} (completed : List (Record n σ))
    (rows : Fin (2 * b) → Fin k → Record n σ) (rest : Fin R → Fin (2 * b) → Fin k → Record n σ)
    (h : ∃ i, firstLive (liveTest letter completed) (rows i) = none) :
    mergeRun letter b (R + 1) completed (Fin.cons rows rest) = completed := by
  simp only [mergeRun, Fin.cons_zero]
  rw [(roundResult_spec letter hb completed rows).2 h]
  rfl

lemma mergeRun_succ_of_some {b : ℕ} (hb : 1 ≤ b) {R : ℕ} (completed : List (Record n σ))
    (rows : Fin (2 * b) → Fin k → Record n σ) (rest : Fin R → Fin (2 * b) → Fin k → Record n σ)
    (y : Fin (2 * b) → Record n σ)
    (hy : ∀ i, firstLive (liveTest letter completed) (rows i) = some (y i)) :
    mergeRun letter b (R + 1) completed (Fin.cons rows rest)
      = mergeRun letter b R (saveBatch completed (unionTuple y)) rest := by
  simp only [mergeRun, Fin.cons_zero, Fin.tail_cons]
  rw [(roundResult_spec letter hb completed rows).1 y hy]
  rfl

/-- A live record has zero weight when the live mass vanishes. -/
lemma firstLive_eq_none_of_liveMass_zero (hμ : IsWeight μ) {live : Record n σ → Bool}
    (hw : liveMass μ live = 0)
    (row : Fin k → Record n σ) (hrow : tupleW μ row ≠ 0) : firstLive live row = none := by
  have hall : ∀ e, live e = true → μ e = 0 := by
    intro e he
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => by
      show (0 : ℝ) ≤ if live e then μ e else 0
      split_ifs <;> [exact hμ.nonneg e; exact le_rfl])).1 hw e (Finset.mem_univ _)
    rw [if_pos he] at h
    exact h
  have hne : ∀ t, live (row t) = false := fun t => by
    by_contra hc
    have hl : live (row t) = true := by simpa using hc
    exact Finset.prod_ne_zero_iff.1 hrow t (Finset.mem_univ _) (hall _ hl)
  clear hrow hw hall
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Fin.cons_self_tail row, firstLive_cons, if_neg (by rw [hne 0]; decide)]
    exact ih (Fin.tail row) fun t => hne t.succ

variable (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
  (hμ : IsWeight μ) (htr : ∀ e, μ e ≠ 0 → e.Truthful x)
include hst hb hμ htr

/-- **The chain bound** (before the final compression): after `R`
rounds of `2b` draws with `k` proposals each, the live mass is at least `a` with
probability at most `w₀·2^{−R}/a + 2bR·(1−a)^k`. -/
theorem chain_bound (hb1 : 1 ≤ b) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ (R : ℕ) (completed : List (Record n σ)), (∀ A ∈ completed, A.Truthful x) →
      ∑ tbl : Fin R → Fin (2 * b) → Fin k → Record n σ, tupleW (tupleW (tupleW μ)) tbl
          * (if a ≤ liveMass μ (liveTest letter (mergeRun letter b R completed tbl)) then 1 else 0)
        ≤ liveMass μ (liveTest letter completed) * (1 / 2) ^ R / a + R * (2 * b) * (1 - a) ^ k
  | 0, completed, _ => by
    rw [sum_pi_zero, tupleW_zero, mergeRun_zero, one_mul, pow_zero, mul_one]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hw0 : 0 ≤ liveMass μ (liveTest letter completed) := liveMass_nonneg hμ _
    split_ifs with h
    · rw [le_div_iff₀ ha, one_mul]; exact h
    · positivity
  | R + 1, completed, hc => by
    rw [sum_pi_succ]
    simp only [tupleW_cons]
    set w₀ := liveMass μ (liveTest letter completed) with hw₀
    have hw0 : 0 ≤ w₀ := liveMass_nonneg hμ _
    have hw1 : w₀ ≤ 1 := liveMass_le_one hμ _
    have hWrows : IsWeight (tupleW μ (k := k)) := isWeight_tupleW hμ k
    have hWtbl : IsWeight (tupleW (tupleW μ (k := k)) (k := 2 * b)) := isWeight_tupleW hWrows _
    have hRrest : IsWeight (tupleW (tupleW (tupleW μ (k := k)) (k := 2 * b)) (k := R)) :=
      isWeight_tupleW hWtbl R
    have hnn : ∀ rows : Fin (2 * b) → Fin k → Record n σ,
        0 ≤ tupleW (tupleW μ) rows := fun rows => tupleW_nonneg hWrows rows
    rcases hw0.lt_or_eq with hwpos | hwzero
    · -- the inner sums, per first-round table
      have hinner : ∀ rows : Fin (2 * b) → Fin k → Record n σ, tupleW (tupleW μ) rows ≠ 0 →
          ∑ rest : Fin R → Fin (2 * b) → Fin k → Record n σ, tupleW (tupleW (tupleW μ)) rest
              * (if a ≤ liveMass μ (liveTest letter
                  (mergeRun letter b (R + 1) completed (Fin.cons rows rest))) then 1 else 0)
            ≤ (if ∃ i, firstLive (liveTest letter completed) (rows i) = none
                then (if a ≤ w₀ then 1 else 0) else 0)
              + (if hs : ∀ i, (firstLive (liveTest letter completed) (rows i)).isSome
                  then liveMass μ (liveTest letter (saveBatch completed (unionTuple (fun i =>
                    (firstLive (liveTest letter completed) (rows i)).get (hs i)))))
                    * (1 / 2) ^ R / a + R * (2 * b) * (1 - a) ^ k
                  else 0) := by
        intro rows hrows
        by_cases hs : ∀ i, (firstLive (liveTest letter completed) (rows i)).isSome
        · have hnone : ¬ ∃ i, firstLive (liveTest letter completed) (rows i) = none := by
            rintro ⟨i, hi⟩; have := hs i; rw [hi] at this; simp at this
          rw [if_neg hnone, dif_pos hs, zero_add]
          have hy' : ∀ i, firstLive (liveTest letter completed) (rows i)
              = some ((firstLive (liveTest letter completed) (rows i)).get (hs i)) :=
            fun i => (Option.some_get (hs i)).symm
          simp only [mergeRun_succ_of_some letter hb1 completed rows _ _ hy']
          refine chain_bound hb1 ha ha1 R _ ?_
          intro A hA
          rw [saveBatch, List.mem_cons] at hA
          rcases hA with rfl | hA
          · refine Record.truthful_union (truthful_unionTuple fun i => ?_) (truthful_unionList x hc)
            have hrow : tupleW μ (rows i) ≠ 0 :=
              Finset.prod_ne_zero_iff.1 hrows i (Finset.mem_univ _)
            have hmem : ∀ {k' : ℕ} (row : Fin k' → Record n σ) (e : Record n σ),
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
            obtain ⟨t, ht⟩ := hmem (rows i) _ (hy' i)
            rw [← ht]
            exact htr _ (Finset.prod_ne_zero_iff.1 hrow t (Finset.mem_univ _))
          · exact hc A hA
        · have hnone : ∃ i, firstLive (liveTest letter completed) (rows i) = none := by
            push Not at hs
            obtain ⟨i, hi⟩ := hs
            exact ⟨i, Option.not_isSome_iff_eq_none.1 hi⟩
          rw [if_pos hnone, dif_neg hs, add_zero]
          simp only [mergeRun_succ_of_none letter hb1 completed rows _ hnone, ← hw₀]
          rw [← Finset.sum_mul, hRrest.sum_one, one_mul]
      -- assemble
      have hsplit : ∀ rows : Fin (2 * b) → Fin k → Record n σ,
          ∑ rest : Fin R → Fin (2 * b) → Fin k → Record n σ,
            tupleW (tupleW μ) rows * tupleW (tupleW (tupleW μ)) rest
              * (if a ≤ liveMass μ (liveTest letter
                  (mergeRun letter b (R + 1) completed (Fin.cons rows rest))) then 1 else 0)
          = tupleW (tupleW μ) rows * ∑ rest : Fin R → Fin (2 * b) → Fin k → Record n σ,
              tupleW (tupleW (tupleW μ)) rest
                * (if a ≤ liveMass μ (liveTest letter
                    (mergeRun letter b (R + 1) completed (Fin.cons rows rest))) then 1 else 0) := by
        intro rows
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun rest _ => ?_
        ring
      simp only [hsplit]
      have hstep : ∀ rows : Fin (2 * b) → Fin k → Record n σ,
          tupleW (tupleW μ) rows * ∑ rest : Fin R → Fin (2 * b) → Fin k → Record n σ,
              tupleW (tupleW (tupleW μ)) rest
                * (if a ≤ liveMass μ (liveTest letter
                    (mergeRun letter b (R + 1) completed (Fin.cons rows rest))) then 1 else 0)
            ≤ tupleW (tupleW μ) rows
              * ((if ∃ i, firstLive (liveTest letter completed) (rows i) = none
                  then (if a ≤ w₀ then 1 else 0) else 0)
                + (if hs : ∀ i, (firstLive (liveTest letter completed) (rows i)).isSome
                    then liveMass μ (liveTest letter (saveBatch completed (unionTuple (fun i =>
                      (firstLive (liveTest letter completed) (rows i)).get (hs i)))))
                      * (1 / 2) ^ R / a + R * (2 * b) * (1 - a) ^ k
                    else 0)) := by
        intro rows
        by_cases hrows : tupleW (tupleW μ) rows = 0
        · rw [hrows, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hinner rows hrows) (hnn rows)
      refine (Finset.sum_le_sum fun rows _ => hstep rows).trans ?_
      simp only [mul_add, Finset.sum_add_distrib]
      -- the failure term
      have h1 : ∑ rows : Fin (2 * b) → Fin k → Record n σ, tupleW (tupleW μ) rows
            * (if ∃ i, firstLive (liveTest letter completed) (rows i) = none
                then (if a ≤ w₀ then 1 else 0) else 0)
          ≤ (2 * b) * (1 - a) ^ k := by
        by_cases haw : a ≤ w₀
        · simp only [if_pos haw]
          have hub := sum_tupleW_exists_le hWrows (m := 2 * b)
            (fun row : Fin k → Record n σ => firstLive (liveTest letter completed) row = none)
          rw [prob_firstLive_none hμ] at hub
          refine hub.trans ?_
          push_cast
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_left₀ (by linarith) (by linarith) k
        · simp only [if_neg haw, ite_self, mul_zero, Finset.sum_const_zero]
          positivity
      -- the success term
      have h2 : ∑ rows : Fin (2 * b) → Fin k → Record n σ, tupleW (tupleW μ) rows
            * (if hs : ∀ i, (firstLive (liveTest letter completed) (rows i)).isSome
                then liveMass μ (liveTest letter (saveBatch completed (unionTuple (fun i =>
                  (firstLive (liveTest letter completed) (rows i)).get (hs i)))))
                  * (1 / 2) ^ R / a + R * (2 * b) * (1 - a) ^ k
                else 0)
          ≤ w₀ / 2 * (1 / 2) ^ R / a + R * (2 * b) * (1 - a) ^ k := by
        rw [expect_batch' hμ (liveTest letter completed) hwpos k (2 * b)
          (fun y => liveMass μ (liveTest letter (saveBatch completed (unionTuple y))) * (1 / 2) ^ R / a
            + R * (2 * b) * (1 - a) ^ k)]
        have hH := halving_saveBatch letter x μ hst hb hμ htr completed hc hwpos
        have hc1 : (1 - (1 - w₀) ^ k) ^ (2 * b) ≤ 1 := by
          refine pow_le_one₀ ?_ ?_
          · have : (1 - w₀) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
            linarith
          · have : 0 ≤ (1 - w₀) ^ k := pow_nonneg (by linarith) k
            linarith
        have hνw : IsWeight (condW μ (liveTest letter completed)) := isWeight_condW hμ hwpos
        have hsum : ∑ y : Fin (2 * b) → Record n σ, tupleW (condW μ (liveTest letter completed)) y
              * (liveMass μ (liveTest letter (saveBatch completed (unionTuple y))) * (1 / 2) ^ R / a
                + R * (2 * b) * (1 - a) ^ k)
            = (∑ y : Fin (2 * b) → Record n σ, tupleW (condW μ (liveTest letter completed)) y
                * liveMass μ (liveTest letter (saveBatch completed (unionTuple y)))) * (1 / 2) ^ R / a
              + R * (2 * b) * (1 - a) ^ k := by
          have e1 : ∀ y : Fin (2 * b) → Record n σ,
              tupleW (condW μ (liveTest letter completed)) y
                * (liveMass μ (liveTest letter (saveBatch completed (unionTuple y))) * (1 / 2) ^ R / a
                  + R * (2 * b) * (1 - a) ^ k)
              = tupleW (condW μ (liveTest letter completed)) y
                  * liveMass μ (liveTest letter (saveBatch completed (unionTuple y))) * ((1 / 2) ^ R * a⁻¹)
                + tupleW (condW μ (liveTest letter completed)) y * (R * (2 * b) * (1 - a) ^ k) :=
            fun y => by ring
          simp only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, sum_tupleW hνw, one_mul]
          ring
        rw [hsum]
        have hb2 : (b : ℝ) / (2 * b + 1) * w₀ ≤ w₀ / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        have hnonneg : 0 ≤ (∑ y : Fin (2 * b) → Record n σ,
              tupleW (condW μ (liveTest letter completed)) y
                * liveMass μ (liveTest letter (saveBatch completed (unionTuple y)))) * (1 / 2) ^ R / a
            + R * (2 * b) * (1 - a) ^ k := by
          have : 0 ≤ ∑ y : Fin (2 * b) → Record n σ,
              tupleW (condW μ (liveTest letter completed)) y
                * liveMass μ (liveTest letter (saveBatch completed (unionTuple y))) :=
            Finset.sum_nonneg fun y _ => mul_nonneg (tupleW_nonneg hνw y) (liveMass_nonneg hμ _)
          have : (0 : ℝ) ≤ (1 - a) ^ k := pow_nonneg (by linarith) k
          positivity
        calc (1 - (1 - w₀) ^ k) ^ (2 * b) * _ ≤ 1 * _ :=
              mul_le_mul_of_nonneg_right hc1 hnonneg
          _ ≤ w₀ / 2 * (1 / 2) ^ R / a + R * (2 * b) * (1 - a) ^ k := by
              rw [one_mul]
              have : (0 : ℝ) ≤ (1 - a) ^ k := pow_nonneg (by linarith) k
              have h3 : (∑ y : Fin (2 * b) → Record n σ,
                    tupleW (condW μ (liveTest letter completed)) y
                      * liveMass μ (liveTest letter (saveBatch completed (unionTuple y)))) * (1 / 2) ^ R / a
                  ≤ w₀ / 2 * (1 / 2) ^ R / a := by
                refine div_le_div_of_nonneg_right ?_ ha.le
                exact mul_le_mul_of_nonneg_right (hH.trans hb2) (by positivity)
              linarith
      calc _ ≤ (2 * b) * (1 - a) ^ k + (w₀ / 2 * (1 / 2) ^ R / a + R * (2 * b) * (1 - a) ^ k) :=
            add_le_add h1 h2
        _ = w₀ * (1 / 2) ^ (R + 1) / a + (R + 1 : ℕ) * (2 * b) * (1 - a) ^ k := by
            push_cast; ring
    · -- zero live mass: every proposal is dead, the run returns `completed`
      have hzero : ∀ rows : Fin (2 * b) → Fin k → Record n σ, tupleW (tupleW μ) rows ≠ 0 →
          ∃ i, firstLive (liveTest letter completed) (rows i) = none := by
        intro rows hrows
        refine ⟨⟨0, by omega⟩, ?_⟩
        exact firstLive_eq_none_of_liveMass_zero μ hμ hwzero.symm _
          (Finset.prod_ne_zero_iff.1 hrows _ (Finset.mem_univ _))
      have hterm : ∀ (rows : Fin (2 * b) → Fin k → Record n σ)
          (rest : Fin R → Fin (2 * b) → Fin k → Record n σ),
          tupleW (tupleW μ) rows * tupleW (tupleW (tupleW μ)) rest
            * (if a ≤ liveMass μ (liveTest letter
                (mergeRun letter b (R + 1) completed (Fin.cons rows rest))) then 1 else 0) = 0 := by
        intro rows rest
        by_cases hrows : tupleW (tupleW μ) rows = 0
        · rw [hrows, zero_mul, zero_mul]
        · rw [mergeRun_succ_of_none letter hb1 completed rows rest (hzero rows hrows), ← hw₀,
            ← hwzero, if_neg (by linarith), mul_zero]
      simp only [hterm, Finset.sum_const_zero]
      have : (0 : ℝ) ≤ (1 - a) ^ k := pow_nonneg (by linarith) k
      positivity

end Run

/-! ## The guarantee for the compressed union -/

section Final

variable [DecidableLE M] (x : Fin n → σ) (μ : Record n σ → ℝ)

/-- **The merger's output**: the compression of the union of the saved batches. -/
noncomputable def mergeK (b : ℕ) (R : ℕ) (tbl : Fin R → Fin (2 * b) → Fin k → Record n σ) :
    Record n σ :=
  Record.compress letter b (unionList (mergeRun letter b R [] tbl))

/-- **Discarded candidates are dominated.** -/
lemma prod_le_of_not_live (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    (completed : List (Record n σ)) (hc : ∀ A ∈ completed, A.Truthful x) {U : Record n σ}
    (hU : U.Truthful x) (hlive : liveTest letter completed U = false) :
    U.prod letter ≤ (Record.compress letter b (unionList completed)).prod letter := by
  have hex : ∃ A ∈ completed, (A.union U).prod letter = A.prod letter := by
    simp only [liveTest, decide_eq_false_iff_not, not_forall, not_not, exists_prop] at hlive
    exact hlive
  obtain ⟨A, hA, hAU⟩ := hex
  have hAt := hc A hA
  rw [(Record.compress_spec letter hb (unionList completed)).2.2,
    Record.prod_of_truthful letter (truthful_unionList x hc), Record.prod_of_truthful letter hU]
  rw [prod_union_truthful letter x hAt hU, Record.prod_of_truthful letter hAt] at hAU
  calc subwordProd letter x U.supp
      ≤ subwordProd letter x (A.supp ∪ U.supp) :=
        hst.subwordProd_mono letter x Finset.subset_union_right
    _ = subwordProd letter x A.supp := hAU
    _ ≤ subwordProd letter x (unionList completed).supp :=
        hst.subwordProd_mono letter x (supp_subset_unionList hA)

/-- The undominated mass is at most the live mass. -/
lemma undominated_le_liveMass (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    (hμ : IsWeight μ) (htr : ∀ e, μ e ≠ 0 → e.Truthful x) (completed : List (Record n σ))
    (hc : ∀ A ∈ completed, A.Truthful x) :
    ∑ U, μ U * (if U.prod letter ≤ (Record.compress letter b (unionList completed)).prod letter
        then 0 else 1)
      ≤ liveMass μ (liveTest letter completed) := by
  unfold liveMass
  refine Finset.sum_le_sum fun U _ => ?_
  by_cases hμU : μ U = 0
  · rw [hμU, zero_mul]; split_ifs <;> exact le_rfl
  · by_cases hl : liveTest letter completed U = true
    · rw [if_pos hl]
      split_ifs
      · rw [mul_zero]; exact hμ.nonneg U
      · rw [mul_one]
    · have hl' : liveTest letter completed U = false := by simpa using hl
      rw [if_neg hl, if_pos (prod_le_of_not_live letter x hst hb completed hc (htr U hμU) hl'),
        mul_zero]

/-- Every batch saved by a run on a table of truthful records is truthful. -/
lemma mergeRun_truthful (hμ : IsWeight μ) (htr : ∀ e, μ e ≠ 0 → e.Truthful x) {b : ℕ}
    (hb1 : 1 ≤ b) :
    ∀ (R : ℕ) (completed : List (Record n σ)), (∀ A ∈ completed, A.Truthful x) →
      ∀ tbl : Fin R → Fin (2 * b) → Fin k → Record n σ, tupleW (tupleW (tupleW μ)) tbl ≠ 0 →
        ∀ A ∈ mergeRun letter b R completed tbl, A.Truthful x
  | 0, completed, hc, _, _ => hc
  | R + 1, completed, hc, tbl, htbl => by
    rw [← Fin.cons_self_tail tbl] at htbl ⊢
    rw [tupleW_cons] at htbl
    have hrows : tupleW (tupleW μ) (tbl 0) ≠ 0 := left_ne_zero_of_mul htbl
    have hrest : tupleW (tupleW (tupleW μ)) (Fin.tail tbl) ≠ 0 := right_ne_zero_of_mul htbl
    by_cases hs : ∀ i, (firstLive (liveTest letter completed) (tbl 0 i)).isSome
    · have hy' : ∀ i, firstLive (liveTest letter completed) (tbl 0 i)
          = some ((firstLive (liveTest letter completed) (tbl 0 i)).get (hs i)) :=
        fun i => (Option.some_get (hs i)).symm
      rw [mergeRun_succ_of_some letter hb1 completed (tbl 0) _ _ hy']
      refine mergeRun_truthful hμ htr hb1 R _ ?_ _ hrest
      intro A hA
      rw [saveBatch, List.mem_cons] at hA
      rcases hA with rfl | hA
      · refine Record.truthful_union (truthful_unionTuple fun i => ?_) (truthful_unionList x hc)
        have hrow : tupleW μ (tbl 0 i) ≠ 0 :=
          Finset.prod_ne_zero_iff.1 hrows i (Finset.mem_univ _)
        have hmem : ∀ {k' : ℕ} (row : Fin k' → Record n σ) (e : Record n σ),
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
        exact htr _ (Finset.prod_ne_zero_iff.1 hrow t (Finset.mem_univ _))
      · exact hc A hA
    · have hnone : ∃ i, firstLive (liveTest letter completed) (tbl 0 i) = none := by
        push Not at hs
        obtain ⟨i, hi⟩ := hs
        exact ⟨i, Option.not_isSome_iff_eq_none.1 hi⟩
      rw [mergeRun_succ_of_none letter hb1 completed (tbl 0) _ hnone]
      exact hc

/-- **`lem:beta-sampling`, the small-mass guarantee `(M)`**: the candidate mass not
dominated by the merger's output is at least `a` with probability at most
`2^{−R}/a + 2bR·(1−a)^k`. -/
theorem merge_small_mass (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    (hμ : IsWeight μ) (htr : ∀ e, μ e ≠ 0 → e.Truthful x) (hb1 : 1 ≤ b) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (R : ℕ) :
    ∑ tbl : Fin R → Fin (2 * b) → Fin k → Record n σ, tupleW (tupleW (tupleW μ)) tbl
        * (if a ≤ ∑ U, μ U * (if U.prod letter ≤ (mergeK letter b R tbl).prod letter then 0 else 1)
            then 1 else 0)
      ≤ (1 / 2) ^ R / a + R * (2 * b) * (1 - a) ^ k := by
  have hW : IsWeight (tupleW (tupleW (tupleW μ (k := k)) (k := 2 * b)) (k := R)) :=
    isWeight_tupleW (isWeight_tupleW (isWeight_tupleW hμ k) _) R
  have hchain := chain_bound letter x μ hst hb hμ htr hb1 ha ha1 (k := k) R []
    (fun A hA => by simp at hA)
  have hnil : liveMass μ (liveTest letter []) = 1 := by
    unfold liveMass; simp only [liveTest_nil, if_true]; exact hμ.sum_one
  rw [hnil, one_mul] at hchain
  refine le_trans ?_ hchain
  refine Finset.sum_le_sum fun tbl _ => ?_
  by_cases htbl : tupleW (tupleW (tupleW μ)) tbl = 0
  · rw [htbl, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_
      (tupleW_nonneg (isWeight_tupleW (isWeight_tupleW hμ k) (2 * b)) tbl)
    have hc := mergeRun_truthful letter x μ hμ htr hb1 R [] (fun A hA => by simp at hA) tbl htbl
    have hle := undominated_le_liveMass letter x μ hst hb hμ htr _ hc
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans hle) h2
    · norm_num
    · exact le_rfl

end Final

end Merger

end MonoidProduct
