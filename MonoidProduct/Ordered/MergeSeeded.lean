import MonoidProduct.Ordered.Merge
import QuantumQueryComplexity.Adaptive

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# The seeded merger: duals and the probability transfer (`lem:beta-sampling`)

Candidates are fixed-seed functions `cand ω : (Fin n → σ) → Record n σ`, each
with a dual of cost `T`.  A seed table `ωs` fills every proposal slot of every
round; for a fixed table the merger is a deterministic function of the input:

* `roundChain` runs the rounds as adaptive calls (`HasDual.adaptiveCall`), each round
  a rejection tree of `2b` draws (`DrawProgram.hasDual_run`), at cost
  `8·T·2b·√k` per round; `hasDual_mergeK_seeded` then gives the compressed
  output `mergeK` at cost `2·R·8·T·2b·√k` (`postcomp_of_determined`);
* `seeded_small_mass` transfers `merge_small_mass` to the seed law: the
  record table is the coordinatewise pushforward of the seed table
  (`sum_tupleW_map`, three levels), so the undominated candidate mass — under
  the candidate law `pushW ν (cand · x)` — is at least `a` with probability at
  most `2^{−R}/a + 2bR(1−a)^k` over the seeds.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity

namespace Seeded

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) {n k : ℕ}

/-! ## The run with a flag, front and back -/

/-- One round from a flagged state (a failed run is left unchanged). -/
def stepRound (b : ℕ) (s : List (Record n σ) × Bool) (rows : Fin (2 * b) → Fin k → Record n σ) :
    List (Record n σ) × Bool :=
  if s.2 then roundResult letter b s.1 rows else s

/-- The flagged run, peeling rounds from the front. -/
def mergeRunF (b : ℕ) :
    ∀ (R : ℕ), List (Record n σ) × Bool → (Fin R → Fin (2 * b) → Fin k → Record n σ)
      → List (Record n σ) × Bool
  | 0, s, _ => s
  | R + 1, s, tbl => mergeRunF b R (stepRound letter b s (tbl 0)) (Fin.tail tbl)

lemma mergeRunF_of_not_alive (b : ℕ) :
    ∀ (R : ℕ) (s : List (Record n σ) × Bool) (tbl : Fin R → Fin (2 * b) → Fin k → Record n σ),
      s.2 = false → mergeRunF letter b R s tbl = s
  | 0, _, _, _ => rfl
  | R + 1, s, tbl, hs => by
    simp only [mergeRunF, stepRound, hs, Bool.false_eq_true, if_false]
    exact mergeRunF_of_not_alive b R s (Fin.tail tbl) hs

lemma roundResult_fst_of_snd_false {b : ℕ} (hb : 1 ≤ b) (c : List (Record n σ))
    (rows : Fin (2 * b) → Fin k → Record n σ) (h : (roundResult letter b c rows).2 = false) :
    (roundResult letter b c rows).1 = c := by
  by_cases hs : ∀ i, (firstLive (liveTest letter c) (rows i)).isSome
  · have := (roundResult_spec letter hb c rows).1 (fun i => (firstLive (liveTest letter c) (rows i)).get (hs i))
      (fun i => (Option.some_get (hs i)).symm)
    rw [this] at h
    simp at h
  · have hnone : ∃ i, firstLive (liveTest letter c) (rows i) = none := by
      push Not at hs
      obtain ⟨i, hi⟩ := hs
      exact ⟨i, Option.not_isSome_iff_eq_none.1 hi⟩
    rw [(roundResult_spec letter hb c rows).2 hnone]

/-- The unflagged run is the first component of the flagged run. -/
lemma mergeRun_eq_mergeRunF {b : ℕ} (hb : 1 ≤ b) :
    ∀ (R : ℕ) (c : List (Record n σ)) (tbl : Fin R → Fin (2 * b) → Fin k → Record n σ),
      mergeRun letter b R c tbl = (mergeRunF letter b R (c, true) tbl).1
  | 0, _, _ => rfl
  | R + 1, c, tbl => by
    simp only [mergeRun, mergeRunF, stepRound, if_true]
    cases hr : (roundResult letter b c (tbl 0)).2
    · rw [if_neg (by simp), mergeRunF_of_not_alive letter b R _ _ (by
        show (roundResult letter b c (tbl 0)).2 = false; exact hr)]
      exact (roundResult_fst_of_snd_false letter hb c (tbl 0) hr).symm
    · rw [if_pos rfl, mergeRun_eq_mergeRunF hb R _ (Fin.tail tbl)]
      have : ((roundResult letter b c (tbl 0)).1, true) = roundResult letter b c (tbl 0) :=
        Prod.ext rfl hr.symm
      rw [this]

/-- Peeling the last round. -/
lemma mergeRunF_snoc (b : ℕ) :
    ∀ (R : ℕ) (s : List (Record n σ) × Bool) (tbl : Fin R → Fin (2 * b) → Fin k → Record n σ)
      (r : Fin (2 * b) → Fin k → Record n σ),
      mergeRunF letter b (R + 1) s (Fin.snoc tbl r) = stepRound letter b (mergeRunF letter b R s tbl) r
  | 0, s, tbl, r => by
    simp only [mergeRunF, Fin.snoc]
    rfl
  | R + 1, s, tbl, r => by
    have h0 : (Fin.snoc tbl r : Fin (R + 2) → Fin (2 * b) → Fin k → Record n σ) 0 = tbl 0 := by
      simp [Fin.snoc]
    have htail : Fin.tail (Fin.snoc tbl r : Fin (R + 2) → Fin (2 * b) → Fin k → Record n σ)
        = Fin.snoc (Fin.tail tbl) r := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.tail, Fin.succ_last, Fin.snoc_last]
      · intro j
        show (Fin.snoc tbl r : Fin (R + 2) → Fin (2 * b) → Fin k → Record n σ)
            (Fin.succ (Fin.castSucc j))
          = (Fin.snoc (Fin.tail tbl) r : Fin (R + 1) → Fin (2 * b) → Fin k → Record n σ)
            (Fin.castSucc j)
        rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        rfl
    simp only [mergeRunF, h0, htail]
    exact mergeRunF_snoc b R _ (Fin.tail tbl) r

/-! ## The roundChain of rounds as adaptive calls -/

/-- Transcripts of `ρ` rounds. -/
def RTrans (S : Type) : ℕ → Type
  | 0 => Unit
  | ρ + 1 => RTrans S ρ × S

def decEqRTrans (S : Type) [DecidableEq S] : ∀ ρ, DecidableEq (RTrans S ρ)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | ρ + 1 => letI := decEqRTrans S ρ; inferInstanceAs (DecidableEq (RTrans S ρ × S))

instance instDecidableEqRTrans {S : Type} [DecidableEq S] {ρ : ℕ} : DecidableEq (RTrans S ρ) :=
  decEqRTrans S ρ

/-- The last state of a transcript. -/
def lastState {S : Type} (s₀ : S) : ∀ {ρ : ℕ}, RTrans S ρ → S
  | 0, _ => s₀
  | _ + 1, t => t.2

/-- A round's raw state: the rejection program's state and its flag. -/
abbrev RState (n : ℕ) (σ : Type) := (List (Record n σ) × Record n σ) × Bool

/-- The initial raw state. -/
def rInit : RState n σ := (([], emptyRec), true)

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- One round from the previous raw state, on the candidates of the seed row `ωr`. -/
def roundFn (b : ℕ) (cand : Ω → (Fin n → σ) → Record n σ) (ωr : Fin (2 * b) → Fin k → Ω)
    (prev : RState n σ) (x : Fin n → σ) : RState n σ :=
  if prev.2 then
    (DrawProgram.run (mergeProg letter b) (2 * b) k (prev.1.1, emptyRec)).eval
      (fun p => cand (ωr p.1 p.2) x)
  else prev

/-- The roundChain of rounds, round `ρ` using the seed rows `ωs ρ`. -/
def roundChain (b : ℕ) (cand : Ω → (Fin n → σ) → Record n σ) (ωs : ℕ → Fin (2 * b) → Fin k → Ω) :
    ∀ ρ : ℕ, (Fin n → σ) → RTrans (RState n σ) ρ
  | 0 => fun _ => ()
  | ρ + 1 => fun x =>
      (roundChain b cand ωs ρ x, roundFn letter b cand (ωs ρ) (lastState rInit (roundChain b cand ωs ρ x)) x)

/-- **The roundChain has a dual of cost `ρ·8·T·2b·√k`.** -/
theorem hasDual_roundChain (b : ℕ) (hb : 1 ≤ b) (hk : 1 ≤ k) (cand : Ω → (Fin n → σ) → Record n σ)
    (ωs : ℕ → Fin (2 * b) → Fin k → Ω) {T : ℝ} (hT : 0 ≤ T) (hc : ∀ ω, HasDual (cand ω) T) :
    ∀ ρ : ℕ, HasDual (roundChain letter b cand ωs ρ)
      (ρ * (8 * T * ((2 * b : ℕ) : ℝ) * Real.sqrt k))
  | 0 => by
    rw [Nat.cast_zero, zero_mul]
    exact hasDual_const fun _ _ => rfl
  | ρ + 1 => by
    have ih := hasDual_roundChain b hb hk cand ωs hT hc ρ
    have hstep : ∀ d : RTrans (RState n σ) ρ,
        HasDual (fun x => roundFn letter b cand (ωs ρ) (lastState rInit d) x)
          (8 * T * ((2 * b : ℕ) : ℝ) * Real.sqrt k) := by
      intro d
      unfold roundFn
      by_cases hd : (lastState rInit d).2 = true
      · simp only [hd, if_true]
        exact DrawProgram.hasDual_run (by omega) hk _ (fun p => cand (ωs ρ p.1 p.2)) hT
          (fun p => hc _)
      · simp only [hd, Bool.false_eq_true, if_false]
        refine (hasDual_const fun _ _ => rfl).mono ?_
        have := Real.sqrt_nonneg (k : ℝ)
        have : (0 : ℝ) ≤ ((2 * b : ℕ) : ℝ) := by positivity
        positivity
    classical
    -- recode the descriptor into its (finite) range
    have hD' : HasDual (fun x => (⟨roundChain letter b cand ωs ρ x, Set.mem_range_self x⟩ :
        Set.range (roundChain letter b cand ωs ρ))) (ρ * (8 * T * ((2 * b : ℕ) : ℝ) * Real.sqrt k)) :=
      ih.ofKer fun x y => Subtype.ext_iff.symm
    have h := HasDual.adaptiveCall
      (D := fun x => (⟨roundChain letter b cand ωs ρ x, Set.mem_range_self x⟩ :
        Set.range (roundChain letter b cand ωs ρ)))
      (T := fun d x => roundFn letter b cand (ωs ρ) (lastState rInit d.val) x) hD'
      (fun d => hstep d.val)
    refine (h.ofKer fun x y => ?_).mono (le_of_eq ?_)
    · constructor
      · intro h
        have h1 : roundChain letter b cand ωs ρ x = roundChain letter b cand ωs ρ y :=
          Subtype.ext_iff.1 (congrArg Prod.fst h)
        have h2 : roundFn letter b cand (ωs ρ) (lastState rInit (roundChain letter b cand ωs ρ x)) x
            = roundFn letter b cand (ωs ρ) (lastState rInit (roundChain letter b cand ωs ρ y)) y :=
          congrArg Prod.snd h
        show (roundChain letter b cand ωs ρ x,
            roundFn letter b cand (ωs ρ) (lastState rInit (roundChain letter b cand ωs ρ x)) x)
          = (roundChain letter b cand ωs ρ y,
            roundFn letter b cand (ωs ρ) (lastState rInit (roundChain letter b cand ωs ρ y)) y)
        exact Prod.ext h1 h2
      · intro h
        have h' : (roundChain letter b cand ωs ρ x,
            roundFn letter b cand (ωs ρ) (lastState rInit (roundChain letter b cand ωs ρ x)) x)
          = (roundChain letter b cand ωs ρ y,
            roundFn letter b cand (ωs ρ) (lastState rInit (roundChain letter b cand ωs ρ y)) y) := h
        have h1 : roundChain letter b cand ωs ρ x = roundChain letter b cand ωs ρ y := congrArg Prod.fst h'
        have h2 : roundFn letter b cand (ωs ρ) (lastState rInit (roundChain letter b cand ωs ρ x)) x
            = roundFn letter b cand (ωs ρ) (lastState rInit (roundChain letter b cand ωs ρ y)) y :=
          congrArg Prod.snd h'
        exact Prod.ext (Subtype.ext h1) h2
    · push_cast
      ring

/-- The saved batches and the flag of a raw state. -/
def projR (s : RState n σ) : List (Record n σ) × Bool := (s.1.1, s.2)

lemma projR_roundFn (b : ℕ) (cand : Ω → (Fin n → σ) → Record n σ) (ωr : Fin (2 * b) → Fin k → Ω)
    (prev : RState n σ) (x : Fin n → σ) :
    projR (roundFn letter b cand ωr prev x)
      = stepRound letter b (projR prev) (fun i t => cand (ωr i t) x) := by
  unfold roundFn stepRound projR
  by_cases h : prev.2 = true
  · simp only [h, if_true]
    rw [DrawProgram.eval_run_eq_foldRows]
    rfl
  · simp only [h, Bool.false_eq_true, if_false]

/-- **The roundChain computes the flagged run.** -/
lemma projR_roundChain (b : ℕ) (cand : Ω → (Fin n → σ) → Record n σ) (ωs : ℕ → Fin (2 * b) → Fin k → Ω)
    (x : Fin n → σ) :
    ∀ R : ℕ, projR (lastState rInit (roundChain letter b cand ωs R x))
      = mergeRunF letter b R ([], true) (fun ρ : Fin R => fun i t => cand (ωs ρ i t) x)
  | 0 => rfl
  | R + 1 => by
    have hsn : (fun ρ : Fin (R + 1) => fun i t => cand (ωs ρ i t) x)
        = Fin.snoc (fun ρ : Fin R => fun i t => cand (ωs ρ i t) x) (fun i t => cand (ωs R i t) x) := by
      funext ρ
      refine Fin.lastCases ?_ ?_ ρ
      · simp [Fin.snoc_last]
      · intro j; simp [Fin.snoc_castSucc]
    rw [hsn, mergeRunF_snoc, ← projR_roundChain b cand ωs x R]
    exact projR_roundFn letter b cand (ωs R) _ x

/-- **The seeded merger's output has a dual of cost `2·R·8·T·2b·√k`.** -/
theorem hasDual_mergeK_seeded (b : ℕ) (hb : 1 ≤ b) (hk : 1 ≤ k)
    (cand : Ω → (Fin n → σ) → Record n σ) {T : ℝ} (hT : 0 ≤ T) (hc : ∀ ω, HasDual (cand ω) T)
    (R : ℕ) (ωs : ℕ → Fin (2 * b) → Fin k → Ω) :
    HasDual (fun x => mergeK letter b R (fun ρ : Fin R => fun i t => cand (ωs ρ i t) x))
      (2 * (R * (8 * T * ((2 * b : ℕ) : ℝ) * Real.sqrt k))) := by
  have : Nonempty (Record n σ) := ⟨emptyRec⟩
  have hnn : (0 : ℝ) ≤ R * (8 * T * ((2 * b : ℕ) : ℝ) * Real.sqrt k) := by
    have := Real.sqrt_nonneg (k : ℝ)
    have : (0 : ℝ) ≤ ((2 * b : ℕ) : ℝ) := by positivity
    positivity
  refine HasDual.postcomp_of_determined hnn (hasDual_roundChain letter b hb hk cand ωs hT hc R) ?_
  intro x y hxy
  unfold mergeK
  rw [mergeRun_eq_mergeRunF letter hb, mergeRun_eq_mergeRunF letter hb,
    ← projR_roundChain letter b cand ωs x R, ← projR_roundChain letter b cand ωs y R, hxy]

/-! ## Truthfulness and size of the output -/

/-- Every batch saved by a run on a table of truthful records is truthful. -/
lemma mergeRun_truthful_of_entries (x : Fin n → σ) {b : ℕ} (hb1 : 1 ≤ b) :
    ∀ (R : ℕ) (completed : List (Record n σ)), (∀ A ∈ completed, A.Truthful x) →
      ∀ tbl : Fin R → Fin (2 * b) → Fin k → Record n σ, (∀ ρ i t, (tbl ρ i t).Truthful x) →
        ∀ A ∈ mergeRun letter b R completed tbl, A.Truthful x
  | 0, _, hc, _, _ => hc
  | R + 1, completed, hc, tbl, hent => by
    rw [← Fin.cons_self_tail tbl]
    by_cases hs : ∀ i, (firstLive (liveTest letter completed) (tbl 0 i)).isSome
    · have hy' : ∀ i, firstLive (liveTest letter completed) (tbl 0 i)
          = some ((firstLive (liveTest letter completed) (tbl 0 i)).get (hs i)) :=
        fun i => (Option.some_get (hs i)).symm
      rw [mergeRun_succ_of_some letter hb1 completed (tbl 0) _ _ hy']
      refine mergeRun_truthful_of_entries x hb1 R _ ?_ _ (fun ρ i t => hent _ i t)
      intro A hA
      rw [saveBatch, List.mem_cons] at hA
      rcases hA with rfl | hA
      · refine Record.truthful_union (truthful_unionTuple fun i => ?_) (truthful_unionList x hc)
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
        exact hent 0 i t
      · exact hc A hA
    · have hnone : ∃ i, firstLive (liveTest letter completed) (tbl 0 i) = none := by
        push Not at hs
        obtain ⟨i, hi⟩ := hs
        exact ⟨i, Option.not_isSome_iff_eq_none.1 hi⟩
      rw [mergeRun_succ_of_none letter hb1 completed (tbl 0) _ hnone]
      exact hc

/-- **The output is a truthful record of at most `b` positions.** -/
theorem mergeK_spec {b : ℕ} (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) (x : Fin n → σ) (R : ℕ)
    (tbl : Fin R → Fin (2 * b) → Fin k → Record n σ) (hent : ∀ ρ i t, (tbl ρ i t).Truthful x) :
    (mergeK letter b R tbl).Truthful x ∧ (mergeK letter b R tbl).supp.card ≤ b :=
  ⟨Record.truthful_compress letter
      (truthful_unionList x (mergeRun_truthful_of_entries letter x hb1 R [] (fun A hA => by simp at hA)
        tbl hent)) b,
    (Record.compress_spec letter hb _).2.1⟩

/-! ## The probability transfer from seeds to records -/

/-- The pushforward of an i.i.d. tuple along a coordinatewise map is the i.i.d. tuple of the
pushforward. -/
lemma pushW_tupleW {E : Type} [Fintype E] [DecidableEq E] {ν : Ω → ℝ} (hν : IsWeight ν)
    (φ : Ω → E) (k : ℕ) :
    pushW (tupleW ν (k := k)) (fun ω i => φ (ω i)) = tupleW (pushW ν φ) := by
  funext z
  have h := sum_tupleW_map hν φ (fun z' : Fin k → E => if z' = z then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_ite_eq' Finset.univ z, if_pos (Finset.mem_univ _)] at h
  rw [← h]
  unfold pushW
  rfl

/-- The three-level transfer. -/
theorem sum_tupleW_map3 {E : Type} [Fintype E] [DecidableEq E] {ν : Ω → ℝ} (hν : IsWeight ν)
    (φ : Ω → E) {R m : ℕ} (F : (Fin R → Fin m → Fin k → E) → ℝ) :
    ∑ ωs : Fin R → Fin m → Fin k → Ω, tupleW (tupleW (tupleW ν)) ωs
        * F (fun ρ i t => φ (ωs ρ i t))
      = ∑ tbl : Fin R → Fin m → Fin k → E, tupleW (tupleW (tupleW (pushW ν φ))) tbl * F tbl := by
  have h1 := sum_tupleW_map (isWeight_tupleW (isWeight_tupleW hν k) m)
    (fun (ω : Fin m → Fin k → Ω) => fun i t => φ (ω i t)) (k := R) F
  have e1 : pushW (tupleW ν) (fun (row : Fin k → Ω) t => φ (row t)) = tupleW (pushW ν φ) :=
    pushW_tupleW hν φ k
  have e2 : pushW (tupleW (tupleW ν)) (fun (ω : Fin m → Fin k → Ω) i t => φ (ω i t))
      = tupleW (tupleW (pushW ν φ)) := by
    rw [← e1]
    exact pushW_tupleW (isWeight_tupleW hν k) (fun (row : Fin k → Ω) t => φ (row t)) m
  rw [h1, e2]

/-- **`lem:beta-sampling`, seeded form**: over the seed law, the candidate mass not
dominated by the merger's output is at least `a` with probability at most
`2^{−R}/a + 2bR(1−a)^k`. -/
theorem seeded_small_mass [DecidableLE M] (hst : IsStableOrder M) {b : ℕ}
    (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) {ν : Ω → ℝ} (hν : IsWeight ν)
    (cand : Ω → (Fin n → σ) → Record n σ) (hcT : ∀ ω x, (cand ω x).Truthful x) (x : Fin n → σ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (R : ℕ) :
    ∑ ωs : Fin R → Fin (2 * b) → Fin k → Ω, tupleW (tupleW (tupleW ν)) ωs
        * (if a ≤ ∑ U, pushW ν (fun ω => cand ω x) U
              * (if U.prod letter ≤ (mergeK letter b R (fun ρ i t => cand (ωs ρ i t) x)).prod letter
                  then 0 else 1)
            then 1 else 0)
      ≤ (1 / 2) ^ R / a + R * (2 * b) * (1 - a) ^ k := by
  rw [sum_tupleW_map3 hν (fun ω => cand ω x)
    (F := fun tbl => if a ≤ ∑ U, pushW ν (fun ω => cand ω x) U
      * (if U.prod letter ≤ (mergeK letter b R tbl).prod letter then 0 else 1) then 1 else 0)]
  refine merge_small_mass letter x (pushW ν fun ω => cand ω x) hst hb (isWeight_pushW hν _) ?_ hb1
    ha ha1 R
  intro e he
  obtain ⟨ω, -, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have : cand ω x = e := by
    by_contra hne
    rw [if_neg hne] at hω
    exact hω rfl
  rw [← this]
  exact hcT ω x

end Seeded

end MonoidProduct
