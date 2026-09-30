import MonoidProduct.Ordered.RankDoubling
import QuantumQueryComplexity.TreeSearch.Optimal

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# Seeded sampling and thinning on an arbitrary tree (`lem:beta-tree-sampling`)

`monoid.tex`, `lem:beta-tree-sampling`, for an **arbitrary** finite rooted tree,
given as an ancestor structure `T : AncTree V` (`QuantumQueryComplexity/TreeSearch.lean`).
`RankDoubling.lean` proves the same construction for the median-frontier tree `DNode J` only;
this file removes that restriction.  The probability side is `Thinning.lean`, generic in the
label set; only the cost side and the transcript/semantics bridge are redone here.

**Setting** (`thm:weighted-tree-search`, `cor:beta-tree-search-depth`).  Every vertex `v` has
a deterministic cell function `cell v : (Fin N → σ) → E` with a dual of cost `t v`.  There are
`q = |Λ| ≥ 1` *labels*; label `ℓ` sits at the vertex `lab ℓ` and carries a record
`cand ℓ y` of the virtual table `y : V → E` that is **determined by the path cells** of
`lab ℓ` (`TsLocal`).  Several labels may sit at one vertex, and records may overlap or repeat.

**The procedure** (for a fixed seed: `R` rows of `2b` orderings of `Λ`).
* A *decision* (`tsDec`) asks whether some label is live against the saved history and has
  rank `< k` in the current ordering: a transcript-tree search whose marking predicate at `v`
  reads only the path cells of `v` (`tsMark_local`), so `thm:weighted-tree-search` applies:
  cost `C_ρ` (`hasDual_tsDec_recCost`), or any weighted bound (`hasDual_tsDec`).
* A *draw* (`tsDraw`) is an emptiness test and a binary search on the rank threshold,
  `⌈log₂(q+1)⌉ + 1` decisions in all (`tsSteps`), after which the first live label of the
  ordering is known exactly (`tsDecChain_spec`); its record is retrieved from its path cells at
  cost `2∑_{w ∈ P(v)} t_w ≤ 2C_ρ` (`hasDual_tsCand`).
* A *round* makes `2b` draws against a fixed history; `R` rounds are chained, and the output
  (`tsOut`) is the compression of the final saved union.

**Results.**
* `tsOut_truthful`, `card_tsOut_le`, `supp_tsOut_subset`: for **every** seed the output is a
  truthful record of at most `b` positions (inside any window containing all records).
* `hasDual_tsOut`: for every seed the exact output function has a dual of cost
  `2·R·2b·(tsSteps·V + P)` for decision cost `V` and retrieval cost `P`.
* `tsOut_fail_le` / `tsOut_success`: with a stable order, breadth `b ≥ 1` and truthful records,
  `Pr{p(C_ℓ) ≤ p(K) for every label ℓ} ≥ 1 − q·2^{−R}` over the uniform seed.
* `tree_sampling_recCost` and **`tree_sampling`** (the paper's shape): with positive cell costs,
  a root `ρ` and depth at most `d`, putting `B = √((d+1)·∑_v t_v²)`, every fixed seed has dual
  cost at most `4·b·R·(⌈log₂(q+1)⌉ + 3)·B ≤ 40·b·R·B·log(q+2)`, i.e. `O(βRB log(q+2))`.

**Faithfulness notes.**  The paper's "labelled vertices" are modelled by a label map
`lab : Λ → V` (not necessarily injective; the paper's case is `lab` injective).  "Unions on
inconsistent virtual records" use `Record.union` (`Option.orElse`, left-biased), the same fixed
tie-breaking rule as `lem:beta-rejection-dual`.  The success event is stated for the
candidates on the actual input `x`; truthfulness of the output only needs the candidates on `x`
to be truthful, and no summary guarantee on the cells is assumed anywhere.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

section TreeSampling

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable [DecidableLE M] (letter : σ → M) {N : ℕ}
variable {V : Type} [Fintype V] [DecidableEq V] (T : AncTree V)
variable {E : Type} [Fintype E] [DecidableEq E]
variable {Λ : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
variable (lab : Λ → V) (cand : Λ → (V → E) → Record N σ)
variable (cell : V → (Fin N → σ) → E)

/-! ## Locality and the candidate table -/

/-- **Records determined by path cells**: the record of label `ℓ` reads the virtual table
only on the root path of its vertex `lab ℓ`. -/
def TsLocal : Prop :=
  ∀ ℓ (y y' : V → E), (∀ i ≤ T.depth (lab ℓ), y (T.ancAt (lab ℓ) i) = y' (T.ancAt (lab ℓ) i)) →
    cand ℓ y = cand ℓ y'

/-- The candidate record of each label on the input `x`. -/
def tsCand (x : Fin N → σ) (ℓ : Λ) : Record N σ := cand ℓ (fun w => cell w x)

/-! ## Decisions -/

/-- The marking of a decision at vertex `v`: some label at `v` is live with rank `< k`. -/
def tsMark (completed : List (Record N σ)) (e : Ord Λ) (k : ℕ) (v : V) (y : V → E) : Prop :=
  ∃ ℓ, lab ℓ = v ∧ liveTest letter completed (cand ℓ y) = true ∧ (e ℓ : ℕ) < k

variable {T lab cand} in
lemma tsMark_local (hloc : TsLocal T lab cand) (completed : List (Record N σ)) (e : Ord Λ)
    (k : ℕ) (v : V) (y y' : V → E) (h : ∀ i ≤ T.depth v, y (T.ancAt v i) = y' (T.ancAt v i)) :
    tsMark letter lab cand completed e k v y ↔ tsMark letter lab cand completed e k v y' := by
  constructor
  · rintro ⟨ℓ, rfl, hl, hk⟩
    exact ⟨ℓ, rfl, by rwa [← hloc ℓ y y' h], hk⟩
  · rintro ⟨ℓ, rfl, hl, hk⟩
    exact ⟨ℓ, rfl, by rwa [hloc ℓ y y' h], hk⟩

/-- **The decision**: is some label live with rank below `k`? -/
noncomputable def tsDec (completed : List (Record N σ)) (e : Ord Λ) (k : ℕ)
    (x : Fin N → σ) : Bool :=
  AncTree.treeSearch (tsMark letter lab cand completed e k) (fun w => cell w x)

open Classical in
lemma tsDec_eq (completed : List (Record N σ)) (e : Ord Λ) (k : ℕ) (x : Fin N → σ) :
    tsDec letter lab cand cell completed e k x
      = decide (∃ ℓ, liveTest letter completed (tsCand cand cell x ℓ) = true
          ∧ (e ℓ : ℕ) < k) := by
  unfold tsDec AncTree.treeSearch tsMark tsCand
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨_, ℓ, _, hl, hk⟩
    exact ⟨ℓ, hl, hk⟩
  · rintro ⟨ℓ, hl, hk⟩
    exact ⟨lab ℓ, ℓ, rfl, hl, hk⟩

variable {T lab cand cell}

/-- **The decision dual from weights** (`hasDual_treeSearch_comp`): positive tables pay the
weighted path sum, negative tables the weighted total. -/
theorem hasDual_tsDec (hloc : TsLocal T lab cand) (D : ℕ) (hD : ∀ v, T.depth v ≤ D)
    {β : V → ℝ} (hβ : ∀ w, β w ≠ 0) {t : V → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell v) (t v)) (Vc : ℝ)
    (hpath : ∀ v, ∑ w ∈ T.path v, t w / (β w) ^ 2 ≤ Vc) (hall : ∑ w, t w * (β w) ^ 2 ≤ Vc)
    (completed : List (Record N σ)) (e : Ord Λ) (k : ℕ) :
    HasDual (tsDec letter lab cand cell completed e k) Vc :=
  AncTree.hasDual_treeSearch_comp T D (tsMark letter lab cand completed e k) hβ hD
    (fun v y y' h => tsMark_local letter hloc completed e k v y y' h) cell ht hcell Vc hpath hall

/-- **The decision dual at the recursive cost** `C_ρ` (`thm:weighted-tree-search`). -/
theorem hasDual_tsDec_recCost (hloc : TsLocal T lab cand) {t : V → ℝ} (ht : ∀ v, 0 < t v)
    {ρ : V} (hρ : T.IsRoot ρ) (hcell : ∀ v, HasDual (cell v) (t v))
    (completed : List (Record N σ)) (e : Ord Λ) (k : ℕ) :
    HasDual (tsDec letter lab cand cell completed e k) (T.recCost t ρ) :=
  (T.hasWeightedDual_treeSearch_recCost ht hρ (tsMark letter lab cand completed e k)
    (fun v y y' h => tsMark_local letter hloc completed e k v y y' h)).composeShared
    (fun v => (ht v).le) hcell

/-! ## Draws: binary search on the rank threshold -/

variable (Λ) in
/-- The number of decisions of a draw: an emptiness test and `⌈log₂(q+1)⌉` halvings. -/
def tsSteps : ℕ := Nat.clog 2 (Fintype.card Λ + 1) + 1

variable (lab cand cell)

/-- The decision step of a draw: threshold from the transcript so far. -/
noncomputable def tsDecStep (completed : List (Record N σ)) (e : Ord Λ) :
    ∀ i : ℕ, Trans Bool i → (Fin N → σ) → Bool :=
  fun _ prev x => tsDec letter lab cand cell completed e (thrD (Fintype.card Λ) prev) x

/-- The decision transcript of a draw. -/
noncomputable def tsDecChain (completed : List (Record N σ)) (e : Ord Λ) (x : Fin N → σ) :
    Trans Bool (tsSteps Λ) :=
  chain (tsDecStep letter lab cand cell completed e) (tsSteps Λ) x

/-- The live predicate on thresholds, for a fixed input. -/
def tsP (completed : List (Record N σ)) (e : Ord Λ) (x : Fin N → σ) (k : ℕ) : Prop :=
  ∃ ℓ, liveTest letter completed (tsCand cand cell x ℓ) = true ∧ (e ℓ : ℕ) < k

lemma tsDecChain_eq_bsChain (completed : List (Record N σ)) (e : Ord Λ) (x : Fin N → σ) :
    ∀ i, chain (tsDecStep letter lab cand cell completed e) i x
      = bsChain (Fintype.card Λ) (tsP letter cand cell completed e x) i
  | 0 => rfl
  | i + 1 => by
    rw [chain_succ, tsDecChain_eq_bsChain completed e x i]
    show (_, tsDec letter lab cand cell completed e _ x) = (_, _)
    congr 1
    rw [tsDec_eq]
    exact (@decide_eq_decide _ _ _ _).2 Iff.rfl

lemma tsP_mono (completed : List (Record N σ)) (e : Ord Λ) (x : Fin N → σ) :
    ∀ k k', k ≤ k' → tsP letter cand cell completed e x k →
      tsP letter cand cell completed e x k' := by
  rintro k k' hk ⟨ℓ, hl, hlt⟩
  exact ⟨ℓ, hl, lt_of_lt_of_le hlt hk⟩

lemma tsP_zero (completed : List (Record N σ)) (e : Ord Λ) (x : Fin N → σ) :
    ¬ tsP letter cand cell completed e x 0 := by
  rintro ⟨ℓ, _, hlt⟩; exact absurd hlt (Nat.not_lt_zero _)

/-- The live labels of the candidate table. -/
noncomputable def tsLive (completed : List (Record N σ)) (x : Fin N → σ) : Finset Λ :=
  thinLive letter (tsCand cand cell x) completed

lemma tsP_card_iff (completed : List (Record N σ)) (e : Ord Λ) (x : Fin N → σ) :
    tsP letter cand cell completed e x (Fintype.card Λ)
      ↔ (tsLive letter cand cell completed x).Nonempty := by
  constructor
  · rintro ⟨ℓ, hl, _⟩
    exact ⟨ℓ, by unfold tsLive thinLive; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hl⟩⟩
  · rintro ⟨ℓ, hl⟩
    unfold tsLive thinLive at hl
    rw [Finset.mem_filter] at hl
    exact ⟨ℓ, hl.2, (e ℓ).isLt⟩

variable (Λ) in
/-- Whether the draw found a live label: bit `0`. -/
def tsFound (tr : Trans Bool (tsSteps Λ)) : Bool := Trans.get tr 0 (by unfold tsSteps; omega)

/-- The label found: rank `hi − 1`. -/
noncomputable def tsLabel (e : Ord Λ) (tr : Trans Bool (tsSteps Λ)) : Λ :=
  e.symm ⟨(bsBounds (Fintype.card Λ) tr).2 - 1, by
    have := bsBounds_range (Fintype.card Λ) Fintype.card_pos tr
    omega⟩

/-- **Draw correctness**: with a live label present the draw finds the first live label of
the ordering; otherwise it reports nothing. -/
theorem tsDecChain_spec (completed : List (Record N σ)) (e : Ord Λ) (x : Fin N → σ) :
    (tsFound Λ (tsDecChain letter lab cand cell completed e x) = true
        ↔ (tsLive letter cand cell completed x).Nonempty)
    ∧ ∀ h : (tsLive letter cand cell completed x).Nonempty,
        tsLabel e (tsDecChain letter lab cand cell completed e x)
          = firstIn e (tsLive letter cand cell completed x) h := by
  unfold tsDecChain
  rw [tsDecChain_eq_bsChain]
  set q := Fintype.card Λ with hqdef
  set P := tsP letter cand cell completed e x with hPdef
  set m := Nat.clog 2 (q + 1) with hm
  have hsteps : tsSteps Λ = m + 1 := rfl
  constructor
  · unfold tsFound
    show Trans.get (bsChain q P (m + 1)) 0 (Nat.succ_pos m) = true ↔ _
    rw [bsChain_get_zero]
    constructor
    · intro h
      exact (tsP_card_iff letter cand cell completed e x).1
        (@of_decide_eq_true _ (Classical.dec _) h)
    · intro h
      exact @decide_eq_true _ (Classical.dec _) ((tsP_card_iff letter cand cell completed e x).2 h)
  · intro h
    have hq : P q := (tsP_card_iff letter cand cell completed e x).2 h
    obtain ⟨hlo, hhi, hw⟩ := bs_correct q P (tsP_mono letter cand cell completed e x)
      (tsP_zero letter cand cell completed e x) hq m
    have hrange := bsBounds_range q Fintype.card_pos (bsChain q P (m + 1))
    have hqm : q + 1 ≤ 2 ^ m := Nat.le_pow_clog (by norm_num) _
    set lo := (bsBounds q (bsChain q P (m + 1))).1 with hlo_def
    set hi := (bsBounds q (bsChain q P (m + 1))).2 with hhi_def
    have hone : hi = lo + 1 := by
      by_contra hne
      have h2 : 1 ≤ hi - lo - 1 := by omega
      have := Nat.mul_le_mul_left (2 ^ m) h2
      omega
    obtain ⟨ℓ, hℓ, hℓlt⟩ := hhi
    have hge : ∀ ℓ' ∈ tsLive letter cand cell completed x, lo ≤ e ℓ' := by
      intro ℓ' hℓ'
      by_contra hlt
      push Not at hlt
      unfold tsLive thinLive at hℓ'
      rw [Finset.mem_filter] at hℓ'
      exact hlo ⟨ℓ', hℓ'.2, hlt⟩
    have hmem : ℓ ∈ tsLive letter cand cell completed x := by
      unfold tsLive thinLive; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hℓ⟩
    have hℓeq : (e ℓ : ℕ) = hi - 1 := by have := hge ℓ hmem; omega
    unfold tsLabel
    rw [firstIn_eq_of_le e h hmem (fun ℓ' hℓ' => ?_)]
    · apply e.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext hℓeq.symm
    · rw [Fin.le_def, hℓeq]
      have := hge ℓ' hℓ'; omega

/-! ## Retrieval and the draw -/

/-- The retrieved record: the candidate of the label found, or empty. -/
noncomputable def tsRetrieve (e : Ord Λ) (tr : Trans Bool (tsSteps Λ)) (x : Fin N → σ) :
    Record N σ :=
  if tsFound Λ tr then tsCand cand cell x (tsLabel e tr) else emptyRec

variable {lab cand cell}

/-- **Retrieval from the path cells**: the record of `ℓ` is a function of the cells on the
root path of `lab ℓ`, so it has a dual of cost `2·∑_{w ∈ P(lab ℓ)} t_w`. -/
theorem hasDual_tsCand (hloc : TsLocal T lab cand) {t : V → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell v) (t v)) (ℓ : Λ) :
    HasDual (fun x => tsCand cand cell x ℓ) (2 * ∑ w ∈ T.path (lab ℓ), t w) := by
  classical
  let P := {w : V // w ∈ T.path (lab ℓ)}
  let p₀ : P := ⟨lab ℓ, T.self_mem_path (lab ℓ)⟩
  let ext : (P → E) → V → E := fun tbl w =>
    if h : w ∈ T.path (lab ℓ) then tbl ⟨w, h⟩ else tbl p₀
  have h := HasDual.combine (fun tbl : P → E => cand ℓ (ext tbl))
    (g := fun p : P => cell p.1) (c := fun p : P => t p.1) (fun p => ht p.1) (fun p => hcell p.1)
  rw [Finset.sum_coe_sort (T.path (lab ℓ)) t] at h
  refine h.ofEq fun x => ?_
  refine hloc ℓ _ _ fun i hi => ?_
  have hmem : T.ancAt (lab ℓ) i ∈ T.path (lab ℓ) := T.ancAt_mem_path hi
  simp only [ext]
  rw [dif_pos hmem]

theorem hasDual_tsRetrieve (hloc : TsLocal T lab cand) {t : V → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell v) (t v)) {Pc : ℝ} (hPc : 0 ≤ Pc)
    (hret : ∀ ℓ, 2 * ∑ w ∈ T.path (lab ℓ), t w ≤ Pc) (e : Ord Λ)
    (tr : Trans Bool (tsSteps Λ)) : HasDual (tsRetrieve cand cell e tr) Pc := by
  unfold tsRetrieve
  split_ifs
  · exact (hasDual_tsCand hloc ht hcell _).mono (hret _)
  · exact (hasDual_const fun _ _ => rfl).mono hPc

/-- The state of one draw: its decision transcript and the retrieved record. -/
abbrev TsDrawState (N : ℕ) (σ Λ : Type) [Fintype Λ] : Type :=
  Trans Bool (tsSteps Λ) × Record N σ

variable (lab cand cell)

/-- **A draw**: decisions, then retrieval. -/
noncomputable def tsDraw (completed : List (Record N σ)) (e : Ord Λ) (x : Fin N → σ) :
    TsDrawState N σ Λ :=
  (tsDecChain letter lab cand cell completed e x,
    tsRetrieve cand cell e (tsDecChain letter lab cand cell completed e x) x)

variable {lab cand cell}

theorem hasDual_tsDraw (hloc : TsLocal T lab cand) {t : V → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell v) (t v)) {Vc : ℝ}
    (hdec : ∀ completed e k, HasDual (tsDec letter lab cand cell completed e k) Vc)
    {Pc : ℝ} (hPc : 0 ≤ Pc) (hret : ∀ ℓ, 2 * ∑ w ∈ T.path (lab ℓ), t w ≤ Pc)
    (completed : List (Record N σ)) (e : Ord Λ) :
    HasDual (tsDraw letter lab cand cell completed e) (tsSteps Λ * Vc + Pc) := by
  have hD : HasDual (tsDecChain letter lab cand cell completed e) (tsSteps Λ * Vc) := by
    unfold tsDecChain
    exact hasDual_chain_const (tsDecStep letter lab cand cell completed e) (c := Vc)
      (fun i prev => hdec completed e _) (tsSteps Λ)
  exact HasDual.adaptiveCall hD (fun d => hasDual_tsRetrieve hloc ht hcell hPc hret e d)

/-! ## Rounds and the whole procedure -/

variable (lab cand cell) (b : ℕ)

/-- A row of orderings extended to all naturals by the canonical ordering. -/
noncomputable def tsRowExt (row : Fin (2 * b) → Ord Λ) (i : ℕ) : Ord Λ :=
  if h : i < 2 * b then row ⟨i, h⟩ else Fintype.equivFin Λ

/-- **A round**: `2b` draws against the same history. -/
noncomputable def tsRound (completed : List (Record N σ)) (row : Fin (2 * b) → Ord Λ)
    (x : Fin N → σ) : Trans (TsDrawState N σ Λ) (2 * b) :=
  chain (fun i _ x => tsDraw letter lab cand cell completed (tsRowExt b row i) x) (2 * b) x

/-- The batch of a round: the union of its retrieved records. -/
noncomputable def tsBatch (tr : Trans (TsDrawState N σ Λ) (2 * b)) : Record N σ :=
  unionTuple fun i : Fin (2 * b) => (Trans.get tr i i.isLt).2

/-- The saved history of a transcript of rounds, newest first. -/
noncomputable def tsCache :
    ∀ {ρ : ℕ}, Trans (Trans (TsDrawState N σ Λ) (2 * b)) ρ → List (Record N σ)
  | 0, _ => []
  | _ + 1, tr => saveBatch (tsCache tr.1) (tsBatch b tr.2)

/-- Rows of orderings extended to all naturals. -/
noncomputable def tsRowsExt {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord Λ) (ρ : ℕ) :
    Fin (2 * b) → Ord Λ :=
  if h : ρ < R then rows ⟨ρ, h⟩ else fun _ => Fintype.equivFin Λ

/-- **The procedure for a fixed seed**: `R` rounds. -/
noncomputable def tsChain {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord Λ) (x : Fin N → σ) :
    Trans (Trans (TsDrawState N σ Λ) (2 * b)) R :=
  chain (fun ρ prev x => tsRound letter lab cand cell b (tsCache b prev) (tsRowsExt b rows ρ) x)
    R x

/-- **The output for a fixed seed**: the compressed final saved union. -/
noncomputable def tsOut {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord Λ) (x : Fin N → σ) :
    Record N σ :=
  Record.compress letter b (unionList (tsCache b (tsChain letter lab cand cell b rows x)))

variable {lab cand cell}

/-- **The dual of the fixed-seed output**: `2·R·2b·(tsSteps·V + P)`. -/
theorem hasDual_tsOut (hloc : TsLocal T lab cand) {t : V → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell v) (t v)) {Vc : ℝ} (hVc : 0 ≤ Vc)
    (hdec : ∀ completed e k, HasDual (tsDec letter lab cand cell completed e k) Vc)
    {Pc : ℝ} (hPc : 0 ≤ Pc) (hret : ∀ ℓ, 2 * ∑ w ∈ T.path (lab ℓ), t w ≤ Pc) {R : ℕ}
    (rows : Fin R → Fin (2 * b) → Ord Λ) :
    HasDual (tsOut letter lab cand cell b rows)
      (2 * (R * ((2 * b : ℕ) * (tsSteps Λ * Vc + Pc)))) := by
  have hround : ∀ completed row,
      HasDual (tsRound letter lab cand cell b completed row)
        ((2 * b : ℕ) * (tsSteps Λ * Vc + Pc)) := fun completed row =>
    hasDual_chain_const _
      (fun i _ => hasDual_tsDraw letter hloc ht hcell hdec hPc hret completed _) (2 * b)
  have hchain : HasDual (tsChain letter lab cand cell b rows)
      (R * ((2 * b : ℕ) * (tsSteps Λ * Vc + Pc))) := by
    unfold tsChain
    exact hasDual_chain_const _ (fun ρ prev => hround _ _) R
  exact HasDual.postcomp_of_determined (by positivity) hchain
    (fun x y h => by unfold tsOut; rw [h])

/-! ## The transcript computes the semantic thinning run -/

variable (lab cand cell)

/-- **A round equals the semantic round** of `Thinning.lean`. -/
theorem tsBatch_tsRound (completed : List (Record N σ)) (row : Fin (2 * b) → Ord Λ)
    (x : Fin N → σ) :
    saveBatch completed (tsBatch b (tsRound letter lab cand cell b completed row x))
      = thinRound letter (tsCand cand cell x) b completed row := by
  unfold thinRound tsBatch tsRound
  have hget : ∀ i : Fin (2 * b), (Trans.get
      (chain (fun i _ x => tsDraw letter lab cand cell completed (tsRowExt b row i) x) (2 * b) x)
        i i.isLt).2
        = tsRetrieve cand cell (row i)
            (tsDecChain letter lab cand cell completed (row i) x) x := by
    intro i
    rw [chain_get]
    unfold tsDraw tsRowExt
    simp only [dif_pos i.isLt]
  simp only [hget]
  split_ifs with h
  · congr 1
    unfold unionTuple
    congr 1
    funext i
    unfold tsRetrieve
    obtain ⟨hf, hl⟩ := tsDecChain_spec letter lab cand cell completed (row i) x
    rw [if_pos (hf.2 h), hl h]
    rfl
  · have hnf : ∀ i : Fin (2 * b),
        tsFound Λ (tsDecChain letter lab cand cell completed (row i) x) = false := by
      intro i
      obtain ⟨hf, _⟩ := tsDecChain_spec letter lab cand cell completed (row i) x
      rw [Bool.eq_false_iff]; intro hc; exact h (hf.1 hc)
    have : (fun i : Fin (2 * b) =>
        tsRetrieve cand cell (row i) (tsDecChain letter lab cand cell completed (row i) x) x)
        = fun _ => emptyRec := by
      funext i; unfold tsRetrieve; rw [hnf i]; rfl
    rw [this, unionTuple_emptyRec]

lemma tsCache_pair {ρ : ℕ} (tr : Trans (Trans (TsDrawState N σ Λ) (2 * b)) ρ)
    (r : Trans (TsDrawState N σ Λ) (2 * b)) :
    tsCache b (ρ := ρ + 1) (tr, r) = saveBatch (tsCache b tr) (tsBatch b r) := rfl

/-- **The saved history of the procedure is the semantic thinning run.** -/
theorem tsCache_tsChain {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord Λ) (x : Fin N → σ) :
    ∀ ρ (hρ : ρ ≤ R),
      tsCache b (chain (fun ρ prev x =>
          tsRound letter lab cand cell b (tsCache b prev) (tsRowsExt b rows ρ) x) ρ x)
        = thinRun letter (tsCand cand cell x) b ρ [] (fun i : Fin ρ => rows ⟨i, by omega⟩)
  | 0, _ => rfl
  | ρ + 1, hρ => by
    rw [chain_succ]
    refine (tsCache_pair b _ _).trans ?_
    rw [tsCache_tsChain rows x ρ (by omega), thinRun_snoc]
    have hinit : Fin.init (fun i : Fin (ρ + 1) => rows ⟨i, by omega⟩)
        = fun i : Fin ρ => rows ⟨i, by omega⟩ := by
      funext i; simp [Fin.init]
    rw [hinit, ← tsBatch_tsRound]
    have hrow : tsRowsExt b rows ρ
        = rows ⟨((Fin.last ρ : Fin (ρ + 1)) : ℕ), by simp; omega⟩ := by
      unfold tsRowsExt
      rw [dif_pos (by omega)]
      exact congrArg rows (Fin.ext (by simp))
    rw [hrow]

lemma tsCache_eq_thinRun {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord Λ) (x : Fin N → σ) :
    tsCache b (tsChain letter lab cand cell b rows x)
      = thinRun letter (tsCand cand cell x) b R [] rows := by
  have h := tsCache_tsChain letter lab cand cell b rows x R le_rfl
  have hrows : (fun i : Fin R => rows ⟨i, by omega⟩) = rows := funext fun i => rfl
  rw [hrows] at h
  exact h

/-! ## Every seed: truthful, at most `b` positions -/

variable (x : Fin N → σ)

/-- **Every seed gives a truthful record** (no summary guarantee on the cells needed). -/
theorem tsOut_truthful (hcand : ∀ ℓ, (tsCand cand cell x ℓ).Truthful x) {R : ℕ}
    (rows : Fin R → Fin (2 * b) → Ord Λ) : (tsOut letter lab cand cell b rows x).Truthful x := by
  unfold tsOut
  refine Record.truthful_compress letter (truthful_unionList x fun A hA => ?_) b
  rw [tsCache_eq_thinRun] at hA
  exact thinRun_truthful letter (tsCand cand cell x) b x hcand R [] (by simp) _ A hA

/-- **Every seed gives at most `b` positions.** -/
theorem card_tsOut_le {b : ℕ} (hb : IsBreadthBound letter b) {R : ℕ}
    (rows : Fin R → Fin (2 * b) → Ord Λ) : (tsOut letter lab cand cell b rows x).supp.card ≤ b :=
  (Record.compress_spec letter hb _).2.1

/-- **Every seed stays inside any window containing all candidate records.** -/
theorem supp_tsOut_subset {b : ℕ} (hb : IsBreadthBound letter b) (I : Finset (Fin N))
    (hI : ∀ ℓ, (tsCand cand cell x ℓ).supp ⊆ I) {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord Λ) :
    (tsOut letter lab cand cell b rows x).supp ⊆ I := by
  unfold tsOut
  refine (Record.compress_spec letter hb _).1.trans (supp_unionList_subset _ _ fun A hA => ?_)
  rw [tsCache_eq_thinRun] at hA
  exact supp_thinRun_subset letter b (tsCand cand cell x) I hI R [] (by simp) _ A hA

/-! ## Success probability -/

open Classical in
/-- **Failure probability**: over the uniform seed, some label's record escapes domination
by the output with probability at most `q·2^{−R}`. -/
theorem tsOut_fail_le (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    (hb1 : 1 ≤ b) (hcand : ∀ ℓ, (tsCand cand cell x ℓ).Truthful x) (R : ℕ) :
    ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows
        * (if ∀ ℓ, (tsCand cand cell x ℓ).prod letter
              ≤ (tsOut letter lab cand cell b rows x).prod letter then 0 else 1)
      ≤ (Fintype.card Λ : ℝ) * (1 / 2) ^ R := by
  refine le_trans (Finset.sum_le_sum fun rows _ => mul_le_mul_of_nonneg_left ?_
    (tupleW_nonneg (isWeight_tupleW (isWeight_unifW _) _) rows))
    (thinRun_fail_le letter (tsCand cand cell x) b x hcand hst hb hb1 R (completed := [])
      (by simp))
  have htr : ∀ A ∈ thinRun letter (tsCand cand cell x) b R [] rows, A.Truthful x :=
    thinRun_truthful letter (tsCand cand cell x) b x hcand R [] (by simp) rows
  split_ifs with hdom hlive hlive
  · norm_num
  · norm_num
  · norm_num
  · exfalso
    apply hdom
    intro ℓ
    have := prod_le_of_thinLive_empty letter (tsCand cand cell x) b x hcand hst hb hb1 htr hlive ℓ
    unfold tsOut
    rw [tsCache_eq_thinRun]
    exact this

open Classical in
/-- **Success probability** `≥ 1 − q·2^{−R}` (`lem:beta-tree-sampling`, first display). -/
theorem tsOut_success (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b)
    (hb1 : 1 ≤ b) (hcand : ∀ ℓ, (tsCand cand cell x ℓ).Truthful x) (R : ℕ) :
    1 - (Fintype.card Λ : ℝ) * (1 / 2) ^ R
      ≤ ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows
        * (if ∀ ℓ, (tsCand cand cell x ℓ).prod letter
              ≤ (tsOut letter lab cand cell b rows x).prod letter then 1 else 0) := by
  have hfail := tsOut_fail_le letter lab cand cell x hst hb hb1 hcand R
  have hsum : ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows = 1 :=
    (isWeight_tupleW (isWeight_tupleW (isWeight_unifW _) _) _).sum_one
  have hsplit : ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows
        * (if ∀ ℓ, (tsCand cand cell x ℓ).prod letter
              ≤ (tsOut letter lab cand cell b rows x).prod letter then 1 else 0)
      + ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows
        * (if ∀ ℓ, (tsCand cand cell x ℓ).prod letter
              ≤ (tsOut letter lab cand cell b rows x).prod letter then 0 else 1) = 1 := by
    rw [← Finset.sum_add_distrib]
    refine (Finset.sum_congr rfl fun rows _ => ?_).trans hsum
    split_ifs <;> ring
  linarith

/-! ## The paper's cost form -/

lemma ts_clog_two_le_four_log {m : ℕ} (hm : 2 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ 4 * Real.log m := by
  have hk1 : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num) (by omega)
  have hlt : 2 ^ (Nat.clog 2 m - 1) < m := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := m) (by omega)
    rwa [Nat.pred_eq_sub_one] at this
  have hlt' : (2 : ℝ) ^ (Nat.clog 2 m - 1) < m := by exact_mod_cast hlt
  have hlog : ((Nat.clog 2 m : ℝ) - 1) * Real.log 2 < Real.log m := by
    have := Real.log_lt_log (by positivity) hlt'
    rw [Real.log_pow] at this
    have hcast : ((Nat.clog 2 m - 1 : ℕ) : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
      rw [Nat.cast_sub hk1]; simp
    rwa [hcast] at this
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm'
  have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hk' : (1 : ℝ) ≤ Nat.clog 2 m := by exact_mod_cast hk1
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (Nat.clog 2 m : ℝ) - 1)
    (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 2)]

/-- `⌈log₂(q+1)⌉ + 3 ≤ 10·log(q+2)` for `q ≥ 1`. -/
lemma ts_steps_le_log (q : ℕ) (hq : 1 ≤ q) :
    (Nat.clog 2 (q + 1) : ℝ) + 3 ≤ 10 * Real.log ((q : ℝ) + 2) := by
  have h1 := ts_clog_two_le_four_log (m := q + 1) (by omega)
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h2 : Real.log (((q + 1 : ℕ) : ℝ)) ≤ Real.log ((q : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have h3 : (1 : ℝ) / 2 ≤ Real.log ((q : ℝ) + 2) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have h22 : Real.log 2 ≤ Real.log ((q : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
    norm_num at this
    linarith
  linarith

variable {lab cand cell}

/-- **`lem:beta-tree-sampling` at the recursive cost** (`thm:weighted-tree-search`): with
positive cell costs and a root `ρ`, every fixed seed has a dual of cost
`4·b·R·(⌈log₂(q+1)⌉ + 3)·C_ρ`. -/
theorem hasDual_tsOut_recCost (hloc : TsLocal T lab cand) {t : V → ℝ} (ht : ∀ v, 0 < t v)
    {ρ : V} (hρ : T.IsRoot ρ) (hcell : ∀ v, HasDual (cell v) (t v)) (b R : ℕ)
    (rows : Fin R → Fin (2 * b) → Ord Λ) :
    HasDual (tsOut letter lab cand cell b rows)
      (4 * b * R * ((Nat.clog 2 (Fintype.card Λ + 1) : ℝ) + 3) * T.recCost t ρ) := by
  have hC := (T.recCost_pos ht ρ).le
  have h := hasDual_tsOut letter b hloc (fun v => (ht v).le) hcell hC
    (hasDual_tsDec_recCost letter hloc ht hρ hcell) (Pc := 2 * T.recCost t ρ) (by positivity)
    (fun ℓ => by have := T.sum_path_le_recCost ht hρ (lab ℓ); linarith) rows
  refine h.mono (le_of_eq ?_)
  unfold tsSteps
  push_cast
  ring

/-- **`lem:beta-tree-sampling`**, in the setting of
`cor:beta-tree-search-depth`: a rooted tree of depth at most `d`, cell functions with duals
of positive costs `t_v`, `B = √((d+1)·∑_v t_v²)`, and `q = |Λ| ≥ 1` labels whose records are
determined by their path cells.  For every `R` and every fixed seed, the output is a
truthful record of at most `b` positions whenever the records are truthful, and the exact
output function has dual cost `4·b·R·(⌈log₂(q+1)⌉+3)·B ≤ 40·b·R·B·log(q+2)`; with a stable
order and breadth `b ≥ 1`, `Pr{p(C_ℓ) ≤ p(K) for every label ℓ} ≥ 1 − q·2^{−R}`. -/
theorem tree_sampling (hloc : TsLocal T lab cand) {t : V → ℝ} (ht : ∀ v, 0 < t v)
    {ρ : V} (hρ : T.IsRoot ρ) {d : ℕ} (hd : ∀ v, T.depth v ≤ d)
    (hcell : ∀ v, HasDual (cell v) (t v)) (hst : IsStableOrder M) {b : ℕ}
    (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) (R : ℕ) :
    (∀ rows : Fin R → Fin (2 * b) → Ord Λ,
      HasDual (tsOut letter lab cand cell b rows)
        (4 * b * R * ((Nat.clog 2 (Fintype.card Λ + 1) : ℝ) + 3)
          * Real.sqrt (((d : ℝ) + 1) * ∑ v, t v ^ 2))
      ∧ HasDual (tsOut letter lab cand cell b rows)
        (40 * b * R * Real.sqrt (((d : ℝ) + 1) * ∑ v, t v ^ 2)
          * Real.log ((Fintype.card Λ : ℝ) + 2)))
    ∧ ∀ x : Fin N → σ, (∀ ℓ, (tsCand cand cell x ℓ).Truthful x) →
      (∀ rows : Fin R → Fin (2 * b) → Ord Λ,
        (tsOut letter lab cand cell b rows x).Truthful x
          ∧ (tsOut letter lab cand cell b rows x).supp.card ≤ b)
      ∧ 1 - (Fintype.card Λ : ℝ) * (1 / 2) ^ R
        ≤ ∑ rows : Fin R → Fin (2 * b) → Ord Λ, tupleW (tupleW (unifW (Ord Λ))) rows
          * (if ∀ ℓ, (tsCand cand cell x ℓ).prod letter
                ≤ (tsOut letter lab cand cell b rows x).prod letter then 1 else 0) := by
  classical
  refine ⟨fun rows => ?_, fun x hcand => ⟨fun rows => ⟨tsOut_truthful letter lab cand cell b x
    hcand rows, card_tsOut_le letter lab cand cell x hb rows⟩, ?_⟩⟩
  · set B := Real.sqrt (((d : ℝ) + 1) * ∑ v, t v ^ 2) with hB
    have hCB : T.recCost t ρ ≤ B := T.recCost_le_sqrt_depth_sqSum ht hρ hd
    have hB0 : 0 ≤ B := Real.sqrt_nonneg _
    have hk : (0 : ℝ) ≤ 4 * b * R * ((Nat.clog 2 (Fintype.card Λ + 1) : ℝ) + 3) := by positivity
    have h1 := (hasDual_tsOut_recCost letter hloc ht hρ hcell b R rows).mono
      (mul_le_mul_of_nonneg_left hCB hk)
    refine ⟨h1, h1.mono ?_⟩
    have hq := ts_steps_le_log (Fintype.card Λ) Fintype.card_pos
    have hbR : (0 : ℝ) ≤ 4 * b * R * B := by positivity
    calc 4 * b * R * ((Nat.clog 2 (Fintype.card Λ + 1) : ℝ) + 3) * B
        = (4 * b * R * B) * ((Nat.clog 2 (Fintype.card Λ + 1) : ℝ) + 3) := by ring
      _ ≤ (4 * b * R * B) * (10 * Real.log ((Fintype.card Λ : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hq hbR
      _ = _ := by ring
  · exact tsOut_success letter lab cand cell x hst hb hb1 hcand R

end TreeSampling

end MonoidProduct
