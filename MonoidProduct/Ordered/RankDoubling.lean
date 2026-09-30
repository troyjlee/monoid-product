import MonoidProduct.Ordered.MedianFrontier
import MonoidProduct.Ordered.Thinning
import QuantumQueryComplexity.Chain

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# Seeded rank doubling (`lem:beta-rank-doubling`)

Fix the dyadic interval `(J+1, Q)` of the padded word and a family `S w` of rank-`r`
summary *functions* for the non-root vertices `w` of its tree (the previous stage, with
its seeds already fixed).  The **table** has a cell at every vertex `v`: the pair of the
summaries of its two children (`cell`), a deterministic function of the input with a
dual of cost `t v`.  The candidate of a vertex is its frontier record read off the table
(`candOf`), a function of the cells on the vertex's root path only (`candOf_congr`).

One **decision** asks whether some vertex is live (its candidate passes the merger's
live test against the current cache) and has rank below a threshold `k` in the current
ordering: a transcript-tree search over the table, with the weighted dual of
`TreeSearch.lean` (`hasDual_decD`).  A **draw** finds the first live label of an
ordering by binary search on the threshold (`bsBounds`, `bs_correct`) and retrieves its
candidate from the cells on its path; a **round** makes `2b` draws; the **doubling**
makes `R` rounds and compresses the union of the batches (`dblOut`).  Every step is a
function of the input given the transcript so far, so the costs add
(`hasDual_dblChain`), and the final projection to the record costs a factor `2`
(`hasDual_dblOut`).  The transcript computes exactly the semantic thinning run of
`Thinning.lean` (`cacheOf_dblChain`), so with all child summaries correct the output is
a `2r`-summary except with probability `≤ |V|·2^{-R}` over the orderings
(`dbl_fail_le`).
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

section RankDoubling

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable [DecidableLE M] (letter : σ → M) {N : ℕ} (J Q : ℕ)

/-! ## Nodes, parents, tables -/

/-- The vertex set: all nodes of the tree of depth `J+1`. -/
abbrev DNode (J : ℕ) : Type := TNode (J + 1)

/-- The number of labels. -/
abbrev qD (J : ℕ) : ℕ := Fintype.card (DNode J)

/-- A table cell: the two child summaries. -/
abbrev Cell (N : ℕ) (σ : Type) : Type := Record N σ × Record N σ

/-- The parent of a non-root node. -/
def parentNode {J' : ℕ} (w : TNode J') (hw : 1 ≤ (w.1 : ℕ)) : TNode J' :=
  ⟨⟨w.1 - 1, by omega⟩, ⟨w.2 / 2, by
    rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ, Nat.sub_add_cancel hw]
    exact w.2.isLt⟩⟩

lemma parentNode_fst {J' : ℕ} (w : TNode J') (hw : 1 ≤ (w.1 : ℕ)) :
    ((parentNode w hw).1 : ℕ) = w.1 - 1 := rfl

lemma parentNode_snd {J' : ℕ} (w : TNode J') (hw : 1 ≤ (w.1 : ℕ)) :
    ((parentNode w hw).2 : ℕ) = w.2 / 2 := rfl

lemma parentNode_lt {J' : ℕ} (w : TNode J') (hw : 1 ≤ (w.1 : ℕ)) :
    ((parentNode w hw).1 : ℕ) < J' := by
  rw [parentNode_fst]; have := w.1.isLt; omega

lemma parentNode_child {J' : ℕ} (v : TNode J') (hv : (v.1 : ℕ) < J') (c : Fin 2) :
    parentNode (tnodeChild J' v hv c) (by unfold tnodeChild; simp) = v := by
  refine tnode_ext ?_ ?_
  · rw [parentNode_fst]; unfold tnodeChild; simp
  · rw [parentNode_snd]; unfold tnodeChild; simp only
    have := c.isLt; omega

lemma child_parentNode {J' : ℕ} (w : TNode J') (hw : 1 ≤ (w.1 : ℕ)) :
    tnodeChild J' (parentNode w hw) (parentNode_lt w hw)
      ⟨(w.2 : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩ = w := by
  refine tnode_ext ?_ ?_
  · unfold tnodeChild; simp only; rw [parentNode_fst]; omega
  · unfold tnodeChild; simp only; rw [parentNode_snd]; exact Nat.div_add_mod _ 2

lemma tnodeChild_snd_mod {J' : ℕ} (v : TNode J') (hv : (v.1 : ℕ) < J') (c : Fin 2) :
    ((tnodeChild J' v hv c).2 : ℕ) % 2 = c := by
  unfold tnodeChild; simp only
  have := c.isLt; omega

/-- The record a table assigns to a node: the component of its parent's cell. -/
def Sof (y : DNode J → Cell N σ) (w : DNode J) : Record N σ :=
  if hw : 1 ≤ (w.1 : ℕ) then
    (if (w.2 : ℕ) % 2 = 0 then (y (parentNode w hw)).1 else (y (parentNode w hw)).2)
  else emptyRec

lemma Sof_child (y : DNode J → Cell N σ) (v : DNode J) (hv : (v.1 : ℕ) < J + 1) (c : Fin 2) :
    Sof J y (tnodeChild (J + 1) v hv c) = (if (c : ℕ) = 0 then (y v).1 else (y v).2) := by
  unfold Sof
  rw [dif_pos (by unfold tnodeChild; simp)]
  have hpar : parentNode (tnodeChild (J + 1) v hv c) (by unfold tnodeChild; simp) = v :=
    parentNode_child v hv c
  rw [tnodeChild_snd_mod]
  simp only [hpar]

/-- The candidate of a vertex: its frontier record (empty at leaves). -/
noncomputable def candOf (y : DNode J → Cell N σ) (v : DNode J) : Record N σ :=
  if hv : (v.1 : ℕ) < J + 1 then frontierRec (Sof J y) v hv else emptyRec

/-! ## Locality of the candidates -/

/-- The frontier record reads the assignment only at non-root nodes. -/
lemma frontierFrom_congr {J' : ℕ} {S₁ S₂ : TNode J' → Record N σ}
    (h : ∀ w, 1 ≤ (w.1 : ℕ) → S₁ w = S₂ w) (v : TNode J') (hv : (v.1 : ℕ) < J') :
    ∀ i : ℕ, i ≤ (v.1 : ℕ) → frontierFrom S₁ v hv i = frontierFrom S₂ v hv i := by
  refine downward_induction (fun i => frontierFrom S₁ v hv i = frontierFrom S₂ v hv i) ?_ ?_
  · rw [frontierFrom_of_not_lt S₁ v hv (lt_irrefl _), frontierFrom_of_not_lt S₂ v hv (lt_irrefl _),
      h _ (by unfold tnodeChild; simp), h _ (by unfold tnodeChild; simp)]
  · intro i hi ih
    rw [frontierFrom_of_lt S₁ v hv hi, frontierFrom_of_lt S₂ v hv hi, ih,
      h _ (by unfold tnodeSib tnodeChild; simp)]

/-- The sibling at depth `i+1` is a child of the ancestor at depth `i`. -/
lemma parentNode_tnodeSib {J' : ℕ} (v : TNode J') {i : ℕ} (hi : i < v.1) :
    parentNode (tnodeSib J' v i hi) (by unfold tnodeSib tnodeChild; simp) = tnodeAncAt J' v i := by
  unfold tnodeSib
  exact parentNode_child _ _ _

/-- **Locality**: the candidate of `v` depends only on the cells on its root path. -/
theorem candOf_congr {y y' : DNode J → Cell N σ} (v : DNode J)
    (h : ∀ i ≤ (v.1 : ℕ), y (tnodeAncAt (J + 1) v i) = y' (tnodeAncAt (J + 1) v i)) :
    candOf J y v = candOf J y' v := by
  unfold candOf
  split_ifs with hv
  · unfold frontierRec
    refine downward_induction (n := (v.1 : ℕ))
      (fun i => frontierFrom (Sof J y) v hv i = frontierFrom (Sof J y') v hv i) ?_ ?_ 0 (Nat.zero_le _)
    · rw [frontierFrom_of_not_lt _ v hv (lt_irrefl _), frontierFrom_of_not_lt _ v hv (lt_irrefl _),
        Sof_child, Sof_child, Sof_child, Sof_child]
      have hv' := h v.1 le_rfl
      rw [tnodeAncAt_self] at hv'
      rw [hv']
    · intro i hi ih
      rw [frontierFrom_of_lt _ v hv hi, frontierFrom_of_lt _ v hv hi, ih]
      congr 1
      unfold Sof
      rw [dif_pos (by unfold tnodeSib tnodeChild; simp), dif_pos (by unfold tnodeSib tnodeChild; simp)]
      rw [parentNode_tnodeSib v hi, h i hi.le]
  · rfl

/-! ## Cells -/

variable (S : DNode J → (Fin N → σ) → Record N σ)

/-- The cell of a vertex: the summaries of its two children (empty at leaves). -/
noncomputable def cell (v : DNode J) (x : Fin N → σ) : Cell N σ :=
  if hv : (v.1 : ℕ) < J + 1 then
    (S (tnodeChild (J + 1) v hv 0) x, S (tnodeChild (J + 1) v hv 1) x)
  else (emptyRec, emptyRec)

/-- The table of cells reproduces the child summaries at every non-root node. -/
lemma Sof_cell (x : Fin N → σ) (w : DNode J) (hw : 1 ≤ (w.1 : ℕ)) :
    Sof J (fun u => cell J S u x) w = S w x := by
  unfold Sof
  rw [dif_pos hw]
  simp only [cell, dif_pos (parentNode_lt w hw)]
  have hc := child_parentNode w hw
  split_ifs with h0
  · have : (⟨(w.2 : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 0 := Fin.ext (by simp [h0])
    rw [this] at hc
    rw [hc]
  · have : (⟨(w.2 : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 1 := Fin.ext (by
      have := Nat.mod_lt (w.2 : ℕ) (by norm_num : 0 < 2)
      simp only [Fin.val_one]
      omega)
    rw [this] at hc
    rw [hc]

/-- The candidate of an internal vertex is its frontier record from the child summaries. -/
lemma candOf_cell (x : Fin N → σ) (v : DNode J) (hv : (v.1 : ℕ) < J + 1) :
    candOf J (fun u => cell J S u x) v = frontierRec (fun w => S w x) v hv := by
  unfold candOf
  rw [dif_pos hv]
  unfold frontierRec
  exact frontierFrom_congr (fun w hw => Sof_cell J S x w hw) v hv 0 (Nat.zero_le _)

lemma candOf_leaf (y : DNode J → Cell N σ) (v : DNode J) (hv : ¬ (v.1 : ℕ) < J + 1) :
    candOf J y v = emptyRec := by
  unfold candOf; rw [dif_neg hv]

/-- The cell cost: `4·A(depth+1)` at internal vertices, `0` at leaves. -/
noncomputable def tcost (Acost : ℕ → ℝ) (v : DNode J) : ℝ :=
  if (v.1 : ℕ) < J + 1 then 4 * Acost (v.1 + 1) else 0

lemma tcost_nonneg {Acost : ℕ → ℝ} (hA : ∀ d, 0 ≤ Acost d) (v : DNode J) : 0 ≤ tcost J Acost v := by
  unfold tcost; split_ifs
  · have := hA (v.1 + 1); positivity
  · exact le_rfl

/-- **The cell dual**: `combine₂` of the two child duals. -/
theorem hasDual_cell {Acost : ℕ → ℝ} (hA : ∀ d, 0 ≤ Acost d)
    (hS : ∀ w : DNode J, 1 ≤ (w.1 : ℕ) → HasDual (S w) (Acost w.1)) (v : DNode J) :
    HasDual (cell J S v) (tcost J Acost v) := by
  unfold cell tcost
  split_ifs with hv
  · have h := HasDual.combine₂ (fun a b : Record N σ => (a, b)) (hA (v.1 + 1)) (hA (v.1 + 1))
      (hS (tnodeChild (J + 1) v hv 0) (by unfold tnodeChild; simp))
      (hS (tnodeChild (J + 1) v hv 1) (by unfold tnodeChild; simp))
    refine h.ofEq (fun x => rfl) |>.mono (le_of_eq ?_)
    ring
  · exact hasDual_const fun _ _ => rfl

/-! ## Decisions -/

/-- The marking of a decision: a live candidate of rank below `k`. -/
def markD (completed : List (Record N σ)) (e : Ord (DNode J)) (k : ℕ) (v : DNode J)
    (y : DNode J → Cell N σ) : Prop :=
  liveTest letter completed (candOf J y v) = true ∧ (e v : ℕ) < k

lemma markD_local (completed : List (Record N σ)) (e : Ord (DNode J)) (k : ℕ) (v : DNode J)
    (y y' : DNode J → Cell N σ)
    (h : ∀ i ≤ (tnodeTree (J + 1)).depth v,
      y ((tnodeTree (J + 1)).ancAt v i) = y' ((tnodeTree (J + 1)).ancAt v i)) :
    markD letter J completed e k v y ↔ markD letter J completed e k v y' := by
  unfold markD
  rw [candOf_congr J v h]

/-- **The decision**: is some vertex live with rank below `k`? -/
noncomputable def decD (completed : List (Record N σ)) (e : Ord (DNode J)) (k : ℕ)
    (x : Fin N → σ) : Bool :=
  AncTree.treeSearch (markD letter J completed e k) (fun w => cell J S w x)

open Classical in
lemma decD_eq (completed : List (Record N σ)) (e : Ord (DNode J)) (k : ℕ) (x : Fin N → σ) :
    decD letter J S completed e k x
      = decide (∃ v, liveTest letter completed (candOf J (fun u => cell J S u x) v) = true
          ∧ (e v : ℕ) < k) := by
  unfold decD AncTree.treeSearch markD
  congr

/-- **The decision dual.** -/
theorem hasDual_decD {β : DNode J → ℝ} (hβ : ∀ w, β w ≠ 0) {t : DNode J → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell J S v) (t v)) (Vc : ℝ)
    (hpath : ∀ v, ∑ w ∈ (tnodeTree (J + 1)).path v, t w / (β w) ^ 2 ≤ Vc)
    (hall : ∑ w, t w * (β w) ^ 2 ≤ Vc) (completed : List (Record N σ)) (e : Ord (DNode J))
    (k : ℕ) :
    HasDual (decD letter J S completed e k) Vc :=
  AncTree.hasDual_treeSearch_comp (tnodeTree (J + 1)) (J + 1) (markD letter J completed e k) hβ
    (fun v => Nat.lt_succ_iff.1 v.1.isLt) (fun v y y' h => markD_local letter J completed e k v y y' h)
    (cell J S) ht hcell Vc hpath hall

/-! ## Binary search on the threshold -/

/-- Search bounds from a transcript of decision bits; bit `0` is the emptiness test, later bits
halve the interval `(lo, hi]`. -/
def bsBounds (q : ℕ) : ∀ {i : ℕ}, Trans Bool i → ℕ × ℕ
  | 0, _ => (0, q)
  | 1, _ => (0, q)
  | i + 2, t =>
    let p := bsBounds q (i := i + 1) t.1
    if p.2 ≤ p.1 + 1 then p else if t.2 then (p.1, (p.1 + p.2) / 2) else ((p.1 + p.2) / 2, p.2)

/-- The threshold queried at step `i`, given the transcript so far. -/
def thrD (q : ℕ) : ∀ {i : ℕ}, Trans Bool i → ℕ
  | 0, _ => q
  | _ + 1, t => ((bsBounds q t).1 + (bsBounds q t).2) / 2

/-- The pure binary-search transcript for a predicate `P`. -/
noncomputable def bsChain (q : ℕ) (P : ℕ → Prop) : ∀ i : ℕ, Trans Bool i
  | 0 => ()
  | i + 1 => (bsChain q P i, @decide (P (thrD q (bsChain q P i))) (Classical.dec _))

lemma bsBounds_succ_succ (q : ℕ) {i : ℕ} (t : Trans Bool (i + 2)) :
    bsBounds q t = (let p := bsBounds q (i := i + 1) t.1
      if p.2 ≤ p.1 + 1 then p else if t.2 then (p.1, (p.1 + p.2) / 2) else ((p.1 + p.2) / 2, p.2)) := by
  rfl

/-- The bounds stay inside `[0, q]` with `hi ≥ 1` whenever `q ≥ 1`. -/
lemma bsBounds_range (q : ℕ) (hq : 1 ≤ q) : ∀ {i : ℕ} (t : Trans Bool i),
    (bsBounds q t).1 < (bsBounds q t).2 ∧ (bsBounds q t).2 ≤ q
  | 0, _ => ⟨hq, le_rfl⟩
  | 1, _ => ⟨hq, le_rfl⟩
  | i + 2, t => by
    obtain ⟨h1, h2⟩ := bsBounds_range q hq (i := i + 1) t.1
    rw [bsBounds_succ_succ]
    simp only
    split_ifs <;> constructor <;> omega

/-- **Binary-search correctness.**  For a monotone predicate false at `0` and true at `q`, after
`i+1` steps the bounds satisfy `¬P lo`, `P hi`, and `2^i·(hi − lo − 1) ≤ q`. -/
theorem bs_correct (q : ℕ) (P : ℕ → Prop) (hmono : ∀ k k', k ≤ k' → P k → P k') (h0 : ¬ P 0)
    (hq : P q) : ∀ i : ℕ,
      ¬ P (bsBounds q (bsChain q P (i + 1))).1 ∧ P (bsBounds q (bsChain q P (i + 1))).2
        ∧ 2 ^ i * ((bsBounds q (bsChain q P (i + 1))).2 - (bsBounds q (bsChain q P (i + 1))).1 - 1) ≤ q
  | 0 => by
    show ¬ P (bsBounds q (i := 1) _).1 ∧ P (bsBounds q (i := 1) _).2 ∧ _
    simp only [bsBounds, pow_zero, one_mul]
    exact ⟨h0, hq, by omega⟩
  | i + 1 => by
    obtain ⟨hlo, hhi, hw⟩ := bs_correct q P hmono h0 hq i
    have hbit : (bsChain q P (i + 2)).2
        = @decide (P (thrD q (bsChain q P (i + 1)))) (Classical.dec _) := rfl
    have hfst : (bsChain q P (i + 2)).1 = bsChain q P (i + 1) := rfl
    have hthr : thrD q (bsChain q P (i + 1))
        = ((bsBounds q (bsChain q P (i + 1))).1 + (bsBounds q (bsChain q P (i + 1))).2) / 2 := rfl
    rw [bsBounds_succ_succ, hfst]
    simp only
    split_ifs with hnarrow hdec
    · refine ⟨hlo, hhi, ?_⟩
      have : (bsBounds q (bsChain q P (i + 1))).2 - (bsBounds q (bsChain q P (i + 1))).1 - 1 = 0 := by
        omega
      rw [this]; simp
    · have hP : P (((bsBounds q (bsChain q P (i + 1))).1 + (bsBounds q (bsChain q P (i + 1))).2) / 2) := by
        rw [← hthr]; exact @of_decide_eq_true _ (Classical.dec _) (by rw [← hbit]; exact hdec)
      refine ⟨hlo, hP, ?_⟩
      dsimp only
      have h2 : 2 * (((bsBounds q (bsChain q P (i + 1))).1 + (bsBounds q (bsChain q P (i + 1))).2) / 2
          - (bsBounds q (bsChain q P (i + 1))).1 - 1)
          ≤ (bsBounds q (bsChain q P (i + 1))).2 - (bsBounds q (bsChain q P (i + 1))).1 - 1 := by omega
      calc 2 ^ (i + 1) * (((bsBounds q (bsChain q P (i + 1))).1 + (bsBounds q (bsChain q P (i + 1))).2) / 2
            - (bsBounds q (bsChain q P (i + 1))).1 - 1)
          = 2 ^ i * (2 * (((bsBounds q (bsChain q P (i + 1))).1 + (bsBounds q (bsChain q P (i + 1))).2) / 2
            - (bsBounds q (bsChain q P (i + 1))).1 - 1)) := by rw [pow_succ]; ring
        _ ≤ 2 ^ i * ((bsBounds q (bsChain q P (i + 1))).2 - (bsBounds q (bsChain q P (i + 1))).1 - 1) :=
            Nat.mul_le_mul_left _ h2
        _ ≤ q := hw
    · have hnP : ¬ P (((bsBounds q (bsChain q P (i + 1))).1 + (bsBounds q (bsChain q P (i + 1))).2) / 2) := by
        rw [← hthr]
        exact @of_decide_eq_false _ (Classical.dec _) (by rw [← hbit]; exact Bool.eq_false_iff.2 hdec)
      refine ⟨hnP, hhi, ?_⟩
      dsimp only
      have h2 : 2 * ((bsBounds q (bsChain q P (i + 1))).2
          - ((bsBounds q (bsChain q P (i + 1))).1 + (bsBounds q (bsChain q P (i + 1))).2) / 2 - 1)
          ≤ (bsBounds q (bsChain q P (i + 1))).2 - (bsBounds q (bsChain q P (i + 1))).1 - 1 := by omega
      calc 2 ^ (i + 1) * ((bsBounds q (bsChain q P (i + 1))).2
            - ((bsBounds q (bsChain q P (i + 1))).1 + (bsBounds q (bsChain q P (i + 1))).2) / 2 - 1)
          = 2 ^ i * (2 * ((bsBounds q (bsChain q P (i + 1))).2
            - ((bsBounds q (bsChain q P (i + 1))).1 + (bsBounds q (bsChain q P (i + 1))).2) / 2 - 1)) := by
            rw [pow_succ]; ring
        _ ≤ 2 ^ i * ((bsBounds q (bsChain q P (i + 1))).2 - (bsBounds q (bsChain q P (i + 1))).1 - 1) :=
            Nat.mul_le_mul_left _ h2
        _ ≤ q := hw

/-! ## The vertex count -/

lemma card_TNode (J' : ℕ) : Fintype.card (TNode J') + 1 = 2 ^ (J' + 1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun d => 2 ^ d) (J' + 1)]
  induction J' with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma card_DNode_lt (J : ℕ) : Fintype.card (DNode J) < 2 ^ (J + 2) := by
  have := card_TNode (J + 1)
  have h2 : (2 : ℕ) ^ (J + 1 + 1) = 2 ^ (J + 2) := rfl
  show Fintype.card (TNode (J + 1)) < 2 ^ (J + 2)
  omega

lemma qD_eq (J : ℕ) : qD J = Fintype.card (DNode J) := rfl

lemma card_DNode_pos (J : ℕ) : 1 ≤ Fintype.card (DNode J) := Fintype.card_pos

/-! ## Draws -/

/-- The decision step of a draw: threshold from the transcript so far. -/
noncomputable def decStep (completed : List (Record N σ)) (e : Ord (DNode J)) :
    ∀ i : ℕ, Trans Bool i → (Fin N → σ) → Bool :=
  fun _ prev x => decD letter J S completed e (thrD (qD J) prev) x

/-- The decision transcript of a draw: `J + 3` decisions. -/
noncomputable def decChain (completed : List (Record N σ)) (e : Ord (DNode J)) (x : Fin N → σ) :
    Trans Bool (J + 3) :=
  chain (decStep letter J S completed e) (J + 3) x

/-- The live predicate on thresholds, for a fixed input. -/
def PD (completed : List (Record N σ)) (e : Ord (DNode J)) (x : Fin N → σ) (k : ℕ) : Prop :=
  ∃ v, liveTest letter completed (candOf J (fun u => cell J S u x) v) = true ∧ (e v : ℕ) < k

lemma decChain_eq_bsChain (completed : List (Record N σ)) (e : Ord (DNode J)) (x : Fin N → σ) :
    ∀ i, chain (decStep letter J S completed e) i x = bsChain (qD J) (PD letter J S completed e x) i
  | 0 => rfl
  | i + 1 => by
    rw [chain_succ, decChain_eq_bsChain completed e x i]
    show (_, decD letter J S completed e _ x) = (_, _)
    congr 1
    rw [decD_eq]
    exact (@decide_eq_decide _ _ _ _).2 Iff.rfl

lemma PD_mono (completed : List (Record N σ)) (e : Ord (DNode J)) (x : Fin N → σ) :
    ∀ k k', k ≤ k' → PD letter J S completed e x k → PD letter J S completed e x k' := by
  rintro k k' hk ⟨v, hv, hlt⟩
  exact ⟨v, hv, lt_of_lt_of_le hlt hk⟩

lemma PD_zero (completed : List (Record N σ)) (e : Ord (DNode J)) (x : Fin N → σ) :
    ¬ PD letter J S completed e x 0 := by
  rintro ⟨v, _, hlt⟩; exact absurd hlt (Nat.not_lt_zero _)

/-- The live set of the candidate table. -/
noncomputable def liveD (completed : List (Record N σ)) (x : Fin N → σ) : Finset (DNode J) :=
  thinLive letter (fun v => candOf J (fun u => cell J S u x) v) completed

lemma PD_q_iff (completed : List (Record N σ)) (e : Ord (DNode J)) (x : Fin N → σ) :
    PD letter J S completed e x (qD J) ↔ (liveD letter J S completed x).Nonempty := by
  constructor
  · rintro ⟨v, hv, _⟩
    exact ⟨v, by unfold liveD thinLive; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hv⟩⟩
  · rintro ⟨v, hv⟩
    unfold liveD thinLive at hv
    rw [Finset.mem_filter] at hv
    exact ⟨v, hv.2, (e v).isLt⟩

lemma bsChain_get_zero (q : ℕ) (P : ℕ → Prop) :
    ∀ i, Trans.get (bsChain q P (i + 1)) 0 (Nat.succ_pos i)
      = @decide (P q) (Classical.dec _)
  | 0 => rfl
  | i + 1 => by
    show (if h : 0 < i + 1 then Trans.get (bsChain q P (i + 1)) 0 h else _) = _
    rw [dif_pos (Nat.succ_pos i)]
    exact bsChain_get_zero q P i

/-- Whether the draw found a live label: bit `0`. -/
def foundOf (t : Trans Bool (J + 3)) : Bool := Trans.get t 0 (by omega)

/-- The label found: rank `hi − 1`. -/
noncomputable def labelOf (e : Ord (DNode J)) (t : Trans Bool (J + 3)) : DNode J :=
  e.symm ⟨(bsBounds (qD J) t).2 - 1, by
    have := bsBounds_range (qD J) (card_DNode_pos J) t
    have hq := qD_eq J
    omega⟩

/-- **Draw correctness**: with a live label present the draw finds the first live label of the
ordering; otherwise it reports nothing. -/
theorem decChain_spec (completed : List (Record N σ)) (e : Ord (DNode J)) (x : Fin N → σ) :
    (foundOf J (decChain letter J S completed e x) = true
        ↔ (liveD letter J S completed x).Nonempty)
    ∧ ∀ h : (liveD letter J S completed x).Nonempty,
        labelOf J e (decChain letter J S completed e x) = firstIn e (liveD letter J S completed x) h := by
  unfold decChain
  rw [decChain_eq_bsChain]
  constructor
  · unfold foundOf
    rw [bsChain_get_zero]
    constructor
    · intro h; exact (PD_q_iff letter J S completed e x).1 (@of_decide_eq_true _ (Classical.dec _) h)
    · intro h; exact @decide_eq_true _ (Classical.dec _) ((PD_q_iff letter J S completed e x).2 h)
  · intro h
    have hq : PD letter J S completed e x (qD J) := (PD_q_iff letter J S completed e x).2 h
    obtain ⟨hlo', hhi', hw'⟩ := bs_correct (qD J) (PD letter J S completed e x)
      (PD_mono letter J S completed e x) (PD_zero letter J S completed e x) hq (J + 2)
    have hlo : ¬ PD letter J S completed e x
        (bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).1 := hlo'
    have hhi : PD letter J S completed e x
        (bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).2 := hhi'
    have hw : 2 ^ (J + 2) * ((bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).2
        - (bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).1 - 1) ≤ qD J := hw'
    clear hlo' hhi' hw'
    have hrange := bsBounds_range (qD J) (card_DNode_pos J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))
    have hcard := card_DNode_lt J
    have hqe := qD_eq J
    -- the interval has width one
    have hone : (bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).2
        = (bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).1 + 1 := by
      by_contra hne
      have h2 : 1 ≤ (bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).2
          - (bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).1 - 1 := by omega
      have := Nat.mul_le_mul_left (2 ^ (J + 2)) h2
      omega
    obtain ⟨v, hv, hvlt⟩ := hhi
    have hvge : ∀ v' ∈ liveD letter J S completed x,
        (bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).1 ≤ e v' := by
      intro v' hv'
      by_contra hlt
      push Not at hlt
      unfold liveD thinLive at hv'
      rw [Finset.mem_filter] at hv'
      exact hlo ⟨v', hv'.2, hlt⟩
    have hvmem : v ∈ liveD letter J S completed x := by
      unfold liveD thinLive; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hv⟩
    have hveq : (e v : ℕ) = (bsBounds (qD J) (bsChain (qD J) (PD letter J S completed e x) (J + 3))).2 - 1 := by
      have := hvge v hvmem; omega
    unfold labelOf
    rw [firstIn_eq_of_le e h hvmem (fun v' hv' => ?_)]
    · apply e.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext hveq.symm
    · rw [Fin.le_def, hveq]
      have := hvge v' hv'; omega

/-! ## Retrieval and the draw -/

/-- The retrieved record: the candidate of the label found, or empty. -/
noncomputable def retrieveD (e : Ord (DNode J)) (t : Trans Bool (J + 3)) (x : Fin N → σ) : Record N σ :=
  if foundOf J t then candOf J (fun w => cell J S w x) (labelOf J e t) else emptyRec

/-- The candidate of `v` is a function of the cells on its path: `combine` over the path. -/
theorem hasDual_candOf_path {t : DNode J → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell J S v) (t v)) (v : DNode J) :
    HasDual (fun x => candOf J (fun w => cell J S w x) v)
      (2 * ∑ w ∈ (tnodeTree (J + 1)).path v, t w) := by
  classical
  let P := {w : DNode J // w ∈ (tnodeTree (J + 1)).path v}
  let ext : (P → Cell N σ) → DNode J → Cell N σ := fun tbl w =>
    if h : w ∈ (tnodeTree (J + 1)).path v then tbl ⟨w, h⟩ else (emptyRec, emptyRec)
  have h := HasDual.combine (fun tbl : P → Cell N σ => candOf J (ext tbl) v)
    (g := fun p : P => cell J S p.1) (c := fun p : P => t p.1) (fun p => ht p.1)
    (fun p => hcell p.1)
  rw [Finset.sum_coe_sort ((tnodeTree (J + 1)).path v) t] at h
  refine h.ofEq fun x => ?_
  refine candOf_congr J v fun i hi => ?_
  have hmem : tnodeAncAt (J + 1) v i ∈ (tnodeTree (J + 1)).path v := (tnodeTree (J + 1)).ancAt_mem_path hi
  simp only [ext]
  rw [dif_pos hmem]

theorem hasDual_retrieveD {t : DNode J → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell J S v) (t v)) {Pc : ℝ} (hPc : 0 ≤ Pc)
    (hret : ∀ v, 2 * ∑ w ∈ (tnodeTree (J + 1)).path v, t w ≤ Pc) (e : Ord (DNode J))
    (tr : Trans Bool (J + 3)) : HasDual (retrieveD J S e tr) Pc := by
  unfold retrieveD
  split_ifs
  · exact (hasDual_candOf_path J S ht hcell _).mono (hret _)
  · exact (hasDual_const fun _ _ => rfl).mono hPc

/-- The state of one draw: its decision transcript and the retrieved record. -/
abbrev SDraw (N : ℕ) (σ : Type) (J : ℕ) : Type := Trans Bool (J + 3) × Record N σ

/-- **A draw**: decisions, then retrieval. -/
noncomputable def drawD (completed : List (Record N σ)) (e : Ord (DNode J)) (x : Fin N → σ) :
    SDraw N σ J :=
  (decChain letter J S completed e x, retrieveD J S e (decChain letter J S completed e x) x)

theorem hasDual_drawD {t : DNode J → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell J S v) (t v)) {Vc : ℝ}
    (hdec : ∀ completed e k, HasDual (decD letter J S completed e k) Vc) {Pc : ℝ} (hPc : 0 ≤ Pc)
    (hret : ∀ v, 2 * ∑ w ∈ (tnodeTree (J + 1)).path v, t w ≤ Pc) (completed : List (Record N σ))
    (e : Ord (DNode J)) :
    HasDual (drawD letter J S completed e) ((J + 3) * Vc + Pc) := by
  have hD : HasDual (decChain letter J S completed e) ((J + 3) * Vc) := by
    unfold decChain
    have := hasDual_chain_const (decStep letter J S completed e) (c := Vc)
      (fun i prev => hdec completed e (thrD (qD J) prev)) (J + 3)
    exact_mod_cast this
  exact HasDual.adaptiveCall hD (fun d => hasDual_retrieveD J S ht hcell hPc hret e d)

/-! ## Rounds -/

variable (b : ℕ)

/-- A row of orderings extended to all naturals by the canonical ordering. -/
noncomputable def rowExt (row : Fin (2 * b) → Ord (DNode J)) (i : ℕ) : Ord (DNode J) :=
  if h : i < 2 * b then row ⟨i, h⟩ else Fintype.equivFin (DNode J)

/-- **A round**: `2b` draws against the same cache. -/
noncomputable def roundD (completed : List (Record N σ)) (row : Fin (2 * b) → Ord (DNode J))
    (x : Fin N → σ) : Trans (SDraw N σ J) (2 * b) :=
  chain (fun i _ x => drawD letter J S completed (rowExt J b row i) x) (2 * b) x

/-- The batch of a round: the union of its retrieved records. -/
noncomputable def batchOf (T : Trans (SDraw N σ J) (2 * b)) : Record N σ :=
  unionTuple fun i : Fin (2 * b) => (Trans.get T i i.isLt).2

theorem hasDual_roundD {t : DNode J → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell J S v) (t v)) {Vc : ℝ}
    (hdec : ∀ completed e k, HasDual (decD letter J S completed e k) Vc) {Pc : ℝ} (hPc : 0 ≤ Pc)
    (hret : ∀ v, 2 * ∑ w ∈ (tnodeTree (J + 1)).path v, t w ≤ Pc) (completed : List (Record N σ))
    (row : Fin (2 * b) → Ord (DNode J)) :
    HasDual (roundD letter J S b completed row) ((2 * b : ℕ) * ((J + 3) * Vc + Pc)) := by
  unfold roundD
  exact hasDual_chain_const _ (fun i _ => hasDual_drawD letter J S ht hcell hdec hPc hret completed _)
    (2 * b)

/-! ## The doubling -/

/-- The cache of a transcript of rounds: the saved history, newest first — after each round
the accumulated union of its batch with the previous saved union (`saveBatch`). -/
noncomputable def cacheOf : ∀ {ρ : ℕ}, Trans (Trans (SDraw N σ J) (2 * b)) ρ → List (Record N σ)
  | 0, _ => []
  | _ + 1, T => saveBatch (cacheOf T.1) (batchOf J b T.2)

/-- Rows of orderings extended to all naturals. -/
noncomputable def rowsExt {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord (DNode J)) (ρ : ℕ) :
    Fin (2 * b) → Ord (DNode J) :=
  if h : ρ < R then rows ⟨ρ, h⟩ else fun _ => Fintype.equivFin (DNode J)

/-- **The doubling chain**: `R` rounds. -/
noncomputable def dblChain {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord (DNode J)) (x : Fin N → σ) :
    Trans (Trans (SDraw N σ J) (2 * b)) R :=
  chain (fun ρ prev x => roundD letter J S b (cacheOf J b prev) (rowsExt J b rows ρ) x) R x

/-- **The output**: the compressed union of all batches. -/
noncomputable def dblOut {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord (DNode J)) (x : Fin N → σ) :
    Record N σ :=
  Record.compress letter b (unionList (cacheOf J b (dblChain letter J S b rows x)))

theorem hasDual_dblChain {t : DNode J → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell J S v) (t v)) {Vc : ℝ}
    (hdec : ∀ completed e k, HasDual (decD letter J S completed e k) Vc) {Pc : ℝ} (hPc : 0 ≤ Pc)
    (hret : ∀ v, 2 * ∑ w ∈ (tnodeTree (J + 1)).path v, t w ≤ Pc) {R : ℕ}
    (rows : Fin R → Fin (2 * b) → Ord (DNode J)) :
    HasDual (dblChain letter J S b rows) (R * ((2 * b : ℕ) * ((J + 3) * Vc + Pc))) := by
  unfold dblChain
  exact hasDual_chain_const _
    (fun ρ prev => hasDual_roundD letter J S b ht hcell hdec hPc hret _ _) R

/-- **The dual of the doubling output.** -/
theorem hasDual_dblOut {t : DNode J → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell J S v) (t v)) {Vc : ℝ} (hVc : 0 ≤ Vc)
    (hdec : ∀ completed e k, HasDual (decD letter J S completed e k) Vc) {Pc : ℝ} (hPc : 0 ≤ Pc)
    (hret : ∀ v, 2 * ∑ w ∈ (tnodeTree (J + 1)).path v, t w ≤ Pc) {R : ℕ}
    (rows : Fin R → Fin (2 * b) → Ord (DNode J)) :
    HasDual (dblOut letter J S b rows) (2 * (R * ((2 * b : ℕ) * ((J + 3) * Vc + Pc)))) :=
  HasDual.postcomp_of_determined (by positivity)
    (hasDual_dblChain letter J S b ht hcell hdec hPc hret rows)
    (fun x y h => by unfold dblOut; rw [h])

/-! ## The transcript computes the semantic thinning run -/

lemma chain_get {ι' σ' S' : Type} [Fintype ι'] [DecidableEq ι'] [Fintype σ'] [DecidableEq σ']
    [Fintype S'] [DecidableEq S'] (step : ∀ ρ, Trans S' ρ → (ι' → σ') → S') (x : ι' → σ') :
    ∀ (ρ i : ℕ) (hi : i < ρ), Trans.get (chain step ρ x) i hi = step i (chain step i x) x
  | ρ + 1, i, hi => by
    show (if h : i < ρ then Trans.get (chain step ρ x) i h else step ρ (chain step ρ x) x) = _
    split_ifs with h
    · exact chain_get step x ρ i h
    · have : i = ρ := by omega
      subst this; rfl

lemma unionTuple_emptyRec : ∀ (m : ℕ), unionTuple (fun _ : Fin m => (emptyRec : Record N σ)) = emptyRec := by
  intro m
  unfold unionTuple
  suffices h : ∀ (m : ℕ) (cur : Record N σ), accUnion cur (fun _ : Fin m => (emptyRec : Record N σ)) = cur from
    h m emptyRec
  intro m
  induction m with
  | zero => intro cur; rfl
  | succ m ih =>
    intro cur
    rw [accUnion_succ]
    show accUnion (cur.union emptyRec) (fun _ : Fin m => emptyRec) = cur
    rw [ih]
    funext i
    simp [Record.union, emptyRec]

/-- The candidate table for a fixed input. -/
noncomputable abbrev candX (x : Fin N → σ) : DNode J → Record N σ :=
  fun v => candOf J (fun u => cell J S u x) v

/-- **A round equals the semantic round.** -/
theorem batchOf_roundD (completed : List (Record N σ)) (row : Fin (2 * b) → Ord (DNode J))
    (x : Fin N → σ) :
    saveBatch completed (batchOf J b (roundD letter J S b completed row x))
      = thinRound letter (candX J S x) b completed row := by
  unfold thinRound batchOf roundD
  have hget : ∀ i : Fin (2 * b), (Trans.get
      (chain (fun i _ x => drawD letter J S completed (rowExt J b row i) x) (2 * b) x) i i.isLt).2
        = retrieveD J S (row i) (decChain letter J S completed (row i) x) x := by
    intro i
    rw [chain_get]
    unfold drawD rowExt
    simp only [dif_pos i.isLt]
  simp only [hget]
  split_ifs with h
  · congr 1
    unfold unionTuple
    congr 1
    funext i
    unfold retrieveD
    obtain ⟨hf, hl⟩ := decChain_spec letter J S completed (row i) x
    rw [if_pos (hf.2 h), hl h]
    rfl
  · have hnf : ∀ i : Fin (2 * b), foundOf J (decChain letter J S completed (row i) x) = false := by
      intro i
      obtain ⟨hf, _⟩ := decChain_spec letter J S completed (row i) x
      rw [Bool.eq_false_iff]; intro hc; exact h (hf.1 hc)
    have : (fun i : Fin (2 * b) => retrieveD J S (row i) (decChain letter J S completed (row i) x) x)
        = fun _ => emptyRec := by
      funext i; unfold retrieveD; rw [hnf i]; rfl
    rw [this, unionTuple_emptyRec]

/-- `thinRun` peeled from the end. -/
lemma thinRun_snoc {Λ : Type} [Fintype Λ] [DecidableEq Λ] (cand : Λ → Record N σ) (ρ : ℕ) :
    ∀ (completed : List (Record N σ)) (rows : Fin (ρ + 1) → Fin (2 * b) → Ord Λ),
      thinRun letter cand b (ρ + 1) completed rows
        = thinRound letter cand b (thinRun letter cand b ρ completed (Fin.init rows)) (rows (Fin.last ρ)) := by
  induction ρ with
  | zero =>
    intro completed rows
    show thinRun letter cand b 0 (thinRound letter cand b completed (rows 0)) (Fin.tail rows) = _
    rw [thinRun_zero, thinRun_zero]
    rfl
  | succ ρ ih =>
    intro completed rows
    show thinRun letter cand b (ρ + 1) (thinRound letter cand b completed (rows 0)) (Fin.tail rows) = _
    rw [ih]
    show _ = thinRound letter cand b (thinRun letter cand b ρ
      (thinRound letter cand b completed (Fin.init rows 0)) (Fin.tail (Fin.init rows))) (rows (Fin.last (ρ + 1)))
    rw [Fin.tail_init_eq_init_tail]
    have h0 : Fin.init rows 0 = rows 0 := by simp [Fin.init]
    have hl : Fin.tail rows (Fin.last ρ) = rows (Fin.last (ρ + 1)) := by simp [Fin.tail, Fin.succ_last]
    rw [h0, hl]

lemma cacheOf_pair {ρ : ℕ} (T : Trans (Trans (SDraw N σ J) (2 * b)) ρ)
    (r : Trans (SDraw N σ J) (2 * b)) :
    cacheOf J b (ρ := ρ + 1) (T, r) = saveBatch (cacheOf J b T) (batchOf J b r) := rfl

/-- **The cache of the doubling chain is the semantic thinning run.** -/
theorem cacheOf_dblChain {R : ℕ} (rows : Fin R → Fin (2 * b) → Ord (DNode J)) (x : Fin N → σ) :
    ∀ ρ (hρ : ρ ≤ R),
      cacheOf J b (chain (fun ρ prev x => roundD letter J S b (cacheOf J b prev) (rowsExt J b rows ρ) x) ρ x)
        = thinRun letter (candX J S x) b ρ [] (fun i : Fin ρ => rows ⟨i, by omega⟩)
  | 0, _ => rfl
  | ρ + 1, hρ => by
    rw [chain_succ]
    refine (cacheOf_pair J b _ _).trans ?_
    rw [cacheOf_dblChain rows x ρ (by omega), thinRun_snoc]
    have hinit : Fin.init (fun i : Fin (ρ + 1) => rows ⟨i, by omega⟩)
        = fun i : Fin ρ => rows ⟨i, by omega⟩ := by
      funext i; simp [Fin.init]
    rw [hinit, ← batchOf_roundD]
    have hrow : rowsExt J b rows ρ = rows ⟨((Fin.last ρ : Fin (ρ + 1)) : ℕ), by simp; omega⟩ := by
      unfold rowsExt
      rw [dif_pos (by omega)]
      exact congrArg rows (Fin.ext (by simp))
    rw [hrow]

/-! ## Truthfulness and support for every seed -/

variable (x : Fin N → σ)

lemma frontierFrom_truthful' {J' : ℕ} {S' : TNode J' → Record N σ}
    (hSt : ∀ w, 1 ≤ (w.1 : ℕ) → (S' w).Truthful x) (v : TNode J') (hv : (v.1 : ℕ) < J') :
    ∀ i : ℕ, i ≤ (v.1 : ℕ) → (frontierFrom S' v hv i).Truthful x := by
  refine downward_induction (fun i => (frontierFrom S' v hv i).Truthful x) ?_ ?_
  · rw [frontierFrom_of_not_lt S' v hv (lt_irrefl _)]
    exact Record.truthful_union (hSt _ (by unfold tnodeChild; simp)) (hSt _ (by unfold tnodeChild; simp))
  · intro i hi ih
    rw [frontierFrom_of_lt S' v hv hi]
    exact Record.truthful_union (hSt _ (by unfold tnodeSib tnodeChild; simp)) ih

lemma supp_frontierFrom_subset' {J' Q' : ℕ} {S' : TNode J' → Record N σ}
    (hSs : ∀ w, 1 ≤ (w.1 : ℕ) → (S' w).supp ⊆ nodeIvl (N := N) J' Q' w) (v : TNode J')
    (hv : (v.1 : ℕ) < J') :
    ∀ i : ℕ, i ≤ (v.1 : ℕ) → (frontierFrom S' v hv i).supp ⊆ nodeIvl (N := N) J' Q' (tnodeAncAt J' v i) := by
  refine downward_induction
    (fun i => (frontierFrom S' v hv i).supp ⊆ nodeIvl (N := N) J' Q' (tnodeAncAt J' v i)) ?_ ?_
  · rw [frontierFrom_of_not_lt S' v hv (lt_irrefl _), Record.supp_union, tnodeAncAt_self v,
      nodeIvl_eq_union_children v hv]
    exact Finset.union_subset_union (hSs _ (by unfold tnodeChild; simp)) (hSs _ (by unfold tnodeChild; simp))
  · intro i hi ih
    rw [frontierFrom_of_lt S' v hv hi, Record.supp_union]
    refine Finset.union_subset ((hSs _ (by unfold tnodeSib tnodeChild; simp)).trans
      (nodeIvl_sib_subset_ancAt v hi)) (ih.trans ?_)
    rcases tnodeSib_or v hi with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> exact nodeIvl_child_subset _ _ _

lemma candX_truthful (hSt : ∀ w : DNode J, 1 ≤ (w.1 : ℕ) → (S w x).Truthful x) (v : DNode J) :
    (candX J S x v).Truthful x := by
  unfold candX candOf
  split_ifs with hv
  · unfold frontierRec
    exact frontierFrom_truthful' x (S' := Sof J (fun u => cell J S u x))
      (fun w hw => by rw [Sof_cell J S x w hw]; exact hSt w hw) v hv 0 (Nat.zero_le _)
  · exact truthful_emptyRec x

lemma candX_supp_subset (hSs : ∀ w : DNode J, 1 ≤ (w.1 : ℕ) → (S w x).supp ⊆ nodeIvl (N := N) (J + 1) Q w)
    (v : DNode J) : (candX J S x v).supp ⊆ ivl (J + 1) Q := by
  unfold candX candOf
  split_ifs with hv
  · unfold frontierRec
    have h := supp_frontierFrom_subset' (Q' := Q) (S' := Sof J (fun u => cell J S u x))
      (fun w hw => by rw [Sof_cell J S x w hw]; exact hSs w hw) v hv 0 (Nat.zero_le _)
    rw [nodeIvl_ancAt_zero] at h
    exact h
  · simp

/-- Every seed gives a truthful record. -/
theorem dblOut_truthful (hSt : ∀ w : DNode J, 1 ≤ (w.1 : ℕ) → (S w x).Truthful x) {R : ℕ}
    (rows : Fin R → Fin (2 * b) → Ord (DNode J)) : (dblOut letter J S b rows x).Truthful x := by
  unfold dblOut dblChain
  refine Record.truthful_compress letter (truthful_unionList x fun A hA => ?_) b
  rw [cacheOf_dblChain letter J S b rows x R le_rfl] at hA
  exact thinRun_truthful letter (candX J S x) b x (candX_truthful J S x hSt) R [] (by simp) _ A hA

lemma supp_thinRun_subset {Λ : Type} [Fintype Λ] [DecidableEq Λ] (cand : Λ → Record N σ)
    (I : Finset (Fin N)) (hcand : ∀ ℓ, (cand ℓ).supp ⊆ I) :
    ∀ (R : ℕ) (completed : List (Record N σ)), (∀ A ∈ completed, A.supp ⊆ I) →
      ∀ rows : Fin R → Fin (2 * b) → Ord Λ, ∀ A ∈ thinRun letter cand b R completed rows, A.supp ⊆ I
  | 0, _, hc, _ => hc
  | R + 1, completed, hc, rows => by
    refine supp_thinRun_subset cand I hcand R _ ?_ (Fin.tail rows)
    have hU : (unionList completed).supp ⊆ I := supp_unionList_subset _ I hc
    unfold thinRound
    split_ifs with h
    · intro A hA
      rw [saveBatch, List.mem_cons] at hA
      rcases hA with rfl | hA
      · rw [Record.supp_union]
        exact Finset.union_subset (supp_unionTuple_subset _ I fun i => hcand _) hU
      · exact hc A hA
    · intro A hA
      rw [saveBatch, List.mem_cons] at hA
      rcases hA with rfl | hA
      · rw [Record.supp_union, supp_emptyRec, Finset.empty_union]
        exact hU
      · exact hc A hA

/-- Every seed gives a record inside the interval. -/
theorem supp_dblOut_subset {b : ℕ} (hb : IsBreadthBound letter b)
    (hSs : ∀ w : DNode J, 1 ≤ (w.1 : ℕ) → (S w x).supp ⊆ nodeIvl (N := N) (J + 1) Q w) {R : ℕ}
    (rows : Fin R → Fin (2 * b) → Ord (DNode J)) :
    (dblOut letter J S b rows x).supp ⊆ ivl (J + 1) Q := by
  unfold dblOut dblChain
  refine (Record.compress_spec letter hb _).1.trans (supp_unionList_subset _ _ fun A hA => ?_)
  rw [cacheOf_dblChain letter J S b rows x R le_rfl] at hA
  exact supp_thinRun_subset letter b (candX J S x) _ (candX_supp_subset J Q S x hSs) R [] (by simp) _ A hA

/-- Every seed gives at most `b` positions. -/
theorem card_dblOut_le {b : ℕ} (hb : IsBreadthBound letter b) {R : ℕ}
    (rows : Fin R → Fin (2 * b) → Ord (DNode J)) : (dblOut letter J S b rows x).supp.card ≤ b :=
  (Record.compress_spec letter hb _).2.1

/-! ## Correctness -/

open Classical in
/-- **The doubling fails with probability at most `|V|·2^{-R}`** when all child summaries are
correct `r`-summaries (`r ≥ 1`). -/
theorem dbl_fail_le (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b)
    {r : ℕ} (hr : 1 ≤ r)
    (hSc : ∀ w : DNode J, 1 ≤ (w.1 : ℕ) →
      IsSummary letter x b r (J + 1 - w.1) (Q * 2 ^ (w.1 : ℕ) + w.2) (S w x)) (R : ℕ) :
    ∑ rows : Fin R → Fin (2 * b) → Ord (DNode J), tupleW (tupleW (unifW (Ord (DNode J)))) rows
        * (if IsSummary letter x b (2 * r) (J + 1) Q (dblOut letter J S b rows x) then 0 else 1)
      ≤ (Fintype.card (DNode J) : ℝ) * (1 / 2) ^ R := by
  classical
  have hSt : ∀ w : DNode J, 1 ≤ (w.1 : ℕ) → (S w x).Truthful x := fun w hw => (hSc w hw).truthful
  have hSs : ∀ w : DNode J, 1 ≤ (w.1 : ℕ) → (S w x).supp ⊆ nodeIvl (N := N) (J + 1) Q w :=
    fun w hw => (hSc w hw).supp_subset
  have hcand := candX_truthful J S x hSt
  refine le_trans (Finset.sum_le_sum fun rows _ => mul_le_mul_of_nonneg_left ?_
    (tupleW_nonneg (isWeight_tupleW (isWeight_unifW _) _) rows))
    (thinRun_fail_le letter (candX J S x) b x hcand hst hb hb1 R (completed := []) (by simp))
  -- pointwise: no live label ⇒ a `2r`-summary
  split_ifs with hsum hlive1 hlive
  · norm_num
  · norm_num
  · norm_num
  · exfalso
    apply hsum
    have hcache : cacheOf J b (dblChain letter J S b rows x)
        = thinRun letter (candX J S x) b R [] rows := by
      have h := cacheOf_dblChain letter J S b rows x R le_rfl
      have hrows : (fun i : Fin R => rows ⟨i, by omega⟩) = rows := funext fun i => rfl
      rw [hrows] at h
      exact h
    have htr : ∀ A ∈ thinRun letter (candX J S x) b R [] rows, A.Truthful x :=
      thinRun_truthful letter (candX J S x) b x hcand R [] (by simp) rows
    refine ⟨dblOut_truthful letter J S b x hSt rows, supp_dblOut_subset letter J Q S x hb hSs rows,
      card_dblOut_le letter J S x hb rows, fun U hU hcard => ?_⟩
    obtain ⟨v, hv, hdom⟩ := median_frontier_covers letter hst x (fun w => S w x) hSc
      (by omega) hr U hU hcard
    refine hdom.trans ?_
    rw [← candOf_cell J S x v hv]
    have := prod_le_of_thinLive_empty letter (candX J S x) b x hcand hst hb hb1 htr hlive v
    unfold dblOut
    rw [hcache]
    exact this

end RankDoubling

end MonoidProduct
