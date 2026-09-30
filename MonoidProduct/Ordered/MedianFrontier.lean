import MonoidProduct.Ordered.Correct
import QuantumQueryComplexity.TreeSearch

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Median frontiers (the paper's `lem:beta-median-frontier`)

The balanced binary tree below the dyadic interval `(J, Q)` has vertices `(d, ν)` with
`d ≤ J`, `ν < 2^d`, node interval `ivl (J − d) (Q·2^d + ν)`, and the ancestor of `(d, ν)`
at depth `i` is `(i, ν / 2^(d−i))` (`tnodeTree`, an `AncTree`).  For an internal vertex
`v` (depth `< J`) its **frontier** consists of its two children and, for every ancestor
`u` of `v`, the child of `u` off the path; these intervals partition the word.

Given a record `S w` for every vertex `w`, the frontier record of `v` is the union of
`S` over its frontier (`frontierRec`), assembled along the root path.  If each `S w` is an
`r`-summary of its interval, then for every subword `U` with at most `2r` positions
there is an internal `v` whose frontier record dominates `U`
(`median_frontier_covers`): split `U` between its two middle positions `a < b` (by rank)
and take `v` = the lowest common ancestor of `a` and `b`; each frontier interval then
contains at most `r` positions of `U`, and the domination follows from the summaries'
domination interval by interval, multiplied in chronological order
(`prod_le_frontierRec_of_counts`).
-/

namespace MonoidProduct

open Finset QuantumQueryComplexity

section MedianFrontier

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable (letter : σ → M) {N : ℕ}

/-! ## Dyadic intervals: children -/

lemma ivl_succ_eq_union (j q : ℕ) :
    ivl (N := N) (j + 1) q = ivl j (2 * q) ∪ ivl j (2 * q + 1) := by
  ext i
  simp only [mem_ivl, Finset.mem_union]
  have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
  have e1 : q * 2 ^ (j + 1) = 2 * q * 2 ^ j := by rw [h2]; ring
  have e2 : (q + 1) * 2 ^ (j + 1) = (2 * q + 1) * 2 ^ j + 2 ^ j := by rw [h2]; ring
  have e3 : (2 * q + 1) * 2 ^ j = 2 * q * 2 ^ j + 2 ^ j := by ring
  have e4 : (2 * q + 1 + 1) * 2 ^ j = 2 * q * 2 ^ j + 2 ^ j + 2 ^ j := by ring
  rw [e1, e2, e3, e4]
  omega

lemma ivl_child_sep (j q : ℕ) {i i' : Fin N} (hi : i ∈ ivl (N := N) j (2 * q))
    (hi' : i' ∈ ivl (N := N) j (2 * q + 1)) : i < i' := by
  rw [mem_ivl] at hi hi'
  rw [Fin.lt_def]
  omega

lemma ivl_child_left_subset (j q : ℕ) : ivl (N := N) j (2 * q) ⊆ ivl (j + 1) q := by
  rw [ivl_succ_eq_union]; exact Finset.subset_union_left

lemma ivl_child_right_subset (j q : ℕ) : ivl (N := N) j (2 * q + 1) ⊆ ivl (j + 1) q := by
  rw [ivl_succ_eq_union]; exact Finset.subset_union_right

/-! ## The tree below `(J, Q)` -/

/-- Vertices of the depth-`J` tree: a depth and an index below `2^depth`. -/
abbrev TNode (J : ℕ) : Type := Σ d : Fin (J + 1), Fin (2 ^ (d : ℕ))

lemma tnode_ext {J : ℕ} {v w : TNode J} (h1 : (v.1 : ℕ) = w.1) (h2 : (v.2 : ℕ) = w.2) : v = w :=
  Sigma.ext (Fin.ext h1) ((Fin.heq_ext_iff (by rw [h1])).2 h2)

/-- The node interval of `(d, ν)` below `(J, Q)`. -/
def nodeIvl (J Q : ℕ) (v : TNode J) : Finset (Fin N) :=
  ivl (J - v.1) (Q * 2 ^ (v.1 : ℕ) + v.2)

/-- The ancestor of `v` at depth `i`. -/
def tnodeAncAt (J : ℕ) (v : TNode J) (i : ℕ) : TNode J :=
  if h : i ≤ v.1 then
    ⟨⟨i, by omega⟩, ⟨v.2 / 2 ^ ((v.1 : ℕ) - i), by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' h]
      exact v.2.isLt⟩⟩
  else v

lemma tnodeAncAt_fst {J : ℕ} (v : TNode J) {i : ℕ} (h : i ≤ v.1) :
    ((tnodeAncAt J v i).1 : ℕ) = i := by
  unfold tnodeAncAt; rw [dif_pos h]

lemma tnodeAncAt_snd {J : ℕ} (v : TNode J) {i : ℕ} (h : i ≤ v.1) :
    ((tnodeAncAt J v i).2 : ℕ) = v.2 / 2 ^ ((v.1 : ℕ) - i) := by
  unfold tnodeAncAt; rw [dif_pos h]

lemma tnodeAncAt_self {J : ℕ} (v : TNode J) : tnodeAncAt J v v.1 = v :=
  tnode_ext (tnodeAncAt_fst v le_rfl)
    (by rw [tnodeAncAt_snd v le_rfl, Nat.sub_self, pow_zero, Nat.div_one])

/-- **The tree as an ancestor structure.** -/
def tnodeTree (J : ℕ) : AncTree (TNode J) where
  depth v := v.1
  ancAt := tnodeAncAt J
  depth_ancAt v i h := tnodeAncAt_fst v h
  ancAt_self v := tnode_ext (tnodeAncAt_fst v le_rfl)
    (by rw [tnodeAncAt_snd v le_rfl, Nat.sub_self, pow_zero, Nat.div_one])
  ancAt_ancAt v i j hj hi := by
    refine tnode_ext ?_ ?_
    · rw [tnodeAncAt_fst _ (by rw [tnodeAncAt_fst v hi]; exact hj), tnodeAncAt_fst v (hj.trans hi)]
    · rw [tnodeAncAt_snd _ (by rw [tnodeAncAt_fst v hi]; exact hj), tnodeAncAt_snd v hi,
        tnodeAncAt_snd v (hj.trans hi), tnodeAncAt_fst v hi, Nat.div_div_eq_div_mul, ← pow_add]
      congr 2
      omega

/-- The child `c ∈ {0, 1}` of a vertex of depth `< J`. -/
def tnodeChild (J : ℕ) (v : TNode J) (hv : (v.1 : ℕ) < J) (c : Fin 2) : TNode J :=
  ⟨⟨v.1 + 1, by omega⟩, ⟨2 * v.2 + c, by
    rw [pow_succ]
    have := v.2.isLt
    have := c.isLt
    omega⟩⟩

lemma nodeIvl_child {J Q : ℕ} (v : TNode J) (hv : (v.1 : ℕ) < J) (c : Fin 2) :
    nodeIvl (N := N) J Q (tnodeChild J v hv c)
      = ivl (J - v.1 - 1) (2 * (Q * 2 ^ (v.1 : ℕ) + v.2) + c) := by
  show ivl (J - ((v.1 : ℕ) + 1)) (Q * 2 ^ ((v.1 : ℕ) + 1) + (2 * (v.2 : ℕ) + (c : ℕ))) = _
  rw [show J - ((v.1 : ℕ) + 1) = J - v.1 - 1 by omega, pow_succ]
  congr 1
  ring

/-- The node interval of the ancestor at depth `i` splits into its two children, one of
which is the ancestor at depth `i + 1`. -/
lemma nodeIvl_ancAt_eq_union {J Q : ℕ} (v : TNode J) {i : ℕ} (hi : i < v.1) :
    nodeIvl (N := N) J Q (tnodeAncAt J v i)
      = nodeIvl J Q (tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega) 0)
        ∪ nodeIvl J Q (tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega) 1) := by
  rw [nodeIvl_child, nodeIvl_child]
  unfold nodeIvl
  rw [tnodeAncAt_snd v hi.le, tnodeAncAt_fst v hi.le]
  have hJ : J - i = (J - i - 1) + 1 := by have := v.1.isLt; omega
  rw [hJ, ivl_succ_eq_union]
  simp only [Nat.add_sub_cancel, Fin.val_zero, Fin.val_one, add_zero]

/-- The path child: the ancestor at depth `i + 1` is the child `bit` of the ancestor at
depth `i`, where `bit = (index at depth i+1) % 2`. -/
lemma tnodeAncAt_succ_eq_child {J : ℕ} (v : TNode J) {i : ℕ} (hi : i < v.1) :
    tnodeAncAt J v (i + 1)
      = tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega)
          ⟨((tnodeAncAt J v (i + 1)).2 : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩ := by
  refine tnode_ext ?_ ?_
  · unfold tnodeChild; simp only
    rw [tnodeAncAt_fst v hi, tnodeAncAt_fst v hi.le]
  · unfold tnodeChild; simp only
    rw [tnodeAncAt_snd v hi, tnodeAncAt_snd v hi.le]
    have e : (v.1 : ℕ) - i = ((v.1 : ℕ) - (i + 1)) + 1 := by omega
    have key : (v.2 : ℕ) / 2 ^ ((v.1 : ℕ) - i) = (v.2 : ℕ) / 2 ^ ((v.1 : ℕ) - (i + 1)) / 2 := by
      rw [e, pow_succ, Nat.div_div_eq_div_mul]
    rw [key]
    exact (Nat.div_add_mod _ 2).symm

/-! ## Frontier records -/

/-- The sibling of the path child at depth `i + 1` below `v` (for `i < depth v`). -/
def tnodeSib (J : ℕ) (v : TNode J) (i : ℕ) (hi : i < v.1) : TNode J :=
  tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega)
    ⟨1 - ((tnodeAncAt J v (i + 1)).2 : ℕ) % 2, by omega⟩

/-- The frontier record of `v`, assembled from depth `i` downwards: the siblings at depths
`i+1, …, depth v` and the two children of `v`. -/
noncomputable def frontierFrom {J : ℕ} (S : TNode J → Record N σ) (v : TNode J)
    (hv : (v.1 : ℕ) < J) : ℕ → Record N σ
  | i =>
    if h : i < v.1 then
      (S (tnodeSib J v i h)).union (frontierFrom S v hv (i + 1))
    else (S (tnodeChild J v hv 0)).union (S (tnodeChild J v hv 1))
termination_by i => (v.1 : ℕ) - i

/-- **The frontier record** of an internal vertex. -/
noncomputable def frontierRec {J : ℕ} (S : TNode J → Record N σ) (v : TNode J)
    (hv : (v.1 : ℕ) < J) : Record N σ :=
  frontierFrom S v hv 0

lemma frontierFrom_of_lt {J : ℕ} (S : TNode J → Record N σ) (v : TNode J) (hv : (v.1 : ℕ) < J)
    {i : ℕ} (h : i < v.1) :
    frontierFrom S v hv i = (S (tnodeSib J v i h)).union (frontierFrom S v hv (i + 1)) := by
  rw [frontierFrom, dif_pos h]

lemma frontierFrom_of_not_lt {J : ℕ} (S : TNode J → Record N σ) (v : TNode J) (hv : (v.1 : ℕ) < J)
    {i : ℕ} (h : ¬ i < v.1) :
    frontierFrom S v hv i = (S (tnodeChild J v hv 0)).union (S (tnodeChild J v hv 1)) := by
  rw [frontierFrom, dif_neg h]

/-! ## Domination along the path -/

variable (hst : IsStableOrder M)
include hst

/-- Separated union, in either order. -/
lemma prod_le_of_split {x : Fin N → σ} {U A B : Finset (Fin N)} {KA KB : Record N σ}
    (hA : KA.Truthful x) (hB : KB.Truthful x) (hsA : KA.supp ⊆ A) (hsB : KB.supp ⊆ B)
    (hsep : ∀ i ∈ A, ∀ i' ∈ B, i < i')
    (h1 : subwordProd letter x (U ∩ A) ≤ KA.prod letter)
    (h2 : subwordProd letter x (U ∩ B) ≤ KB.prod letter) :
    subwordProd letter x (U ∩ (A ∪ B)) ≤ (KA.union KB).prod letter := by
  rw [Finset.inter_union_distrib_left,
    subwordProd_union_of_sep letter x (fun i hi i' hi' =>
      hsep i (Finset.mem_inter.1 hi).2 i' (Finset.mem_inter.1 hi').2),
    prod_union_truthful letter x hA hB,
    subwordProd_union_of_sep letter x (fun i hi i' hi' => hsep i (hsA hi) i' (hsB hi'))]
  rw [Record.prod_of_truthful letter hA] at h1
  rw [Record.prod_of_truthful letter hB] at h2
  exact hst.mul_le_mul h1 h2

omit hst in
/-- Downward induction from `n`. -/
lemma downward_induction {n : ℕ} (P : ℕ → Prop) (base : P n)
    (step : ∀ i, i < n → P (i + 1) → P i) : ∀ i, i ≤ n → P i := by
  suffices h : ∀ m i, i + m = n → P i from fun i hi => h (n - i) i (by omega)
  intro m
  induction m with
  | zero => intro i hi; rw [Nat.add_zero] at hi; rw [hi]; exact base
  | succ m ih => intro i hi; exact step i (by omega) (ih (i + 1) (by omega))

omit hst in
lemma nodeIvl_eq_union_children {J Q : ℕ} (w : TNode J) (hw : (w.1 : ℕ) < J) :
    nodeIvl (N := N) J Q w = nodeIvl J Q (tnodeChild J w hw 0) ∪ nodeIvl J Q (tnodeChild J w hw 1) := by
  rw [nodeIvl_child, nodeIvl_child]
  unfold nodeIvl
  have hJ : J - w.1 = (J - w.1 - 1) + 1 := by omega
  rw [hJ, ivl_succ_eq_union]
  simp only [Nat.add_sub_cancel, Fin.val_zero, Fin.val_one, add_zero]

omit hst in
lemma nodeIvl_children_sep {J Q : ℕ} (w : TNode J) (hw : (w.1 : ℕ) < J) :
    ∀ i ∈ nodeIvl (N := N) J Q (tnodeChild J w hw 0),
      ∀ i' ∈ nodeIvl (N := N) J Q (tnodeChild J w hw 1), i < i' := by
  intro i hi i' hi'
  rw [nodeIvl_child] at hi hi'
  simp only [Fin.val_zero, Fin.val_one, add_zero] at hi hi'
  exact ivl_child_sep _ _ hi hi'

omit hst in
lemma nodeIvl_child_subset {J Q : ℕ} (w : TNode J) (hw : (w.1 : ℕ) < J) (c : Fin 2) :
    nodeIvl (N := N) J Q (tnodeChild J w hw c) ⊆ nodeIvl J Q w := by
  rw [nodeIvl_eq_union_children w hw]
  fin_cases c
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

omit hst in
/-- The path child and the sibling are the two children of the ancestor. -/
lemma tnodeSib_or {J : ℕ} (v : TNode J) {i : ℕ} (hi : i < v.1) :
    (tnodeAncAt J v (i + 1) = tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega) 0
        ∧ tnodeSib J v i hi = tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega) 1)
    ∨ (tnodeAncAt J v (i + 1) = tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega) 1
        ∧ tnodeSib J v i hi = tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega) 0) := by
  have h := tnodeAncAt_succ_eq_child v hi
  unfold tnodeSib
  rcases Nat.mod_two_eq_zero_or_one ((tnodeAncAt J v (i + 1)).2 : ℕ) with h0 | h1
  · left
    refine ⟨?_, ?_⟩
    · rw [h]; congr 1; exact Fin.ext h0
    · congr 1; exact Fin.ext (by simp [h0])
  · right
    refine ⟨?_, ?_⟩
    · rw [h]; congr 1; exact Fin.ext h1
    · congr 1; exact Fin.ext (by simp [h1])

omit hst in
lemma nodeIvl_subset_ancAt {J Q : ℕ} (v : TNode J) : ∀ i : ℕ, i ≤ (v.1 : ℕ) →
    nodeIvl (N := N) J Q v ⊆ nodeIvl J Q (tnodeAncAt J v i) := by
  refine downward_induction (fun i => nodeIvl (N := N) J Q v ⊆ nodeIvl J Q (tnodeAncAt J v i)) ?_ ?_
  · rw [tnodeAncAt_self v]
  · intro i hi ih
    refine ih.trans ?_
    rcases tnodeSib_or v hi with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> exact nodeIvl_child_subset _ _ _

omit hst in
lemma nodeIvl_ancAt_zero {J Q : ℕ} (v : TNode J) : nodeIvl (N := N) J Q (tnodeAncAt J v 0) = ivl J Q := by
  unfold nodeIvl
  rw [tnodeAncAt_snd v (Nat.zero_le _), tnodeAncAt_fst v (Nat.zero_le _), Nat.sub_zero,
    Nat.sub_zero, Nat.div_eq_of_lt v.2.isLt]
  simp

omit hst in
lemma nodeIvl_sib_subset_ancAt {J Q : ℕ} (v : TNode J) {i : ℕ} (hi : i < v.1) :
    nodeIvl (N := N) J Q (tnodeSib J v i hi) ⊆ nodeIvl J Q (tnodeAncAt J v i) := by
  rcases tnodeSib_or v hi with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> exact nodeIvl_child_subset _ _ _

omit hst in
lemma prod_union_comm {x : Fin N → σ} {A B : Record N σ} (hA : A.Truthful x) (hB : B.Truthful x) :
    (A.union B).prod letter = (B.union A).prod letter := by
  rw [prod_union_truthful letter x hA hB, prod_union_truthful letter x hB hA, Finset.union_comm]

section Frontier

variable {J Q b r : ℕ} (x : Fin N → σ) (S : TNode J → Record N σ)
variable (hS : ∀ w : TNode J, 1 ≤ (w.1 : ℕ) →
  IsSummary letter x b r (J - w.1) (Q * 2 ^ (w.1 : ℕ) + w.2) (S w))
include hS

omit hst in
lemma hS_child {v : TNode J} (hv : (v.1 : ℕ) < J) (c : Fin 2) :
    IsSummary letter x b r (J - (tnodeChild J v hv c).1)
      (Q * 2 ^ ((tnodeChild J v hv c).1 : ℕ) + (tnodeChild J v hv c).2) (S (tnodeChild J v hv c)) :=
  hS _ (by unfold tnodeChild; simp)

omit hst in
lemma hS_sib {v : TNode J} {i : ℕ} (hi : i < v.1) :
    IsSummary letter x b r (J - (tnodeSib J v i hi).1)
      (Q * 2 ^ ((tnodeSib J v i hi).1 : ℕ) + (tnodeSib J v i hi).2) (S (tnodeSib J v i hi)) :=
  hS _ (by unfold tnodeSib tnodeChild; simp)

omit hst in
lemma frontierFrom_truthful (v : TNode J) (hv : (v.1 : ℕ) < J) :
    ∀ i : ℕ, i ≤ (v.1 : ℕ) → (frontierFrom S v hv i).Truthful x := by
  refine downward_induction (fun i => (frontierFrom S v hv i).Truthful x) ?_ ?_
  · rw [frontierFrom_of_not_lt S v hv (lt_irrefl _)]
    exact Record.truthful_union (hS_child letter x S hS hv 0).truthful (hS_child letter x S hS hv 1).truthful
  · intro i hi ih
    rw [frontierFrom_of_lt S v hv hi]
    exact Record.truthful_union (hS_sib letter x S hS hi).truthful ih

omit hst in
lemma supp_frontierFrom_subset (v : TNode J) (hv : (v.1 : ℕ) < J) :
    ∀ i : ℕ, i ≤ (v.1 : ℕ) → (frontierFrom S v hv i).supp ⊆ nodeIvl (N := N) J Q (tnodeAncAt J v i) := by
  refine downward_induction
    (fun i => (frontierFrom S v hv i).supp ⊆ nodeIvl (N := N) J Q (tnodeAncAt J v i)) ?_ ?_
  · rw [frontierFrom_of_not_lt S v hv (lt_irrefl _), Record.supp_union, tnodeAncAt_self v,
      nodeIvl_eq_union_children v hv]
    exact Finset.union_subset_union (hS_child letter x S hS hv 0).supp_subset
      (hS_child letter x S hS hv 1).supp_subset
  · intro i hi ih
    rw [frontierFrom_of_lt S v hv hi, Record.supp_union]
    exact Finset.union_subset
      ((hS_sib letter x S hS hi).supp_subset.trans (nodeIvl_sib_subset_ancAt v hi))
      (ih.trans (nodeIvl_subset_ancAt_succ v hi))
  where
  nodeIvl_subset_ancAt_succ (v : TNode J) {i : ℕ} (hi : i < v.1) :
      nodeIvl (N := N) J Q (tnodeAncAt J v (i + 1)) ⊆ nodeIvl J Q (tnodeAncAt J v i) := by
    rcases tnodeSib_or v hi with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> exact nodeIvl_child_subset _ _ _

/-- Along the path: if every frontier interval meets `U` in at most `r` positions, the frontier
record from depth `i` dominates `U` inside the ancestor at depth `i`. -/
theorem prod_le_frontierFrom (v : TNode J) (hv : (v.1 : ℕ) < J) (U : Finset (Fin N))
    (hsib : ∀ (i : ℕ) (hi : i < (v.1 : ℕ)), (U ∩ nodeIvl (N := N) J Q (tnodeSib J v i hi)).card ≤ r)
    (hch : ∀ c : Fin 2, (U ∩ nodeIvl (N := N) J Q (tnodeChild J v hv c)).card ≤ r) :
    ∀ i : ℕ, i ≤ (v.1 : ℕ) →
      subwordProd letter x (U ∩ nodeIvl (N := N) J Q (tnodeAncAt J v i))
        ≤ (frontierFrom S v hv i).prod letter := by
  refine downward_induction (fun i => subwordProd letter x (U ∩ nodeIvl (N := N) J Q (tnodeAncAt J v i))
    ≤ (frontierFrom S v hv i).prod letter) ?_ ?_
  · rw [frontierFrom_of_not_lt S v hv (lt_irrefl _), tnodeAncAt_self v,
      nodeIvl_eq_union_children v hv]
    exact prod_le_of_split letter hst (hS_child letter x S hS hv 0).truthful
      (hS_child letter x S hS hv 1).truthful (hS_child letter x S hS hv 0).supp_subset
      (hS_child letter x S hS hv 1).supp_subset (nodeIvl_children_sep v hv)
      ((hS_child letter x S hS hv 0).dom _ Finset.inter_subset_right (hch 0))
      ((hS_child letter x S hS hv 1).dom _ Finset.inter_subset_right (hch 1))
  · intro i hi ih
    rw [frontierFrom_of_lt S v hv hi]
    have hsibdom := (hS_sib letter x S hS hi).dom _ Finset.inter_subset_right (hsib i hi)
    have hFtr := frontierFrom_truthful letter x S hS v hv (i + 1) hi
    have hFsupp := supp_frontierFrom_subset letter x S hS v hv (i + 1) hi
    have hu : nodeIvl (N := N) J Q (tnodeAncAt J v i)
        = nodeIvl J Q (tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega) 0)
          ∪ nodeIvl J Q (tnodeChild J (tnodeAncAt J v i) (by rw [tnodeAncAt_fst v hi.le]; omega) 1) :=
      nodeIvl_eq_union_children _ _
    have hsep := nodeIvl_children_sep (N := N) (Q := Q) (tnodeAncAt J v i)
      (by rw [tnodeAncAt_fst v hi.le]; omega)
    rcases tnodeSib_or v hi with ⟨hp, hs⟩ | ⟨hp, hs⟩
    · -- path child first, sibling second
      rw [← hp, ← hs] at hsep
      rw [hu, ← hp, ← hs, prod_union_comm letter (hS_sib letter x S hS hi).truthful hFtr]
      exact prod_le_of_split letter hst hFtr (hS_sib letter x S hS hi).truthful hFsupp
        (hS_sib letter x S hS hi).supp_subset hsep ih hsibdom
    · -- sibling first, path child second
      rw [← hp, ← hs] at hsep
      rw [hu, ← hp, ← hs]
      exact prod_le_of_split letter hst (hS_sib letter x S hS hi).truthful hFtr
        (hS_sib letter x S hS hi).supp_subset hFsupp hsep hsibdom ih

/-! ## Ranks inside a target -/

omit hst hS in
/-- The number of positions of `U` before `p`. -/
def rk (U : Finset (Fin N)) (p : Fin N) : ℕ := (U.filter (· < p)).card

omit hst hS in
lemma rk_lt_of_lt {U : Finset (Fin N)} {a a' : Fin N} (ha : a ∈ U) (h : a < a') :
    rk U a < rk U a' := by
  unfold rk
  refine Finset.card_lt_card ⟨fun p hp => ?_, ?_⟩
  · rw [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, lt_trans hp.2 h⟩
  intro hsub
  have := hsub (Finset.mem_filter.2 ⟨ha, h⟩)
  exact lt_irrefl a (Finset.mem_filter.1 this).2

omit hst hS in
lemma rk_mono {U : Finset (Fin N)} {a a' : Fin N} (h : a ≤ a') : rk U a ≤ rk U a' :=
  Finset.card_le_card fun p hp => by
    rw [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, lt_of_lt_of_le hp.2 h⟩

omit hst hS in
lemma rk_lt_card {U : Finset (Fin N)} {p : Fin N} (hp : p ∈ U) : rk U p < U.card := by
  unfold rk
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
  exact lt_irrefl p (Finset.mem_filter.1 (hsub hp)).2

omit hst hS in
lemma card_filter_gt {U : Finset (Fin N)} {a : Fin N} (ha : a ∈ U) :
    (U.filter (a < ·)).card = U.card - 1 - rk U a := by
  have hdisj : Disjoint (U.filter (· < a)) (U.filter (a < ·)) :=
    Finset.disjoint_filter.2 fun p _ h1 h2 => lt_asymm h1 h2
  have hunion : U.filter (· < a) ∪ U.filter (a < ·) = U.erase a := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hp, h⟩ | ⟨hp, h⟩)
      · exact ⟨ne_of_lt h, hp⟩
      · exact ⟨(ne_of_lt h).symm, hp⟩
    · rintro ⟨hne, hp⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
  have h := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem ha] at h
  unfold rk
  omega

omit hst hS in
/-- Every rank below `|U|` is attained. -/
lemma exists_rk_eq {U : Finset (Fin N)} {k : ℕ} (hk : k < U.card) : ∃ p ∈ U, rk U p = k := by
  classical
  have hinj : Set.InjOn (rk U) U := by
    intro a ha a' ha' h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd h (ne_of_lt (rk_lt_of_lt ha hlt))
    · exact absurd h (ne_of_gt (rk_lt_of_lt ha' hlt))
  have hsub : U.image (rk U) ⊆ Finset.range U.card := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
    exact Finset.mem_range.2 (rk_lt_card hp)
  have hcard : (Finset.range U.card).card ≤ (U.image (rk U)).card := by
    rw [Finset.card_range, Finset.card_image_of_injOn hinj]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : k ∈ U.image (rk U) := by rw [heq]; exact Finset.mem_range.2 hk
  obtain ⟨p, hp, hpk⟩ := Finset.mem_image.1 this
  exact ⟨p, hp, hpk⟩

/-! ## Coverage -/

/-- **Median-frontier coverage.**  If every non-root vertex carries an `r`-summary of its
interval (`r ≥ 1`, `J ≥ 1`), then every subword of at most `2r` positions is dominated by
the frontier record of some internal vertex. -/
theorem median_frontier_covers (hJ : 1 ≤ J) (hr : 1 ≤ r) (U : Finset (Fin N))
    (hU : U ⊆ ivl J Q) (hcard : U.card ≤ 2 * r) :
    ∃ (v : TNode J) (hv : (v.1 : ℕ) < J),
      subwordProd letter x U ≤ (frontierRec S v hv).prod letter := by
  classical
  rcases Nat.lt_or_ge U.card 2 with hlt | hge
  · -- at most one position: the root works
    refine ⟨⟨⟨0, by omega⟩, ⟨0, by simp⟩⟩, hJ, ?_⟩
    have h := prod_le_frontierFrom letter hst x S hS ⟨⟨0, by omega⟩, ⟨0, by simp⟩⟩ hJ U
      (fun i hi => absurd hi (by simp)) (fun c => le_trans (Finset.card_le_card Finset.inter_subset_left)
        (by omega)) 0 (Nat.zero_le _)
    rw [nodeIvl_ancAt_zero, Finset.inter_eq_left.2 hU] at h
    exact h
  · -- two middle positions by rank
    obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
    set s := U.card with hs
    set m := s / 2 with hm
    have hm1 : 1 ≤ m := by omega
    obtain ⟨a, haU, hrka⟩ := exists_rk_eq (U := U) (k := m - 1) (by omega)
    obtain ⟨b', hbU, hrkb⟩ := exists_rk_eq (U := U) (k := m) (by omega)
    have hab : a < b' := by
      by_contra h
      push Not at h
      have := rk_mono (U := U) h
      omega
    have hpair : ({a, b'} : Finset (Fin N)) ⊆ ivl (j + 1) Q :=
      Finset.insert_subset (hU haU) (Finset.singleton_subset_iff.2 (hU hbU))
    have hpc : 2 ≤ ({a, b'} : Finset (Fin N)).card := by
      rw [Finset.card_pair (ne_of_lt hab)]
    obtain ⟨d, hdj, ν, hν, hall, ⟨a₀, ha₀, ha₀c⟩, ⟨b₀, hb₀, hb₀c⟩⟩ := exists_lca hpair hpc
    -- `a` is in the left child and `b'` in the right one
    have hsep' : ∀ {i i' : Fin N}, i ∈ ivl (N := N) (j - d) (2 * (Q * 2 ^ d + ν)) →
        i' ∈ ivl (N := N) (j - d) (2 * (Q * 2 ^ d + ν) + 1) → i < i' :=
      fun hi hi' => ivl_child_sep _ _ hi hi'
    have hac : a ∈ ivl (N := N) (j - d) (2 * (Q * 2 ^ d + ν)) := by
      rcases hall a (Finset.mem_insert_self _ _) with h | h
      · exact h
      · exfalso
        rw [Finset.mem_insert, Finset.mem_singleton] at ha₀
        rcases ha₀ with rfl | rfl
        · exact lt_irrefl _ (hsep' ha₀c h)
        · exact lt_asymm hab (hsep' ha₀c h)
    have hbc : b' ∈ ivl (N := N) (j - d) (2 * (Q * 2 ^ d + ν) + 1) := by
      rcases hall b' (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) with h | h
      · exfalso
        rw [Finset.mem_insert, Finset.mem_singleton] at hb₀
        rcases hb₀ with rfl | rfl
        · exact lt_asymm hab (hsep' h hb₀c)
        · exact lt_irrefl _ (hsep' h hb₀c)
      · exact h
    -- the vertex
    let v : TNode (j + 1) := ⟨⟨d, by omega⟩, ⟨ν, hν⟩⟩
    have hv : (v.1 : ℕ) < j + 1 := by show d < j + 1; omega
    have hchild : ∀ c : Fin 2, nodeIvl (N := N) (j + 1) Q (tnodeChild (j + 1) v hv c)
        = ivl (j - d) (2 * (Q * 2 ^ d + ν) + c) := by
      intro c
      rw [nodeIvl_child]
      show ivl (j + 1 - d - 1) _ = _
      rw [show j + 1 - d - 1 = j - d by omega]
    have hav : a ∈ nodeIvl (N := N) (j + 1) Q v :=
      nodeIvl_child_subset v hv 0 (by rw [hchild]; simpa using hac)
    have hbv : b' ∈ nodeIvl (N := N) (j + 1) Q v :=
      nodeIvl_child_subset v hv 1 (by rw [hchild]; simpa using hbc)
    -- counts
    have hlt_b : (U.filter (· < b')).card = m := hrkb
    have hlt_a : (U.filter (· < a)).card = m - 1 := hrka
    have hgt_a : (U.filter (a < ·)).card = s - 1 - (m - 1) := by rw [card_filter_gt haU, hrka]
    have hgt_b : (U.filter (b' < ·)).card = s - 1 - m := by rw [card_filter_gt hbU, hrkb]
    have hch : ∀ c : Fin 2, (U ∩ nodeIvl (N := N) (j + 1) Q (tnodeChild (j + 1) v hv c)).card ≤ r := by
      intro c
      fin_cases c
      · refine le_trans (Finset.card_le_card (fun p hp => ?_)) (le_of_eq hlt_b |>.trans (by omega))
        rw [Finset.mem_inter, hchild] at hp
        exact Finset.mem_filter.2 ⟨hp.1, hsep' (by simpa using hp.2) hbc⟩
      · refine le_trans (Finset.card_le_card (fun p hp => ?_)) (le_of_eq hgt_a |>.trans (by omega))
        rw [Finset.mem_inter, hchild] at hp
        exact Finset.mem_filter.2 ⟨hp.1, hsep' hac (by simpa using hp.2)⟩
    have hsib : ∀ (i : ℕ) (hi : i < (v.1 : ℕ)),
        (U ∩ nodeIvl (N := N) (j + 1) Q (tnodeSib (j + 1) v i hi)).card ≤ r := by
      intro i hi
      have hpath : nodeIvl (N := N) (j + 1) Q v ⊆ nodeIvl (j + 1) Q (tnodeAncAt (j + 1) v (i + 1)) :=
        nodeIvl_subset_ancAt v (i + 1) hi
      have hsep := nodeIvl_children_sep (N := N) (Q := Q) (tnodeAncAt (j + 1) v i)
        (by rw [tnodeAncAt_fst v hi.le]; omega)
      rcases tnodeSib_or v hi with ⟨hp, hs⟩ | ⟨hp, hs⟩
      · -- sibling is the right child: its positions exceed `b'`
        refine le_trans (Finset.card_le_card (fun p hp' => ?_)) (le_of_eq hgt_b |>.trans (by omega))
        rw [Finset.mem_inter] at hp'
        refine Finset.mem_filter.2 ⟨hp'.1, hsep b' (by rw [← hp]; exact hpath hbv) p (by rw [← hs]; exact hp'.2)⟩
      · -- sibling is the left child: its positions precede `a`
        refine le_trans (Finset.card_le_card (fun p hp' => ?_)) (le_of_eq hlt_a |>.trans (by omega))
        rw [Finset.mem_inter] at hp'
        refine Finset.mem_filter.2 ⟨hp'.1, hsep p (by rw [← hs]; exact hp'.2) a (by rw [← hp]; exact hpath hav)⟩
    refine ⟨v, hv, ?_⟩
    have h := prod_le_frontierFrom letter hst x S hS v hv U hsib hch 0 (Nat.zero_le _)
    rw [nodeIvl_ancAt_zero, Finset.inter_eq_left.2 hU] at h
    exact h

end Frontier

end MedianFrontier

end MonoidProduct
