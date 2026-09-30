import QuantumQueryComplexity.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Unitriangular tropical matrices and the least-common-ancestor decomposition

`T = (ℝ ∪ {-∞}, max, +)` is the max-plus tropical semiring and `U_k(T)` the
monoid of `k × k` matrices with `0` on the diagonal and `-∞` below it.  A matrix
`M ∈ U_k(T)` is an edge-weighted graph on the ordered states `1 < ⋯ < k`: a
self-loop of weight `0` at every state, and a *transition* `s → t` of weight
`M s t` for `s < t`.  In the product `x₁ ⊗ ⋯ ⊗ xₙ`, the `(s,t)` entry is the best
weight of a walk from `s` to `t` that reads the letters in order and takes its
transitions at strictly increasing positions.  Since the states visited strictly
increase, no walk uses more than `t - s ≤ k - 1` transitions: that bounded
*transition budget*, not any chain condition, is what makes the product problem
easy.

Put the complete binary tree on `2 ^ L` positions.  A node is named by its
**height** `j` (its interval has `2 ^ j` positions) and its **prefix** `p` (the
positions `i` with `i / 2 ^ j = p`); `nodeProd letter L j p x` is the product of
the letters under it.  The main theorem of this file is the least-common-ancestor
decomposition: for `s < t`,

  `P_{j,p}(s,t) = D_{j,p}(s,t) ⊔ ⨆_{h < j} L^h_{j,p}(s,t)`,

where `D` is the best *single* direct transition among the letters under the node
and `L^h` is the best split whose least common ancestor has children of height
`h`.  Grouping the splits by level is the whole point: level `h` contains
`2 ^ (j-h-1)` internal nodes but their children have only `2 ^ h` positions each,
and in the query bound the `√` of the first cancels the `√` of the second.

The proof needs no path formula.  Everything follows by induction on `j` from
three facts about `U_k(T)`: the product of an internal node is the tropical
product of its two children, the diagonal is `0`, and everything below the
diagonal is `-∞`.  The last two collapse the two degenerate terms `v = s` and
`v = t` of the matrix product into "the whole path stays in one child", which is
exactly what the induction hypothesis then expands.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-- The carrier of the max-plus tropical semiring: `max` is `⊔`, tropical
multiplication is `+`, and `-∞` is `⊥` and absorbs. -/
abbrev Trop := WithBot ℝ

/-- A `k × k` tropical matrix. -/
abbrev TMat (k : ℕ) := Fin k → Fin k → Trop

variable {k : ℕ}

/-- Tropical matrix multiplication: `(M ⊗ N) s t = ⨆ᵥ (M s v + N v t)`. -/
noncomputable def tmul (M N : TMat k) : TMat k :=
  fun s t => Finset.univ.sup fun v => M s v + N v t

/-- The identity of `U_k(T)`: `0` on the diagonal, `-∞` off it. -/
noncomputable def tone (k : ℕ) : TMat k := fun s t => if s = t then 0 else ⊥

/-- **Unitriangular**: `0` on the diagonal and `-∞` strictly below it.  Entries
above the diagonal are arbitrary tropical values. -/
structure IsUtri (M : TMat k) : Prop where
  /-- The diagonal carries the tropical unit. -/
  diag : ∀ s, M s s = 0
  /-- Nothing runs backwards. -/
  below : ∀ s t, t < s → M s t = ⊥

lemma isUtri_tone : IsUtri (tone k) where
  diag s := by simp [tone]
  below s t h := by simp [tone, ne_of_gt h]

/-- `U_k(T)` is closed under tropical multiplication.  A walk from `s` to `s`
can only stand still, and a walk from `s` to `t < s` cannot exist at all. -/
lemma IsUtri.tmul {M N : TMat k} (hM : IsUtri M) (hN : IsUtri N) :
    IsUtri (tmul M N) where
  diag s := by
    have hmid : M s s + N s s = 0 := by rw [hM.diag, hN.diag]; simp
    refine le_antisymm (Finset.sup_le fun v _ => ?_) ?_
    · rcases lt_trichotomy v s with h | h | h
      · rw [hM.below s v h, WithBot.bot_add]
        exact bot_le
      · subst h
        exact le_of_eq hmid
      · rw [hN.below v s h, WithBot.add_bot]
        exact bot_le
    · refine le_trans (le_of_eq hmid.symm) ?_
      exact Finset.le_sup (f := fun v => M s v + N v s) (Finset.mem_univ s)
  below s t hts := by
    refine (Finset.sup_eq_bot_iff _ _).2 fun v _ => ?_
    rcases lt_or_ge v s with h | h
    · rw [hM.below s v h, WithBot.bot_add]
    · rw [hN.below v t (lt_of_lt_of_le hts h), WithBot.add_bot]

/-! ## Nodes of the binary tree on `2 ^ L` positions -/

variable {L : ℕ}

/-- The positions under the node at height `j` with prefix `p`. -/
def nodeSet (L j p : ℕ) : Finset (Fin (2 ^ L)) :=
  Finset.univ.filter fun i => (i : ℕ) / 2 ^ j = p

lemma mem_nodeSet {j p : ℕ} {i : Fin (2 ^ L)} :
    i ∈ nodeSet L j p ↔ (i : ℕ) / 2 ^ j = p := by simp [nodeSet]

/-- **A node splits into its two children.**  Dividing by `2 ^ (j+1)` is dividing
by `2 ^ j` and then by `2`, and the prefixes that halve to `p` are `2p` and
`2p+1`. -/
lemma nodeSet_succ (j p : ℕ) :
    nodeSet L (j + 1) p = nodeSet L j (2 * p) ∪ nodeSet L j (2 * p + 1) := by
  ext i
  simp only [mem_nodeSet, Finset.mem_union]
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  omega

lemma nodeSet_zero_of_lt {p : ℕ} (h : p < 2 ^ L) :
    nodeSet L 0 p = {(⟨p, h⟩ : Fin (2 ^ L))} := by
  ext i
  simp only [mem_nodeSet, pow_zero, Nat.div_one, Finset.mem_singleton, Fin.ext_iff]

lemma nodeSet_zero_of_le {p : ℕ} (h : 2 ^ L ≤ p) : nodeSet L 0 p = ∅ := by
  ext i
  simp only [mem_nodeSet, pow_zero, Nat.div_one, Finset.notMem_empty, iff_false]
  have := i.isLt
  omega

/-- A node at height `j` holds at most `2 ^ j` positions: a position under it is
determined by its remainder mod `2 ^ j`. -/
lemma card_nodeSet_le (j p : ℕ) : (nodeSet L j p).card ≤ 2 ^ j := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (fun i => (i : ℕ) % 2 ^ j)
    (fun i _ => Finset.mem_range.2 (Nat.mod_lt _ (Nat.two_pow_pos j)))
    ?_) (le_of_eq (Finset.card_range _))
  intro i hi i' hi' hmod
  rw [Finset.mem_coe, mem_nodeSet] at hi hi'
  dsimp only at hmod
  refine Fin.ext ?_
  have e1 := Nat.div_add_mod (i : ℕ) (2 ^ j)
  have e2 := Nat.div_add_mod (i' : ℕ) (2 ^ j)
  rw [hi] at e1
  rw [hi'] at e2
  omega

/-! ## The product of a node -/

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The tropical product of the letters under the node at height `j` and prefix
`p`, multiplied in position order.  Prefixes that overflow name empty nodes and
get the empty product. -/
noncomputable def nodeProd (letter : σ → TMat k) (L : ℕ) :
    ℕ → ℕ → (Fin (2 ^ L) → σ) → TMat k
  | 0, p, x => if h : p < 2 ^ L then letter (x ⟨p, h⟩) else tone k
  | j + 1, p, x =>
      tmul (nodeProd letter L j (2 * p) x) (nodeProd letter L j (2 * p + 1) x)

lemma nodeProd_zero_of_lt (letter : σ → TMat k) {p : ℕ} (h : p < 2 ^ L)
    (x : Fin (2 ^ L) → σ) :
    nodeProd letter L 0 p x = letter (x ⟨p, h⟩) := dif_pos h

lemma nodeProd_zero_of_le (letter : σ → TMat k) {p : ℕ} (h : ¬ p < 2 ^ L)
    (x : Fin (2 ^ L) → σ) : nodeProd letter L 0 p x = tone k := dif_neg h

lemma nodeProd_succ (letter : σ → TMat k) (j p : ℕ) (x : Fin (2 ^ L) → σ) :
    nodeProd letter L (j + 1) p x
      = tmul (nodeProd letter L j (2 * p) x) (nodeProd letter L j (2 * p + 1) x) :=
  rfl

lemma isUtri_nodeProd {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (j p : ℕ) (x : Fin (2 ^ L) → σ) : IsUtri (nodeProd letter L j p x) := by
  induction j generalizing p with
  | zero =>
      by_cases h : p < 2 ^ L
      · rw [nodeProd_zero_of_lt letter h]
        exact hL _
      · rw [nodeProd_zero_of_le letter h]
        exact isUtri_tone
  | succ j ih => exact (ih (2 * p)).tmul (ih (2 * p + 1))

/-! ## The two kinds of term in the decomposition -/

/-- The best **direct** transition `s → t` among the letters under a node: the
walk that takes a single transition and stands still everywhere else. -/
noncomputable def dirMax (letter : σ → TMat k) (L j p : ℕ) (x : Fin (2 ^ L) → σ)
    (s t : Fin k) : Trop :=
  (nodeSet L j p).sup fun i => letter (x i) s t

lemma dirMax_succ (letter : σ → TMat k) (j p : ℕ) (x : Fin (2 ^ L) → σ)
    (s t : Fin k) :
    dirMax letter L (j + 1) p x s t
      = dirMax letter L j (2 * p) x s t ⊔ dirMax letter L j (2 * p + 1) x s t := by
  rw [dirMax, nodeSet_succ, Finset.sup_union]
  rfl

/-- One **split** candidate: the least common ancestor of the transitions is the
node with prefix `q` whose two children have height `h`, and the walk crosses
from the left child to the right child at state `v`. -/
noncomputable def splitVal (letter : σ → TMat k) (L h q : ℕ)
    (x : Fin (2 ^ L) → σ) (s v t : Fin k) : Trop :=
  nodeProd letter L h (2 * q) x s v + nodeProd letter L h (2 * q + 1) x v t

/-- The internal nodes of the subtree rooted at `(j, p)` whose children have
height `h`, named by their prefixes. -/
def lcaSet (j p h : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ (j - h - 1) * p) (2 ^ (j - h - 1) * (p + 1))

lemma card_lcaSet (j p h : ℕ) : (lcaSet j p h).card = 2 ^ (j - h - 1) := by
  rw [lcaSet, Nat.card_Ico, Nat.mul_succ, Nat.add_sub_cancel_left]

/-- **The level-`h` term**: the best split of the node `(j, p)` whose least
common ancestor has children of height `h`.  The intermediate state `v` must lie
strictly between `s` and `t`, which is what forces both halves of the walk to
have strictly smaller state width. -/
noncomputable def levelVal (letter : σ → TMat k) (L j p h : ℕ)
    (x : Fin (2 ^ L) → σ) (s t : Fin k) : Trop :=
  (lcaSet j p h).sup fun q =>
    (Finset.Ioo s t).sup fun v => splitVal letter L h q x s v t

/-- The level whose least common ancestor is the root of `(j+1, p)` itself. -/
lemma levelVal_top (letter : σ → TMat k) (j p : ℕ) (x : Fin (2 ^ L) → σ)
    (s t : Fin k) :
    levelVal letter L (j + 1) p j x s t
      = (Finset.Ioo s t).sup fun v =>
          nodeProd letter L j (2 * p) x s v + nodeProd letter L j (2 * p + 1) x v t := by
  have hj : j + 1 - j - 1 = 0 := by omega
  have hsingle : Finset.Ico p (p + 1) = {p} := by
    ext q
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [levelVal, lcaSet, hj, pow_zero, one_mul, one_mul, hsingle,
    Finset.sup_singleton]
  rfl

/-- **Every deeper level splits along the two children.**  The internal nodes of
the subtree rooted at `(j+1, p)` whose children have height `h < j` are exactly
those of the two child subtrees. -/
lemma levelVal_succ (letter : σ → TMat k) {j : ℕ} (p : ℕ) {h : ℕ} (hh : h < j)
    (x : Fin (2 ^ L) → σ) (s t : Fin k) :
    levelVal letter L (j + 1) p h x s t
      = levelVal letter L j (2 * p) h x s t ⊔ levelVal letter L j (2 * p + 1) h x s t := by
  have hsplit : lcaSet (j + 1) p h = lcaSet j (2 * p) h ∪ lcaSet j (2 * p + 1) h := by
    have hpow : 2 ^ (j + 1 - h - 1) = 2 ^ (j - h - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [lcaSet, lcaSet, lcaSet, hpow]
    rw [Finset.Ico_union_Ico_eq_Ico (by nlinarith [Nat.zero_le (2 ^ (j - h - 1))])
      (by nlinarith [Nat.zero_le (2 ^ (j - h - 1))])]
    congr 1 <;> ring
  rw [levelVal, levelVal, levelVal, hsplit, Finset.sup_union]

/-! ## The least-common-ancestor decomposition -/

/-- Splitting a supremum over all states at the two states `s < t`, when the
family vanishes outside `[s, t]`. -/
private lemma sup_univ_split {s t : Fin k} (F : Fin k → Trop)
    (hlo : ∀ v, v < s → F v = ⊥) (hhi : ∀ v, t < v → F v = ⊥) :
    Finset.univ.sup F = F s ⊔ F t ⊔ (Finset.Ioo s t).sup F := by
  refine le_antisymm (Finset.sup_le fun v _ => ?_) ?_
  · rcases lt_trichotomy v s with hv | hv | hv
    · rw [hlo v hv]; exact bot_le
    · subst hv; exact le_sup_of_le_left le_sup_left
    · rcases lt_trichotomy v t with hv' | hv' | hv'
      · exact le_sup_of_le_right
          (Finset.le_sup (f := F) (Finset.mem_Ioo.2 ⟨hv, hv'⟩))
      · subst hv'; exact le_sup_of_le_left le_sup_right
      · rw [hhi v hv']; exact bot_le
  · refine sup_le (sup_le ?_ ?_) (Finset.sup_le fun v _ => ?_)
    · exact Finset.le_sup (f := F) (Finset.mem_univ s)
    · exact Finset.le_sup (f := F) (Finset.mem_univ t)
    · exact Finset.le_sup (f := F) (Finset.mem_univ v)

private lemma sup_sup_distrib {α : Type*} (S : Finset α) (F G : α → Trop) :
    (S.sup fun a => F a ⊔ G a) = S.sup F ⊔ S.sup G := by
  refine le_antisymm (Finset.sup_le fun a ha => ?_)
    (sup_le (Finset.sup_le fun a ha => ?_) (Finset.sup_le fun a ha => ?_))
  · exact sup_le (le_sup_of_le_left (Finset.le_sup ha))
      (le_sup_of_le_right (Finset.le_sup ha))
  · exact le_trans le_sup_left (Finset.le_sup (f := fun a => F a ⊔ G a) ha)
  · exact le_trans le_sup_right (Finset.le_sup (f := fun a => F a ⊔ G a) ha)

private lemma range_succ_eq (j : ℕ) :
    Finset.range (j + 1) = insert j (Finset.range j) := by
  ext m
  simp only [Finset.mem_range, Finset.mem_insert]
  omega

/-- **The product of an internal node, with its degenerate terms identified.**

The matrix product ranges over all intermediate states `v`; unitriangularity
kills `v < s` and `t < v`, while `v = s` and `v = t` say that the walk uses only
the right child, respectively only the left child. -/
private lemma nodeProd_succ_apply {letter : σ → TMat k}
    (hL : ∀ a, IsUtri (letter a)) (j p : ℕ) (x : Fin (2 ^ L) → σ) (s t : Fin k) :
    nodeProd letter L (j + 1) p x s t
      = (nodeProd letter L j (2 * p) x s t
            ⊔ nodeProd letter L j (2 * p + 1) x s t)
          ⊔ (Finset.Ioo s t).sup fun v =>
              nodeProd letter L j (2 * p) x s v
                + nodeProd letter L j (2 * p + 1) x v t := by
  have hPL := isUtri_nodeProd hL j (2 * p) x
  have hPR := isUtri_nodeProd hL j (2 * p + 1) x
  rw [nodeProd_succ]
  simp only [tmul]
  rw [sup_univ_split
    (fun v => nodeProd letter L j (2 * p) x s v
      + nodeProd letter L j (2 * p + 1) x v t)
    (fun v hv => by rw [hPL.below s v hv, WithBot.bot_add])
    (fun v hv => by rw [hPR.below v t hv, WithBot.add_bot])]
  rw [hPL.diag s, hPR.diag t]
  simp only [zero_add, add_zero]
  rw [sup_comm (nodeProd letter L j (2 * p + 1) x s t)
    (nodeProd letter L j (2 * p) x s t)]

/-- **The levels of a node are the root split together with the levels of its two
children.** -/
private lemma sup_levelVal_succ (letter : σ → TMat k) (j p : ℕ)
    (x : Fin (2 ^ L) → σ) (s t : Fin k) :
    ((Finset.range (j + 1)).sup fun h => levelVal letter L (j + 1) p h x s t)
      = (((Finset.range j).sup fun h => levelVal letter L j (2 * p) h x s t)
          ⊔ (Finset.range j).sup fun h => levelVal letter L j (2 * p + 1) h x s t)
        ⊔ (Finset.Ioo s t).sup fun v =>
            nodeProd letter L j (2 * p) x s v
              + nodeProd letter L j (2 * p + 1) x v t := by
  rw [range_succ_eq, Finset.sup_insert, levelVal_top letter j p x s t,
    Finset.sup_congr rfl fun h hh =>
      levelVal_succ letter p (Finset.mem_range.1 hh) x s t,
    sup_sup_distrib]
  exact sup_comm _ _

/-- **The least-common-ancestor decomposition.**

A walk from `s` to `t` under the node `(j, p)` either uses a single direct
transition — that is `dirMax` — or uses at least two, and then the least common
ancestor of its transition positions is a genuine internal node of the subtree.
That node's children have some height `h < j`, the walk crosses from the left
child to the right child at some state `v` with `s < v < t`, and its two halves
are walks under the children.  Conversely any such pair of halves concatenates.

The proof is an induction on `j` and uses only `nodeProd_succ` and
unitriangularity: at an internal node the two degenerate terms of the matrix
product, `v = s` and `v = t`, say that the walk stays inside one child, and the
induction hypothesis expands those. -/
theorem nodeProd_eq_dirMax_sup_levels {letter : σ → TMat k}
    (hL : ∀ a, IsUtri (letter a)) (j p : ℕ) (x : Fin (2 ^ L) → σ) {s t : Fin k}
    (hst : s < t) :
    nodeProd letter L j p x s t
      = dirMax letter L j p x s t
          ⊔ (Finset.range j).sup fun h => levelVal letter L j p h x s t := by
  induction j generalizing p with
  | zero =>
      rw [Finset.range_zero, Finset.sup_empty, sup_bot_eq, dirMax]
      by_cases h : p < 2 ^ L
      · rw [nodeProd_zero_of_lt letter h, nodeSet_zero_of_lt h, Finset.sup_singleton]
      · rw [nodeProd_zero_of_le letter h, nodeSet_zero_of_le (by omega),
          Finset.sup_empty, tone, if_neg (ne_of_lt hst)]
  | succ j ih =>
      rw [nodeProd_succ_apply hL j p x s t, ih (2 * p), ih (2 * p + 1),
        dirMax_succ, sup_levelVal_succ letter j p x s t]
      ac_rfl

end MonoidProduct
