import MonoidProduct.Matroid.Quantum
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.Sigma.Order
set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Minimum spanning forests

This file proves the graphic example of `sec:matroid-bases` in `monoid.tex` (after
`thm:matroid-basis-query`): the graphic matroid of the complete graph on a known vertex set, and
the query bounds for minimum spanning forests.

* **The graphic matroid.**  `graphicMatroid V` is the matroid on the public edge universe
  `Sym2 V` (all unordered pairs, including the self-loops `s(v, v)`) whose independent sets are
  the forests `IsForestEdgeSet`: no self-loop, acyclic.  The augmentation axiom is proved by
  counting connected components (`IsForestEdgeSet.exists_insert`), and the rank is at most
  `#V - 1` (`eRank_graphicMatroid_le`).
* **Bases are spanning forests.**  For weighted edge records `x : ι → Option (Sym2 V × W)`,
  `isParallelBasis_graphicMatroid_iff` identifies the bases of the input restriction (parallel
  copies for repeated edges, nulls for absent edges, loops for self-loops) with the spanning
  forests `IsSpanningForestIndices` of the input graph `inputGraph x T`, which may be
  disconnected.  `basisIndices_isMinimumSpanningForest` proves that the canonical basis is a
  spanning forest with the connectivity of the input graph and minimum total weight.
* **Edge records.**  `minSpanningForest_minWeight_and_qQuery`: with `n` weighted edge records,
  `Q_{1/3} ≤ min{n, 2^18·√(n·(#V - 1))}`, for the positions and for the records.
* **Encoded inputs.**  `encodedBasisReadout_qQuery_le_min_sqrt` extends
  `thm:matroid-basis-query` to inputs whose positions encode records through a public,
  position-dependent map (`encodeRecords`), with one query per position.
* **Adjacency matrix and adjacency arrays.**  `adjacencyMatrix_minSpanningForest`: one query per
  entry of a `V × V` matrix of optional weights, `Q_{1/3} ≤ 2^18·#V·√#V`.
  `adjacencyArray_minSpanningForest`: public degrees `deg`, one query per array entry
  (neighbor and weight), `Q_{1/3} ≤ min{m, 2^18·√(m·(#V - 1))}` with `m = ∑ᵥ deg v`.

The public linear order on `Sym2 V` is arbitrary; `sym2LexLinearOrder` supplies one.
-/

namespace MonoidProduct.Matroid

open Set SimpleGraph

/-! ### Counting connected components of forests -/

section Components

variable {V : Type*}

/-- Reachability after adding the edge `uv`: either the old graph already connects `x` and `y`,
or both are connected to an endpoint of the new edge. -/
lemma reachable_sup_edge_cases {G : SimpleGraph V} {u v x y : V}
    (h : (G ⊔ edge u v).Reachable x y) :
    G.Reachable x y ∨ ((G.Reachable x u ∨ G.Reachable x v) ∧
      (G.Reachable y u ∨ G.Reachable y v)) := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl Reachable.rfl
  | @tail y z _ hyz ih =>
    rw [sup_adj] at hyz
    rcases hyz with hG | hE
    · have hzy : G.Reachable z y := hG.reachable.symm
      rcases ih with h | ⟨hx, hy⟩
      · exact Or.inl (h.trans hG.reachable)
      · exact Or.inr ⟨hx, hy.imp hzy.trans hzy.trans⟩
    · rw [edge_adj] at hE
      obtain ⟨hyz, -⟩ := hE
      have hz : G.Reachable z u ∨ G.Reachable z v := by
        rcases hyz with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact Or.inr Reachable.rfl
        · exact Or.inl Reachable.rfl
      have hy : G.Reachable y u ∨ G.Reachable y v := by
        rcases hyz with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact Or.inl Reachable.rfl
        · exact Or.inr Reachable.rfl
      rcases ih with h | ⟨hx, -⟩
      · exact Or.inr ⟨hy.imp h.trans h.trans, hz⟩
      · exact Or.inr ⟨hx, hz⟩

/-- If every edge of `G` joins vertices connected in `H`, then `G`-reachability implies
`H`-reachability. -/
lemma reachable_of_forall_adj_reachable {G H : SimpleGraph V}
    (h : ∀ a b, G.Adj a b → H.Reachable a b) {x y : V} (hxy : G.Reachable x y) :
    H.Reachable x y := by
  rw [reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact Reachable.rfl
  | tail _ hab ih => exact ih.trans (h _ _ hab)

/-- If `G`-reachability implies `H`-reachability, `H` has at most as many components. -/
lemma natCard_connectedComponent_le_of_reachable [Finite V] {G H : SimpleGraph V}
    (h : ∀ a b, G.Reachable a b → H.Reachable a b) :
    Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent := by
  refine Nat.card_le_card_of_surjective
    (ConnectedComponent.lift (fun v => H.connectedComponentMk v)
      fun a b p _ => ConnectedComponent.sound (h a b ⟨p⟩)) fun c => ?_
  induction c using ConnectedComponent.ind with
  | h v => exact ⟨G.connectedComponentMk v, rfl⟩

/-- The edgeless graph has one component per vertex. -/
lemma natCard_connectedComponent_bot :
    Nat.card (⊥ : SimpleGraph V).ConnectedComponent = Nat.card V := by
  refine (Nat.card_congr (Equiv.ofBijective (⊥ : SimpleGraph V).connectedComponentMk
    ⟨fun a b hab => ?_, fun c => ?_⟩)).symm
  · exact reachable_bot.1 (ConnectedComponent.exact hab)
  · induction c using ConnectedComponent.ind with
    | h v => exact ⟨v, rfl⟩

/-- Adding one edge removes at most one component. -/
lemma natCard_connectedComponent_le_sup_edge_add_one [Finite V] (G : SimpleGraph V)
    (u v : V) :
    Nat.card G.ConnectedComponent ≤ Nat.card (G ⊔ edge u v).ConnectedComponent + 1 := by
  set φ := ConnectedComponent.map (Hom.ofLE (le_sup_left : G ≤ G ⊔ edge u v))
  set c := G.connectedComponentMk v
  have hinj : InjOn φ {a | a ≠ c} := by
    intro a ha b hb hab
    induction a using ConnectedComponent.ind with | h x => ?_
    induction b using ConnectedComponent.ind with | h y => ?_
    have hxv : ¬G.Reachable x v := fun h => ha (ConnectedComponent.sound h)
    have hyv : ¬G.Reachable y v := fun h => hb (ConnectedComponent.sound h)
    have hxy := ConnectedComponent.exact hab
    refine ConnectedComponent.sound ?_
    rcases reachable_sup_edge_cases hxy with h | ⟨hx, hy⟩
    · exact h
    · exact (hx.resolve_right hxv).trans (hy.resolve_right hyv).symm
  have h1 := Set.ncard_le_ncard_of_injOn φ (fun a _ => mem_univ (φ a)) hinj
  have h2 : ({a | a ≠ c} : Set G.ConnectedComponent).ncard + 1 =
      Nat.card G.ConnectedComponent := by
    have : ({a | a ≠ c} : Set G.ConnectedComponent) = univ \ {c} := by ext; simp
    rw [this, Set.ncard_sdiff_singleton_add_one (mem_univ c), Set.ncard_univ]
  rw [Set.ncard_univ] at h1
  omega

/-- Adding an edge between two components removes at least one component. -/
lemma natCard_connectedComponent_sup_edge_add_one_le [Finite V] {G : SimpleGraph V}
    {u v : V} (h : ¬G.Reachable u v) :
    Nat.card (G ⊔ edge u v).ConnectedComponent + 1 ≤ Nat.card G.ConnectedComponent := by
  have huv : u ≠ v := fun e => h (e ▸ Reachable.rfl)
  have := Fintype.ofFinite G.ConnectedComponent
  have := Fintype.ofFinite (G ⊔ edge u v).ConnectedComponent
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.add_one_le_iff]
  refine Fintype.card_lt_of_surjective_not_injective _
    (ConnectedComponent.surjective_map_ofLE (le_sup_left : G ≤ G ⊔ edge u v)) fun hinj => h ?_
  refine ConnectedComponent.exact (hinj ?_)
  refine ConnectedComponent.sound (Adj.reachable ?_)
  rw [sup_adj, edge_adj]
  exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩

lemma fromEdgeSet_insert_mk (S : Set (Sym2 V)) (a b : V) :
    fromEdgeSet (insert s(a, b) S) = fromEdgeSet S ⊔ edge a b := by
  rw [edge, ← fromEdgeSet_union, Set.insert_eq, Set.union_comm]

/-- Every graph on the vertices has at least `#V - #edges` components. -/
lemma natCard_le_card_add_natCard_connectedComponent [Finite V] (S : Finset (Sym2 V)) :
    Nat.card V ≤ S.card + Nat.card (fromEdgeSet (S : Set (Sym2 V))).ConnectedComponent := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fromEdgeSet_empty, natCard_connectedComponent_bot]
  | @insert e S he ih =>
    induction e using Sym2.ind with
    | h a b =>
      rw [Finset.coe_insert, fromEdgeSet_insert_mk, Finset.card_insert_of_notMem he]
      have := natCard_connectedComponent_le_sup_edge_add_one (fromEdgeSet (S : Set (Sym2 V))) a b
      omega

/-- A **forest** with edge set `S` has at most `#V - #S` components. -/
lemma card_add_natCard_connectedComponent_le [Finite V] (S : Finset (Sym2 V))
    (hdiag : ∀ e ∈ S, ¬e.IsDiag) (hS : (fromEdgeSet (S : Set (Sym2 V))).IsAcyclic) :
    S.card + Nat.card (fromEdgeSet (S : Set (Sym2 V))).ConnectedComponent ≤ Nat.card V := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fromEdgeSet_empty, natCard_connectedComponent_bot]
  | @insert e S he ih =>
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := fun h => hdiag _ (Finset.mem_insert_self _ _) (Sym2.mk_isDiag_iff.2 h)
      rw [Finset.coe_insert, fromEdgeSet_insert_mk] at hS ⊢
      rw [Finset.card_insert_of_notMem he]
      obtain ⟨hS', hreach⟩ := isAcyclic_sup_fromEdgeSet_iff.1 hS
      have hnr : ¬(fromEdgeSet (S : Set (Sym2 V))).Reachable a b := by
        intro hr
        rcases hreach hr with h | h
        · exact hab h
        · exact he ((fromEdgeSet_adj _).1 h).1
      have := natCard_connectedComponent_sup_edge_add_one_le hnr
      have := ih (fun e he => hdiag e (Finset.mem_insert_of_mem he)) hS'
      omega

end Components

/-! ### The graphic matroid on the public edge universe -/

section GraphicMatroid

variable {V : Type*}

/-- A set of edges is a **forest**: it contains no self-loop, and the graph it spans is
acyclic. -/
def IsForestEdgeSet (S : Set (Sym2 V)) : Prop :=
  (∀ e ∈ S, ¬e.IsDiag) ∧ (fromEdgeSet S).IsAcyclic

lemma IsForestEdgeSet.anti {S S' : Set (Sym2 V)} (h : IsForestEdgeSet S') (hS : S ⊆ S') :
    IsForestEdgeSet S :=
  ⟨fun e he => h.1 e (hS he), h.2.anti (fromEdgeSet_mono hS)⟩

lemma isForestEdgeSet_empty : IsForestEdgeSet (∅ : Set (Sym2 V)) :=
  ⟨fun _ h => h.elim, by rw [fromEdgeSet_empty]; exact isAcyclic_bot⟩

/-- A forest with edge set `S` has at most `#V - #S` components. -/
lemma IsForestEdgeSet.ncard_add_natCard_le [Finite V] {S : Set (Sym2 V)}
    (h : IsForestEdgeSet S) :
    S.ncard + Nat.card (fromEdgeSet S).ConnectedComponent ≤ Nat.card V := by
  obtain ⟨F, rfl⟩ := (Set.toFinite S).exists_finset_coe
  rw [Set.ncard_coe_finset]
  exact card_add_natCard_connectedComponent_le F h.1 h.2

/-- Every edge set spans a graph with at least `#V - #S` components. -/
lemma natCard_le_ncard_add_natCard [Finite V] (S : Set (Sym2 V)) :
    Nat.card V ≤ S.ncard + Nat.card (fromEdgeSet S).ConnectedComponent := by
  obtain ⟨F, rfl⟩ := (Set.toFinite S).exists_finset_coe
  rw [Set.ncard_coe_finset]
  exact natCard_le_card_add_natCard_connectedComponent F

/-- **Augmentation for forests**: a larger forest has an edge extending a smaller one. -/
lemma IsForestEdgeSet.exists_insert [Finite V] {I J : Set (Sym2 V)} (hI : IsForestEdgeSet I)
    (hJ : IsForestEdgeSet J) (hIJ : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ IsForestEdgeSet (insert e I) := by
  by_contra hcon
  push Not at hcon
  have hadj : ∀ a b, (fromEdgeSet J).Adj a b → (fromEdgeSet I).Reachable a b := by
    intro a b hab
    obtain ⟨habJ, hne⟩ := (fromEdgeSet_adj _).1 hab
    by_cases habI : s(a, b) ∈ I
    · exact ((fromEdgeSet_adj _).2 ⟨habI, hne⟩).reachable
    · by_contra hnr
      refine hcon _ habJ habI ⟨fun e he => ?_, ?_⟩
      · rcases Set.mem_insert_iff.1 he with rfl | he
        · exact fun h => hne (Sym2.mk_isDiag_iff.1 h)
        · exact hI.1 e he
      · rw [fromEdgeSet_insert_mk]
        exact hI.2.sup_edge_of_not_reachable hnr
  have hc := natCard_connectedComponent_le_of_reachable
    (G := fromEdgeSet J) (H := fromEdgeSet I) fun a b h =>
      reachable_of_forall_adj_reachable hadj h
  have h1 := hJ.ncard_add_natCard_le
  have h2 := natCard_le_ncard_add_natCard I
  omega

/-- The independence axioms of the **graphic matroid** of the complete graph (with a self-loop
at each vertex) on `V`: a set of edges is independent exactly when it is a forest. -/
def graphicIndepMatroid (V : Type*) [Finite V] : IndepMatroid (Sym2 V) :=
  IndepMatroid.ofFinite Set.finite_univ IsForestEdgeSet isForestEdgeSet_empty
    (fun _ _ hJ hIJ => hJ.anti hIJ) (fun _ _ hI hJ h => hI.exists_insert hJ h)
    (fun _ _ => subset_univ _)

/-- The **graphic matroid** on the public edge universe `Sym2 V` (`sec:matroid-bases`): the
independent sets are the forests; the self-loops `s(v, v)` are the matroid loops. -/
def graphicMatroid (V : Type*) [Finite V] : _root_.Matroid (Sym2 V) :=
  (graphicIndepMatroid V).matroid

@[simp] lemma graphicMatroid_indep_iff [Finite V] {S : Set (Sym2 V)} :
    (graphicMatroid V).Indep S ↔ IsForestEdgeSet S :=
  Iff.rfl

lemma graphicMatroid_ground [Finite V] : (graphicMatroid V).E = univ :=
  rfl

/-- **The graphic matroid has rank at most `#V - 1`.** -/
theorem eRank_graphicMatroid_le [Finite V] :
    (graphicMatroid V).eRank ≤ ((Nat.card V - 1 : ℕ) : ℕ∞) := by
  obtain ⟨B, hB⟩ := (graphicMatroid V).exists_isBase
  rw [← hB.encard_eq_eRank, ← (Set.toFinite B).cast_ncard_eq, Nat.cast_le]
  have h := (graphicMatroid_indep_iff.1 hB.indep).ncard_add_natCard_le
  rcases isEmpty_or_nonempty V with hV | hV
  · rw [Nat.card_of_isEmpty (α := V)] at h ⊢
    omega
  · obtain ⟨v⟩ := hV
    have : Nonempty (fromEdgeSet B).ConnectedComponent := ⟨connectedComponentMk _ v⟩
    have : 0 < Nat.card (fromEdgeSet B).ConnectedComponent := Nat.card_pos
    omega

end GraphicMatroid

/-! ### Bases of the input records are spanning forests -/

section SpanningForest

variable {ι V W : Type*}

/-- The **input graph** of the positions in `T`: the simple graph on `V` whose edges are the
edges occurring in the input records at those positions (self-loops are dropped). -/
def inputGraph (x : ι → Option (Sym2 V × W)) (T : Finset ι) : SimpleGraph V :=
  fromEdgeSet (inputElements x T)

/-- A set `J` of input positions is a **spanning forest of the input restricted to `T`**:
its records are nonnull, carry distinct edges, and form a forest (no self-loop, acyclic), and
the endpoints of every input edge at a position of `T` are connected within it. -/
def IsSpanningForestIndices (x : ι → Option (Sym2 V × W)) (T J : Finset ι) : Prop :=
  J ⊆ T ∧ (∀ i ∈ J, (x i).isSome) ∧
    (∀ i ∈ J, ∀ j ∈ J, ∀ (e : Sym2 V) (w w' : W), x i = some (e, w) → x j = some (e, w') →
      i = j) ∧
    IsForestEdgeSet (inputElements x J) ∧
    ∀ i ∈ T, ∀ (a b : V) (w : W), x i = some (s(a, b), w) → (inputGraph x J).Reachable a b

lemma inputElements_insert_of_eq_some [DecidableEq ι] {x : ι → Option (Sym2 V × W)}
    {J : Finset ι} {i : ι} {e : Sym2 V} {w : W} (h : x i = some (e, w)) :
    inputElements x (insert i J) = insert e (inputElements x J) := by
  ext f
  constructor
  · rintro ⟨j, hj, w', hx⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · rw [h, Option.some.injEq, Prod.mk.injEq] at hx
      exact Or.inl hx.1.symm
    · exact Or.inr ⟨j, hj, w', hx⟩
  · rintro (rfl | ⟨j, hj, w', hx⟩)
    · exact ⟨i, Finset.mem_insert_self _ _, w, h⟩
    · exact ⟨j, Finset.mem_insert_of_mem hj, w', hx⟩

/-- A spanning forest of the input connects exactly what the input graph connects, and is a
subgraph of it. -/
theorem IsSpanningForestIndices.reachable_eq {x : ι → Option (Sym2 V × W)} {T J : Finset ι}
    (h : IsSpanningForestIndices x T J) :
    inputGraph x J ≤ inputGraph x T ∧ (inputGraph x J).Reachable = (inputGraph x T).Reachable := by
  have hle : inputGraph x J ≤ inputGraph x T := fromEdgeSet_mono (inputElements_mono h.1)
  refine ⟨hle, ?_⟩
  ext a b
  refine ⟨fun hr => hr.mono hle, fun hr => reachable_of_forall_adj_reachable
    (fun c d hcd => ?_) hr⟩
  obtain ⟨hmem, -⟩ := (fromEdgeSet_adj (inputElements x T)).1 hcd
  obtain ⟨i, hi, w, hx⟩ := hmem
  exact h.2.2.2.2 i hi c d w hx

variable [Finite V] [LinearOrder ι] [LinearOrder (Sym2 V)] [LinearOrder W]

omit [LinearOrder (Sym2 V)] [LinearOrder W] in
/-- **Bases of the input records in the graphic matroid are exactly the spanning forests of
the input graph** (`sec:matroid-bases`).  Absent edges are null records, repeated edge records
are parallel copies, and self-loops are matroid loops; the input graph may be disconnected. -/
theorem isParallelBasis_graphicMatroid_iff {x : ι → Option (Sym2 V × W)} {T J : Finset ι} :
    IsParallelBasis (graphicMatroid V) x T J ↔ IsSpanningForestIndices x T J := by
  constructor
  · rintro ⟨hJT, ⟨hs, hd, hind⟩, hmax⟩
    refine ⟨hJT, hs, hd, hind, fun i hi a b w hx => ?_⟩
    by_contra hnr
    have hab : a ≠ b := fun h => hnr (h ▸ Reachable.rfl)
    have key : ∀ l ∈ J, ∀ w₃, x l = some (s(a, b), w₃) → False := fun l hl w₃ hl' =>
      hnr ((fromEdgeSet_adj (inputElements x J)).2 ⟨⟨l, hl, w₃, hl'⟩, hab⟩).reachable
    have hiJ : i ∉ J := fun hiJ => key i hiJ w hx
    have hJ' : IsParallelIndep (graphicMatroid V) x (insert i J) := by
      refine ⟨fun j hj => ?_, fun j hj k hk e w₁ w₂ hxj hxk => ?_, ?_⟩
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · rw [hx]; rfl
        · exact hs j hj
      · by_cases hji : j = i <;> by_cases hki : k = i
        · rw [hji, hki]
        · rw [hji, hx, Option.some.injEq, Prod.mk.injEq] at hxj
          obtain ⟨rfl, -⟩ := hxj
          exact (key k ((Finset.mem_insert.1 hk).resolve_left hki) w₂ hxk).elim
        · rw [hki, hx, Option.some.injEq, Prod.mk.injEq] at hxk
          obtain ⟨rfl, -⟩ := hxk
          exact (key j ((Finset.mem_insert.1 hj).resolve_left hji) w₁ hxj).elim
        · exact hd j ((Finset.mem_insert.1 hj).resolve_left hji) k
            ((Finset.mem_insert.1 hk).resolve_left hki) e w₁ w₂ hxj hxk
      · rw [graphicMatroid_indep_iff, inputElements_insert_of_eq_some hx]
        refine ⟨fun e he => ?_, ?_⟩
        · rcases Set.mem_insert_iff.1 he with rfl | he
          · exact fun h => hab (Sym2.mk_isDiag_iff.1 h)
          · exact hind.1 e he
        · rw [fromEdgeSet_insert_mk]
          exact hind.2.sup_edge_of_not_reachable hnr
    have := hmax _ (Finset.subset_insert _ _) (Finset.insert_subset hi hJT) hJ'
    exact hiJ (this ▸ Finset.mem_insert_self i J)
  · rintro ⟨hJT, hs, hd, hind, hspan⟩
    refine ⟨hJT, ⟨hs, hd, hind⟩, fun J' hJJ' hJ'T hJ' => ?_⟩
    obtain ⟨hs', hd', hind'⟩ := hJ'
    refine Finset.Subset.antisymm (fun i hi => ?_) hJJ'
    by_contra hiJ
    obtain ⟨⟨e, w⟩, hx⟩ := Option.isSome_iff_exists.1 (hs' i hi)
    induction e using Sym2.ind with | h a b => ?_
    have hmem : s(a, b) ∈ inputElements x J' := ⟨i, hi, w, hx⟩
    have hab : a ≠ b := fun h => hind'.1 _ hmem (Sym2.mk_isDiag_iff.2 h)
    have hr := hspan i (hJ'T hi) a b w hx
    have hsub : insert s(a, b) (inputElements x J) ⊆ inputElements x J' :=
      Set.insert_subset hmem (inputElements_mono hJJ')
    have hac := hind'.2.anti (fromEdgeSet_mono hsub)
    rw [fromEdgeSet_insert_mk] at hac
    rcases (isAcyclic_sup_fromEdgeSet_iff.1 hac).2 hr with h | h
    · exact hab h
    · obtain ⟨⟨j, hj, w', hxj⟩, -⟩ := (fromEdgeSet_adj _).1 h
      exact hiJ (hd' i hi j (hJJ' hj) _ w w' hx hxj ▸ hj)

/-- **Minimum spanning forest of weighted edge records** (`sec:matroid-bases`, the graphic
example after `thm:matroid-basis-query`).  For the input `x` of weighted edge records
restricted to the positions `T`:
1. every returned record is a truthful record of `x` at a position of `T`;
2. the returned positions form a spanning forest of the input graph: a subgraph with the same
   connectivity, with distinct edges and no cycle;
3. its total weight is at most that of every spanning forest of the input. -/
theorem basisIndices_isMinimumSpanningForest (weight : W ↪o ℝ)
    (x : ι → Option (Sym2 V × W)) (T : Finset ι) :
    (∀ r ∈ basisRecords (graphicMatroid V) x T,
      r.index ∈ T ∧ x r.index = some (r.element, r.weight)) ∧
    IsSpanningForestIndices x T (basisIndices (graphicMatroid V) x T) ∧
    inputGraph x (basisIndices (graphicMatroid V) x T) ≤ inputGraph x T ∧
    (inputGraph x (basisIndices (graphicMatroid V) x T)).Reachable =
      (inputGraph x T).Reachable ∧
    ∀ J : Finset ι, IsSpanningForestIndices x T J →
      ∑ i ∈ basisIndices (graphicMatroid V) x T, inputWeight weight x i ≤
        ∑ i ∈ J, inputWeight weight x i := by
  obtain ⟨h1, -, h3, h4⟩ := basisRecords_isMinimumWeightBasis graphicMatroid_ground weight x T
  have hsf := isParallelBasis_graphicMatroid_iff.1 h3
  exact ⟨h1, hsf, hsf.reachable_eq.1, hsf.reachable_eq.2,
    fun J hJ => h4 J (isParallelBasis_graphicMatroid_iff.2 hJ)⟩

end SpanningForest

/-! ### A public order on the edge universe -/

/-- A public linear order on the edge universe `Sym2 V`: compare edges by the pair (smaller
endpoint, larger endpoint), lexicographically.  Any other public linear order works equally
well; it only breaks ties between records of equal weight at the same position. -/
@[reducible] def sym2LexLinearOrder (V : Type*) [LinearOrder V] : LinearOrder (Sym2 V) :=
  LinearOrder.lift' (fun e => toLex (e.inf, e.sup)) fun a b h => by
    simp only [toLex_inj, Prod.mk.injEq] at h
    exact Sym2.inf_eq_inf_and_sup_eq_sup.1 h

/-! ### Query complexity with weighted edge records -/

section EdgeRecords

open QuantumQueryComplexity

lemma eRank_graphicMatroid_le_card {V : Type*} [Fintype V] :
    (graphicMatroid V).eRank ≤ ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
  rw [← Nat.card_eq_fintype_card]
  exact eRank_graphicMatroid_le

variable {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder (Sym2 V)]
  [Fintype W] [LinearOrder W]

/-- **Minimum spanning forest from weighted edge records, operational** (`sec:matroid-bases`):
for `x : Fin n → Option (Sym2 V × W)`, computing the positions of the canonical minimum
spanning forest costs `Q_{1/3} ≤ min{n, 2^18·√(n·(#V - 1))}`. -/
theorem minSpanningForestIndices_qQuery_le_min_sqrt (n : ℕ) :
    (qQuery (fun x : Fin n → Option (Sym2 V × W) =>
        basisIndices (graphicMatroid V) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * (Fintype.card V - 1 : ℕ))) := by
  have h := matroidBasisIndices_qQuery_le_min_sqrt (E := Sym2 V) (W := W) 
    (M := graphicMatroid V) graphicMatroid_ground eRank_graphicMatroid_le_card n
  convert h using 3

/-- The same bound for returning the selected weighted edge records. -/
theorem minSpanningForestRecords_qQuery_le_min_sqrt (n : ℕ) :
    (qQuery (fun x : Fin n → Option (Sym2 V × W) =>
        basisRecords (graphicMatroid V) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * (Fintype.card V - 1 : ℕ))) := by
  have h := matroidBasisRecords_qQuery_le_min_sqrt (E := Sym2 V) (W := W) 
    (M := graphicMatroid V) graphicMatroid_ground eRank_graphicMatroid_le_card n
  convert h using 3

/-- **Minimum spanning forests from weighted edge records** (`sec:matroid-bases`, the graphic
example after `thm:matroid-basis-query`).  The public edge universe is `Sym2 V` with any public
linear order; a record is a weighted edge or null.  For every input
`x : Fin n → Option (Sym2 V × W)`:
1. the returned positions form a spanning forest of the input graph (same connectivity, distinct
   edges, no cycle), and its total weight is at most that of every spanning forest;
2. computing the returned positions costs `Q_{1/3} ≤ min{n, 2^18·√(n·(#V - 1))}`;
3. so does computing the returned weighted edge records. -/
theorem minSpanningForest_minWeight_and_qQuery (weight : W ↪o ℝ) (n : ℕ) :
    (∀ x : Fin n → Option (Sym2 V × W),
      IsSpanningForestIndices x Finset.univ (basisIndices (graphicMatroid V) x Finset.univ) ∧
      (inputGraph x (basisIndices (graphicMatroid V) x Finset.univ)).Reachable =
        (inputGraph x Finset.univ).Reachable ∧
      ∀ J : Finset (Fin n), IsSpanningForestIndices x Finset.univ J →
        ∑ i ∈ basisIndices (graphicMatroid V) x Finset.univ, inputWeight weight x i ≤
          ∑ i ∈ J, inputWeight weight x i) ∧
    (qQuery (fun x : Fin n → Option (Sym2 V × W) =>
        basisIndices (graphicMatroid V) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * (Fintype.card V - 1 : ℕ))) ∧
    (qQuery (fun x : Fin n → Option (Sym2 V × W) =>
        basisRecords (graphicMatroid V) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * (Fintype.card V - 1 : ℕ))) := by
  refine ⟨fun x => ?_, minSpanningForestIndices_qQuery_le_min_sqrt n,
    minSpanningForestRecords_qQuery_le_min_sqrt n⟩
  obtain ⟨-, h2, -, h4, h5⟩ := basisIndices_isMinimumSpanningForest weight x Finset.univ
  exact ⟨h2, h4, h5⟩

end EdgeRecords

/-! ### Position-wise encoded inputs -/

section Encoded

open QuantumQueryComplexity

variable {ι A E W O : Type} [Fintype ι] [LinearOrder ι] [Fintype A] [DecidableEq A]
  [Fintype E] [LinearOrder E] [Fintype W] [LinearOrder W] [Fintype O] [DecidableEq O]
  {M : _root_.Matroid E}

/-- A **position-wise encoding** of an input `y : ι → A` into weighted records: position `i`
holding the symbol `a` encodes the record `enc i a`.  The encoding is public and may depend on
the position. -/
def encodeRecords (enc : ι → A → Option (E × W)) (y : ι → A) : ι → Option (E × W) :=
  fun i => enc i (y i)

/-- The canonical basis of an encoded input as an incremental summary over the alphabet `A`:
one query to `y` reveals the encoded record at that position. -/
noncomputable def encodedBasisSummary (hM : M.E = univ) (enc : ι → A → Option (E × W))
    (g : Finset (WeightedRecord ι E W) → O) :
    IncrementalSummary ι A O (Finset (WeightedRecord ι E W)) where
  state y T := basisRecords M (encodeRecords enc y) T
  out y := g (basisRecords M (encodeRecords enc y) Finset.univ)
  state_empty _ _ := by rw [basisRecords_empty, basisRecords_empty]
  state_insert _ _ _ _ _ hT hi :=
    basisRecords_insert_congr hM hT (by simp only [encodeRecords, hi])
  out_congr _ _ h := congrArg g h

/-- The essential positions of an encoded input are exactly its selected positions. -/
theorem encodedBasisSummary_essentialSet_eq (hM : M.E = univ) (enc : ι → A → Option (E × W))
    (g : Finset (WeightedRecord ι E W) → O) (y : ι → A) (T : Finset ι) :
    (encodedBasisSummary hM enc g).essentialSet y T = basisIndices M (encodeRecords enc y) T := by
  ext i
  rw [IncrementalSummary.mem_essentialSet]
  change i ∈ T ∧ basisRecords M (encodeRecords enc y) T ≠
    basisRecords M (encodeRecords enc y) (T.erase i) ↔ _
  rw [ne_comm, Ne, basisRecords_erase_eq_iff hM, not_not]
  exact ⟨And.right, fun h => ⟨basisIndices_subset M _ T h, h⟩⟩

/-- **The query bound for position-wise encoded inputs** (`thm:matroid-basis-query`): if each
position of `y : ι → A` encodes a weighted record through a public map, any readout of the
canonical basis records of the encoded input costs `Q_{1/3} ≤ min{|ι|, 2^18·√(|ι|·r)}`. -/
theorem encodedBasisReadout_qQuery_le_min_sqrt [Nonempty O] (hM : M.E = univ) {r : ℕ}
    (hr : M.eRank ≤ r) (enc : ι → A → Option (E × W))
    (g : Finset (WeightedRecord ι E W) → O) :
    (qQuery (fun y : ι → A => g (basisRecords M (encodeRecords enc y) Finset.univ)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * r)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : qQuery (fun y : ι → A => g (basisRecords M (encodeRecords enc y) Finset.univ))
        (1 / 3) = 0 :=
      qQueryOn_const_eq_zero id
        (c := g (basisRecords M (encodeRecords enc fun i => isEmptyElim i) Finset.univ))
        (fun y => by rw [Subsingleton.elim y fun i => isEmptyElim i]) (by norm_num)
    rw [h0, Fintype.card_eq_zero]
    simp
  · exact summary_qQuery_le_min_sqrt (encodedBasisSummary hM enc g) fun y T => by
      rw [encodedBasisSummary_essentialSet_eq, card_basisIndices]
      exact_mod_cast (card_basisRecords_le_eRank hM _ T).trans hr

end Encoded

/-! ### The adjacency-matrix and adjacency-array models -/

section AdjacencyModels

open QuantumQueryComplexity

variable {V W : Type} [Fintype V] [LinearOrder V] [LinearOrder (Sym2 V)]
  [Fintype W] [LinearOrder W]

/-- The **adjacency-matrix encoding**: the matrix entry at the ordered pair `(u, v)` is either
absent (`none`) or the weight `w` of the edge `uv`, encoded as the record `(s(u, v), w)`.  A
diagonal entry encodes a self-loop; the two entries of an unordered pair are parallel
copies. -/
def adjacencyMatrixRecords (y : V ×ₗ V → Option W) : V ×ₗ V → Option (Sym2 V × W) :=
  encodeRecords (fun p o => o.map fun w => (s((ofLex p).1, (ofLex p).2), w)) y

omit [LinearOrder V] [LinearOrder (Sym2 V)] [Fintype W] [LinearOrder W] in
/-- The edges of the adjacency-matrix encoding are the pairs with a present entry. -/
lemma mem_inputElements_adjacencyMatrixRecords {y : V ×ₗ V → Option W} {e : Sym2 V} :
    e ∈ inputElements (adjacencyMatrixRecords y) Finset.univ ↔
      ∃ u v w, y (toLex (u, v)) = some w ∧ e = s(u, v) := by
  constructor
  · rintro ⟨p, -, w, hp⟩
    simp only [adjacencyMatrixRecords, encodeRecords, Option.map_eq_some_iff, Prod.mk.injEq]
      at hp
    obtain ⟨w', hw', rfl, rfl⟩ := hp
    exact ⟨(ofLex p).1, (ofLex p).2, w', hw', rfl⟩
  · rintro ⟨u, v, w, hw, rfl⟩
    refine ⟨toLex (u, v), Finset.mem_univ _, w, ?_⟩
    simp [adjacencyMatrixRecords, encodeRecords, hw]

/-- **Minimum spanning forest in the adjacency-matrix model** (`sec:matroid-bases`): with one
query per matrix entry, the canonical minimum spanning forest costs
`Q_{1/3} ≤ min{#V², 2^18·√(#V²·(#V - 1))}`. -/
theorem adjacencyMatrix_minSpanningForest_qQuery_le :
    (qQuery (fun y : V ×ₗ V → Option W =>
        basisIndices (graphicMatroid V) (adjacencyMatrixRecords y) Finset.univ) (1 / 3) : ℝ)
      ≤ min ((Fintype.card V : ℝ) ^ 2)
        (2 ^ 18 * Real.sqrt ((Fintype.card V : ℝ) ^ 2 * (Fintype.card V - 1 : ℕ))) := by
  have h := encodedBasisReadout_qQuery_le_min_sqrt (O := Finset (V ×ₗ V))
    graphicMatroid_ground eRank_graphicMatroid_le_card
    (fun p (o : Option W) => o.map fun w => (s((ofLex p).1, (ofLex p).2), w))
    (Finset.image WeightedRecord.index)
  rw [Fintype.card_lex, Fintype.card_prod] at h
  push_cast at h
  rw [sq]
  exact h

/-- The adjacency-matrix bound is `O(#V^{3/2})`. -/
theorem adjacencyMatrix_minSpanningForest_qQuery_le_pow :
    (qQuery (fun y : V ×ₗ V → Option W =>
        basisIndices (graphicMatroid V) (adjacencyMatrixRecords y) Finset.univ) (1 / 3) : ℝ)
      ≤ 2 ^ 18 * ((Fintype.card V : ℝ) * Real.sqrt (Fintype.card V)) := by
  refine adjacencyMatrix_minSpanningForest_qQuery_le.trans ((min_le_right _ _).trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Nat.cast_nonneg _)
  exact_mod_cast Nat.sub_le _ _

/-- **Minimum spanning forest in the adjacency-matrix model** (`sec:matroid-bases`): for every
matrix `y`, the returned entries form a spanning forest of the graph of present entries, of
minimum total weight among all its spanning forests; computing them costs
`Q_{1/3} ≤ min{#V², 2^18·√(#V²·(#V - 1))} ≤ 2^18·#V·√#V`. -/
theorem adjacencyMatrix_minSpanningForest (weight : W ↪o ℝ) :
    (∀ y : V ×ₗ V → Option W,
      IsSpanningForestIndices (adjacencyMatrixRecords y) Finset.univ
        (basisIndices (graphicMatroid V) (adjacencyMatrixRecords y) Finset.univ) ∧
      ∀ J : Finset (V ×ₗ V), IsSpanningForestIndices (adjacencyMatrixRecords y) Finset.univ J →
        ∑ i ∈ basisIndices (graphicMatroid V) (adjacencyMatrixRecords y) Finset.univ,
            inputWeight weight (adjacencyMatrixRecords y) i ≤
          ∑ i ∈ J, inputWeight weight (adjacencyMatrixRecords y) i) ∧
    (qQuery (fun y : V ×ₗ V → Option W =>
        basisIndices (graphicMatroid V) (adjacencyMatrixRecords y) Finset.univ) (1 / 3) : ℝ)
      ≤ 2 ^ 18 * ((Fintype.card V : ℝ) * Real.sqrt (Fintype.card V)) := by
  refine ⟨fun y => ?_, adjacencyMatrix_minSpanningForest_qQuery_le_pow⟩
  obtain ⟨-, h2, -, -, h5⟩ :=
    basisIndices_isMinimumSpanningForest weight (adjacencyMatrixRecords y) Finset.univ
  exact ⟨h2, h5⟩

variable (deg : V → ℕ)

/-- The **adjacency-array encoding** with public degrees `deg`: the array of vertex `v` has
`deg v` entries, and its entry `k` holds a neighbor `u` of `v` together with the weight `w` of
the edge `vu`, encoded as the record `(s(v, u), w)`.  An edge listed in the arrays of both
endpoints gives two parallel copies. -/
def adjacencyArrayRecords (y : (Σₗ v : V, Fin (deg v)) → V × W) :
    (Σₗ v : V, Fin (deg v)) → Option (Sym2 V × W) :=
  encodeRecords (fun p q => some (s((ofLex p).1, q.1), q.2)) y

omit [LinearOrder V] [LinearOrder (Sym2 V)] [Fintype W] [LinearOrder W] in
/-- The edges of the adjacency-array encoding are the listed vertex–neighbor pairs. -/
lemma mem_inputElements_adjacencyArrayRecords {y : (Σₗ v : V, Fin (deg v)) → V × W}
    {e : Sym2 V} :
    e ∈ inputElements (adjacencyArrayRecords deg y) Finset.univ ↔
      ∃ (v : V) (k : Fin (deg v)), e = s(v, (y (toLex ⟨v, k⟩)).1) := by
  constructor
  · rintro ⟨p, -, w, hp⟩
    simp only [adjacencyArrayRecords, encodeRecords, Option.some.injEq, Prod.mk.injEq] at hp
    exact ⟨(ofLex p).1, (ofLex p).2, hp.1.symm⟩
  · rintro ⟨v, k, rfl⟩
    exact ⟨toLex ⟨v, k⟩, Finset.mem_univ _, (y (toLex ⟨v, k⟩)).2, rfl⟩

/-- **Minimum spanning forest in the adjacency-array model with public degrees**
(`sec:matroid-bases`): with one query per array entry, the canonical minimum spanning forest
costs `Q_{1/3} ≤ min{m, 2^18·√(m·(#V - 1))}`, where `m = ∑ᵥ deg v` is the total array length
(twice the number of edges of a simple graph). -/
theorem adjacencyArray_minSpanningForest_qQuery_le :
    (qQuery (fun y : (Σₗ v : V, Fin (deg v)) → V × W =>
        basisIndices (graphicMatroid V) (adjacencyArrayRecords deg y) Finset.univ) (1 / 3) : ℝ)
      ≤ min ((∑ v, deg v : ℕ) : ℝ)
        (2 ^ 18 * Real.sqrt (((∑ v, deg v : ℕ) : ℝ) * (Fintype.card V - 1 : ℕ))) := by
  have h := encodedBasisReadout_qQuery_le_min_sqrt (O := Finset (Σₗ v : V, Fin (deg v)))
    graphicMatroid_ground eRank_graphicMatroid_le_card
    (fun p (q : V × W) => some (s((ofLex p).1, q.1), q.2))
    (Finset.image WeightedRecord.index)
  rw [Fintype.card_lex, Fintype.card_sigma] at h
  simp only [Fintype.card_fin] at h
  exact h

/-- **Minimum spanning forest in the adjacency-array model with public degrees**
(`sec:matroid-bases`): for every array content `y`, the returned entries form a spanning forest
of the listed graph, of minimum total weight among all its spanning forests; computing them
costs `Q_{1/3} ≤ min{m, 2^18·√(m·(#V - 1))}` with `m = ∑ᵥ deg v`. -/
theorem adjacencyArray_minSpanningForest (weight : W ↪o ℝ) :
    (∀ y : (Σₗ v : V, Fin (deg v)) → V × W,
      IsSpanningForestIndices (adjacencyArrayRecords deg y) Finset.univ
        (basisIndices (graphicMatroid V) (adjacencyArrayRecords deg y) Finset.univ) ∧
      ∀ J : Finset (Σₗ v : V, Fin (deg v)),
        IsSpanningForestIndices (adjacencyArrayRecords deg y) Finset.univ J →
        ∑ i ∈ basisIndices (graphicMatroid V) (adjacencyArrayRecords deg y) Finset.univ,
            inputWeight weight (adjacencyArrayRecords deg y) i ≤
          ∑ i ∈ J, inputWeight weight (adjacencyArrayRecords deg y) i) ∧
    (qQuery (fun y : (Σₗ v : V, Fin (deg v)) → V × W =>
        basisIndices (graphicMatroid V) (adjacencyArrayRecords deg y) Finset.univ) (1 / 3) : ℝ)
      ≤ min ((∑ v, deg v : ℕ) : ℝ)
        (2 ^ 18 * Real.sqrt (((∑ v, deg v : ℕ) : ℝ) * (Fintype.card V - 1 : ℕ))) := by
  refine ⟨fun y => ?_, adjacencyArray_minSpanningForest_qQuery_le deg⟩
  obtain ⟨-, h2, -, -, h5⟩ :=
    basisIndices_isMinimumSpanningForest weight (adjacencyArrayRecords deg y) Finset.univ
  exact ⟨h2, h5⟩

end AdjacencyModels

/-! ### Examples -/

section Examples

open QuantumQueryComplexity

/-- A self-loop record is never selected. -/
example {ι V W : Type*} [Finite V] [LinearOrder ι] [LinearOrder (Sym2 V)] [LinearOrder W]
    (x : ι → Option (Sym2 V × W)) (T : Finset ι) {i : ι} {v : V} {w : W}
    (hx : x i = some (s(v, v), w)) : i ∉ basisIndices (graphicMatroid V) x T := by
  intro hi
  have hsf := isParallelBasis_graphicMatroid_iff.1
    (isParallelBasis_basisIndices graphicMatroid_ground x T)
  exact hsf.2.2.2.1.1 _ ⟨i, hi, w, hx⟩ (Sym2.mk_isDiag_iff.2 rfl)

/-- The edge-record bound on the vertex set `Fin k`, with the sorted-endpoint order on edges. -/
example (k n : ℕ) :
    letI := sym2LexLinearOrder (Fin k)
    (qQuery (fun x : Fin n → Option (Sym2 (Fin k) × Fin 3) =>
        basisIndices (graphicMatroid (Fin k)) x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * (k - 1 : ℕ))) := by
  let _ := sym2LexLinearOrder (Fin k)
  simpa using minSpanningForestIndices_qQuery_le_min_sqrt (V := Fin k) (W := Fin 3) n

end Examples

end MonoidProduct.Matroid
