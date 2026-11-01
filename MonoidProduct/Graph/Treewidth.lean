import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Linarith
set_option linter.style.header false

/-!
# Bounded treewidth

`monoid.tex`, section `sec:graph-certificates`, paragraph "Planarity and minor-closed
properties", which lists treewidth at most a fixed constant among the proper minor-closed
classes.  Mathlib has no tree decompositions.

* `TreeDecomposition G` (Diestel, *Graph Theory*, Section 12.3): a finite tree `T` with a bag
  `X i` of vertices at every node, covering every vertex and every edge of `G`, such that
  `X i ∩ X k ⊆ X j` whenever `j` lies on the `i`–`k` path of `T`.
* `TreewidthLE t G`: `G` has a tree decomposition whose bags have at most `t + 1` vertices.
* `TreewidthLE.ncard_edgeSet_le`: such a graph has at most `t·v` edges.  The proof is by
  induction on the number of nodes and the total bag size
  (`ncard_edgeSet_le_of_decomposition`).  Take a leaf `ℓ` of `T`, with neighbour `p`.  If
  `X ℓ ⊆ X p`, deleting `ℓ` leaves a decomposition of the same graph.  Otherwise some vertex `u`
  of `X ℓ` lies in no other bag, since every other node is reached from `ℓ` through `p`.  Then
  all neighbours of `u` lie in `X ℓ`, so `u` has at most `t` of them, and deleting `u` from the
  graph and from every bag leaves a decomposition.
* Examples: `K_(t+1)` has treewidth at most `t`, with a single bag; the path `0 − 1 − 2` has
  treewidth at most `1`, with the bags `{0, 1}` and `{1, 2}`.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V : Type*}

/-- **A tree decomposition** of `G` (Diestel, *Graph Theory*, Section 12.3): a tree on a finite
type of nodes, with a bag of vertices at each node, such that every vertex and every edge lies in
a bag, and the bags at the ends of a path of the tree share their vertices with every bag on the
path. -/
structure TreeDecomposition (G : SimpleGraph V) where
  /-- The nodes of the tree. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The tree. -/
  tree : SimpleGraph ι
  isTree : tree.IsTree
  /-- The bag at a node. -/
  bag : ι → Finset V
  cover_vertex : ∀ v, ∃ i, v ∈ bag i
  cover_edge : ∀ u w, G.Adj u w → ∃ i, u ∈ bag i ∧ w ∈ bag i
  mem_of_mem_path : ∀ (i j k : ι) (p : tree.Walk i k), p.IsPath → j ∈ p.support →
    ∀ v, v ∈ bag i → v ∈ bag k → v ∈ bag j

/-- **Treewidth at most `t`**: a tree decomposition with bags of at most `t + 1` vertices. -/
def TreewidthLE (t : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ t + 1

section Bound

variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The edges inside a set of `s ≤ t + 1` vertices number at most `t·s`. -/
private theorem ncard_le_of_subset_bag {G : SimpleGraph V} {B : Finset V} {t : ℕ}
    (hB : B.card ≤ t + 1) (h : ∀ u w, G.Adj u w → u ∈ B ∧ w ∈ B) :
    G.edgeSet.ncard ≤ t * B.card := by
  classical
  have hsub : G.edgeSet ⊆ ↑(B.offDiag.image (Function.uncurry Sym2.mk)) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
    obtain ⟨ha, hb⟩ := h a b he
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, G.ne_of_adj he⟩, rfl⟩)
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Sym2.card_image_offDiag, Nat.choose_two_right] at h1
  refine h1.trans (Nat.div_le_of_le_mul ?_)
  calc B.card * (B.card - 1) ≤ B.card * t := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 2 * (t * B.card) := by nlinarith

omit [Fintype V] in
/-- **The edge bound for tree decompositions**, by induction on the number of nodes plus the
total bag size: a graph whose edges are covered by the bags of a tree decomposition with bags of
at most `t + 1` vertices has at most `t·|⋃ bags|` edges. -/
theorem ncard_edgeSet_le_of_decomposition [Finite V] (t : ℕ) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] (T : SimpleGraph ι) (X : ι → Finset V)
      (G : SimpleGraph V), T.IsTree →
      (∀ u w, G.Adj u w → ∃ i, u ∈ X i ∧ w ∈ X i) →
      (∀ (i j k : ι) (p : T.Walk i k), p.IsPath → j ∈ p.support →
        ∀ v, v ∈ X i → v ∈ X k → v ∈ X j) →
      (∀ i, (X i).card ≤ t + 1) → Fintype.card ι + ∑ i, (X i).card = n →
      G.edgeSet.ncard ≤ t * (Finset.univ.biUnion X).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ T X G hT hcov hpath hwidth hn
  classical
  have := Fintype.ofFinite V
  rcases subsingleton_or_nontrivial ι with hsub | hnt
  · -- One node: every edge lies in its bag.
    obtain ⟨i₀⟩ := hT.connected.nonempty
    have hU : Finset.univ.biUnion X = X i₀ := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => Subsingleton.elim i i₀ ▸ hi, fun h => ⟨i₀, h⟩⟩
    rw [hU]
    refine ncard_le_of_subset_bag (hwidth i₀) fun u w h => ?_
    obtain ⟨i, hu, hw⟩ := hcov u w h
    rw [Subsingleton.elim i i₀] at hu hw
    exact ⟨hu, hw⟩
  · -- A leaf `ℓ` with its neighbour `p`.
    obtain ⟨ℓ, hℓ⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨p, hℓp, hp⟩ := degree_eq_one_iff_existsUnique_adj.mp hℓ
    have hpℓ : p ≠ ℓ := (T.ne_of_adj hℓp).symm
    -- Every path from `ℓ` to another node passes through `p`.
    have hthrough : ∀ i, i ≠ ℓ → ∃ q : T.Walk ℓ i, q.IsPath ∧ p ∈ q.support := by
      intro i hi
      obtain ⟨q, hq⟩ := (hT.connected.preconnected ℓ i).some.toPath
      cases q with
      | nil => exact absurd rfl hi
      | cons h q' =>
        have hv := hp _ h
        refine ⟨.cons h q', hq, ?_⟩
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ (hv ▸ q'.start_mem_support)
    by_cases hsub : X ℓ ⊆ X p
    · -- The leaf's bag is redundant: delete the leaf.
      let ι' := ↥({ℓ}ᶜ : Set ι)
      have hT' : (T.induce ({ℓ}ᶜ : Set ι)).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hℓ, hT.isAcyclic.induce _⟩
      have hcov' : ∀ u w, G.Adj u w → ∃ i : ι', u ∈ X i.1 ∧ w ∈ X i.1 := by
        intro u w h
        obtain ⟨i, hu, hw⟩ := hcov u w h
        by_cases hi : i = ℓ
        · subst hi
          exact ⟨⟨p, hpℓ⟩, hsub hu, hsub hw⟩
        · exact ⟨⟨i, hi⟩, hu, hw⟩
      have hpath' : ∀ (i j k : ι') (q : (T.induce ({ℓ}ᶜ : Set ι)).Walk i k), q.IsPath →
          j ∈ q.support → ∀ v, v ∈ X i.1 → v ∈ X k.1 → v ∈ X j.1 := by
        intro i j k q hq hj v hi hk
        let f := (Embedding.induce (G := T) ({ℓ}ᶜ : Set ι)).toHom
        have hq' : ((q.map f).copy (rfl : f i = i.1) (rfl : f k = k.1)).IsPath := by
          rw [Walk.isPath_copy]
          exact hq.map Subtype.val_injective
        have hj' : j.1 ∈ ((q.map f).copy (rfl : f i = i.1) (rfl : f k = k.1)).support := by
          rw [Walk.support_copy, Walk.support_map]
          exact List.mem_map_of_mem hj
        exact hpath i.1 j.1 k.1 _ hq' hj' v hi hk
      have hcard : Fintype.card ι' = Fintype.card ι - 1 := by
        change Fintype.card ↥({ℓ}ᶜ : Set ι) = _
        rw [Fintype.card_compl_set, Set.card_singleton]
      have hsum : ∑ i : ι', (X i.1).card ≤ ∑ i, (X i).card := by
        rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ ({ℓ}ᶜ : Set ι)))
          (fun i => by simp) (fun i => (X i).card)]
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have hpos : 0 < Fintype.card ι := Fintype.card_pos
      have hU : (Finset.univ.biUnion fun i : ι' => X i.1) = Finset.univ.biUnion X := by
        ext v
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨i.1, hi⟩
        · rintro ⟨i, hi⟩
          by_cases hiℓ : i = ℓ
          · subst hiℓ
            exact ⟨⟨p, hpℓ⟩, hsub hi⟩
          · exact ⟨⟨i, hiℓ⟩, hi⟩
      rw [← hU]
      exact ih _ (by omega) ι' (T.induce ({ℓ}ᶜ : Set ι)) (fun i => X i.1) G hT' hcov' hpath'
        (fun i => hwidth i.1) rfl
    · -- A vertex `u` private to the leaf's bag.
      obtain ⟨u, huℓ, hup⟩ := Finset.not_subset.mp hsub
      have honly : ∀ i, u ∈ X i → i = ℓ := by
        intro i hi
        by_contra hiℓ
        obtain ⟨q, hq, hpq⟩ := hthrough i hiℓ
        exact hup (hpath ℓ p i q hq hpq u huℓ hi)
      -- All neighbours of `u` lie in the leaf's bag.
      have hnbr : G.neighborSet u ⊆ ↑((X ℓ).erase u) := by
        intro w hw
        obtain ⟨i, hu, hw'⟩ := hcov u w hw
        rw [honly i hu] at hw'
        exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨(G.ne_of_adj hw).symm, hw'⟩)
      have hdeg : G.degree u ≤ t := by
        rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        have := Set.ncard_le_ncard hnbr (Finset.finite_toSet _)
        rw [Set.ncard_coe_finset, Finset.card_erase_of_mem huℓ] at this
        have := hwidth ℓ
        omega
      -- Delete `u` from the graph and from every bag.
      let X'' : ι → Finset V := fun i => (X i).erase u
      have hcov'' : ∀ a b, (G.deleteIncidenceSet u).Adj a b → ∃ i, a ∈ X'' i ∧ b ∈ X'' i := by
        intro a b h
        obtain ⟨hab, hau, hbu⟩ := deleteIncidenceSet_adj.mp h
        obtain ⟨i, ha, hb⟩ := hcov a b hab
        exact ⟨i, Finset.mem_erase.mpr ⟨hau, ha⟩, Finset.mem_erase.mpr ⟨hbu, hb⟩⟩
      have hpath'' : ∀ (i j k : ι) (q : T.Walk i k), q.IsPath → j ∈ q.support →
          ∀ v, v ∈ X'' i → v ∈ X'' k → v ∈ X'' j := by
        intro i j k q hq hj v hi hk
        obtain ⟨hvu, hi⟩ := Finset.mem_erase.mp hi
        exact Finset.mem_erase.mpr ⟨hvu, hpath i j k q hq hj v hi (Finset.mem_erase.mp hk).2⟩
      have hsum : ∑ i, (X'' i).card < ∑ i, (X i).card :=
        Finset.sum_lt_sum (fun i _ => Finset.card_erase_le) ⟨ℓ, Finset.mem_univ _,
          Finset.card_erase_lt_of_mem huℓ⟩
      have hU : Finset.univ.biUnion X'' = (Finset.univ.biUnion X).erase u := by
        ext v
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_erase, X'']
        exact ⟨fun ⟨i, hvu, hi⟩ => ⟨hvu, i, hi⟩, fun ⟨hvu, i, hi⟩ => ⟨i, hvu, hi⟩⟩
      have huU : u ∈ Finset.univ.biUnion X :=
        Finset.mem_biUnion.mpr ⟨ℓ, Finset.mem_univ _, huℓ⟩
      have hrec := ih _ (by omega) ι T X'' (G.deleteIncidenceSet u) hT hcov'' hpath''
        (fun i => (Finset.card_erase_le).trans (hwidth i)) rfl
      rw [hU, Finset.card_erase_of_mem huU] at hrec
      -- `|E(G)| = |E(G − u)| + deg u`.
      have hE : G.edgeSet.ncard = (G.deleteIncidenceSet u).edgeSet.ncard + G.degree u := by
        rw [← coe_edgeFinset, ← coe_edgeFinset, Set.ncard_coe_finset, Set.ncard_coe_finset,
          card_edgeFinset_deleteIncidenceSet]
        have : G.degree u ≤ G.edgeFinset.card := by
          rw [← card_incidenceFinset_eq_degree]
          exact Finset.card_le_card (G.incidenceFinset_subset u)
        omega
      have hUpos : 0 < (Finset.univ.biUnion X).card := Finset.card_pos.mpr ⟨u, huU⟩
      rw [hE]
      calc (G.deleteIncidenceSet u).edgeSet.ncard + G.degree u
          ≤ t * ((Finset.univ.biUnion X).card - 1) + t := by omega
        _ = t * (Finset.univ.biUnion X).card := by
          rw [← mul_add_one]
          congr 1
          omega

omit [DecidableEq V] in
/-- **Graphs of treewidth at most `t` have at most `t·v` edges.** -/
theorem TreewidthLE.ncard_edgeSet_le {t : ℕ} {G : SimpleGraph V} (h : TreewidthLE t G) :
    G.edgeSet.ncard ≤ t * Fintype.card V := by
  classical
  obtain ⟨D, hD⟩ := h
  have := D.fintype
  refine (ncard_edgeSet_le_of_decomposition t _ D.ι D.tree D.bag G D.isTree D.cover_edge
    D.mem_of_mem_path hD rfl).trans (Nat.mul_le_mul_left _ ?_)
  exact Finset.card_le_univ _

end Bound

/-! ## Examples -/

/-- **`K_(t+1)` has treewidth at most `t`**, with a single bag. -/
theorem treewidthLE_top (t : ℕ) : TreewidthLE t (⊤ : SimpleGraph (Fin (t + 1))) :=
  ⟨{ ι := Unit
     tree := ⊥
     isTree := IsTree.of_subsingleton
     bag := fun _ => Finset.univ
     cover_vertex := fun _ => ⟨(), Finset.mem_univ _⟩
     cover_edge := fun _ _ _ => ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩
     mem_of_mem_path := fun _ _ _ _ _ _ _ _ _ => Finset.mem_univ _ },
    fun _ => by simp⟩

/-- The path `0 − 1 − 2`. -/
def path3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun a b => b = a + 1 ∧ a ≠ 2

/-- **The path `0 − 1 − 2` has treewidth at most `1`**, with the bags `{0, 1}` and `{1, 2}` on
the tree with two nodes. -/
theorem treewidthLE_one_path3 : TreewidthLE 1 path3 := by
  have hT : (⊤ : SimpleGraph (Fin 2)).IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨(connected_top), ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [← Set.toFinset_card, ← edgeFinset, card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
    rfl
  refine ⟨{ ι := Fin 2
            tree := ⊤
            isTree := hT
            bag := ![{0, 1}, {1, 2}]
            cover_vertex := ?_
            cover_edge := ?_
            mem_of_mem_path := ?_ }, ?_⟩
  · decide
  · intro u w h
    simp only [path3, fromRel_adj] at h
    revert u w
    decide
  · intro i j k q hq hj v hi hk
    by_cases hji : j = i
    · rwa [hji]
    by_cases hjk : j = k
    · rwa [hjk]
    -- Two nodes: `i = k`, and a path from a node to itself is trivial.
    have hik : i = k := by omega
    subst hik
    cases q with
    | nil => exact absurd (List.mem_singleton.mp hj) hji
    | cons h q' =>
      exact absurd q'.end_mem_support ((Walk.cons_isPath_iff h q').mp hq).2
  · intro i
    change (![({0, 1} : Finset (Fin 3)), {1, 2}] i).card ≤ 1 + 1
    fin_cases i <;> decide

end MonoidProduct.Graph
