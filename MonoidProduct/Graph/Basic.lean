import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Sym.Card
set_option linter.style.header false

/-!
# Graphs on a fixed vertex set as sets of possible edges

`monoid.tex`, section `sec:graph-certificates`.  Fix a known labelled vertex set `V`.  Graphs
are simple and undirected, and are identified with their edge sets `G ⊆ binom(V, 2)`.  Every
extension adds edges on the same vertex set, including its isolated vertices.

* `Edge V` is the universe `binom(V, 2)`: the unordered pairs `s(u, w)` of distinct vertices,
  that is, `Sym2 V` without its diagonal.  It has `C(#V, 2)` elements (`card_edge`).
* `toGraph S` is the simple graph on all of `V` whose edges are `S` (`toGraph_adj`,
  `edgeSet_toGraph`).  Vertices on no edge of `S` are isolated vertices of `toGraph S`.
* `ofGraph G` is the edge set of a graph `G` on `V`.  `graphOrderIso` packages `toGraph` and
  `ofGraph` as an order isomorphism `Finset (Edge V) ≃o SimpleGraph V`, so inclusion of edge
  sets is the subgraph order (`toGraph_le_toGraph`).
* The conversion preserves union (`toGraph_union`), deletion (`toGraph_sdiff`,
  `toGraph_sdiff_eq_deleteEdges`) and the number of edges (`ncard_edgeSet_toGraph`).
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V : Type*}

/-- **The possible edges** `binom(V, 2)`: the unordered pairs of distinct vertices. -/
abbrev Edge (V : Type*) : Type _ := {e : Sym2 V // ¬e.IsDiag}

/-- The unordered pairs `s(u, w)` of a set of edges. -/
def pairs (S : Finset (Edge V)) : Finset (Sym2 V) :=
  S.map (Function.Embedding.subtype _)

theorem mem_pairs {S : Finset (Edge V)} {e : Sym2 V} :
    e ∈ pairs S ↔ ∃ h : ¬e.IsDiag, (⟨e, h⟩ : Edge V) ∈ S := by
  simp [pairs]

theorem coe_mem_pairs {S : Finset (Edge V)} {e : Edge V} : (e : Sym2 V) ∈ pairs S ↔ e ∈ S :=
  Finset.mem_map' _

@[simp] theorem card_pairs (S : Finset (Edge V)) : (pairs S).card = S.card :=
  Finset.card_map _

/-- **The graph with edge set `S`**, on all of `V`. -/
def toGraph (S : Finset (Edge V)) : SimpleGraph V :=
  fromEdgeSet (pairs S : Set (Sym2 V))

/-- **Adjacency**: `u` and `w` are adjacent in `toGraph S` exactly when `s(u, w)` is an edge
of `S`. -/
theorem toGraph_adj {S : Finset (Edge V)} {u w : V} :
    (toGraph S).Adj u w ↔ ∃ e ∈ S, (e : Sym2 V) = s(u, w) := by
  rw [toGraph, fromEdgeSet_adj, Finset.mem_coe, pairs, Finset.mem_map]
  constructor
  · rintro ⟨⟨e, he, hew⟩, -⟩
    exact ⟨e, he, hew⟩
  · rintro ⟨e, he, hew⟩
    refine ⟨⟨e, he, hew⟩, fun huw => e.2 ?_⟩
    rw [hew, huw]
    exact Sym2.mk_isDiag_iff.mpr rfl

/-- The edges of `toGraph S` are exactly the pairs of `S`. -/
theorem edgeSet_toGraph (S : Finset (Edge V)) :
    (toGraph S).edgeSet = (pairs S : Set (Sym2 V)) := by
  rw [toGraph, edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
  intro e he hdiag
  exact (mem_pairs.mp (Finset.mem_coe.mp he)).1 (Sym2.mem_diagSet.mp hdiag)

@[simp] theorem coe_mem_edgeSet_toGraph {S : Finset (Edge V)} {e : Edge V} :
    (e : Sym2 V) ∈ (toGraph S).edgeSet ↔ e ∈ S := by
  rw [edgeSet_toGraph, Finset.mem_coe, coe_mem_pairs]

/-- **The number of edges** of `toGraph S` is `#S`. -/
theorem ncard_edgeSet_toGraph (S : Finset (Edge V)) : (toGraph S).edgeSet.ncard = S.card := by
  rw [edgeSet_toGraph, Set.ncard_coe_finset, card_pairs]

theorem toGraph_mono {S T : Finset (Edge V)} (h : S ⊆ T) : toGraph S ≤ toGraph T :=
  fromEdgeSet_mono (Finset.coe_subset.mpr (Finset.map_subset_map.mpr h))

/-- **Inclusion of edge sets is the subgraph order.** -/
@[simp] theorem toGraph_le_toGraph {S T : Finset (Edge V)} : toGraph S ≤ toGraph T ↔ S ⊆ T := by
  refine ⟨fun h e he => ?_, toGraph_mono⟩
  rw [← coe_mem_edgeSet_toGraph] at he ⊢
  exact edgeSet_subset_edgeSet.mpr h he

theorem toGraph_injective : Function.Injective (toGraph (V := V)) := fun _ _ h =>
  (toGraph_le_toGraph.mp h.le).antisymm (toGraph_le_toGraph.mp h.ge)

@[simp] theorem toGraph_empty : toGraph (∅ : Finset (Edge V)) = ⊥ := by
  simp [toGraph, pairs]

theorem toGraph_singleton (e : Edge V) : toGraph {e} = fromEdgeSet {(e : Sym2 V)} := by
  simp [toGraph, pairs]

section DecidableEq

variable [DecidableEq V]

/-- **Union of edge sets is union of graphs.** -/
theorem toGraph_union (S T : Finset (Edge V)) : toGraph (S ∪ T) = toGraph S ⊔ toGraph T := by
  simp only [toGraph, pairs, Finset.map_union, Finset.coe_union, fromEdgeSet_union]

/-- **Deleting a set of edges.** -/
theorem toGraph_sdiff (S T : Finset (Edge V)) : toGraph (S \ T) = toGraph S \ toGraph T := by
  simp only [toGraph, pairs, Finset.map_sdiff, Finset.coe_sdiff, fromEdgeSet_sdiff]

/-- Deleting the edges `T` from `toGraph S`, in Mathlib's `deleteEdges` form. -/
theorem toGraph_sdiff_eq_deleteEdges (S T : Finset (Edge V)) :
    toGraph (S \ T) = (toGraph S).deleteEdges (pairs T : Set (Sym2 V)) := by
  rw [toGraph_sdiff, deleteEdges]
  rfl

/-- Adding one edge. -/
theorem toGraph_insert (e : Edge V) (S : Finset (Edge V)) :
    toGraph (insert e S) = toGraph S ⊔ fromEdgeSet {(e : Sym2 V)} := by
  rw [Finset.insert_eq, toGraph_union, sup_comm, toGraph_singleton]

variable [Fintype V]

/-- **The edge set** of a graph `G` on `V`. -/
noncomputable def ofGraph (G : SimpleGraph V) : Finset (Edge V) := by
  classical exact Finset.univ.filter fun e => (e : Sym2 V) ∈ G.edgeSet

@[simp] theorem mem_ofGraph {G : SimpleGraph V} {e : Edge V} :
    e ∈ ofGraph G ↔ (e : Sym2 V) ∈ G.edgeSet := by
  simp [ofGraph]

@[simp] theorem toGraph_ofGraph (G : SimpleGraph V) : toGraph (ofGraph G) = G := by
  ext u w
  rw [toGraph_adj]
  constructor
  · rintro ⟨e, he, hew⟩
    rw [mem_ofGraph, hew, mem_edgeSet] at he
    exact he
  · intro h
    exact ⟨⟨s(u, w), fun hd => h.ne (Sym2.mk_isDiag_iff.mp hd)⟩,
      mem_ofGraph.mpr (G.mem_edgeSet.mpr h), rfl⟩

@[simp] theorem ofGraph_toGraph (S : Finset (Edge V)) : ofGraph (toGraph S) = S := by
  ext e
  rw [mem_ofGraph, coe_mem_edgeSet_toGraph]

/-- **Graphs on `V` are the sets of possible edges**, as ordered sets. -/
noncomputable def graphOrderIso : Finset (Edge V) ≃o SimpleGraph V where
  toFun := toGraph
  invFun := ofGraph
  left_inv := ofGraph_toGraph
  right_inv := toGraph_ofGraph
  map_rel_iff' := toGraph_le_toGraph

/-- All possible edges form the complete graph. -/
@[simp] theorem toGraph_univ : toGraph (Finset.univ : Finset (Edge V)) = ⊤ := by
  ext u w
  rw [toGraph_adj, top_adj]
  constructor
  · rintro ⟨e, -, hew⟩ huw
    exact e.2 (hew ▸ Sym2.mk_isDiag_iff.mpr huw)
  · intro huw
    exact ⟨⟨s(u, w), fun hd => huw (Sym2.mk_isDiag_iff.mp hd)⟩, Finset.mem_univ _, rfl⟩

/-- **`binom(V, 2)` has `C(#V, 2)` elements.** -/
theorem card_edge : Fintype.card (Edge V) = (Fintype.card V).choose 2 :=
  Sym2.card_subtype_not_diag

end DecidableEq

end MonoidProduct.Graph
