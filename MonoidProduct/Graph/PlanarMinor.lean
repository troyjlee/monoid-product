import MonoidProduct.Graph.PlanarContraction
import MonoidProduct.Graph.PlanarIso
set_option linter.style.header false

/-!
# Planarity is closed under minors

* `IsPlanar.of_injective`: if `f : H →g G` is injective and `G` is planar, so is `H`.  The image of
  `H` is a subgraph, on the range of `f`, of the graph induced on the range, which is planar; and
  it is isomorphic to `H`.  Edges of `G` that are not images, and vertices outside the range, are
  dropped this way.
* `IsPlanar.of_minor`: **a minor of a planar graph is planar**, by strong induction on the number
  of vertices of the ambient graph.  If every branch set of the minor model is a single vertex,
  the vertices give an injective homomorphism.  Otherwise some branch set has two vertices, hence
  an edge inside it; contracting that edge keeps planarity (`IsPlanar.contractEdge`), pushes the
  model forward (`MinorModel.contractEdge`), and removes a vertex.

No finiteness is assumed of the vertex type of the minor: disjoint nonempty branch sets in a finite
graph make it finite.
-/

namespace MonoidProduct.Graph

open SimpleGraph

universe u

/-- **Planarity passes to the domain of an injective homomorphism**: the image of `H` is a subgraph
of the graph induced on the range, and is isomorphic to `H`. -/
theorem IsPlanar.of_injective {V W : Type*} [Finite V] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : IsPlanar G) (f : H →g G) (hf : Function.Injective f) : IsPlanar H := by
  let e : W ≃ Set.range f := Equiv.ofInjective f hf
  have hle : H.map e.toEmbedding ≤ G.induce (Set.range f) := by
    intro a b hab
    obtain ⟨u, w, huw, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hab
    exact f.map_adj huw
  exact ((hG.induce (Set.range f)).mono hle).of_iso (SimpleGraph.Iso.map e H).symm

/-- **A minor of a planar graph is planar.**  By strong induction on the number of vertices: with
singleton branch sets the model is an injective homomorphism; otherwise contract an edge inside a
branch set. -/
theorem IsPlanar.of_minor {V : Type u} {W : Type*} [Finite V] {G : SimpleGraph V}
    {H : SimpleGraph W} (hG : IsPlanar G) (hHG : IsMinor H G) : IsPlanar H := by
  classical
  obtain ⟨m⟩ := hHG
  suffices key : ∀ (n : ℕ) (V : Type u) [Finite V] (G : SimpleGraph V), Nat.card V = n →
      IsPlanar G → MinorModel H G → IsPlanar H from key _ V G rfl hG m
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G hn hG m
  by_cases hsing : ∀ w, (m.branch w).Subsingleton
  · -- Every branch set is a single vertex: the vertices give an injective homomorphism.
    choose rep hrep using fun w => (m.connected w).1
    refine hG.of_injective ⟨rep, fun {w w'} h => ?_⟩ fun w w' he => ?_
    · obtain ⟨a, ha, b, hb, hab⟩ := m.adj w w' h
      rwa [hsing w ha (hrep w), hsing w' hb (hrep w')] at hab
    · have he' : rep w = rep w' := he
      by_contra hne
      exact Set.disjoint_left.mp (m.disjoint w w' hne) (hrep w) (he' ▸ hrep w')
  · -- A branch set with two vertices contains an edge; contract it.
    push Not at hsing
    obtain ⟨w₀, hw₀⟩ := hsing
    obtain ⟨u, hu, v, hv, huv⟩ := hw₀
    obtain ⟨x, hx, y, hy, hxy⟩ := (m.connected w₀).exists_adj_of_ne hu hv huv
    have hcard : Nat.card {v // v ≠ y} < n := by
      have := natCard_subtype_ne_add_one y
      omega
    exact ih _ hcard {v // v ≠ y} (Graph.contractEdge G x y) rfl (hG.contractEdge hxy)
      (m.contractEdge hxy hx hy)

end MonoidProduct.Graph
