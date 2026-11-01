import MonoidProduct.Graph.WagnerContractible
set_option linter.style.header false

/-!
# Acceptance statements for contractible edges

The statements of `Graph/WagnerContractible.lean`, restated, followed by small sanity checks.
Lean checks every `example` here against the library's statement.

* The contraction away from the merged vertex, including the graph left by deleting it.
* Contracting an edge of a `(k + 1)`-connected graph leaves a `k`-connected graph.
* When contracting an edge keeps `3`-connectivity: no separating triple through the edge.
* Component containment and the strictly smaller component.
* Every `3`-connected graph on at least five vertices has an edge with a `3`-connected
  contraction.

The sanity checks cover:
* `K₅`, which is `3`-connected on five vertices, so that the theorem applies; contracting the edge
  `01` gives a `3`-connected graph;
* the wheel with hub `0` and rim `1, 2, 3, 4`, which is `3`-connected; contracting the rim edge
  `12` keeps `3`-connectivity, while contracting the spoke `01` does not, as `{0, 1, 3}`
  separates the wheel;
* `K₄`, which is `3`-connected, but no contraction of which is, since only three vertices
  remain: the bound of five vertices is needed.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-! ## Statements -/

section Statements

variable {V : Type*} {G : SimpleGraph V}

/-- **Away from the merged vertex, the contraction is `G`**; in particular, deleting the merged
vertex from `contractEdge G x y` leaves the graph `G - {x, y}`. -/
example {x y : V} {s : Set {v // v ≠ y}} {u : Set V}
    (h : ∀ v, v ∈ u ↔ ∃ hv : v ≠ y, (⟨v, hv⟩ : {v // v ≠ y}) ∈ s) (hx : x ∉ u) :
    Nonempty ((contractEdge G x y).induce s ≃g G.induce u) ∧
      Nonempty ((contractEdge G x y).induce {p | p.1 ≠ x} ≃g G.induce {v | v ≠ x ∧ v ≠ y}) :=
  ⟨⟨contractEdgeInduceIso G h hx⟩, ⟨contractEdgeInduceIso G
    (fun _ => ⟨fun h' => ⟨h'.2, h'.1⟩, fun ⟨hvy, hvx⟩ => ⟨hvx, hvy⟩⟩) fun h' => h'.1 rfl⟩⟩

/-- **Contracting keeps connectivity away from the merged vertex.** -/
example {x y : V} (hxy : G.Adj x y) {S : Finset {v // v ≠ y}}
    (hx : (⟨x, hxy.ne⟩ : {v // v ≠ y}) ∉ S)
    (h : (G.induce {v | v ∉ S.map (Function.Embedding.subtype _)}).Connected) :
    ((contractEdge G x y).induce {p | p ∉ S}).Connected :=
  connected_induce_contractEdge hxy hx h

/-- **Contracting an edge of a `(k + 1)`-connected graph leaves a `k`-connected graph**; contracting
any edge of a `3`-connected graph leaves a `2`-connected graph. -/
example [Finite V] {k : ℕ} {x y : V} (hxy : G.Adj x y) :
    (IsKConnected G (k + 1) → IsKConnected (contractEdge G x y) k) ∧
      (IsKConnected G 3 → IsKConnected (contractEdge G x y) 2) :=
  ⟨fun hG => isKConnected_contractEdge hG hxy, fun hG => isKConnected_contractEdge hG hxy⟩

/-- **When contracting `xy` keeps `3`-connectivity**: exactly when no third vertex `z` makes
`{x, y, z}` a separator; so a bad edge lies in a separating triple. -/
example [Finite V] (hG : IsKConnected G 3) {x y : V} (hxy : G.Adj x y) (hV : 5 ≤ Nat.card V) :
    (IsKConnected (contractEdge G x y) 3 ↔
      ∀ z, z ≠ x → z ≠ y → (G.induce {v | v ≠ x ∧ v ≠ y ∧ v ≠ z}).Connected) ∧
    (¬ IsKConnected (contractEdge G x y) 3 →
      ∃ z, z ≠ x ∧ z ≠ y ∧ ¬ (G.induce {v | v ≠ x ∧ v ≠ y ∧ v ≠ z}).Connected) :=
  ⟨isKConnected_contractEdge_three_iff hG hxy hV, exists_separating_triple hG hxy hV⟩

/-- **Component containment**: a component of the graph induced on `s` that lies in `t` and meets
a component of the graph induced on `t` lies inside it. -/
example {s t : Set V} {b c u : V} (hb : b ∈ s)
    (hst : ∀ d, d ∈ s → (restrictTo G s).Reachable b d → d ∈ t) (hus : u ∈ s)
    (hbu : (restrictTo G s).Reachable b u) (hcu : (restrictTo G t).Reachable c u) :
    {d | d ∈ s ∧ (restrictTo G s).Reachable b d} ⊆
      {d | d ∈ t ∧ (restrictTo G t).Reachable c d} :=
  setOf_reachable_subset hb hst hus hbu hcu

/-- **A strictly smaller component**: if `xy` is an edge of a `3`-connected graph, `v` lies in the
component `C` of `c` in `G - {x, y, z}`, and `{z, v, w}` is a separator, then some component of
`G - {z, v, w}` has fewer vertices than `C`. -/
example [Finite V] (hG : IsKConnected G 3) {x y z v w c : V}
    (hxy : G.Adj x y) (hzx : z ≠ x) (hzy : z ≠ y) (hwz : w ≠ z) (hwv : w ≠ v)
    (hv : v ∈ {d | d ∈ {u | u ≠ x ∧ u ≠ y ∧ u ≠ z} ∧
      (restrictTo G {u | u ≠ x ∧ u ≠ y ∧ u ≠ z}).Reachable c d})
    (hS : ¬ (G.induce {u | u ≠ z ∧ u ≠ v ∧ u ≠ w}).Connected) :
    ∃ b, (b ≠ z ∧ b ≠ v ∧ b ≠ w) ∧
      {d | d ∈ {u | u ≠ z ∧ u ≠ v ∧ u ≠ w} ∧
          (restrictTo G {u | u ≠ z ∧ u ≠ v ∧ u ≠ w}).Reachable b d}.ncard <
        {d | d ∈ {u | u ≠ x ∧ u ≠ y ∧ u ≠ z} ∧
          (restrictTo G {u | u ≠ x ∧ u ≠ y ∧ u ≠ z}).Reachable c d}.ncard :=
  exists_ncard_setOf_reachable_lt hG hxy hzx hzy hwz hwv hv hS

/-- **A contractible edge**: every `3`-connected graph on at least five vertices has an edge
whose contraction is `3`-connected. -/
example [Finite V] (hG : IsKConnected G 3) (hV : 5 ≤ Nat.card V) :
    ∃ x y, G.Adj x y ∧ IsKConnected (contractEdge G x y) 3 :=
  exists_contractEdge_isKConnected_three hG hV

end Statements

/-! ## Sanity checks -/

/-- Adjacency in a contraction of a graph with decidable adjacency is decidable. -/
local instance {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} :
    DecidableRel (contractEdge G x y).Adj :=
  fun _ _ => decidable_of_iff _ contractEdge_adj.symm

/-- **`K₅` is `3`-connected on five vertices**, so it has an edge with a `3`-connected
contraction; contracting `01`, which leaves `K₄`, is one. -/
example : IsKConnected (⊤ : SimpleGraph (Fin 5)) 3 ∧
    (∃ x y, (⊤ : SimpleGraph (Fin 5)).Adj x y ∧ IsKConnected (contractEdge ⊤ x y) 3) ∧
    IsKConnected (contractEdge (⊤ : SimpleGraph (Fin 5)) 0 1) 3 := by
  have h3 : IsKConnected (⊤ : SimpleGraph (Fin 5)) 3 :=
    ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩
  refine ⟨h3, exists_contractEdge_isKConnected_three h3
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]), ?_⟩
  exact ⟨by rw [Nat.card_eq_fintype_card]; decide, by decide⟩

/-- The wheel with hub `0` and rim `1, 2, 3, 4`. -/
private abbrev wheelFour : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun a b => a = 0 ∨ (a ≠ 0 ∧ b.val = a.val % 4 + 1)

/-- **The wheel is `3`-connected; contracting the rim edge `12` keeps this, contracting the spoke
`01` does not**: `{0, 1, 3}` separates the wheel, as the rim vertices `2` and `4` are not
adjacent. -/
example : IsKConnected wheelFour 3 ∧ IsKConnected (contractEdge wheelFour 1 2) 3 ∧
    ¬ IsKConnected (contractEdge wheelFour 0 1) 3 := by
  have h3 : IsKConnected wheelFour 3 :=
    ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩
  have h5 : 5 ≤ Nat.card (Fin 5) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨h3, ⟨by rw [Nat.card_eq_fintype_card]; decide, by decide⟩, fun h => ?_⟩
  -- The separating triple `{0, 1, 3}`, through the iff.
  exact (by decide : ¬ (wheelFour.induce {v | v ≠ 0 ∧ v ≠ 1 ∧ v ≠ 3}).Connected)
    ((isKConnected_contractEdge_three_iff h3 (by decide) h5).mp h 3 (by decide) (by decide))

/-- **The rim edge `12` of the wheel lies in no separating triple**, as the iff predicts. -/
example :
    ∀ z : Fin 5, z ≠ 1 → z ≠ 2 → (wheelFour.induce {v | v ≠ 1 ∧ v ≠ 2 ∧ v ≠ z}).Connected := by
  decide

/-- **Five vertices are needed**: `K₄` is `3`-connected, but contracting any of its edges leaves
three vertices, too few for `3`-connectivity. -/
example : IsKConnected (⊤ : SimpleGraph (Fin 4)) 3 ∧
    ∀ x y : Fin 4, ¬ IsKConnected (contractEdge ⊤ x y) 3 := by
  have hcard : ∀ y : Fin 4, Fintype.card {v // v ≠ y} = 3 := by decide
  refine ⟨⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩,
    fun _ y h => ?_⟩
  have h4 := h.1
  rw [Nat.card_eq_fintype_card, hcard y] at h4
  exact absurd h4 (by norm_num)

end MonoidProduct.Graph
