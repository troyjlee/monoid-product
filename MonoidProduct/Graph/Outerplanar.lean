import Mathlib.Logic.Equiv.Fin.Basic
import MonoidProduct.Graph.PlanarExamples
import MonoidProduct.Graph.PlanarIso
set_option linter.style.header false

/-!
# Outerplanar graphs

`monoid.tex`, section `sec:graph-certificates`, paragraph "Planarity and minor-closed
properties", which lists outerplanarity among the proper minor-closed classes.

A graph is outerplanar when it has a planar drawing with every vertex on the outer face.
Chartrand and Harary showed that this holds exactly when adding one new vertex adjacent to every
vertex gives a planar graph; that characterization is the definition here.

* `apex G`: `G` on `Option V` with a new vertex `none` adjacent to every vertex
  (`apex_adj`); it has `|E(G)| + v` edges (`ncard_edgeSet_apex`).
* `IsOuterplanar G`: `apex G` is planar (`IsPlanar`, `Graph/Planar.lean`).
* `IsOuterplanar.ncard_edgeSet_le`: an outerplanar graph on `v ≥ 2` vertices has at most
  `2v - 3` edges, from the planar bound `3(v + 1) - 6` for `apex G`.
* `not_isOuterplanar_top_four`: `K₄` is not outerplanar, since `6 > 2·4 − 3`.
* `isOuterplanar_top_three`: the triangle is outerplanar, since its apex graph is `K₄`
  (`IsPlanar.of_iso`); with `3 = 2·3 − 3` edges it attains the bound.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V : Type*}

/-- **The apex graph**: `G` on `Option V`, with a new vertex `none` adjacent to every vertex of
`G`. -/
def apex (G : SimpleGraph V) : SimpleGraph (Option V) :=
  SimpleGraph.fromRel fun a b => match a, b with
    | none, some _ => True
    | some u, some w => G.Adj u w
    | _, _ => False

@[simp] theorem apex_adj_none_some (G : SimpleGraph V) (v : V) : (apex G).Adj none (some v) := by
  simp [apex]

@[simp] theorem apex_adj_some_some {G : SimpleGraph V} {u w : V} :
    (apex G).Adj (some u) (some w) ↔ G.Adj u w := by
  simp only [apex, fromRel_adj, ne_eq, Option.some.injEq]
  exact ⟨fun h => h.2.elim id fun h' => h'.symm, fun h => ⟨h.ne, Or.inl h⟩⟩

@[simp] theorem apex_adj_some_none (G : SimpleGraph V) (v : V) : (apex G).Adj (some v) none :=
  (apex_adj_none_some G v).symm

@[simp] theorem apex_not_adj_none_none (G : SimpleGraph V) : ¬(apex G).Adj none none :=
  (apex G).irrefl

/-- The edges of `apex G`: those of `G`, and one from the apex to every vertex. -/
theorem edgeSet_apex (G : SimpleGraph V) :
    (apex G).edgeSet = Sym2.map some '' G.edgeSet ∪ Set.range fun v => s(none, some v) := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
  rw [mem_edgeSet]
  constructor
  · intro h
    rcases a with _ | a <;> rcases b with _ | b
    · exact absurd h (apex_not_adj_none_none G)
    · exact Or.inr ⟨b, rfl⟩
    · exact Or.inr ⟨a, Sym2.eq_swap⟩
    · exact Or.inl ⟨s(a, b), G.mem_edgeSet.mpr (apex_adj_some_some.mp h), rfl⟩
  · rintro (⟨e, he, hab⟩ | ⟨v, hv⟩)
    · induction e using Sym2.ind with
      | h u w =>
      rw [Sym2.map_mk] at hab
      rw [← mem_edgeSet, ← hab, mem_edgeSet, apex_adj_some_some]
      exact he
    · rw [← mem_edgeSet, ← hv, mem_edgeSet]
      exact apex_adj_none_some G v

/-- **`apex G` has `|E(G)| + v` edges.** -/
theorem ncard_edgeSet_apex [Finite V] (G : SimpleGraph V) :
    (apex G).edgeSet.ncard = G.edgeSet.ncard + Nat.card V := by
  have := Fintype.ofFinite V
  have hinj : Function.Injective (Sym2.map (some : V → Option V)) :=
    Sym2.map.injective (Option.some_injective V)
  have hdisj : Disjoint (Sym2.map some '' G.edgeSet) (Set.range fun v : V => s(none, some v)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨e, -, rfl⟩ ⟨v, hv⟩
    induction e using Sym2.ind with
    | h a b =>
    rw [Sym2.map_mk] at hv
    rcases Sym2.eq_iff.mp hv with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by simp)
  rw [edgeSet_apex, Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ hinj,
    Set.ncard_range_of_injective fun v w h => Option.some_injective V (Sym2.congr_right.mp h)]

/-- **Outerplanarity**: adding a vertex adjacent to every vertex gives a planar graph; by
Chartrand and Harary, this is a planar drawing with every vertex on the outer face. -/
def IsOuterplanar (G : SimpleGraph V) : Prop := IsPlanar (apex G)

/-- **Outerplanar graphs on `v ≥ 2` vertices have at most `2v - 3` edges.** -/
theorem IsOuterplanar.ncard_edgeSet_le [Fintype V] {G : SimpleGraph V} (h : IsOuterplanar G)
    (hv : 2 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 2 * Fintype.card V - 3 := by
  have hb := IsPlanar.ncard_edgeSet_le h (by rw [Fintype.card_option]; omega)
  rw [ncard_edgeSet_apex, Fintype.card_option, Nat.card_eq_fintype_card] at hb
  omega

/-- **`K₄` is not outerplanar**: it has `6 > 2·4 − 3` edges. -/
theorem not_isOuterplanar_top_four : ¬IsOuterplanar (⊤ : SimpleGraph (Fin 4)) := fun h => by
  have := h.ncard_edgeSet_le (by simp)
  rw [ncard_edgeSet_top_four, Fintype.card_fin] at this
  omega

/-- The apex graph of the triangle is the complete graph on four vertices. -/
theorem apex_top_three : apex (⊤ : SimpleGraph (Fin 3)) = ⊤ := by
  ext a b
  rcases a with _ | a <;> rcases b with _ | b <;> simp

/-- **The triangle is outerplanar**: its apex graph is `K₄`. -/
theorem isOuterplanar_top_three : IsOuterplanar (⊤ : SimpleGraph (Fin 3)) := by
  unfold IsOuterplanar
  rw [apex_top_three]
  exact IsPlanar.of_iso (Iso.completeGraph (finSuccEquiv 3)) isPlanar_top_four

/-- **The triangle attains the bound**: it has `3 = 2·3 − 3` edges. -/
theorem ncard_edgeSet_top_three : (⊤ : SimpleGraph (Fin 3)).edgeSet.ncard = 2 * 3 - 3 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin]
  rfl

end MonoidProduct.Graph
