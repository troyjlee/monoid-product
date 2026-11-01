import MonoidProduct.Graph.Wagner
import MonoidProduct.Graph.WagnerConverse
set_option linter.style.header false

/-!
# Acceptance statements for the converse of Wagner's theorem

The statements of `Graph/WagnerConverse.lean`, restated, followed by Wagner's theorem and small
sanity checks.  Lean checks every `example` here against the library's statement.

* Every graph on at most four vertices is planar.
* A `3`-connected graph with neither a `K₅` minor nor a `K₃,₃` minor is planar.
* The converse of Wagner's theorem: a finite graph with neither a `K₅` minor nor a `K₃,₃` minor is
  planar, with only `[Finite V]` assumed.
* **Wagner's theorem**: a finite graph is planar exactly when it has neither a `K₅` minor nor a
  `K₃,₃` minor, from the converse and `IsPlanar.wagner_easy` (`Graph/Wagner.lean`).

The sanity checks cover:
* every graph on `Fin 4` and every graph on an empty vertex type;
* `K₄`, which is `3`-connected and has no Kuratowski minor, so that the `3`-connected converse
  applies to it;
* the edgeless graph on seven vertices, neither small nor connected, whose excluded minors are
  ruled out directly, as `K₅` and `K₃,₃` have edges;
* the contrapositive form: a finite graph is not planar exactly when it has a `K₅` minor or a
  `K₃,₃` minor.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-! ## Statements -/

/-- **Every graph on at most four vertices is planar.** -/
example {V : Type*} [Finite V] {G : SimpleGraph V} (hV : Nat.card V ≤ 4) : IsPlanar G :=
  isPlanar_of_natCard_le_four hV

/-- **The converse of Wagner's theorem for `3`-connected graphs.** -/
example {V : Type*} [Finite V] {G : SimpleGraph V} (hG : IsKConnected G 3)
    (h : NoKuratowskiMinor G) : IsPlanar G :=
  wagner_threeConnected hG h

/-- **The converse of Wagner's theorem**: a finite graph with neither a `K₅` minor nor a `K₃,₃`
minor is planar. -/
example {V : Type*} [Finite V] {G : SimpleGraph V}
    (h5 : ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G)
    (h33 : ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G) : IsPlanar G :=
  wagner_hard h5 h33

/-- **Wagner's theorem**: a finite graph is planar exactly when it has neither a `K₅` minor nor a
`K₃,₃` minor. -/
example {V : Type*} [Finite V] {G : SimpleGraph V} :
    IsPlanar G ↔
      ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G ∧
        ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G :=
  ⟨fun hG => hG.wagner_easy, fun h => wagner_hard h.1 h.2⟩

/-! ## Sanity checks -/

/-- **Every graph on `Fin 4`, and every graph on an empty type, is planar.** -/
example (G : SimpleGraph (Fin 4)) (G' : SimpleGraph Empty) : IsPlanar G ∧ IsPlanar G' :=
  ⟨isPlanar_of_natCard_le_four (by simp), isPlanar_of_natCard_le_four (by simp)⟩

/-- **`K₄` meets the hypotheses of the `3`-connected converse**: it is `3`-connected, and has no
Kuratowski minor, being planar. -/
example : IsKConnected (⊤ : SimpleGraph (Fin 4)) 3 ∧ NoKuratowskiMinor (⊤ : SimpleGraph (Fin 4)) ∧
    IsPlanar (⊤ : SimpleGraph (Fin 4)) := by
  have h3 : IsKConnected (⊤ : SimpleGraph (Fin 4)) 3 :=
    ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num, by decide⟩
  have hK : NoKuratowskiMinor (⊤ : SimpleGraph (Fin 4)) := isPlanar_top_four.wagner_easy
  exact ⟨h3, hK, wagner_threeConnected h3 hK⟩

/-- **The edgeless graph on seven vertices is planar by the converse**: a minor model of `K₅` or
`K₃,₃` would need an edge between two branch sets. -/
example : IsPlanar (⊥ : SimpleGraph (Fin 7)) := by
  refine wagner_hard (fun ⟨m⟩ => ?_) (fun ⟨m⟩ => ?_)
  · obtain ⟨a, -, b, -, hab⟩ := m.adj 0 1 (by decide)
    exact hab
  · obtain ⟨a, -, b, -, hab⟩ := m.adj (Sum.inl 0) (Sum.inr 0) (by simp)
    exact hab

/-- **A finite graph is not planar exactly when it has a `K₅` minor or a `K₃,₃` minor.** -/
example {V : Type*} [Finite V] {G : SimpleGraph V} :
    ¬ IsPlanar G ↔
      IsMinor (⊤ : SimpleGraph (Fin 5)) G ∨ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G := by
  constructor
  · intro hG
    by_contra h
    push Not at h
    exact hG (wagner_hard h.1 h.2)
  · rintro (h | h) hG
    · exact hG.wagner_easy.1 h
    · exact hG.wagner_easy.2 h

end MonoidProduct.Graph
