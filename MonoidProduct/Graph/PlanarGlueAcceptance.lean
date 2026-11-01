import MonoidProduct.Graph.PlanarGlue
import MonoidProduct.Graph.PlanarExamples
set_option linter.style.header false

/-!
# Acceptance statements for gluing planar graphs

The statements of `Graph/PlanarGlueVertex.lean` and `Graph/PlanarGlue.lean`, restated, followed
by small sanity checks.  Lean checks every `example` here against the library's statement.

* Disjoint unions: the Euler defects add, and planarity is kept.
* Identifying two vertices in different components: splicing the two vertex cycles keeps the
  Euler defect and merges the faces of the two spliced darts; so does carrying the rotation over
  when one of the two vertices is isolated.
* One-vertex gluing: a spherical rotation system keeping two chosen faces together, and
  planarity.
* Separators: planarity of the two induced sides gives planarity of the graph, for an empty
  separator, a single vertex, and the two ends of an edge.

The sanity checks glue two copies of `K₂` at a vertex, and show that two disjoint triangles, two
triangles sharing a vertex, and two copies of `K₄` sharing an edge are planar, each from the
planarity of `K₄`.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-! ## Statements -/

section Statements

variable {V V₁ V₂ W : Type*} {G : SimpleGraph V} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
  {H : SimpleGraph W}

/-- **Disjoint unions**: the Euler defects add, so spherical rotation systems and planarity are
kept. -/
example [Finite V₁] [Finite V₂] (ρ₁ : RotationSystem G₁) (ρ₂ : RotationSystem G₂) :
    (ρ₁.sum ρ₂).eulerDefect = ρ₁.eulerDefect + ρ₂.eulerDefect :=
  ρ₁.eulerDefect_sum ρ₂

example [Finite V₁] [Finite V₂] (h₁ : IsPlanar G₁) (h₂ : IsPlanar G₂) : IsPlanar (G₁ ⊕g G₂) :=
  h₁.sum h₂

/-- **Splicing at two vertices in different components** keeps the Euler defect, and merges the
faces of the two spliced darts. -/
example [Finite W] [DecidableEq W] (ρ : RotationSystem H) {x₁ x₂ : W}
    (h : ¬ H.Reachable x₁ x₂) {a b : H.Dart} (ha : a.fst = x₁) (hb : b.fst = x₂) :
    (ρ.identifySplice h ha hb).eulerDefect = ρ.eulerDefect ∧
      ∀ ⦃d e : H.Dart⦄, ρ.face.SameCycle a d → ρ.face.SameCycle b e →
        (ρ.identifySplice h ha hb).face.SameCycle (identifyDartEquiv h d)
          (identifyDartEquiv h e) :=
  ⟨ρ.eulerDefect_identifySplice h ha hb, fun _ _ hd he =>
    ρ.sameCycle_identifySplice_face h ha hb hd he⟩

/-- **Identifying with an isolated vertex** keeps the Euler defect. -/
example [Finite W] [DecidableEq W] (ρ : RotationSystem H) {x₁ x₂ : W}
    (h : ¬ H.Reachable x₁ x₂) (hI : x₁ ∈ isolatedVerts H ∨ x₂ ∈ isolatedVerts H) :
    (ρ.identifyPlain h hI).eulerDefect = ρ.eulerDefect :=
  ρ.eulerDefect_identifyPlain h hI

/-- **One-vertex gluing, keeping two faces together.** -/
example [Finite V₁] [Finite V₂] {ρ₁ : RotationSystem G₁} {ρ₂ : RotationSystem G₂}
    (h₁ : ρ₁.IsSpherical) (h₂ : ρ₂.IsSpherical) {x₁ : V₁} {x₂ : V₂} {a : G₁.Dart}
    {b : G₂.Dart} (ha : a.fst = x₁) (hb : b.fst = x₂) :
    ∃ σ : RotationSystem (contractEdge (G₁ ⊕g G₂) (.inl x₁) (.inr x₂)), σ.IsSpherical ∧
      ∀ ⦃d : G₁.Dart⦄ ⦃e : G₂.Dart⦄, ρ₁.face.SameCycle a d → ρ₂.face.SameCycle b e →
        σ.face.SameCycle (glueDartLeft x₁ x₂ d) (glueDartRight x₁ x₂ e) :=
  exists_isSpherical_glueVertex h₁ h₂ ha hb

/-- **The glued darts keep their tails**, the glued vertex aside. -/
example (x₁ : V₁) (x₂ : V₂) (d : G₁.Dart) (e : G₂.Dart) (he : e.fst ≠ x₂) :
    (glueDartLeft (G₂ := G₂) x₁ x₂ d).fst = ⟨.inl d.fst, Sum.inl_ne_inr⟩ ∧
      (glueDartRight (G₁ := G₁) x₁ x₂ e).fst = ⟨.inr e.fst, fun h => he (Sum.inr.inj h)⟩ :=
  ⟨fst_glueDartLeft x₁ x₂ d, fst_glueDartRight x₁ e he⟩

/-- **Gluing two planar graphs at a vertex.** -/
example [Finite V₁] [Finite V₂] (h₁ : IsPlanar G₁) (h₂ : IsPlanar G₂) (x₁ : V₁) (x₂ : V₂) :
    IsPlanar (contractEdge (G₁ ⊕g G₂) (.inl x₁) (.inr x₂)) :=
  h₁.glueVertex h₂ x₁ x₂

/-- **An empty separator.** -/
example [Finite V] {A B : Set V}
    (hcov : A ∪ B = Set.univ) (hnadj : ∀ ⦃u w : V⦄, u ∈ A \ B → w ∈ B \ A → ¬ G.Adj u w)
    (hAB : A ∩ B = ∅) (hA : IsPlanar (G.induce A)) (hB : IsPlanar (G.induce B)) :
    IsPlanar G :=
  isPlanar_of_induce_of_inter_eq_empty hcov hnadj hAB hA hB

/-- **A separator of one vertex.** -/
example [Finite V] {A B : Set V} {x : V}
    (hcov : A ∪ B = Set.univ) (hnadj : ∀ ⦃u w : V⦄, u ∈ A \ B → w ∈ B \ A → ¬ G.Adj u w)
    (hAB : A ∩ B = {x}) (hA : IsPlanar (G.induce A)) (hB : IsPlanar (G.induce B)) :
    IsPlanar G :=
  isPlanar_of_induce_of_inter_eq_singleton hcov hnadj hAB hA hB

/-- **A separator of two adjacent vertices.** -/
example [Finite V] {A B : Set V} {x y : V}
    (hcov : A ∪ B = Set.univ) (hnadj : ∀ ⦃u w : V⦄, u ∈ A \ B → w ∈ B \ A → ¬ G.Adj u w)
    (hxy : G.Adj x y) (hAB : A ∩ B = {x, y}) (hA : IsPlanar (G.induce A))
    (hB : IsPlanar (G.induce B)) : IsPlanar G :=
  isPlanar_of_induce_of_inter_eq_pair hcov hnadj hxy hAB hA hB

end Statements

/-! ## Sanity checks -/

section Checks

/-- A graph with an injection into `Fin 4` is planar, as a subgraph of `K₄`. -/
private theorem isPlanar_of_injective_fin_four {W : Type*} (H : SimpleGraph W) (f : W → Fin 4)
    (hf : Function.Injective f) : IsPlanar H :=
  isPlanar_top_four.of_injective ⟨f, fun h => (top_adj _ _).mpr (hf.ne h.ne)⟩ hf

/-- An induced graph on at most four vertices, numbered one-to-one below `4`, is planar. -/
private theorem isPlanar_induce_of_injOn {n : ℕ} (G : SimpleGraph (Fin n)) (A : Set (Fin n))
    (g : Fin n → ℕ) (hg : ∀ v ∈ A, g v < 4) (hinj : ∀ v ∈ A, ∀ w ∈ A, g v = g w → v = w) :
    IsPlanar (G.induce A) :=
  isPlanar_of_injective_fin_four _ (fun v => ⟨g v.1, hg v.1 v.2⟩)
    fun v w h => Subtype.ext (hinj v.1 v.2 w.1 w.2 (congrArg Fin.val h))

/-- **Two copies of `K₂` glued at a vertex**: a path with two edges. -/
example : IsPlanar (contractEdge ((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2)))
    (.inl 0) (.inr 0)) := by
  have hK₂ := isPlanar_of_injective_fin_four (⊤ : SimpleGraph (Fin 2)) (Fin.castLE (by omega))
    (Fin.castLE_injective _)
  exact hK₂.glueVertex hK₂ 0 0

/-- Two triangles, `0 1 2` and `3 4 5`. -/
private def twoTriangles : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v => (u.val ≤ 2 ∧ v.val ≤ 2) ∨ (3 ≤ u.val ∧ 3 ≤ v.val)

/-- **Two disjoint triangles are planar.** -/
example : IsPlanar twoTriangles := by
  refine isPlanar_of_induce_of_inter_eq_empty (A := {v | v.val ≤ 2}) (B := {v | 3 ≤ v.val})
    (Set.eq_univ_of_forall fun v => by simp only [Set.mem_union, Set.mem_ofPred_eq]; omega)
    (fun u w hu hw h => ?_) (Set.eq_empty_of_forall_notMem fun v hv => ?_)
    (isPlanar_induce_of_injOn _ _ (fun v => v.val)
      (fun v hv => by simp only [Set.mem_ofPred_eq] at hv; omega) fun v _ w _ h => Fin.ext h)
    (isPlanar_induce_of_injOn _ _ (fun v => v.val - 3) (fun v _ => by omega)
      fun v hv w hw h => by simp only [Set.mem_ofPred_eq] at hv hw; exact Fin.ext (by omega))
  · simp only [Set.mem_sdiff, Set.mem_ofPred_eq] at hu hw
    rw [twoTriangles, fromRel_adj] at h
    omega
  · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hv
    omega

/-- Two triangles sharing the vertex `2`: `0 1 2` and `2 3 4`. -/
private def bowtie : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun u v => (u.val ≤ 2 ∧ v.val ≤ 2) ∨ (2 ≤ u.val ∧ 2 ≤ v.val)

/-- **Two triangles sharing a vertex are planar.** -/
example : IsPlanar bowtie := by
  refine isPlanar_of_induce_of_inter_eq_singleton (A := {v | v.val ≤ 2}) (B := {v | 2 ≤ v.val})
    (x := 2) (Set.eq_univ_of_forall fun v => by simp only [Set.mem_union, Set.mem_ofPred_eq]; omega)
    (fun u w hu hw h => ?_) (Set.ext fun v => ?_)
    (isPlanar_induce_of_injOn _ _ (fun v => v.val)
      (fun v hv => by simp only [Set.mem_ofPred_eq] at hv; omega) fun v _ w _ h => Fin.ext h)
    (isPlanar_induce_of_injOn _ _ (fun v => v.val - 2) (fun v _ => by omega)
      fun v hv w hw h => by simp only [Set.mem_ofPred_eq] at hv hw; exact Fin.ext (by omega))
  · simp only [Set.mem_sdiff, Set.mem_ofPred_eq] at hu hw
    rw [bowtie, fromRel_adj] at h
    omega
  · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Fin.ext_iff]
    omega

/-- Two copies of `K₄` sharing the edge `0 1`: on `0 1 2 3` and on `0 1 4 5`. -/
private def twoK₄ : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    (u.val ≤ 3 ∧ v.val ≤ 3) ∨ ((u.val ≤ 1 ∨ 4 ≤ u.val) ∧ (v.val ≤ 1 ∨ 4 ≤ v.val))

/-- **Two copies of `K₄` sharing an edge form a planar graph.** -/
example : IsPlanar twoK₄ := by
  refine isPlanar_of_induce_of_inter_eq_pair (A := {v | v.val ≤ 3})
    (B := {v | v.val ≤ 1 ∨ 4 ≤ v.val}) (x := 0) (y := 1)
    (Set.eq_univ_of_forall fun v => by simp only [Set.mem_union, Set.mem_ofPred_eq]; omega)
    (fun u w hu hw h => ?_) ?_ (Set.ext fun v => ?_)
    (isPlanar_induce_of_injOn _ _ (fun v => v.val)
      (fun v hv => by simp only [Set.mem_ofPred_eq] at hv; omega) fun v _ w _ h => Fin.ext h)
    (isPlanar_induce_of_injOn _ _ (fun v => if v.val ≤ 1 then v.val else v.val - 2)
      (fun v _ => by split_ifs <;> omega)
      fun v hv w hw h => by
        simp only [Set.mem_ofPred_eq] at hv hw
        exact Fin.ext (by split_ifs at h <;> omega))
  · simp only [Set.mem_sdiff, Set.mem_ofPred_eq] at hu hw
    rw [twoK₄, fromRel_adj] at h
    omega
  · rw [twoK₄, fromRel_adj]
    decide
  · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Fin.ext_iff]
    omega

end Checks

end MonoidProduct.Graph
