import MonoidProduct.Graph.PlanarGlueVertex
import MonoidProduct.Graph.PlanarMinor
import MonoidProduct.Graph.RotationChord
set_option linter.style.header false

/-!
# Gluing planar graphs across separators of size zero, one and two

Let `A ∪ B` be all the vertices of `G`, with no edge between `A \ B` and `B \ A`.  If the induced
graphs `G.induce A` and `G.induce B` are planar (`Graph/Planar.lean`), then so is `G`, when the
separator `A ∩ B` is empty, a single vertex, or the two ends of an edge of `G`.

* `glueSide hcov : V → A ⊕ B` sends the vertices of `A` to the left copy and the others to the
  right copy.  It is one-to-one, and an edge of `G` with both ends on one side goes to an edge of
  that side.
* `isPlanar_of_induce_of_inter_eq_empty`: every edge lies on one side, so `glueSide` is an
  injective homomorphism into the disjoint union `G.induce A ⊕g G.induce B`, which is planar
  (`IsPlanar.sum`).
* `isPlanar_of_induce_of_inter_eq_singleton`: the edges between the two sides go through the
  separator `x`.  `glueSide` is an injective homomorphism into the gluing of the two sides at
  their copies of `x`, which is planar (`IsPlanar.glueVertex`).
* `isPlanar_of_induce_of_inter_eq_pair`, for the ends of an edge `xy`: glue the two sides at
  their copies of `x`, keeping the faces of the two copies of the dart from `x` to `y` together
  (`exists_isSpherical_glueVertex`).  The merged face contains the darts after them, which start
  at the two copies of `y`; these are distinct and not adjacent, so the chord between them keeps
  planarity (`isPlanar_sup_edge_of_sameCycle`).  Contracting that chord
  (`IsPlanar.contractEdge`) identifies the two copies of `y`, and the two copies of the edge `xy`
  become one.  `G` maps into the contraction by an injective homomorphism.  A bridge `xy` needs
  no separate treatment, since no face has to be a cycle.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

/-! ## The two sides -/

private theorem glue_mem_right (hcov : A ∪ B = Set.univ) {v : V} (hv : v ∉ A) : v ∈ B :=
  (Set.eq_univ_iff_forall.mp hcov v).resolve_left hv

open Classical in
/-- **The side of a vertex**: the left copy for the vertices of `A`, the right copy for the
others. -/
noncomputable def glueSide (hcov : A ∪ B = Set.univ) (v : V) : A ⊕ B :=
  if hv : v ∈ A then .inl ⟨v, hv⟩ else .inr ⟨v, glue_mem_right hcov hv⟩

theorem glueSide_of_mem (hcov : A ∪ B = Set.univ) {v : V} (hv : v ∈ A) :
    glueSide hcov v = .inl ⟨v, hv⟩ :=
  dite_eq_left hv

theorem glueSide_of_notMem (hcov : A ∪ B = Set.univ) {v : V} (hv : v ∉ A) :
    glueSide hcov v = .inr ⟨v, glue_mem_right hcov hv⟩ :=
  dite_eq_right hv

/-- The vertex of `G` underlying its side. -/
theorem elim_glueSide (hcov : A ∪ B = Set.univ) (v : V) :
    Sum.elim Subtype.val Subtype.val (glueSide hcov v) = v := by
  by_cases hv : v ∈ A
  · rw [glueSide_of_mem hcov hv]
    rfl
  · rw [glueSide_of_notMem hcov hv]
    rfl

theorem glueSide_injective (hcov : A ∪ B = Set.univ) : Function.Injective (glueSide hcov) :=
  fun u w h => by rw [← elim_glueSide hcov u, h, elim_glueSide hcov w]

/-- **An edge with both ends on one side** is an edge of that side. -/
theorem sum_adj_glueSide (hcov : A ∪ B = Set.univ) {u w : V} (huw : G.Adj u w)
    (hside : u ∈ A ↔ w ∈ A) :
    (G.induce A ⊕g G.induce B).Adj (glueSide hcov u) (glueSide hcov w) := by
  by_cases hu : u ∈ A
  · rw [glueSide_of_mem hcov hu, glueSide_of_mem hcov (hside.mp hu)]
    exact huw
  · rw [glueSide_of_notMem hcov hu, glueSide_of_notMem hcov (fun hw => hu (hside.mpr hw))]
    exact huw

/-! ## An empty separator -/

/-- **Two planar sides with no common vertex and no edge between them form a planar graph.** -/
theorem isPlanar_of_induce_of_inter_eq_empty [Finite V] {A B : Set V}
    (hcov : A ∪ B = Set.univ) (hnadj : ∀ ⦃u w : V⦄, u ∈ A \ B → w ∈ B \ A → ¬ G.Adj u w)
    (hAB : A ∩ B = ∅) (hA : IsPlanar (G.induce A)) (hB : IsPlanar (G.induce B)) :
    IsPlanar G := by
  have hside : ∀ ⦃u w⦄, G.Adj u w → (u ∈ A ↔ w ∈ A) := fun u w huw => by
    have hout : ∀ ⦃u w⦄, G.Adj u w → u ∈ A → w ∈ A := fun u w huw hu => by
      by_contra hw
      refine hnadj ⟨hu, fun huB => ?_⟩ ⟨glue_mem_right hcov hw, hw⟩ huw
      have : u ∈ A ∩ B := ⟨hu, huB⟩
      rw [hAB] at this
      exact this
    exact ⟨hout huw, hout huw.symm⟩
  exact (hA.sum hB).of_injective ⟨glueSide hcov, fun huw => sum_adj_glueSide hcov huw (hside huw)⟩
    (glueSide_injective hcov)

/-! ## Gluing at a vertex of the separator -/

section GlueAt

variable {x : V}

/-- The side of a vertex never is the right copy of a vertex `x` of `A`. -/
theorem glueSide_ne (hcov : A ∪ B = Set.univ) (hxA : x ∈ A) (hxB : x ∈ B) (v : V) :
    glueSide hcov v ≠ .inr ⟨x, hxB⟩ := by
  by_cases hv : v ∈ A
  · rw [glueSide_of_mem hcov hv]
    exact Sum.inl_ne_inr
  · rw [glueSide_of_notMem hcov hv]
    intro h
    have hvx : v = x := congrArg Subtype.val (Sum.inr.inj h)
    exact hv (hvx ▸ hxA)

/-- **The vertex map into the gluing of the two sides at `x`**: the side of each vertex, which
is never the right copy of `x`. -/
noncomputable def glueVertexMap (hcov : A ∪ B = Set.univ) (hxA : x ∈ A) (hxB : x ∈ B) (v : V) :
    {s : A ⊕ B // s ≠ .inr ⟨x, hxB⟩} :=
  ⟨glueSide hcov v, glueSide_ne hcov hxA hxB v⟩

theorem glueVertexMap_injective (hcov : A ∪ B = Set.univ) (hxA : x ∈ A) (hxB : x ∈ B) :
    Function.Injective (glueVertexMap hcov hxA hxB) :=
  fun _ _ h => glueSide_injective hcov (congrArg Subtype.val h)

/-- **An edge with both ends on one side survives the gluing at `x`.** -/
theorem glueVertexMap_adj_of_side (hcov : A ∪ B = Set.univ) (hxA : x ∈ A) (hxB : x ∈ B)
    {u w : V} (huw : G.Adj u w) (hside : u ∈ A ↔ w ∈ A) :
    (contractEdge (G.induce A ⊕g G.induce B) (.inl ⟨x, hxA⟩) (.inr ⟨x, hxB⟩)).Adj
      (glueVertexMap hcov hxA hxB u) (glueVertexMap hcov hxA hxB w) :=
  contractEdge_adj.mpr ⟨(glueVertexMap_injective hcov hxA hxB).ne huw.ne,
    Or.inl (Or.inl (sum_adj_glueSide hcov huw hside))⟩

/-- **An edge from `x` to the other side survives the gluing at `x`**: it is an edge of the right
copy of `x`, which is identified with the left one. -/
theorem glueVertexMap_adj_self (hcov : A ∪ B = Set.univ) (hxA : x ∈ A) (hxB : x ∈ B) {w : V}
    (hxw : G.Adj x w) (hw : w ∉ A) :
    (contractEdge (G.induce A ⊕g G.induce B) (.inl ⟨x, hxA⟩) (.inr ⟨x, hxB⟩)).Adj
      (glueVertexMap hcov hxA hxB x) (glueVertexMap hcov hxA hxB w) := by
  refine contractEdge_adj.mpr ⟨(glueVertexMap_injective hcov hxA hxB).ne hxw.ne,
    Or.inl (Or.inr ⟨glueSide_of_mem hcov hxA, ?_⟩)⟩
  change (G.induce A ⊕g G.induce B).Adj (.inr ⟨x, hxB⟩) (glueSide hcov w)
  rw [glueSide_of_notMem hcov hw]
  exact hxw

end GlueAt

/-! ## A separator of one vertex -/

/-- **Two planar sides meeting in one vertex, with no edge between the rest, form a planar
graph.** -/
theorem isPlanar_of_induce_of_inter_eq_singleton [Finite V] {A B : Set V} {x : V}
    (hcov : A ∪ B = Set.univ) (hnadj : ∀ ⦃u w : V⦄, u ∈ A \ B → w ∈ B \ A → ¬ G.Adj u w)
    (hAB : A ∩ B = {x}) (hA : IsPlanar (G.induce A)) (hB : IsPlanar (G.induce B)) :
    IsPlanar G := by
  obtain ⟨hxA, hxB⟩ : x ∈ A ∩ B := hAB ▸ rfl
  -- An edge leaving `A` starts at `x`.
  have hcross : ∀ ⦃u w⦄, G.Adj u w → u ∈ A → w ∉ A → u = x := fun u w huw hu hw => by
    have huB : u ∈ B := by
      by_contra huB
      exact hnadj ⟨hu, huB⟩ ⟨glue_mem_right hcov hw, hw⟩ huw
    have : u ∈ A ∩ B := ⟨hu, huB⟩
    rw [hAB] at this
    exact this
  refine (hA.glueVertex hB ⟨x, hxA⟩ ⟨x, hxB⟩).of_injective
    ⟨glueVertexMap hcov hxA hxB, fun {u w} huw => ?_⟩ (glueVertexMap_injective hcov hxA hxB)
  by_cases hu : u ∈ A <;> by_cases hw : w ∈ A
  · exact glueVertexMap_adj_of_side hcov hxA hxB huw (iff_of_true hu hw)
  · obtain rfl := hcross huw hu hw
    exact glueVertexMap_adj_self hcov hxA hxB huw hw
  · obtain rfl := hcross huw.symm hw hu
    exact (glueVertexMap_adj_self hcov hxA hxB huw.symm hu).symm
  · exact glueVertexMap_adj_of_side hcov hxA hxB huw (iff_of_false hu hw)

/-! ## A separator of two adjacent vertices -/

/-- **Two planar sides meeting in the two ends of an edge, with no edge between the rest, form
a planar graph.**  Glue the sides at `x`, add the chord between the two copies of `y` inside the
face that holds both copies of the edge `xy`, and contract it. -/
theorem isPlanar_of_induce_of_inter_eq_pair [Finite V] {A B : Set V} {x y : V}
    (hcov : A ∪ B = Set.univ) (hnadj : ∀ ⦃u w : V⦄, u ∈ A \ B → w ∈ B \ A → ¬ G.Adj u w)
    (hxy : G.Adj x y) (hAB : A ∩ B = {x, y}) (hA : IsPlanar (G.induce A))
    (hB : IsPlanar (G.induce B)) : IsPlanar G := by
  obtain ⟨hxA, hxB⟩ : x ∈ A ∩ B := hAB ▸ Set.mem_insert x {y}
  obtain ⟨hyA, hyB⟩ : y ∈ A ∩ B := hAB ▸ Set.mem_insert_of_mem x rfl
  -- An edge leaving `A` starts at `x` or at `y`.
  have hcross : ∀ ⦃u w⦄, G.Adj u w → u ∈ A → w ∉ A → u = x ∨ u = y := fun u w huw hu hw => by
    have huB : u ∈ B := by
      by_contra huB
      exact hnadj ⟨hu, huB⟩ ⟨glue_mem_right hcov hw, hw⟩ huw
    have : u ∈ A ∩ B := ⟨hu, huB⟩
    rw [hAB] at this
    exact this
  obtain ⟨ρ₁, hρ₁⟩ := hA
  obtain ⟨ρ₂, hρ₂⟩ := hB
  -- Glue at `x`, keeping the faces of the two copies of the dart from `x` to `y` together.
  set a : (G.induce A).Dart := ⟨(⟨x, hxA⟩, ⟨y, hyA⟩), hxy⟩
  set b : (G.induce B).Dart := ⟨(⟨x, hxB⟩, ⟨y, hyB⟩), hxy⟩
  obtain ⟨σ, hσ, hface⟩ := exists_isSpherical_glueVertex hρ₁ hρ₂ (a := a) (b := b) rfl rfl
  set K := contractEdge (G.induce A ⊕g G.induce B) (.inl ⟨x, hxA⟩) (.inr ⟨x, hxB⟩)
  -- The two copies of `y`.
  set y₁ : {s : A ⊕ B // s ≠ .inr ⟨x, hxB⟩} := ⟨.inl ⟨y, hyA⟩, Sum.inl_ne_inr⟩
  set y₂ : {s : A ⊕ B // s ≠ .inr ⟨x, hxB⟩} :=
    ⟨.inr ⟨y, hyB⟩, fun h => hxy.ne (congrArg Subtype.val (Sum.inr.inj h)).symm⟩
  have hy₁₂ : y₁ ≠ y₂ := fun h => Sum.inl_ne_inr (congrArg Subtype.val h)
  -- The darts after `a` and `b` on the merged face start at `y₁` and `y₂`.
  have h₁ : (glueDartLeft (G₂ := G.induce B) ⟨x, hxA⟩ ⟨x, hxB⟩ (ρ₁.face a)).fst = y₁ := by
    rw [fst_glueDartLeft]
    exact Subtype.ext (congrArg Sum.inl (ρ₁.fst_face a))
  have hfb : (ρ₂.face b).fst = ⟨y, hyB⟩ := ρ₂.fst_face b
  have h₂ : (glueDartRight (G₁ := G.induce A) ⟨x, hxA⟩ ⟨x, hxB⟩ (ρ₂.face b)).fst = y₂ := by
    rw [fst_glueDartRight _ _ (by rw [hfb]; exact fun h => hxy.ne (congrArg Subtype.val h).symm)]
    exact Subtype.ext (congrArg Sum.inr hfb)
  have hchord := isPlanar_sup_edge_of_sameCycle hσ
    (hface (Equiv.Perm.sameCycle_apply_right.mpr .rfl)
      (Equiv.Perm.sameCycle_apply_right.mpr .rfl)) (by rw [h₁, h₂]; exact hy₁₂)
  rw [h₁, h₂] at hchord
  -- Contract the chord.
  have hadj : (K ⊔ edge y₁ y₂).Adj y₁ y₂ :=
    (sup_adj _ _ _ _).mpr (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hy₁₂⟩))
  have hC := hchord.contractEdge hadj
  -- `G` maps into the contraction.
  have hne₂ : ∀ v, glueVertexMap hcov hxA hxB v ≠ y₂ := fun v h => by
    have h' : glueSide hcov v = .inr ⟨y, hyB⟩ := congrArg Subtype.val h
    by_cases hv : v ∈ A
    · rw [glueSide_of_mem hcov hv] at h'
      exact Sum.inl_ne_inr h'
    · rw [glueSide_of_notMem hcov hv] at h'
      have hvy : v = y := congrArg Subtype.val (Sum.inr.inj h')
      exact hv (hvy ▸ hyA)
  let f : V → {s // s ≠ y₂} := fun v => ⟨glueVertexMap hcov hxA hxB v, hne₂ v⟩
  have hf : Function.Injective f :=
    fun _ _ h => glueVertexMap_injective hcov hxA hxB (congrArg Subtype.val h)
  -- Edges of `K` survive the contraction.
  have hK : ∀ ⦃u w⦄, u ≠ w →
      K.Adj (glueVertexMap hcov hxA hxB u) (glueVertexMap hcov hxA hxB w) →
      (Graph.contractEdge (K ⊔ edge y₁ y₂) y₁ y₂).Adj (f u) (f w) := fun u w huw h =>
    contractEdge_adj.mpr ⟨hf.ne huw, Or.inl (Or.inl ((sup_adj _ _ _ _).mpr (Or.inl h)))⟩
  -- An edge from `y` to the other side survives as an edge of the right copy of `y`.
  have hY : ∀ ⦃w⦄, G.Adj y w → w ∉ A →
      (Graph.contractEdge (K ⊔ edge y₁ y₂) y₁ y₂).Adj (f y) (f w) := fun w hyw hw => by
    have hwy : glueVertexMap hcov hxA hxB w ≠ y₂ := hne₂ w
    have hK₂ : K.Adj y₂ (glueVertexMap hcov hxA hxB w) := by
      refine contractEdge_adj.mpr ⟨hwy.symm, Or.inl (Or.inl ?_)⟩
      change (G.induce A ⊕g G.induce B).Adj (.inr ⟨y, hyB⟩) (glueSide hcov w)
      rw [glueSide_of_notMem hcov hw]
      exact hyw
    refine contractEdge_adj.mpr ⟨hf.ne hyw.ne, Or.inl (Or.inr ⟨?_, ?_⟩)⟩
    · exact Subtype.ext (glueSide_of_mem hcov hyA)
    · exact (sup_adj _ _ _ _).mpr (Or.inl hK₂)
  refine hC.of_injective ⟨f, fun {u w} huw => ?_⟩ hf
  by_cases hu : u ∈ A <;> by_cases hw : w ∈ A
  · exact hK huw.ne (glueVertexMap_adj_of_side hcov hxA hxB huw (iff_of_true hu hw))
  · rcases hcross huw hu hw with rfl | rfl
    · exact hK huw.ne (glueVertexMap_adj_self hcov hxA hxB huw hw)
    · exact hY huw hw
  · rcases hcross huw.symm hw hu with rfl | rfl
    · exact (hK huw.ne.symm (glueVertexMap_adj_self hcov hxA hxB huw.symm hu)).symm
    · exact (hY huw.symm hu).symm
  · exact hK huw.ne (glueVertexMap_adj_of_side hcov hxA hxB huw (iff_of_false hu hw))

end MonoidProduct.Graph
