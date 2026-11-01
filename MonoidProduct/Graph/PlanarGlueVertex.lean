import Mathlib.Combinatorics.SimpleGraph.Sum
import MonoidProduct.Graph.PlanarContraction
set_option linter.style.header false

/-!
# Gluing rotation systems: disjoint unions and one vertex

Planarity (`Graph/Planar.lean`) of graphs glued from planar pieces, by explicit rotation systems
and the Euler defect `Δ = 2C − V + E − F̂` (`Graph/RotationDeletion.lean`), which vanishes exactly
for spherical rotation systems (`isSpherical_iff_eulerDefect_eq_zero`).

* **Disjoint unions** `G₁ ⊕g G₂`: the darts are those of the two graphs (`sumDartEquiv`), and the
  two rotations side by side form `RotationSystem.sum`, whose faces are those of the two sides
  (`sum_face`).  Components, vertices, edges, faces and isolated vertices add up, so
  `eulerDefect_sum`: the defects add, and `IsPlanar.sum`: **a disjoint union of planar graphs is
  planar**.
* **Identifying two vertices in different components**: `contractEdge H x₁ x₂`, which merges `x₂`
  into `x₁`, needs no edge `x₁x₂`.  When `x₁` and `x₂` do not reach each other, its darts are those
  of `H` (`identifyDartEquiv`), and it has one component and one vertex fewer, with the same edges
  (`natCard_connectedComponent_contractEdge_add_one_of_not_reachable`, through the bridge `x₁x₂`).
* `RotationSystem.identifySplice`: for darts `a` at `x₁` and `b` at `x₂`, the rotation
  `swap a b * rot` merges the two vertex cycles.  Its face permutation is `swap a b * face`
  (`identifySplice_face`), which merges the faces of `a` and of `b` into one
  (`sameCycle_identifySplice_face`) and keeps the others: one face fewer.  So the Euler defect is
  unchanged (`eulerDefect_identifySplice`).
* `RotationSystem.identifyPlain`: when `x₁` or `x₂` is isolated, the rotation is carried over
  unchanged; there is one isolated vertex fewer instead of one face fewer, and again the Euler
  defect is unchanged (`eulerDefect_identifyPlain`).
* **One-vertex gluing** of `G₁` and `G₂` at `x₁` and `x₂`: the graph
  `contractEdge (G₁ ⊕g G₂) (.inl x₁) (.inr x₂)`, with the darts `glueDartLeft` and
  `glueDartRight` of the two sides.  `exists_isSpherical_glueVertex`: **for spherical rotation
  systems of the sides and darts `a` at `x₁` and `b` at `x₂`, the gluing has a spherical rotation
  system in which the faces of `a` and of `b` lie in one face**.  `IsPlanar.glueVertex`: gluing
  two planar graphs at a vertex gives a planar graph, isolated glued vertices included.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm

/-! ## Cycles of a sum of permutations -/

section SumCongr

variable {α β : Type*}

private theorem sumCongr_zpow (p : Perm α) (q : Perm β) (i : ℤ) :
    Perm.sumCongr p q ^ i = Perm.sumCongr (p ^ i) (q ^ i) :=
  (map_zpow (sumCongrHom α β) (p, q) i).symm

private theorem sameCycle_sumCongr_inl {p : Perm α} {q : Perm β} {a b : α} :
    (Perm.sumCongr p q).SameCycle (.inl a) (.inl b) ↔ p.SameCycle a b := by
  constructor
  · rintro ⟨i, hi⟩
    rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl, Sum.inl.injEq] at hi
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl, hi]⟩

private theorem sameCycle_sumCongr_inr {p : Perm α} {q : Perm β} {a b : β} :
    (Perm.sumCongr p q).SameCycle (.inr a) (.inr b) ↔ q.SameCycle a b := by
  constructor
  · rintro ⟨i, hi⟩
    rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inr, Sum.inr.injEq] at hi
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inr, hi]⟩

private theorem not_sameCycle_sumCongr_inl_inr {p : Perm α} {q : Perm β} {a : α} {b : β} :
    ¬ (Perm.sumCongr p q).SameCycle (.inl a) (.inr b) := by
  rintro ⟨i, hi⟩
  rw [sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl] at hi
  exact Sum.inl_ne_inr hi

/-- **The cycles of a sum of permutations** are those of the two summands. -/
private theorem cycleCount_sumCongr [Finite α] [Finite β] (p : Perm α) (q : Perm β) :
    cycleCount (Perm.sumCongr p q) = cycleCount p + cycleCount q := by
  let Φ : Quotient (SameCycle.setoid p) ⊕ Quotient (SameCycle.setoid q) →
      Quotient (SameCycle.setoid (Perm.sumCongr p q)) :=
    Sum.elim (Quotient.map Sum.inl fun _ _ h => sameCycle_sumCongr_inl.mpr h)
      (Quotient.map Sum.inr fun _ _ h => sameCycle_sumCongr_inr.mpr h)
  have hΦ : Function.Bijective Φ := by
    refine ⟨?_, fun c => ?_⟩
    · rintro (c | c) (c' | c') h <;> induction c using Quotient.inductionOn <;>
        induction c' using Quotient.inductionOn
      · exact congrArg Sum.inl (Quotient.sound (sameCycle_sumCongr_inl.mp (Quotient.exact h)))
      · exact absurd (Quotient.exact h) not_sameCycle_sumCongr_inl_inr
      · exact absurd (Quotient.exact h).symm not_sameCycle_sumCongr_inl_inr
      · exact congrArg Sum.inr (Quotient.sound (sameCycle_sumCongr_inr.mp (Quotient.exact h)))
    · induction c using Quotient.inductionOn with
      | h z =>
      rcases z with a | b
      · exact ⟨.inl ⟦a⟧, rfl⟩
      · exact ⟨.inr ⟦b⟧, rfl⟩
  unfold cycleCount
  rw [← Nat.card_eq_of_bijective Φ hΦ, Nat.card_sum]

end SumCongr

/-! ## Disjoint unions -/

section Sum

variable {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}

/-- A dart of either graph, as a dart of the disjoint union. -/
def sumDart : G₁.Dart ⊕ G₂.Dart → (G₁ ⊕g G₂).Dart
  | .inl d => ⟨(.inl d.fst, .inl d.snd), d.adj⟩
  | .inr d => ⟨(.inr d.fst, .inr d.snd), d.adj⟩

theorem sumDart_bijective : Function.Bijective (sumDart (G₁ := G₁) (G₂ := G₂)) := by
  refine ⟨?_, ?_⟩
  · rintro (d | d) (d' | d') h
    · have h1 := congrArg (fun d : (G₁ ⊕g G₂).Dart => d.fst) h
      have h2 := congrArg (fun d : (G₁ ⊕g G₂).Dart => d.snd) h
      simp only [sumDart, Sum.inl.injEq] at h1 h2
      exact congrArg Sum.inl (Dart.ext _ _ (Prod.ext h1 h2))
    · exact absurd (congrArg (fun d : (G₁ ⊕g G₂).Dart => d.fst) h) Sum.inl_ne_inr
    · exact absurd (congrArg (fun d : (G₁ ⊕g G₂).Dart => d.fst) h) Sum.inr_ne_inl
    · have h1 := congrArg (fun d : (G₁ ⊕g G₂).Dart => d.fst) h
      have h2 := congrArg (fun d : (G₁ ⊕g G₂).Dart => d.snd) h
      simp only [sumDart, Sum.inr.injEq] at h1 h2
      exact congrArg Sum.inr (Dart.ext _ _ (Prod.ext h1 h2))
  · rintro ⟨⟨u | u, w | w⟩, h⟩
    · exact ⟨.inl ⟨(u, w), h⟩, rfl⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact ⟨.inr ⟨(u, w), h⟩, rfl⟩

/-- **The darts of a disjoint union** are those of the two graphs. -/
noncomputable def sumDartEquiv : G₁.Dart ⊕ G₂.Dart ≃ (G₁ ⊕g G₂).Dart :=
  Equiv.ofBijective sumDart sumDart_bijective

theorem sumDartEquiv_symm (z : G₁.Dart ⊕ G₂.Dart) :
    sumDartEquiv (Sum.map Dart.symm Dart.symm z) = (sumDartEquiv z).symm := by
  rcases z with d | d <;> rfl

namespace RotationSystem

/-- **The rotation system of a disjoint union**: the two rotations side by side. -/
noncomputable def sum (ρ₁ : RotationSystem G₁) (ρ₂ : RotationSystem G₂) :
    RotationSystem (G₁ ⊕g G₂) where
  rot := sumDartEquiv.permCongr (Perm.sumCongr ρ₁.rot ρ₂.rot)
  fst_rot d := by
    obtain ⟨z, rfl⟩ := sumDartEquiv.surjective d
    rw [permCongr_apply, symm_apply_apply]
    rcases z with z | z
    · exact congrArg Sum.inl (ρ₁.fst_rot z)
    · exact congrArg Sum.inr (ρ₂.fst_rot z)
  sameCycle_rot d d' h := by
    obtain ⟨z, rfl⟩ := sumDartEquiv.surjective d
    obtain ⟨z', rfl⟩ := sumDartEquiv.surjective d'
    rw [sameCycle_permCongr]
    rcases z with z | z <;> rcases z' with z' | z'
    · exact sameCycle_sumCongr_inl.mpr (ρ₁.sameCycle_rot z z' (Sum.inl.inj h))
    · exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inr_ne_inl
    · exact sameCycle_sumCongr_inr.mpr (ρ₂.sameCycle_rot z z' (Sum.inr.inj h))

/-- **The faces of a disjoint union**: the two face permutations side by side. -/
theorem sum_face (ρ₁ : RotationSystem G₁) (ρ₂ : RotationSystem G₂) :
    (ρ₁.sum ρ₂).face = sumDartEquiv.permCongr (Perm.sumCongr ρ₁.face ρ₂.face) := by
  refine Equiv.ext fun d => ?_
  obtain ⟨z, rfl⟩ := sumDartEquiv.surjective d
  rw [face_apply, ← sumDartEquiv_symm]
  change sumDartEquiv (Perm.sumCongr ρ₁.rot ρ₂.rot (sumDartEquiv.symm _)) =
    sumDartEquiv (Perm.sumCongr ρ₁.face ρ₂.face (sumDartEquiv.symm _))
  rw [symm_apply_apply, symm_apply_apply]
  rcases z with z | z <;> rfl

/-- The faces of the left graph are faces of the disjoint union. -/
theorem sameCycle_sum_face_inl (ρ₁ : RotationSystem G₁) (ρ₂ : RotationSystem G₂)
    {d e : G₁.Dart} :
    (ρ₁.sum ρ₂).face.SameCycle (sumDartEquiv (.inl d)) (sumDartEquiv (.inl e)) ↔
      ρ₁.face.SameCycle d e := by
  rw [sum_face, sameCycle_permCongr, sameCycle_sumCongr_inl]

/-- The faces of the right graph are faces of the disjoint union. -/
theorem sameCycle_sum_face_inr (ρ₁ : RotationSystem G₁) (ρ₂ : RotationSystem G₂)
    {d e : G₂.Dart} :
    (ρ₁.sum ρ₂).face.SameCycle (sumDartEquiv (.inr d)) (sumDartEquiv (.inr e)) ↔
      ρ₂.face.SameCycle d e := by
  rw [sum_face, sameCycle_permCongr, sameCycle_sumCongr_inr]

/-- **The faces of a disjoint union** are those of the two rotation systems. -/
theorem natCard_face_sum [Finite V₁] [Finite V₂] (ρ₁ : RotationSystem G₁)
    (ρ₂ : RotationSystem G₂) :
    Nat.card (ρ₁.sum ρ₂).Face = Nat.card ρ₁.Face + Nat.card ρ₂.Face := by
  have := finite_dart (G := G₁)
  have := finite_dart (G := G₂)
  change cycleCount (ρ₁.sum ρ₂).face = cycleCount ρ₁.face + cycleCount ρ₂.face
  rw [sum_face, cycleCount_permCongr, cycleCount_sumCongr]

end RotationSystem

/-- A function constant along the edges is constant along walks. -/
private theorem eq_of_reachable_of_forall_adj_eq {V α : Type*} {G : SimpleGraph V} {f : V → α}
    (hf : ∀ ⦃u w⦄, G.Adj u w → f u = f w) {u w : V} (h : G.Reachable u w) : f u = f w := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hab ih => exact ih.trans (hf hab)

/-- **Walks of a disjoint union stay on the left.** -/
private theorem reachable_sum_inl_iff {u w : V₁} :
    (G₁ ⊕g G₂).Reachable (.inl u) (.inl w) ↔ G₁.Reachable u w := by
  refine ⟨fun h => ?_, fun h => h.map Embedding.sumInl.toHom⟩
  let f : V₁ ⊕ V₂ → Option G₁.ConnectedComponent :=
    Sum.elim (fun v => some (G₁.connectedComponentMk v)) fun _ => none
  have hf : ∀ ⦃s t⦄, (G₁ ⊕g G₂).Adj s t → f s = f t := by
    rintro (s | s) (t | t) hst
    · exact congrArg some (ConnectedComponent.eq.mpr (Adj.reachable hst))
    · simp at hst
    · simp at hst
    · rfl
  exact ConnectedComponent.eq.mp (Option.some.inj (eq_of_reachable_of_forall_adj_eq hf h))

/-- **Walks of a disjoint union stay on the right.** -/
private theorem reachable_sum_inr_iff {u w : V₂} :
    (G₁ ⊕g G₂).Reachable (.inr u) (.inr w) ↔ G₂.Reachable u w := by
  refine ⟨fun h => ?_, fun h => h.map Embedding.sumInr.toHom⟩
  let f : V₁ ⊕ V₂ → Option G₂.ConnectedComponent :=
    Sum.elim (fun _ => none) fun v => some (G₂.connectedComponentMk v)
  have hf : ∀ ⦃s t⦄, (G₁ ⊕g G₂).Adj s t → f s = f t := by
    rintro (s | s) (t | t) hst
    · rfl
    · simp at hst
    · simp at hst
    · exact congrArg some (ConnectedComponent.eq.mpr (Adj.reachable hst))
  exact ConnectedComponent.eq.mp (Option.some.inj (eq_of_reachable_of_forall_adj_eq hf h))

/-- **The components of a disjoint union** are those of the two graphs. -/
theorem natCard_connectedComponent_sum [Finite V₁] [Finite V₂] :
    Nat.card (G₁ ⊕g G₂).ConnectedComponent =
      Nat.card G₁.ConnectedComponent + Nat.card G₂.ConnectedComponent := by
  let Φ : G₁.ConnectedComponent ⊕ G₂.ConnectedComponent → (G₁ ⊕g G₂).ConnectedComponent :=
    Sum.elim (ConnectedComponent.map Embedding.sumInl.toHom)
      (ConnectedComponent.map Embedding.sumInr.toHom)
  have hΦ : Function.Bijective Φ := by
    refine ⟨?_, fun c => ?_⟩
    · rintro (c | c) (c' | c') h <;> induction c using ConnectedComponent.ind <;>
        induction c' using ConnectedComponent.ind
      · exact congrArg Sum.inl (ConnectedComponent.eq.mpr
          (reachable_sum_inl_iff.mp (ConnectedComponent.eq.mp h)))
      · exact absurd (ConnectedComponent.eq.mp h) (not_reachable_sum_inl_inr _ _)
      · exact absurd (ConnectedComponent.eq.mp h).symm (not_reachable_sum_inl_inr _ _)
      · exact congrArg Sum.inr (ConnectedComponent.eq.mpr
          (reachable_sum_inr_iff.mp (ConnectedComponent.eq.mp h)))
    · induction c using ConnectedComponent.ind with
      | h s =>
      rcases s with u | u
      · exact ⟨.inl (G₁.connectedComponentMk u), rfl⟩
      · exact ⟨.inr (G₂.connectedComponentMk u), rfl⟩
  rw [← Nat.card_eq_of_bijective Φ hΦ, Nat.card_sum]

/-- **The edges of a disjoint union** are those of the two graphs. -/
theorem ncard_edgeSet_sum [Finite V₁] [Finite V₂] :
    (G₁ ⊕g G₂).edgeSet.ncard = G₁.edgeSet.ncard + G₂.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr edgeSetSumEquiv, Nat.card_sum, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq]

/-- **The isolated vertices of a disjoint union** are those of the two graphs. -/
theorem isolatedVerts_sum :
    isolatedVerts (G₁ ⊕g G₂) = Sum.inl '' isolatedVerts G₁ ∪ Sum.inr '' isolatedVerts G₂ := by
  ext (u | u) <;> simp [isolatedVerts, Sum.forall]

/-- The number of isolated vertices of a disjoint union. -/
theorem ncard_isolatedVerts_sum [Finite V₁] [Finite V₂] :
    (isolatedVerts (G₁ ⊕g G₂)).ncard = (isolatedVerts G₁).ncard + (isolatedVerts G₂).ncard := by
  rw [isolatedVerts_sum, Set.ncard_union_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]
  rw [Set.disjoint_left]
  rintro _ ⟨u, -, rfl⟩ ⟨w, -, h⟩
  exact Sum.inr_ne_inl h

namespace RotationSystem

/-- **The Euler defect of a disjoint union** is the sum of the two defects: components,
vertices, edges, faces and isolated vertices all add up. -/
theorem eulerDefect_sum [Finite V₁] [Finite V₂] (ρ₁ : RotationSystem G₁)
    (ρ₂ : RotationSystem G₂) : (ρ₁.sum ρ₂).eulerDefect = ρ₁.eulerDefect + ρ₂.eulerDefect := by
  unfold eulerDefect completedFaceCount
  rw [natCard_connectedComponent_sum, Nat.card_sum, ncard_edgeSet_sum, natCard_face_sum,
    ncard_isolatedVerts_sum]
  push_cast
  ring

/-- **A disjoint union of spherical rotation systems is spherical.** -/
theorem IsSpherical.sum [Finite V₁] [Finite V₂] {ρ₁ : RotationSystem G₁}
    {ρ₂ : RotationSystem G₂} (h₁ : ρ₁.IsSpherical) (h₂ : ρ₂.IsSpherical) :
    (ρ₁.sum ρ₂).IsSpherical := by
  rw [isSpherical_iff_eulerDefect_eq_zero] at h₁ h₂ ⊢
  rw [eulerDefect_sum, h₁, h₂, add_zero]

end RotationSystem

/-- **A disjoint union of planar graphs is planar.** -/
theorem IsPlanar.sum [Finite V₁] [Finite V₂] (h₁ : IsPlanar G₁) (h₂ : IsPlanar G₂) :
    IsPlanar (G₁ ⊕g G₂) := by
  obtain ⟨ρ₁, hρ₁⟩ := h₁
  obtain ⟨ρ₂, hρ₂⟩ := h₂
  exact ⟨ρ₁.sum ρ₂, hρ₁.sum hρ₂⟩

end Sum

/-! ## Identifying two vertices in different components -/

section Identify

variable {W : Type*} {H : SimpleGraph W} {x₁ x₂ : W}

/-- Vertices that do not reach each other are distinct. -/
theorem identify_ne_of_not_reachable (h : ¬ H.Reachable x₁ x₂) : x₁ ≠ x₂ := by
  rintro rfl
  exact h .rfl

/-- Darts in different components lie on different faces. -/
private theorem RotationSystem.not_sameCycle_face_of_not_reachable (ρ : RotationSystem H)
    {a b : H.Dart} (h : ¬ H.Reachable a.fst b.fst) : ¬ ρ.face.SameCycle a b := fun hs =>
  h (ConnectedComponent.eq.mp (eq_of_sameCycle_of_forall
    (g := fun d : H.Dart => H.connectedComponentMk d.fst) ρ.connectedComponentMk_fst_face hs))

/-- The rotation keeps tails backwards too. -/
private theorem RotationSystem.fst_rot_inv (ρ : RotationSystem H) (d : H.Dart) :
    (ρ.rot⁻¹ d).fst = d.fst := by
  have := ρ.fst_rot (ρ.rot⁻¹ d)
  rw [Perm.inv_def, Equiv.apply_symm_apply] at this
  exact this.symm

/-- **Adding the edge `x₁x₂` and contracting it** is the same as identifying `x₂` with `x₁`. -/
private theorem contractEdge_sup_edge :
    contractEdge (H ⊔ edge x₁ x₂) x₁ x₂ = contractEdge H x₁ x₂ := by
  have key : ∀ r s : {v // v ≠ x₂}, (H ⊔ edge x₁ x₂).Adj r s ↔ H.Adj r s := fun r s => by
    rw [sup_adj, edge_adj]
    constructor
    · rintro (h | ⟨⟨-, h⟩ | ⟨h, -⟩, -⟩)
      · exact h
      · exact absurd h s.2
      · exact absurd h r.2
    · exact Or.inl
  have key2 : ∀ s : {v // v ≠ x₂}, (H ⊔ edge x₁ x₂).Adj x₂ s ↔ H.Adj x₂ s ∨ s.1 = x₁ :=
    fun s => by
      rw [sup_adj, edge_adj]
      constructor
      · rintro (h | ⟨⟨-, h⟩ | ⟨-, h⟩, -⟩)
        · exact Or.inl h
        · exact absurd h s.2
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr ⟨rfl, h⟩, fun h' => s.2 h'.symm⟩
  ext p q
  rw [contractEdge_adj, contractEdge_adj, key, key, key2, key2]
  constructor
  · rintro ⟨hpq, h'⟩
    refine ⟨hpq, ?_⟩
    rcases h' with (h' | ⟨hp, h' | hq⟩) | (h' | ⟨hq, h' | hp⟩)
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr ⟨hp, h'⟩)
    · exact absurd (Subtype.ext (hp.trans hq.symm)) hpq
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr ⟨hq, h'⟩)
    · exact absurd (Subtype.ext (hp.trans hq.symm)) hpq
  · rintro ⟨hpq, h'⟩
    refine ⟨hpq, ?_⟩
    rcases h' with (h' | ⟨hp, h'⟩) | (h' | ⟨hq, h'⟩)
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr ⟨hp, Or.inl h'⟩)
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr ⟨hq, Or.inl h'⟩)

/-- **Identifying two vertices in different components removes a component**: the identification
is the contraction of the edge `x₁x₂` added to `H`, which is a bridge. -/
theorem natCard_connectedComponent_contractEdge_add_one_of_not_reachable [Finite W]
    (h : ¬ H.Reachable x₁ x₂) :
    Nat.card (contractEdge H x₁ x₂).ConnectedComponent + 1 = Nat.card H.ConnectedComponent := by
  have hne := identify_ne_of_not_reachable h
  have hadj : (H ⊔ edge x₁ x₂).Adj x₁ x₂ :=
    (sup_adj _ _ _ _).mpr (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩))
  have hdel : (H ⊔ edge x₁ x₂).deleteEdges {s(x₁, x₂)} = H := by
    ext u w
    rw [deleteEdges_adj, sup_adj, edge_adj, Set.mem_singleton_iff]
    constructor
    · rintro ⟨huw | ⟨huw, -⟩, hne'⟩
      · exact huw
      · exfalso
        apply hne'
        rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
    · intro huw
      refine ⟨Or.inl huw, fun he => h ?_⟩
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huw.reachable
      · exact huw.reachable.symm
  have hbr : (H ⊔ edge x₁ x₂).IsBridge s(x₁, x₂) := isBridge_iff.mpr (by rw [hdel]; exact h)
  have hC : Nat.card ((H ⊔ edge x₁ x₂).deleteEdges {s(x₁, x₂)}).ConnectedComponent =
      Nat.card (H ⊔ edge x₁ x₂).ConnectedComponent + 1 :=
    natCard_connectedComponent_deleteEdges_of_isBridge (a := ⟨(x₁, x₂), hadj⟩) hbr
  have hK := natCard_connectedComponent_contractEdge hadj
  rw [hdel] at hC
  rw [contractEdge_sup_edge] at hK
  omega

private theorem ncard_preimage_val_of_notMem [Finite W] {S : Set W} (hS : x₂ ∉ S) :
    (Subtype.val ⁻¹' S : Set {v // v ≠ x₂}).ncard = S.ncard :=
  Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
    fun v hv => ⟨⟨v, fun h => hS (h ▸ hv)⟩, rfl⟩

variable [DecidableEq W]

/-- **The edges of `H` survive the identification** of two vertices in different components. -/
theorem contractEdge_adj_contractVertex_of_not_reachable (h : ¬ H.Reachable x₁ x₂) {u w : W}
    (huw : H.Adj u w) :
    (contractEdge H x₁ x₂).Adj (contractVertex (identify_ne_of_not_reachable h) u)
      (contractVertex (identify_ne_of_not_reachable h) w) := by
  have hne := identify_ne_of_not_reachable h
  rw [contractEdge_adj]
  refine ⟨fun hq => ?_, ?_⟩
  · rcases (contractVertex_eq_iff hne).mp hq with huw' | ⟨hu | hu, hw | hw⟩
    · exact huw.ne huw'
    · exact huw.ne (hu.trans hw.symm)
    · exact h (hu ▸ hw ▸ huw.reachable)
    · exact h (hw ▸ hu ▸ huw.reachable.symm)
    · exact huw.ne (hu.trans hw.symm)
  · by_cases hu : u = x₂
    · have hw : w ≠ x₂ := fun hw => huw.ne (hu.trans hw.symm)
      rw [hu, contractVertex_self, contractVertex_of_ne _ hw]
      exact Or.inl (Or.inr ⟨rfl, hu ▸ huw⟩)
    · by_cases hw : w = x₂
      · rw [hw, contractVertex_self, contractVertex_of_ne _ hu]
        exact Or.inr (Or.inr ⟨rfl, hw ▸ huw.symm⟩)
      · rw [contractVertex_of_ne _ hu, contractVertex_of_ne _ hw]
        exact Or.inl (Or.inl huw)

/-- A dart of `H`, after identifying two vertices in different components. -/
def identifyDart (h : ¬ H.Reachable x₁ x₂) (d : H.Dart) : (contractEdge H x₁ x₂).Dart :=
  ⟨(contractVertex (identify_ne_of_not_reachable h) d.fst,
      contractVertex (identify_ne_of_not_reachable h) d.snd),
    contractEdge_adj_contractVertex_of_not_reachable h d.adj⟩

theorem identifyDart_injective (h : ¬ H.Reachable x₁ x₂) :
    Function.Injective (identifyDart h) := by
  have hne := identify_ne_of_not_reachable h
  -- Two of the identified vertices that reach each other are equal.
  have hr : ∀ {u w : W}, (u = x₁ ∨ u = x₂) → (w = x₁ ∨ w = x₂) → H.Reachable u w → u = w := by
    rintro u w (rfl | rfl) (rfl | rfl) huw
    · rfl
    · exact absurd huw h
    · exact absurd huw.symm h
    · rfl
  intro d d' hdd
  have h1 : contractVertex hne d.fst = contractVertex hne d'.fst :=
    congrArg (fun d : (contractEdge H x₁ x₂).Dart => d.fst) hdd
  have h2 : contractVertex hne d.snd = contractVertex hne d'.snd :=
    congrArg (fun d : (contractEdge H x₁ x₂).Dart => d.snd) hdd
  rw [contractVertex_eq_iff] at h1 h2
  have hd := d.adj.reachable
  have hd' := d'.adj.reachable
  have hfst : d.fst = d'.fst := by
    rcases h1 with h1 | ⟨hu, hu'⟩
    · exact h1
    · rcases h2 with h2 | ⟨hw, -⟩
      · exact hr hu hu' (hd.trans (by rw [h2]; exact hd'.symm))
      · exact absurd (hr hu hw hd) d.adj.ne
  have hsnd : d.snd = d'.snd := by
    rcases h2 with h2 | ⟨hw, hw'⟩
    · exact h2
    · exact hr hw hw' (hd.symm.trans (by rw [hfst]; exact hd'))
  exact Dart.ext _ _ (Prod.ext hfst hsnd)

theorem identifyDart_surjective (h : ¬ H.Reachable x₁ x₂) :
    Function.Surjective (identifyDart h) := by
  have hne := identify_ne_of_not_reachable h
  rintro ⟨⟨p, q⟩, hpq⟩
  obtain ⟨-, (hadj | ⟨hp, hadj⟩) | (hadj | ⟨hq, hadj⟩)⟩ := contractEdge_adj.mp hpq
  · exact ⟨⟨(p.1, q.1), hadj⟩,
      Dart.ext _ _ (Prod.ext (contractVertex_val hne p) (contractVertex_val hne q))⟩
  · refine ⟨⟨(x₂, q.1), hadj⟩, Dart.ext _ _ (Prod.ext ?_ (contractVertex_val hne q))⟩
    change contractVertex hne x₂ = p
    rw [contractVertex_self]
    exact Subtype.ext hp.symm
  · exact ⟨⟨(p.1, q.1), hadj.symm⟩,
      Dart.ext _ _ (Prod.ext (contractVertex_val hne p) (contractVertex_val hne q))⟩
  · refine ⟨⟨(p.1, x₂), hadj.symm⟩, Dart.ext _ _ (Prod.ext (contractVertex_val hne p) ?_)⟩
    change contractVertex hne x₂ = q
    rw [contractVertex_self]
    exact Subtype.ext hq.symm

/-- **The darts after identifying two vertices in different components** are those of `H`: no
edge joins the two vertices, and they have no common neighbour. -/
noncomputable def identifyDartEquiv (h : ¬ H.Reachable x₁ x₂) :
    H.Dart ≃ (contractEdge H x₁ x₂).Dart :=
  Equiv.ofBijective (identifyDart h) ⟨identifyDart_injective h, identifyDart_surjective h⟩

theorem fst_identifyDartEquiv (h : ¬ H.Reachable x₁ x₂) (d : H.Dart) :
    (identifyDartEquiv h d).fst = contractVertex (identify_ne_of_not_reachable h) d.fst := rfl

theorem identifyDartEquiv_symm (h : ¬ H.Reachable x₁ x₂) (d : H.Dart) :
    identifyDartEquiv h d.symm = (identifyDartEquiv h d).symm := rfl

theorem identifyDartEquiv_symm_apply_symm (h : ¬ H.Reachable x₁ x₂)
    (d : (contractEdge H x₁ x₂).Dart) :
    (identifyDartEquiv h).symm d.symm = ((identifyDartEquiv h).symm d).symm := by
  apply (identifyDartEquiv h).injective
  rw [apply_symm_apply, identifyDartEquiv_symm, apply_symm_apply]

omit [DecidableEq W] in
/-- **The edges after identifying two vertices in different components** are those of `H`. -/
theorem ncard_edgeSet_contractEdge_of_not_reachable [Finite W] (h : ¬ H.Reachable x₁ x₂) :
    (contractEdge H x₁ x₂).edgeSet.ncard = H.edgeSet.ncard := by
  classical
  have h1 := two_mul_ncard_edgeSet_eq_natCard_dart (G := H)
  have h2 := two_mul_ncard_edgeSet_eq_natCard_dart (G := contractEdge H x₁ x₂)
  rw [← Nat.card_congr (identifyDartEquiv h)] at h2
  omega

/-- The transposition of a dart at `x₁` and a dart at `x₂` keeps the tails, up to the
identification. -/
private theorem contractVertex_fst_swap (hne : x₁ ≠ x₂) {a b : H.Dart} (ha : a.fst = x₁)
    (hb : b.fst = x₂) (z : H.Dart) :
    contractVertex hne (swap a b z).fst = contractVertex hne z.fst := by
  rcases eq_or_ne z a with rfl | hza
  · rw [swap_apply_left, ha, hb, contractVertex_self, contractVertex_of_ne hne hne]
  · rcases eq_or_ne z b with rfl | hzb
    · rw [swap_apply_right, ha, hb, contractVertex_self, contractVertex_of_ne hne hne]
    · rw [swap_apply_of_ne_of_ne hza hzb]

omit [DecidableEq W] in
/-- **The isolated vertices after identifying two vertices in different components**: a vertex
is isolated when it was, and the merged vertex when both were. -/
theorem mem_isolatedVerts_contractEdge_iff_of_not_reachable (h : ¬ H.Reachable x₁ x₂)
    (p : {v // v ≠ x₂}) :
    p ∈ isolatedVerts (contractEdge H x₁ x₂) ↔
      p.1 ∈ isolatedVerts H ∧ (p.1 = x₁ → x₂ ∈ isolatedVerts H) := by
  classical
  have hne := identify_ne_of_not_reachable h
  constructor
  · intro hp
    refine ⟨fun w hw => ?_, fun hp1 w hw => ?_⟩
    · have := contractEdge_adj_contractVertex_of_not_reachable h hw
      rw [contractVertex_val] at this
      exact hp _ this
    · have := contractEdge_adj_contractVertex_of_not_reachable h hw
      rw [contractVertex_self, show (⟨x₁, hne⟩ : {v // v ≠ x₂}) = p from
        Subtype.ext hp1.symm] at this
      exact hp _ this
  · rintro ⟨hp, hp'⟩ q hq
    obtain ⟨-, (h' | ⟨hp1, h'⟩) | (h' | ⟨-, h'⟩)⟩ := contractEdge_adj.mp hq
    · exact hp _ h'
    · exact hp' hp1 _ h'
    · exact hp _ h'.symm
    · exact hp _ h'.symm

omit [DecidableEq W] in
/-- **The isolated vertices after identifying two vertices in different components, one of
them isolated**: one fewer. -/
theorem ncard_isolatedVerts_contractEdge_add_one_of_not_reachable [Finite W]
    (h : ¬ H.Reachable x₁ x₂) (hI : x₁ ∈ isolatedVerts H ∨ x₂ ∈ isolatedVerts H) :
    (isolatedVerts (contractEdge H x₁ x₂)).ncard + 1 = (isolatedVerts H).ncard := by
  by_cases h₂ : x₂ ∈ isolatedVerts H
  · have hset : isolatedVerts (contractEdge H x₁ x₂) =
        Subtype.val ⁻¹' (isolatedVerts H \ {x₂}) := by
      ext p
      rw [Set.mem_preimage, mem_isolatedVerts_contractEdge_iff_of_not_reachable h, Set.mem_sdiff,
        Set.mem_singleton_iff]
      exact ⟨fun hp => ⟨hp.1, p.2⟩, fun hp => ⟨hp.1, fun _ => h₂⟩⟩
    rw [hset, ncard_preimage_val_of_notMem (fun hx => hx.2 rfl),
      Set.ncard_sdiff_singleton_add_one h₂]
  · have h₁ := hI.resolve_right h₂
    have hset : isolatedVerts (contractEdge H x₁ x₂) =
        Subtype.val ⁻¹' (isolatedVerts H \ {x₁}) := by
      ext p
      rw [Set.mem_preimage, mem_isolatedVerts_contractEdge_iff_of_not_reachable h, Set.mem_sdiff,
        Set.mem_singleton_iff]
      exact ⟨fun hp => ⟨hp.1, fun hp1 => h₂ (hp.2 hp1)⟩,
        fun hp => ⟨hp.1, fun hp1 => absurd hp1 hp.2⟩⟩
    rw [hset, ncard_preimage_val_of_notMem (fun hx => h₂ hx.1),
      Set.ncard_sdiff_singleton_add_one h₁]

omit [DecidableEq W] in
/-- **The isolated vertices after identifying two vertices in different components, neither of
them isolated**: as many as before. -/
theorem ncard_isolatedVerts_contractEdge_of_not_reachable [Finite W] (h : ¬ H.Reachable x₁ x₂)
    (h₁ : x₁ ∉ isolatedVerts H) (h₂ : x₂ ∉ isolatedVerts H) :
    (isolatedVerts (contractEdge H x₁ x₂)).ncard = (isolatedVerts H).ncard := by
  have hset : isolatedVerts (contractEdge H x₁ x₂) = Subtype.val ⁻¹' isolatedVerts H := by
    ext p
    rw [Set.mem_preimage, mem_isolatedVerts_contractEdge_iff_of_not_reachable h]
    exact ⟨fun hp => hp.1, fun hp => ⟨hp, fun hp1 => absurd (hp1 ▸ hp) h₁⟩⟩
  rw [hset, ncard_preimage_val_of_notMem h₂]

namespace RotationSystem

variable (ρ : RotationSystem H)

/-- **Identifying with a vertex without darts**: when `x₁` or `x₂` is isolated, the rotation of
`H` carried along the darts. -/
noncomputable def identifyPlain (h : ¬ H.Reachable x₁ x₂)
    (hI : x₁ ∈ isolatedVerts H ∨ x₂ ∈ isolatedVerts H) :
    RotationSystem (contractEdge H x₁ x₂) where
  rot := (identifyDartEquiv h).permCongr ρ.rot
  fst_rot d := by
    obtain ⟨z, rfl⟩ := (identifyDartEquiv h).surjective d
    rw [permCongr_apply, symm_apply_apply, fst_identifyDartEquiv, fst_identifyDartEquiv,
      ρ.fst_rot]
  sameCycle_rot d d' hdd := by
    obtain ⟨z, rfl⟩ := (identifyDartEquiv h).surjective d
    obtain ⟨z', rfl⟩ := (identifyDartEquiv h).surjective d'
    rw [sameCycle_permCongr]
    rw [fst_identifyDartEquiv, fst_identifyDartEquiv, contractVertex_eq_iff] at hdd
    refine ρ.sameCycle_rot z z' ?_
    have hz : ∀ z : H.Dart, z.fst ∉ isolatedVerts H := fun z hz => hz z.snd z.adj
    rcases hdd with hdd | ⟨hu | hu, hw | hw⟩
    · exact hdd
    · exact hu.trans hw.symm
    · exact (hI.elim (fun hI => hz z (hu ▸ hI)) fun hI => hz z' (hw ▸ hI)).elim
    · exact (hI.elim (fun hI => hz z' (hw ▸ hI)) fun hI => hz z (hu ▸ hI)).elim
    · exact hu.trans hw.symm

theorem identifyPlain_face (h : ¬ H.Reachable x₁ x₂)
    (hI : x₁ ∈ isolatedVerts H ∨ x₂ ∈ isolatedVerts H) :
    (ρ.identifyPlain h hI).face = (identifyDartEquiv h).permCongr ρ.face := by
  refine Equiv.ext fun d => ?_
  rw [face_apply]
  change identifyDartEquiv h (ρ.rot ((identifyDartEquiv h).symm d.symm)) =
    identifyDartEquiv h (ρ.face ((identifyDartEquiv h).symm d))
  rw [identifyDartEquiv_symm_apply_symm]
  rfl

/-- **Splicing the rotations at `x₁` and `x₂`**: the rotation of `H` after the transposition of
a dart `a` at `x₁` and a dart `b` at `x₂`, which merges the two vertex cycles into one. -/
noncomputable def identifySplice [Finite W] (h : ¬ H.Reachable x₁ x₂) {a b : H.Dart}
    (ha : a.fst = x₁) (hb : b.fst = x₂) : RotationSystem (contractEdge H x₁ x₂) where
  rot := (identifyDartEquiv h).permCongr (swap a b * ρ.rot)
  fst_rot d := by
    obtain ⟨z, rfl⟩ := (identifyDartEquiv h).surjective d
    rw [permCongr_apply, symm_apply_apply, fst_identifyDartEquiv, fst_identifyDartEquiv,
      mul_apply, contractVertex_fst_swap _ ha hb, ρ.fst_rot]
  sameCycle_rot d d' hdd := by
    have := finite_dart (G := H)
    obtain ⟨z, rfl⟩ := (identifyDartEquiv h).surjective d
    obtain ⟨z', rfl⟩ := (identifyDartEquiv h).surjective d'
    have hne := identify_ne_of_not_reachable h
    -- `swap a b * rot = rot * swap (rot⁻¹ a) (rot⁻¹ b)` joins the vertex cycles at `x₁` and `x₂`.
    have hab : ¬ ρ.rot.SameCycle (ρ.rot⁻¹ a) (ρ.rot⁻¹ b) := fun hs => by
      have := eq_of_sameCycle_of_forall (g := fun d : H.Dart => d.fst) ρ.fst_rot hs
      rw [ρ.fst_rot_inv, ρ.fst_rot_inv, ha, hb] at this
      exact hne this
    rw [sameCycle_permCongr, swap_mul_eq_mul_swap, sameCycle_mul_swap_iff_of_not_sameCycle hab]
    rw [fst_identifyDartEquiv, fst_identifyDartEquiv, contractVertex_eq_iff] at hdd
    have ha' : (ρ.rot⁻¹ a).fst = x₁ := (ρ.fst_rot_inv a).trans ha
    have hb' : (ρ.rot⁻¹ b).fst = x₂ := (ρ.fst_rot_inv b).trans hb
    rcases hdd with hdd | ⟨hu | hu, hw | hw⟩
    · exact Or.inl (ρ.sameCycle_rot z z' hdd)
    · exact Or.inl (ρ.sameCycle_rot z z' (hu.trans hw.symm))
    · exact Or.inr ⟨Or.inl (ρ.sameCycle_rot _ _ (hu.trans ha'.symm)),
        Or.inr (ρ.sameCycle_rot _ _ (hw.trans hb'.symm))⟩
    · exact Or.inr ⟨Or.inr (ρ.sameCycle_rot _ _ (hu.trans hb'.symm)),
        Or.inl (ρ.sameCycle_rot _ _ (hw.trans ha'.symm))⟩
    · exact Or.inl (ρ.sameCycle_rot z z' (hu.trans hw.symm))

/-- **The faces after splicing**: the face permutation of `H` after the transposition of `a` and
`b`. -/
theorem identifySplice_face [Finite W] (h : ¬ H.Reachable x₁ x₂) {a b : H.Dart}
    (ha : a.fst = x₁) (hb : b.fst = x₂) :
    (ρ.identifySplice h ha hb).face = (identifyDartEquiv h).permCongr (swap a b * ρ.face) := by
  refine Equiv.ext fun d => ?_
  rw [face_apply]
  change identifyDartEquiv h ((swap a b * ρ.rot) ((identifyDartEquiv h).symm d.symm)) =
    identifyDartEquiv h ((swap a b * ρ.face) ((identifyDartEquiv h).symm d))
  rw [identifyDartEquiv_symm_apply_symm]
  rfl

omit [DecidableEq W] in
/-- The darts before `a` and `b` in their faces lie on different faces. -/
private theorem not_sameCycle_face_inv (h : ¬ H.Reachable x₁ x₂) {a b : H.Dart} (ha : a.fst = x₁)
    (hb : b.fst = x₂) : ¬ ρ.face.SameCycle (ρ.face⁻¹ a) (ρ.face⁻¹ b) := fun hs =>
  ρ.not_sameCycle_face_of_not_reachable (by rw [ha, hb]; exact h)
    (sameCycle_symm_apply_right.mp (sameCycle_symm_apply_left.mp hs))

/-- **Splicing merges the faces of `a` and `b`**: one face fewer. -/
theorem natCard_face_identifySplice_add_one [Finite W] (h : ¬ H.Reachable x₁ x₂)
    {a b : H.Dart} (ha : a.fst = x₁) (hb : b.fst = x₂) :
    Nat.card (ρ.identifySplice h ha hb).Face + 1 = Nat.card ρ.Face := by
  have := finite_dart (G := H)
  change cycleCount (ρ.identifySplice h ha hb).face + 1 = cycleCount ρ.face
  rw [identifySplice_face, cycleCount_permCongr, swap_mul_eq_mul_swap]
  exact cycleCount_mul_swap_of_not_sameCycle (ρ.not_sameCycle_face_inv h ha hb)

/-- **The merged face** contains the face of `a` and the face of `b`. -/
theorem sameCycle_identifySplice_face [Finite W] (h : ¬ H.Reachable x₁ x₂) {a b : H.Dart}
    (ha : a.fst = x₁) (hb : b.fst = x₂) {d e : H.Dart} (hd : ρ.face.SameCycle a d)
    (he : ρ.face.SameCycle b e) :
    (ρ.identifySplice h ha hb).face.SameCycle (identifyDartEquiv h d)
      (identifyDartEquiv h e) := by
  have := finite_dart (G := H)
  rw [identifySplice_face, sameCycle_permCongr, swap_mul_eq_mul_swap,
    sameCycle_mul_swap_iff_of_not_sameCycle (ρ.not_sameCycle_face_inv h ha hb)]
  exact Or.inr ⟨Or.inl (sameCycle_symm_apply_right.mpr hd.symm),
    Or.inr (sameCycle_symm_apply_right.mpr he.symm)⟩

/-- **Identifying with a vertex without darts keeps the Euler defect**: one component, one vertex
and one isolated vertex fewer. -/
theorem eulerDefect_identifyPlain [Finite W] (h : ¬ H.Reachable x₁ x₂)
    (hI : x₁ ∈ isolatedVerts H ∨ x₂ ∈ isolatedVerts H) :
    (ρ.identifyPlain h hI).eulerDefect = ρ.eulerDefect := by
  have := finite_dart (G := H)
  have hC := natCard_connectedComponent_contractEdge_add_one_of_not_reachable h
  have hV := natCard_subtype_ne_add_one x₂
  have hE := ncard_edgeSet_contractEdge_of_not_reachable h
  have hF : Nat.card (ρ.identifyPlain h hI).Face = Nat.card ρ.Face := by
    change cycleCount (ρ.identifyPlain h hI).face = cycleCount ρ.face
    rw [identifyPlain_face, cycleCount_permCongr]
  have hI' := ncard_isolatedVerts_contractEdge_add_one_of_not_reachable h hI
  unfold eulerDefect completedFaceCount
  rw [hE, hF]
  omega

/-- **Splicing keeps the Euler defect**: one component, one vertex and one face fewer. -/
theorem eulerDefect_identifySplice [Finite W] (h : ¬ H.Reachable x₁ x₂) {a b : H.Dart}
    (ha : a.fst = x₁) (hb : b.fst = x₂) :
    (ρ.identifySplice h ha hb).eulerDefect = ρ.eulerDefect := by
  have hC := natCard_connectedComponent_contractEdge_add_one_of_not_reachable h
  have hV := natCard_subtype_ne_add_one x₂
  have hE := ncard_edgeSet_contractEdge_of_not_reachable h
  have hF := ρ.natCard_face_identifySplice_add_one h ha hb
  have hI := ncard_isolatedVerts_contractEdge_of_not_reachable h
    (fun hI => hI a.snd (ha ▸ a.adj)) (fun hI => hI b.snd (hb ▸ b.adj))
  unfold eulerDefect completedFaceCount
  rw [hE, hI]
  omega

end RotationSystem

end Identify

/-! ## Gluing two graphs at a vertex -/

section GlueVertex

variable {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}

/-- **A dart of the left graph** in the gluing `contractEdge (G₁ ⊕g G₂) (.inl x₁) (.inr x₂)` of
`G₁` and `G₂` at `x₁` and `x₂`. -/
noncomputable def glueDartLeft (x₁ : V₁) (x₂ : V₂) (d : G₁.Dart) :
    (contractEdge (G₁ ⊕g G₂) (.inl x₁) (.inr x₂)).Dart :=
  letI := Classical.decEq (V₁ ⊕ V₂)
  identifyDartEquiv (not_reachable_sum_inl_inr x₁ x₂) (sumDartEquiv (.inl d))

/-- **A dart of the right graph** in the gluing `contractEdge (G₁ ⊕g G₂) (.inl x₁) (.inr x₂)` of
`G₁` and `G₂` at `x₁` and `x₂`. -/
noncomputable def glueDartRight (x₁ : V₁) (x₂ : V₂) (d : G₂.Dart) :
    (contractEdge (G₁ ⊕g G₂) (.inl x₁) (.inr x₂)).Dart :=
  letI := Classical.decEq (V₁ ⊕ V₂)
  identifyDartEquiv (not_reachable_sum_inl_inr x₁ x₂) (sumDartEquiv (.inr d))

/-- A dart of the left graph keeps its tail. -/
theorem fst_glueDartLeft (x₁ : V₁) (x₂ : V₂) (d : G₁.Dart) :
    (glueDartLeft (G₂ := G₂) x₁ x₂ d).fst = ⟨.inl d.fst, Sum.inl_ne_inr⟩ := by
  let _ := Classical.decEq (V₁ ⊕ V₂)
  exact contractVertex_of_ne _ Sum.inl_ne_inr

/-- A dart of the right graph keeps its tail, unless that is the glued vertex. -/
theorem fst_glueDartRight (x₁ : V₁) {x₂ : V₂} (d : G₂.Dart) (hd : d.fst ≠ x₂) :
    (glueDartRight (G₁ := G₁) x₁ x₂ d).fst = ⟨.inr d.fst, fun h => hd (Sum.inr.inj h)⟩ := by
  let _ := Classical.decEq (V₁ ⊕ V₂)
  exact contractVertex_of_ne _ _

/-- **Gluing two spherical rotation systems at a vertex, keeping two faces together**: for darts
`a` at `x₁` and `b` at `x₂`, the gluing of `G₁` and `G₂` at `x₁` and `x₂` has a spherical
rotation system in which the faces of `a` and of `b` lie in one face. -/
theorem exists_isSpherical_glueVertex [Finite V₁] [Finite V₂] {ρ₁ : RotationSystem G₁}
    {ρ₂ : RotationSystem G₂} (h₁ : ρ₁.IsSpherical) (h₂ : ρ₂.IsSpherical) {x₁ : V₁} {x₂ : V₂}
    {a : G₁.Dart} {b : G₂.Dart} (ha : a.fst = x₁) (hb : b.fst = x₂) :
    ∃ σ : RotationSystem (contractEdge (G₁ ⊕g G₂) (.inl x₁) (.inr x₂)), σ.IsSpherical ∧
      ∀ ⦃d : G₁.Dart⦄ ⦃e : G₂.Dart⦄, ρ₁.face.SameCycle a d → ρ₂.face.SameCycle b e →
        σ.face.SameCycle (glueDartLeft x₁ x₂ d) (glueDartRight x₁ x₂ e) := by
  let _ := Classical.decEq (V₁ ⊕ V₂)
  have h := not_reachable_sum_inl_inr (G := G₁) (H := G₂) x₁ x₂
  have hτ := (RotationSystem.isSpherical_iff_eulerDefect_eq_zero (ρ₁.sum ρ₂)).mp (h₁.sum h₂)
  have ha' : (sumDartEquiv (.inl a) : (G₁ ⊕g G₂).Dart).fst = .inl x₁ := congrArg Sum.inl ha
  have hb' : (sumDartEquiv (.inr b) : (G₁ ⊕g G₂).Dart).fst = .inr x₂ := congrArg Sum.inr hb
  refine ⟨(ρ₁.sum ρ₂).identifySplice h ha' hb', ?_, fun d e hd he => ?_⟩
  · rw [RotationSystem.isSpherical_iff_eulerDefect_eq_zero,
      RotationSystem.eulerDefect_identifySplice, hτ]
  · exact (ρ₁.sum ρ₂).sameCycle_identifySplice_face h ha' hb'
      ((ρ₁.sameCycle_sum_face_inl ρ₂).mpr hd) ((ρ₁.sameCycle_sum_face_inr ρ₂).mpr he)

/-- **Gluing two planar graphs at a vertex gives a planar graph.** -/
theorem IsPlanar.glueVertex [Finite V₁] [Finite V₂] (h₁ : IsPlanar G₁) (h₂ : IsPlanar G₂)
    (x₁ : V₁) (x₂ : V₂) : IsPlanar (Graph.contractEdge (G₁ ⊕g G₂) (.inl x₁) (.inr x₂)) := by
  classical
  obtain ⟨ρ₁, hρ₁⟩ := h₁
  obtain ⟨ρ₂, hρ₂⟩ := h₂
  have h := not_reachable_sum_inl_inr (G := G₁) (H := G₂) x₁ x₂
  have hτ := (RotationSystem.isSpherical_iff_eulerDefect_eq_zero (ρ₁.sum ρ₂)).mp (hρ₁.sum hρ₂)
  by_cases hI : (Sum.inl x₁ : V₁ ⊕ V₂) ∈ isolatedVerts (G₁ ⊕g G₂) ∨
      (Sum.inr x₂ : V₁ ⊕ V₂) ∈ isolatedVerts (G₁ ⊕g G₂)
  · refine ⟨(ρ₁.sum ρ₂).identifyPlain h hI, ?_⟩
    rw [RotationSystem.isSpherical_iff_eulerDefect_eq_zero,
      RotationSystem.eulerDefect_identifyPlain, hτ]
  · obtain ⟨hI₁, hI₂⟩ := not_or.mp hI
    simp only [isolatedVerts, Set.mem_ofPred_eq, not_forall, not_not] at hI₁ hI₂
    obtain ⟨w₁, hw₁⟩ := hI₁
    obtain ⟨w₂, hw₂⟩ := hI₂
    refine ⟨(ρ₁.sum ρ₂).identifySplice h (a := ⟨(.inl x₁, w₁), hw₁⟩)
      (b := ⟨(.inr x₂, w₂), hw₂⟩) rfl rfl, ?_⟩
    rw [RotationSystem.isSpherical_iff_eulerDefect_eq_zero,
      RotationSystem.eulerDefect_identifySplice, hτ]

end GlueVertex

end MonoidProduct.Graph
