import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import MonoidProduct.Graph.VertexCertificate
set_option linter.style.header false

/-!
# Graph minors

`monoid.tex`, section `sec:graph-certificates`, paragraph "Planarity and minor-closed
properties": every fixed proper minor-closed graph class has a linear edge bound.  Mathlib has no
graph minors; they are defined here by minor models (Diestel, *Graph Theory*, Section 1.7).

* `IsConnectedSet G s`: `s` is nonempty and any two of its vertices are joined by a walk inside
  `s`, that is, Mathlib's `(G.induce s).Connected` (`isConnectedSet_iff`).
* `MinorModel H G`: disjoint connected branch sets of `G`, one for each vertex of `H`, with an
  edge of `G` between the branch sets of any two adjacent vertices of `H`.  `IsMinor H G` when
  one exists: `H` is isomorphic to a graph obtained from a subgraph of `G` by contracting
  connected sets.  `H` and `G` may have different vertex types.
* Minors are reflexive and transitive (`MinorModel.trans`); injective homomorphic images,
  subgraphs and induced subgraphs are minors (`MinorModel.ofInjective`).
* `contractEdge G x y`: contracting the edge `xy`, on `V \ {y}`, where `x` also takes the
  neighbours of `y`.  It is a minor of `G` (`MinorModel.ofContractEdge`) and loses at most
  `1 + |N(x) ∩ N(y)|` edges (`ncard_edgeSet_le_contractEdge`).
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {U V W : Type*}

/-! ## Connected vertex sets -/

/-- The edges of `G` with both ends in `s`, as a graph on all of `V`. -/
def restrictTo (G : SimpleGraph V) (s : Set V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ s ∧ b ∈ s
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

@[simp] theorem restrictTo_adj {G : SimpleGraph V} {s : Set V} {a b : V} :
    (restrictTo G s).Adj a b ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s := Iff.rfl

theorem restrictTo_mono {G : SimpleGraph V} {s t : Set V} (h : s ⊆ t) :
    restrictTo G s ≤ restrictTo G t :=
  fun _ _ hab => ⟨hab.1, h hab.2.1, h hab.2.2⟩

/-- **A connected vertex set**: nonempty, with any two of its vertices joined by a walk inside
it. -/
def IsConnectedSet (G : SimpleGraph V) (s : Set V) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, (restrictTo G s).Reachable a b

/-- Connected vertex sets are those inducing connected subgraphs. -/
theorem isConnectedSet_iff {G : SimpleGraph V} {s : Set V} :
    IsConnectedSet G s ↔ (G.induce s).Connected := by
  rw [connected_iff]
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    exact ⟨fun a b => (reachable_induce_iff (G' := restrictTo G s) (fun _ _ => Iff.rfl)
      a.2 b.2).mpr (h a a.2 b b.2), ⟨⟨v, hv⟩⟩⟩
  · rintro ⟨h, ⟨v⟩⟩
    exact ⟨⟨v, v.2⟩, fun a ha b hb => (reachable_induce_iff (G' := restrictTo G s)
      (fun _ _ => Iff.rfl) ha hb).mp (h ⟨a, ha⟩ ⟨b, hb⟩)⟩

theorem isConnectedSet_singleton (G : SimpleGraph V) (v : V) : IsConnectedSet G {v} :=
  ⟨⟨v, rfl⟩, fun a ha b hb => by rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]⟩

/-- The ends of an edge form a connected set. -/
theorem isConnectedSet_pair {G : SimpleGraph V} {x y : V} (h : G.Adj x y) :
    IsConnectedSet G {x, y} := by
  have hxy : (restrictTo G {x, y}).Adj x y := ⟨h, Set.mem_insert _ _, by simp⟩
  refine ⟨⟨x, Set.mem_insert _ _⟩, fun a ha b hb => ?_⟩
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · rfl
  · rw [Set.mem_singleton_iff.mp hb]
    exact hxy.reachable
  · rw [Set.mem_singleton_iff.mp ha]
    exact hxy.reachable.symm
  · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]

/-- **Homomorphisms map connected sets to connected sets.** -/
theorem IsConnectedSet.image {G : SimpleGraph V} {G' : SimpleGraph W} (f : G →g G') {s : Set V}
    (h : IsConnectedSet G s) : IsConnectedSet G' (f '' s) := by
  refine ⟨h.1.image f, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  let φ : restrictTo G s →g restrictTo G' (f '' s) :=
    ⟨f, fun {x y} hxy => ⟨f.map_adj hxy.1, ⟨x, hxy.2.1, rfl⟩, ⟨y, hxy.2.2, rfl⟩⟩⟩
  exact (h.2 a ha b hb).map φ

/-- **Gluing connected pieces**: if the pieces `B w` for `w` in `S` are connected and adjacent
indices of `S` have adjacent pieces, then pieces over indices joined inside `S` are joined inside
the union. -/
theorem reachable_biUnion {H : SimpleGraph W} {G : SimpleGraph V} {S : Set W} {B : W → Set V}
    (hB : ∀ w ∈ S, IsConnectedSet G (B w))
    (hadj : ∀ w w', w ∈ S → w' ∈ S → H.Adj w w' → ∃ a ∈ B w, ∃ b ∈ B w', G.Adj a b)
    {w w' : W} (hww' : (restrictTo H S).Reachable w w') (hw : w ∈ S) {a b : V} (ha : a ∈ B w)
    (hb : b ∈ B w') : (restrictTo G (⋃ x ∈ S, B x)).Reachable a b := by
  have hsub : ∀ x ∈ S, B x ⊆ ⋃ x ∈ S, B x := fun x hx => Set.subset_biUnion_of_mem hx
  rw [reachable_iff_reflTransGen] at hww'
  induction hww' generalizing b with
  | refl => exact ((hB w hw).2 a ha b hb).mono (restrictTo_mono (hsub w hw))
  | tail _ hxy ih =>
      obtain ⟨hxy, hx, hy⟩ := hxy
      obtain ⟨a', ha', b', hb', hab'⟩ := hadj _ _ hx hy hxy
      exact (ih ha').trans
        ((restrictTo_adj.mpr ⟨hab', hsub _ hx ha', hsub _ hy hb'⟩).reachable.trans
          (((hB _ hy).2 b' hb' b hb).mono (restrictTo_mono (hsub _ hy))))

/-! ## Minor models -/

/-- **A minor model of `H` in `G`** (Diestel, *Graph Theory*, Section 1.7): disjoint connected
branch sets of `G`, one for each vertex of `H`, with an edge of `G` between the branch sets of any
two adjacent vertices of `H`. -/
structure MinorModel (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set of a vertex of `H`. -/
  branch : W → Set V
  connected : ∀ w, IsConnectedSet G (branch w)
  disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  adj : ∀ w w', H.Adj w w' → ∃ a ∈ branch w, ∃ b ∈ branch w', G.Adj a b

/-- **`H` is a minor of `G`**: `H` has a minor model in `G`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel H G)

namespace MinorModel

/-- **Injective homomorphic images are minors**, with singleton branch sets. -/
def ofInjective {H : SimpleGraph W} {G : SimpleGraph V} (f : H →g G)
    (hf : Function.Injective f) : MinorModel H G where
  branch w := {f w}
  connected w := isConnectedSet_singleton G (f w)
  disjoint _ _ h := Set.disjoint_singleton.mpr fun he => h (hf he)
  adj w w' h := ⟨f w, rfl, f w', rfl, f.map_adj h⟩

/-- **Minors of minors are minors**: the branch set of `u` is the union of the branch sets of the
vertices in its branch set. -/
def trans {K : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} (m₁ : MinorModel K H)
    (m₂ : MinorModel H G) : MinorModel K G where
  branch u := ⋃ w ∈ m₁.branch u, m₂.branch w
  connected u := by
    obtain ⟨⟨w₀, hw₀⟩, h₁⟩ := m₁.connected u
    obtain ⟨a₀, ha₀⟩ := (m₂.connected w₀).1
    refine ⟨⟨a₀, Set.mem_biUnion hw₀ ha₀⟩, fun a ha b hb => ?_⟩
    obtain ⟨w, hw, ha⟩ := Set.mem_iUnion₂.mp ha
    obtain ⟨w', hw', hb⟩ := Set.mem_iUnion₂.mp hb
    exact reachable_biUnion (fun x _ => m₂.connected x) (fun x y _ _ hxy => m₂.adj x y hxy)
      (h₁ w hw w' hw') hw ha hb
  disjoint u u' huu' := by
    rw [Set.disjoint_left]
    intro a ha ha'
    obtain ⟨w, hw, ha⟩ := Set.mem_iUnion₂.mp ha
    obtain ⟨w', hw', ha'⟩ := Set.mem_iUnion₂.mp ha'
    by_cases hww : w = w'
    · subst hww
      exact Set.disjoint_left.mp (m₁.disjoint u u' huu') hw hw'
    · exact Set.disjoint_left.mp (m₂.disjoint w w' hww) ha ha'
  adj u u' h := by
    obtain ⟨w, hw, w', hw', hww'⟩ := m₁.adj u u' h
    obtain ⟨a, ha, b, hb, hab⟩ := m₂.adj w w' hww'
    exact ⟨a, Set.mem_biUnion hw ha, b, Set.mem_biUnion hw' hb, hab⟩

end MinorModel

theorem IsMinor.refl (G : SimpleGraph V) : IsMinor G G :=
  ⟨.ofInjective Hom.id Function.injective_id⟩

theorem IsMinor.trans {K : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V}
    (h₁ : IsMinor K H) (h₂ : IsMinor H G) : IsMinor K G :=
  ⟨h₁.some.trans h₂.some⟩

/-- **Subgraphs are minors.** -/
theorem isMinor_of_le {G' G : SimpleGraph V} (h : G' ≤ G) : IsMinor G' G :=
  ⟨.ofInjective (Hom.ofLE h) Function.injective_id⟩

/-- **Induced subgraphs are minors.** -/
theorem isMinor_induce (G : SimpleGraph V) (s : Set V) : IsMinor (G.induce s) G :=
  ⟨.ofInjective (Embedding.induce s).toHom Subtype.val_injective⟩

/-- **Isomorphic graphs are minors of each other.** -/
theorem Iso.isMinor {H : SimpleGraph W} {G : SimpleGraph V} (f : H ≃g G) : IsMinor H G :=
  ⟨.ofInjective f.toHom f.injective⟩

/-- **Every graph on `W` is a minor of the complete graph on any type of the same size.** -/
theorem isMinor_top_of_equiv {H : SimpleGraph W} {W' : Type*} (e : W ≃ W') :
    IsMinor H (⊤ : SimpleGraph W') :=
  ⟨.ofInjective ⟨e, fun {_ _} h => (top_adj _ _).mpr (e.injective.ne h.ne)⟩ e.injective⟩

/-! ## Contracting an edge -/

/-- **Contracting the edge `xy`**: the graph on `V \ {y}` in which `x` also takes the neighbours
of `y`. -/
def contractEdge (G : SimpleGraph V) (x y : V) : SimpleGraph {v // v ≠ y} :=
  SimpleGraph.fromRel fun a b => G.Adj a b ∨ (a.1 = x ∧ G.Adj y b)

theorem contractEdge_adj {G : SimpleGraph V} {x y : V} {a b : {v // v ≠ y}} :
    (contractEdge G x y).Adj a b ↔
      a ≠ b ∧ ((G.Adj a b ∨ (a.1 = x ∧ G.Adj y b)) ∨ (G.Adj b a ∨ (b.1 = x ∧ G.Adj y a))) :=
  fromRel_adj _ _ _

open Classical in
/-- **Contracting an edge gives a minor**: the branch set of `x` is `{x, y}`, and every other
vertex is its own branch set. -/
noncomputable def MinorModel.ofContractEdge {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    MinorModel (contractEdge G x y) G where
  branch a := if a.1 = x then {x, y} else {a.1}
  connected a := by
    split_ifs
    · exact isConnectedSet_pair hxy
    · exact isConnectedSet_singleton _ _
  disjoint a a' h := by
    have h' : a.1 ≠ a'.1 := fun he => h (Subtype.ext he)
    have ha := a.2
    have ha' := a'.2
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) h'
    · rw [Set.disjoint_singleton_right]
      rintro (h3 | h3)
      · exact h2 h3
      · exact ha' h3
    · rw [Set.disjoint_singleton_left]
      rintro (h3 | h3)
      · exact h1 h3
      · exact ha h3
    · exact Set.disjoint_singleton.mpr h'
  adj a b h := by
    have hself : ∀ c : {v // v ≠ y}, c.1 ∈ (if c.1 = x then ({x, y} : Set V) else {c.1}) :=
      fun c => by
        split_ifs with hc
        · exact Or.inl hc
        · exact rfl
    have hy : ∀ c : {v // v ≠ y}, c.1 = x → y ∈ (if c.1 = x then ({x, y} : Set V) else {c.1}) :=
      fun c hc => by
        rw [ite_eq_left hc]
        exact Or.inr rfl
    obtain ⟨-, (h | ⟨hax, h⟩) | (h | ⟨hbx, h⟩)⟩ := contractEdge_adj.mp h
    · exact ⟨a, hself a, b, hself b, h⟩
    · exact ⟨y, hy a hax, b, hself b, h⟩
    · exact ⟨a, hself a, b, hself b, h.symm⟩
    · exact ⟨a, hself a, y, hy b hbx, h.symm⟩

/-- **Contracting an edge is a minor.** -/
theorem isMinor_contractEdge {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    IsMinor (contractEdge G x y) G :=
  ⟨.ofContractEdge hxy⟩

end MonoidProduct.Graph
