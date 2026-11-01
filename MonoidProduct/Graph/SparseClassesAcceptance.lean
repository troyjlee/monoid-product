import MonoidProduct.Graph.SparseClasses
import MonoidProduct.Graph.SurfaceExamples
set_option linter.style.header false

/-!
# Acceptance statements for minor-closed and sparse classes

The paper-facing statements of `monoid.tex`, section `sec:graph-certificates`, paragraph
"Planarity and minor-closed properties" after its planarity sentence, and the row of
`tab:graph-certificates` for minor-closed properties.  They are restated with the definitions
unfolded where that makes their meaning visible, followed by sanity checks.  Lean checks every
`example` here against the library's statement.

* Minors through minor models, Mader's theorem, and the linear edge bound of every proper
  minor-closed class.
* Outerplanarity through the apex graph, treewidth through tree decompositions, and embeddings
  in surfaces through embedding schemes, each with its edge bound.
* The certificate sizes `b_P = O_P(v)` and the query bounds `O_P(min{n, √(nv)})` and
  `O_P(v^{3/2})`.

The sanity checks cover:
* the triangle, outerplanar with `3 = 2·3 − 3` edges, and `K₄`, which is not outerplanar;
* `K_(t+1)` of treewidth at most `t`, and the path `0 − 1 − 2` of treewidth at most `1`;
* planar graphs of genus `0`, `K₄` among them, and `K₅`, not of Euler genus `0`;
* `K₇` on the torus: orientable genus at most `1`, but not Euler genus at most `1`;
* the classes excluding a complete minor, which are proper and minor-closed.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

/-! ## Minors and Mader's theorem -/

section Minors

variable {V W : Type*}

/-- **Minor models** (Diestel, Section 1.7): disjoint branch sets inducing connected subgraphs,
one per vertex of `H`, with an edge of `G` between the branch sets of adjacent vertices. -/
example (H : SimpleGraph W) (G : SimpleGraph V) (m : MinorModel H G) (w w' : W) :
    (G.induce (m.branch w)).Connected ∧ (w ≠ w' → Disjoint (m.branch w) (m.branch w')) ∧
      (H.Adj w w' → ∃ a ∈ m.branch w, ∃ b ∈ m.branch w', G.Adj a b) ∧
      (IsMinor H G ↔ Nonempty (MinorModel H G)) :=
  ⟨isConnectedSet_iff.mp (m.connected w), m.disjoint w w', m.adj w w', Iff.rfl⟩

/-- **Minors are reflexive and transitive**; subgraphs, induced subgraphs and contractions of an
edge are minors.  Contracting `xy` deletes `y` and gives `x` the neighbours of `y`. -/
example {U : Type*} (K : SimpleGraph U) (H : SimpleGraph W) (G G' : SimpleGraph V) (s : Set V)
    (x y : V) (hxy : G.Adj x y) (a b : {v // v ≠ y}) :
    IsMinor G G ∧ (IsMinor K H → IsMinor H G → IsMinor K G) ∧ (G' ≤ G → IsMinor G' G) ∧
      IsMinor (G.induce s) G ∧ IsMinor (contractEdge G x y) G ∧
      ((contractEdge G x y).Adj a b ↔ a ≠ b ∧
        ((G.Adj a b ∨ (a.1 = x ∧ G.Adj y b)) ∨ (G.Adj b a ∨ (b.1 = x ∧ G.Adj y a)))) :=
  ⟨IsMinor.refl G, IsMinor.trans, isMinor_of_le, isMinor_induce G s, isMinor_contractEdge hxy,
    contractEdge_adj⟩

end Minors

/-- **Mader's theorem** (Diestel, Proposition 7.2.1): for `r ≥ 2`, average degree at least
`2^(r−2)` forces a `K_r` minor; so graphs without a `K_r` minor have at most `2^r·v` edges. -/
example {V : Type} [Fintype V] (G : SimpleGraph V) (r : ℕ) :
    (2 ≤ r → 1 ≤ Fintype.card V → 2 ^ (r - 2) * Fintype.card V ≤ 2 * G.edgeSet.ncard →
      IsMinor (⊤ : SimpleGraph (Fin r)) G) ∧
    (¬IsMinor (⊤ : SimpleGraph (Fin r)) G → G.edgeSet.ncard ≤ 2 ^ r * Fintype.card V) :=
  ⟨fun hr hV hE => isMinor_top_of_le hr hV hE, ncard_edgeSet_le_of_not_isMinor r⟩

/-- **Every fixed proper minor-closed class has a linear edge bound** (`sec:graph-certificates`):
a class of graphs on finite vertex types, closed under minors, and missing some finite graph, has
a constant `C` with `|E| ≤ C·v` for its members. -/
example (P : ∀ V : Type, SimpleGraph V → Prop)
    (hP : ∀ {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W},
      IsMinor H G → P V G → P W H)
    (hprop : ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W), ¬P W H) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), P V G →
      G.edgeSet.ncard ≤ C * Fintype.card V :=
  IsMinorClosed.exists_ncard_edgeSet_le hP hprop

/-! ## Outerplanarity, treewidth and surfaces -/

section Classes

variable {V : Type*} (G : SimpleGraph V)

/-- **Outerplanarity**: the apex graph, with a new vertex adjacent to every vertex, is planar
(Chartrand–Harary).  On `v ≥ 2` vertices, at most `2v − 3` edges. -/
example [Fintype V] (u w : V) :
    (IsOuterplanar G ↔ IsPlanar (apex G)) ∧ (apex G).Adj none (some u) ∧
      ((apex G).Adj (some u) (some w) ↔ G.Adj u w) ∧ ¬(apex G).Adj none none ∧
      (apex G).edgeSet.ncard = G.edgeSet.ncard + Fintype.card V ∧
      (IsOuterplanar G → 2 ≤ Fintype.card V → G.edgeSet.ncard ≤ 2 * Fintype.card V - 3) := by
  refine ⟨Iff.rfl, apex_adj_none_some G u, apex_adj_some_some, apex_not_adj_none_none G, ?_,
    fun h hv => h.ncard_edgeSet_le hv⟩
  rw [ncard_edgeSet_apex, Nat.card_eq_fintype_card]

/-- **Treewidth** (Diestel, Section 12.3): a tree decomposition covers every vertex and edge, and
the bags at the ends of a tree path share their vertices with every bag on it.  Treewidth at most
`t` gives at most `t·v` edges. -/
example [Fintype V] (t : ℕ) (D : TreeDecomposition G) (i j k : D.ι) (p : D.tree.Walk i k)
    (v u w : V) :
    D.tree.IsTree ∧ (∃ i, v ∈ D.bag i) ∧ (G.Adj u w → ∃ i, u ∈ D.bag i ∧ w ∈ D.bag i) ∧
      (p.IsPath → j ∈ p.support → v ∈ D.bag i → v ∈ D.bag k → v ∈ D.bag j) ∧
      (TreewidthLE t G ↔ ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ t + 1) ∧
      (TreewidthLE t G → G.edgeSet.ncard ≤ t * Fintype.card V) :=
  ⟨D.isTree, D.cover_vertex v, D.cover_edge u w, fun hp hj => D.mem_of_mem_path i j k p hp hj v,
    Iff.rfl,
    TreewidthLE.ncard_edgeSet_le⟩

/-- **Embeddings in surfaces**: an embedding scheme twists some edges; face tracing crosses a
dart, flips the orientation on a twisted edge, and leaves along the next dart in the current
orientation.  Euler genus at most `k` gives at most `3v − 6 + 3k` edges, and orientable genus at
most `g` at most `3v − 6 + 6g`, for `v ≥ 3`; planar graphs have genus `0`. -/
example [Fintype V] (σ : EmbeddingScheme G) (d : G.Dart) (ε : Bool) (k g : ℕ)
    (c : G.ConnectedComponent) (hc : (componentEdges G c).Nonempty) :
    σ.trace (d, ε) = (if xor ε (σ.twist d) then σ.rot.symm d.symm else σ.rot d.symm,
      xor ε (σ.twist d)) ∧
    σ.twiceEulerGenus c =
      (2 * (componentEdges G c).ncard + 4) - (2 * c.supp.ncard + (σ.orbitsIn c).ncard) ∧
    (EulerGenusLE G k ↔ ∃ σ : EmbeddingScheme G, ∑ᶠ c, σ.twiceEulerGenus c ≤ 2 * k) ∧
    (GenusLE G g ↔ ∃ σ : EmbeddingScheme G, (∀ d, σ.twist d = false) ∧
      ∑ᶠ c, σ.twiceEulerGenus c ≤ 4 * g) ∧
    (3 ≤ Fintype.card V → EulerGenusLE G k →
      G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 + 3 * k) ∧
    (3 ≤ Fintype.card V → GenusLE G g → G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 + 6 * g) ∧
    (IsPlanar G → GenusLE G 0) := by
  refine ⟨rfl, ?_, Iff.rfl, Iff.rfl, fun hv h => h.ncard_edgeSet_le hv,
    fun hv h => h.ncard_edgeSet_le hv, IsPlanar.genusLE_zero⟩
  unfold EmbeddingScheme.twiceEulerGenus
  exact ite_eq_left hc

end Classes

/-! ## Certificate sizes -/

section Certificates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`b_P = O_P(v)`** for outerplanarity (`2v`, and `min{C(v, 2), 2v − 2}`), treewidth at most
`t` (`(t + 1)·v`, and `min{C(v, 2), t·v + 1}`), Euler genus at most `k` (`(3k + 4)·v`), and
orientable genus at most `g` (`(6g + 4)·v`). -/
example (t k g : ℕ) :
    strongCertificateSize (isOuterplanar (V := V)) ≤
        min ((Fintype.card V).choose 2) (2 * Fintype.card V - 2) ∧
      strongCertificateSize (isOuterplanar (V := V)) ≤ 2 * Fintype.card V ∧
      strongCertificateSize (hasTreewidthLE (V := V) t) ≤
        min ((Fintype.card V).choose 2) (t * Fintype.card V + 1) ∧
      strongCertificateSize (hasTreewidthLE (V := V) t) ≤ (t + 1) * Fintype.card V ∧
      strongCertificateSize (hasEulerGenusLE (V := V) k) ≤ (3 * k + 4) * Fintype.card V ∧
      strongCertificateSize (hasGenusLE (V := V) g) ≤ (6 * g + 4) * Fintype.card V :=
  ⟨outerplanarity_strongCertificateSize_le, outerplanarity_strongCertificateSize_le_linear,
    treewidth_strongCertificateSize_le t, treewidth_strongCertificateSize_le_linear t,
    surfaceEmbedding_strongCertificateSize_le k, genus_strongCertificateSize_le g⟩

/-- The Boolean outputs decide the classes of `toGraph S`. -/
example (t k g : ℕ) (S : Finset (Edge V)) :
    (isOuterplanar S = true ↔ IsOuterplanar (toGraph S)) ∧
      (hasTreewidthLE t S = true ↔ TreewidthLE t (toGraph S)) ∧
      (hasEulerGenusLE k S = true ↔ EulerGenusLE (toGraph S) k) ∧
      (hasGenusLE g S = true ↔ GenusLE (toGraph S) g) :=
  ⟨isOuterplanar_eq_true_iff, hasTreewidthLE_eq_true_iff, hasEulerGenusLE_eq_true_iff,
    hasGenusLE_eq_true_iff⟩

end Certificates

/-- **`b_P = O_P(v)` for every fixed proper minor-closed class** (`sec:graph-certificates`): a
constant `C`, depending only on `P`, with `b_P ≤ C·v` on every finite vertex type. -/
example (P : ∀ V : Type, SimpleGraph V → Prop) (hP : IsMinorClosed P)
    (hprop : IsProperClass P) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V],
      strongCertificateSize (classIndicator P V) ≤ C * Fintype.card V :=
  minorClosed_strongCertificateSize_le_linear hP hprop

/-! ## Query bounds -/

/-- **`Q_list(P; n) = O_P(min{n, √(nv)})`** and **`Q_matrix(P) = O_P(v^{3/2})`** for every fixed
proper minor-closed class (`sec:graph-certificates`, `tab:graph-certificates`). -/
example (P : ∀ V : Type, SimpleGraph V → Prop) (hP : IsMinorClosed P)
    (hprop : IsProperClass P) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (n : ℕ),
      (qList (classIndicator P V) n : ℝ) ≤
          min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (C * Fintype.card V : ℕ))) ∧
        (qMatrix (classIndicator P V) : ℝ) ≤
          2 ^ 18 * Real.sqrt C * Fintype.card V * Real.sqrt (Fintype.card V) :=
  minorClosed_query_le hP hprop

/-- **The named classes**, with explicit constants. -/
example {V : Type} [Fintype V] [DecidableEq V] (t k n : ℕ) :
    (qMatrix (isOuterplanar (V := V)) : ℝ) ≤
        2 ^ 18 * Real.sqrt 2 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qMatrix (hasTreewidthLE (V := V) t) : ℝ) ≤
        2 ^ 18 * Real.sqrt (t + 1) * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qMatrix (hasEulerGenusLE (V := V) k) : ℝ) ≤
        2 ^ 18 * Real.sqrt (3 * k + 4) * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qList (isOuterplanar (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * Fintype.card V - 2 : ℕ))) :=
  ⟨(outerplanarity_query_le n).2, (treewidth_query_le t n).2, (surfaceEmbedding_query_le k n).2,
    (outerplanarity_query_le n).1⟩

/-! ## Sanity checks -/

/-- **Outerplanarity**: the triangle is outerplanar and attains `2v − 3`; `K₄` is not
outerplanar. -/
example : IsOuterplanar (⊤ : SimpleGraph (Fin 3)) ∧
    (⊤ : SimpleGraph (Fin 3)).edgeSet.ncard = 2 * Fintype.card (Fin 3) - 3 ∧
    ¬IsOuterplanar (⊤ : SimpleGraph (Fin 4)) :=
  ⟨isOuterplanar_top_three, ncard_edgeSet_top_three, not_isOuterplanar_top_four⟩

/-- **Treewidth**: `K_(t+1)` has treewidth at most `t`, and the path `0 − 1 − 2` at most `1`. -/
example (t : ℕ) : TreewidthLE t (⊤ : SimpleGraph (Fin (t + 1))) ∧ TreewidthLE 1 path3 :=
  ⟨treewidthLE_top t, treewidthLE_one_path3⟩

/-- **Surfaces**: `K₄` has genus `0`; `K₅` does not have Euler genus `0`; graphs without edges
have Euler genus `0`. -/
example : GenusLE (⊤ : SimpleGraph (Fin 4)) 0 ∧ ¬EulerGenusLE (⊤ : SimpleGraph (Fin 5)) 0 ∧
    EulerGenusLE (⊥ : SimpleGraph (Fin 5)) 0 :=
  ⟨genusLE_zero_top_four, not_eulerGenusLE_zero_top_five, eulerGenusLE_zero_bot⟩

/-- **`K₇` on the torus**: an explicit rotation with `14` triangular faces gives orientable
genus at most `1`, so Euler genus at most `2`; `K₇` does not have Euler genus at most `1`. -/
example : GenusLE (⊤ : SimpleGraph (Fin 7)) 1 ∧ EulerGenusLE (⊤ : SimpleGraph (Fin 7)) 2 ∧
    ¬EulerGenusLE (⊤ : SimpleGraph (Fin 7)) 1 ∧ Nat.card k7Rotation.Face = 14 :=
  ⟨genusLE_one_top_seven, genusLE_one_top_seven.eulerGenusLE, not_eulerGenusLE_one_top_seven,
    natCard_k7Face⟩

/-- **Excluding `K_t` as a minor** is a proper minor-closed class, so the general theorem
applies to it. -/
example (t : ℕ) : IsMinorClosed (fun _ G => ¬IsMinor (⊤ : SimpleGraph (Fin t)) G) ∧
    IsProperClass (fun _ G => ¬IsMinor (⊤ : SimpleGraph (Fin t)) G) :=
  ⟨isMinorClosed_not_isMinor_top t, isProperClass_not_isMinor_top t⟩

end MonoidProduct.Graph
