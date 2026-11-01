import MonoidProduct.Graph.PlanarCertificate
import MonoidProduct.Graph.PlanarExamples
set_option linter.style.header false

/-!
# Acceptance statements for planarity

The paper-facing statements of `monoid.tex`, section `sec:graph-certificates`, paragraph
"Planarity and minor-closed properties", and the planarity row of `tab:graph-certificates`.  They
are restated with the definitions unfolded where that makes their meaning visible, followed by
sanity checks.  Lean checks every `example` here against the library's statement.

* Rotation systems, faces, and planarity as a spherical rotation system, unfolded.
* The edge bound `|E| ≤ 3v - 6` for `v ≥ 3`, and `|E| ≤ 2v - 4` for two-colourable graphs.
* `b_planar ≤ min{C(v, 2), 3v - 5}`, in the paper's form `v ≥ 3` and for every `v`.
* The list, matrix and adjacency-list bounds.

The sanity checks cover:
* `K₄`, which is planar, with all four faces triangles and `6 = 3·4 − 6` edges, so the bound is
  attained;
* `K₅` and `K₃,₃`, which are not planar; `K₃,₃` has only `9 ≤ 3·6 − 6` edges, so planarity is
  more than the edge bound;
* graphs without edges, which are planar.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

/-! ## Rotation systems and planarity -/

section Definitions

variable {V : Type*} (G : SimpleGraph V)

/-- **Rotation systems**: a permutation of the darts that keeps every dart's tail and is one
cycle on the darts at each vertex.  The face permutation leaves the head of a dart along the
next dart around it, and the faces are its cycles, each in one component. -/
example (ρ : RotationSystem G) (d d' : G.Dart) :
    (ρ.rot d).fst = d.fst ∧ (d.fst = d'.fst → ρ.rot.SameCycle d d') ∧
      ρ.face d = ρ.rot d.symm ∧ (ρ.face d).fst = d.snd ∧
      ((⟦d⟧ : ρ.Face) = ⟦d'⟧ ↔ ρ.face.SameCycle d d') ∧
      RotationSystem.Face.component (⟦d⟧ : ρ.Face) = G.connectedComponentMk d.fst :=
  ⟨ρ.fst_rot d, ρ.sameCycle_rot d d', rfl, ρ.fst_face d, Quotient.eq, rfl⟩

/-- **Planarity**: some rotation system satisfies Euler's formula `V + F = E + 2` in every
connected component with an edge, counting the vertices, faces and edges of that component. -/
example : IsPlanar G ↔ ∃ ρ : RotationSystem G, ∀ c : G.ConnectedComponent,
    {e | e ∈ G.edgeSet ∧ ∀ v ∈ e, G.connectedComponentMk v = c}.Nonempty →
      c.supp.ncard + {f : ρ.Face | f.component = c}.ncard =
        {e | e ∈ G.edgeSet ∧ ∀ v ∈ e, G.connectedComponentMk v = c}.ncard + 2 :=
  Iff.rfl

/-- **`|E| ≤ 3v - 6`** (`sec:graph-certificates`): a planar graph on `v ≥ 3` vertices has at
most `3v - 6` edges, connected or not; two-colourable planar graphs have at most `2v - 4`. -/
example [Fintype V] (h : IsPlanar G) (hv : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 ∧
      (G.Colorable 2 → G.edgeSet.ncard ≤ 2 * Fintype.card V - 4) :=
  ⟨h.ncard_edgeSet_le hv, fun hcol => h.ncard_edgeSet_le_of_colorable hcol hv⟩

end Definitions

/-! ## The certificate size -/

section Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`b_planar ≤ min{C(v, 2), 3v - 5}`** (`sec:graph-certificates`), in the paper's form
`v ≥ 3`, with the certificates; `isPlanar` decides `IsPlanar` of `toGraph S`, and its
yes-instances have at most `3v - 6` edges. -/
example (_hv : 3 ≤ Fintype.card V) (S : Finset (Edge V)) :
    (isPlanar S = true ↔ IsPlanar (toGraph S)) ∧
      (isPlanar S = true → S.card ≤ 3 * Fintype.card V - 6) ∧
      strongCertificateSize (isPlanar (V := V)) ≤
        min ((Fintype.card V).choose 2) (3 * Fintype.card V - 5) ∧
      HasStrongCertificateBound (isPlanar (V := V))
        (min ((Fintype.card V).choose 2) (3 * Fintype.card V - 5)) :=
  ⟨isPlanar_eq_true_iff, fun h => card_le_of_isPlanar h _hv, planarity_strongCertificateSize_le,
    hasStrongCertificateBound_isPlanar⟩

/-- The certificate bound holds for every `v`: for `v ≤ 2` it is the cap `C(v, 2)`. -/
example : strongCertificateSize (isPlanar (V := V)) ≤
    min ((Fintype.card V).choose 2) (3 * Fintype.card V - 5) :=
  planarity_strongCertificateSize_le

end Certificate

/-! ## Query bounds -/

section Queries

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Planarity**: `Q_list(planar; n) ≤ min{n, 2^18·√(n(3v - 5))}`, the paper's
`O(min{n, √(nv)})`; `Q_matrix ≤ 2^19·v·√v`, the `O(v^{3/2})` of `tab:graph-certificates`; and
the adjacency-list form. -/
example (n m : ℕ) :
    (qList (isPlanar (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (3 * Fintype.card V - 5 : ℕ))) ∧
      (qMatrix (isPlanar (V := V)) : ℝ) ≤ min ((Fintype.card V).choose 2 : ℝ)
        (2 ^ 18 * Real.sqrt ((Fintype.card V).choose 2 * (3 * Fintype.card V - 5 : ℕ))) ∧
      (qMatrix (isPlanar (V := V)) : ℝ) ≤ 2 ^ 19 * Fintype.card V * Real.sqrt (Fintype.card V) ∧
      (qAdjEdges (isPlanar (V := V)) m : ℝ)
        ≤ min (2 * m : ℝ) (2 ^ 19 * Real.sqrt (m * (3 * Fintype.card V - 5 : ℕ))) :=
  ⟨planarity_qList_le n, planarity_qMatrix_le, planarity_qMatrix_le_mul_sqrt,
    planarity_qAdjEdges_le m⟩

end Queries

/-! ## Sanity checks -/

section Sanity

/-- **`K₄` is planar and attains the bound**: its rotation system, read off a drawing with `3`
inside the triangle `0 1 2`, has four triangular faces, and `K₄` has `6 = 3·4 − 6` edges. -/
example : IsPlanar (⊤ : SimpleGraph (Fin 4)) ∧
    (∀ d, k4Rotation.face (k4Rotation.face (k4Rotation.face d)) = d) ∧
    Nat.card k4Rotation.Face = 4 ∧
    (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard = 3 * Fintype.card (Fin 4) - 6 :=
  ⟨isPlanar_top_four, k4_face_three, natCard_k4Face, ncard_edgeSet_top_four⟩

/-- **`K₅` and `K₃,₃` are not planar.**  `K₃,₃` has only `9` edges, within `3·6 − 6 = 12`, so
planarity is more than the edge bound; it fails the two-colourable bound `2·6 − 4 = 8`. -/
example : ¬IsPlanar (⊤ : SimpleGraph (Fin 5)) ∧
    ¬IsPlanar (completeBipartiteGraph (Fin 3) (Fin 3)) ∧
    (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet.ncard ≤
      3 * Fintype.card (Fin 3 ⊕ Fin 3) - 6 := by
  refine ⟨not_isPlanar_top_five, not_isPlanar_completeBipartite_three_three, ?_⟩
  rw [ncard_edgeSet_completeBipartite_three_three, Fintype.card_sum, Fintype.card_fin]
  decide

/-- **Graphs without edges are planar**, on any vertex set. -/
example {V : Type*} : IsPlanar (⊥ : SimpleGraph V) := isPlanar_bot

end Sanity

end MonoidProduct.Graph
