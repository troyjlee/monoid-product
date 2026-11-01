import MonoidProduct.Graph.Mader
import MonoidProduct.Graph.PlanarExamples
import MonoidProduct.Graph.PlanarMinor
set_option linter.style.header false

/-!
# The easy direction of Wagner's theorem

**A planar graph has neither a `K₅` minor nor a `K₃,₃` minor** (`IsPlanar.wagner_easy`).  Planarity
is `IsPlanar` (`Graph/Planar.lean`: a rotation system satisfying Euler's formula in every component
with an edge), minors are minor models (`Graph/Minor.lean`), and the vertex type is only assumed
finite: the graph need not be connected, and nothing is assumed of its edges.

Planarity is closed under minors (`IsPlanar.of_minor`), and `K₅` and `K₃,₃` are not planar
(`not_isPlanar_top_five`, by `|E| ≤ 3v − 6`, and `not_isPlanar_completeBipartite_three_three`, by
`|E| ≤ 2v − 4` for two-colourable graphs).  So planarity is a proper minor-closed class
(`isMinorClosed_isPlanar`, `isProperClass_isPlanar`).

The converse, that a finite graph with neither minor is planar, is the hard direction of Wagner's
theorem and is not formalized here.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- **A planar graph has no `K₅` minor.** -/
theorem IsPlanar.not_isMinor_top_five (hG : IsPlanar G) :
    ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G :=
  fun hM => not_isPlanar_top_five (hG.of_minor hM)

/-- **A planar graph has no `K₃,₃` minor.** -/
theorem IsPlanar.not_isMinor_completeBipartite_three_three (hG : IsPlanar G) :
    ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G :=
  fun hM => not_isPlanar_completeBipartite_three_three (hG.of_minor hM)

/-- **The easy direction of Wagner's theorem**: a planar graph on a finite vertex type has neither
a `K₅` minor nor a `K₃,₃` minor. -/
theorem IsPlanar.wagner_easy (hG : IsPlanar G) :
    ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G ∧
      ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G :=
  ⟨hG.not_isMinor_top_five, hG.not_isMinor_completeBipartite_three_three⟩

/-- **Planarity is a minor-closed class.** -/
theorem isMinorClosed_isPlanar : IsMinorClosed fun _ G => IsPlanar G :=
  fun hM hG => hG.of_minor hM

/-- **Planarity is a proper class**: `K₅` is not planar. -/
theorem isProperClass_isPlanar : IsProperClass fun _ G => IsPlanar G :=
  ⟨Fin 5, inferInstance, ⊤, not_isPlanar_top_five⟩

end MonoidProduct.Graph
