import MonoidProduct.Graph.Basic
import MonoidProduct.Graph.Components
import MonoidProduct.Graph.TwoColorings
import MonoidProduct.Graph.Sparse
import MonoidProduct.Graph.Acceptance
import MonoidProduct.Graph.QueryModels
import MonoidProduct.Graph.Quantum
import MonoidProduct.Graph.QueryAcceptance
import MonoidProduct.Graph.Planar
import MonoidProduct.Graph.PlanarExamples
import MonoidProduct.Graph.PlanarCertificate
import MonoidProduct.Graph.PlanarAcceptance
import MonoidProduct.Graph.EdgeFaults
import MonoidProduct.Graph.FailureQueries
import MonoidProduct.Graph.FailureAcceptance
import MonoidProduct.Graph.VertexFaults
import MonoidProduct.Graph.Enumeration
import MonoidProduct.Graph.FailureLower
import MonoidProduct.Graph.LowerAcceptance
import MonoidProduct.Graph.VertexCertificate
import MonoidProduct.Graph.VertexReadouts
import MonoidProduct.Graph.VertexQueries
import MonoidProduct.Graph.VertexAcceptance
import MonoidProduct.Graph.Surface
import MonoidProduct.Graph.SurfaceExamples
import MonoidProduct.Graph.PlanarIso
import MonoidProduct.Graph.Outerplanar
import MonoidProduct.Graph.Treewidth
import MonoidProduct.Graph.Minor
import MonoidProduct.Graph.Mader
import MonoidProduct.Graph.SparseClasses
import MonoidProduct.Graph.SparseClassesAcceptance
import MonoidProduct.Graph.RotationPermutation
import MonoidProduct.Graph.RotationDeletion
import MonoidProduct.Graph.PlanarSubgraph
import MonoidProduct.Graph.PlanarSubgraphAcceptance
import MonoidProduct.Graph.MinorContraction
import MonoidProduct.Graph.PlanarContraction
import MonoidProduct.Graph.PlanarMinor
import MonoidProduct.Graph.Wagner
import MonoidProduct.Graph.PlanarMinorAcceptance
set_option linter.style.header false

/-!
# Graph properties with small certificates (`monoid.tex`, `sec:graph-certificates`)

Graphs on a fixed vertex set as subsets of the possible edges.  Strong certificates of at most
`v - 1` or `v` edges, `v = #V`, for:
* the component partition, with connectivity and `s`–`t` connectivity;
* the set of all proper two-colourings, with bipartiteness and a canonical colouring;
* cycle detection.

Also sparse yes-instances (`prop:sparse-certificates`).

The query models: edge lists, adjacency matrices and adjacency arrays, compared with factor two
(`eq:graph-model-comparison`), and the query bounds `eq:graph-certificate-list` and
`eq:graph-certificate-matrix` for every one of these outputs.

Planarity: planar graphs as graphs with a spherical rotation system (a combinatorial embedding
of genus `0`), the edge bound `3v - 6`, certificates of at most `min{C(v, 2), 3v - 5}` edges, and
the query bounds; `K₄` is planar, and `K₅` and `K₃,₃` are not.  Euler's inequality
`V − E + F ≤ 2` in every component, for every rotation system, through the Euler defect and its
behaviour under edge deletion; planarity is closed under subgraphs, induced subgraphs, edge
contraction and minors, so planar graphs have no `K₅` and no `K₃,₃` minor (the easy direction of
Wagner's theorem).

Minor-closed classes: graph minors, Mader's theorem, and the linear edge bound of every proper
minor-closed class, so `b_P = O_P(v)`; outerplanarity (through the apex graph), bounded treewidth
(through tree decompositions) and embeddings in surfaces (through embedding schemes and the Euler
genus), each with explicit linear certificate and query bounds.

Edge failures (`monoid.tex`, `sec:failure-profiles`): the edge-failure profile, certificates of
at most `k(v - 1)` edges from successive spanning forests, the bridges, the partitions after their
deletion and `k`-edge-connectivity, with their query bounds.  The vertex-failure profile, and
the lower bounds `Ω(min{v², v^{3/2}√k})` for both profiles in the matrix model, through the
enumeration adversary of the Johnson exchange graphs.  Vertex failures: certificates of at most
`2kv` edges from a greedy construction, the articulation points, the partitions after their
deletion and `k`-vertex-connectivity, with their query bounds, so that both profiles cost
`Θ(min{v², v^{3/2}√k})` matrix queries.
-/
