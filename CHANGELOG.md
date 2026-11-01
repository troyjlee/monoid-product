# Changelog

## 0.2.0

- Strong certificates (`MonoidProduct.Certificates`, the paper's Section
  6.1): equivalence under extensions, strong certificates and the
  certificate size `strongCertificateSize`, the extension monoid
  `ExtensionMonoid` and its cardinality bound, the equality of product
  breadth with the certificate size (`certificate_breadth`), and the query
  bound `strongCertificate_qQuery_le_min_sqrt`, also for position-dependent
  encodings (`encodedCertificate_qQuery_le_min_sqrt`).
- Greedy bases as strong certificates (`Matroid/Certificates.lean`): the
  extension monoid of the greedy-basis map is the greedy-basis monoid, and
  the minimum-weight basis bound is rederived through the certificate
  theorem. The existing matroid endpoints are unchanged.
- Graph certificates (`MonoidProduct.Graph`, the paper's Section 6.3):
  - graphs on a fixed vertex set as subsets of the possible edges;
  - strong certificates of at most `v - 1` edges for the component
    partition, connectivity and `s`–`t` connectivity;
  - strong certificates of at most `v` edges for the set of all proper
    two-colourings, bipartiteness, a canonical colouring and cycle
    detection;
  - Proposition 34 (`sparseYes_strongCertificateSize_le`), for graphs and
    for any finite universe.
- Planar graphs (`Graph/Planar.lean`, `Graph/PlanarExamples.lean`,
  `Graph/PlanarCertificate.lean`):
  - rotation systems on Mathlib's darts, their faces, and planarity as a
    rotation system satisfying Euler's formula in every component with an
    edge (`IsPlanar`);
  - the edge bound `|E| ≤ 3v - 6` for `v ≥ 3` (`IsPlanar.ncard_edgeSet_le`),
    and `|E| ≤ 2v - 4` for two-colourable planar graphs;
  - `K₄` is planar, and `K₅` and `K₃,₃` are not;
  - `b_planar ≤ min{C(v, 2), 3v - 5}` (`planarity_strongCertificateSize_le`)
    and the query bounds, with `2^19·v·√v` matrix queries.
- Minor-closed and sparse classes (`Graph/Minor.lean`, `Graph/Mader.lean`,
  `Graph/Outerplanar.lean`, `Graph/Treewidth.lean`, `Graph/Surface.lean`,
  `Graph/PlanarIso.lean`, `Graph/SparseClasses.lean`):
  - graph minors by minor models, with transitivity and edge contraction,
    and Mader's theorem (`isMinor_top_of_le`);
  - every proper minor-closed class has a linear edge bound
    (`IsMinorClosed.exists_ncard_edgeSet_le`), hence `b_P = O_P(v)`
    (`minorClosed_strongCertificateSize_le_linear`) and its query bounds;
  - outerplanarity (planarity of the apex graph, `2v - 3` edges), tree
    decompositions (`t·v` edges for treewidth at most `t`), and embedding
    schemes with the Euler genus (`3v - 6 + 3k` edges), each with linear
    certificate and query bounds;
  - planarity is invariant under isomorphism, and planar graphs have
    genus `0`.
- Planar subgraphs (`Graph/RotationPermutation.lean`,
  `Graph/RotationDeletion.lean`, `Graph/PlanarSubgraph.lean`):
  - cycle counts of permutations, fixed points included, under a
    transposition (which splits or merges cycles) and under erasing
    elements (`cycleCount_mul_swap_of_sameCycle`, `cycleCount_eraseOne`);
  - the Euler defect `2C − V + E − F̂` of a rotation system and its change
    when an edge is deleted: none for a bridge or for an edge whose darts
    lie on two faces, minus two otherwise (`eulerDefect_deleteEdge_le`);
  - Euler's inequality `V − E + F ≤ 2` in every component, for every
    rotation system (`eulerDefect_nonneg`,
    `ncard_supp_add_ncard_facesIn_le`), and sphericity as defect zero
    (`isSpherical_iff_eulerDefect_eq_zero`); every rotation system of a
    forest is spherical;
  - planarity is closed under subgraphs and induced subgraphs
    (`IsPlanar.mono`, `IsPlanar.deleteEdges`, `IsPlanar.induce`).
- Planar minors (`Graph/MinorContraction.lean`, `Graph/PlanarContraction.lean`,
  `Graph/PlanarMinor.lean`, `Graph/Wagner.lean`):
  - contracting an edge keeps the Euler defect when its ends have no common
    neighbour (`eulerDefect_contract`), and common neighbours can be thinned
    away first, so planarity is closed under edge contraction
    (`IsPlanar.contractEdge`);
  - minor models pass through contractions inside a branch set
    (`MinorModel.contractEdge`), so planarity is closed under injective
    homomorphisms and minors (`IsPlanar.of_injective`, `IsPlanar.of_minor`);
  - the easy direction of Wagner's theorem: a planar graph has no `K₅` and
    no `K₃,₃` minor (`IsPlanar.wagner_easy`); planarity is a proper
    minor-closed class (`isMinorClosed_isPlanar`, `isProperClass_isPlanar`);
  - the Petersen graph is not planar, by its `K₅` minor, although it is
    within the edge bound `3v − 6`.
- Connectivity and cyclic arcs (`Graph/WagnerConnectivity.lean`,
  `Graph/CycleArcs.lean`):
  - `k`-connectivity (`IsKConnected`), which agrees with `isVertexConnected`;
    monotonicity, the degree bound, vertex deletion and minimum separators;
  - proper separations from separators, with smaller sides; every vertex of
    a minimum separator has a neighbour in every component of the rest
    (`exists_adj_reachable`);
  - marker edges: for a separator `{x, y}` of a `2`-connected graph, each
    side with the edge `xy` added is a minor of the graph
    (`isMinor_sup_edge_induce_left`, `isMinor_sup_edge_induce_right`);
  - arcs of cyclic lists: distances, membership, rotation invariance,
    concatenation, disjointness, consecutive marks, and connectedness along
    a cycle of the graph.
- Face walks (`Graph/FaceWalk.lean`):
  - orbits of permutations as lists (`orbitList`), with their members,
    rotation along the cycle, and the identification of a list shifted
    cyclically by a permutation as an orbit (`orbitList_eq_of_getElem`);
  - the darts and the walk of the face through a dart (`faceDarts`,
    `faceWalk`): adjacency of consecutive vertices, and a walk without
    repeated vertices is a cycle of the graph (`isCycleList_faceWalk`);
  - rotation systems carried along isomorphisms (`RotationSystem.mapIso`),
    which stay spherical and carry face walks to face walks
    (`IsSpherical.mapIso`, `faceWalk_mapIso`); `IsPlanar.of_iso` now
    follows from them.
- Obstructions on a cycle (`Graph/WagnerObstructions.lean`): for an edge
  `xy` and a cycle avoiding it, three common neighbours of `x` and `y` on
  the cycle give a `K₅` minor and four alternating ones a `K₃,₃` minor, with
  explicit branch sets of arcs (`isMinor_top_five_of_three_common`,
  `isMinor_completeBipartite_of_alternating`); in a graph with neither minor,
  if `x` and `y` each have at least two neighbours on the cycle, the
  neighbours of `y` lie on the closed arc between two consecutive neighbours
  of `x` (`exists_isConsecutive_subset_closedArc`).
- A contractible edge (`Graph/WagnerContractible.lean`): every `3`-connected
  graph on at least five vertices has an edge whose contraction is
  `3`-connected (`exists_contractEdge_isKConnected_three`); contracting an
  edge of a `(k + 1)`-connected graph leaves a `k`-connected graph
  (`isKConnected_contractEdge`), and an edge fails exactly when it lies in a
  separating triple (`isKConnected_contractEdge_three_iff`).
- Faces of `2`-connected embeddings (`Graph/RotationSplit.lean`,
  `Graph/RotationFaces.lean`): in a spherical rotation system of a
  `2`-connected graph distinct darts of a face have distinct tails, so every
  face walk is a cycle (`RotationSystem.fst_injective_on_face`,
  `RotationSystem.isCycleList_faceWalk_of_isKConnected`), by splitting a
  vertex into two (`RotationSystem.splitRotation`, Euler defect `-2`);
  deleting a vertex leaves a spherical rotation system
  (`exists_rotationSystem_induce_ne`) with, for a `2`-connected graph, a face
  through all the neighbours of the deleted vertex
  (`exists_induce_ne_faceWalk`).
- Insertions into faces (`Graph/RotationChord.lean`,
  `Graph/RotationInsert.lean`): a chord between two corners of one face, with
  the two new faces read off as lists of darts (`RotationSystem.insertChord`,
  `faceDarts_insertChord`), keeps a rotation system spherical, so joining two
  vertices of one face keeps planarity (`isPlanar_sup_edge_of_sameCycle`); a
  leaf at a corner (`RotationSystem.insertLeaf`); a new vertex joined to
  vertices of a face without repeated vertices (`attachVertex`), keeping a
  face through the new vertex and a whole closed interval of the old face
  (`exists_isSpherical_attachVertex_faceWalk`), and its planarity
  (`isPlanar_attachVertex_of_subset_faceWalk`).
- Gluing planar graphs (`Graph/PlanarGlueVertex.lean`, `Graph/PlanarGlue.lean`):
  disjoint unions of planar graphs are planar (`IsPlanar.sum`), and so are
  two planar graphs glued at a vertex (`IsPlanar.glueVertex`, with a marked
  version keeping two chosen faces in one, `exists_isSpherical_glueVertex`);
  a graph whose two sides of a separation are planar is planar when the
  separator is empty, one vertex, or the two ends of an edge
  (`isPlanar_of_induce_of_inter_eq_empty`, `_singleton`, `_pair`).
- Wagner's theorem (`Graph/WagnerConverse.lean`, `Graph/Wagner.lean`): a
  finite graph with neither a `K₅` minor nor a `K₃,₃` minor is planar
  (`wagner_hard`), first for `3`-connected graphs (`wagner_threeConnected`);
  with the easy direction, a graph on a finite vertex type is planar exactly
  when it has neither minor (`wagner_iff`); acceptance examples in
  `Graph/WagnerAcceptance.lean`.
- Graph query models (`Graph/QueryModels.lean`, `Graph/Quantum.lean`):
  - edge lists (`qList`), adjacency matrices (`qMatrix`) and valid
    adjacency arrays with public degrees (`qAdj`, `qAdjEdges`);
  - their comparison `qMatrix f ≤ 2·qList f C(v, 2)` and
    `qAdj f deg ≤ 2·qList f (∑ deg)`, through two new oracle simulations
    (`qQueryOn_positionAlphabetMap_le`, `qQueryOn_reindex`);
  - the query bounds `min{n, 2^18·√(n·b_f)}` for edge lists,
    `min{C(v, 2), 2^18·√(C(v, 2)·b_f)} ≤ 2^18·v·√b_f` for matrices and
    `min{2m, 2^19·√(m·b_f)}` for adjacency arrays, and named list, matrix
    and adjacency-array bounds for every graph application above.
- Edge-failure profiles (`Graph/EdgeFaults.lean`, `Graph/FailureQueries.lean`,
  the paper's Section 6.4):
  - the profile `edgeFailureProfile k` of partitions after fewer than `k`
    edge deletions, its combination under union, truncation, and the cases
    `k = 0, 1`;
  - certificates of at most `k(v - 1)` edges from `k` successive spanning
    forests (`edgeFailureProfile_strongCertificateSize_le`);
  - the bridges (also characterized by the number of components), the
    partitions after their deletion, and `k`-edge-connectivity, with
    certificates of at most `2(v - 1)` and `k(v - 1)` edges;
  - the query bounds `min{n, 2^18·√(n·k(v - 1))}` for edge lists and
    `2^18·min{v², v·√(v·k)}` for matrices, and `2^19·v·√v` matrix queries
    for the bridges;
  - `strongCertificateSize_le_of_determined`: an output determined by another
    has no larger certificate size.
- Failure-profile lower bounds (`Graph/VertexFaults.lean`,
  `Graph/Enumeration.lean`, `Graph/FailureLower.lean`):
  - the vertex-failure profile `vertexFailureProfile k`, whose coordinates
    are the partitions of the surviving vertices in the induced graphs;
  - the enumeration adversary: identifying `r` independent `d`-subsets of a
    `q`-set from their membership bits costs `Q_{1/3} ≥ (7/1376)·r√(d(q−d))`
    (`enumeration_qQuery_ge`), with a weighted Schur test for the masks;
  - `(1/10000)·min{v², v√(vk)} ≤ Q_matrix` for both profiles, every `v ≥ 2`
    and every `k`, and the two-sided bound for edge failures
    (`edgeFailureProfile_qMatrix_theta`).
- Vertex-failure certificates (`Graph/VertexCertificate.lean`,
  `Graph/VertexReadouts.lean`, `Graph/VertexQueries.lean`):
  - the sparse vertex-connectivity certificate: every graph has a subgraph
    with at most `2kv` edges and the same partition after every deletion of
    fewer than `k` vertices (`exists_vertexFailureCertificate`), from a
    greedy construction and a Mader-type count (`card_le_of_blocking`);
  - the vertex profile's combination under union, and
    `b_{Σ^V_k} ≤ min{C(v, 2), 2kv}`
    (`vertexFailureProfile_strongCertificateSize_le`);
  - the articulation points (by the number of components and by
    separation), the partitions after their deletion, and
    `k`-vertex-connectivity, with certificates of at most `4v` and `2kv`
    edges;
  - the query bounds `min{n, 2^18·√(n·2kv)}` for edge lists and
    `2^18·min{v², v·√(v·k)}` for matrices, `2^19·v·√v` matrix queries for
    the articulation points, and the two-sided matrix bound for both
    profiles (`failureProfiles_qMatrix_theta`).
- The paper correspondence follows the paper's current numbering, which
  shifted from Section 6 onward. All numbered results of Section 6 are
  formalized, and the README and library guide list the graph applications
  among the headline statements.
- `MonoidProductChecks.lean` guards the axioms of every public theorem of
  the Section 6 modules.
- The sampling lemma and the rank-doubling lemma of the ordered-product
  section as standalone statements in the paper's form, with explicit
  constants: `beta_sampling` (`lem:beta-sampling`, cost
  `768·β·T·√h·L^{3/2}`, `Ordered/BetaSampling.lean`) and `rank_doubling`
  (`lem:beta-rank-doubling`, for an arbitrary rank-`r` family with arbitrary
  seed weights, cost `5760·β·A·L⁴·√m`, `Ordered/RankDoublingLemma.lean`).
  The recursion behind the logarithmic-exponent theorem applies exactly this
  doubling step (`summary2_succ_succ_eq`).

## 0.1.0

- First public release of the `MonoidProduct` library.
- Formalizes the results of *The quantum query complexity of the semigroup
  product problem* (Lee and Santha): commutative aperiodic monoids,
  stably ordered monoids, finite aperiodic semigroups, and minimum-weight
  matroid bases.
- Depends on QuantumQueryComplexity and on the `Sunflower` library of TCS
  formalizations, each pinned to a fixed commit.
- Requires Lean and Mathlib 4.35.0-rc2; exact dependencies are in the manifest.
