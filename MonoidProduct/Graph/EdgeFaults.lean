import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import MonoidProduct.Certificates.Readout
import MonoidProduct.Graph.Components
set_option linter.style.header false

/-!
# Edge-failure profiles

`monoid.tex`, section `sec:failure-profiles`: `eq:edge-failure-profile`, the paragraph "Edge
failures", and the bridge and `k`-edge-connectivity readouts of the text after
`eq:failure-profile-queries`.  Write `v = #V` and `N = C(v, 2)`.

* `edgeFailureProfile k S` (`Σ^E_k(S)`): the component partition `π(S \ F)` for every set `F`
  of fewer than `k` possible edges, present or absent (`EdgeFailureSet V k`).  It is one output
  in the fixed finite type `EdgeFailureSet V k → Finset (V × V)`.  The paper takes `k ≥ 1`;
  `k = 0` gives the empty family.
* **Union.**  Deletion commutes with union and partitions combine by their join, so the profile
  of a union is determined by the profiles of its parts (`edgeFailureProfile_union_congr`).
  Equivalence under extensions is therefore equality of profiles
  (`extensionEquiv_edgeFailureProfile_iff`), and a subgraph with the same profile is a strong
  certificate (`isStrongCertificate_edgeFailureProfile`).
* **Successive spanning forests** (`forestStack S k`).  `F_1` is a spanning forest of `S`,
  `F_{i+1}` a spanning forest of `S \ (F_1 ∪ ⋯ ∪ F_i)` (`forestLayer`), and
  `H = F_1 ∪ ⋯ ∪ F_k`.  The forests are pairwise disjoint, so a set `F` of fewer than `k`
  edges misses one of them (`exists_disjoint_forestLayer`).  An edge of `S` outside `H` lies in
  every residual graph, so its endpoints are connected in every forest, in particular in one
  that `F` misses.  Hence `π(H \ F) = π(S \ F)` (`connectedComponents_forestStack_sdiff`).  As
  `H` has at most `k(v - 1)` edges (`card_forestStack_le`),
  `b_{Σ^E_k} ≤ min{N, k(v - 1)}` (`edgeFailureProfile_strongCertificateSize_le`).
* **Truncation and small `k`.**  The profile for `k' ≤ k` is a restriction of the profile for
  `k` (`edgeFailureProfile_of_le`); at `k = 1` the profile is the component partition
  (`edgeFailureProfile_one_strongCertificateSize`), and at `k = 0` it is constant.
* **Bridges** (`bridges`): the edges of `S` that are bridges in Mathlib's sense, those whose
  deletion disconnects their endpoints, equivalently those whose deletion increases the number
  of components (`mem_bridges_iff_card_lt`).  The profile for `k = 2` determines them
  (`mem_bridges_iff_edgeFailureProfile`) and the partitions after their deletion
  (`bridgePartitions`), so both have certificates of at most `min{N, 2(v - 1)}` edges.
* **`k`-edge-connectivity** (`isEdgeConnected`, Mathlib's `IsEdgeConnected`): every coordinate
  of the profile is the one-block partition (`isEdgeConnected_iff_edgeFailureProfile`), so its
  certificate size is at most `min{N, k(v - 1)}`.
-/

namespace MonoidProduct.Graph

open SimpleGraph Certificates

/-! ## The profile -/

/-- The failure sets of the `k`-edge-failure profile: the sets of fewer than `k` possible edges,
present or absent. -/
abbrev EdgeFailureSet (V : Type*) (k : ℕ) : Type _ := {F : Finset (Edge V) // F.card < k}

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The edge-failure profile** `Σ^E_k(S)` (`eq:edge-failure-profile`): for every set `F` of
fewer than `k` possible edges, the component partition of `toGraph S` with the edges of `F`
deleted. -/
noncomputable def edgeFailureProfile (k : ℕ) (S : Finset (Edge V)) :
    EdgeFailureSet V k → Finset (V × V) :=
  fun F => connectedComponents (S \ F.1)

/-- The coordinate at `F` is the reachability relation of `toGraph (S \ F)`. -/
theorem mem_edgeFailureProfile {k : ℕ} {S : Finset (Edge V)} {F : EdgeFailureSet V k}
    {u w : V} : (u, w) ∈ edgeFailureProfile k S F ↔ (toGraph (S \ F.1)).Reachable u w :=
  mem_connectedComponents

/-- **Deletion commutes with union**, and partitions combine by their join: the profile of a
union is determined by the profiles of its parts. -/
theorem edgeFailureProfile_union_congr {k : ℕ} {S S' T T' : Finset (Edge V)}
    (hS : edgeFailureProfile k S = edgeFailureProfile k S')
    (hT : edgeFailureProfile k T = edgeFailureProfile k T') :
    edgeFailureProfile k (S ∪ T) = edgeFailureProfile k (S' ∪ T') := by
  funext F
  simp only [edgeFailureProfile, Finset.union_sdiff_distrib]
  exact connectedComponents_union_congr (congrFun hS F) (congrFun hT F)

/-- **Equivalence under extensions is equality of profiles.** -/
theorem extensionEquiv_edgeFailureProfile_iff {k : ℕ} {S T : Finset (Edge V)} :
    ExtensionEquiv (edgeFailureProfile k) S T ↔
      edgeFailureProfile k S = edgeFailureProfile k T :=
  extensionEquiv_iff_of_merge (f := edgeFailureProfile k) fun _ _ _ _ =>
    edgeFailureProfile_union_congr

/-- **A subgraph with the same profile is a strong certificate** for the profile. -/
theorem isStrongCertificate_edgeFailureProfile {k : ℕ} {C S : Finset (Edge V)} (hCS : C ⊆ S)
    (h : edgeFailureProfile k C = edgeFailureProfile k S) :
    IsStrongCertificate (edgeFailureProfile k) C S :=
  ⟨hCS, extensionEquiv_edgeFailureProfile_iff.mpr h⟩

/-! ## Successive spanning forests -/

omit [DecidableEq V] in
/-- A fixed spanning forest of `toGraph S`: an acyclic subgraph with the same reachability. -/
noncomputable def spanningForest (S : Finset (Edge V)) : Finset (Edge V) :=
  (exists_spanningForest S).choose

omit [DecidableEq V] in
theorem spanningForest_subset (S : Finset (Edge V)) : spanningForest S ⊆ S :=
  (exists_spanningForest S).choose_spec.1

omit [DecidableEq V] in
theorem reachable_spanningForest (S : Finset (Edge V)) :
    (toGraph (spanningForest S)).Reachable = (toGraph S).Reachable :=
  (exists_spanningForest S).choose_spec.2.2

omit [DecidableEq V] in
theorem isAcyclic_spanningForest (S : Finset (Edge V)) : (toGraph (spanningForest S)).IsAcyclic :=
  (exists_spanningForest S).choose_spec.2.1

omit [DecidableEq V] in
theorem card_spanningForest_le (S : Finset (Edge V)) :
    (spanningForest S).card ≤ Fintype.card V - 1 :=
  card_le_of_isAcyclic (isAcyclic_spanningForest S)

/-- **Successive spanning forests**: `forestStack S k = F_1 ∪ ⋯ ∪ F_k`, where `F_{i+1}` is a
spanning forest of `S \ (F_1 ∪ ⋯ ∪ F_i)`. -/
noncomputable def forestStack (S : Finset (Edge V)) : ℕ → Finset (Edge V)
  | 0 => ∅
  | i + 1 => forestStack S i ∪ spanningForest (S \ forestStack S i)

/-- The forest `F_{i+1}`: a spanning forest of `S` without the first `i` forests. -/
noncomputable def forestLayer (S : Finset (Edge V)) (i : ℕ) : Finset (Edge V) :=
  spanningForest (S \ forestStack S i)

theorem forestStack_succ (S : Finset (Edge V)) (i : ℕ) :
    forestStack S (i + 1) = forestStack S i ∪ forestLayer S i :=
  rfl

theorem forestLayer_subset (S : Finset (Edge V)) (i : ℕ) :
    forestLayer S i ⊆ S \ forestStack S i :=
  spanningForest_subset _

/-- **Each layer is a spanning forest of what the earlier layers leave**: it is acyclic and has
the reachability of `S \ (F_1 ∪ ⋯ ∪ F_i)`. -/
theorem isAcyclic_forestLayer (S : Finset (Edge V)) (i : ℕ) :
    (toGraph (forestLayer S i)).IsAcyclic :=
  isAcyclic_spanningForest _

theorem reachable_forestLayer (S : Finset (Edge V)) (i : ℕ) :
    (toGraph (forestLayer S i)).Reachable = (toGraph (S \ forestStack S i)).Reachable :=
  reachable_spanningForest _

/-- `forestStack S k` is the union `F_1 ∪ ⋯ ∪ F_k` of the first `k` layers. -/
theorem forestStack_eq_biUnion (S : Finset (Edge V)) :
    ∀ k, forestStack S k = (Finset.range k).biUnion (forestLayer S)
  | 0 => rfl
  | k + 1 => by
      rw [forestStack_succ, forestStack_eq_biUnion S k, Finset.range_add_one,
        Finset.biUnion_insert, Finset.union_comm]

/-- The forests are subgraphs of `S`. -/
theorem forestStack_subset (S : Finset (Edge V)) : ∀ k, forestStack S k ⊆ S
  | 0 => Finset.empty_subset _
  | i + 1 => Finset.union_subset (forestStack_subset S i)
      ((forestLayer_subset S i).trans Finset.sdiff_subset)

theorem forestStack_mono (S : Finset (Edge V)) : Monotone (forestStack S) :=
  monotone_nat_of_le_succ fun _ => Finset.subset_union_left

theorem forestLayer_subset_forestStack (S : Finset (Edge V)) {i j : ℕ} (h : i < j) :
    forestLayer S i ⊆ forestStack S j :=
  (Finset.subset_union_right (s₁ := forestStack S i)).trans (forestStack_mono S h)

/-- **The forests are pairwise disjoint**: each is taken from what the earlier ones leave. -/
theorem disjoint_forestLayer (S : Finset (Edge V)) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (forestLayer S i) (forestLayer S j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact Finset.disjoint_of_subset_left (forestLayer_subset_forestStack S h)
      (Finset.disjoint_of_subset_right (forestLayer_subset S j) Finset.disjoint_sdiff)
  · exact (Finset.disjoint_of_subset_left (forestLayer_subset_forestStack S h)
      (Finset.disjoint_of_subset_right (forestLayer_subset S i) Finset.disjoint_sdiff)).symm

/-- **`k` forests have at most `k(v - 1)` edges.** -/
theorem card_forestStack_le (S : Finset (Edge V)) :
    ∀ k, (forestStack S k).card ≤ k * (Fintype.card V - 1)
  | 0 => by simp [forestStack]
  | k + 1 => by
      rw [forestStack_succ, Nat.succ_mul]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add (card_forestStack_le S k) (card_spanningForest_le _))

/-- **Pigeonhole**: a set of fewer than `k` edges misses one of the first `k` forests, since
they are pairwise disjoint. -/
theorem exists_disjoint_forestLayer (S : Finset (Edge V)) {k : ℕ} {F : Finset (Edge V)}
    (hF : F.card < k) : ∃ i < k, Disjoint (forestLayer S i) F := by
  by_contra hcon
  have hpick : ∀ i ∈ Finset.range k, ∃ e ∈ forestLayer S i, e ∈ F := fun i hi =>
    Finset.not_disjoint_iff.mp fun hd => hcon ⟨i, Finset.mem_range.mp hi, hd⟩
  have : Nonempty (Edge V) := by
    obtain ⟨e, -, -⟩ := hpick 0 (Finset.mem_range.mpr (Nat.zero_lt_of_lt hF))
    exact ⟨e⟩
  choose! g hg1 hg2 using hpick
  have hinj : Set.InjOn g (Finset.range k : Set ℕ) := fun i hi j hj hij => by
    by_contra hne
    exact Finset.disjoint_left.mp (disjoint_forestLayer S hne) (hg1 i hi) (hij ▸ hg1 j hj)
  have := Finset.card_le_card_of_injOn g (fun i hi => hg2 i hi) hinj
  rw [Finset.card_range] at this
  omega

/-- **Successive spanning forests preserve the partition after fewer than `k` edge failures**
(`sec:failure-profiles`, "Edge failures"): `π(H \ F) = π(S \ F)` for `H = forestStack S k` and
every set `F` of fewer than `k` possible edges. -/
theorem connectedComponents_forestStack_sdiff (S : Finset (Edge V)) {k : ℕ}
    {F : Finset (Edge V)} (hF : F.card < k) :
    connectedComponents (forestStack S k \ F) = connectedComponents (S \ F) := by
  rw [connectedComponents_eq_iff]
  intro u w
  refine ⟨fun h => h.mono (toGraph_mono (Finset.sdiff_subset_sdiff (forestStack_subset S k)
    subset_rfl)), fun h => Matroid.reachable_of_forall_adj_reachable (fun a b hab => ?_) h⟩
  obtain ⟨e, he, hab'⟩ := toGraph_adj.mp hab
  rw [Finset.mem_sdiff] at he
  by_cases heH : e ∈ forestStack S k
  · exact (toGraph_adj.mpr ⟨e, Finset.mem_sdiff.mpr ⟨heH, he.2⟩, hab'⟩).reachable
  · obtain ⟨i, hi, hdisj⟩ := exists_disjoint_forestLayer S hF
    have heS : e ∈ S \ forestStack S i :=
      Finset.mem_sdiff.mpr ⟨he.1, fun h' => heH (forestStack_mono S hi.le h')⟩
    have hreach : (toGraph (forestLayer S i)).Reachable a b := by
      rw [forestLayer, reachable_spanningForest]
      exact (toGraph_adj.mpr ⟨e, heS, hab'⟩).reachable
    exact hreach.mono (toGraph_mono fun x hx => Finset.mem_sdiff.mpr
      ⟨forestLayer_subset_forestStack S hi hx, Finset.disjoint_left.mp hdisj hx⟩)

/-- The union of `k` successive spanning forests has the same profile. -/
theorem edgeFailureProfile_forestStack (k : ℕ) (S : Finset (Edge V)) :
    edgeFailureProfile k (forestStack S k) = edgeFailureProfile k S :=
  funext fun F => connectedComponents_forestStack_sdiff S F.2

/-- **`k` successive spanning forests are a strong certificate for the profile.** -/
theorem isStrongCertificate_forestStack (k : ℕ) (S : Finset (Edge V)) :
    IsStrongCertificate (edgeFailureProfile k) (forestStack S k) S :=
  isStrongCertificate_edgeFailureProfile (forestStack_subset S k)
    (edgeFailureProfile_forestStack k S)

/-- **Every graph has a strong certificate for its profile with at most `k(v - 1)` edges.** -/
theorem hasStrongCertificateBound_edgeFailureProfile (k : ℕ) :
    HasStrongCertificateBound (edgeFailureProfile (V := V) k) (k * (Fintype.card V - 1)) :=
  fun S => ⟨forestStack S k, isStrongCertificate_forestStack k S, card_forestStack_le S k⟩

/-- **The edge-failure profile** (`sec:failure-profiles`, "Edge failures"):
`b_{Σ^E_k} ≤ min{C(v, 2), k(v - 1)}`. -/
theorem edgeFailureProfile_strongCertificateSize_le (k : ℕ) :
    strongCertificateSize (edgeFailureProfile (V := V) k) ≤
      min ((Fintype.card V).choose 2) (k * (Fintype.card V - 1)) := by
  refine le_min ?_ (strongCertificateSize_le (hasStrongCertificateBound_edgeFailureProfile k))
  rw [← card_edge]
  exact strongCertificateSize_le_card _

/-- **Certificates for the profile within `min{C(v, 2), k(v - 1)}` edges.** -/
theorem hasStrongCertificateBound_min_edgeFailureProfile (k : ℕ) :
    HasStrongCertificateBound (edgeFailureProfile (V := V) k)
      (min ((Fintype.card V).choose 2) (k * (Fintype.card V - 1))) :=
  hasStrongCertificateBound_iff_size_le.mpr (edgeFailureProfile_strongCertificateSize_le k)

/-! ## Truncation, `k = 0` and `k = 1` -/

/-- **Truncation**: for `k' ≤ k`, the profile for `k'` is a restriction of the profile for
`k`. -/
theorem edgeFailureProfile_of_le {k k' : ℕ} (h : k' ≤ k) (S : Finset (Edge V))
    (F : EdgeFailureSet V k') :
    edgeFailureProfile k' S F = edgeFailureProfile k S ⟨F.1, F.2.trans_le h⟩ :=
  rfl

/-- Truncation does not increase the certificate size. -/
theorem edgeFailureProfile_strongCertificateSize_mono {k k' : ℕ} (h : k' ≤ k) :
    strongCertificateSize (edgeFailureProfile (V := V) k') ≤
      strongCertificateSize (edgeFailureProfile (V := V) k) :=
  strongCertificateSize_le_of_determined fun _ _ hST =>
    funext fun F => congrFun hST ⟨F.1, F.2.trans_le h⟩

/-- **`k = 0`**: there are no failure sets, so the profile is constant and needs no
certificate. -/
theorem edgeFailureProfile_zero_strongCertificateSize :
    strongCertificateSize (edgeFailureProfile (V := V) 0) = 0 :=
  strongCertificateSize_eq_zero_iff.mpr fun _ _ =>
    funext fun F => absurd F.2 (Nat.not_lt_zero _)

/-- **`k = 1`**: the only failure set is `∅`, at which the profile is the component
partition. -/
theorem edgeFailureProfile_one (S : Finset (Edge V)) :
    edgeFailureProfile 1 S ⟨∅, by simp⟩ = connectedComponents S := by
  simp [edgeFailureProfile]

/-- At `k = 1`, two graphs have the same profile exactly when they have the same partition. -/
theorem edgeFailureProfile_one_eq_iff {S T : Finset (Edge V)} :
    edgeFailureProfile 1 S = edgeFailureProfile 1 T ↔
      connectedComponents S = connectedComponents T := by
  constructor
  · intro h
    rw [← edgeFailureProfile_one, ← edgeFailureProfile_one, h]
  · intro h
    funext F
    have hF : F.1 = ∅ := Finset.card_eq_zero.mp (Nat.lt_one_iff.mp F.2)
    simp only [edgeFailureProfile, hF, Finset.sdiff_empty, h]

/-- At `k = 1` the profile has the certificate size of the component partition. -/
theorem edgeFailureProfile_one_strongCertificateSize :
    strongCertificateSize (edgeFailureProfile (V := V) 1) =
      strongCertificateSize (connectedComponents (V := V)) :=
  le_antisymm
    (strongCertificateSize_le_of_determined fun _ _ h => edgeFailureProfile_one_eq_iff.mpr h)
    (strongCertificateSize_le_of_determined fun _ _ h => edgeFailureProfile_one_eq_iff.mp h)

/-! ## Bridges -/

omit [Fintype V] [DecidableEq V] in
/-- Every possible edge is `s(u, w)` for some `u` and `w`. -/
theorem exists_edge_eq_mk (e : Edge V) : ∃ u w, (e : Sym2 V) = s(u, w) := by
  obtain ⟨⟨u, w⟩, h⟩ := Quot.exists_rep e.1
  exact ⟨u, w, h.symm⟩

omit [Fintype V] in
/-- Deleting one edge, in Mathlib's `deleteEdges` form. -/
theorem toGraph_sdiff_singleton (S : Finset (Edge V)) (e : Edge V) :
    toGraph (S \ {e}) = (toGraph S).deleteEdges {(e : Sym2 V)} := by
  rw [toGraph_sdiff_eq_deleteEdges]
  simp [pairs]

/-- **The bridges** of `toGraph S`: the edges of `S` whose deletion disconnects their endpoints
(Mathlib's `IsBridge`). -/
noncomputable def bridges (S : Finset (Edge V)) : Finset (Edge V) := by
  classical exact S.filter fun e => (toGraph S).IsBridge e

omit [Fintype V] [DecidableEq V] in
theorem mem_bridges {S : Finset (Edge V)} {e : Edge V} :
    e ∈ bridges S ↔ e ∈ S ∧ (toGraph S).IsBridge e := by
  simp [bridges]

omit [Fintype V] in
/-- For `e = s(u, w)`, being a bridge means that deleting `e` disconnects `u` and `w`. -/
theorem isBridge_iff_not_reachable_sdiff {S : Finset (Edge V)} {e : Edge V} {u w : V}
    (he : (e : Sym2 V) = s(u, w)) :
    (toGraph S).IsBridge e ↔ ¬(toGraph (S \ {e})).Reachable u w := by
  rw [toGraph_sdiff_singleton, he, isBridge_iff]

/-- **The profile for `k = 2` determines the bridges**: `e = s(u, w)` is a bridge exactly when
`u` and `w` are connected before, and not after, deleting `e`. -/
theorem mem_bridges_iff_edgeFailureProfile {S : Finset (Edge V)} {e : Edge V} {u w : V}
    (he : (e : Sym2 V) = s(u, w)) :
    e ∈ bridges S ↔ (u, w) ∈ edgeFailureProfile 2 S ⟨∅, by simp⟩ ∧
      (u, w) ∉ edgeFailureProfile 2 S ⟨{e}, by simp⟩ := by
  rw [mem_bridges, mem_edgeFailureProfile, mem_edgeFailureProfile, Finset.sdiff_empty,
    isBridge_iff_not_reachable_sdiff he]
  constructor
  · rintro ⟨heS, hb⟩
    exact ⟨(toGraph_adj.mpr ⟨e, heS, he⟩).reachable, hb⟩
  · rintro ⟨hr, hb⟩
    refine ⟨?_, hb⟩
    by_contra heS
    rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem heS] at hb
    exact hb hr

omit [Fintype V] in
/-- **Bridges increase the number of components**: an edge of `S` is a bridge exactly when
deleting it increases the number of connected components. -/
theorem mem_bridges_iff_card_lt [Finite V] {S : Finset (Edge V)} {e : Edge V} :
    e ∈ bridges S ↔ e ∈ S ∧ Nat.card (toGraph S).ConnectedComponent <
      Nat.card (toGraph (S \ {e})).ConnectedComponent := by
  obtain ⟨u, w, he⟩ := exists_edge_eq_mk e
  rw [mem_bridges, isBridge_iff_not_reachable_sdiff he]
  refine and_congr_right fun heS => ?_
  have hle : toGraph (S \ {e}) ≤ toGraph S := toGraph_mono Finset.sdiff_subset
  let φ := ConnectedComponent.map (Hom.ofLE hle)
  have hφ : ∀ x, φ ((toGraph (S \ {e})).connectedComponentMk x) =
      (toGraph S).connectedComponentMk x := fun x => ConnectedComponent.map_mk _ _
  have hsurj : Function.Surjective φ := fun c => by
    induction c using ConnectedComponent.ind with
    | h x => exact ⟨_, hφ x⟩
  have hadj : (toGraph S).Adj u w := toGraph_adj.mpr ⟨e, heS, he⟩
  constructor
  · intro hnr
    refine lt_of_le_of_ne (Nat.card_le_card_of_surjective φ hsurj) fun heq => hnr ?_
    have hinj := (hsurj.bijective_of_nat_card_le heq.ge).1
    rw [← ConnectedComponent.eq]
    exact hinj (by rw [hφ, hφ, ConnectedComponent.eq]; exact hadj.reachable)
  · intro hlt hr
    have hinj : Function.Injective φ := by
      intro c d hcd
      induction c using ConnectedComponent.ind with
      | h x =>
      induction d using ConnectedComponent.ind with
      | h y =>
      rw [hφ, hφ, ConnectedComponent.eq] at hcd
      rw [ConnectedComponent.eq]
      refine Matroid.reachable_of_forall_adj_reachable (fun a b hab => ?_) hcd
      obtain ⟨e', he', hab'⟩ := toGraph_adj.mp hab
      by_cases hee : e' = e
      · subst hee
        rcases Sym2.eq_iff.mp (he.symm.trans hab') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hr
        · exact hr.symm
      · exact (toGraph_adj.mpr ⟨e', Finset.mem_sdiff.mpr ⟨he', by simpa using hee⟩,
          hab'⟩).reachable
    have := Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)
    omega

/-- The profile for `k = 2` determines the bridges. -/
theorem bridges_eq_of_edgeFailureProfile {S T : Finset (Edge V)}
    (h : edgeFailureProfile 2 S = edgeFailureProfile 2 T) : bridges S = bridges T := by
  ext e
  obtain ⟨u, w, he⟩ := exists_edge_eq_mk e
  rw [mem_bridges_iff_edgeFailureProfile he, mem_bridges_iff_edgeFailureProfile he, h]

/-- **Bridges** (`sec:failure-profiles`): through the profile for `k = 2`, their certificate size
is at most `min{C(v, 2), 2(v - 1)}`. -/
theorem bridges_strongCertificateSize_le :
    strongCertificateSize (bridges (V := V)) ≤
      min ((Fintype.card V).choose 2) (2 * (Fintype.card V - 1)) :=
  (strongCertificateSize_le_of_determined fun _ _ => bridges_eq_of_edgeFailureProfile).trans
    (edgeFailureProfile_strongCertificateSize_le 2)

/-- **Certificates for the bridges within `min{C(v, 2), 2(v - 1)}` edges.** -/
theorem hasStrongCertificateBound_bridges :
    HasStrongCertificateBound (bridges (V := V))
      (min ((Fintype.card V).choose 2) (2 * (Fintype.card V - 1))) :=
  hasStrongCertificateBound_iff_size_le.mpr bridges_strongCertificateSize_le

/-- **The bridges with the partitions after their deletion**: `some π(S \ {e})` when `e` is a
bridge of `toGraph S`, and `none` otherwise. -/
noncomputable def bridgePartitions (S : Finset (Edge V)) : Edge V → Option (Finset (V × V)) :=
  fun e => if e ∈ bridges S then some (connectedComponents (S \ {e})) else none

theorem bridgePartitions_eq_some_iff {S : Finset (Edge V)} {e : Edge V} {P : Finset (V × V)} :
    bridgePartitions S e = some P ↔ e ∈ bridges S ∧ P = connectedComponents (S \ {e}) := by
  unfold bridgePartitions
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem bridgePartitions_eq_none_iff {S : Finset (Edge V)} {e : Edge V} :
    bridgePartitions S e = none ↔ e ∉ bridges S := by
  unfold bridgePartitions
  split_ifs with h <;> simp [h]

/-- The profile for `k = 2` determines the bridges and the partitions after their deletion. -/
theorem bridgePartitions_eq_of_edgeFailureProfile {S T : Finset (Edge V)}
    (h : edgeFailureProfile 2 S = edgeFailureProfile 2 T) :
    bridgePartitions S = bridgePartitions T := by
  funext e
  have hb := bridges_eq_of_edgeFailureProfile h
  have hπ : connectedComponents (S \ {e}) = connectedComponents (T \ {e}) :=
    congrFun h ⟨{e}, by simp⟩
  simp only [bridgePartitions, hb, hπ]

/-- **The bridges and the partitions after their deletion** (`sec:failure-profiles`): their
certificate size is at most `min{C(v, 2), 2(v - 1)}`. -/
theorem bridgePartitions_strongCertificateSize_le :
    strongCertificateSize (bridgePartitions (V := V)) ≤
      min ((Fintype.card V).choose 2) (2 * (Fintype.card V - 1)) :=
  (strongCertificateSize_le_of_determined fun _ _ =>
    bridgePartitions_eq_of_edgeFailureProfile).trans (edgeFailureProfile_strongCertificateSize_le 2)

/-- **Certificates for the bridges and their partitions within `min{C(v, 2), 2(v - 1)}`
edges.** -/
theorem hasStrongCertificateBound_bridgePartitions :
    HasStrongCertificateBound (bridgePartitions (V := V))
      (min ((Fintype.card V).choose 2) (2 * (Fintype.card V - 1))) :=
  hasStrongCertificateBound_iff_size_le.mpr bridgePartitions_strongCertificateSize_le

/-! ## `k`-edge-connectivity -/

/-- **`k`-edge-connectivity**: whether `toGraph S` stays connected after deleting any fewer
than `k` edges (Mathlib's `IsEdgeConnected`). -/
noncomputable def isEdgeConnected (k : ℕ) (S : Finset (Edge V)) : Bool := by
  classical exact decide ((toGraph S).IsEdgeConnected k)

omit [Fintype V] [DecidableEq V] in
theorem isEdgeConnected_eq_true_iff {k : ℕ} {S : Finset (Edge V)} :
    isEdgeConnected k S = true ↔ (toGraph S).IsEdgeConnected k := by
  simp [isEdgeConnected]

/-- **The profile for `k` determines `k`-edge-connectivity**: `toGraph S` is `k`-edge-connected
exactly when every coordinate of the profile relates every pair of vertices.  Mathlib's
deletions range over sets of `Sym2 V` with fewer than `k` elements; their diagonal elements
delete nothing. -/
theorem isEdgeConnected_iff_edgeFailureProfile {k : ℕ} {S : Finset (Edge V)} :
    (toGraph S).IsEdgeConnected k ↔
      ∀ (F : EdgeFailureSet V k) (u w : V), (u, w) ∈ edgeFailureProfile k S F := by
  constructor
  · intro h F u w
    rw [mem_edgeFailureProfile, toGraph_sdiff_eq_deleteEdges]
    refine h u w ?_
    rw [Set.encard_coe_eq_coe_finsetCard, card_pairs]
    exact_mod_cast F.2
  · intro h u w s hs
    classical
    let F : Finset (Edge V) := Finset.univ.filter fun e => (e : Sym2 V) ∈ s
    have hFs : (pairs F : Set (Sym2 V)) ⊆ s := fun x hx => by
      obtain ⟨hx', hxF⟩ := mem_pairs.mp hx
      exact (Finset.mem_filter.mp hxF).2
    have hF : F.card < k := by
      have hle := Set.encard_le_encard hFs
      rw [Set.encard_coe_eq_coe_finsetCard, card_pairs] at hle
      exact_mod_cast hle.trans_lt hs
    have h' := h ⟨F, hF⟩ u w
    rw [mem_edgeFailureProfile, toGraph_sdiff_eq_deleteEdges] at h'
    refine h'.mono fun a b hab => ?_
    rw [deleteEdges_adj] at hab ⊢
    refine ⟨hab.1, fun has => hab.2 ?_⟩
    have hd : ¬(s(a, b) : Sym2 V).IsDiag := by
      rw [Sym2.mk_isDiag_iff]
      exact hab.1.ne
    exact mem_pairs.mpr ⟨hd, Finset.mem_filter.mpr ⟨Finset.mem_univ _, has⟩⟩

/-- The profile for `k` determines `k`-edge-connectivity. -/
theorem isEdgeConnected_eq_of_edgeFailureProfile {k : ℕ} {S T : Finset (Edge V)}
    (h : edgeFailureProfile k S = edgeFailureProfile k T) :
    isEdgeConnected k S = isEdgeConnected k T := by
  rw [Bool.eq_iff_iff, isEdgeConnected_eq_true_iff, isEdgeConnected_eq_true_iff,
    isEdgeConnected_iff_edgeFailureProfile, isEdgeConnected_iff_edgeFailureProfile, h]

/-- **`k`-edge-connectivity** (`sec:failure-profiles`): its certificate size is at most
`min{C(v, 2), k(v - 1)}`. -/
theorem edgeConnectivity_strongCertificateSize_le (k : ℕ) :
    strongCertificateSize (isEdgeConnected (V := V) k) ≤
      min ((Fintype.card V).choose 2) (k * (Fintype.card V - 1)) :=
  (strongCertificateSize_le_of_determined fun _ _ => isEdgeConnected_eq_of_edgeFailureProfile).trans
    (edgeFailureProfile_strongCertificateSize_le k)

/-- **Certificates for `k`-edge-connectivity within `min{C(v, 2), k(v - 1)}` edges.** -/
theorem hasStrongCertificateBound_isEdgeConnected (k : ℕ) :
    HasStrongCertificateBound (isEdgeConnected (V := V) k)
      (min ((Fintype.card V).choose 2) (k * (Fintype.card V - 1))) :=
  hasStrongCertificateBound_iff_size_le.mpr (edgeConnectivity_strongCertificateSize_le k)

end MonoidProduct.Graph
