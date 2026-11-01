import MonoidProduct.Graph.Basic
import MonoidProduct.Certificates.Basic
import MonoidProduct.Matroid.Graphic
set_option linter.style.header false

/-!
# Connected components: certificates of at most `v - 1` edges

`monoid.tex`, section `sec:graph-certificates`, paragraph "Connected components".  Write
`v = #V`.  The partition `π(G)` of `V` into connected components has strong certificates of at
most `v - 1` edges, and so do connectivity and `s`–`t` connectivity.

* `connectedComponents S : Finset (V × V)` records the partition `π(S)` by its labelled
  reachability relation (`mem_connectedComponents`).  Equality of these relations is equality
  of the partitions, on a fixed finite output type.
* Under union, partitions combine by their join (`reachable_union_of`).  So `C ∼_π S`, for
  every extension, exactly when `C` and `S` have the same partition
  (`extensionEquiv_connectedComponents_iff`).
* Every graph has a spanning forest: an acyclic subgraph with the same reachability
  (`exists_spanningForest`, from Mathlib's `exists_isAcyclic_reachable_eq_le`).
* A forest has at most `v - 1` edges (`card_le_of_isAcyclic`).  This reuses the component
  count of the graphic matroid of `Matroid/Graphic.lean`, whose independent sets are the forests
  (`graphicMatroid_indep_pairs_iff`).  So a spanning forest is a strong certificate of at most
  `v - 1` edges (`hasStrongCertificateBound_connectedComponents`).
* `connectedComponents_strongCertificateSize_le`: `b_π ≤ v - 1`.  Postprocessing then gives
  `connectivity_strongCertificateSize_le` and `stConnectivity_strongCertificateSize_le`, with
  the certificates `hasStrongCertificateBound_isConnected` and
  `hasStrongCertificateBound_isSTConnected`.

Subtraction is natural: with no vertices there are no edges and every bound is `0`.
-/

namespace MonoidProduct.Graph

open SimpleGraph Certificates

variable {V : Type*}

/-! ## Forests -/

/-- **A forest on `V` has at most `#V - 1` edges.** -/
theorem card_le_of_isAcyclic [Fintype V] {S : Finset (Edge V)} (h : (toGraph S).IsAcyclic) :
    S.card ≤ Fintype.card V - 1 := by
  have hc : (pairs S).card + Nat.card (toGraph S).ConnectedComponent ≤ Nat.card V :=
    Matroid.card_add_natCard_connectedComponent_le (pairs S) (fun _ he => (mem_pairs.mp he).1) h
  rw [card_pairs, Nat.card_eq_fintype_card (α := V)] at hc
  rcases isEmpty_or_nonempty V with hV | hV
  · have : Fintype.card V = 0 := Fintype.card_eq_zero
    omega
  · obtain ⟨v⟩ := hV
    have : Nonempty (toGraph S).ConnectedComponent := ⟨(toGraph S).connectedComponentMk v⟩
    have : 0 < Nat.card (toGraph S).ConnectedComponent := Nat.card_pos
    omega

/-- **Forests are the independent sets of the graphic matroid**: through the injection into
`Sym2 V`, an edge set is independent in `Matroid.graphicMatroid V` exactly when it spans an
acyclic graph. -/
theorem graphicMatroid_indep_pairs_iff [Finite V] {S : Finset (Edge V)} :
    (Matroid.graphicMatroid V).Indep (pairs S : Set (Sym2 V)) ↔ (toGraph S).IsAcyclic := by
  rw [Matroid.graphicMatroid_indep_iff, Matroid.IsForestEdgeSet]
  exact ⟨fun h => h.2, fun h => ⟨fun _ he => (mem_pairs.mp he).1, h⟩⟩

/-- **Spanning forests**: every graph has an acyclic subgraph with the same reachability. -/
theorem exists_spanningForest [Finite V] (S : Finset (Edge V)) :
    ∃ C ⊆ S, (toGraph C).IsAcyclic ∧ (toGraph C).Reachable = (toGraph S).Reachable := by
  have := Fintype.ofFinite V
  classical
  obtain ⟨F, hFS, hF, hreach⟩ := (toGraph S).exists_isAcyclic_reachable_eq_le
  refine ⟨ofGraph F, ?_, ?_, ?_⟩
  · rw [← toGraph_le_toGraph, toGraph_ofGraph]
    exact hFS
  · rwa [toGraph_ofGraph]
  · rwa [toGraph_ofGraph]

/-! ## The component partition -/

section Partition

variable [Fintype V]

/-- **The component partition** `π(S)` of `V`, recorded by its labelled reachability relation:
`(u, w) ∈ connectedComponents S` when `u` and `w` lie in the same component of `toGraph S`. -/
noncomputable def connectedComponents (S : Finset (Edge V)) : Finset (V × V) := by
  classical exact Finset.univ.filter fun p => (toGraph S).Reachable p.1 p.2

@[simp] theorem mem_connectedComponents {S : Finset (Edge V)} {u w : V} :
    (u, w) ∈ connectedComponents S ↔ (toGraph S).Reachable u w := by
  simp [connectedComponents]

/-- Two graphs have the same partition exactly when they have the same reachability. -/
theorem connectedComponents_eq_iff {S T : Finset (Edge V)} :
    connectedComponents S = connectedComponents T ↔
      ∀ u w, (toGraph S).Reachable u w ↔ (toGraph T).Reachable u w := by
  constructor
  · intro h u w
    rw [← mem_connectedComponents, h, mem_connectedComponents]
  · intro h
    ext ⟨u, w⟩
    rw [mem_connectedComponents, mem_connectedComponents, h]

end Partition

section Union

variable [DecidableEq V]

/-- **Partitions combine by their join**: if `S`-reachability implies `S'`-reachability and
`T`-reachability implies `T'`-reachability, then `(S ∪ T)`-reachability implies
`(S' ∪ T')`-reachability. -/
theorem reachable_union_of {S S' T T' : Finset (Edge V)}
    (hS : ∀ u w, (toGraph S).Reachable u w → (toGraph S').Reachable u w)
    (hT : ∀ u w, (toGraph T).Reachable u w → (toGraph T').Reachable u w) {u w : V}
    (h : (toGraph (S ∪ T)).Reachable u w) : (toGraph (S' ∪ T')).Reachable u w := by
  refine Matroid.reachable_of_forall_adj_reachable (fun a b hab => ?_) h
  rw [toGraph_union, sup_adj] at hab
  rw [toGraph_union]
  rcases hab with hab | hab
  · exact (hS a b hab.reachable).mono le_sup_left
  · exact (hT a b hab.reachable).mono le_sup_right

variable [Fintype V]

theorem connectedComponents_union_congr {S S' T T' : Finset (Edge V)}
    (hS : connectedComponents S = connectedComponents S')
    (hT : connectedComponents T = connectedComponents T') :
    connectedComponents (S ∪ T) = connectedComponents (S' ∪ T') := by
  rw [connectedComponents_eq_iff] at hS hT ⊢
  exact fun u w => ⟨reachable_union_of (fun a b => (hS a b).1) (fun a b => (hT a b).1),
    reachable_union_of (fun a b => (hS a b).2) (fun a b => (hT a b).2)⟩

/-- **Equivalence under extensions is equality of partitions**, since partitions combine by
their join. -/
theorem extensionEquiv_connectedComponents_iff {S T : Finset (Edge V)} :
    ExtensionEquiv connectedComponents S T ↔ connectedComponents S = connectedComponents T :=
  extensionEquiv_iff_of_merge (f := connectedComponents) fun _ _ _ _ =>
    connectedComponents_union_congr

/-- **A spanning subgraph certifies the partition**: a subgraph `C ⊆ S` with the same
reachability as `S` is a strong certificate for `π`, under every extension. -/
theorem isStrongCertificate_connectedComponents {S C : Finset (Edge V)} (hCS : C ⊆ S)
    (h : (toGraph C).Reachable = (toGraph S).Reachable) :
    IsStrongCertificate connectedComponents C S :=
  ⟨hCS, extensionEquiv_connectedComponents_iff.mpr
    (connectedComponents_eq_iff.mpr fun u w => by rw [h])⟩

/-- **Every graph has a strong certificate for its partition with at most `v - 1` edges**: a
spanning forest. -/
theorem hasStrongCertificateBound_connectedComponents :
    HasStrongCertificateBound (connectedComponents (V := V)) (Fintype.card V - 1) := fun S => by
  obtain ⟨C, hCS, hC, hreach⟩ := exists_spanningForest S
  exact ⟨C, isStrongCertificate_connectedComponents hCS hreach, card_le_of_isAcyclic hC⟩

/-- **The component partition** (`sec:graph-certificates`): `b_π ≤ v - 1`. -/
theorem connectedComponents_strongCertificateSize_le :
    strongCertificateSize (connectedComponents (V := V)) ≤ Fintype.card V - 1 :=
  strongCertificateSize_le hasStrongCertificateBound_connectedComponents

end Union

/-! ## Connectivity and `s`–`t` connectivity -/

/-- **Connectivity**: whether `toGraph S` is connected.  Mathlib's `Connected` includes
`Nonempty V`, so the graph on no vertices is not connected. -/
noncomputable def isConnected (S : Finset (Edge V)) : Bool := by
  classical exact decide (toGraph S).Connected

theorem isConnected_eq_true_iff {S : Finset (Edge V)} :
    isConnected S = true ↔ (toGraph S).Connected := by
  simp [isConnected]

/-- **`s`–`t` connectivity**: whether `s` and `t` lie in the same component of `toGraph S`. -/
noncomputable def isSTConnected (s t : V) (S : Finset (Edge V)) : Bool := by
  classical exact decide ((toGraph S).Reachable s t)

theorem isSTConnected_eq_true_iff {s t : V} {S : Finset (Edge V)} :
    isSTConnected s t S = true ↔ (toGraph S).Reachable s t := by
  simp [isSTConnected]

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Connectivity is a function of the partition. -/
theorem isConnected_eq_true_iff_connectedComponents {S : Finset (Edge V)} :
    isConnected S = true ↔ Nonempty V ∧ ∀ p : V × V, p ∈ connectedComponents S := by
  rw [isConnected_eq_true_iff, connected_iff, Preconnected, Prod.forall]
  simp only [mem_connectedComponents]
  exact and_comm

/-- **Connectivity** (`sec:graph-certificates`): its strong-certificate size is at most
`v - 1`. -/
theorem connectivity_strongCertificateSize_le :
    strongCertificateSize (isConnected (V := V)) ≤ Fintype.card V - 1 := by
  classical
  have h : isConnected (V := V) = fun S =>
      decide (Nonempty V ∧ ∀ p : V × V, p ∈ connectedComponents S) :=
    funext fun S => Bool.eq_iff_iff.mpr
      (isConnected_eq_true_iff_connectedComponents.trans decide_eq_true_iff.symm)
  rw [h]
  exact (strongCertificateSize_postcomp_le connectedComponents
    (fun R => decide (Nonempty V ∧ ∀ p : V × V, p ∈ R))).trans
    connectedComponents_strongCertificateSize_le

/-- **`s`–`t` connectivity** (`sec:graph-certificates`): its strong-certificate size is at most
`v - 1`, for fixed `s` and `t`. -/
theorem stConnectivity_strongCertificateSize_le (s t : V) :
    strongCertificateSize (isSTConnected s t) ≤ Fintype.card V - 1 := by
  classical
  have h : isSTConnected s t = fun S => decide ((s, t) ∈ connectedComponents S) :=
    funext fun S => Bool.eq_iff_iff.mpr
      (isSTConnected_eq_true_iff.trans (mem_connectedComponents.symm.trans decide_eq_true_iff.symm))
  rw [h]
  exact (strongCertificateSize_postcomp_le connectedComponents
    (fun R => decide ((s, t) ∈ R))).trans connectedComponents_strongCertificateSize_le

/-- **Certificates for connectivity**: every graph has a strong certificate of at most
`v - 1` edges. -/
theorem hasStrongCertificateBound_isConnected :
    HasStrongCertificateBound (isConnected (V := V)) (Fintype.card V - 1) :=
  hasStrongCertificateBound_iff_size_le.mpr connectivity_strongCertificateSize_le

/-- **Certificates for `s`–`t` connectivity**: every graph has a strong certificate of at most
`v - 1` edges. -/
theorem hasStrongCertificateBound_isSTConnected (s t : V) :
    HasStrongCertificateBound (isSTConnected s t) (Fintype.card V - 1) :=
  hasStrongCertificateBound_iff_size_le.mpr (stConnectivity_strongCertificateSize_le s t)

end MonoidProduct.Graph
