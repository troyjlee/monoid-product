import MonoidProduct.Graph.TwoColorings
import MonoidProduct.Graph.Sparse
set_option linter.style.header false

/-!
# Acceptance statements for graph certificates

The paper-facing statements of `monoid.tex`, section `sec:graph-certificates`, without the
query models.  They are restated with the definitions unfolded where that makes their meaning
visible, followed by small sanity checks.  Lean checks every `example` here against the
library's statement.

* The representation: `binom(V, 2)` has `C(v, 2)` elements, graphs keep all of `V`, and union of
  edge sets is union of graphs.
* The outputs: the component partition as a reachability relation, the set of all proper
  two-colourings, and the Boolean readouts as `decide` of Mathlib's predicates.
* The certificate bounds, and the certificates within them for every application.  "Strong
  certificate" is unfolded for the component partition, the two-colourings and
  `prop:sparse-certificates`: one subgraph preserves the output under **every** extension.
* `prop:sparse-certificates` in the paper's form, with `0 ≤ L < C(v, 2)` and `b_P` the maximum
  of the minimum certificate sizes.

The sanity checks cover:
* the empty vertex set, and a constant property;
* isolated vertices and a disconnected graph;
* the triangle, which is not bipartite and has a cycle;
* two bipartite graphs with different sets of two-colourings, so the output is more than a
  Boolean readout;
* two graphs with the same connectivity value where the smaller is not a strong certificate, so
  the extension clause matters;
* the sparse bound on a property whose yes-instances have no edges.
-/

namespace MonoidProduct.Graph

open SimpleGraph Certificates

/-! ## The representation and the outputs -/

section Statements

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `binom(V, 2)` has `C(v, 2)` elements. -/
example : Fintype.card (Edge V) = (Fintype.card V).choose 2 :=
  card_edge

/-- A graph is its edge set, on all of `V`.  No edges give the empty graph, all possible edges
give the complete graph, union of edge sets is union of graphs, and `#S` counts the edges. -/
example (S T : Finset (Edge V)) (u w : V) :
    ((toGraph S).Adj u w ↔ ∃ e ∈ S, (e : Sym2 V) = s(u, w)) ∧
      toGraph (∅ : Finset (Edge V)) = ⊥ ∧ toGraph (Finset.univ : Finset (Edge V)) = ⊤ ∧
      toGraph (S ∪ T) = toGraph S ⊔ toGraph T ∧ (toGraph S).edgeSet.ncard = S.card :=
  ⟨toGraph_adj, toGraph_empty, toGraph_univ, toGraph_union S T, ncard_edgeSet_toGraph S⟩

/-- **The outputs**: the full partition and the full set of proper two-colourings, and the
Boolean readouts of Mathlib's predicates. -/
example (S : Finset (Edge V)) (s t u w : V) (c : V → Fin 2) :
    ((u, w) ∈ connectedComponents S ↔ (toGraph S).Reachable u w) ∧
      (c ∈ twoColorings S ↔ ∀ u w, (toGraph S).Adj u w → c u ≠ c w) ∧
      (isConnected S = true ↔ (toGraph S).Connected) ∧
      (isSTConnected s t S = true ↔ (toGraph S).Reachable s t) ∧
      (isBipartite S = true ↔ (toGraph S).IsBipartite) ∧
      (hasCycle S = true ↔ ∃ (x : V) (p : (toGraph S).Walk x x), p.IsCycle) ∧
      (properTwoColoring S = none ↔ ¬(toGraph S).IsBipartite) ∧
      (properTwoColoring S = some c → ∀ u w, (toGraph S).Adj u w → c u ≠ c w) :=
  ⟨mem_connectedComponents, mem_twoColorings, isConnected_eq_true_iff,
    isSTConnected_eq_true_iff, isBipartite_eq_true_iff, hasCycle_eq_true_iff,
    properTwoColoring_eq_none_iff, properTwoColoring_spec⟩

/-! ## Certificate bounds -/

/-- **The component partition**, with strong certificates unfolded: every graph has a subgraph
of at most `v - 1` edges with the same reachability after **every** extension. -/
example (S : Finset (Edge V)) :
    ∃ C ⊆ S, C.card ≤ Fintype.card V - 1 ∧
      ∀ (K : Finset (Edge V)) (u w : V),
        (toGraph (C ∪ K)).Reachable u w ↔ (toGraph (S ∪ K)).Reachable u w := by
  obtain ⟨C, ⟨hCS, hext⟩, hcard⟩ := hasStrongCertificateBound_connectedComponents S
  exact ⟨C, hCS, hcard, fun K => connectedComponents_eq_iff.mp (hext K)⟩

/-- **All proper two-colourings**, with strong certificates unfolded: every graph has a subgraph
of at most `v` edges with the same proper two-colourings after **every** extension. -/
example (S : Finset (Edge V)) :
    ∃ C ⊆ S, C.card ≤ Fintype.card V ∧
      ∀ (K : Finset (Edge V)) (c : V → Fin 2),
        (∀ u w, (toGraph (C ∪ K)).Adj u w → c u ≠ c w) ↔
          (∀ u w, (toGraph (S ∪ K)).Adj u w → c u ≠ c w) := by
  obtain ⟨C, ⟨hCS, hext⟩, hcard⟩ := hasStrongCertificateBound_twoColorings S
  refine ⟨C, hCS, hcard, fun K c => ?_⟩
  rw [← mem_twoColorings, ← mem_twoColorings, hext K]

/-- **The certificate sizes**:
* `v - 1` for components, connectivity and `s`–`t` connectivity;
* `v` for two-colourings, bipartiteness, a canonical colouring, acyclicity and cycle
  detection. -/
example (s t : V) :
    strongCertificateSize (connectedComponents (V := V)) ≤ Fintype.card V - 1 ∧
      strongCertificateSize (isConnected (V := V)) ≤ Fintype.card V - 1 ∧
      strongCertificateSize (isSTConnected s t) ≤ Fintype.card V - 1 ∧
      strongCertificateSize (twoColorings (V := V)) ≤ Fintype.card V ∧
      strongCertificateSize (isBipartite (V := V)) ≤ Fintype.card V ∧
      strongCertificateSize (properTwoColoring (V := V)) ≤ Fintype.card V ∧
      strongCertificateSize (isAcyclic (V := V)) ≤ Fintype.card V ∧
      strongCertificateSize (hasCycle (V := V)) ≤ Fintype.card V :=
  ⟨connectedComponents_strongCertificateSize_le, connectivity_strongCertificateSize_le,
    stConnectivity_strongCertificateSize_le s t, twoColorings_strongCertificateSize_le,
    bipartite_strongCertificateSize_le, properTwoColoring_strongCertificateSize_le,
    isAcyclic_strongCertificateSize_le, cycle_strongCertificateSize_le⟩

/-- **The certificates themselves**: every graph has a strong certificate within each of these
bounds. -/
example (s t : V) :
    HasStrongCertificateBound (connectedComponents (V := V)) (Fintype.card V - 1) ∧
      HasStrongCertificateBound (isConnected (V := V)) (Fintype.card V - 1) ∧
      HasStrongCertificateBound (isSTConnected s t) (Fintype.card V - 1) ∧
      HasStrongCertificateBound (twoColorings (V := V)) (Fintype.card V) ∧
      HasStrongCertificateBound (isBipartite (V := V)) (Fintype.card V) ∧
      HasStrongCertificateBound (properTwoColoring (V := V)) (Fintype.card V) ∧
      HasStrongCertificateBound (isAcyclic (V := V)) (Fintype.card V) ∧
      HasStrongCertificateBound (hasCycle (V := V)) (Fintype.card V) :=
  ⟨hasStrongCertificateBound_connectedComponents, hasStrongCertificateBound_isConnected,
    hasStrongCertificateBound_isSTConnected s t, hasStrongCertificateBound_twoColorings,
    hasStrongCertificateBound_isBipartite, hasStrongCertificateBound_properTwoColoring,
    hasStrongCertificateBound_isAcyclic, hasStrongCertificateBound_hasCycle⟩

/-- **`prop:sparse-certificates` as stated.**
* `L` is an integer with `0 ≤ L < C(v, 2)`, and every graph satisfying `P` has at most `L`
  edges.
* `b_P` is the maximum over graphs of the minimum size of a strong certificate.

Then `b_P ≤ L + 1`.  The hypothesis `L < C(v, 2)` is not needed. -/
example (P : SimpleGraph V → Prop) [DecidablePred P] (L : ℕ)
    (_hL : L < (Fintype.card V).choose 2)
    (hP : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ L) :
    Finset.univ.sup (minStrongCertificateSize fun S : Finset (Edge V) => decide (P (toGraph S)))
      ≤ L + 1 := by
  rw [← strongCertificateSize_eq_sup]
  exact (sparseYes_strongCertificateSize_le P hP).trans (min_le_right _ _)

/-- **`prop:sparse-certificates`, the certificates**, with "strong certificate" unfolded: every
graph has a subgraph of at most `min(C(v, 2), L + 1)` edges on which `P` agrees with the graph
after **every** extension. -/
example (P : SimpleGraph V → Prop) [DecidablePred P] (L : ℕ)
    (hP : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ L) (S : Finset (Edge V)) :
    ∃ C ⊆ S, C.card ≤ min ((Fintype.card V).choose 2) (L + 1) ∧
      ∀ K : Finset (Edge V), P (toGraph (C ∪ K)) ↔ P (toGraph (S ∪ K)) := by
  obtain ⟨C, ⟨hCS, hext⟩, hcard⟩ := hasStrongCertificateBound_of_sparseYes P hP S
  exact ⟨C, hCS, hcard, fun K => by simpa using hext K⟩

/-- `prop:sparse-certificates` for any finite universe: the bound, and certificates within it
and within `L + 1`. -/
example {U : Type*} [Fintype U] [DecidableEq U] (P : Finset U → Bool) (L : ℕ)
    (hP : ∀ S, P S = true → S.card ≤ L) :
    strongCertificateSize P ≤ min (Fintype.card U) (L + 1) ∧
      HasStrongCertificateBound P (min (Fintype.card U) (L + 1)) ∧
      HasStrongCertificateBound P (L + 1) :=
  ⟨Certificates.sparseYes_strongCertificateSize_le hP,
    Certificates.hasStrongCertificateBound_min_of_sparseYes hP,
    Certificates.hasStrongCertificateBound_of_sparseYes hP⟩

end Statements

/-! ## Sanity checks -/

section Sanity

/-- **The empty vertex set**: there are no possible edges, every certificate size is `0`, and
the graph on no vertices is not connected. -/
example : Fintype.card (Edge Empty) = 0 ∧
    strongCertificateSize (connectedComponents (V := Empty)) = 0 ∧
    strongCertificateSize (twoColorings (V := Empty)) = 0 ∧
    isConnected (∅ : Finset (Edge Empty)) = false := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · exact Nat.le_zero.mp ((strongCertificateSize_le_card _).trans (by simp))
  · exact Nat.le_zero.mp ((strongCertificateSize_le_card _).trans (by simp))
  · rw [Bool.eq_false_iff, ne_eq, isConnected_eq_true_iff]
    exact fun h => h.nonempty.some.elim

/-- **A constant property** has certificate size `0`. -/
example {V : Type*} [Fintype V] [DecidableEq V] :
    strongCertificateSize (fun _ : Finset (Edge V) => true) = 0 :=
  strongCertificateSize_eq_zero_iff.mpr fun _ _ => rfl

/-- A vertex with no neighbours is reachable only from itself. -/
private theorem eq_of_reachable_of_isolated {V : Type*} {G : SimpleGraph V} {u w : V}
    (hw : ∀ x, ¬G.Adj w x) (h : G.Reachable u w) : u = w := by
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hw _)

private theorem adj_singleton {V : Type*} {e : Edge V} {u w : V} :
    (toGraph {e}).Adj u w ↔ (e : Sym2 V) = s(u, w) := by
  rw [toGraph_adj]
  simp

/-- The edge `{0, 1}` on three vertices. -/
private def e01 : Edge (Fin 3) := ⟨s(0, 1), by simp⟩

/-- The edge `{1, 2}` on three vertices. -/
private def e12 : Edge (Fin 3) := ⟨s(1, 2), by simp⟩

/-- In the graph with the single edge `{0, 1}` on three vertices, the vertex `2` is isolated. -/
private theorem isolated_two : ∀ x, ¬(toGraph {e01}).Adj 2 x := fun x h => by
  rw [adj_singleton] at h
  simp [e01] at h

private theorem isConnected_e01 : isConnected {e01} = false := by
  rw [Bool.eq_false_iff, ne_eq, isConnected_eq_true_iff]
  exact fun h => absurd (eq_of_reachable_of_isolated isolated_two (h.preconnected 0 2))
    (by decide)

/-- **Isolated vertices and a disconnected graph**: with the single edge `{0, 1}` on three
vertices, `0` and `1` are connected, the vertex `2` is isolated, and the graph is not
connected. -/
example : (0, 1) ∈ connectedComponents {e01} ∧ (0, 2) ∉ connectedComponents {e01} ∧
    isConnected {e01} = false := by
  refine ⟨?_, ?_, isConnected_e01⟩
  · rw [mem_connectedComponents]
    exact (adj_singleton.mpr rfl).reachable
  · rw [mem_connectedComponents]
    exact fun h => absurd (eq_of_reachable_of_isolated isolated_two h) (by decide)

/-- **The triangle**: the complete graph on three vertices has no proper two-colouring, is not
bipartite, and has a cycle.  It has three edges, more than a forest on three vertices. -/
example : twoColorings (Finset.univ : Finset (Edge (Fin 3))) = ∅ ∧
    isBipartite (Finset.univ : Finset (Edge (Fin 3))) = false ∧
    hasCycle (Finset.univ : Finset (Edge (Fin 3))) = true := by
  have hcol : twoColorings (Finset.univ : Finset (Edge (Fin 3))) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
    rw [mem_twoColorings, toGraph_univ] at hc
    have key : ∀ a b d : Fin 2, a ≠ b → b ≠ d → a ≠ d → False := by decide
    exact key (c 0) (c 1) (c 2) (hc 0 1 (by simp)) (hc 1 2 (by simp)) (hc 0 2 (by simp))
  have hac : isAcyclic (Finset.univ : Finset (Edge (Fin 3))) = false := by
    rw [Bool.eq_false_iff, ne_eq, isAcyclic_eq_true_iff]
    intro h
    have h3 := card_le_of_isAcyclic h
    rw [Finset.card_univ, card_edge, Fintype.card_fin] at h3
    exact absurd h3 (by decide)
  refine ⟨hcol, ?_, ?_⟩
  · rw [Bool.eq_false_iff, ne_eq, isBipartite_eq_true_iff, ← twoColorings_nonempty_iff, hcol]
    exact Finset.not_nonempty_empty
  · rw [hasCycle_eq_not_isAcyclic, hac]
    rfl

/-- The edge `{0, 1}` on two vertices. -/
private def f01 : Edge (Fin 2) := ⟨s(0, 1), by simp⟩

/-- **The full set of two-colourings, not a Boolean readout**: on two vertices, the empty graph
and the single edge are both bipartite, but the constant colouring is proper only for the
empty graph. -/
example : isBipartite (∅ : Finset (Edge (Fin 2))) = true ∧ isBipartite {f01} = true ∧
    (fun _ => 0) ∈ twoColorings (∅ : Finset (Edge (Fin 2))) ∧
    (fun _ => 0) ∉ twoColorings {f01} := by
  have hbot : (fun _ => 0) ∈ twoColorings (∅ : Finset (Edge (Fin 2))) := by
    rw [mem_twoColorings, toGraph_empty]
    exact fun _ _ h => h.elim
  have hid : (id : Fin 2 → Fin 2) ∈ twoColorings {f01} :=
    mem_twoColorings.mpr fun _ _ h => h.ne
  refine ⟨?_, ?_, hbot, fun h => mem_twoColorings.mp h 0 1 (adj_singleton.mpr rfl) rfl⟩
  · exact isBipartite_eq_true_iff.mpr (twoColorings_nonempty_iff.mp ⟨_, hbot⟩)
  · exact isBipartite_eq_true_iff.mpr (twoColorings_nonempty_iff.mp ⟨_, hid⟩)

/-- **The extension clause matters**: on three vertices, `∅` and the edge `{0, 1}` are both
disconnected.  But `∅` is not a strong certificate for the connectivity of `{0, 1}`: adding the
edge `{1, 2}` connects `{0, 1}` but not `∅`. -/
example : isConnected (∅ : Finset (Edge (Fin 3))) = isConnected {e01} ∧
    ¬IsStrongCertificate isConnected ∅ {e01} := by
  have h0 : isConnected (∅ : Finset (Edge (Fin 3))) = false := by
    rw [Bool.eq_false_iff, ne_eq, isConnected_eq_true_iff, toGraph_empty]
    intro h
    exact absurd (reachable_bot.mp (h.preconnected 0 1)) (by decide)
  have h12 : isConnected {e12} = false := by
    rw [Bool.eq_false_iff, ne_eq, isConnected_eq_true_iff]
    intro h
    have hiso : ∀ x, ¬(toGraph {e12}).Adj 0 x := fun x hx => by
      rw [adj_singleton] at hx
      simp [e12] at hx
    exact absurd (eq_of_reachable_of_isolated hiso (h.preconnected 1 0)) (by decide)
  have hboth : isConnected ({e01} ∪ {e12}) = true := by
    rw [isConnected_eq_true_iff, connected_iff_exists_forall_reachable]
    have a10 : (toGraph ({e01} ∪ {e12})).Adj 1 0 :=
      toGraph_adj.mpr ⟨e01, by simp, Sym2.eq_swap⟩
    have a12 : (toGraph ({e01} ∪ {e12})).Adj 1 2 := toGraph_adj.mpr ⟨e12, by simp, rfl⟩
    refine ⟨1, fun w => ?_⟩
    fin_cases w
    · exact a10.reachable
    · exact Reachable.rfl
    · exact a12.reachable
  refine ⟨h0.trans isConnected_e01.symm, fun hcert => ?_⟩
  have h := hcert.2 {e12}
  rw [Finset.empty_union, h12, hboth] at h
  exact Bool.false_ne_true h

/-- **`prop:sparse-certificates` on a small case**: the yes-instances of "has no edges" have
`0` edges, so its certificate size is at most `1`. -/
example {V : Type*} [Fintype V] [DecidableEq V] [DecidablePred fun G : SimpleGraph V => G = ⊥] :
    strongCertificateSize (fun S : Finset (Edge V) => decide (toGraph S = ⊥)) ≤ 1 :=
  (sparseYes_strongCertificateSize_le (fun G : SimpleGraph V => G = ⊥) (L := 0)
    fun G hG => by simp [hG]).trans (min_le_right _ _)

end Sanity

end MonoidProduct.Graph
