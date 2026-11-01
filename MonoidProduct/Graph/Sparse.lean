import MonoidProduct.Certificates.Sparse
import MonoidProduct.Graph.Components
set_option linter.style.header false

/-!
# Sparse yes-instances and cycle detection

`monoid.tex`, section `sec:graph-certificates`: `prop:sparse-certificates` for graphs, and the
paragraph "Cycle detection".  Write `v = #V` and `N = C(v, 2)`.

* `sparseYes_strongCertificateSize_le` (`prop:sparse-certificates`): let `P` be a Boolean
  property of simple graphs on `V` whose yes-instances have at most `L` edges.  Then its
  strong-certificate size is at most `min(N, L + 1)`, with no closure or monotonicity
  assumption on `P`.  The paper assumes `0 ≤ L < N` and concludes `b_P ≤ L + 1`.  The
  hypothesis is not needed, and `min(N, L + 1) ≤ L + 1`.  The certificates themselves:
  `hasStrongCertificateBound_of_sparseYes`.
* `cycle_strongCertificateSize_le` (certificates: `hasStrongCertificateBound_hasCycle`):
  cycle detection has strong certificates of at most `v` edges.  Acyclic graphs are forests,
  with at most `v - 1` edges (`card_le_of_isAcyclic`), so the sparse bound applies to
  acyclicity with `L = v - 1`.  Cycle detection is its negation.
  * A graph with at most `v - 1` edges certifies itself.
  * Any `v` edges of a larger graph certify it: every extension of them still has a cycle.
  * The paper instead retains a simple cycle; both certificates have at most `v` edges.
-/

namespace MonoidProduct.Graph

open SimpleGraph Certificates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`prop:sparse-certificates`**: if every graph on `V` satisfying `P` has at most `L` edges,
then deciding `P` has strong-certificate size at most `min(C(v, 2), L + 1)`.  No closure or
monotonicity assumption on `P` is needed. -/
theorem sparseYes_strongCertificateSize_le (P : SimpleGraph V → Prop) [DecidablePred P] {L : ℕ}
    (hP : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ L) :
    strongCertificateSize (fun S : Finset (Edge V) => decide (P (toGraph S))) ≤
      min ((Fintype.card V).choose 2) (L + 1) := by
  have h := Certificates.sparseYes_strongCertificateSize_le
    (P := fun S : Finset (Edge V) => decide (P (toGraph S))) (L := L) fun S hS => by
      rw [← ncard_edgeSet_toGraph]
      exact hP _ (of_decide_eq_true hS)
  rwa [card_edge] at h

/-- **Certificates for `prop:sparse-certificates`**: if every graph on `V` satisfying `P` has
at most `L` edges, every graph has a strong certificate for `P` of at most `min(C(v, 2), L + 1)`
edges. -/
theorem hasStrongCertificateBound_of_sparseYes (P : SimpleGraph V → Prop) [DecidablePred P]
    {L : ℕ} (hP : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ L) :
    HasStrongCertificateBound (fun S : Finset (Edge V) => decide (P (toGraph S)))
      (min ((Fintype.card V).choose 2) (L + 1)) :=
  hasStrongCertificateBound_iff_size_le.mpr (sparseYes_strongCertificateSize_le P hP)

omit [Fintype V] [DecidableEq V] in
/-- **Acyclicity**: whether `toGraph S` is a forest. -/
noncomputable def isAcyclic (S : Finset (Edge V)) : Bool := by
  classical exact decide (toGraph S).IsAcyclic

omit [Fintype V] [DecidableEq V] in
/-- **Cycle detection**: whether `toGraph S` contains a cycle, that is, is not acyclic. -/
noncomputable def hasCycle (S : Finset (Edge V)) : Bool := by
  classical exact decide ¬(toGraph S).IsAcyclic

omit [Fintype V] [DecidableEq V] in
theorem isAcyclic_eq_true_iff {S : Finset (Edge V)} :
    isAcyclic S = true ↔ (toGraph S).IsAcyclic := by
  simp [isAcyclic]

omit [Fintype V] [DecidableEq V] in
/-- `hasCycle S` holds exactly when `toGraph S` contains a cycle. -/
theorem hasCycle_eq_true_iff {S : Finset (Edge V)} :
    hasCycle S = true ↔ ∃ (u : V) (c : (toGraph S).Walk u u), c.IsCycle := by
  have h : hasCycle S = true ↔ ¬(toGraph S).IsAcyclic := by simp [hasCycle]
  rw [h, IsAcyclic]
  simp only [not_forall, not_not]

omit [Fintype V] [DecidableEq V] in
theorem hasCycle_eq_not_isAcyclic (S : Finset (Edge V)) : hasCycle S = !isAcyclic S := by
  classical
  simp [hasCycle, isAcyclic]

/-- **Acyclicity** has strong-certificate size at most `v`, by `prop:sparse-certificates`
with the forest bound `L = v - 1`. -/
theorem isAcyclic_strongCertificateSize_le :
    strongCertificateSize (isAcyclic (V := V)) ≤ Fintype.card V := by
  have h := Certificates.sparseYes_strongCertificateSize_le (P := isAcyclic (V := V))
    (L := Fintype.card V - 1) fun S hS => card_le_of_isAcyclic (isAcyclic_eq_true_iff.mp hS)
  rw [card_edge] at h
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hv | hv
  · rw [hv] at h ⊢
    simpa using h
  · exact h.trans (min_le_right _ _) |>.trans (by omega)

/-- **Cycle detection** (`sec:graph-certificates`): its strong-certificate size is at most
`v`. -/
theorem cycle_strongCertificateSize_le :
    strongCertificateSize (hasCycle (V := V)) ≤ Fintype.card V := by
  rw [show hasCycle (V := V) = fun S => !isAcyclic S from funext hasCycle_eq_not_isAcyclic]
  exact (strongCertificateSize_postcomp_le isAcyclic (fun b : Bool => !b)).trans
    isAcyclic_strongCertificateSize_le

/-- **Certificates for acyclicity**: every graph has a strong certificate of at most `v`
edges. -/
theorem hasStrongCertificateBound_isAcyclic :
    HasStrongCertificateBound (isAcyclic (V := V)) (Fintype.card V) :=
  hasStrongCertificateBound_iff_size_le.mpr isAcyclic_strongCertificateSize_le

/-- **Certificates for cycle detection**: every graph has a strong certificate of at most `v`
edges. -/
theorem hasStrongCertificateBound_hasCycle :
    HasStrongCertificateBound (hasCycle (V := V)) (Fintype.card V) :=
  hasStrongCertificateBound_iff_size_le.mpr cycle_strongCertificateSize_le

end MonoidProduct.Graph
