import MonoidProduct.Graph.FailureLower
set_option linter.style.header false

/-!
# Acceptance statements for the failure-profile lower bounds

The paper-facing statements of `monoid.tex`, section `sec:failure-profiles`:
`eq:vertex-failure-profile` (the definition), `eq:profile-enumeration-lower`, and the lower
bounds of `prop:failure-profile-complexity`, with both halves for edge failures.  They are
restated with the definitions unfolded where that makes their meaning visible, followed by
small sanity checks.  Lean checks every `example` here against the library's statement.

* The vertex profile: one coordinate for every set of fewer than `k` vertices, holding the
  partition of the surviving vertices in the induced graph; deleted vertices appear in no pair.
* The enumeration problem: membership bits in, the whole tuple out, at error `1/3`.
* `prop:failure-profile-complexity` over its whole range (here every `k` and every `v ≥ 2`).
* The constructions: each profile determines every unknown neighbourhood.

The sanity checks cover:
* deleting the middle vertex of the path `0 - 1 - 2`: the ends are separated and the deleted
  vertex is in no pair, not even with itself;
* the smallest enumeration instance, two inputs, which already costs a query;
* the paper's range `1 ≤ k ≤ v` as a special case.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph FailureLower

/-! ## The vertex profile -/

section Vertex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`Σ^V_k`** (`eq:vertex-failure-profile`): one coordinate for every set `X` of fewer than
`k` vertices.  Two vertices are related exactly when both survive and they are connected in the
graph induced on `V \ X`, Mathlib's `G.induce`. -/
example (k : ℕ) (S : Finset (Edge V)) (X : Finset V) (hX : X.card < k) (u w : V) :
    ((u, w) ∈ vertexFailureProfile k S ⟨X, hX⟩ ↔ ∃ (hu : u ∉ X) (hw : w ∉ X),
      ((toGraph S).induce {z | z ∉ X}).Reachable ⟨u, hu⟩ ⟨w, hw⟩) ∧
    ((u, w) ∈ vertexFailureProfile k S ⟨X, hX⟩ → u ∉ X ∧ w ∉ X) :=
  ⟨mem_vertexFailureProfile, fst_notMem_of_mem_vertexFailureProfile⟩

/-- Truncation, deleting no vertex, and the cases `k = 0, 1`. -/
example (k k' : ℕ) (h : k' ≤ k) (hk : 0 < k) (S T : Finset (Edge V))
    (X : VertexFailureSet V k') (u w : V) :
    vertexFailureProfile k' S X = vertexFailureProfile k S ⟨X.1, X.2.trans_le h⟩ ∧
      ((u, w) ∈ vertexFailureProfile k S ⟨∅, by simpa using hk⟩ ↔ (toGraph S).Reachable u w) ∧
      vertexFailureProfile 0 S = vertexFailureProfile 0 T ∧
      (vertexFailureProfile 1 S = vertexFailureProfile 1 T ↔
        connectedComponents S = connectedComponents T) :=
  ⟨vertexFailureProfile_of_le h S X, mem_vertexFailureProfile_empty hk,
    vertexFailureProfile_zero S T, vertexFailureProfile_one_eq_iff⟩

end Vertex

/-! ## The enumeration adversary -/

section Enumeration

variable {r q d : ℕ}

/-- **The enumeration problem**: a query at `(u, b)` returns whether `b ∈ x u`, and the output is
the whole tuple.  Two inputs are joined by the adversary matrix when one row changes by
exchanging one present and one absent element. -/
example (x y : JTuple r q d) (p : Fin r × Fin q) :
    enumRead x p = decide (p.2 ∈ (x p.1).1) ∧
      (Exch x y ↔ ∃ u, (∀ u', u' ≠ u → y u' = x u') ∧
        ∃ a ∈ (x u).1, ∃ c ∉ (x u).1, (y u).1 = insert c ((x u).1.erase a)) ∧
      (Exch x y → Exch y x ∧ x ≠ y) ∧
      r * (d * (q - d)) ≤ (Finset.univ.filter fun y => Exch x y).card :=
  ⟨rfl, Iff.rfl, fun h => ⟨h.symm, h.ne⟩, card_exch_ge x⟩

/-- **`eq:profile-enumeration-lower`**: for `1 ≤ d < q`, `ADV ≥ r·√(d(q − d))` for every read map
whose positions are constant or reveal one membership bit, and `Q_{1/3} ≥ (7/1376)·r·√(d(q − d))`
for the enumeration problem itself; the output is the whole tuple, not a bit. -/
example (hd : 0 < d) (hdq : d < q) :
    (r : ℝ) * Real.sqrt (d * (q - d : ℕ)) ≤ advPMOn (enumRead (r := r) (q := q) (d := d)) id ∧
      (7 / 1376 : ℝ) * (r * Real.sqrt (d * (q - d : ℕ))) ≤
        qQueryOn (enumRead (r := r) (q := q) (d := d)) id (1 / 3) := by
  refine ⟨enumeration_advPMOn_ge hd hdq enumRead id (fun x y h => ?_) (fun x y h => h.ne)
    (fun p => Or.inr ⟨p.1, p.2, fun x y h => ?_⟩), enumeration_qQuery_ge hd hdq⟩
  · funext u
    refine Subtype.ext (Finset.ext fun b => ?_)
    have := congrFun h (u, b)
    simp only [enumRead, decide_eq_decide] at this
    exact this
  · simp only [enumRead, ne_eq, decide_eq_decide] at h
    tauto

/-- **The smallest instance**: one row, `q = 2`, `d = 1`, two inputs; it already costs
`7/1376` queries. -/
example : (7 / 1376 : ℝ) ≤ qQueryOn (enumRead (r := 1) (q := 2) (d := 1)) id (1 / 3) := by
  have h := enumeration_qQuery_ge (r := 1) (q := 2) (d := 1) one_pos one_lt_two
  norm_num at h ⊢
  exact h

end Enumeration

/-! ## `prop:failure-profile-complexity` -/

section Profiles

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **`prop:failure-profile-complexity`**: for every `v ≥ 2` and every `k`, both profiles cost
`Q_matrix ≥ (1/10000)·min{v², v·√(v·k)}`, and the edge profile also
`Q_matrix ≤ 2^18·min{v², v·√(v·k)}`: `Θ(min{v², v^{3/2}·√k})` for edge failures. -/
example (hv : 2 ≤ Fintype.card V) (k : ℕ) :
    (1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (edgeFailureProfile (V := V) k) ∧
    (1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (vertexFailureProfile (V := V) k) ∧
    (qMatrix (edgeFailureProfile (V := V) k) : ℝ) ≤
      2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2) (Fintype.card V * Real.sqrt (Fintype.card V * k)) :=
  ⟨edgeFailureProfile_qMatrix_ge hv k, vertexFailureProfile_qMatrix_ge hv k,
    (edgeFailureProfile_qMatrix_theta hv k).2⟩

/-- **The paper's range** `1 ≤ k ≤ v` is a special case. -/
example (hv : 2 ≤ Fintype.card V) (k : ℕ) (_hk1 : 1 ≤ k) (_hkv : k ≤ Fintype.card V) :
    (1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (vertexFailureProfile (V := V) k) :=
  vertexFailureProfile_qMatrix_ge hv k

/-- **The constructions**: with `B` a clique and `A` independent, each profile for `k > d`
determines every unknown `d`-element neighbourhood `x u`; with both sides independent and one
neighbour each, the component partition determines every neighbour. -/
example {q r d k : ℕ} (lab : Fin q ⊕ Fin r ↪ V) (hdk : d < k) (x y : JTuple r q d)
    (x' y' : JTuple r q 1) :
    (edgeFailureProfile k (bClique lab ∪ crossEdges lab x) =
      edgeFailureProfile k (bClique lab ∪ crossEdges lab y) → x = y) ∧
    (vertexFailureProfile k (bClique lab ∪ crossEdges lab x) =
      vertexFailureProfile k (bClique lab ∪ crossEdges lab y) → x = y) ∧
    (connectedComponents (∅ ∪ crossEdges lab x') =
      connectedComponents (∅ ∪ crossEdges lab y') → x' = y') :=
  ⟨edgeFailureProfile_baseGraph_injective lab hdk fun _ he u =>
      aVert_notMem_of_mem_bClique lab he u,
    vertexFailureProfile_baseGraph_injective lab hdk fun _ he u =>
      aVert_notMem_of_mem_bClique lab he u,
    connectedComponents_starGraph_injective lab⟩

end Profiles

/-! ## Sanity checks -/

section Sanity

/-- The edges `{0, 1}` and `{1, 2}` on three vertices. -/
private def e01 : Edge (Fin 3) := ⟨s(0, 1), by decide⟩
private def e12 : Edge (Fin 3) := ⟨s(1, 2), by decide⟩

/-- **Deleting the middle vertex of the path `0 - 1 - 2`**: in `Σ^V_2`, at `X = {1}`, the ends
are not connected, and the deleted vertex appears in no pair, not even with itself. -/
example : (0, 2) ∉ vertexFailureProfile 2 ({e01, e12} : Finset (Edge (Fin 3))) ⟨{1}, by decide⟩ ∧
    (1, 1) ∉ vertexFailureProfile 2 ({e01, e12} : Finset (Edge (Fin 3))) ⟨{1}, by decide⟩ := by
  refine ⟨fun h => ?_, fun h => (fst_notMem_of_mem_vertexFailureProfile h).1
    (Finset.mem_singleton_self 1)⟩
  obtain ⟨h0, h2, hr⟩ := mem_vertexFailureProfile.mp h
  have hiso : ∀ z, ¬((toGraph ({e01, e12} : Finset (Edge (Fin 3)))).induce
      {z : Fin 3 | z ∉ ({1} : Finset (Fin 3))}).Adj ⟨0, h0⟩ z := by
    intro z hz
    have hadj : (toGraph ({e01, e12} : Finset (Edge (Fin 3)))).Adj 0 z.1 := hz
    obtain ⟨e, he, hez⟩ := toGraph_adj.mp hadj
    have hz1 : z.1 ≠ 1 := fun h => z.2 (by rw [h]; exact Finset.mem_singleton_self 1)
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Sym2.eq_iff.mp hez with ⟨-, h⟩ | ⟨-, h⟩
      · exact hz1 h.symm
      · exact absurd (h : (1 : Fin 3) = 0) (by decide)
    · rw [Finset.mem_singleton.mp he] at hez
      rcases Sym2.eq_iff.mp hez with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd (h : (1 : Fin 3) = 0) (by decide)
      · exact absurd (h : (2 : Fin 3) = 0) (by decide)
  have := eq_of_reachable_of_forall_not_adj hiso hr
  have h20 : (2 : Fin 3) = 0 := congrArg Subtype.val this
  exact absurd h20 (by decide)

end Sanity

end MonoidProduct.Graph
