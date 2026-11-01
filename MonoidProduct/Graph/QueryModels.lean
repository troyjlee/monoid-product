import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import MonoidProduct.Graph.Basic
import MonoidProduct.Certificates.Quantum
import MonoidProduct.Quantum.PositionAlphabet
import MonoidProduct.Quantum.Reindex
set_option linter.style.header false

/-!
# Query models for graphs

`monoid.tex`, section `sec:graph-certificates`, paragraphs "Query models" and "Comparison of the
models".  A function `f : Finset (Edge V) → O` of graphs on a fixed finite vertex set `V` is to
be computed with error at most `1/3`; `V` and `f` are known.  Write `v = #V` and
`N = C(v, 2)`.

* **Edge lists**, `qList f n` (`Q_list(f; n)`).  The input is `x : Fin n → Option (Edge V)`, in
  any order, with null entries `none` (the paper's `⊥`) and repeated edges.  It represents the
  graph `{x_i : x_i ≠ ⊥}` (`recordSet x`), and a query to `i` returns `x_i`.
* **Adjacency matrices**, `qMatrix f` (`Q_matrix(f)`).  The input is `a : Edge V → Bool`, one
  bit for each pair of distinct vertices, and a query to a pair returns its bit.  It represents
  `matrixGraph a`, the pairs whose bit is set.
* **Adjacency lists**, `qAdj f deg`.  The degree vector `deg : V → ℕ` is public, and a query to
  `(u, j)`, `j < deg u`, returns the `j`th neighbour of `u`.  The input is a valid adjacency
  array (`IsAdjArray`): no loops, no repeated neighbour in a row, and `w` occurs in row `u`
  exactly when `u` occurs in row `w`.  The rows may list the neighbours in any order.  It
  represents `adjGraph deg nbr`, whose neighbours of `u` are row `u` (`adjGraph_adj`), and
  `∑ u, deg u = 2m` for its `m` edges (`sum_deg_eq_two_mul_card_adjGraph`).
  `qAdjEdges f m` (`Q_adj(f; m)`, graphs with `m` edges) is the worst case over the degree
  vectors with `∑ u, deg u = 2m`.

Every graph has exactly one adjacency matrix (`matrixGraph_indicator`, `matrixGraph_injective`)
and some adjacency array (`exists_adjArray`), so neither model restricts the graphs.

**Comparison of the models** (`eq:graph-model-comparison`).  A matrix is a virtual edge list
with one position per pair `e`, holding `e` when its bit is set and `⊥` otherwise
(`matrixEntry`).  An adjacency array is a virtual edge list with one position per `(u, j)`,
holding the edge `{u, nbr(u, j)}` (`adjEdge`).  Either way the virtual entry is a public
function of the position and of the one oracle answer there.  So a list query costs two queries
to the original oracle, including the uncomputation (`qQueryOn_positionAlphabetMap_le`), and
renaming the positions to `Fin N` or `Fin (∑ u, deg u)` is free (`qQueryOn_reindex`):

  `qMatrix f ≤ 2·qList f N`,  `qAdj f deg ≤ 2·qList f (∑ u, deg u)`,
  `qAdjEdges f m ≤ 2·qList f (2m)`.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

/-! ## Edge lists -/

section Records

variable {ι ι' U : Type} [Fintype ι] [Fintype ι'] [DecidableEq U]

/-- The set of nonnull records does not depend on the names of the positions. -/
theorem recordSet_comp_equiv (e : ι ≃ ι') (y : ι → Option U) :
    recordSet (fun i' => y (e.symm i')) = recordSet y := by
  ext u
  simp only [mem_recordSet]
  exact ⟨fun ⟨_, h⟩ => ⟨_, h⟩, fun ⟨i, h⟩ => ⟨e i, by simpa using h⟩⟩

end Records

variable {V O : Type} [Fintype V] [DecidableEq V] [DecidableEq O]

/-- **`Q_list(f; n)`**: the quantum query complexity, at error `1/3`, of computing `f` of the
graph `{x_i : x_i ≠ ⊥}` from an edge list `x : Fin n → Option (Edge V)`.  The list may have any
order, null entries `none` and repeated edges, and a query to `i` returns `x_i`. -/
noncomputable def qList (f : Finset (Edge V) → O) (n : ℕ) : ℕ :=
  qQuery (fun x : Fin n → Option (Edge V) => f (recordSet x)) (1 / 3)

/-- **Edge lists on any finite set of positions**: the complexity depends only on the number of
positions. -/
theorem qQuery_recordSet_eq_qList {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : Finset (Edge V) → O) :
    qQuery (fun y : ι → Option (Edge V) => f (recordSet y)) (1 / 3)
      = qList f (Fintype.card ι) := by
  rw [qList, ← qQuery_comp_reindex (Fintype.equivFin ι)
    (fun x : Fin (Fintype.card ι) → Option (Edge V) => f (recordSet x))]
  simp only [recordSet_comp_equiv]

/-- Reading the whole list suffices: `qList f n ≤ n`. -/
theorem qList_le (f : Finset (Edge V) → O) (n : ℕ) : qList f n ≤ n := by
  have : Nonempty O := ⟨f ∅⟩
  have h := qQueryOn_le_card (read := (id : (Fin n → Option (Edge V)) → _))
    (f := fun x => f (recordSet x)) (fun x y h => by rw [show x = y from h])
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-! ## Adjacency matrices -/

/-- The entry of the virtual edge list of a matrix at the pair `e`: `e` when its bit is set,
`⊥` otherwise. -/
def matrixEntry (e : Edge V) (b : Bool) : Option (Edge V) :=
  if b then some e else none

/-- **The graph of an adjacency matrix** `a : Edge V → Bool`: the pairs whose bit is set. -/
def matrixGraph (a : Edge V → Bool) : Finset (Edge V) :=
  Finset.univ.filter fun e => a e = true

/-- `e` is an edge of the graph of `a` exactly when its bit is set. -/
theorem mem_matrixGraph {a : Edge V → Bool} {e : Edge V} : e ∈ matrixGraph a ↔ a e = true := by
  simp [matrixGraph]

/-- **Every graph has an adjacency matrix**: its indicator. -/
theorem matrixGraph_indicator (S : Finset (Edge V)) :
    matrixGraph (fun e => decide (e ∈ S)) = S := by
  ext e
  simp [mem_matrixGraph]

/-- **A matrix is determined by its graph**, so each graph has exactly one adjacency matrix. -/
theorem matrixGraph_injective : Function.Injective (matrixGraph (V := V)) := by
  intro a b h
  funext e
  have h' : e ∈ matrixGraph a ↔ e ∈ matrixGraph b := by rw [h]
  rw [mem_matrixGraph, mem_matrixGraph] at h'
  exact Bool.eq_iff_iff.mpr h'

/-- The graph of a matrix is the graph of its virtual edge list. -/
theorem matrixGraph_eq_recordSet (a : Edge V → Bool) :
    matrixGraph a = recordSet fun e => matrixEntry e (a e) := by
  ext e
  rw [mem_matrixGraph, mem_recordSet]
  constructor
  · intro h
    exact ⟨e, by simp [matrixEntry, h]⟩
  · rintro ⟨e', h⟩
    unfold matrixEntry at h
    split_ifs at h with h'
    exact Option.some_injective _ h ▸ h'

/-- **`Q_matrix(f)`**: the quantum query complexity, at error `1/3`, of computing `f` of the
graph of an adjacency matrix `a : Edge V → Bool`.  A query to a pair of distinct vertices
returns the bit saying whether they are adjacent. -/
noncomputable def qMatrix (f : Finset (Edge V) → O) : ℕ :=
  qQuery (fun a : Edge V → Bool => f (matrixGraph a)) (1 / 3)

/-- Reading the whole matrix suffices: `qMatrix f ≤ C(v, 2)`. -/
theorem qMatrix_le (f : Finset (Edge V) → O) : qMatrix f ≤ (Fintype.card V).choose 2 := by
  have : Nonempty O := ⟨f ∅⟩
  have h := qQueryOn_le_card (read := (id : (Edge V → Bool) → _))
    (f := fun a => f (matrixGraph a)) (fun x y h => by rw [show x = y from h])
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [card_edge] at h

/-! ## Adjacency arrays -/

/-- The positions of an adjacency array with degree vector `deg`: the pairs `(u, j)` with
`j < deg u`. -/
abbrev AdjPos (deg : V → ℕ) : Type := (u : V) × Fin (deg u)

omit [DecidableEq V] in
/-- An adjacency array has `∑ u, deg u` positions. -/
theorem card_adjPos (deg : V → ℕ) : Fintype.card (AdjPos deg) = ∑ u, deg u := by
  simp [AdjPos, Fintype.card_sigma]

/-- **A valid adjacency array** with degree vector `deg`: row `u` lists `deg u` neighbours of
`u`, in any order. -/
structure IsAdjArray (deg : V → ℕ) (nbr : AdjPos deg → V) : Prop where
  /-- No loops: `u` is not its own neighbour. -/
  ne_self : ∀ u (j : Fin (deg u)), nbr ⟨u, j⟩ ≠ u
  /-- No neighbour is repeated in a row. -/
  row_injective : ∀ u, Function.Injective fun j : Fin (deg u) => nbr ⟨u, j⟩
  /-- Symmetric adjacency: if `w` occurs in row `u`, then `u` occurs in row `w`. -/
  symm : ∀ u w, (∃ j, nbr ⟨u, j⟩ = w) → ∃ j, nbr ⟨w, j⟩ = u

/-- The edge recorded by an entry `w` of row `u`: the pair `{u, w}`, or `⊥` if `w = u`, which a
valid array excludes. -/
def adjEdge (u w : V) : Option (Edge V) :=
  if h : u = w then none else some ⟨s(u, w), by simpa using h⟩

omit [Fintype V] in
theorem adjEdge_eq_some_iff {u w : V} {e : Edge V} :
    adjEdge u w = some e ↔ u ≠ w ∧ (e : Sym2 V) = s(u, w) := by
  unfold adjEdge
  split_ifs with h
  · simp [h]
  · simp only [Option.some.injEq, ne_eq, h, not_false_eq_true, true_and]
    constructor
    · rintro rfl
      rfl
    · intro he
      exact Subtype.ext he.symm

/-- **The graph of an adjacency array**: the pairs `{u, nbr(u, j)}`. -/
def adjGraph (deg : V → ℕ) (nbr : AdjPos deg → V) : Finset (Edge V) :=
  recordSet fun p => adjEdge p.1 (nbr p)

theorem mem_adjGraph {deg : V → ℕ} {nbr : AdjPos deg → V} {e : Edge V} :
    e ∈ adjGraph deg nbr ↔ ∃ p, adjEdge p.1 (nbr p) = some e :=
  mem_recordSet

/-- **The represented graph has the rows as neighbourhoods**: for a valid array, `u` and `w` are
adjacent exactly when `w` occurs in row `u`. -/
theorem adjGraph_adj {deg : V → ℕ} {nbr : AdjPos deg → V} (h : IsAdjArray deg nbr) {u w : V} :
    (toGraph (adjGraph deg nbr)).Adj u w ↔ ∃ j, nbr ⟨u, j⟩ = w := by
  rw [toGraph_adj]
  constructor
  · rintro ⟨e, he, hew⟩
    obtain ⟨⟨u', j⟩, hp⟩ := mem_adjGraph.mp he
    obtain ⟨-, he'⟩ := adjEdge_eq_some_iff.mp hp
    rcases Sym2.eq_iff.mp (he'.symm.trans hew) with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
    · exact ⟨j, h2⟩
    · exact h.symm _ _ ⟨j, h2⟩
  · rintro ⟨j, rfl⟩
    have hne : u ≠ nbr ⟨u, j⟩ := (h.ne_self u j).symm
    exact ⟨⟨s(u, nbr ⟨u, j⟩), by simpa using hne⟩,
      mem_adjGraph.mpr ⟨⟨u, j⟩, adjEdge_eq_some_iff.mpr ⟨hne, rfl⟩⟩, rfl⟩

/-- For a valid array, the degree of `u` in the represented graph is `deg u`. -/
theorem degree_toGraph_adjGraph {deg : V → ℕ} {nbr : AdjPos deg → V} (h : IsAdjArray deg nbr)
    (u : V) [Fintype ((toGraph (adjGraph deg nbr)).neighborSet u)] :
    (toGraph (adjGraph deg nbr)).degree u = deg u := by
  classical
  have hN : (toGraph (adjGraph deg nbr)).neighborFinset u
      = Finset.univ.image fun j : Fin (deg u) => nbr ⟨u, j⟩ := by
    ext w
    simp [mem_neighborFinset, adjGraph_adj h]
  rw [← card_neighborFinset_eq_degree, hN,
    Finset.card_image_of_injective _ (h.row_injective u), Finset.card_univ, Fintype.card_fin]

/-- **Handshake**: for a valid array, `∑ u, deg u = 2m`, where `m` is the number of edges of the
represented graph. -/
theorem sum_deg_eq_two_mul_card_adjGraph {deg : V → ℕ} {nbr : AdjPos deg → V}
    (h : IsAdjArray deg nbr) : ∑ u, deg u = 2 * (adjGraph deg nbr).card := by
  classical
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (toGraph (adjGraph deg nbr))
  rw [Finset.sum_congr rfl fun u _ => degree_toGraph_adjGraph h u] at hsum
  rw [hsum, edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    ncard_edgeSet_toGraph]

/-- **Every graph has an adjacency array**: list the neighbours of each vertex in any order. -/
theorem exists_adjArray (S : Finset (Edge V)) :
    ∃ (deg : V → ℕ) (nbr : AdjPos deg → V), IsAdjArray deg nbr ∧ adjGraph deg nbr = S := by
  classical
  let G := toGraph S
  let deg : V → ℕ := fun u => (G.neighborFinset u).card
  let nbr : AdjPos deg → V := fun p => ((G.neighborFinset p.1).equivFin.symm p.2).1
  have hmem : ∀ u (j : Fin (deg u)), G.Adj u (nbr ⟨u, j⟩) := fun u j =>
    (mem_neighborFinset G u _).mp ((G.neighborFinset u).equivFin.symm j).2
  have hrow : ∀ u w, (∃ j, nbr ⟨u, j⟩ = w) ↔ G.Adj u w := by
    intro u w
    refine ⟨fun ⟨j, hj⟩ => hj ▸ hmem u j, fun hw => ?_⟩
    refine ⟨(G.neighborFinset u).equivFin ⟨w, (mem_neighborFinset G u w).mpr hw⟩, ?_⟩
    change ((G.neighborFinset u).equivFin.symm ((G.neighborFinset u).equivFin ⟨w, _⟩)).1 = w
    rw [Equiv.symm_apply_apply]
  have hvalid : IsAdjArray deg nbr :=
    { ne_self := fun u j => (G.ne_of_adj (hmem u j)).symm
      row_injective := fun u j j' hj =>
        (G.neighborFinset u).equivFin.symm.injective (Subtype.ext hj)
      symm := fun u w huw => (hrow w u).mpr ((hrow u w).mp huw).symm }
  refine ⟨deg, nbr, hvalid, toGraph_injective ?_⟩
  ext u w
  rw [adjGraph_adj hvalid, hrow]

/-- The valid adjacency arrays with degree vector `deg`: the promise of the adjacency-list
model. -/
abbrev AdjArray (deg : V → ℕ) : Type := {nbr : AdjPos deg → V // IsAdjArray deg nbr}

/-- **`Q_adj` for the degree vector `deg`**: the quantum query complexity, at error `1/3`, of
computing `f` of the graph of a valid adjacency array.  The degrees are public, and a query to
`(u, j)` returns the `j`th neighbour of `u`. -/
noncomputable def qAdj (f : Finset (Edge V) → O) (deg : V → ℕ) : ℕ :=
  qQueryOn (fun a : AdjArray deg => a.1) (fun a => f (adjGraph deg a.1)) (1 / 3)

/-- Reading the whole array suffices: `qAdj f deg ≤ ∑ u, deg u`. -/
theorem qAdj_le (f : Finset (Edge V) → O) (deg : V → ℕ) : qAdj f deg ≤ ∑ u, deg u := by
  have : Nonempty O := ⟨f ∅⟩
  have := Fintype.ofFinite (AdjArray deg)
  have h := qQueryOn_le_card (read := fun a : AdjArray deg => a.1)
    (f := fun a => f (adjGraph deg a.1)) (fun x y h => by rw [h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [card_adjPos] at h

/-- **`Q_adj(f; m)`**: the worst case of `qAdj f deg` over the degree vectors of graphs with `m`
edges, those with `∑ u, deg u = 2m`. -/
noncomputable def qAdjEdges (f : Finset (Edge V) → O) (m : ℕ) : ℕ :=
  ⨆ deg : {deg : V → ℕ // ∑ u, deg u = 2 * m}, qAdj f deg.1

/-- `qAdjEdges f m` bounds every `qAdj f deg` with `∑ u, deg u = 2m`. -/
theorem qAdj_le_qAdjEdges (f : Finset (Edge V) → O) {deg : V → ℕ} {m : ℕ}
    (h : ∑ u, deg u = 2 * m) : qAdj f deg ≤ qAdjEdges f m := by
  unfold qAdjEdges
  refine le_ciSup (f := fun d : {deg : V → ℕ // ∑ u, deg u = 2 * m} => qAdj f d.1) ?_ ⟨deg, h⟩
  refine ⟨2 * m, ?_⟩
  rintro _ ⟨d, rfl⟩
  exact (qAdj_le f d.1).trans d.2.le

/-- A real bound on every `qAdj f deg` with `∑ u, deg u = 2m` bounds `qAdjEdges f m`. -/
theorem qAdjEdges_le_of_forall {f : Finset (Edge V) → O} {m : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ deg : V → ℕ, ∑ u, deg u = 2 * m → (qAdj f deg : ℝ) ≤ B) :
    (qAdjEdges f m : ℝ) ≤ B := by
  have hle : qAdjEdges f m ≤ ⌊B⌋₊ := by
    unfold qAdjEdges
    exact ciSup_le' fun d => Nat.le_floor (h d.1 d.2)
  exact (Nat.cast_le.mpr hle).trans (Nat.floor_le hB)

/-! ## Comparison of the models -/

/-- **`eq:graph-model-comparison`, adjacency matrices**: `Q_matrix(f) ≤ 2·Q_list(f; C(v, 2))`.
Position `e` of the virtual list holds `e` or `⊥` according to the bit of `e`; a list query is
simulated by two matrix queries, and the `C(v, 2)` positions are renamed `Fin C(v, 2)`. -/
theorem qMatrix_le_two_mul_qList (f : Finset (Edge V) → O) :
    qMatrix f ≤ 2 * qList f ((Fintype.card V).choose 2) := by
  have : Nonempty O := ⟨f ∅⟩
  have hne : (QueryCounts (fun (a : Edge V → Bool) e => matrixEntry e (a e))
      (fun a => f (matrixGraph a)) (1 / 3)).Nonempty :=
    queryCounts_nonempty (fun a b h => by
      simp only [matrixGraph_eq_recordSet]
      exact congrArg (fun y => f (recordSet y)) h) (by norm_num)
  have h1 := qQueryOn_positionAlphabetMap_le matrixEntry (id : (Edge V → Bool) → Edge V → Bool)
    (fun a => f (matrixGraph a)) hne
  have h2 : qQueryOn (fun (a : Edge V → Bool) e => matrixEntry e (a e))
      (fun a => f (matrixGraph a)) (1 / 3)
      ≤ qQuery (fun y : Edge V → Option (Edge V) => f (recordSet y)) (1 / 3) := by
    have h := qQueryOn_comp_read_le_qQuery (fun (a : Edge V → Bool) e => matrixEntry e (a e))
      (fun y : Edge V → Option (Edge V) => f (recordSet y)) (ε := 1 / 3)
      (queryCounts_nonempty (fun x y h => by rw [show x = y from h]) (by norm_num))
    simpa only [← matrixGraph_eq_recordSet] using h
  have h3 := qQuery_recordSet_eq_qList (ι := Edge V) f
  rw [card_edge] at h3
  calc qMatrix f
      ≤ 2 * qQueryOn (fun (a : Edge V → Bool) e => matrixEntry e (a e))
          (fun a => f (matrixGraph a)) (1 / 3) := h1
    _ ≤ 2 * qQuery (fun y : Edge V → Option (Edge V) => f (recordSet y)) (1 / 3) :=
        Nat.mul_le_mul_left 2 h2
    _ = 2 * qList f ((Fintype.card V).choose 2) := by rw [h3]

/-- **`eq:graph-model-comparison`, adjacency lists**: `Q_adj ≤ 2·Q_list(f; ∑ u, deg u)` for the
degree vector `deg`.  Position `(u, j)` of the virtual list holds the edge `{u, nbr(u, j)}`; a
list query is simulated by two array queries, and the positions are renamed
`Fin (∑ u, deg u)`, which the public degrees determine. -/
theorem qAdj_le_two_mul_qList (f : Finset (Edge V) → O) (deg : V → ℕ) :
    qAdj f deg ≤ 2 * qList f (∑ u, deg u) := by
  have : Nonempty O := ⟨f ∅⟩
  have := Fintype.ofFinite (AdjArray deg)
  have hne : (QueryCounts (fun (a : AdjArray deg) (p : AdjPos deg) => adjEdge p.1 (a.1 p))
      (fun a => f (adjGraph deg a.1)) (1 / 3)).Nonempty :=
    queryCounts_nonempty (fun a b h => congrArg (fun y => f (recordSet y)) h) (by norm_num)
  have h1 := qQueryOn_positionAlphabetMap_le (fun (p : AdjPos deg) w => adjEdge p.1 w)
    (fun a : AdjArray deg => a.1) (fun a => f (adjGraph deg a.1)) hne
  have h2 : qQueryOn (fun (a : AdjArray deg) (p : AdjPos deg) => adjEdge p.1 (a.1 p))
      (fun a => f (adjGraph deg a.1)) (1 / 3)
      ≤ qQuery (fun y : AdjPos deg → Option (Edge V) => f (recordSet y)) (1 / 3) :=
    qQueryOn_comp_read_le_qQuery (fun (a : AdjArray deg) (p : AdjPos deg) => adjEdge p.1 (a.1 p))
      (fun y : AdjPos deg → Option (Edge V) => f (recordSet y)) (ε := 1 / 3)
      (queryCounts_nonempty (fun x y h => by rw [show x = y from h]) (by norm_num))
  have h3 := qQuery_recordSet_eq_qList (ι := AdjPos deg) f
  rw [card_adjPos] at h3
  calc qAdj f deg
      ≤ 2 * qQueryOn (fun (a : AdjArray deg) (p : AdjPos deg) => adjEdge p.1 (a.1 p))
          (fun a => f (adjGraph deg a.1)) (1 / 3) := h1
    _ ≤ 2 * qQuery (fun y : AdjPos deg → Option (Edge V) => f (recordSet y)) (1 / 3) :=
        Nat.mul_le_mul_left 2 h2
    _ = 2 * qList f (∑ u, deg u) := by rw [h3]

/-- **`eq:graph-model-comparison`, adjacency lists for graphs with `m` edges**:
`Q_adj(f; m) ≤ 2·Q_list(f; 2m)`. -/
theorem qAdjEdges_le_two_mul_qList (f : Finset (Edge V) → O) (m : ℕ) :
    qAdjEdges f m ≤ 2 * qList f (2 * m) := by
  unfold qAdjEdges
  exact ciSup_le' fun d => (qAdj_le_two_mul_qList f d.1).trans (by rw [d.2])

end MonoidProduct.Graph
