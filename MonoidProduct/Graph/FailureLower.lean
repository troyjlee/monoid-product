import MonoidProduct.Graph.Enumeration
import MonoidProduct.Graph.FailureQueries
import MonoidProduct.Graph.VertexFaults
set_option linter.style.header false

/-!
# Lower bounds for failure profiles

`monoid.tex`, `prop:failure-profile-complexity`, the lower bounds: for every `v ≥ 2` and every `k`,

  `(1/10000)·min{v², v·√(v·k)} ≤ Q_matrix(Σ^E_k)` and the same for `Σ^V_k`

(`edgeFailureProfile_qMatrix_ge`, `vertexFailureProfile_qMatrix_ge`).  With the upper bound of
`Graph/FailureQueries.lean`, `Q_matrix(Σ^E_k) = Θ(min{v², v^{3/2}·√k})`
(`edgeFailureProfile_qMatrix_theta`).  The paper's range is `1 ≤ k ≤ v`; at `k = 0` the bound
is `0`.

**The matrix model on a family of graphs** (`qMatrix_ge_of_enumeration`).  If a family of graphs
`G x`, indexed by tuples `x` of `d`-subsets, has every adjacency bit constant or equal to one
membership bit, and the output separates the family, the enumeration adversary of
`Graph/Enumeration.lean` gives `(7/1376)·r·√(d(q − d)) ≤ Q_matrix`.

**The constructions** (vertices `b_j`, `j < q`, and `a_u`, `u < r`, from an embedding
`Fin q ⊕ Fin r ↪ V`; the other vertices are isolated).  All bits other than the `a_u b_j` bits
are fixed, and `a_u` is adjacent to `b_j` exactly when `j ∈ x u`.
* `2 ≤ k ≤ v/4`, `d = k − 1`: `B` is a clique and `A` is independent.  Deleting the `d` possible
  edges `{a_u, b_j}`, `j ∈ Y`, isolates `a_u` exactly when `Y = x u`; so does deleting the
  vertices `b_j`, `j ∈ Y`.  These failure sets have `d < k` elements, so either profile
  determines every `x u` (`edgeFailureProfile_baseGraph_injective`,
  `vertexFailureProfile_baseGraph_injective`).  With `q = ⌊v/2⌋` and `r = v − q` this gives
  `(7/8256)·v·√(v·k)`.
* `k = 1`, `d = 1`: both sides are independent and each `a_u` has one neighbour.  Every
  component contains exactly one vertex of `B`, so the component partition, which is the profile
  for `k = 1`, determines every neighbour (`connectedComponents_starGraph_injective`).  This
  replaces the cited connectivity lower bound and gives `(7/5504)·v^{3/2}` for `v ≥ 8`.
* `k > v/4`, `v ≥ 8`: the profile for `k` determines the profile for `k₀ = ⌊v/4⌋`, which costs
  `Ω(v²)`.
* `2 ≤ v ≤ 7`: two graphs with different profiles give `7/1376` (`qMatrix_ge_of_ne`).
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The matrix model on a family of graphs -/

/-- **Postprocessing is free** in the matrix model. -/
theorem qMatrix_postcomp_le {O O' : Type} [DecidableEq O] [DecidableEq O']
    (f : Finset (Edge V) → O) (g : O → O') : qMatrix (fun S => g (f S)) ≤ qMatrix f := by
  have : Nonempty O := ⟨f ∅⟩
  exact qQueryOn_postcomp_le (read := (id : (Edge V → Bool) → Edge V → Bool))
    (f := fun a => f (matrixGraph a)) (ε := 1 / 3) g
    (queryCounts_nonempty (fun a b h => by rw [show a = b from h]) (by norm_num))

/-- **Two graphs with different values** force `Q_matrix(f) ≥ 7/1376`. -/
theorem qMatrix_ge_of_ne {O : Type} [Finite O] [DecidableEq O] (f : Finset (Edge V) → O)
    {S T : Finset (Edge V)} (h : f S ≠ f T) : (7 / 1376 : ℝ) ≤ qMatrix f := by
  have := Fintype.ofFinite O
  have : Nonempty O := ⟨f ∅⟩
  have hdet : ∀ a b : Edge V → Bool, id a = id b → f (matrixGraph a) = f (matrixGraph b) :=
    fun a b hab => by rw [show a = b from hab]
  have h1 := one_le_advPMOn_of_ne (read := (id : (Edge V → Bool) → Edge V → Bool))
    (f := fun a => f (matrixGraph a)) hdet (x := fun e => decide (e ∈ S))
    (y := fun e => decide (e ∈ T)) (by simp only [matrixGraph_indicator]; exact h)
  have h2 := mul_advPMOn_le_qQueryOn_third_finiteOutput
    (read := (id : (Edge V → Bool) → Edge V → Bool)) (f := fun a => f (matrixGraph a)) hdet
  calc (7 / 1376 : ℝ) = 7 / 1376 * 1 := by ring
    _ ≤ 7 / 1376 * advPMOn (id : (Edge V → Bool) → Edge V → Bool)
          (fun a => f (matrixGraph a)) := by gcongr
    _ ≤ qMatrix f := h2

/-- **The matrix model restricted to a family of graphs** `G x` indexed by tuples of
`d`-subsets: if every adjacency bit is constant on the family or can only separate inputs that
differ in one membership bit, and `f` separates the family, then
`(7/1376)·r·√(d(q − d)) ≤ Q_matrix(f)`. -/
theorem qMatrix_ge_of_enumeration {O : Type} [Finite O] [DecidableEq O]
    (f : Finset (Edge V) → O) {r q d : ℕ} (hd : 0 < d) (hdq : d < q)
    (G : JTuple r q d → Finset (Edge V))
    (hpos : ∀ e : Edge V, (∀ x y, (e ∈ G x ↔ e ∈ G y)) ∨
      ∃ u b, ∀ x y, ¬(e ∈ G x ↔ e ∈ G y) → (b ∈ (x u).1 ↔ b ∉ (y u).1))
    (hsep : ∀ x y, f (G x) = f (G y) → x = y) :
    (7 / 1376 : ℝ) * (r * Real.sqrt (d * (q - d : ℕ))) ≤ qMatrix f := by
  have := Fintype.ofFinite O
  have : Nonempty O := ⟨f ∅⟩
  let read : JTuple r q d → Edge V → Bool := fun x e => decide (e ∈ G x)
  have hG : ∀ x, matrixGraph (read x) = G x := fun x => matrixGraph_indicator (G x)
  have hdet : ∀ x y, read x = read y → f (G x) = f (G y) := fun x y h => by
    rw [← hG x, ← hG y, h]
  have hread : ∀ e, (∀ x y, read x e = read y e) ∨
      ∃ u b, ∀ x y, read x e ≠ read y e → (b ∈ (x u).1 ↔ b ∉ (y u).1) := by
    intro e
    rcases hpos e with hc | ⟨u, b, hub⟩
    · exact Or.inl fun x y => by simp only [read, decide_eq_decide]; exact hc x y
    · exact Or.inr ⟨u, b, fun x y hne => hub x y fun hiff =>
        hne (by simp only [read, decide_eq_decide]; exact hiff)⟩
  have hadv := enumeration_advPMOn_ge hd hdq read (fun x => f (G x)) hdet
    (fun x y hxy h => hxy.ne (hsep x y h)) hread
  have hq := mul_advPMOn_le_qQueryOn_third_finiteOutput (read := read)
    (f := fun x => f (G x)) hdet
  have hres : qQueryOn read (fun x => f (G x)) (1 / 3) ≤ qMatrix f := by
    have h := qQueryOn_comp_read_le_qQuery read (fun a => f (matrixGraph a)) (ε := 1 / 3)
      (queryCounts_nonempty (fun a b hab => by rw [show a = b from hab]) (by norm_num))
    simp only [hG] at h
    exact h
  calc (7 / 1376 : ℝ) * (r * Real.sqrt (d * (q - d : ℕ)))
      ≤ 7 / 1376 * advPMOn read (fun x => f (G x)) := by gcongr
    _ ≤ qQueryOn read (fun x => f (G x)) (1 / 3) := hq
    _ ≤ qMatrix f := by exact_mod_cast hres

/-! ## The constructions -/

namespace FailureLower

variable {q r : ℕ} (lab : Fin q ⊕ Fin r ↪ V)

/-- The `j`th vertex of the side `B`. -/
def bVert (j : Fin q) : V := lab (Sum.inl j)

/-- The `u`th vertex of the side `A`, whose neighbourhood in `B` is unknown. -/
def aVert (u : Fin r) : V := lab (Sum.inr u)

omit [Fintype V] [DecidableEq V] in
theorem aVert_ne_bVert (u : Fin r) (j : Fin q) : aVert lab u ≠ bVert lab j :=
  fun h => Sum.inr_ne_inl (lab.injective h)

omit [Fintype V] [DecidableEq V] in
theorem aVert_injective : Function.Injective (aVert lab) :=
  fun _ _ h => Sum.inr_injective (lab.injective h)

omit [Fintype V] [DecidableEq V] in
theorem bVert_injective : Function.Injective (bVert lab) :=
  fun _ _ h => Sum.inl_injective (lab.injective h)

/-- The possible edge `{a_u, b_j}`. -/
def crossEdge (u : Fin r) (j : Fin q) : Edge V :=
  ⟨s(aVert lab u, bVert lab j), by simpa using aVert_ne_bVert lab u j⟩

omit [Fintype V] [DecidableEq V] in
/-- `s(a_u, w) = s(a_u', b_j)` exactly when `u = u'` and `w = b_j`. -/
theorem mk_aVert_eq_iff {u u' : Fin r} {j : Fin q} {w : V} :
    s(aVert lab u, w) = s(aVert lab u', bVert lab j) ↔ u = u' ∧ w = bVert lab j := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
    · exact ⟨aVert_injective lab h1, h2⟩
    · exact absurd h1 (aVert_ne_bVert lab u j)
  · rintro ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem crossEdge_injective {u u' : Fin r} {j j' : Fin q}
    (h : crossEdge lab u j = crossEdge lab u' j') : u = u' ∧ j = j' := by
  have h' : s(aVert lab u, bVert lab j) = s(aVert lab u', bVert lab j') := congrArg Subtype.val h
  obtain ⟨hu, hb⟩ := (mk_aVert_eq_iff lab).mp h'
  exact ⟨hu, bVert_injective lab hb⟩

/-- The cross edges of an input: `{a_u, b_j}` for every `j ∈ x u`. -/
def crossEdges {d : ℕ} (x : JTuple r q d) : Finset (Edge V) :=
  (Finset.univ.filter fun p : Fin r × Fin q => p.2 ∈ (x p.1).1).image
    fun p => crossEdge lab p.1 p.2

omit [Fintype V] in
theorem mem_crossEdges {d : ℕ} {x : JTuple r q d} {e : Edge V} :
    e ∈ crossEdges lab x ↔ ∃ u, ∃ j ∈ (x u).1, e = crossEdge lab u j := by
  simp only [crossEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨u, j, hj, rfl⟩
    exact ⟨u, j, hj, rfl⟩
  · rintro ⟨u, j, hj, rfl⟩
    exact ⟨u, j, hj, rfl⟩

omit [Fintype V] in
theorem crossEdge_mem_crossEdges {d : ℕ} {x : JTuple r q d} {u : Fin r} {j : Fin q} :
    crossEdge lab u j ∈ crossEdges lab x ↔ j ∈ (x u).1 := by
  rw [mem_crossEdges]
  constructor
  · rintro ⟨u', j', hj', h⟩
    obtain ⟨rfl, rfl⟩ := crossEdge_injective lab h
    exact hj'
  · intro hj
    exact ⟨u, j, hj, rfl⟩

/-- The clique on `B`. -/
def bClique : Finset (Edge V) :=
  Finset.univ.filter fun e => ∃ j j' : Fin q, (e : Sym2 V) = s(bVert lab j, bVert lab j')

theorem aVert_notMem_of_mem_bClique {e : Edge V} (he : e ∈ bClique lab) (u : Fin r) :
    aVert lab u ∉ (e : Sym2 V) := by
  obtain ⟨j, j', hjj⟩ := (Finset.mem_filter.mp he).2
  rw [hjj, Sym2.mem_iff]
  rintro (h | h)
  · exact aVert_ne_bVert lab u j h
  · exact aVert_ne_bVert lab u j' h

theorem crossEdge_notMem_bClique (u : Fin r) (j : Fin q) : crossEdge lab u j ∉ bClique lab :=
  fun h => aVert_notMem_of_mem_bClique lab h u (Sym2.mem_mk_left _ _)

/-! ### Adjacency bits -/

omit [Fintype V] in
/-- **Every adjacency bit is fixed or one membership bit**, for graphs `B₀ ∪ crossEdges x`
whose fixed part `B₀` contains no cross edge. -/
theorem position_of_base {d : ℕ} (B0 : Finset (Edge V)) (hB0 : ∀ u j, crossEdge lab u j ∉ B0)
    (e : Edge V) :
    (∀ x y : JTuple r q d, (e ∈ B0 ∪ crossEdges lab x ↔ e ∈ B0 ∪ crossEdges lab y)) ∨
      ∃ u b, ∀ x y : JTuple r q d,
        ¬(e ∈ B0 ∪ crossEdges lab x ↔ e ∈ B0 ∪ crossEdges lab y) →
          (b ∈ (x u).1 ↔ b ∉ (y u).1) := by
  by_cases he : ∃ u j, e = crossEdge lab u j
  · obtain ⟨u, j, rfl⟩ := he
    refine Or.inr ⟨u, j, fun x y hne => ?_⟩
    simp only [Finset.mem_union, hB0, false_or, crossEdge_mem_crossEdges] at hne
    tauto
  · refine Or.inl fun x y => ?_
    have hc : ∀ z : JTuple r q d, e ∉ crossEdges lab z := fun z h => by
      obtain ⟨u, j, -, rfl⟩ := (mem_crossEdges lab).mp h
      exact he ⟨u, j, rfl⟩
    simp only [Finset.mem_union, hc, or_false]

/-! ### Neighbourhoods of the vertices `a_u` -/

omit [Fintype V] in
/-- The neighbours of `a_u`, after deleting a set `F` of possible edges, are the `b_j` with
`j ∈ x u` and `{a_u, b_j} ∉ F`. -/
theorem adj_aVert_iff {d : ℕ} {B0 : Finset (Edge V)}
    (hA : ∀ e ∈ B0, ∀ u, aVert lab u ∉ (e : Sym2 V)) {x : JTuple r q d} {F : Finset (Edge V)}
    {u : Fin r} {w : V} :
    (toGraph ((B0 ∪ crossEdges lab x) \ F)).Adj (aVert lab u) w ↔
      ∃ j ∈ (x u).1, crossEdge lab u j ∉ F ∧ w = bVert lab j := by
  rw [toGraph_adj]
  constructor
  · rintro ⟨e, he, hew⟩
    rw [Finset.mem_sdiff, Finset.mem_union] at he
    obtain ⟨he0 | hec, heF⟩ := he
    · exact absurd (hew.symm ▸ Sym2.mem_mk_left _ _) (hA e he0 u)
    · obtain ⟨u', j, hj, rfl⟩ := (mem_crossEdges lab).mp hec
      have h' : s(aVert lab u, w) = s(aVert lab u', bVert lab j) := hew.symm
      obtain ⟨rfl, rfl⟩ := (mk_aVert_eq_iff lab).mp h'
      exact ⟨j, hj, heF, rfl⟩
  · rintro ⟨j, hj, hjF, rfl⟩
    exact ⟨crossEdge lab u j, Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right _ ((crossEdge_mem_crossEdges lab).mpr hj), hjF⟩, rfl⟩

omit [Fintype V] in
/-- **Deleting edges isolates `a_u` exactly when they cover its neighbourhood**: after deleting
`{a_u, b_j}` for `j ∈ Y`, the vertex `a_u` is reachable only from itself exactly when
`x u ⊆ Y`. -/
theorem isolated_sdiff_iff {d : ℕ} {B0 : Finset (Edge V)}
    (hA : ∀ e ∈ B0, ∀ u, aVert lab u ∉ (e : Sym2 V)) {x : JTuple r q d} {u : Fin r}
    {Y : Finset (Fin q)} :
    (∀ w, (toGraph ((B0 ∪ crossEdges lab x) \ Y.image (crossEdge lab u))).Reachable
      (aVert lab u) w → w = aVert lab u) ↔ (x u).1 ⊆ Y := by
  constructor
  · intro hiso j hj
    by_contra hjY
    have hnF : crossEdge lab u j ∉ Y.image (crossEdge lab u) := fun h => by
      obtain ⟨j', hj', heq⟩ := Finset.mem_image.mp h
      obtain ⟨-, rfl⟩ := crossEdge_injective lab heq
      exact hjY hj'
    have hadj := (adj_aVert_iff lab hA).mpr ⟨j, hj, hnF, rfl⟩
    exact aVert_ne_bVert lab u j (hiso _ hadj.reachable).symm
  · intro hsub w hw
    refine eq_of_reachable_of_forall_not_adj (fun z hz => ?_) hw
    obtain ⟨j, hj, hjF, -⟩ := (adj_aVert_iff lab hA).mp hz
    exact hjF (Finset.mem_image_of_mem _ (hsub hj))

omit [Fintype V] in
theorem aVert_notMem_image_bVert (u : Fin r) (Y : Finset (Fin q)) :
    aVert lab u ∉ Y.image (bVert lab) := fun h => by
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
  exact aVert_ne_bVert lab u j hj.symm

omit [Fintype V] in
/-- **Deleting vertices isolates `a_u` exactly when they cover its neighbourhood**: in
`G − {b_j : j ∈ Y}`, the vertex `a_u` is reachable only from itself exactly when `x u ⊆ Y`. -/
theorem isolated_induce_iff {d : ℕ} {B0 : Finset (Edge V)}
    (hA : ∀ e ∈ B0, ∀ u, aVert lab u ∉ (e : Sym2 V)) {x : JTuple r q d} {u : Fin r}
    {Y : Finset (Fin q)} :
    (∀ w (hw : w ∉ Y.image (bVert lab)),
      ((toGraph (B0 ∪ crossEdges lab x)).induce {z | z ∉ Y.image (bVert lab)}).Reachable
        ⟨aVert lab u, aVert_notMem_image_bVert lab u Y⟩ ⟨w, hw⟩ → w = aVert lab u) ↔
      (x u).1 ⊆ Y := by
  have hadj : ∀ w, (toGraph (B0 ∪ crossEdges lab x)).Adj (aVert lab u) w ↔
      ∃ j ∈ (x u).1, w = bVert lab j := fun w => by
    have h := adj_aVert_iff lab hA (x := x) (F := ∅) (u := u) (w := w)
    rw [Finset.sdiff_empty] at h
    rw [h]
    simp
  constructor
  · intro hiso j hj
    by_contra hjY
    have hbj : bVert lab j ∉ Y.image (bVert lab) := fun h => by
      obtain ⟨j', hj', heq⟩ := Finset.mem_image.mp h
      exact hjY (bVert_injective lab heq ▸ hj')
    have hind : ((toGraph (B0 ∪ crossEdges lab x)).induce {z | z ∉ Y.image (bVert lab)}).Adj
        ⟨aVert lab u, aVert_notMem_image_bVert lab u Y⟩ ⟨bVert lab j, hbj⟩ :=
      (hadj _).mpr ⟨j, hj, rfl⟩
    exact aVert_ne_bVert lab u j (hiso _ hbj hind.reachable).symm
  · intro hsub w hw hr
    have := eq_of_reachable_of_forall_not_adj (fun z hz => ?_) hr
    · exact congrArg Subtype.val this
    · obtain ⟨j, hj, hzj⟩ := (hadj z.1).mp hz
      exact z.2 (hzj ▸ Finset.mem_image_of_mem _ (hsub hj))

/-! ### The profiles determine the input -/

/-- **The edge profile determines every neighbourhood** (`d < k`): deleting the `d` possible
edges `{a_u, b_j}`, `j ∈ x u`, isolates `a_u` in `G x` and in no `G y` with `y u ≠ x u`. -/
theorem edgeFailureProfile_baseGraph_injective {d k : ℕ} (hdk : d < k) {B0 : Finset (Edge V)}
    (hA : ∀ e ∈ B0, ∀ u, aVert lab u ∉ (e : Sym2 V)) {x y : JTuple r q d}
    (h : edgeFailureProfile k (B0 ∪ crossEdges lab x) =
      edgeFailureProfile k (B0 ∪ crossEdges lab y)) : x = y := by
  funext u
  let Y : Finset (Fin q) := (x u).1
  have hF : (Y.image (crossEdge lab u)).card < k :=
    (Finset.card_image_le.trans (le_of_eq (x u).2)).trans_lt hdk
  have hcoord := congrFun h ⟨Y.image (crossEdge lab u), hF⟩
  have hx := (isolated_sdiff_iff lab hA (x := x) (u := u) (Y := Y)).mpr subset_rfl
  have hy : (y u).1 ⊆ Y := by
    refine (isolated_sdiff_iff lab hA (x := y) (u := u) (Y := Y)).mp fun w hw => hx w ?_
    have hmem : (aVert lab u, w) ∈
        edgeFailureProfile k (B0 ∪ crossEdges lab y) ⟨Y.image (crossEdge lab u), hF⟩ :=
      mem_edgeFailureProfile.mpr hw
    rw [← hcoord] at hmem
    have hr := mem_edgeFailureProfile.mp hmem
    exact hr
  exact (Subtype.ext (Finset.eq_of_subset_of_card_le hy (by rw [(x u).2, (y u).2]))).symm

/-- **The vertex profile determines every neighbourhood** (`d < k`): deleting the `d` vertices
`b_j`, `j ∈ x u`, isolates `a_u` in `G x` and in no `G y` with `y u ≠ x u`. -/
theorem vertexFailureProfile_baseGraph_injective {d k : ℕ} (hdk : d < k)
    {B0 : Finset (Edge V)} (hA : ∀ e ∈ B0, ∀ u, aVert lab u ∉ (e : Sym2 V))
    {x y : JTuple r q d}
    (h : vertexFailureProfile k (B0 ∪ crossEdges lab x) =
      vertexFailureProfile k (B0 ∪ crossEdges lab y)) : x = y := by
  funext u
  have hX : ((x u).1.image (bVert lab)).card < k :=
    (Finset.card_image_le.trans (le_of_eq (x u).2)).trans_lt hdk
  have hx := (isolated_induce_iff lab hA (x := x) (u := u) (Y := (x u).1)).mpr subset_rfl
  have hy : (y u).1 ⊆ (x u).1 := by
    refine (isolated_induce_iff lab hA).mp fun w hw hr => hx w hw ?_
    have hmem : (aVert lab u, w) ∈
        vertexFailureProfile k (B0 ∪ crossEdges lab y) ⟨_, hX⟩ :=
      mem_vertexFailureProfile.mpr ⟨aVert_notMem_image_bVert lab u _, hw, hr⟩
    rw [← h] at hmem
    obtain ⟨_, _, hr'⟩ := mem_vertexFailureProfile.mp hmem
    exact hr'
  exact (Subtype.ext (Finset.eq_of_subset_of_card_le hy (by rw [(x u).2, (y u).2]))).symm

omit [Fintype V] [DecidableEq V] in
/-- A set closed under adjacency contains everything reachable from it. -/
theorem mem_of_reachable_of_closed {G : SimpleGraph V} {C : Set V}
    (hC : ∀ a b, G.Adj a b → a ∈ C → b ∈ C) {a b : V} (ha : a ∈ C) (h : G.Reachable a b) :
    b ∈ C := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ha
  | tail _ hab ih => exact hC _ _ hab ih

/-- **In the star construction, `a_u` is connected to `b_j` exactly when `j ∈ x u`**: every
component contains exactly one vertex of `B`. -/
theorem mem_connectedComponents_star {x : JTuple r q 1} {u : Fin r} {j : Fin q} :
    (aVert lab u, bVert lab j) ∈ connectedComponents (∅ ∪ crossEdges lab x) ↔ j ∈ (x u).1 := by
  rw [mem_connectedComponents]
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := Finset.card_eq_one.mp (x u).2
    have hsingle : ∀ u', σ ∈ (x u').1 → (x u').1 = {σ} := fun u' hu' => by
      obtain ⟨τ, hτ⟩ := Finset.card_eq_one.mp (x u').2
      rw [hτ, Finset.mem_singleton] at hu'
      rw [hτ, hu']
    let C : Set V := {w | w = bVert lab σ ∨ ∃ u', w = aVert lab u' ∧ (x u').1 = {σ}}
    have hC : ∀ a b, (toGraph (∅ ∪ crossEdges lab x)).Adj a b → a ∈ C → b ∈ C := by
      intro a b hab ha
      obtain ⟨e, he, heab⟩ := toGraph_adj.mp hab
      rw [Finset.empty_union] at he
      obtain ⟨u'', j'', hj'', rfl⟩ := (mem_crossEdges lab).mp he
      have heab' : s(aVert lab u'', bVert lab j'') = s(a, b) := heab
      rcases ha with rfl | ⟨u', rfl, hu'⟩
      · rcases Sym2.eq_iff.mp heab' with ⟨h1, -⟩ | ⟨h1, h2⟩
        · exact absurd h1 (aVert_ne_bVert lab u'' σ)
        · have hj : j'' = σ := bVert_injective lab h2
          subst hj
          exact Or.inr ⟨u'', h1.symm, hsingle u'' hj''⟩
      · rcases Sym2.eq_iff.mp heab' with ⟨h1, h2⟩ | ⟨-, h2⟩
        · have hu : u'' = u' := aVert_injective lab h1
          subst hu
          rw [hu', Finset.mem_singleton] at hj''
          subst hj''
          exact Or.inl h2.symm
        · exact absurd h2.symm (aVert_ne_bVert lab u' j'')
    have hb := mem_of_reachable_of_closed hC (Or.inr ⟨u, rfl, hσ⟩) h
    rcases hb with hb | ⟨u', hb, -⟩
    · rw [bVert_injective lab hb, hσ]
      exact Finset.mem_singleton_self σ
    · exact absurd hb.symm (aVert_ne_bVert lab u' j)
  · intro hj
    refine Adj.reachable (toGraph_adj.mpr ⟨crossEdge lab u j, ?_, rfl⟩)
    rw [Finset.empty_union]
    exact (crossEdge_mem_crossEdges lab).mpr hj

/-- **In the star construction the component partition determines the input.** -/
theorem connectedComponents_starGraph_injective {x y : JTuple r q 1}
    (h : connectedComponents (∅ ∪ crossEdges lab x) = connectedComponents (∅ ∪ crossEdges lab y)) :
    x = y := by
  funext u
  refine Subtype.ext (Finset.ext fun j => ?_)
  rw [← mem_connectedComponents_star lab, h, mem_connectedComponents_star lab]

end FailureLower

open FailureLower

/-! ## The three regimes -/

/-- **`2 ≤ k ≤ v/4`**: for any output that separates the clique construction with `d = k − 1`,
`Q_matrix ≥ (7/8256)·v·√(v·k)`. -/
theorem qMatrix_ge_clique {O : Type} [Finite O] [DecidableEq O] (P : Finset (Edge V) → O)
    {k : ℕ} (hk : 2 ≤ k) (hkv : 4 * k ≤ Fintype.card V)
    (hsep : ∀ {q r : ℕ} (lab : Fin q ⊕ Fin r ↪ V) (x y : JTuple r q (k - 1)),
      P (bClique lab ∪ crossEdges lab x) = P (bClique lab ∪ crossEdges lab y) → x = y) :
    (7 / 8256 : ℝ) * (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤ qMatrix P := by
  set v := Fintype.card V with hvdef
  obtain ⟨lab⟩ : Nonempty (Fin (v / 2) ⊕ Fin (v - v / 2) ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simp [Fintype.card_sum, hvdef]; omega)
  have h := qMatrix_ge_of_enumeration P (d := k - 1) (by omega) (by omega)
    (fun x => bClique lab ∪ crossEdges lab x)
    (position_of_base lab (bClique lab) (crossEdge_notMem_bClique lab)) (hsep lab)
  refine le_trans ?_ h
  have hvr : (v : ℝ) ≤ 2 * ((v - v / 2 : ℕ) : ℝ) := by
    have : v ≤ 2 * (v - v / 2) := by omega
    exact_mod_cast this
  have hprod : (v : ℝ) * k ≤ 9 * (((k - 1 : ℕ) : ℝ) * ((v / 2 - (k - 1) : ℕ) : ℝ)) := by
    have h1 : (k : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ) := by
      have : k ≤ 2 * (k - 1) := by omega
      exact_mod_cast this
    have h2 : (v : ℝ) ≤ 4 * ((v / 2 - (k - 1) : ℕ) : ℝ) := by
      have : v ≤ 4 * (v / 2 - (k - 1)) := by omega
      exact_mod_cast this
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
    nlinarith [mul_le_mul h2 h1 hk0 (by positivity)]
  have hsq : Real.sqrt (v * k) ≤
      3 * Real.sqrt (((k - 1 : ℕ) : ℝ) * ((v / 2 - (k - 1) : ℕ) : ℝ)) := by
    have h3 : (3 : ℝ) = Real.sqrt 9 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h3, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hprod
  have hmul := mul_le_mul hvr hsq (Real.sqrt_nonneg _) (by positivity)
  calc (7 / 8256 : ℝ) * (v * Real.sqrt (v * k))
      ≤ 7 / 8256 * ((2 * ((v - v / 2 : ℕ) : ℝ)) *
          (3 * Real.sqrt (((k - 1 : ℕ) : ℝ) * ((v / 2 - (k - 1) : ℕ) : ℝ)))) := by gcongr
    _ = 7 / 1376 * (((v - v / 2 : ℕ) : ℝ) *
          Real.sqrt (((k - 1 : ℕ) : ℝ) * ((v / 2 - (k - 1) : ℕ) : ℝ))) := by ring

/-- **`k = 1`, `v ≥ 8`**: for any output that separates the star construction,
`Q_matrix ≥ (7/5504)·v^{3/2}`. -/
theorem qMatrix_ge_star {O : Type} [Finite O] [DecidableEq O] (P : Finset (Edge V) → O)
    (hv : 8 ≤ Fintype.card V)
    (hsep : ∀ {q r : ℕ} (lab : Fin q ⊕ Fin r ↪ V) (x y : JTuple r q 1),
      P (∅ ∪ crossEdges lab x) = P (∅ ∪ crossEdges lab y) → x = y) :
    (7 / 5504 : ℝ) * (Fintype.card V * Real.sqrt (Fintype.card V)) ≤ qMatrix P := by
  set v := Fintype.card V with hvdef
  obtain ⟨lab⟩ : Nonempty (Fin (v / 2) ⊕ Fin (v - v / 2) ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simp [Fintype.card_sum, hvdef]; omega)
  have h := qMatrix_ge_of_enumeration P (d := 1) one_pos (by omega)
    (fun x => ∅ ∪ crossEdges lab x)
    (position_of_base lab ∅ fun _ _ h => Finset.notMem_empty _ h) (hsep lab)
  refine le_trans ?_ h
  have hvr : (v : ℝ) ≤ 2 * ((v - v / 2 : ℕ) : ℝ) := by
    have : v ≤ 2 * (v - v / 2) := by omega
    exact_mod_cast this
  have hq : (v : ℝ) ≤ 4 * ((v / 2 - 1 : ℕ) : ℝ) := by
    have : v ≤ 4 * (v / 2 - 1) := by omega
    exact_mod_cast this
  have hsq : Real.sqrt v ≤ 2 * Real.sqrt (((1 : ℕ) : ℝ) * ((v / 2 - 1 : ℕ) : ℝ)) := by
    have h2 : (2 : ℝ) = Real.sqrt 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Nat.cast_one, one_mul, h2, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hq
  have hmul := mul_le_mul hvr hsq (Real.sqrt_nonneg _) (by positivity)
  calc (7 / 5504 : ℝ) * (v * Real.sqrt v)
      ≤ 7 / 5504 * ((2 * ((v - v / 2 : ℕ) : ℝ)) *
          (2 * Real.sqrt (((1 : ℕ) : ℝ) * ((v / 2 - 1 : ℕ) : ℝ)))) := by gcongr
    _ = 7 / 1376 * (((v - v / 2 : ℕ) : ℝ) *
          Real.sqrt (((1 : ℕ) : ℝ) * ((v / 2 - 1 : ℕ) : ℝ))) := by ring

/-- The fixed part `B₀` of the constructions avoids the vertices `a_u`. -/
private theorem hA_bClique {q r : ℕ} (lab : Fin q ⊕ Fin r ↪ V) :
    ∀ e ∈ bClique lab, ∀ u, aVert lab u ∉ (e : Sym2 V) :=
  fun _ he u => aVert_notMem_of_mem_bClique lab he u

omit [Fintype V] [DecidableEq V] in
private theorem hA_empty {q r : ℕ} (lab : Fin q ⊕ Fin r ↪ V) :
    ∀ e ∈ (∅ : Finset (Edge V)), ∀ u, aVert lab u ∉ (e : Sym2 V) :=
  fun _ he => absurd he (Finset.notMem_empty _)

omit [DecidableEq V] in
/-- Two vertices give two graphs with different partitions: no edge, and the edge `{a, b}`. -/
private theorem exists_ne_connectedComponents (hv : 2 ≤ Fintype.card V) :
    ∃ (e : Edge V) (a b : V), (a, b) ∈ connectedComponents {e} ∧
      (a, b) ∉ connectedComponents (∅ : Finset (Edge V)) := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  refine ⟨⟨s(a, b), by simpa using hab⟩, a, b, ?_, ?_⟩
  · rw [mem_connectedComponents]
    exact (toGraph_adj.mpr ⟨_, Finset.mem_singleton_self _, rfl⟩).reachable
  · rw [mem_connectedComponents, toGraph_empty, reachable_bot]
    exact hab

/-- The real arithmetic of the final case analysis. -/
private theorem final_bound {v k : ℕ} (hv : 2 ≤ v) {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hsmall : v ≤ 7 → 1 ≤ k → (7 / 1376 : ℝ) ≤ Q)
    (hstar : 8 ≤ v → k = 1 → (7 / 5504 : ℝ) * (v * Real.sqrt v) ≤ Q)
    (hclique : 8 ≤ v → 2 ≤ k → 4 * k ≤ v → (7 / 8256 : ℝ) * (v * Real.sqrt (v * k)) ≤ Q)
    (htrunc : 8 ≤ v → 2 ≤ k → v < 4 * k →
      (7 / 8256 : ℝ) * (v * Real.sqrt (v * (v / 4 : ℕ))) ≤ Q) :
    (1 / 10000 : ℝ) * min ((v : ℝ) ^ 2) (v * Real.sqrt (v * k)) ≤ Q := by
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  have hmin1 : min ((v : ℝ) ^ 2) (v * Real.sqrt (v * k)) ≤ (v : ℝ) ^ 2 := min_le_left _ _
  have hmin2 : min ((v : ℝ) ^ 2) (v * Real.sqrt (v * k)) ≤ v * Real.sqrt (v * k) :=
    min_le_right _ _
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have h0 : min ((v : ℝ) ^ 2) (v * Real.sqrt (v * ((0 : ℕ) : ℝ))) = 0 := by
      rw [Nat.cast_zero, mul_zero, Real.sqrt_zero, mul_zero]
      exact min_eq_right (sq_nonneg _)
    rw [h0, mul_zero]
    exact hQ0
  by_cases h7 : v ≤ 7
  · have hQ := hsmall h7 hk0
    have hv7 : (v : ℝ) ≤ 7 := by exact_mod_cast h7
    have hsq : (v : ℝ) ^ 2 ≤ 49 := by nlinarith
    linarith
  have h8 : 8 ≤ v := by omega
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · have hQ := hstar h8 rfl
    rw [Nat.cast_one, mul_one] at hmin2 ⊢
    have hs : 0 ≤ (v : ℝ) * Real.sqrt v := by positivity
    linarith
  by_cases h4 : 4 * k ≤ v
  · have hQ := hclique h8 hk2 h4
    have hs : 0 ≤ (v : ℝ) * Real.sqrt (v * k) := by positivity
    linarith
  · have hQ := htrunc h8 hk2 (by omega)
    have hk0' : (v : ℝ) ≤ 9 * ((v / 4 : ℕ) : ℝ) := by
      have : v ≤ 9 * (v / 4) := by omega
      exact_mod_cast this
    have hsq : (v : ℝ) / 3 ≤ Real.sqrt (v * (v / 4 : ℕ)) := by
      rw [show (v : ℝ) / 3 = Real.sqrt (((v : ℝ) / 3) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hvv := mul_le_mul_of_nonneg_left hsq hv0
    have hs : 0 ≤ (v : ℝ) * Real.sqrt (v * (v / 4 : ℕ)) := by positivity
    nlinarith

/-- **`prop:failure-profile-complexity`, lower bound for edge failures**: for every `v ≥ 2` and
every `k`, `(1/10000)·min{v², v·√(v·k)} ≤ Q_matrix(Σ^E_k)`. -/
theorem edgeFailureProfile_qMatrix_ge (hv : 2 ≤ Fintype.card V) (k : ℕ) :
    (1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (edgeFailureProfile (V := V) k) := by
  refine final_bound hv (Nat.cast_nonneg _) (fun _ hk1 => ?_) (fun hv8 hk => ?_)
    (fun _ hk2 h4 => ?_) (fun _ hk2 h4 => ?_)
  · obtain ⟨e, a, b, h1, h2⟩ := exists_ne_connectedComponents hv
    refine qMatrix_ge_of_ne _ (S := {e}) (T := ∅) fun h => h2 ?_
    have h' := congrFun h ⟨∅, by simp; omega⟩
    simp only [edgeFailureProfile, Finset.sdiff_empty] at h'
    rw [← h']
    exact h1
  · subst hk
    exact qMatrix_ge_star _ hv8 fun lab x y h =>
      connectedComponents_starGraph_injective lab (edgeFailureProfile_one_eq_iff.mp h)
  · exact qMatrix_ge_clique _ hk2 h4 fun lab x y h =>
      edgeFailureProfile_baseGraph_injective lab (by omega) (hA_bClique lab) h
  · have hk0 : 2 ≤ Fintype.card V / 4 := by omega
    have hkk : Fintype.card V / 4 ≤ k := by omega
    have h := qMatrix_ge_clique (edgeFailureProfile (V := V) (Fintype.card V / 4)) hk0
      (by omega) fun lab x y h =>
        edgeFailureProfile_baseGraph_injective lab (by omega) (hA_bClique lab) h
    refine h.trans (Nat.cast_le.mpr ?_)
    exact qMatrix_postcomp_le (edgeFailureProfile (V := V) k)
      (fun P (F : EdgeFailureSet V (Fintype.card V / 4)) => P ⟨F.1, F.2.trans_le hkk⟩)

/-- **`prop:failure-profile-complexity`, lower bound for vertex failures**: for every `v ≥ 2`
and every `k`, `(1/10000)·min{v², v·√(v·k)} ≤ Q_matrix(Σ^V_k)`. -/
theorem vertexFailureProfile_qMatrix_ge (hv : 2 ≤ Fintype.card V) (k : ℕ) :
    (1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (vertexFailureProfile (V := V) k) := by
  refine final_bound hv (Nat.cast_nonneg _) (fun _ hk1 => ?_) (fun hv8 hk => ?_)
    (fun _ hk2 h4 => ?_) (fun _ hk2 h4 => ?_)
  · obtain ⟨e, a, b, h1, h2⟩ := exists_ne_connectedComponents hv
    refine qMatrix_ge_of_ne _ (S := {e}) (T := ∅) fun h => h2 ?_
    have hk : 0 < k := by omega
    have hmem : (a, b) ∈ vertexFailureProfile k {e} ⟨∅, by simpa using hk⟩ := by
      rw [mem_vertexFailureProfile_empty hk]
      exact mem_connectedComponents.mp h1
    rw [h, mem_vertexFailureProfile_empty hk] at hmem
    exact mem_connectedComponents.mpr hmem
  · subst hk
    exact qMatrix_ge_star _ hv8 fun lab x y h =>
      connectedComponents_starGraph_injective lab (vertexFailureProfile_one_eq_iff.mp h)
  · exact qMatrix_ge_clique _ hk2 h4 fun lab x y h =>
      vertexFailureProfile_baseGraph_injective lab (by omega) (hA_bClique lab) h
  · have hk0 : 2 ≤ Fintype.card V / 4 := by omega
    have hkk : Fintype.card V / 4 ≤ k := by omega
    have h := qMatrix_ge_clique (vertexFailureProfile (V := V) (Fintype.card V / 4)) hk0
      (by omega) fun lab x y h =>
        vertexFailureProfile_baseGraph_injective lab (by omega) (hA_bClique lab) h
    refine h.trans (Nat.cast_le.mpr ?_)
    exact qMatrix_postcomp_le (vertexFailureProfile (V := V) k)
      (fun P (X : VertexFailureSet V (Fintype.card V / 4)) => P ⟨X.1, X.2.trans_le hkk⟩)

/-- **`prop:failure-profile-complexity` for edge failures, both halves**: for every `v ≥ 2` and
every `k`, `(1/10000)·min{v², v·√(v·k)} ≤ Q_matrix(Σ^E_k) ≤ 2^18·min{v², v·√(v·k)}`. -/
theorem edgeFailureProfile_qMatrix_theta (hv : 2 ≤ Fintype.card V) (k : ℕ) :
    (1 / 10000 : ℝ) * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) ≤
      qMatrix (edgeFailureProfile (V := V) k) ∧
    (qMatrix (edgeFailureProfile (V := V) k) : ℝ) ≤
      2 ^ 18 * min ((Fintype.card V : ℝ) ^ 2)
        (Fintype.card V * Real.sqrt (Fintype.card V * k)) :=
  ⟨edgeFailureProfile_qMatrix_ge hv k, edgeFailureProfile_qMatrix_le_min k⟩

end MonoidProduct.Graph
