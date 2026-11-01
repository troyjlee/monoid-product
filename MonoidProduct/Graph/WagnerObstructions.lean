import MonoidProduct.Graph.CycleArcs
import MonoidProduct.Graph.WagnerConnectivity
set_option linter.style.header false

/-!
# Obstructions to attaching an edge to a cycle

Let `xy` be an edge of `G` and `C` a cycle of `G` avoiding `x` and `y`.  The edge attaches to `C`
through `X`, the neighbours of `x` on `C`, and `Y`, the neighbours of `y` on `C`.  Two attachment
patterns give an excluded minor, with explicit branch sets built from arcs of `C`:

* **Three common attachments** `u, v, w`, in this cyclic order, give a `K₅` model
  (`MinorModel.ofThreeCommon`) with branch sets `{x}`, `{y}` and the arcs from `u` to `v`, from `v`
  to `w` and from `w` to `u`; so `K₅` is a minor (`isMinor_top_five_of_three_common`, and
  `isMinor_top_five_of_three_common'` for three distinct common attachments in any order).
* **Four alternating attachments** `x₁, y₁, x₂, y₂`, distinct and in this cyclic order, with
  `x₁, x₂` attached to `x` and `y₁, y₂` to `y`, give a `K₃,₃` model (`MinorModel.ofAlternating`)
  with branch sets `{x}`, `arc C y₁ x₂`, `arc C y₂ x₁` on one side and `{y}`, `arc C x₁ y₁`,
  `arc C x₂ y₂` on the other (`isMinor_completeBipartite_of_alternating`).
* **The interval lemma** (`exists_isConsecutive_subset_closedArc`): if `G` has neither minor and
  each of `x` and `y` has at least two neighbours on `C`, then the neighbours of `y` on `C` all lie
  on the closed arc between two consecutive neighbours of `x`.  This includes the case `Y ⊆ X`, and
  the case `|X| = 2`, where the two neighbours of `x` cut `C` into only two arcs.  It follows from
  a statement about marks on a cyclic list, `exists_isConsecutive_subset_closedArc_of_cyclic`: at
  most two marks of `X` are marks of `Y`, and no four distinct marks alternate between `X` and `Y`.
* `MinorModel.ofPairwise`, `MinorModel.ofBipartite`: complete and complete bipartite minor models
  from branch sets, with each unordered pair of branch sets checked once.
* `mem_arc_iff_of_cycDist_le`, `mem_arc_iff_cycDist_le`: membership in an arc, read off the
  distances from a vertex that does not lie strictly inside it.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V : Type*}

/-! ## Complete and complete bipartite minor models -/

section Models

variable {G : SimpleGraph V}

namespace MinorModel

/-- **A complete minor from pairwise adjacent branch sets**: connected branch sets indexed by a
linearly ordered type, where for `i < j` the branch sets of `i` and `j` are disjoint and joined by
an edge. -/
def ofPairwise {ι : Type*} [LinearOrder ι] (S : ι → Set V)
    (hconn : ∀ i, IsConnectedSet G (S i)) (hdisj : ∀ i j, i < j → Disjoint (S i) (S j))
    (hadj : ∀ i j, i < j → ∃ a ∈ S i, ∃ b ∈ S j, G.Adj a b) :
    MinorModel (⊤ : SimpleGraph ι) G where
  branch := S
  connected := hconn
  disjoint i j hij := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdisj i j h
    · exact (hdisj j i h).symm
  adj i j hij := by
    rcases lt_or_gt_of_ne ((top_adj i j).mp hij) with h | h
    · exact hadj i j h
    · obtain ⟨a, ha, b, hb, hab⟩ := hadj j i h
      exact ⟨b, hb, a, ha, hab.symm⟩

/-- **A complete bipartite minor from branch sets on two sides**: connected branch sets, pairwise
disjoint, with an edge between the branch sets of any left vertex and any right vertex.
Disjointness on each side is checked for `i < i'` only. -/
def ofBipartite {ι κ : Type*} [LinearOrder ι] [LinearOrder κ] (L : ι → Set V) (R : κ → Set V)
    (hL : ∀ i, IsConnectedSet G (L i)) (hR : ∀ j, IsConnectedSet G (R j))
    (hLL : ∀ i i', i < i' → Disjoint (L i) (L i')) (hRR : ∀ j j', j < j' → Disjoint (R j) (R j'))
    (hLR : ∀ i j, Disjoint (L i) (R j)) (hadj : ∀ i j, ∃ a ∈ L i, ∃ b ∈ R j, G.Adj a b) :
    MinorModel (completeBipartiteGraph ι κ) G where
  branch := Sum.elim L R
  connected := by
    rintro (i | j)
    · exact hL i
    · exact hR j
  disjoint := by
    rintro (i | j) (i' | j') h
    · rcases lt_or_gt_of_ne (fun e => h (congrArg Sum.inl e) : i ≠ i') with h' | h'
      · exact hLL i i' h'
      · exact (hLL i' i h').symm
    · exact hLR i j'
    · exact (hLR i' j).symm
    · rcases lt_or_gt_of_ne (fun e => h (congrArg Sum.inr e) : j ≠ j') with h' | h'
      · exact hRR j j' h'
      · exact (hRR j' j h').symm
  adj := by
    rintro (i | j) (i' | j') h
    · simp at h
    · exact hadj i j'
    · obtain ⟨a, ha, b, hb, hab⟩ := hadj i' j
      exact ⟨b, hb, a, ha, hab.symm⟩
    · simp at h

end MinorModel

end Models

/-- A statement about the pairs `i < j` of `Fin 5`, from its ten instances. -/
private theorem forall_lt_fin_five {P : Fin 5 → Fin 5 → Prop} (h01 : P 0 1) (h02 : P 0 2)
    (h03 : P 0 3) (h04 : P 0 4) (h12 : P 1 2) (h13 : P 1 3) (h14 : P 1 4) (h23 : P 2 3)
    (h24 : P 2 4) (h34 : P 3 4) : ∀ i j, i < j → P i j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | exact absurd hij (by decide) | assumption

/-- A statement about the pairs `i < j` of `Fin 3`, from its three instances. -/
private theorem forall_lt_fin_three {P : Fin 3 → Fin 3 → Prop} (h01 : P 0 1) (h02 : P 0 2)
    (h12 : P 1 2) : ∀ i j, i < j → P i j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | exact absurd hij (by decide) | assumption

/-- A statement about all pairs of `Fin 3`, from its nine instances. -/
private theorem forall_fin_three {P : Fin 3 → Fin 3 → Prop} (h00 : P 0 0) (h01 : P 0 1)
    (h02 : P 0 2) (h10 : P 1 0) (h11 : P 1 1) (h12 : P 1 2) (h20 : P 2 0) (h21 : P 2 1)
    (h22 : P 2 2) : ∀ i j, P i j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals assumption

/-! ## Arcs measured from another vertex -/

section Arcs

variable [DecidableEq V] {C : List V} {a b c v : V}

/-- **Membership in an arc, measured from an earlier vertex**: if `a` comes no later than `b`
reading from `c`, the arc from `a` to `b` consists of the vertices from `a`, included, to `b`,
excluded, reading from `c`. -/
theorem mem_arc_iff_of_cycDist_le (hC : C.Nodup) (hc : c ∈ C) (ha : a ∈ C) (hb : b ∈ C)
    (h : cycDist C c a ≤ cycDist C c b) :
    v ∈ arc C a b ↔ v ∈ C ∧ cycDist C c a ≤ cycDist C c v ∧ cycDist C c v < cycDist C c b := by
  have happ := arc_append_arc hC hc ha hb h
  have hdisj := disjoint_arc_arc hC hc ha hb h
  constructor
  · intro hv
    have hv' : v ∈ arc C c b := happ ▸ List.mem_append_right _ hv
    obtain ⟨hvC, hvb⟩ := (mem_arc_iff hC).mp hv'
    refine ⟨hvC, ?_, hvb⟩
    by_contra hlt
    push Not at hlt
    exact hdisj ((mem_arc_iff hC).mpr ⟨hvC, hlt⟩) hv
  · rintro ⟨hvC, hav, hvb⟩
    have hv' : v ∈ arc C c a ++ arc C a b := happ ▸ (mem_arc_iff hC).mpr ⟨hvC, hvb⟩
    rcases List.mem_append.mp hv' with h' | h'
    · exact absurd ((mem_arc_iff hC).mp h').2 (not_lt.mpr hav)
    · exact h'

/-- **Membership in an arc, measured from its end**: the arc from `a` to `c ≠ a` consists of the
vertices that come no earlier than `a`, reading from `c`. -/
theorem mem_arc_iff_cycDist_le (hC : C.Nodup) (ha : a ∈ C) (hc : c ∈ C) (hac : a ≠ c) :
    v ∈ arc C a c ↔ v ∈ C ∧ cycDist C c a ≤ cycDist C c v := by
  have hdisj := disjoint_arc_arc_self hC hc ha hac.symm
  constructor
  · intro hv
    have hvC := mem_of_mem_arc hv
    refine ⟨hvC, ?_⟩
    by_contra hlt
    push Not at hlt
    exact hdisj ((mem_arc_iff hC).mpr ⟨hvC, hlt⟩) hv
  · rintro ⟨hvC, hav⟩
    rcases mem_arc_or_mem_arc hC hc ha hac.symm hvC with h' | h'
    · exact absurd ((mem_arc_iff hC).mp h').2 (not_lt.mpr hav)
    · exact h'

/-! ## Marks on a cyclic list -/

/-- **The interval lemma for marks on a cyclic list.**  Let `X` and `Y` be sets of at least two
marks on `C`, with at most two marks in common, and with no four distinct marks
`x₁, y₁, x₂, y₂` in this cyclic order with `x₁, x₂ ∈ X` and `y₁, y₂ ∈ Y`.  Then the marks of `Y`
all lie on the closed arc between two consecutive marks of `X`.

If some mark of `Y` is not in `X`, it lies strictly between two consecutive marks `p, q` of `X`,
and a mark of `Y` outside the closed arc from `p` to `q` would alternate with it.  Otherwise
`Y ⊆ X` has exactly two marks `a, b`; if marks of `X` lay strictly inside both arcs between `a`
and `b`, they would alternate with `a` and `b`. -/
theorem exists_isConsecutive_subset_closedArc_of_cyclic (hC : C.Nodup) {X Y : Finset V}
    (hXC : ∀ v ∈ X, v ∈ C) (hYC : ∀ v ∈ Y, v ∈ C) (hX2 : 2 ≤ X.card) (hY2 : 2 ≤ Y.card)
    (hXY : (X ∩ Y).card ≤ 2)
    (halt : ∀ x₁ ∈ X, ∀ y₁ ∈ Y, ∀ x₂ ∈ X, ∀ y₂ ∈ Y, x₁ ≠ y₁ →
      cycDist C x₁ y₁ < cycDist C x₁ x₂ → cycDist C x₁ x₂ < cycDist C x₁ y₂ → False) :
    ∃ p q, IsConsecutive C X p q ∧ ∀ v ∈ Y, v ∈ closedArc C p q := by
  by_cases hsub : Y ⊆ X
  · -- `Y` consists of two marks `a, b` of `X`.
    have hY : Y.card = 2 := le_antisymm (by rwa [Finset.inter_eq_right.mpr hsub] at hXY) hY2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hY
    have haY : a ∈ ({a, b} : Finset V) := Finset.mem_insert_self a {b}
    have hbY : b ∈ ({a, b} : Finset V) := Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    have haX := hsub haY
    have hbX := hsub hbY
    have ha := hXC a haX
    have hb := hXC b hbX
    -- Both marks lie on either closed arc between them.
    have hab' : ∀ v ∈ ({a, b} : Finset V), v ∈ closedArc C a b := by
      intro v hv
      rcases Finset.mem_insert.mp hv with h | h
      · rw [h]
        exact left_mem_closedArc hC ha
      · rw [Finset.mem_singleton.mp h]
        exact right_mem_closedArc hC hb
    have hba' : ∀ v ∈ ({a, b} : Finset V), v ∈ closedArc C b a := by
      intro v hv
      rcases Finset.mem_insert.mp hv with h | h
      · rw [h]
        exact right_mem_closedArc hC ha
      · rw [Finset.mem_singleton.mp h]
        exact left_mem_closedArc hC hb
    by_cases h1 : ∀ r ∈ X, r ∈ arc C a b → r = a
    · exact ⟨a, b, ⟨haX, hbX, hab, h1⟩, hab'⟩
    by_cases h2 : ∀ r ∈ X, r ∈ arc C b a → r = b
    · exact ⟨b, a, ⟨hbX, haX, hab.symm, h2⟩, hba'⟩
    -- Otherwise marks `c` and `d` of `X` lie strictly inside the two arcs, and `c, b, d, a`
    -- alternate.
    push Not at h1 h2
    obtain ⟨c, hcX, hc, hca⟩ := h1
    obtain ⟨d, hdX, hd, hdb⟩ := h2
    exfalso
    have hcC := hXC c hcX
    have hdC := hXC d hdX
    have hcb := ((mem_arc_iff hC).mp hc).2
    have hc0 := cycDist_pos hC ha hcC (Ne.symm hca)
    have hbd : cycDist C a b < cycDist C a d := by
      have hnot : d ∉ arc C a b := fun h => disjoint_arc_arc_self hC ha hb hab h hd
      rcases lt_or_eq_of_le (not_lt.mp fun h => hnot ((mem_arc_iff hC).mpr ⟨hdC, h⟩)) with h | h
      · exact h
      · exact absurd (eq_of_cycDist_eq hb hdC h).symm hdb
    have hdn := cycDist_lt_length (a := a) hdC
    have e1 := cycDist_add_cycDist hC ha hcC hb hcb.le
    have e2 := cycDist_add_cycDist hC ha hcC hdC (by omega)
    have e3 := cycDist_add_cycDist_comm hC ha hcC (Ne.symm hca)
    exact halt c hcX b hbY d hdX a haY (fun h => right_not_mem_arc hC (h ▸ hc)) (by omega)
      (by omega)
  · -- A mark `y'` of `Y` outside `X` lies strictly between consecutive marks `p, q` of `X`.
    obtain ⟨y', hy'Y, hy'X⟩ := Finset.not_subset.mp hsub
    obtain ⟨p, q, hpq, hy'⟩ := exists_isConsecutive_mem_arc hC hXC (by omega) (hYC y' hy'Y)
    refine ⟨p, q, hpq, fun v hv => ?_⟩
    by_contra hvpq
    have hvC := hYC v hv
    have hfar : cycDist C p q < cycDist C p v := by
      by_contra hle
      exact hvpq ((mem_closedArc_iff hC).mpr ⟨hvC, not_lt.mp hle⟩)
    exact halt p hpq.1 y' hy'Y q hpq.2.1 v hv (fun h => hy'X (h ▸ hpq.1))
      ((mem_arc_iff hC).mp hy').2 hfar

end Arcs

/-! ## The obstruction models -/

section Obstructions

variable {G : SimpleGraph V} {C : List V} {x y : V}

/-- A vertex off the cycle is disjoint from every arc. -/
private theorem disjoint_singleton_arc [DecidableEq V] (hx : x ∉ C) (a b : V) :
    Disjoint ({x} : Set V) {z | z ∈ arc C a b} :=
  Set.disjoint_singleton_left.mpr fun h => hx (mem_of_mem_arc h)

/-- Arcs with no common vertex are disjoint sets. -/
private theorem disjoint_setOf_arc [DecidableEq V] {a b c d : V}
    (h : ∀ z, z ∈ arc C a b → z ∈ arc C c d → False) :
    Disjoint {z | z ∈ arc C a b} {z | z ∈ arc C c d} :=
  Set.disjoint_left.mpr fun z h₁ h₂ => h z h₁ h₂

/-- **The `K₅` model of three common attachments.**  If `x` and `y` are adjacent, lie off the
cycle `C`, and are both adjacent to three vertices `u, v, w` of `C` in this cyclic order, then the
branch sets `{x}`, `{y}` and the arcs from `u` to `v`, from `v` to `w` and from `w` to `u` form a
`K₅` model. -/
def MinorModel.ofThreeCommon [DecidableEq V] (hxy : G.Adj x y)
    (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {u v w : V} (hu : u ∈ C) (hv : v ∈ C)
    (hw : w ∈ C) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (horder : cycDist C u v < cycDist C u w) (hxu : G.Adj x u) (hxv : G.Adj x v)
    (hxw : G.Adj x w) (hyu : G.Adj y u) (hyv : G.Adj y v) (hyw : G.Adj y w) :
    MinorModel (⊤ : SimpleGraph (Fin 5)) G := by
  have hCn := hC.1
  -- Membership in the three arcs, read from `u`.
  have m₁ : ∀ z, z ∈ arc C u v → cycDist C u z < cycDist C u v :=
    fun z h => ((mem_arc_iff hCn).mp h).2
  have m₂ : ∀ z, z ∈ arc C v w → cycDist C u v ≤ cycDist C u z ∧ cycDist C u z < cycDist C u w :=
    fun z h => ((mem_arc_iff_of_cycDist_le hCn hu hv hw horder.le).mp h).2
  have m₃ : ∀ z, z ∈ arc C w u → cycDist C u w ≤ cycDist C u z :=
    fun z h => ((mem_arc_iff_cycDist_le hCn hw hu huw.symm).mp h).2
  have hu' := left_mem_arc hCn hu hv huv
  have hv' := left_mem_arc hCn hv hw hvw
  have hw' := left_mem_arc hCn hw hu huw.symm
  refine MinorModel.ofPairwise
    ![{x}, {y}, {z | z ∈ arc C u v}, {z | z ∈ arc C v w}, {z | z ∈ arc C w u}] ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact isConnectedSet_singleton G x
    · exact isConnectedSet_singleton G y
    · exact hC.isConnectedSet_arc hu hv huv
    · exact hC.isConnectedSet_arc hv hw hvw
    · exact hC.isConnectedSet_arc hw hu huw.symm
  · refine forall_lt_fin_five ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Set.disjoint_singleton.mpr hxy.ne
    · exact disjoint_singleton_arc hx u v
    · exact disjoint_singleton_arc hx v w
    · exact disjoint_singleton_arc hx w u
    · exact disjoint_singleton_arc hy u v
    · exact disjoint_singleton_arc hy v w
    · exact disjoint_singleton_arc hy w u
    · exact disjoint_setOf_arc fun z h h' => by have := m₁ z h; have := m₂ z h'; omega
    · exact disjoint_setOf_arc fun z h h' => by have := m₁ z h; have := m₃ z h'; omega
    · exact disjoint_setOf_arc fun z h h' => by have := m₂ z h; have := m₃ z h'; omega
  · obtain ⟨a₁, ha₁, ha₁v⟩ := hC.exists_mem_arc_adj hu hv huv
    obtain ⟨a₂, ha₂, ha₂w⟩ := hC.exists_mem_arc_adj hv hw hvw
    obtain ⟨a₃, ha₃, ha₃u⟩ := hC.exists_mem_arc_adj hw hu huw.symm
    refine forall_lt_fin_five ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact ⟨x, rfl, y, rfl, hxy⟩
    · exact ⟨x, rfl, u, hu', hxu⟩
    · exact ⟨x, rfl, v, hv', hxv⟩
    · exact ⟨x, rfl, w, hw', hxw⟩
    · exact ⟨y, rfl, u, hu', hyu⟩
    · exact ⟨y, rfl, v, hv', hyv⟩
    · exact ⟨y, rfl, w, hw', hyw⟩
    · exact ⟨a₁, ha₁, v, hv', ha₁v⟩
    · exact ⟨u, hu', a₃, ha₃, ha₃u.symm⟩
    · exact ⟨a₂, ha₂, w, hw', ha₂w⟩

/-- **Three common attachments give a `K₅` minor.**  If `x` and `y` are adjacent, lie off the
cycle `C`, and are both adjacent to three vertices `u, v, w` of `C` in this cyclic order, then
`K₅` is a minor of `G`, with branch sets `{x}`, `{y}` and the arcs from `u` to `v`, from `v` to `w`
and from `w` to `u` (`MinorModel.ofThreeCommon`). -/
theorem isMinor_top_five_of_three_common [DecidableEq V] (hxy : G.Adj x y)
    (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {u v w : V} (hu : u ∈ C) (hv : v ∈ C)
    (hw : w ∈ C) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (horder : cycDist C u v < cycDist C u w) (hxu : G.Adj x u) (hxv : G.Adj x v)
    (hxw : G.Adj x w) (hyu : G.Adj y u) (hyv : G.Adj y v) (hyw : G.Adj y w) :
    IsMinor (⊤ : SimpleGraph (Fin 5)) G :=
  ⟨.ofThreeCommon hxy hC hx hy hu hv hw huv hvw huw horder hxu hxv hxw hyu hyv hyw⟩

/-- **Three common attachments give a `K₅` minor**, in any order along the cycle: if `x` and `y`
are adjacent, lie off the cycle `C`, and are both adjacent to three distinct vertices of `C`, then
`K₅` is a minor of `G`. -/
theorem isMinor_top_five_of_three_common' (hxy : G.Adj x y) (hC : IsCycleList G C) (hx : x ∉ C)
    (hy : y ∉ C) {u v w : V} (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C) (huv : u ≠ v) (hvw : v ≠ w)
    (huw : u ≠ w) (hxu : G.Adj x u) (hxv : G.Adj x v) (hxw : G.Adj x w) (hyu : G.Adj y u)
    (hyv : G.Adj y v) (hyw : G.Adj y w) : IsMinor (⊤ : SimpleGraph (Fin 5)) G := by
  classical
  rcases lt_or_gt_of_ne (fun h => hvw (eq_of_cycDist_eq hv hw h) :
      cycDist C u v ≠ cycDist C u w) with h | h
  · exact isMinor_top_five_of_three_common hxy hC hx hy hu hv hw huv hvw huw h hxu hxv hxw hyu
      hyv hyw
  · exact isMinor_top_five_of_three_common hxy hC hx hy hu hw hv huw hvw.symm huv h hxu hxw hxv
      hyu hyw hyv

/-- **The `K₃,₃` model of four alternating attachments.**  If `x` and `y` are adjacent and lie off
the cycle `C`, `x` is adjacent to `x₁, x₂` on `C` and `y` to `y₁, y₂` on `C`, and these are
distinct and in the cyclic order `x₁, y₁, x₂, y₂`, then the branch sets `{x}`, `arc C y₁ x₂`,
`arc C y₂ x₁` on the left and `{y}`, `arc C x₁ y₁`, `arc C x₂ y₂` on the right form a `K₃,₃`
model.  Distinctness follows from the order once `x₁ ≠ y₁`. -/
def MinorModel.ofAlternating [DecidableEq V] (hxy : G.Adj x y)
    (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {x₁ y₁ x₂ y₂ : V} (hx₁C : x₁ ∈ C)
    (hy₁C : y₁ ∈ C) (hx₂C : x₂ ∈ C) (hy₂C : y₂ ∈ C) (hne : x₁ ≠ y₁)
    (horder : cycDist C x₁ y₁ < cycDist C x₁ x₂ ∧ cycDist C x₁ x₂ < cycDist C x₁ y₂)
    (hx₁ : G.Adj x x₁) (hx₂ : G.Adj x x₂) (hy₁ : G.Adj y y₁) (hy₂ : G.Adj y y₂) :
    MinorModel (completeBipartiteGraph (Fin 3) (Fin 3)) G := by
  have hCn := hC.1
  obtain ⟨h₁, h₂⟩ := horder
  have hy₁x₂ : y₁ ≠ x₂ := fun h => by rw [h] at h₁; omega
  have hx₂y₂ : x₂ ≠ y₂ := fun h => by rw [h] at h₂; omega
  have hy₂x₁ : y₂ ≠ x₁ := fun h => by rw [h, cycDist_self hCn hx₁C] at h₂; omega
  -- Membership in the four arcs, read from `x₁`.
  have m₁ : ∀ z, z ∈ arc C x₁ y₁ → cycDist C x₁ z < cycDist C x₁ y₁ :=
    fun z h => ((mem_arc_iff hCn).mp h).2
  have m₂ : ∀ z, z ∈ arc C y₁ x₂ →
      cycDist C x₁ y₁ ≤ cycDist C x₁ z ∧ cycDist C x₁ z < cycDist C x₁ x₂ :=
    fun z h => ((mem_arc_iff_of_cycDist_le hCn hx₁C hy₁C hx₂C h₁.le).mp h).2
  have m₃ : ∀ z, z ∈ arc C x₂ y₂ →
      cycDist C x₁ x₂ ≤ cycDist C x₁ z ∧ cycDist C x₁ z < cycDist C x₁ y₂ :=
    fun z h => ((mem_arc_iff_of_cycDist_le hCn hx₁C hx₂C hy₂C h₂.le).mp h).2
  have m₄ : ∀ z, z ∈ arc C y₂ x₁ → cycDist C x₁ y₂ ≤ cycDist C x₁ z :=
    fun z h => ((mem_arc_iff_cycDist_le hCn hy₂C hx₁C hy₂x₁).mp h).2
  have hx₁' := left_mem_arc hCn hx₁C hy₁C hne
  have hy₁' := left_mem_arc hCn hy₁C hx₂C hy₁x₂
  have hx₂' := left_mem_arc hCn hx₂C hy₂C hx₂y₂
  have hy₂' := left_mem_arc hCn hy₂C hx₁C hy₂x₁
  refine MinorModel.ofBipartite ![{x}, {z | z ∈ arc C y₁ x₂}, {z | z ∈ arc C y₂ x₁}]
    ![{y}, {z | z ∈ arc C x₁ y₁}, {z | z ∈ arc C x₂ y₂}] ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact isConnectedSet_singleton G x
    · exact hC.isConnectedSet_arc hy₁C hx₂C hy₁x₂
    · exact hC.isConnectedSet_arc hy₂C hx₁C hy₂x₁
  · intro j
    fin_cases j
    · exact isConnectedSet_singleton G y
    · exact hC.isConnectedSet_arc hx₁C hy₁C hne
    · exact hC.isConnectedSet_arc hx₂C hy₂C hx₂y₂
  · refine forall_lt_fin_three ?_ ?_ ?_
    · exact disjoint_singleton_arc hx y₁ x₂
    · exact disjoint_singleton_arc hx y₂ x₁
    · exact disjoint_setOf_arc fun z h h' => by have := m₂ z h; have := m₄ z h'; omega
  · refine forall_lt_fin_three ?_ ?_ ?_
    · exact disjoint_singleton_arc hy x₁ y₁
    · exact disjoint_singleton_arc hy x₂ y₂
    · exact disjoint_setOf_arc fun z h h' => by have := m₁ z h; have := m₃ z h'; omega
  · refine forall_fin_three ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Set.disjoint_singleton.mpr hxy.ne
    · exact disjoint_singleton_arc hx x₁ y₁
    · exact disjoint_singleton_arc hx x₂ y₂
    · exact (disjoint_singleton_arc hy y₁ x₂).symm
    · exact disjoint_setOf_arc fun z h h' => by have := m₂ z h; have := m₁ z h'; omega
    · exact disjoint_setOf_arc fun z h h' => by have := m₂ z h; have := m₃ z h'; omega
    · exact (disjoint_singleton_arc hy y₂ x₁).symm
    · exact disjoint_setOf_arc fun z h h' => by have := m₄ z h; have := m₁ z h'; omega
    · exact disjoint_setOf_arc fun z h h' => by have := m₄ z h; have := m₃ z h'; omega
  · obtain ⟨a₁, ha₁, ha₁y₁⟩ := hC.exists_mem_arc_adj hx₁C hy₁C hne
    obtain ⟨a₂, ha₂, ha₂x₂⟩ := hC.exists_mem_arc_adj hy₁C hx₂C hy₁x₂
    obtain ⟨a₃, ha₃, ha₃y₂⟩ := hC.exists_mem_arc_adj hx₂C hy₂C hx₂y₂
    obtain ⟨a₄, ha₄, ha₄x₁⟩ := hC.exists_mem_arc_adj hy₂C hx₁C hy₂x₁
    refine forall_fin_three ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact ⟨x, rfl, y, rfl, hxy⟩
    · exact ⟨x, rfl, x₁, hx₁', hx₁⟩
    · exact ⟨x, rfl, x₂, hx₂', hx₂⟩
    · exact ⟨y₁, hy₁', y, rfl, hy₁.symm⟩
    · exact ⟨y₁, hy₁', a₁, ha₁, ha₁y₁.symm⟩
    · exact ⟨a₂, ha₂, x₂, hx₂', ha₂x₂⟩
    · exact ⟨y₂, hy₂', y, rfl, hy₂.symm⟩
    · exact ⟨a₄, ha₄, x₁, hx₁', ha₄x₁⟩
    · exact ⟨y₂, hy₂', a₃, ha₃, ha₃y₂.symm⟩

/-- **Four alternating attachments give a `K₃,₃` minor.**  If `x` and `y` are adjacent and lie off
the cycle `C`, `x` is adjacent to `x₁, x₂` on `C` and `y` to `y₁, y₂` on `C`, and these are
distinct and in the cyclic order `x₁, y₁, x₂, y₂`, then `K₃,₃` is a minor of `G`.  The branch sets
are `{x}`, `arc C y₁ x₂`, `arc C y₂ x₁` on the left and `{y}`, `arc C x₁ y₁`, `arc C x₂ y₂` on the
right (`MinorModel.ofAlternating`).  Distinctness follows from the order once `x₁ ≠ y₁`. -/
theorem isMinor_completeBipartite_of_alternating [DecidableEq V] (hxy : G.Adj x y)
    (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {x₁ y₁ x₂ y₂ : V} (hx₁C : x₁ ∈ C)
    (hy₁C : y₁ ∈ C) (hx₂C : x₂ ∈ C) (hy₂C : y₂ ∈ C) (hne : x₁ ≠ y₁)
    (horder : cycDist C x₁ y₁ < cycDist C x₁ x₂ ∧ cycDist C x₁ x₂ < cycDist C x₁ y₂)
    (hx₁ : G.Adj x x₁) (hx₂ : G.Adj x x₂) (hy₁ : G.Adj y y₁) (hy₂ : G.Adj y y₂) :
    IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G :=
  ⟨.ofAlternating hxy hC hx hy hx₁C hy₁C hx₂C hy₂C hne horder hx₁ hx₂ hy₁ hy₂⟩

/-- **The interval lemma.**  Let `xy` be an edge of a graph with neither `K₅` nor `K₃,₃` as a
minor, and `C` a cycle avoiding `x` and `y`.  If `x` has the set `X` of at least two neighbours on
`C`, and `y` the set `Y` of at least two, then `Y` lies on the closed arc between two consecutive
vertices of `X`.  Three common neighbours on `C` would give `K₅`, and four alternating ones
`K₃,₃`. -/
theorem exists_isConsecutive_subset_closedArc [DecidableEq V] (hG : NoKuratowskiMinor G)
    (hxy : G.Adj x y) (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {X Y : Finset V}
    (hX : ∀ v, v ∈ X ↔ v ∈ C ∧ G.Adj x v) (hY : ∀ v, v ∈ Y ↔ v ∈ C ∧ G.Adj y v)
    (hX2 : 2 ≤ X.card) (hY2 : 2 ≤ Y.card) :
    ∃ p q, IsConsecutive C X p q ∧ ∀ v ∈ Y, v ∈ closedArc C p q := by
  refine exists_isConsecutive_subset_closedArc_of_cyclic hC.1 (fun v hv => ((hX v).mp hv).1)
    (fun v hv => ((hY v).mp hv).1) hX2 hY2 ?_ ?_
  · by_contra h
    push Not at h
    obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ := Finset.two_lt_card.mp h
    rw [Finset.mem_inter, hX, hY] at hu hv hw
    exact hG.1 (isMinor_top_five_of_three_common' hxy hC hx hy hu.1.1 hv.1.1 hw.1.1 huv hvw huw
      hu.1.2 hv.1.2 hw.1.2 hu.2.2 hv.2.2 hw.2.2)
  · intro x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ hne h₁ h₂
    rw [hX] at hx₁ hx₂
    rw [hY] at hy₁ hy₂
    exact hG.2 (isMinor_completeBipartite_of_alternating hxy hC hx hy hx₁.1 hy₁.1 hx₂.1 hy₂.1 hne
      ⟨h₁, h₂⟩ hx₁.2 hx₂.2 hy₁.2 hy₂.2)

end Obstructions

end MonoidProduct.Graph
