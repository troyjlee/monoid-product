import MonoidProduct.Graph.WagnerObstructions
set_option linter.style.header false

/-!
# Acceptance statements for obstructions on a cycle

The statements of `Graph/WagnerObstructions.lean`, restated with the definitions unfolded where
that makes their meaning visible, followed by small sanity checks.  Lean checks every `example`
here against the library's statement.

* The `K₅` model of three common attachments, with its branch sets, and the resulting minor, for
  attachments in cyclic order and in any order.
* The `K₃,₃` model of four alternating attachments, with its branch sets, and the resulting minor.
* The interval lemma, for an edge of a graph with neither excluded minor, and for marks on a cyclic
  list.

The sanity checks cover:
* `K₅` as the edge `01` attached at all three vertices of a triangle, and `K₃,₃` as the edge from
  `inl 0` to `inr 0` attached at alternating vertices of a square;
* marks on the hexagon `[0, 1, 2, 3, 4, 5]` where the interval lemma for cyclic lists applies:
  `|X| = 2` with `Y` inside one of the two arcs, `Y = X` with two marks, `Y ⊆ X` with three marks
  of `X`, an overlap at one end of the interval, and an interval across the end of the list;
* configurations where no interval contains `Y`: three common marks, and four alternating marks.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-! ## Statements -/

section Statements

variable {V : Type*} {G : SimpleGraph V} {C : List V} {x y : V}

/-- **Three common attachments in any order give `K₅`.** -/
example (hxy : G.Adj x y) (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {u v w : V}
    (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hxu : G.Adj x u) (hxv : G.Adj x v) (hxw : G.Adj x w) (hyu : G.Adj y u) (hyv : G.Adj y v)
    (hyw : G.Adj y w) : IsMinor (⊤ : SimpleGraph (Fin 5)) G :=
  isMinor_top_five_of_three_common' hxy hC hx hy hu hv hw huv hvw huw hxu hxv hxw hyu hyv hyw

variable [DecidableEq V]

/-- **The `K₅` model of three common attachments** `u, v, w` in cyclic order: its branch sets are
`{x}`, `{y}` and the arcs from `u` to `v`, from `v` to `w` and from `w` to `u`. -/
example (hxy : G.Adj x y) (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {u v w : V}
    (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (horder : cycDist C u v < cycDist C u w) (hxu : G.Adj x u) (hxv : G.Adj x v)
    (hxw : G.Adj x w) (hyu : G.Adj y u) (hyv : G.Adj y v) (hyw : G.Adj y w) :
    ∃ m : MinorModel (⊤ : SimpleGraph (Fin 5)) G,
      m.branch = ![{x}, {y}, {z | z ∈ arc C u v}, {z | z ∈ arc C v w}, {z | z ∈ arc C w u}] :=
  ⟨.ofThreeCommon hxy hC hx hy hu hv hw huv hvw huw horder hxu hxv hxw hyu hyv hyw, rfl⟩

/-- **Three common attachments in cyclic order give `K₅`.** -/
example (hxy : G.Adj x y) (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {u v w : V}
    (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (horder : cycDist C u v < cycDist C u w) (hxu : G.Adj x u) (hxv : G.Adj x v)
    (hxw : G.Adj x w) (hyu : G.Adj y u) (hyv : G.Adj y v) (hyw : G.Adj y w) :
    IsMinor (⊤ : SimpleGraph (Fin 5)) G :=
  isMinor_top_five_of_three_common hxy hC hx hy hu hv hw huv hvw huw horder hxu hxv hxw hyu hyv hyw

/-- **The `K₃,₃` model of four alternating attachments** `x₁, y₁, x₂, y₂`: its branch sets are
`{x}`, `arc C y₁ x₂`, `arc C y₂ x₁` on the left and `{y}`, `arc C x₁ y₁`, `arc C x₂ y₂` on the
right. -/
example (hxy : G.Adj x y) (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {x₁ y₁ x₂ y₂ : V}
    (hx₁C : x₁ ∈ C) (hy₁C : y₁ ∈ C) (hx₂C : x₂ ∈ C) (hy₂C : y₂ ∈ C) (hne : x₁ ≠ y₁)
    (horder : cycDist C x₁ y₁ < cycDist C x₁ x₂ ∧ cycDist C x₁ x₂ < cycDist C x₁ y₂)
    (hx₁ : G.Adj x x₁) (hx₂ : G.Adj x x₂) (hy₁ : G.Adj y y₁) (hy₂ : G.Adj y y₂) :
    ∃ m : MinorModel (completeBipartiteGraph (Fin 3) (Fin 3)) G,
      m.branch = Sum.elim ![{x}, {z | z ∈ arc C y₁ x₂}, {z | z ∈ arc C y₂ x₁}]
        ![{y}, {z | z ∈ arc C x₁ y₁}, {z | z ∈ arc C x₂ y₂}] :=
  ⟨.ofAlternating hxy hC hx hy hx₁C hy₁C hx₂C hy₂C hne horder hx₁ hx₂ hy₁ hy₂, rfl⟩

/-- **Four alternating attachments give `K₃,₃`.** -/
example (hxy : G.Adj x y) (hC : IsCycleList G C) (hx : x ∉ C) (hy : y ∉ C) {x₁ y₁ x₂ y₂ : V}
    (hx₁C : x₁ ∈ C) (hy₁C : y₁ ∈ C) (hx₂C : x₂ ∈ C) (hy₂C : y₂ ∈ C) (hne : x₁ ≠ y₁)
    (horder : cycDist C x₁ y₁ < cycDist C x₁ x₂ ∧ cycDist C x₁ x₂ < cycDist C x₁ y₂)
    (hx₁ : G.Adj x x₁) (hx₂ : G.Adj x x₂) (hy₁ : G.Adj y y₁) (hy₂ : G.Adj y y₂) :
    IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G :=
  isMinor_completeBipartite_of_alternating hxy hC hx hy hx₁C hy₁C hx₂C hy₂C hne horder hx₁ hx₂ hy₁
    hy₂

/-- **The interval lemma**, with consecutive marks unfolded: the neighbours of `y` on `C` lie on
the closed arc between distinct neighbours `p, q` of `x` on `C`, with no neighbour of `x` strictly
between them. -/
example (hG : NoKuratowskiMinor G) (hxy : G.Adj x y) (hC : IsCycleList G C) (hx : x ∉ C)
    (hy : y ∉ C) {X Y : Finset V} (hX : ∀ v, v ∈ X ↔ v ∈ C ∧ G.Adj x v)
    (hY : ∀ v, v ∈ Y ↔ v ∈ C ∧ G.Adj y v) (hX2 : 2 ≤ X.card) (hY2 : 2 ≤ Y.card) :
    ∃ p q, (p ∈ X ∧ q ∈ X ∧ p ≠ q ∧ ∀ r ∈ X, r ∈ arc C p q → r = p) ∧
      ∀ v ∈ Y, v ∈ closedArc C p q :=
  exists_isConsecutive_subset_closedArc hG hxy hC hx hy hX hY hX2 hY2

/-- **The interval lemma for marks on a cyclic list**: at most two common marks, and no four
distinct marks alternating between `X` and `Y`. -/
example (hC : C.Nodup) {X Y : Finset V} (hXC : ∀ v ∈ X, v ∈ C) (hYC : ∀ v ∈ Y, v ∈ C)
    (hX2 : 2 ≤ X.card) (hY2 : 2 ≤ Y.card) (hXY : (X ∩ Y).card ≤ 2)
    (halt : ∀ x₁ ∈ X, ∀ y₁ ∈ Y, ∀ x₂ ∈ X, ∀ y₂ ∈ Y, x₁ ≠ y₁ →
      cycDist C x₁ y₁ < cycDist C x₁ x₂ → cycDist C x₁ x₂ < cycDist C x₁ y₂ → False) :
    ∃ p q, IsConsecutive C X p q ∧ ∀ v ∈ Y, v ∈ closedArc C p q :=
  exists_isConsecutive_subset_closedArc_of_cyclic hC hXC hYC hX2 hY2 hXY halt

end Statements

/-! ## Sanity checks: the obstruction models -/

/-- **`K₅` from a triangle**: in `K₅`, the edge `01` is attached at all three vertices of the
triangle `[2, 3, 4]`; the arcs between the attachments are single vertices. -/
example : arc [2, 3, 4] (2 : Fin 5) 3 = [2] ∧ arc [2, 3, 4] (3 : Fin 5) 4 = [3] ∧
    arc [2, 3, 4] (4 : Fin 5) 2 = [4] ∧
    IsMinor (⊤ : SimpleGraph (Fin 5)) (⊤ : SimpleGraph (Fin 5)) := by
  have hC : IsCycleList (⊤ : SimpleGraph (Fin 5)) [2, 3, 4] := by
    unfold IsCycleList
    decide
  exact ⟨by decide, by decide, by decide,
    isMinor_top_five_of_three_common (x := 0) (y := 1) (u := 2) (v := 3) (w := 4) (by decide) hC
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)⟩

/-- **`K₃,₃` from a square**: in `K₃,₃`, the edge from `inl 0` to `inr 0` is attached to the square
`[inl 1, inr 1, inl 2, inr 2]`, `inl 0` at `inr 1, inr 2` and `inr 0` at `inl 1, inl 2`; these
alternate along the square. -/
example :
    IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  have hC : IsCycleList (completeBipartiteGraph (Fin 3) (Fin 3))
      [.inl 1, .inr 1, .inl 2, .inr 2] := by
    unfold IsCycleList
    simp only [completeBipartiteGraph_adj]
    decide
  exact isMinor_completeBipartite_of_alternating (x := .inl 0) (y := .inr 0) (x₁ := .inr 1)
    (y₁ := .inl 2) (x₂ := .inr 2) (y₂ := .inl 1) (by simp) hC (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp) (by simp)
    (by simp)

/-! ## Sanity checks: intervals on a hexagon -/

/-- **Two marks of `X`**: they cut the hexagon into two arcs, and `Y = {1, 2}` lies on the closed
arc from `0` to `3`; the interval lemma for cyclic lists applies. -/
example : (IsConsecutive [0, 1, 2, 3, 4, 5] {0, 3} 0 3 ∧
      ∀ v ∈ ({1, 2} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] 0 3) ∧
    ∃ p q, IsConsecutive [0, 1, 2, 3, 4, 5] {0, 3} p q ∧
      ∀ v ∈ ({1, 2} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] p q := by
  refine ⟨by unfold IsConsecutive; decide, ?_⟩
  exact exists_isConsecutive_subset_closedArc_of_cyclic (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- **`Y = X` with two marks**: the interval is `X` itself, with `Y` at both ends. -/
example : IsConsecutive [0, 1, 2, 3, 4, 5] {0, 3} 0 3 ∧
    ∀ v ∈ ({0, 3} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] 0 3 := by
  unfold IsConsecutive
  decide

/-- **`Y ⊆ X` with three marks of `X`**: `Y = {3, 5}` is a consecutive pair of `X = {1, 3, 5}`;
the interval lemma for cyclic lists applies. -/
example : (IsConsecutive [0, 1, 2, 3, 4, 5] {1, 3, 5} 3 5 ∧
      ∀ v ∈ ({3, 5} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] 3 5) ∧
    ∃ p q, IsConsecutive [0, 1, 2, 3, 4, 5] {1, 3, 5} p q ∧
      ∀ v ∈ ({3, 5} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] p q := by
  refine ⟨by unfold IsConsecutive; decide, ?_⟩
  exact exists_isConsecutive_subset_closedArc_of_cyclic (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- **An overlap at one end**: `Y = {3, 4}` meets `X = {1, 3, 5}` at the start of the interval from
`3` to `5`. -/
example : IsConsecutive [0, 1, 2, 3, 4, 5] {1, 3, 5} 3 5 ∧
    ∀ v ∈ ({3, 4} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] 3 5 := by
  unfold IsConsecutive
  decide

/-- **An interval across the end of the list**: `Y = {5, 0}` lies on the closed arc
`[4, 5, 0, 1]` between the consecutive marks `4` and `1` of `X = {1, 4}`. -/
example : closedArc [0, 1, 2, 3, 4, 5] 4 1 = [4, 5, 0, 1] ∧
    IsConsecutive [0, 1, 2, 3, 4, 5] {1, 4} 4 1 ∧
    ∀ v ∈ ({5, 0} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] 4 1 := by
  unfold IsConsecutive
  decide

/-- **Three common marks**: for `X = Y = {0, 2, 4}`, no closed arc between consecutive marks of
`X` contains `Y`, although the closed arc from `0` to `4`, across the mark `2`, does. -/
example : ({0, 2, 4} ∩ {0, 2, 4} : Finset ℕ).card = 3 ∧
    (∀ p ∈ ({0, 2, 4} : Finset ℕ), ∀ q ∈ ({0, 2, 4} : Finset ℕ),
      IsConsecutive [0, 1, 2, 3, 4, 5] {0, 2, 4} p q →
        ¬ ∀ v ∈ ({0, 2, 4} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] p q) ∧
    ∀ v ∈ ({0, 2, 4} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] 0 4 := by
  unfold IsConsecutive
  decide

/-- **Four alternating marks**: `0, 1, 3, 4` alternate between `X = {0, 3}` and `Y = {1, 4}`, and
neither closed arc between the two marks of `X` contains `Y`. -/
example : (cycDist [0, 1, 2, 3, 4, 5] 0 1 < cycDist [0, 1, 2, 3, 4, 5] 0 3 ∧
      cycDist [0, 1, 2, 3, 4, 5] 0 3 < cycDist [0, 1, 2, 3, 4, 5] 0 4) ∧
    ∀ p ∈ ({0, 3} : Finset ℕ), ∀ q ∈ ({0, 3} : Finset ℕ),
      IsConsecutive [0, 1, 2, 3, 4, 5] {0, 3} p q →
        ¬ ∀ v ∈ ({1, 4} : Finset ℕ), v ∈ closedArc [0, 1, 2, 3, 4, 5] p q := by
  unfold IsConsecutive
  decide

end MonoidProduct.Graph
