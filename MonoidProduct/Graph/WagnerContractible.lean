import MonoidProduct.Graph.MinorContraction
import MonoidProduct.Graph.WagnerConnectivity
set_option linter.style.header false

/-!
# A contractible edge in a `3`-connected graph

Every `3`-connected graph on at least five vertices has an edge whose contraction is again
`3`-connected (Thomassen; Diestel, *Graph Theory*, Section 3.2).  The contraction is
`contractEdge G x y` (`Graph/Minor.lean`) on the vertices other than `y`, in which `x` also takes
the neighbours of `y`, so that common neighbours of `x` and `y` give a single edge.

* `contractEdgeInduceIso`: **away from the merged vertex `x`, the contraction is `G`**: an induced
  subgraph of the contraction avoiding `x` is the graph induced by `G` on the same vertices.
  `connected_induce_contractEdge`: deleting vertices other than `x` from the contraction keeps
  it connected when deleting them from `G` does.
* `isKConnected_contractEdge`: **contracting an edge of a `(k + 1)`-connected graph leaves a
  `k`-connected graph**; contracting any edge of a `3`-connected graph leaves a `2`-connected
  graph.
* `isKConnected_contractEdge_three_iff`: for a `3`-connected graph on at least five vertices,
  **contracting the edge `xy` keeps `3`-connectivity exactly when no third vertex `z` makes
  `{x, y, z}` a separator**; `exists_separating_triple` is the direction used below.
* `setOf_reachable_subset`: **component containment**: a component of `G - S` that avoids `T` and
  meets a component of `G - T` lies inside it.  `exists_ncard_setOf_reachable_lt`: **a strictly
  smaller component**: if `xy` is an edge, `v` lies in a component `C` of `G - {x, y, z}`, and
  `{z, v, w}` is a separator, then some component of `G - {z, v, w}` has fewer vertices than `C`.
* `exists_contractEdge_isKConnected_three`: **every `3`-connected graph on at least five vertices
  has an edge with a `3`-connected contraction.**  Otherwise every edge lies in a separating
  triple; a triple `{x, y, z}` with `xy` an edge and a component `C` of `G - {x, y, z}` of least
  size give a neighbour `v ∈ C` of `z`, the edge `zv` lies in a separating triple `{z, v, w}`, and
  `G - {z, v, w}` has a smaller component.
-/

namespace MonoidProduct.Graph

open SimpleGraph

section Contraction

variable {V : Type*} {G : SimpleGraph V}

/-- Removing one vertex from a finite type. -/
private theorem natCard_ne_add_one [Finite V] (y : V) : Nat.card {v // v ≠ y} + 1 = Nat.card V := by
  have h := Set.ncard_add_ncard_compl ({y} : Set V)
  rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at h
  rw [← h, add_comm]
  rfl

/-- A finite type with more than three elements has an element outside any three. -/
private theorem exists_ne_of_three_lt [Finite V] (h : 3 < Nat.card V) (x y z : V) :
    ∃ c, c ≠ x ∧ c ≠ y ∧ c ≠ z := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {x, y, z})
    (t := Finset.univ) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      have := Finset.card_le_three (a := x) (b := y) (c := z)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc⟩

/-- A disconnected induced graph has a vertex unreachable from any given vertex. -/
private theorem exists_not_reachable {s : Set V} {a : V} (ha : a ∈ s)
    (h : ¬ (G.induce s).Connected) : ∃ b ∈ s, ¬ (restrictTo G s).Reachable a b := by
  by_contra hall
  push Not at hall
  refine h ((connected_iff _).mpr ⟨fun p q => ?_, ⟨⟨a, ha⟩⟩⟩)
  rw [reachable_induce_iff_restrictTo]
  exact (hall p.1 p.2).symm.trans (hall q.1 q.2)

/-- The neighbour property for a separating triple of a `3`-connected graph: each vertex of the
triple has a neighbour in every component of the rest. -/
private theorem exists_adj_reachable_triple (hG : IsKConnected G 3) {x y z s c : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hs : s = x ∨ s = y ∨ s = z)
    (hc : c ∈ {u | u ≠ x ∧ u ≠ y ∧ u ≠ z}) :
    ∃ d ∈ {u | u ≠ x ∧ u ≠ y ∧ u ≠ z},
      (restrictTo G {u | u ≠ x ∧ u ≠ y ∧ u ≠ z}).Reachable c d ∧ G.Adj s d := by
  classical
  have hcard : ({x, y, z} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hset : {u | u ∉ ({x, y, z} : Finset V)} = {u | u ≠ x ∧ u ≠ y ∧ u ≠ z} := by
    ext u
    simp only [Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton, not_or]
  obtain ⟨d, hd, hcd, hsd⟩ := exists_adj_reachable (S := {x, y, z}) (hcard ▸ hG) (s := s)
    (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact hs)
    (v := c) (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact hc)
  rw [hset] at hcd
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  exact ⟨d, hd, hcd, hsd⟩

/-! ## The contraction away from the merged vertex -/

/-- **Away from the merged vertex, the contraction is `G`**: an induced subgraph of
`contractEdge G x y` whose vertices avoid `x` is the graph induced by `G` on the same vertices. -/
def contractEdgeInduceIso (G : SimpleGraph V) {x y : V} {s : Set {v // v ≠ y}} {u : Set V}
    (h : ∀ v, v ∈ u ↔ ∃ hv : v ≠ y, (⟨v, hv⟩ : {v // v ≠ y}) ∈ s) (hx : x ∉ u) :
    (contractEdge G x y).induce s ≃g G.induce u where
  toFun p := ⟨p.1.1, (h _).mpr ⟨p.1.2, p.2⟩⟩
  invFun q := ⟨⟨q.1, ((h _).mp q.2).1⟩, ((h _).mp q.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨⟨p, hp⟩, hps⟩ ⟨⟨q, hq⟩, hqs⟩
    have hpx : p ≠ x := fun he => hx (he ▸ (h p).mpr ⟨hp, hps⟩)
    have hqx : q ≠ x := fun he => hx (he ▸ (h q).mpr ⟨hq, hqs⟩)
    change G.Adj p q ↔ (contractEdge G x y).Adj ⟨p, hp⟩ ⟨q, hq⟩
    rw [contractEdge_adj]
    constructor
    · intro hpq
      exact ⟨fun he => hpq.ne (congrArg Subtype.val he), Or.inl (Or.inl hpq)⟩
    · rintro ⟨-, (hpq | ⟨hpx', -⟩) | (hqp | ⟨hqx', -⟩)⟩
      · exact hpq
      · exact absurd hpx' hpx
      · exact hqp.symm
      · exact absurd hqx' hqx

/-- **Contracting keeps connectivity away from the merged vertex**: if `S` avoids the merged
vertex `x` and `G` stays connected after deleting the vertices of `S`, so does the contraction. -/
theorem connected_induce_contractEdge {x y : V} (hxy : G.Adj x y) {S : Finset {v // v ≠ y}}
    (hx : (⟨x, hxy.ne⟩ : {v // v ≠ y}) ∉ S)
    (h : (G.induce {v | v ∉ S.map (Function.Embedding.subtype _)}).Connected) :
    ((contractEdge G x y).induce {p | p ∉ S}).Connected := by
  classical
  have hc := (isConnectedSet_iff.mpr h).image_of_eq_or_adj (G' := contractEdge G x y)
    (contractVertex hxy.ne) fun _ _ _ _ huw => contractVertex_eq_or_adj hxy huw
  have himage : contractVertex hxy.ne '' {v | v ∉ S.map (Function.Embedding.subtype _)} =
      {p | p ∉ S} := by
    ext p
    constructor
    · rintro ⟨v, hv, rfl⟩
      by_cases hvy : v = y
      · subst hvy
        rw [contractVertex_self]
        exact hx
      · rw [contractVertex_of_ne _ hvy]
        exact fun hS => hv (Finset.mem_map_of_mem _ hS)
    · intro hp
      refine ⟨p.1, fun hm => ?_, contractVertex_val _ p⟩
      obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hm
      rw [show q = p from Subtype.ext hqp] at hq
      exact hp hq
  rw [himage] at hc
  exact isConnectedSet_iff.mp hc

/-- Deleting the merged vertex and one more vertex `z` from the contraction is deleting `x`, `y`
and `z` from `G`. -/
private theorem connected_contractEdge_induce_pair_iff {x y : V} (hxy : x ≠ y)
    {z : {v // v ≠ y}} {S : Finset {v // v ≠ y}} (hS : ∀ p, p ∈ S ↔ p = ⟨x, hxy⟩ ∨ p = z) :
    ((contractEdge G x y).induce {p | p ∉ S}).Connected ↔
      (G.induce {v | v ≠ x ∧ v ≠ y ∧ v ≠ z.1}).Connected := by
  refine (contractEdgeInduceIso G (fun v => ?_) fun h => h.1 rfl).connected_iff
  constructor
  · rintro ⟨hvx, hvy, hvz⟩
    refine ⟨hvy, fun hm => ?_⟩
    rcases (hS _).mp hm with he | he
    · exact hvx (congrArg Subtype.val he)
    · exact hvz (congrArg Subtype.val he)
  · rintro ⟨hvy, hvS⟩
    exact ⟨fun he => hvS ((hS _).mpr (Or.inl (Subtype.ext he))), hvy,
      fun he => hvS ((hS _).mpr (Or.inr (Subtype.ext he)))⟩

/-! ## Contracting an edge of a `k`-connected graph -/

/-- **Contracting an edge of a `(k + 1)`-connected graph leaves a `k`-connected graph**: deleting
fewer than `k` vertices of the contraction is deleting at most `k` vertices of `G` when the merged
vertex is among them, and otherwise contracts the edge of a connected graph. -/
theorem isKConnected_contractEdge [Finite V] {k : ℕ} (hG : IsKConnected G (k + 1)) {x y : V}
    (hxy : G.Adj x y) : IsKConnected (contractEdge G x y) k := by
  classical
  refine ⟨?_, fun S hS => ?_⟩
  · have := natCard_ne_add_one y
    have := hG.1
    omega
  · by_cases hx : (⟨x, hxy.ne⟩ : {v // v ≠ y}) ∈ S
    · have hcard : (insert y (S.map (Function.Embedding.subtype _))).card < k + 1 := by
        have := Finset.card_insert_le y (S.map (Function.Embedding.subtype _))
        rw [Finset.card_map] at this
        omega
      refine (contractEdgeInduceIso G (fun v => ?_) ?_).connected_iff.mpr (hG.2 _ hcard)
      · simp only [Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_map,
          Function.Embedding.subtype_apply, not_or, not_exists, not_and]
        constructor
        · rintro ⟨hvy, hv⟩
          exact ⟨hvy, fun h' => hv ⟨v, hvy⟩ h' rfl⟩
        · rintro ⟨hvy, hv⟩
          exact ⟨hvy, fun q hq hqv => hv (by subst hqv; exact hq)⟩
      · exact fun h' => h' (Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hx))
    · exact connected_induce_contractEdge hxy hx (hG.2 _ (by rw [Finset.card_map]; omega))

/-- **When contracting `xy` keeps `3`-connectivity**: for a `3`-connected graph on at least five
vertices, `contractEdge G x y` is `3`-connected exactly when deleting `x`, `y` and any third
vertex `z` leaves `G` connected. -/
theorem isKConnected_contractEdge_three_iff [Finite V] (hG : IsKConnected G 3) {x y : V}
    (hxy : G.Adj x y) (hV : 5 ≤ Nat.card V) :
    IsKConnected (contractEdge G x y) 3 ↔
      ∀ z, z ≠ x → z ≠ y → (G.induce {v | v ≠ x ∧ v ≠ y ∧ v ≠ z}).Connected := by
  classical
  constructor
  · intro hK z hzx hzy
    have hS : ∀ p, p ∈ ({⟨x, hxy.ne⟩, ⟨z, hzy⟩} : Finset {v // v ≠ y}) ↔
        p = ⟨x, hxy.ne⟩ ∨ p = ⟨z, hzy⟩ := fun p => by simp
    exact (connected_contractEdge_induce_pair_iff hxy.ne hS).mp
      (hK.2 _ (Finset.card_le_two.trans_lt (by norm_num)))
  · intro hall
    refine ⟨by have := natCard_ne_add_one y; omega, fun S hS => ?_⟩
    by_cases hS2 : S.card < 2
    · exact (isKConnected_contractEdge (k := 2) hG hxy).2 S hS2
    by_cases hx : (⟨x, hxy.ne⟩ : {v // v ≠ y}) ∈ S
    · -- `S` is the merged vertex and one more vertex `z`.
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp
        (by rw [Finset.card_erase_of_mem hx]; omega : (S.erase ⟨x, hxy.ne⟩).card = 1)
      have hmem : ∀ p, p ∈ S ↔ p = ⟨x, hxy.ne⟩ ∨ p = z := by
        intro p
        rw [← Finset.insert_erase hx, hz]
        simp
      have hzx : z.1 ≠ x := by
        intro he
        have hzS : z ∈ S.erase ⟨x, hxy.ne⟩ := hz ▸ Finset.mem_singleton_self z
        exact Finset.ne_of_mem_erase hzS (Subtype.ext he)
      exact (connected_contractEdge_induce_pair_iff hxy.ne hmem).mpr (hall z.1 hzx z.2)
    · exact connected_induce_contractEdge hxy hx (hG.2 _ (by rw [Finset.card_map]; omega))

/-- **A separating triple for a bad edge**: if contracting the edge `xy` of a `3`-connected graph
on at least five vertices does not give a `3`-connected graph, then deleting `x`, `y` and some
third vertex `z` disconnects `G`. -/
theorem exists_separating_triple [Finite V] (hG : IsKConnected G 3) {x y : V} (hxy : G.Adj x y)
    (hV : 5 ≤ Nat.card V) (h : ¬ IsKConnected (contractEdge G x y) 3) :
    ∃ z, z ≠ x ∧ z ≠ y ∧ ¬ (G.induce {v | v ≠ x ∧ v ≠ y ∧ v ≠ z}).Connected := by
  rw [isKConnected_contractEdge_three_iff hG hxy hV] at h
  push Not at h
  exact h

/-! ## Components next to separating triples -/

/-- **Component containment**: a component of the graph induced on `s` that lies in `t` and
meets the component of `c` in the graph induced on `t` lies inside that component. -/
theorem setOf_reachable_subset {s t : Set V} {b c u : V} (hb : b ∈ s)
    (hst : ∀ d, d ∈ s → (restrictTo G s).Reachable b d → d ∈ t) (hus : u ∈ s)
    (hbu : (restrictTo G s).Reachable b u) (hcu : (restrictTo G t).Reachable c u) :
    {d | d ∈ s ∧ (restrictTo G s).Reachable b d} ⊆
      {d | d ∈ t ∧ (restrictTo G t).Reachable c d} := by
  rintro d ⟨hds, hbd⟩
  refine ⟨hst d hds hbd, hcu.trans ?_⟩
  exact ((isConnectedSet_setOf_reachable hb).2 u ⟨hus, hbu⟩ d ⟨hds, hbd⟩).mono
    (restrictTo_mono fun e he => hst e he.1 he.2)

/-- **A strictly smaller component**: let `xy` be an edge of a `3`-connected graph, `z` a third
vertex, and `v` a vertex of the component `C` of `c` in `G - {x, y, z}`.  If `{z, v, w}` is a
separator, then some component of `G - {z, v, w}` has fewer vertices than `C`.  Indeed the
vertices among `x, y` other than `w` lie in one component of `G - {z, v, w}`; another component
avoids `x`, `y` and `z`, and contains a neighbour of `v`, so it lies in `C`, which also contains
`v`. -/
theorem exists_ncard_setOf_reachable_lt [Finite V] (hG : IsKConnected G 3) {x y z v w c : V}
    (hxy : G.Adj x y) (hzx : z ≠ x) (hzy : z ≠ y) (hwz : w ≠ z) (hwv : w ≠ v)
    (hv : v ∈ {d | d ∈ {u | u ≠ x ∧ u ≠ y ∧ u ≠ z} ∧
      (restrictTo G {u | u ≠ x ∧ u ≠ y ∧ u ≠ z}).Reachable c d})
    (hS : ¬ (G.induce {u | u ≠ z ∧ u ≠ v ∧ u ≠ w}).Connected) :
    ∃ b, (b ≠ z ∧ b ≠ v ∧ b ≠ w) ∧
      {d | d ∈ {u | u ≠ z ∧ u ≠ v ∧ u ≠ w} ∧
          (restrictTo G {u | u ≠ z ∧ u ≠ v ∧ u ≠ w}).Reachable b d}.ncard <
        {d | d ∈ {u | u ≠ x ∧ u ≠ y ∧ u ≠ z} ∧
          (restrictTo G {u | u ≠ x ∧ u ≠ y ∧ u ≠ z}).Reachable c d}.ncard := by
  set t : Set V := {u | u ≠ x ∧ u ≠ y ∧ u ≠ z}
  set s : Set V := {u | u ≠ z ∧ u ≠ v ∧ u ≠ w}
  obtain ⟨hvt, hcv⟩ := hv
  have hv3 : v ≠ x ∧ v ≠ y ∧ v ≠ z := hvt
  obtain ⟨hvx, hvy, hvz⟩ := hv3
  -- A vertex `a` among `x, y` outside `{z, v, w}` reaching those of `x, y` outside it.
  obtain ⟨a, has, hax, hay⟩ : ∃ a ∈ s, (x ∈ s → (restrictTo G s).Reachable a x) ∧
      (y ∈ s → (restrictTo G s).Reachable a y) := by
    by_cases hxw : x = w
    · exact ⟨y, ⟨hzy.symm, hvy.symm, fun h => hxy.ne (hxw.trans h.symm)⟩,
        fun h => absurd hxw h.2.2, fun _ => .rfl⟩
    · have hxs : x ∈ s := ⟨hzx.symm, hvx.symm, hxw⟩
      exact ⟨x, hxs, fun _ => .rfl, fun hys => (restrictTo_adj.mpr ⟨hxy, hxs, hys⟩).reachable⟩
  -- The component of a vertex `b` not reachable from `a` avoids `x` and `y`, so lies in `t`.
  obtain ⟨b, hbs, hab⟩ := exists_not_reachable has hS
  have hDt : ∀ d, d ∈ s → (restrictTo G s).Reachable b d → d ∈ t := by
    intro d hds hbd
    refine ⟨?_, ?_, hds.1⟩
    · rintro rfl
      exact hab ((hax hds).trans hbd.symm)
    · rintro rfl
      exact hab ((hay hds).trans hbd.symm)
  -- `v` has a neighbour `u` in that component, and `u` lies in `C`.
  obtain ⟨u, hus, hbu, hvu⟩ := exists_adj_reachable_triple hG hvz.symm hwz.symm hwv.symm
    (Or.inr (Or.inl rfl)) hbs
  have hut := hDt u hus hbu
  have hcu : (restrictTo G t).Reachable c u :=
    hcv.trans (restrictTo_adj.mpr ⟨hvu, hvt, hut⟩).reachable
  refine ⟨b, hbs, Set.ncard_lt_ncard ⟨setOf_reachable_subset hbs hDt hus hbu hcu, fun h => ?_⟩⟩
  -- `v` lies in `C` but not in the component of `b`.
  exact (h (a := v) ⟨hvt, hcv⟩).1.2.1 rfl

end Contraction

/-! ## The contractible edge -/

/-- **A contractible edge**: every `3`-connected graph on at least five vertices has an edge whose
contraction is `3`-connected.  Otherwise every edge `xy` lies in a separating triple `{x, y, z}`;
choose such a triple and a component `C` of `G - {x, y, z}` with as few vertices as possible.
The vertex `z` has a neighbour `v` in `C`, the edge `zv` lies in a separating triple `{z, v, w}`,
and `G - {z, v, w}` has a component with fewer vertices than `C`. -/
theorem exists_contractEdge_isKConnected_three {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : IsKConnected G 3) (hV : 5 ≤ Nat.card V) :
    ∃ x y, G.Adj x y ∧ IsKConnected (contractEdge G x y) 3 := by
  classical
  by_contra hbad
  push Not at hbad
  -- `P n`: some triple `{x, y, z}`, with `xy` an edge, leaves a component with `n` vertices.
  let P : ℕ → Prop := fun n => ∃ x y z c : V, G.Adj x y ∧ z ≠ x ∧ z ≠ y ∧
    c ∈ {u | u ≠ x ∧ u ≠ y ∧ u ≠ z} ∧
    {d | d ∈ {u | u ≠ x ∧ u ≠ y ∧ u ≠ z} ∧
      (restrictTo G {u | u ≠ x ∧ u ≠ y ∧ u ≠ z}).Reachable c d}.ncard = n
  have hP : ∃ n, P n := by
    obtain ⟨x⟩ := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card V)).1
    obtain ⟨y, hxy⟩ := Set.nonempty_of_ncard_ne_zero
      (by have := hG.le_ncard_neighborSet x; omega : (G.neighborSet x).ncard ≠ 0)
    have hxy : G.Adj x y := hxy
    obtain ⟨z, hzx, hzy, -⟩ := exists_separating_triple hG hxy hV (hbad x y hxy)
    obtain ⟨c, hc⟩ := exists_ne_of_three_lt (by omega : 3 < Nat.card V) x y z
    exact ⟨_, x, y, z, c, hxy, hzx, hzy, hc, rfl⟩
  -- Each such component gives a smaller one.
  have hstep : ∀ n, P n → ∃ m < n, P m := by
    rintro n ⟨x, y, z, c, hxy, hzx, hzy, hc, rfl⟩
    obtain ⟨v, hv, hcv, hzv⟩ := exists_adj_reachable_triple hG hxy.ne hzx.symm hzy.symm
      (Or.inr (Or.inr rfl)) hc
    obtain ⟨w, hwz, hwv, hS⟩ := exists_separating_triple hG hzv hV (hbad z v hzv)
    obtain ⟨b, hb, hlt⟩ := exists_ncard_setOf_reachable_lt hG hxy hzx hzy hwz hwv ⟨hv, hcv⟩ hS
    exact ⟨_, hlt, z, v, w, b, hzv, hwz, hwv, hb, rfl⟩
  obtain ⟨m, hm, hPm⟩ := hstep _ (Nat.find_spec hP)
  exact Nat.find_min hP hm hPm

end MonoidProduct.Graph
