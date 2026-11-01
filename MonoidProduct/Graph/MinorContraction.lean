import MonoidProduct.Graph.Minor
set_option linter.style.header false

/-!
# Contracting an edge inside a branch set

The vertex map of the contraction `contractEdge G x y` (`Graph/Minor.lean`), and what it does to
edges, reachability, connected sets and minor models.

* `contractVertex hxy : V → {v // v ≠ y}`: `y` goes to `x`, every other vertex to itself.  Two
  vertices have the same image exactly when they are equal or both ends of the edge
  (`contractVertex_eq_iff`).
* Every edge other than `xy` survives the contraction (`contractEdge_adj_contractVertex`), so
  adjacent vertices go to equal or adjacent vertices (`contractVertex_eq_or_adj`); the map is not a
  graph homomorphism, as it collapses `xy`.
* Contracting an edge keeps reachability both ways, hence the number of components
  (`natCard_connectedComponent_contractEdge`).
* `IsConnectedSet.image_of_eq_or_adj`: connected sets go to connected sets under any map sending
  adjacent vertices to equal or adjacent vertices.  `IsConnectedSet.exists_adj_of_ne`: a connected
  set with two distinct vertices contains an edge.
* `MinorModel.contractEdge`: contracting an edge with both ends in one branch set pushes a minor
  model of `H` in `G` forward to a minor model of `H` in the contraction, with the image branch
  sets.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V}

/-! ## The vertex map -/

section ContractVertex

variable [DecidableEq V] {x y : V}

/-- **The vertex map of contracting `xy`**: `y` goes to `x`, every other vertex to itself. -/
def contractVertex (hxy : x ≠ y) (v : V) : {v // v ≠ y} :=
  if h : v = y then ⟨x, hxy⟩ else ⟨v, h⟩

theorem contractVertex_of_ne (hxy : x ≠ y) {v : V} (hv : v ≠ y) :
    contractVertex hxy v = ⟨v, hv⟩ :=
  dite_eq_right hv

@[simp] theorem contractVertex_self (hxy : x ≠ y) : contractVertex hxy y = ⟨x, hxy⟩ :=
  dite_eq_left rfl

/-- The map is the identity on the remaining vertices. -/
@[simp] theorem contractVertex_val (hxy : x ≠ y) (p : {v // v ≠ y}) :
    contractVertex hxy p.1 = p :=
  contractVertex_of_ne hxy p.2

theorem val_contractVertex (hxy : x ≠ y) (v : V) :
    (contractVertex hxy v : V) = if v = y then x else v := by
  unfold contractVertex
  split_ifs <;> rfl

/-- **The fibres of the vertex map**: two vertices have the same image exactly when they are equal
or both are ends of the edge. -/
theorem contractVertex_eq_iff (hxy : x ≠ y) {u w : V} :
    contractVertex hxy u = contractVertex hxy w ↔ u = w ∨ ((u = x ∨ u = y) ∧ (w = x ∨ w = y)) := by
  rw [← Subtype.coe_inj, val_contractVertex, val_contractVertex]
  by_cases hu : u = y <;> by_cases hw : w = y
  · subst hu hw
    simp
  · subst hu
    rw [ite_eq_left rfl, ite_eq_right hw]
    constructor
    · intro h
      exact Or.inr ⟨Or.inr rfl, Or.inl h.symm⟩
    · rintro (h | ⟨-, h | h⟩)
      · exact absurd h.symm hw
      · exact h.symm
      · exact absurd h hw
  · subst hw
    rw [ite_eq_right hu, ite_eq_left rfl]
    constructor
    · intro h
      exact Or.inr ⟨Or.inl h, Or.inr rfl⟩
    · rintro (h | ⟨h | h, -⟩)
      · exact absurd h hu
      · exact h
      · exact absurd h hu
  · rw [ite_eq_right hu, ite_eq_right hw]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h | h, h' | h'⟩)
      · exact h
      · exact h.trans h'.symm
      · exact absurd h' hw
      · exact absurd h hu
      · exact absurd h hu

/-- **Edges other than `xy` survive the contraction.** -/
theorem contractEdge_adj_contractVertex (hxy : G.Adj x y) {u w : V} (h : G.Adj u w)
    (he : s(u, w) ≠ s(x, y)) :
    (contractEdge G x y).Adj (contractVertex hxy.ne u) (contractVertex hxy.ne w) := by
  rw [contractEdge_adj]
  refine ⟨fun hq => ?_, ?_⟩
  · rcases (contractVertex_eq_iff hxy.ne).mp hq with huw | ⟨hu | hu, hw | hw⟩
    · exact h.ne huw
    · exact h.ne (hu.trans hw.symm)
    · exact he (by rw [hu, hw])
    · exact he (by rw [hu, hw, Sym2.eq_swap])
    · exact h.ne (hu.trans hw.symm)
  · by_cases hu : u = y
    · subst hu
      have hw : w ≠ u := h.ne.symm
      rw [contractVertex_self, contractVertex_of_ne _ hw]
      exact Or.inl (Or.inr ⟨rfl, h⟩)
    · by_cases hw : w = y
      · subst hw
        rw [contractVertex_self, contractVertex_of_ne _ hu]
        exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
      · rw [contractVertex_of_ne _ hu, contractVertex_of_ne _ hw]
        exact Or.inl (Or.inl h)

/-- **Adjacent vertices go to equal or adjacent vertices**: the edge `xy` collapses, every other
edge survives. -/
theorem contractVertex_eq_or_adj (hxy : G.Adj x y) {u w : V} (h : G.Adj u w) :
    contractVertex hxy.ne u = contractVertex hxy.ne w ∨
      (contractEdge G x y).Adj (contractVertex hxy.ne u) (contractVertex hxy.ne w) := by
  by_cases he : s(u, w) = s(x, y)
  · refine Or.inl ((contractVertex_eq_iff hxy.ne).mpr (Or.inr ?_))
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
  · exact Or.inr (contractEdge_adj_contractVertex hxy h he)

/-! ## Reachability and components -/

/-- **Contracting keeps reachability.** -/
theorem reachable_contractVertex (hxy : G.Adj x y) {u w : V} (h : G.Reachable u w) :
    (contractEdge G x y).Reachable (contractVertex hxy.ne u) (contractVertex hxy.ne w) := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hcd ih =>
    rcases contractVertex_eq_or_adj hxy hcd with he | hadj
    · rwa [← he]
    · exact ih.trans hadj.reachable

omit [DecidableEq V] in
/-- **Reachability after contracting comes from reachability before.** -/
theorem reachable_of_reachable_contractEdge (hxy : G.Adj x y) {p r : {v // v ≠ y}}
    (h : (contractEdge G x y).Reachable p r) : G.Reachable p.1 r.1 := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hcd ih =>
    refine ih.trans ?_
    obtain ⟨-, (h | ⟨hx, h⟩) | (h | ⟨hx, h⟩)⟩ := contractEdge_adj.mp hcd
    · exact h.reachable
    · rw [hx]
      exact hxy.reachable.trans h.reachable
    · exact h.reachable.symm
    · rw [hx]
      exact (hxy.reachable.trans h.reachable).symm

/-- A vertex reaches its image. -/
theorem reachable_val_contractVertex (hxy : G.Adj x y) (u : V) :
    G.Reachable u (contractVertex hxy.ne u).1 := by
  by_cases hu : u = y
  · subst hu
    rw [contractVertex_self]
    exact hxy.reachable.symm
  · rw [contractVertex_of_ne _ hu]

omit [DecidableEq V] in
/-- **Contracting an edge keeps the number of components.** -/
theorem natCard_connectedComponent_contractEdge (hxy : G.Adj x y) :
    Nat.card (contractEdge G x y).ConnectedComponent = Nat.card G.ConnectedComponent := by
  classical
  let φ : G.ConnectedComponent → (contractEdge G x y).ConnectedComponent :=
    Quot.lift (fun v => (contractEdge G x y).connectedComponentMk (contractVertex hxy.ne v))
      fun u w h => ConnectedComponent.eq.mpr (reachable_contractVertex hxy h)
  refine (Nat.card_eq_of_bijective φ ⟨fun c c' hcc => ?_, fun c' => ?_⟩).symm
  · induction c using ConnectedComponent.ind with
    | h u =>
    induction c' using ConnectedComponent.ind with
    | h w =>
    have h := reachable_of_reachable_contractEdge hxy (ConnectedComponent.eq.mp hcc)
    exact ConnectedComponent.eq.mpr (((reachable_val_contractVertex hxy u).trans h).trans
      (reachable_val_contractVertex hxy w).symm)
  · induction c' using ConnectedComponent.ind with
    | h p =>
    refine ⟨G.connectedComponentMk p.1, ?_⟩
    change (contractEdge G x y).connectedComponentMk (contractVertex hxy.ne p.1) = _
    rw [contractVertex_val]

end ContractVertex

/-! ## Connected sets -/

/-- **Connected sets under maps sending adjacent vertices to equal or adjacent vertices.** -/
theorem IsConnectedSet.image_of_eq_or_adj {G' : SimpleGraph W} {s : Set V}
    (h : IsConnectedSet G s) (f : V → W)
    (hf : ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → f u = f v ∨ G'.Adj (f u) (f v)) :
    IsConnectedSet G' (f '' s) := by
  refine ⟨h.1.image f, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hr := h.2 a ha b hb
  clear hb
  rw [reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => rfl
  | tail _ hcd ih =>
    obtain ⟨hcd, hc, hd⟩ := hcd
    rcases hf _ hc _ hd hcd with he | hadj
    · rwa [← he]
    · exact ih.trans (restrictTo_adj.mpr
        ⟨hadj, Set.mem_image_of_mem f hc, Set.mem_image_of_mem f hd⟩).reachable

/-- **A connected set with two distinct vertices contains an edge**: the first edge of a walk
inside it between them. -/
theorem IsConnectedSet.exists_adj_of_ne {s : Set V} (h : IsConnectedSet G s) {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v) : ∃ x ∈ s, ∃ y ∈ s, G.Adj x y := by
  obtain ⟨p⟩ := h.2 u hu v hv
  cases p with
  | nil => exact absurd rfl huv
  | cons hadj _ => exact ⟨u, hadj.2.1, _, hadj.2.2, hadj.1⟩

/-! ## Minor models -/

variable [DecidableEq V]

/-- **Pushing a minor model through the contraction of an edge inside one branch set**: the
branch sets are the images under `contractVertex`.  They stay connected, since `xy` collapses and
every other edge survives; they stay disjoint, since only `x` and `y` are identified and both lie
in the same branch set; and an edge between two branch sets survives, as it is not `xy`. -/
def MinorModel.contractEdge {H : SimpleGraph W} (m : MinorModel H G) {x y : V} (hxy : G.Adj x y)
    {w₀ : W} (hx : x ∈ m.branch w₀) (hy : y ∈ m.branch w₀) :
    MinorModel H (Graph.contractEdge G x y) where
  branch w := contractVertex hxy.ne '' m.branch w
  connected w :=
    (m.connected w).image_of_eq_or_adj _ fun _ _ _ _ h => contractVertex_eq_or_adj hxy h
  disjoint w w' h := by
    -- Both ends of the edge lie in the branch set of `w₀`.
    have hend : ∀ {u w}, u ∈ m.branch w → (u = x ∨ u = y) → w = w₀ := fun {u w} hu hxy' => by
      by_contra hne
      exact Set.disjoint_left.mp (m.disjoint w w₀ hne) hu (hxy'.elim (· ▸ hx) (· ▸ hy))
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    rcases (contractVertex_eq_iff hxy.ne).mp he with rfl | ⟨hv', hu'⟩
    · exact Set.disjoint_left.mp (m.disjoint w w' h) hu hv
    · exact h ((hend hu hu').trans (hend hv hv').symm)
  adj w w' h := by
    obtain ⟨a, ha, b, hb, hab⟩ := m.adj w w' h
    refine ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, contractEdge_adj_contractVertex hxy hab fun he => ?_⟩
    -- The edge `ab` is not `xy`: its ends would lie in one branch set.
    have hend : ∀ {u w}, u ∈ m.branch w → (u = x ∨ u = y) → w = w₀ := fun {u w} hu hxy' => by
      by_contra hne
      exact Set.disjoint_left.mp (m.disjoint w w₀ hne) hu (hxy'.elim (· ▸ hx) (· ▸ hy))
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact H.loopless.irrefl w (((hend ha (Or.inl rfl)).trans (hend hb (Or.inr rfl)).symm) ▸ h)
    · exact H.loopless.irrefl w (((hend ha (Or.inr rfl)).trans (hend hb (Or.inl rfl)).symm) ▸ h)

@[simp] theorem MinorModel.branch_contractEdge {H : SimpleGraph W} (m : MinorModel H G) {x y : V}
    (hxy : G.Adj x y) {w₀ : W} (hx : x ∈ m.branch w₀) (hy : y ∈ m.branch w₀) (w : W) :
    (m.contractEdge hxy hx hy).branch w = contractVertex hxy.ne '' m.branch w :=
  rfl

end MonoidProduct.Graph
