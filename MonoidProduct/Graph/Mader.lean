import Mathlib.Tactic.Linarith
import MonoidProduct.Graph.Minor
set_option linter.style.header false

/-!
# Mader's theorem and minor-closed classes

`monoid.tex`, section `sec:graph-certificates`, paragraph "Planarity and minor-closed
properties": every fixed proper minor-closed graph class has a linear edge bound.

* `isMinor_top_of_le` (Mader; Diestel, *Graph Theory*, Proposition 7.2.1): a graph on `v ≥ 1`
  vertices with `2^(r-2)·v ≤ 2|E|`, that is with average degree at least `2^(r-2)`, has the
  complete graph `K_r` as a minor, for every `r ≥ 2`.  The proof is by induction on `r` and on
  `v`.  If some edge `xy` has fewer than `2^(r-3)` common neighbours, contracting it loses at most
  `2^(r-3)` edges and one vertex, which keeps the density (`ncard_edgeSet_le_contractEdge`).
  Otherwise any vertex `x` with a neighbour has a neighbourhood of average degree at least
  `2^(r-3)`, which by induction has a `K_(r-1)` minor; with `x` this is a `K_r` minor
  (`isMinor_top_succ_of_induce_neighborSet`).
* `ncard_edgeSet_le_of_not_isMinor`: a graph without a `K_r` minor has at most `2^r·v` edges.
* `IsMinorClosed P` and `IsProperClass P`: a class of graphs on finite vertex types, closed under
  minors (hence under isomorphism), and not containing every finite graph.
* `IsMinorClosed.exists_ncard_edgeSet_le`: **every proper minor-closed class has a linear edge
  bound**.  A finite graph `H` outside the class is a minor of `K_t`, `t = |V(H)|`, so no graph of
  the class has a `K_t` minor, and Mader's bound applies with the constant `2^t`.
-/

namespace MonoidProduct.Graph

open SimpleGraph

/-! ## Counting -/

section Counting

variable {V : Type*}

/-- **Handshake**: `2|E| = Σ_v |N(v)|`. -/
theorem two_mul_ncard_edgeSet [Fintype V] (G : SimpleGraph V) :
    2 * G.edgeSet.ncard = ∑ v, (G.neighborSet v).ncard := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← sum_degrees_eq_twice_card_edges]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]

/-- **In the neighbourhood of `x`**, the degree of `y` is the number of common neighbours of `x`
and `y`. -/
theorem ncard_neighborSet_induce_neighborSet (G : SimpleGraph V) {x : V}
    (y : G.neighborSet x) :
    ((G.induce (G.neighborSet x)).neighborSet y).ncard =
      (G.neighborSet x ∩ G.neighborSet y).ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext z
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hzx, hzy⟩
    exact ⟨⟨z, hzx⟩, hzy, rfl⟩

/-- **Contracting an edge `xy` loses at most `1 + |N(x) ∩ N(y)|` edges.** -/
theorem ncard_edgeSet_le_contractEdge [Finite V] {G : SimpleGraph V} {x y : V}
    (hxy : G.Adj x y) :
    G.edgeSet.ncard ≤
      (contractEdge G x y).edgeSet.ncard + 1 + (G.neighborSet x ∩ G.neighborSet y).ncard := by
  classical
  have hxy' : x ≠ y := hxy.ne
  -- `φ` keeps every vertex other than `y`, and sends `y` to `x`.
  let φ : V → {v // v ≠ y} := fun v => if h : v = y then ⟨x, hxy'⟩ else ⟨v, h⟩
  have hφ : ∀ v (hv : v ≠ y), φ v = ⟨v, hv⟩ := fun v hv => dite_eq_right hv
  set A : Set (Sym2 V) := {e | e ∈ G.edgeSet ∧ y ∉ e} with hAdef
  set R : Set V := G.neighborSet y \ insert x (G.neighborSet x) with hRdef
  -- (1) The edges split into those avoiding `y` and those at `y`.
  have hE : G.edgeSet = A ∪ (fun b => s(y, b)) '' G.neighborSet y := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
    constructor
    · intro he
      by_cases hy : y ∈ s(a, b)
      · right
        rcases Sym2.mem_iff.mp hy with rfl | rfl
        · exact ⟨b, he, rfl⟩
        · exact ⟨a, (G.mem_edgeSet.mp he).symm, Sym2.eq_swap⟩
      · exact Or.inl ⟨he, hy⟩
    · rintro (⟨he, -⟩ | ⟨c, hc, he⟩)
      · exact he
      · rw [← he]
        exact hc
  have hdisj : Disjoint A ((fun b => s(y, b)) '' G.neighborSet y) := by
    rw [Set.disjoint_left]
    rintro e ⟨-, hy⟩ ⟨c, -, rfl⟩
    exact hy (Sym2.mem_mk_left _ _)
  have h1 : G.edgeSet.ncard = A.ncard + (G.neighborSet y).ncard := by
    rw [hE, Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _
      fun b c h => Sym2.congr_right.mp h]
  -- (2) The neighbours of `y` are `x`, the common neighbours, and the rest `R`.
  have h2 : (G.neighborSet y).ncard ≤ 1 + (G.neighborSet x ∩ G.neighborSet y).ncard + R.ncard := by
    have hsub : G.neighborSet y ⊆ insert x (G.neighborSet x ∩ G.neighborSet y) ∪ R := by
      intro b hb
      by_cases hbx : b = x
      · exact Or.inl (Or.inl hbx)
      by_cases hb' : G.Adj x b
      · exact Or.inl (Or.inr ⟨hb', hb⟩)
      · exact Or.inr ⟨hb, fun h => (Set.mem_insert_iff.mp h).elim hbx hb'⟩
    calc (G.neighborSet y).ncard ≤ (insert x (G.neighborSet x ∩ G.neighborSet y) ∪ R).ncard :=
          Set.ncard_le_ncard hsub
      _ ≤ (insert x (G.neighborSet x ∩ G.neighborSet y)).ncard + R.ncard :=
          Set.ncard_union_le _ _
      _ ≤ (G.neighborSet x ∩ G.neighborSet y).ncard + 1 + R.ncard := by
          gcongr
          exact Set.ncard_insert_le _ _
      _ = 1 + (G.neighborSet x ∩ G.neighborSet y).ncard + R.ncard := by ring
  -- (3) The edges avoiding `y`, and the edges from `x` to `R`, are edges of the contraction.
  let f : Sym2 V → Sym2 {v // v ≠ y} := Sym2.map φ
  let g : V → Sym2 {v // v ≠ y} := fun b => s(⟨x, hxy'⟩, φ b)
  have hval : ∀ e ∈ A, Sym2.map Subtype.val (f e) = e := by
    intro e he
    rw [Sym2.map_map]
    calc Sym2.map (Subtype.val ∘ φ) e = Sym2.map id e := Sym2.map_congr fun v hv => by
          have hvy : v ≠ y := fun h => he.2 (h ▸ hv)
          simp [Function.comp, hφ v hvy]
      _ = e := by simp
  have hfA : Set.InjOn f A := fun e he e' he' h => by
    rw [← hval e he, ← hval e' he', h]
  have hgR : Set.InjOn g R := fun b hb c hc h => by
    have hb' : b ≠ y := G.ne_of_adj hb.1 |>.symm
    have hc' : c ≠ y := G.ne_of_adj hc.1 |>.symm
    have := Sym2.congr_right.mp h
    rw [hφ b hb', hφ c hc'] at this
    exact congrArg Subtype.val this
  have hfsub : f '' A ⊆ (contractEdge G x y).edgeSet := by
    rintro _ ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | h a b =>
    have hab := G.mem_edgeSet.mp he.1
    have ha : a ≠ y := fun h => he.2 (h ▸ Sym2.mem_mk_left a b)
    have hb : b ≠ y := fun h => he.2 (h ▸ Sym2.mem_mk_right a b)
    change (contractEdge G x y).Adj (φ a) (φ b)
    rw [hφ a ha, hφ b hb, contractEdge_adj]
    exact ⟨fun h => hab.ne (congrArg Subtype.val h), Or.inl (Or.inl hab)⟩
  have hgsub : g '' R ⊆ (contractEdge G x y).edgeSet := by
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b ≠ y := (G.ne_of_adj hb.1).symm
    have hbx : b ≠ x := fun h => hb.2 (Set.mem_insert_iff.mpr (Or.inl h))
    change (contractEdge G x y).Adj ⟨x, hxy'⟩ (φ b)
    rw [hφ b hb', contractEdge_adj]
    exact ⟨fun h => hbx (congrArg Subtype.val h).symm, Or.inl (Or.inr ⟨rfl, hb.1⟩)⟩
  have hfg : Disjoint (f '' A) (g '' R) := by
    rw [Set.disjoint_left]
    rintro _ ⟨e, he, rfl⟩ ⟨b, hb, hfe⟩
    have hb' : b ≠ y := (G.ne_of_adj hb.1).symm
    have := congrArg (Sym2.map Subtype.val) hfe
    rw [hval e he] at this
    simp only [g, Sym2.map_mk, hφ b hb'] at this
    have hxb : G.Adj x b := by
      have h := he.1
      rw [← this] at h
      exact h
    exact hb.2 (Set.mem_insert_iff.mpr (Or.inr hxb))
  have h3 : A.ncard + R.ncard ≤ (contractEdge G x y).edgeSet.ncard := by
    rw [← hfA.ncard_image, ← hgR.ncard_image, ← Set.ncard_union_eq hfg]
    exact Set.ncard_le_ncard (Set.union_subset hfsub hgsub)
  omega

end Counting

/-! ## Mader's theorem -/

section Mader

variable {V : Type*}

/-- **A vertex joined to a `K_r` minor of its neighbourhood gives a `K_(r+1)` minor**: its own
branch set is `{x}`. -/
theorem isMinor_top_succ_of_induce_neighborSet {G : SimpleGraph V} {x : V} {r : ℕ}
    (h : IsMinor (⊤ : SimpleGraph (Fin r)) (G.induce (G.neighborSet x))) :
    IsMinor (⊤ : SimpleGraph (Fin (r + 1))) G := by
  obtain ⟨m⟩ := h
  let B : Fin (r + 1) → Set V := fun i =>
    Fin.lastCases {x} (fun j => Subtype.val '' m.branch j) i
  have hBl : B (Fin.last r) = {x} := Fin.lastCases_last
  have hBc : ∀ j, B j.castSucc = Subtype.val '' m.branch j := fun j => Fin.lastCases_castSucc j
  have hx : ∀ j, x ∉ Subtype.val '' m.branch j := by
    rintro j ⟨a, -, ha⟩
    exact G.ne_of_adj a.2 ha.symm
  refine ⟨⟨B, fun i => ?_, fun i i' hii' => ?_, fun i i' hii' => ?_⟩⟩
  · induction i using Fin.lastCases with
    | last => rw [hBl]; exact isConnectedSet_singleton G x
    | cast j => rw [hBc]; exact (m.connected j).image (Embedding.induce _).toHom
  · induction i using Fin.lastCases with
    | last =>
      induction i' using Fin.lastCases with
      | last => exact absurd rfl hii'
      | cast j' =>
        rw [hBl, hBc, Set.disjoint_singleton_left]
        exact hx j'
    | cast j =>
      induction i' using Fin.lastCases with
      | last =>
        rw [hBl, hBc, Set.disjoint_singleton_right]
        exact hx j
      | cast j' =>
        rw [hBc, hBc, Set.disjoint_image_iff Subtype.val_injective]
        exact m.disjoint j j' fun h => hii' (congrArg Fin.castSucc h)
  · induction i using Fin.lastCases with
    | last =>
      induction i' using Fin.lastCases with
      | last => exact absurd rfl hii'.ne
      | cast j' =>
        obtain ⟨a, ha⟩ := (m.connected j').1
        rw [hBl, hBc]
        exact ⟨x, rfl, a, ⟨a, ha, rfl⟩, a.2⟩
    | cast j =>
      induction i' using Fin.lastCases with
      | last =>
        obtain ⟨a, ha⟩ := (m.connected j).1
        rw [hBl, hBc]
        exact ⟨a, ⟨a, ha, rfl⟩, x, rfl, a.2.symm⟩
      | cast j' =>
        obtain ⟨a, ha, b, hb, hab⟩ :=
          m.adj j j' ((top_adj _ _).mpr fun h => hii'.ne (congrArg Fin.castSucc h))
        rw [hBc, hBc]
        exact ⟨a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, hab⟩

/-- A graph with an edge has `K₂` as a minor. -/
theorem isMinor_top_two_of_adj {G : SimpleGraph V} {a b : V} (h : G.Adj a b) :
    IsMinor (⊤ : SimpleGraph (Fin 2)) G := by
  refine ⟨.ofInjective ⟨![a, b], fun {i j} hij => ?_⟩ fun i j hij => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij.ne
    · exact h
    · exact h.symm
    · exact absurd rfl hij.ne
  · fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij h.ne
    · exact absurd hij.symm h.ne
    · rfl

/-- The induction step of Mader's theorem, by induction on the number of vertices. -/
private theorem mader_step {r : ℕ} (hr : 2 ≤ r)
    (ih : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), 1 ≤ Fintype.card V →
      2 ^ (r - 2) * Fintype.card V ≤ 2 * G.edgeSet.ncard →
        IsMinor (⊤ : SimpleGraph (Fin r)) G) :
    ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = n → 1 ≤ n →
      2 ^ (r + 1 - 2) * n ≤ 2 * G.edgeSet.ncard → IsMinor (⊤ : SimpleGraph (Fin (r + 1))) G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro V _ G hn h1 hE
  classical
  have hD : 2 ^ (r + 1 - 2) = 2 * 2 ^ (r - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hD] at hE
  by_cases hcon : ∃ x y, G.Adj x y ∧ (G.neighborSet x ∩ G.neighborSet y).ncard < 2 ^ (r - 2)
  · -- Contract an edge with few common neighbours.
    obtain ⟨x, y, hxy, ht⟩ := hcon
    have hcount := ncard_edgeSet_le_contractEdge hxy
    have hcard : Fintype.card {v // v ≠ y} = n - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hn]
    have hn2 : 2 ≤ n := by
      rw [← hn]
      exact Fintype.one_lt_card_iff.mpr ⟨x, y, hxy.ne⟩
    have hE' : 2 ^ (r + 1 - 2) * (n - 1) ≤ 2 * (contractEdge G x y).edgeSet.ncard := by
      rw [hD]
      have hn' : n = (n - 1) + 1 := by omega
      rw [hn', mul_add_one] at hE
      have : 2 * 2 ^ (r - 2) * (n - 1 + 1 - 1) = 2 * 2 ^ (r - 2) * (n - 1) := by
        congr 1
      omega
    exact (ihn (n - 1) (by omega) {v // v ≠ y} (contractEdge G x y) hcard (by omega)
      hE').trans (isMinor_contractEdge hxy)
  · -- Every edge has many common neighbours: use a neighbourhood.
    have hall : ∀ x y, G.Adj x y → 2 ^ (r - 2) ≤ (G.neighborSet x ∩ G.neighborSet y).ncard :=
      fun x y hxy => not_lt.mp fun h => hcon ⟨x, y, hxy, h⟩
    have hEpos : 0 < G.edgeSet.ncard := by
      have : 0 < 2 * 2 ^ (r - 2) * n := by positivity
      omega
    obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite _)).mp hEpos
    induction e using Sym2.ind with
    | h x y₀ =>
    have hxy₀ : G.Adj x y₀ := G.mem_edgeSet.mp he
    set s := G.neighborSet x
    have hs1 : 1 ≤ Fintype.card s := Fintype.card_pos_iff.mpr ⟨⟨y₀, hxy₀⟩⟩
    have hEs : 2 ^ (r - 2) * Fintype.card s ≤ 2 * (G.induce s).edgeSet.ncard := by
      rw [two_mul_ncard_edgeSet, mul_comm, ← smul_eq_mul, ← Finset.card_univ]
      refine Finset.card_nsmul_le_sum _ _ _ fun y _ => ?_
      rw [ncard_neighborSet_induce_neighborSet]
      exact hall x y y.2
    exact isMinor_top_succ_of_induce_neighborSet (ih s (G.induce s) hs1 hEs)

/-- **Mader's theorem** (Diestel, *Graph Theory*, Proposition 7.2.1): for `r ≥ 2`, a graph on
`v ≥ 1` vertices with `2^(r-2)·v ≤ 2|E|`, that is of average degree at least `2^(r-2)`, has a
`K_r` minor. -/
theorem isMinor_top_of_le {r : ℕ} (hr : 2 ≤ r) {V : Type} [Fintype V] {G : SimpleGraph V}
    (hV : 1 ≤ Fintype.card V) (hE : 2 ^ (r - 2) * Fintype.card V ≤ 2 * G.edgeSet.ncard) :
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  induction r, hr using Nat.le_induction generalizing V with
  | base =>
    have hEpos : 0 < G.edgeSet.ncard := by
      simp only [Nat.sub_self, pow_zero, one_mul] at hE
      omega
    obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite _)).mp hEpos
    induction e using Sym2.ind with
    | h a b => exact isMinor_top_two_of_adj (G.mem_edgeSet.mp he)
  | succ r hr ih =>
    exact mader_step hr (fun V _ G => ih) _ V G rfl hV hE

/-- **Graphs without a `K_r` minor have at most `2^r·v` edges**, for every `r`. -/
theorem ncard_edgeSet_le_of_not_isMinor (r : ℕ) {V : Type} [Fintype V] {G : SimpleGraph V}
    (h : ¬IsMinor (⊤ : SimpleGraph (Fin r)) G) : G.edgeSet.ncard ≤ 2 ^ r * Fintype.card V := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hV | hV
  · -- No vertices, no edges.
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    have hE0 : G.edgeSet = ∅ := Set.eq_empty_of_forall_notMem fun e => by
      induction e using Sym2.ind with
      | h a b => exact isEmptyElim a
    rw [hE0, Set.ncard_empty]
    exact Nat.zero_le _
  rcases lt_or_ge r 2 with hr | hr
  · -- `K₀` and `K₁` are minors of every nonempty graph.
    exfalso
    obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hV
    refine h ⟨.ofInjective ⟨fun _ => v₀, fun {i j} hij => ?_⟩ fun i j _ => ?_⟩
    · exact absurd (Subsingleton.elim (h := by
        rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> infer_instance) i j) hij.ne
    · rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · exact i.elim0
      · exact Subsingleton.elim i j
  · by_contra hlt
    have hle : 2 ^ (r - 2) * Fintype.card V ≤ 2 * G.edgeSet.ncard := by
      have h4 : 2 ^ r = 2 ^ (r - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      have : 2 ^ r * Fintype.card V < G.edgeSet.ncard := not_le.mp hlt
      rw [h4] at this
      nlinarith
    exact h (isMinor_top_of_le hr hV hle)

end Mader

/-! ## Minor-closed classes -/

/-- **A minor-closed class** of graphs on finite vertex types: a minor of a member is a member.
In particular the class is closed under isomorphism. -/
def IsMinorClosed (P : ∀ V : Type, SimpleGraph V → Prop) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W},
    IsMinor H G → P V G → P W H

/-- **A proper class**: some graph on a finite vertex type is not a member. -/
def IsProperClass (P : ∀ V : Type, SimpleGraph V → Prop) : Prop :=
  ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W), ¬P W H

/-- **Every proper minor-closed class has a linear edge bound** (`sec:graph-certificates`): a
graph `H` outside the class on `t` vertices is a minor of `K_t`, so no member has a `K_t` minor,
and the members have at most `2^t·v` edges. -/
theorem IsMinorClosed.exists_ncard_edgeSet_le {P : ∀ V : Type, SimpleGraph V → Prop}
    (hP : IsMinorClosed P) (hprop : IsProperClass P) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), P V G →
      G.edgeSet.ncard ≤ C * Fintype.card V := by
  obtain ⟨W, _, H, hH⟩ := hprop
  have := Fintype.ofFinite W
  refine ⟨2 ^ Fintype.card W, fun V _ G hG => ncard_edgeSet_le_of_not_isMinor _ fun hmin => hH ?_⟩
  have hK : P (Fin (Fintype.card W)) ⊤ := hP hmin hG
  exact hP (isMinor_top_of_equiv (Fintype.equivFin W)) hK

end MonoidProduct.Graph
