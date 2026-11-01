import MonoidProduct.Graph.CycleArcs
import MonoidProduct.Graph.VertexReadouts
set_option linter.style.header false

/-!
# Connectivity, separations and marker edges

Graph-level connectivity and separations, for the converse of Wagner's theorem.

* `NoKuratowskiMinor G`: neither `K₅` nor `K₃,₃` is a minor of `G`; minors inherit it, by
  transitivity of minors (`NoKuratowskiMinor.of_isMinor`).
* `IsKConnected G k`: more than `k` vertices, and connected after deleting any fewer than `k`
  vertices, the convention of the Boolean `isVertexConnected` (`Graph/VertexReadouts.lean`), with
  which it agrees on edge sets (`isVertexConnected_eq_true_iff_isKConnected`).  It is monotone in
  `k`; every vertex has at least `k` neighbours (`IsKConnected.le_ncard_neighborSet`); deleting a
  vertex of a `(k + 1)`-connected graph leaves a `k`-connected graph (`IsKConnected.induce_ne`).
  `induceInduceIso` identifies an induced subgraph of an induced subgraph with an induced
  subgraph, so that successive deletions stay on vertex types of `V`.
* A graph with more than `k` vertices that is not `k`-connected has a **minimum separator**: a set
  of fewer than `k` vertices whose deletion disconnects it, such that deleting fewer vertices never
  does (`exists_minimum_separator`).
* `IsProperSeparation G A B`: `A ∪ B` is everything, no edge joins `A \ B` to `B \ A`, and both
  are nonempty; the separator is `A ∩ B`, and edges may meet it.  A separator gives one, with one
  component of the rest on one side (`exists_isProperSeparation`).  Both sides have fewer vertices
  than `G`.  **Every vertex of a minimum separator has a neighbour in every component of the
  rest** (`exists_adj_reachable`).
* **Marker edges**: for a proper separation of a `2`-connected graph with separator `{x, y}`, each
  side with the edge `xy` added is a minor of `G`, whether or not `xy` is an edge
  (`isMinor_sup_edge_induce_left`, `isMinor_sup_edge_induce_right`): the branch set of `x` takes a
  component on the other side, which reaches both `x` and `y`.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V}

/-! ## The excluded minors -/

/-- **Neither `K₅` nor `K₃,₃` is a minor of `G`.** -/
def NoKuratowskiMinor (G : SimpleGraph V) : Prop :=
  ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G ∧ ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G

/-- **Minors inherit the exclusions**, by transitivity of minors. -/
theorem NoKuratowskiMinor.of_isMinor {H : SimpleGraph W} (hG : NoKuratowskiMinor G)
    (hHG : IsMinor H G) : NoKuratowskiMinor H :=
  ⟨fun h => hG.1 (h.trans hHG), fun h => hG.2 (h.trans hHG)⟩

/-! ## Reachability helpers -/

/-- Reachability in the graph induced on `s` is reachability along edges inside `s`. -/
theorem reachable_induce_iff_restrictTo {s : Set V} {a b : V} (ha : a ∈ s) (hb : b ∈ s) :
    (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩ ↔ (restrictTo G s).Reachable a b :=
  reachable_induce_iff (fun _ _ => Iff.rfl) ha hb

/-- **Reachability stays in a closed set**: if every edge of `H` starting in `D` ends in `D`, then
everything reachable from `D` is in `D`. -/
theorem mem_of_reachable_of_forall_adj {H : SimpleGraph V} {D : Set V}
    (hD : ∀ ⦃a b⦄, H.Adj a b → a ∈ D → b ∈ D) {u w : V} (h : H.Reachable u w) (hu : u ∈ D) :
    w ∈ D := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hab ih => exact hD hab ih

/-- **A component is connected**: the vertices reachable from `u` along edges inside `s` form a
connected set. -/
theorem isConnectedSet_setOf_reachable {s : Set V} {u : V} (hu : u ∈ s) :
    IsConnectedSet G {d | d ∈ s ∧ (restrictTo G s).Reachable u d} := by
  set D := {d | d ∈ s ∧ (restrictTo G s).Reachable u d}
  -- Walks from `u` inside `s` stay in the component.
  have hlift : ∀ {d}, (restrictTo G s).Reachable u d → (restrictTo G D).Reachable u d := by
    intro d hd
    have hd' := hd
    rw [reachable_iff_reflTransGen] at hd'
    induction hd' with
    | refl => rfl
    | @tail c e hc hce ih =>
      have hcD : c ∈ D := ⟨hce.2.1, (reachable_iff_reflTransGen _ _).mpr hc⟩
      have heD : e ∈ D := ⟨hce.2.2, ((reachable_iff_reflTransGen _ _).mpr hc).trans hce.reachable⟩
      exact (ih ((reachable_iff_reflTransGen _ _).mpr hc)).trans
        (restrictTo_adj.mpr ⟨hce.1, hcD, heD⟩).reachable
  exact ⟨⟨u, hu, .rfl⟩, fun a ha b hb => (hlift ha.2).symm.trans (hlift hb.2)⟩

/-! ## Inducing twice -/

/-- **Inducing twice is inducing once**: the graph induced on `t ⊆ s` inside the graph induced on
`s` is the graph induced on the vertices of `t`. -/
def induceInduceIso (G : SimpleGraph V) {s : Set V} {t : Set s} {u : Set V}
    (h : ∀ v, v ∈ u ↔ ∃ hv : v ∈ s, (⟨v, hv⟩ : s) ∈ t) :
    (G.induce s).induce t ≃g G.induce u where
  toFun x := ⟨x.1.1, (h _).mpr ⟨x.1.2, x.2⟩⟩
  invFun y := ⟨⟨y.1, ((h _).mp y.2).1⟩, ((h _).mp y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- **Deleting two vertices one at a time.** -/
def deleteDeleteIso (G : SimpleGraph V) (x y : V) :
    (G.induce {v | v ≠ x}).induce {u | u.1 ≠ y} ≃g G.induce {v | v ≠ x ∧ v ≠ y} :=
  induceInduceIso G fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

/-! ## `k`-connectivity -/

/-- **`k`-connectivity**: more than `k` vertices, and connected after deleting any fewer than `k`
vertices. -/
def IsKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Nat.card V ∧ ∀ S : Finset V, S.card < k → (G.induce {v | v ∉ S}).Connected

/-- **The Boolean readout agrees**: `isVertexConnected k` of an edge set is `k`-connectivity of
its graph. -/
theorem isVertexConnected_eq_true_iff_isKConnected [Fintype V] [DecidableEq V] {k : ℕ}
    {S : Finset (Edge V)} : isVertexConnected k S = true ↔ IsKConnected (toGraph S) k := by
  rw [isVertexConnected_eq_true_iff, IsKConnected, Nat.card_eq_fintype_card]

theorem IsKConnected.mono {j k : ℕ} (h : IsKConnected G k) (hjk : j ≤ k) : IsKConnected G j :=
  ⟨lt_of_le_of_lt hjk h.1, fun S hS => h.2 S (lt_of_lt_of_le hS hjk)⟩

/-- A `k`-connected graph is connected for `k ≥ 1`. -/
theorem IsKConnected.connected {k : ℕ} (h : IsKConnected G k) (hk : 0 < k) : G.Connected := by
  have hc := h.2 ∅ (by simpa using hk)
  rw [show {v | v ∉ (∅ : Finset V)} = (Set.univ : Set V) by ext; simp] at hc
  exact (induceUnivIso G).connected_iff.mp hc

/-- **Every vertex of a `k`-connected graph has at least `k` neighbours**: deleting fewer
neighbours would isolate it from the other remaining vertices. -/
theorem IsKConnected.le_ncard_neighborSet [Finite V] {k : ℕ} (h : IsKConnected G k) (v : V) :
    k ≤ (G.neighborSet v).ncard := by
  classical
  have := Fintype.ofFinite V
  by_contra hlt
  push Not at hlt
  set S := (G.neighborSet v).toFinset
  have hS : S.card < k := by rwa [← Set.ncard_eq_toFinset_card']
  have hv : v ∉ S := by simp [S]
  -- Another vertex survives the deletion.
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := insert v S)
    (t := Finset.univ) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      have := Finset.card_insert_le v S
      have := h.1
      omega)
  have hwS : w ∉ S := fun h' => hw (Finset.mem_insert_of_mem h')
  have hwv : w ≠ v := fun h' => hw (h' ▸ Finset.mem_insert_self v S)
  obtain ⟨p⟩ := (h.2 S hS).preconnected ⟨v, hv⟩ ⟨w, hwS⟩
  cases p with
  | nil => exact hwv rfl
  | @cons _ u' _ hadj _ =>
    exact u'.2 (by simpa [S] using hadj)

/-- **Deleting a vertex of a `(k + 1)`-connected graph leaves a `k`-connected graph.** -/
theorem IsKConnected.induce_ne [Finite V] {k : ℕ} (h : IsKConnected G (k + 1)) (z : V) :
    IsKConnected (G.induce {v | v ≠ z}) k := by
  classical
  refine ⟨?_, fun S' hS' => ?_⟩
  · have hc := Set.ncard_add_ncard_compl ({z} : Set V)
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq (({z} : Set V)ᶜ)] at hc
    have : Nat.card ↥(({z} : Set V)ᶜ) = Nat.card ↥{v | v ≠ z} := rfl
    have := h.1
    omega
  · have hS : (insert z (S'.map (Function.Embedding.subtype _))).card < k + 1 := by
      have := Finset.card_insert_le z (S'.map (Function.Embedding.subtype _))
      rw [Finset.card_map] at this
      omega
    refine (induceInduceIso G fun v => ?_).connected_iff.mpr (h.2 _ hS)
    simp only [Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_map,
      Function.Embedding.subtype_apply, not_or, not_exists, not_and]
    constructor
    · rintro ⟨hvz, hv⟩
      exact ⟨hvz, fun h' => hv ⟨v, hvz⟩ h' rfl⟩
    · rintro ⟨hvz, hv⟩
      exact ⟨hvz, fun u hu huv => hv (by subst huv; exact hu)⟩

/-- **A minimum separator**: a graph with more than `k` vertices that is not `k`-connected has a
set of fewer than `k` vertices whose deletion disconnects it, such that the graph is
`|S|`-connected, that is, deleting fewer vertices never disconnects it. -/
theorem exists_minimum_separator {k : ℕ} (hk : k < Nat.card V) (h : ¬ IsKConnected G k) :
    ∃ S : Finset V, S.card < k ∧ ¬ (G.induce {v | v ∉ S}).Connected ∧ IsKConnected G S.card := by
  classical
  unfold IsKConnected at h
  push Not at h
  obtain ⟨S₀, hS₀, hnc₀⟩ := h hk
  have hex : ∃ j, ∃ S : Finset V, S.card = j ∧ ¬ (G.induce {v | v ∉ S}).Connected :=
    ⟨_, S₀, rfl, hnc₀⟩
  obtain ⟨S, hSj, hnc⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ S₀.card := Nat.find_min' hex ⟨S₀, rfl, hnc₀⟩
  refine ⟨S, by omega, hnc, by omega, fun T hT => ?_⟩
  by_contra hT'
  exact Nat.find_min hex (hSj ▸ hT) ⟨T, rfl, hT'⟩

/-! ## Proper separations -/

/-- **A proper separation** of `G`: the sides `A` and `B` cover all vertices, no edge joins
`A \ B` to `B \ A`, and both of those are nonempty.  The separator is `A ∩ B`; edges may meet it. -/
structure IsProperSeparation (G : SimpleGraph V) (A B : Set V) : Prop where
  union_eq : A ∪ B = Set.univ
  not_adj : ∀ ⦃u w : V⦄, u ∈ A \ B → w ∈ B \ A → ¬ G.Adj u w
  nonempty_left : (A \ B).Nonempty
  nonempty_right : (B \ A).Nonempty

namespace IsProperSeparation

variable {A B : Set V}

theorem symm (h : IsProperSeparation G A B) : IsProperSeparation G B A :=
  ⟨by rw [Set.union_comm]; exact h.union_eq, fun _ _ hu hw huw => h.not_adj hw hu huw.symm,
    h.nonempty_right, h.nonempty_left⟩

/-- **The left side has fewer vertices than `G`.** -/
theorem natCard_lt_left [Finite V] (h : IsProperSeparation G A B) : Nat.card A < Nat.card V := by
  obtain ⟨b, -, hb⟩ := h.nonempty_right
  rw [Nat.card_coe_set_eq, ← Set.ncard_univ]
  exact Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr fun hA => hb (hA ▸ Set.mem_univ b))

/-- **The right side has fewer vertices than `G`.** -/
theorem natCard_lt_right [Finite V] (h : IsProperSeparation G A B) : Nat.card B < Nat.card V :=
  h.symm.natCard_lt_left

/-- **Away from the separator, one stays on one side**: walks avoiding `A ∩ B` from `B \ A` stay
in `B \ A`. -/
theorem mem_of_reachable (h : IsProperSeparation G A B) {u w : V}
    (hr : (restrictTo G {v | v ∉ A ∩ B}).Reachable u w) (hu : u ∈ B \ A) : w ∈ B \ A := by
  refine mem_of_reachable_of_forall_adj (fun a b hab ha => ?_) hr hu
  obtain ⟨hab, -, hbS⟩ := hab
  have hb : b ∈ A ∪ B := h.union_eq ▸ Set.mem_univ b
  by_cases hbA : b ∈ A
  · have hbB : b ∉ B := fun hbB => hbS ⟨hbA, hbB⟩
    exact absurd hab.symm (h.not_adj ⟨hbA, hbB⟩ ha)
  · exact ⟨hb.resolve_left hbA, hbA⟩

/-- **The separator separates**: no walk avoiding `A ∩ B` joins `A \ B` to `B \ A`. -/
theorem not_reachable (h : IsProperSeparation G A B) {u w : V} (hu : u ∈ A \ B) (hw : w ∈ B \ A) :
    ¬ (restrictTo G {v | v ∉ A ∩ B}).Reachable w u := fun hr =>
  (h.mem_of_reachable hr hw).2 hu.1

end IsProperSeparation

/-- **A separator gives a proper separation**, with the component of one vertex on one side,
the other components on the other, and the separator in both. -/
theorem exists_isProperSeparation (S : Finset V) (hS : ¬ (G.induce {v | v ∉ S}).Connected)
    {u : V} (hu : u ∉ S) : ∃ A B : Set V, IsProperSeparation G A B ∧ A ∩ B = ↑S := by
  set s : Set V := {v | v ∉ S}
  set D : Set V := {d | d ∈ s ∧ (restrictTo G s).Reachable u d}
  -- Some vertex outside `S` is not reachable from `u`.
  have hfar : ∃ w, w ∉ S ∧ ¬ (restrictTo G s).Reachable u w := by
    by_contra hall
    push Not at hall
    refine hS ((connected_iff _).mpr ⟨fun a b => ?_, ⟨⟨u, hu⟩⟩⟩)
    rw [reachable_induce_iff_restrictTo]
    exact (hall a.1 a.2).symm.trans (hall b.1 b.2)
  obtain ⟨w, hwS, hw⟩ := hfar
  refine ⟨↑S ∪ D, Dᶜ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · ext v
    by_cases hv : v ∈ D <;> simp [hv]
  · rintro a b ⟨-, haD⟩ ⟨hbD, hbA⟩ hab
    have haD' : a ∈ D := not_not.mp haD
    have hbS : b ∉ S := fun h' => hbA (Or.inl h')
    exact hbD ⟨hbS, haD'.2.trans (restrictTo_adj.mpr ⟨hab, haD'.1, hbS⟩).reachable⟩
  · exact ⟨u, Or.inr ⟨hu, .rfl⟩, fun h' => h' ⟨hu, .rfl⟩⟩
  · exact ⟨w, fun h' => hw h'.2, fun h' => h'.elim (fun h'' => hwS h'') fun h'' => hw h''.2⟩
  · ext v
    constructor
    · rintro ⟨hv | hv, hvD⟩
      · exact hv
      · exact absurd hv hvD
    · intro hv
      exact ⟨Or.inl hv, fun h' => h'.1 hv⟩

/-- **Every vertex of a minimum separator has a neighbour in every component of the rest**: if
`s ∈ S` had no neighbour reachable from `v` avoiding `S`, then `S` without `s` would still cut `v`
off from `s`, although the graph is `|S|`-connected. -/
theorem exists_adj_reachable {S : Finset V} (hmin : IsKConnected G S.card)
    {s v : V} (hs : s ∈ S) (hv : v ∉ S) :
    ∃ d, d ∉ S ∧ (restrictTo G {w | w ∉ S}).Reachable v d ∧ G.Adj s d := by
  classical
  by_contra hno
  push Not at hno
  set T := S.erase s
  have hvT : v ∉ T := fun h => hv (Finset.mem_of_mem_erase h)
  have hsT : s ∉ T := Finset.notMem_erase s S
  have hr := (reachable_induce_iff_restrictTo hvT hsT).mp
    ((hmin.2 T (Finset.card_erase_lt_of_mem hs)).preconnected ⟨v, hvT⟩ ⟨s, hsT⟩)
  have hclosed : ∀ ⦃a b⦄, (restrictTo G {w | w ∉ T}).Adj a b →
      a ∈ {d | d ∉ S ∧ (restrictTo G {w | w ∉ S}).Reachable v d} →
      b ∈ {d | d ∉ S ∧ (restrictTo G {w | w ∉ S}).Reachable v d} := by
    rintro a b ⟨hab, -, hbT⟩ ⟨haS, hra⟩
    by_cases hbs : b = s
    · subst hbs
      exact absurd hab.symm (hno a haS hra)
    · have hbS : b ∉ S := fun h => hbT (Finset.mem_erase.mpr ⟨hbs, h⟩)
      exact ⟨hbS, hra.trans (restrictTo_adj.mpr ⟨hab, haS, hbS⟩).reachable⟩
  exact (mem_of_reachable_of_forall_adj hclosed hr ⟨hv, .rfl⟩).1 hs

/-! ## Marker edges -/

section Marker

variable {A B : Set V} {x y : V}

/-- **The marker-edge model**: the branch set of `x` is `x` together with a component on the other
side, and every other vertex of `A` is its own branch set. -/
private theorem isMinor_sup_edge_induce_left_aux (h2 : IsKConnected G 2)
    (hAB : IsProperSeparation G A B) (hxy : x ≠ y) (hS : A ∩ B = {x, y}) :
    IsMinor ((G ⊔ edge x y).induce A) G := by
  classical
  set S : Finset V := {x, y}
  have hSc : S.card = 2 := Finset.card_pair hxy
  have hmin : IsKConnected G S.card := hSc ▸ h2
  have hset : {w : V | w ∉ S} = {w | w ∉ A ∩ B} := by
    ext w
    simp [S, hS]
  have hxA : x ∈ A := (hS.symm ▸ Set.mem_insert x {y} : x ∈ A ∩ B).1
  have hyA : y ∈ A := (hS.symm ▸ Set.mem_insert_of_mem x rfl : y ∈ A ∩ B).1
  obtain ⟨b₀, hb₀B, hb₀A⟩ := hAB.nonempty_right
  have hb₀S : b₀ ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl) <;> contradiction
  -- The component `D` of `b₀` avoiding `x` and `y`: connected, on the other side, and reaching
  -- both `x` and `y`.
  set D : Set V := {d | d ∈ {w | w ∉ S} ∧ (restrictTo G {w | w ∉ S}).Reachable b₀ d}
  have hDconn : IsConnectedSet G D := isConnectedSet_setOf_reachable (s := {w | w ∉ S}) hb₀S
  have hDB : ∀ d ∈ D, d ∉ A := fun d hd =>
    (hAB.mem_of_reachable (hset ▸ hd.2) ⟨hb₀B, hb₀A⟩).2
  obtain ⟨dx, hdxS, hdx, hxdx⟩ := exists_adj_reachable hmin (s := x) (by simp [S]) hb₀S
  obtain ⟨dy, hdyS, hdy, hydy⟩ := exists_adj_reachable hmin (s := y) (by simp [S]) hb₀S
  have hdxD : dx ∈ D := ⟨hdxS, hdx⟩
  have hdyD : dy ∈ D := ⟨hdyS, hdy⟩
  let branch : A → Set V := fun a => if a.1 = x then insert x D else {a.1}
  have hself : ∀ a : A, a.1 ∈ branch a := fun a => by
    by_cases ha : a.1 = x
    · simp only [branch, ha, ite_true]
      exact Set.mem_insert x D
    · simp only [branch, ha, ite_false, Set.mem_singleton_iff]
  have hbx : ∀ a : A, a.1 = x → D ⊆ branch a := fun a ha => by
    simp only [branch, ha, ite_true]
    exact Set.subset_insert x D
  refine ⟨MinorModel.mk branch (fun a => ?_) (fun a a' haa => ?_) (fun a a' haa => ?_)⟩
  · by_cases ha : a.1 = x
    · simp only [branch, ha, ite_true]
      exact hDconn.insert_of_adj hdxD hxdx
    · simp only [branch, ha, ite_false]
      exact isConnectedSet_singleton G a.1
  · have hne : a.1 ≠ a'.1 := fun h => haa (Subtype.ext h)
    by_cases ha : a.1 = x <;> by_cases ha' : a'.1 = x
    · exact absurd (ha.trans ha'.symm) hne
    · rw [show branch a = insert x D from ite_eq_left ha,
        show branch a' = {a'.1} from ite_eq_right ha', Set.disjoint_singleton_right,
        Set.mem_insert_iff, not_or]
      exact ⟨ha', fun h => hDB _ h a'.2⟩
    · rw [show branch a = {a.1} from ite_eq_right ha,
        show branch a' = insert x D from ite_eq_left ha', Set.disjoint_singleton_left,
        Set.mem_insert_iff, not_or]
      exact ⟨ha, fun h => hDB _ h a.2⟩
    · simp only [branch, ha, ha', ite_false, Set.disjoint_singleton]
      exact hne
  · change (G ⊔ edge x y).Adj a.1 a'.1 at haa
    rw [sup_adj, edge_adj] at haa
    rcases haa with h | ⟨⟨hax, hay⟩ | ⟨hay, hax⟩, -⟩
    · exact ⟨a.1, hself a, a'.1, hself a', h⟩
    · refine ⟨dy, hbx a hax hdyD, a'.1, hself a', ?_⟩
      rw [hay]
      exact hydy.symm
    · refine ⟨a.1, hself a, dy, hbx a' hax hdyD, ?_⟩
      rw [hay]
      exact hydy

/-- **The left side with the marker edge is a minor**: for a proper separation of a
`2`-connected graph with separator `{x, y}`, the graph induced on `A`, with the edge `xy` added
whether or not it was there, is a minor of `G`. -/
theorem isMinor_sup_edge_induce_left (h2 : IsKConnected G 2) (hAB : IsProperSeparation G A B)
    (hxy : x ≠ y) (hS : A ∩ B = {x, y}) : IsMinor ((G ⊔ edge x y).induce A) G :=
  isMinor_sup_edge_induce_left_aux h2 hAB hxy hS

/-- **The right side with the marker edge is a minor.** -/
theorem isMinor_sup_edge_induce_right (h2 : IsKConnected G 2) (hAB : IsProperSeparation G A B)
    (hxy : x ≠ y) (hS : A ∩ B = {x, y}) : IsMinor ((G ⊔ edge x y).induce B) G :=
  isMinor_sup_edge_induce_left_aux h2 hAB.symm hxy (by rw [Set.inter_comm]; exact hS)

end Marker

end MonoidProduct.Graph
