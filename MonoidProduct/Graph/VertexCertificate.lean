import MonoidProduct.Graph.EdgeFaults
import MonoidProduct.Graph.VertexFaults
set_option linter.style.header false

/-!
# The vertex-failure certificate

`monoid.tex`, section `sec:failure-profiles`, paragraph "Vertex failures": the classical sparse
connectivity-certificate theorem gives every graph `G` a subgraph `H ⊆ G` with `O(kv)` edges and
`π(H − X) = π(G − X)` for every set `X` of fewer than `k` vertices.  The paper cites Nagamochi and
Ibaraki, and Parter and Tzalik for the formulation that preserves all residual components.  Here
it is proved for every `k` with the explicit bound `|H| ≤ 2kv`.  Write `v = #V` and
`N = C(v, 2)`.

* **The profile through edge sets.**  `edgesWithin W S` holds the edges of `S` with both ends in
  `W`; for `W = V \ X` they are the edges of `G − X`.  The coordinate of `Σ^V_k(S)` at `X`
  relates `u` and `w` exactly when both survive and they are connected in
  `toGraph (edgesWithin Xᶜ S)` (`mem_vertexFailureProfile_iff_edgesWithin`), a graph on all of
  `V` in which the vertices of `X` are isolated.  Restricting to `V \ X` commutes with union, so
  the profile of a union is determined by the profiles of its parts
  (`vertexFailureProfile_union_congr`).  Equivalence under extensions is therefore equality of
  profiles (`extensionEquiv_vertexFailureProfile_iff`), and a subgraph with the same profile is
  a strong certificate (`isStrongCertificate_vertexFailureProfile`).
* **The greedy certificate** (`greedyCert k S`).  The edges of `S` are processed in a fixed
  order, and an edge is kept exactly when it is `Separable` in the edges kept so far: some set of
  fewer than `k` vertices, avoiding both of its ends, separates them.  An edge that is left out
  has its ends connected after every such deletion, in the kept edges and hence in the final
  certificate.  So the profile is preserved (`vertexFailureProfile_greedyCert`).
* **Its size** (`card_le_of_blocking`).  Every nonempty set `T` of kept edges contains an edge
  that is separable in `T` without it, namely the last one kept (`Blocking`,
  `blocking_greedyCert`).  A blocking edge set has at most `2kv` edges.  The proof is the
  counting argument of Diestel's proof of Mader's theorem.  Take a vertex set `W` of least size
  with `|W| ≥ 2k` and more than `2k(|W| - k)` edges inside it.  Then `|W| ≠ 2k`, and every vertex
  of `W` has more than `2k` edges inside `W`.  The blocking property gives an edge `uw` inside
  `W` and a set `X` of fewer than `k` vertices separating `u` from `w` without that edge.  Let `C`
  be the vertices of `W \ X` connected to `u` without `X` and that edge.  Then
  `U₁ = C ∪ {w} ∪ (X ∩ W)` and `U₂ = W \ C` meet in at most `k` vertices, every edge inside `W`
  lies inside one of them, and the degrees make both of them smaller candidates.  Their edge
  counts then add up to at most `2k(|W| - k)` (`card_edgesWithin_le_of_blocking`).
* `vertexFailureProfile_strongCertificateSize_le`: `b_{Σ^V_k} ≤ min{N, 2kv}`, for every `k` and
  every `v`.  Truncation, `k = 0` and `k = 1` are restated for certificate sizes.

The paper prescribes no construction.  This is not Nagamochi and Ibaraki's scan-first search: the
greedy construction proves the cited statement directly, with the constant `2`.
-/

namespace MonoidProduct.Graph

open SimpleGraph Certificates

/-! ## Edges inside a vertex set -/

section Within

variable {V : Type*}

/-- **The edges of `S` inside `W`**: those with both ends in `W`.  For `W = V \ X` they are the
edges of `G − X`. -/
noncomputable def edgesWithin (W : Finset V) (S : Finset (Edge V)) : Finset (Edge V) := by
  classical exact S.filter fun e => ∀ z ∈ (e : Sym2 V), z ∈ W

theorem mem_edgesWithin {W : Finset V} {S : Finset (Edge V)} {e : Edge V} :
    e ∈ edgesWithin W S ↔ e ∈ S ∧ ∀ z ∈ (e : Sym2 V), z ∈ W := by
  classical
  unfold edgesWithin
  exact Finset.mem_filter

/-- An edge `s(a, b)` lies inside `W` when both `a` and `b` do. -/
theorem mem_edgesWithin_of_eq {W : Finset V} {S : Finset (Edge V)} {e : Edge V} {a b : V}
    (he : (e : Sym2 V) = s(a, b)) : e ∈ edgesWithin W S ↔ e ∈ S ∧ a ∈ W ∧ b ∈ W := by
  rw [mem_edgesWithin, he, Sym2.ball]

theorem edgesWithin_subset (W : Finset V) (S : Finset (Edge V)) : edgesWithin W S ⊆ S :=
  fun _ he => (mem_edgesWithin.mp he).1

theorem edgesWithin_mono {W W' : Finset V} {S S' : Finset (Edge V)} (hW : W ⊆ W')
    (hS : S ⊆ S') : edgesWithin W S ⊆ edgesWithin W' S' := fun e he => by
  obtain ⟨heS, heW⟩ := mem_edgesWithin.mp he
  exact mem_edgesWithin.mpr ⟨hS heS, fun z hz => hW (heW z hz)⟩

/-- Adjacency through the edges inside `W`. -/
theorem toGraph_edgesWithin_adj {W : Finset V} {S : Finset (Edge V)} {a b : V} :
    (toGraph (edgesWithin W S)).Adj a b ↔ (toGraph S).Adj a b ∧ a ∈ W ∧ b ∈ W := by
  rw [toGraph_adj, toGraph_adj]
  constructor
  · rintro ⟨e, he, hab⟩
    obtain ⟨heS, ha, hb⟩ := (mem_edgesWithin_of_eq hab).mp he
    exact ⟨⟨e, heS, hab⟩, ha, hb⟩
  · rintro ⟨⟨e, heS, hab⟩, ha, hb⟩
    exact ⟨e, (mem_edgesWithin_of_eq hab).mpr ⟨heS, ha, hb⟩, hab⟩

/-- Restricting to `W` commutes with union. -/
theorem edgesWithin_union [DecidableEq V] (W : Finset V) (S T : Finset (Edge V)) :
    edgesWithin W (S ∪ T) = edgesWithin W S ∪ edgesWithin W T := by
  ext e
  simp only [mem_edgesWithin, Finset.mem_union]
  tauto

/-- All edges lie inside `V`. -/
theorem edgesWithin_univ [Fintype V] (S : Finset (Edge V)) : edgesWithin Finset.univ S = S := by
  ext e
  simp only [mem_edgesWithin, Finset.mem_univ, implies_true, and_true]

/-! ### Reachability in induced graphs -/

/-- A walk along edges whose second ends lie in `s`, starting in `s`, stays in `s`; it gives a
path of the graph induced on `s`. -/
theorem exists_reachable_induce_of_walk {G G' : SimpleGraph V} {s : Set V}
    (hG : ∀ a b, G'.Adj a b → G.Adj a b ∧ b ∈ s) :
    ∀ {a b : V} (_ : G'.Walk a b) (ha : a ∈ s),
      ∃ hb : b ∈ s, (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩
  | _, _, .nil, ha => ⟨ha, Reachable.rfl⟩
  | _, _, @Walk.cons _ _ a c _ h p, ha => by
      obtain ⟨hadj, hc⟩ := hG a c h
      obtain ⟨hb, hr⟩ := exists_reachable_induce_of_walk hG p hc
      have hadj' : (G.induce s).Adj ⟨a, ha⟩ ⟨c, hc⟩ := hadj
      exact ⟨hb, hadj'.reachable.trans hr⟩

/-- **The graph induced on `s` and the edges inside `s`**: if `G'` has exactly the edges of `G`
with both ends in `s`, then the two have the same reachability on `s`. -/
theorem reachable_induce_iff {G G' : SimpleGraph V} {s : Set V}
    (hG : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s) {a b : V} (ha : a ∈ s) (hb : b ∈ s) :
    (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩ ↔ G'.Reachable a b := by
  constructor
  · intro h
    exact h.map (⟨Subtype.val, fun {x y} hxy => (hG x y).mpr ⟨hxy, x.2, y.2⟩⟩ : G.induce s →g G')
  · rintro ⟨p⟩
    obtain ⟨_, h⟩ := exists_reachable_induce_of_walk
      (fun x y hxy => ⟨((hG x y).mp hxy).1, ((hG x y).mp hxy).2.2⟩) p ha
    exact h

end Within

/-! ## The profile through edge sets -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency in `G − X`, through the edges avoiding `X`. -/
theorem toGraph_edgesWithin_compl_adj {X : Finset V} {S : Finset (Edge V)} {a b : V} :
    (toGraph (edgesWithin Xᶜ S)).Adj a b ↔ (toGraph S).Adj a b ∧ a ∉ X ∧ b ∉ X := by
  rw [toGraph_edgesWithin_adj, Finset.mem_compl, Finset.mem_compl]

/-- The vertices of `X` are isolated in `toGraph (edgesWithin Xᶜ S)`. -/
theorem eq_of_reachable_edgesWithin_compl {X : Finset V} {S : Finset (Edge V)} {u w : V}
    (hu : u ∈ X) (h : (toGraph (edgesWithin Xᶜ S)).Reachable u w) : w = u :=
  eq_of_reachable_of_forall_not_adj (fun _ hz => (toGraph_edgesWithin_compl_adj.mp hz).2.1 hu) h

/-- **Reachability in `G − X` through edge sets**: two surviving vertices are connected in the
graph induced on `V \ X` exactly when they are connected using the edges avoiding `X`. -/
theorem reachable_induce_compl_iff {X : Finset V} {S : Finset (Edge V)} {u w : V} (hu : u ∉ X)
    (hw : w ∉ X) : ((toGraph S).induce {z | z ∉ X}).Reachable ⟨u, hu⟩ ⟨w, hw⟩ ↔
      (toGraph (edgesWithin Xᶜ S)).Reachable u w :=
  reachable_induce_iff (fun _ _ => toGraph_edgesWithin_compl_adj) hu hw

/-- **The vertex profile through edge sets**: the coordinate at `X` relates `u` and `w` exactly
when both survive and they are connected using the edges of `S` that avoid `X`. -/
theorem mem_vertexFailureProfile_iff_edgesWithin {k : ℕ} {S : Finset (Edge V)}
    {X : VertexFailureSet V k} {u w : V} :
    (u, w) ∈ vertexFailureProfile k S X ↔
      u ∉ X.1 ∧ w ∉ X.1 ∧ (toGraph (edgesWithin X.1ᶜ S)).Reachable u w := by
  rw [mem_vertexFailureProfile]
  exact ⟨fun ⟨hu, hw, h⟩ => ⟨hu, hw, (reachable_induce_compl_iff hu hw).mp h⟩,
    fun ⟨hu, hw, h⟩ => ⟨hu, hw, (reachable_induce_compl_iff hu hw).mpr h⟩⟩

/-- Reachability through the edges avoiding `X` is equality or the coordinate at `X`: the
vertices of `X` are isolated. -/
theorem reachable_edgesWithin_compl_iff {k : ℕ} {S : Finset (Edge V)} {X : VertexFailureSet V k}
    {u w : V} : (toGraph (edgesWithin X.1ᶜ S)).Reachable u w ↔
      u = w ∨ (u, w) ∈ vertexFailureProfile k S X := by
  rw [mem_vertexFailureProfile_iff_edgesWithin]
  constructor
  · intro h
    by_cases hu : u ∈ X.1
    · exact Or.inl (eq_of_reachable_edgesWithin_compl hu h).symm
    by_cases hw : w ∈ X.1
    · exact Or.inl (eq_of_reachable_edgesWithin_compl hw h.symm)
    exact Or.inr ⟨hu, hw, h⟩
  · rintro (rfl | ⟨-, -, h⟩)
    · exact Reachable.rfl
    · exact h

/-- **Equal vertex profiles are equal partitions after every deletion**: two graphs have the same
`Σ^V_k` exactly when, for every set `X` of fewer than `k` vertices, their graphs induced on
`V \ X` have the same reachability. -/
theorem vertexFailureProfile_eq_iff {k : ℕ} {S T : Finset (Edge V)} :
    vertexFailureProfile k S = vertexFailureProfile k T ↔ ∀ X : Finset V, X.card < k →
      ((toGraph S).induce {z | z ∉ X}).Reachable = ((toGraph T).induce {z | z ∉ X}).Reachable := by
  constructor
  · intro h X hX
    funext a b
    apply propext
    have key : ∀ {A B : Finset (Edge V)}, vertexFailureProfile k A = vertexFailureProfile k B →
        ((toGraph A).induce {z | z ∉ X}).Reachable a b →
          ((toGraph B).induce {z | z ∉ X}).Reachable a b := by
      intro A B hAB hr
      have hm : (a.1, b.1) ∈ vertexFailureProfile k A ⟨X, hX⟩ :=
        mem_vertexFailureProfile.mpr ⟨a.2, b.2, hr⟩
      rw [hAB] at hm
      obtain ⟨_, _, hr'⟩ := mem_vertexFailureProfile.mp hm
      exact hr'
    exact ⟨key h, key h.symm⟩
  · intro h
    funext X
    ext ⟨u, w⟩
    rw [mem_vertexFailureProfile, mem_vertexFailureProfile, h X.1 X.2]

/-- **Deletion commutes with union**, and partitions combine by their join: the vertex profile of
a union is determined by the profiles of its parts. -/
theorem vertexFailureProfile_union_congr {k : ℕ} {S S' T T' : Finset (Edge V)}
    (hS : vertexFailureProfile k S = vertexFailureProfile k S')
    (hT : vertexFailureProfile k T = vertexFailureProfile k T') :
    vertexFailureProfile k (S ∪ T) = vertexFailureProfile k (S' ∪ T') := by
  have key : ∀ {A A' : Finset (Edge V)}, vertexFailureProfile k A = vertexFailureProfile k A' →
      ∀ (X : VertexFailureSet V k) (u w : V), (toGraph (edgesWithin X.1ᶜ A)).Reachable u w →
        (toGraph (edgesWithin X.1ᶜ A')).Reachable u w := by
    intro A A' h X u w hr
    rw [reachable_edgesWithin_compl_iff, h] at hr
    exact reachable_edgesWithin_compl_iff.mpr hr
  funext X
  ext ⟨u, w⟩
  rw [mem_vertexFailureProfile_iff_edgesWithin, mem_vertexFailureProfile_iff_edgesWithin,
    edgesWithin_union, edgesWithin_union]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨reachable_union_of (key hS X) (key hT X), reachable_union_of (key hS.symm X) (key hT.symm X)⟩

/-- **Equivalence under extensions is equality of vertex profiles.** -/
theorem extensionEquiv_vertexFailureProfile_iff {k : ℕ} {S T : Finset (Edge V)} :
    ExtensionEquiv (vertexFailureProfile k) S T ↔
      vertexFailureProfile k S = vertexFailureProfile k T :=
  extensionEquiv_iff_of_merge (f := vertexFailureProfile k) fun _ _ _ _ =>
    vertexFailureProfile_union_congr

/-- **A subgraph with the same vertex profile is a strong certificate** for it. -/
theorem isStrongCertificate_vertexFailureProfile {k : ℕ} {C S : Finset (Edge V)} (hCS : C ⊆ S)
    (h : vertexFailureProfile k C = vertexFailureProfile k S) :
    IsStrongCertificate (vertexFailureProfile k) C S :=
  ⟨hCS, extensionEquiv_vertexFailureProfile_iff.mpr h⟩

/-! ## The greedy certificate -/

/-- **A separable edge**: some set `X` of fewer than `k` vertices, avoiding both ends of `e`,
separates them in `T`, that is in `toGraph (edgesWithin Xᶜ T)`.  An edge of `T` is never
separable in `T`. -/
def Separable (k : ℕ) (T : Finset (Edge V)) (e : Edge V) : Prop :=
  ∃ X : Finset V, X.card < k ∧ ∃ u w, (e : Sym2 V) = s(u, w) ∧ u ∉ X ∧ w ∉ X ∧
    ¬(toGraph (edgesWithin Xᶜ T)).Reachable u w

/-- An edge of `T` is not separable in `T`: its ends are adjacent after every deletion that
avoids them. -/
theorem not_separable_of_mem {k : ℕ} {T : Finset (Edge V)} {e : Edge V} (he : e ∈ T) :
    ¬Separable k T e := by
  rintro ⟨X, -, u, w, hew, hu, hw, hr⟩
  exact hr (toGraph_adj.mpr ⟨e, (mem_edgesWithin_of_eq hew).mpr
    ⟨he, Finset.mem_compl.mpr hu, Finset.mem_compl.mpr hw⟩, hew⟩).reachable

/-- Separability passes to subsets. -/
theorem Separable.mono {k : ℕ} {T T' : Finset (Edge V)} {e : Edge V} (h : Separable k T e)
    (hT : T' ⊆ T) : Separable k T' e := by
  obtain ⟨X, hX, u, w, he, hu, hw, hr⟩ := h
  exact ⟨X, hX, u, w, he, hu, hw, fun h' =>
    hr (h'.mono (toGraph_mono (edgesWithin_mono subset_rfl hT)))⟩

/-- **Blocking edge sets**: every nonempty `T ⊆ H` contains an edge that is separable in `T`
without it. -/
def Blocking (k : ℕ) (H : Finset (Edge V)) : Prop :=
  ∀ T ⊆ H, T.Nonempty → ∃ e ∈ T, Separable k (T.erase e) e

theorem blocking_empty (k : ℕ) : Blocking k (∅ : Finset (Edge V)) := fun T hT hne => by
  rw [Finset.subset_empty.mp hT] at hne
  exact absurd hne Finset.not_nonempty_empty

/-- **One greedy step**: keep `e` when it is separable in the edges kept so far. -/
noncomputable def greedyStep (k : ℕ) (H : Finset (Edge V)) (e : Edge V) : Finset (Edge V) := by
  classical exact if Separable k H e then insert e H else H

/-- **The greedy certificate**: the edges of `S`, processed in the order of `S.toList`. -/
noncomputable def greedyCert (k : ℕ) (S : Finset (Edge V)) : Finset (Edge V) :=
  S.toList.foldl (greedyStep k) ∅

theorem greedyStep_of_separable {k : ℕ} {H : Finset (Edge V)} {e : Edge V}
    (h : Separable k H e) : greedyStep k H e = insert e H := by
  unfold greedyStep
  exact ite_eq_left h

theorem greedyStep_of_not_separable {k : ℕ} {H : Finset (Edge V)} {e : Edge V}
    (h : ¬Separable k H e) : greedyStep k H e = H := by
  unfold greedyStep
  exact ite_eq_right h

theorem subset_greedyStep (k : ℕ) (H : Finset (Edge V)) (e : Edge V) : H ⊆ greedyStep k H e := by
  by_cases h : Separable k H e
  · rw [greedyStep_of_separable h]
    exact Finset.subset_insert e H
  · rw [greedyStep_of_not_separable h]

theorem greedyStep_subset_insert (k : ℕ) (H : Finset (Edge V)) (e : Edge V) :
    greedyStep k H e ⊆ insert e H := by
  by_cases h : Separable k H e
  · rw [greedyStep_of_separable h]
  · rw [greedyStep_of_not_separable h]
    exact Finset.subset_insert e H

/-- After its step, an edge is kept or no longer separable. -/
theorem mem_or_not_separable_greedyStep (k : ℕ) (H : Finset (Edge V)) (e : Edge V) :
    e ∈ greedyStep k H e ∨ ¬Separable k (greedyStep k H e) e := by
  by_cases h : Separable k H e
  · rw [greedyStep_of_separable h]
    exact Or.inl (Finset.mem_insert_self e H)
  · rw [greedyStep_of_not_separable h]
    exact Or.inr h

/-- **A greedy step keeps blocking**: a newly kept edge is the last edge of every set containing
it. -/
theorem Blocking.greedyStep {k : ℕ} {H : Finset (Edge V)} (hH : Blocking k H) (e : Edge V) :
    Blocking k (greedyStep k H e) := by
  by_cases h : Separable k H e
  · rw [greedyStep_of_separable h]
    intro T hT hne
    by_cases heT : e ∈ T
    · refine ⟨e, heT, h.mono fun x hx => ?_⟩
      obtain ⟨hxe, hxT⟩ := Finset.mem_erase.mp hx
      exact (Finset.mem_insert.mp (hT hxT)).resolve_left hxe
    · exact hH T (fun x hx => (Finset.mem_insert.mp (hT hx)).resolve_left
        fun hxe => heT (hxe ▸ hx)) hne
  · rw [greedyStep_of_not_separable h]
    exact hH

/-- **The greedy fold**: it only adds edges of the list, keeps blocking, and leaves every edge of
the list kept or no longer separable. -/
theorem foldl_greedyStep (k : ℕ) : ∀ (l : List (Edge V)) (H : Finset (Edge V)),
    H ⊆ l.foldl (greedyStep k) H ∧ l.foldl (greedyStep k) H ⊆ H ∪ l.toFinset ∧
      (Blocking k H → Blocking k (l.foldl (greedyStep k) H)) ∧
      ∀ e ∈ l, e ∈ l.foldl (greedyStep k) H ∨ ¬Separable k (l.foldl (greedyStep k) H) e
  | [], H => by
      refine ⟨subset_rfl, Finset.subset_union_left, id, fun e he => absurd he List.not_mem_nil⟩
  | e :: l, H => by
      obtain ⟨h1, h2, h3, h4⟩ := foldl_greedyStep k l (greedyStep k H e)
      rw [List.foldl_cons]
      refine ⟨(subset_greedyStep k H e).trans h1, fun x hx => ?_, fun hH => h3 (hH.greedyStep e),
        fun x hx => ?_⟩
      · rcases Finset.mem_union.mp (h2 hx) with hx | hx
        · rcases Finset.mem_insert.mp (greedyStep_subset_insert k H e hx) with rfl | hx
          · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_cons_self))
          · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _
            (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp hx)))
      · rcases List.mem_cons.mp hx with rfl | hx
        · rcases mem_or_not_separable_greedyStep k H x with h | h
          · exact Or.inl (h1 h)
          · exact Or.inr fun hs => h (hs.mono h1)
        · exact h4 x hx

/-- **The greedy certificate is a subgraph.** -/
theorem greedyCert_subset (k : ℕ) (S : Finset (Edge V)) : greedyCert k S ⊆ S := fun e he => by
  have h := (foldl_greedyStep k S.toList ∅).2.1 he
  rw [Finset.empty_union, List.mem_toFinset, Finset.mem_toList] at h
  exact h

/-- The greedy certificate is blocking. -/
theorem blocking_greedyCert (k : ℕ) (S : Finset (Edge V)) : Blocking k (greedyCert k S) :=
  (foldl_greedyStep k S.toList ∅).2.2.1 (blocking_empty k)

/-- Every edge of `S` is kept, or no longer separable in the greedy certificate. -/
theorem mem_or_not_separable_greedyCert {k : ℕ} {S : Finset (Edge V)} {e : Edge V} (he : e ∈ S) :
    e ∈ greedyCert k S ∨ ¬Separable k (greedyCert k S) e :=
  (foldl_greedyStep k S.toList ∅).2.2.2 e (Finset.mem_toList.mpr he)

/-- **The greedy certificate has the same vertex profile**: an edge of `G − X` that was left out
has its ends connected in the certificate without `X`. -/
theorem vertexFailureProfile_greedyCert (k : ℕ) (S : Finset (Edge V)) :
    vertexFailureProfile k (greedyCert k S) = vertexFailureProfile k S := by
  funext X
  ext ⟨u, w⟩
  rw [mem_vertexFailureProfile_iff_edgesWithin, mem_vertexFailureProfile_iff_edgesWithin]
  refine and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h => h.mono (toGraph_mono (edgesWithin_mono subset_rfl (greedyCert_subset k S))),
      fun h => Matroid.reachable_of_forall_adj_reachable (fun a b hab => ?_) h⟩
  obtain ⟨hab', ha, hb⟩ := toGraph_edgesWithin_adj.mp hab
  obtain ⟨e, he, hea⟩ := toGraph_adj.mp hab'
  rcases mem_or_not_separable_greedyCert (k := k) he with hH | hns
  · exact (toGraph_edgesWithin_adj.mpr ⟨toGraph_adj.mpr ⟨e, hH, hea⟩, ha, hb⟩).reachable
  · by_contra hr
    exact hns ⟨X.1, X.2, a, b, hea, Finset.mem_compl.mp ha, Finset.mem_compl.mp hb, hr⟩

/-- **The greedy certificate is a strong certificate** for the vertex profile. -/
theorem isStrongCertificate_greedyCert (k : ℕ) (S : Finset (Edge V)) :
    IsStrongCertificate (vertexFailureProfile k) (greedyCert k S) S :=
  isStrongCertificate_vertexFailureProfile (greedyCert_subset k S)
    (vertexFailureProfile_greedyCert k S)

/-! ## Blocking edge sets have at most `2kv` edges -/

omit [Fintype V] [DecidableEq V] in
/-- At most `C(#W, 2)` edges lie inside `W`. -/
theorem card_edgesWithin_le (W : Finset V) (S : Finset (Edge V)) :
    (edgesWithin W S).card ≤ W.card.choose 2 := by
  classical
  rw [← Sym2.card_image_offDiag]
  refine Finset.card_le_card_of_injOn (fun e => (e : Sym2 V)) (fun e he => ?_)
    (fun e _ e' _ h => Subtype.ext h)
  obtain ⟨a, b, hab⟩ := exists_edge_eq_mk e
  obtain ⟨-, ha, hb⟩ := (mem_edgesWithin_of_eq hab).mp (Finset.mem_coe.mp he)
  have hne : a ≠ b := fun h => e.2 (by rw [hab, h]; exact Sym2.mk_isDiag_iff.mpr rfl)
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩, hab.symm⟩)

omit [Fintype V] in
/-- **Deleting a vertex from `W`** removes exactly the edges inside `W` at that vertex. -/
theorem card_edgesWithin_erase_add (W : Finset V) (S : Finset (Edge V)) (x : V) :
    (edgesWithin (W.erase x) S).card +
      ((edgesWithin W S).filter fun e : Edge V => x ∈ (e : Sym2 V)).card =
        (edgesWithin W S).card := by
  have h : (edgesWithin W S).filter (fun e : Edge V => ¬x ∈ (e : Sym2 V)) =
      edgesWithin (W.erase x) S := by
    ext e
    rw [Finset.mem_filter, mem_edgesWithin, mem_edgesWithin]
    constructor
    · rintro ⟨⟨heS, heW⟩, hx⟩
      exact ⟨heS, fun z hz => Finset.mem_erase.mpr ⟨fun hzx => hx (hzx ▸ hz), heW z hz⟩⟩
    · rintro ⟨heS, heW⟩
      exact ⟨⟨heS, fun z hz => (Finset.mem_erase.mp (heW z hz)).2⟩,
        fun hx => (Finset.mem_erase.mp (heW x hx)).1 rfl⟩
  rw [← h, add_comm]
  exact Finset.card_filter_add_card_filter_not _

omit [Fintype V] in
/-- **Degrees through other ends**: if the other end of every edge of `T` at `x` lies in `U`,
then `x` lies on at most `#U` edges of `T`. -/
theorem card_filter_mem_le {T : Finset (Edge V)} {x : V} {U : Finset V}
    (h : ∀ f ∈ T, ∀ y, (f : Sym2 V) = s(x, y) → y ∈ U) :
    (T.filter fun f : Edge V => x ∈ (f : Sym2 V)).card ≤ U.card := by
  classical
  let g : Edge V → V := fun f => if hx : x ∈ (f : Sym2 V) then Sym2.Mem.other hx else x
  have hg : ∀ (f : Edge V) (hx : x ∈ (f : Sym2 V)), g f = Sym2.Mem.other hx :=
    fun f hx => dite_eq_left hx
  refine Finset.card_le_card_of_injOn g (fun f hf => ?_) (fun f₁ hf₁ f₂ hf₂ heq => ?_)
  · obtain ⟨hfT, hx⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
    rw [Finset.mem_coe, hg f hx]
    exact h f hfT _ (Sym2.other_spec hx).symm
  · obtain ⟨-, hx₁⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hf₁)
    obtain ⟨-, hx₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hf₂)
    rw [hg f₁ hx₁, hg f₂ hx₂] at heq
    exact Subtype.ext ((Sym2.other_spec hx₁).symm.trans
      ((congrArg (fun y => s(x, y)) heq).trans (Sym2.other_spec hx₂)))

omit [Fintype V] [DecidableEq V] in
/-- The other end of an edge differs from the given end. -/
theorem ne_of_edge_eq_mk {f : Edge V} {x y : V} (h : (f : Sym2 V) = s(x, y)) : y ≠ x :=
  fun hyx => f.2 (by rw [h, hyx]; exact Sym2.mk_isDiag_iff.mpr rfl)

omit [Fintype V] [DecidableEq V] in
/-- The ends of an edge inside `W` lie in `W`. -/
theorem mem_of_mem_edgesWithin {W : Finset V} {S : Finset (Edge V)} {f : Edge V} {x y : V}
    (hf : f ∈ edgesWithin W S) (h : (f : Sym2 V) = s(x, y)) : x ∈ W ∧ y ∈ W :=
  ((mem_edgesWithin_of_eq h).mp hf).2

/-- The counting argument, by strong induction on `|W|`. -/
private theorem card_edgesWithin_le_of_blocking_aux {k : ℕ} {H : Finset (Edge V)} (hk : 1 ≤ k)
    (hH : Blocking k H) :
    ∀ (n : ℕ) (W : Finset V), W.card = n → 2 * k ≤ n →
      (edgesWithin W H).card ≤ 2 * k * (n - k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hWn hkn
  subst hWn
  by_contra hcon
  have hlt : 2 * k * (W.card - k) < (edgesWithin W H).card := not_le.mp hcon
  -- No candidate has exactly `2k` vertices.
  have hW2k : 2 * k < W.card := by
    rcases lt_or_eq_of_le hkn with h | h
    · exact h
    · exfalso
      have hle := card_edgesWithin_le W H
      rw [← h] at hle hlt
      have hchoose : (2 * k).choose 2 ≤ 2 * k * (2 * k - k) := by
        rw [Nat.choose_two_right, show 2 * k - k = k by omega]
        apply Nat.div_le_of_le_mul
        calc 2 * k * (2 * k - 1) ≤ 2 * k * (2 * k) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = 2 * (2 * k * k) := by ring
      omega
  -- Every vertex of `W` has more than `2k` edges inside `W`.
  have hdeg : ∀ x ∈ W,
      2 * k < ((edgesWithin W H).filter fun e : Edge V => x ∈ (e : Sym2 V)).card := by
    intro x hx
    by_contra hd
    have hd := not_lt.mp hd
    have hcard : (W.erase x).card = W.card - 1 := Finset.card_erase_of_mem hx
    have hih := ih (W.card - 1) (by omega) (W.erase x) hcard (by omega)
    have hsplit := card_edgesWithin_erase_add W H x
    have hsub : W.card - k = (W.card - 1 - k) + 1 := by omega
    have hmul : 2 * k * (W.card - k) = 2 * k * (W.card - 1 - k) + 2 * k := by
      rw [hsub, mul_add_one]
    omega
  -- The blocking property, on the edges inside `W`.
  set T := edgesWithin W H with hTdef
  have hTne : T.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hlt)
  obtain ⟨e, heT, X, hX, u, w, hew, hu, hw, hsep⟩ := hH T (edgesWithin_subset W H) hTne
  obtain ⟨huW, hwW⟩ := mem_of_mem_edgesWithin heT hew
  set R := toGraph (edgesWithin Xᶜ (T.erase e)) with hRdef
  -- The vertices of `W \ X` connected to `u` without `X` and `e`.
  classical
  set C := W.filter fun z => z ∉ X ∧ R.Reachable u z with hCdef
  have hmemC : ∀ {z}, z ∈ C ↔ z ∈ W ∧ z ∉ X ∧ R.Reachable u z := fun {z} => by
    rw [hCdef, Finset.mem_filter]
  have huC : u ∈ C := hmemC.mpr ⟨huW, hu, Reachable.rfl⟩
  have hwC : w ∉ C := fun h => hsep (hmemC.mp h).2.2
  -- An edge of `T` other than `e`, with both ends outside `X`, is an edge of `R`.
  have hRadj : ∀ f ∈ T, f ≠ e → ∀ a b, (f : Sym2 V) = s(a, b) → a ∉ X → b ∉ X → R.Adj a b :=
    fun f hf hfe a b hab ha hb => toGraph_adj.mpr ⟨f, (mem_edgesWithin_of_eq hab).mpr
      ⟨Finset.mem_erase.mpr ⟨hfe, hf⟩, Finset.mem_compl.mpr ha, Finset.mem_compl.mpr hb⟩, hab⟩
  set U₁ := C ∪ insert w (X ∩ W) with hU₁def
  set U₂ := W \ C with hU₂def
  have hU₁W : U₁ ⊆ W := Finset.union_subset (Finset.filter_subset _ _)
    (Finset.insert_subset hwW Finset.inter_subset_right)
  have hU₂W : U₂ ⊆ W := Finset.sdiff_subset
  have hunion : U₁ ∪ U₂ = W := by
    refine (Finset.union_subset hU₁W hU₂W).antisymm fun z hz => ?_
    by_cases hzC : z ∈ C
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hzC)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, hzC⟩)
  have hinter : (U₁ ∩ U₂).card ≤ k := by
    have hsub : U₁ ∩ U₂ ⊆ insert w (X ∩ W) := fun z hz => by
      obtain ⟨hz₁, hz₂⟩ := Finset.mem_inter.mp hz
      rcases Finset.mem_union.mp hz₁ with hzC | hz
      · exact absurd hzC (Finset.mem_sdiff.mp hz₂).2
      · exact hz
    calc (U₁ ∩ U₂).card ≤ (insert w (X ∩ W)).card := Finset.card_le_card hsub
      _ ≤ (X ∩ W).card + 1 := Finset.card_insert_le _ _
      _ ≤ X.card + 1 := by gcongr; exact Finset.inter_subset_left
      _ ≤ k := hX
  -- Every edge inside `W` lies inside `U₁` or inside `U₂`.
  have hsplit : ∀ f ∈ T, f ∈ edgesWithin U₁ H ∨ f ∈ edgesWithin U₂ H := by
    intro f hf
    have hfH : f ∈ H := edgesWithin_subset W H hf
    obtain ⟨a, b, hab⟩ := exists_edge_eq_mk f
    obtain ⟨haW, hbW⟩ := mem_of_mem_edgesWithin hf hab
    by_cases hfe : f = e
    · subst hfe
      rcases Sym2.eq_iff.mp (hab.symm.trans hew) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ((mem_edgesWithin_of_eq hab).mpr ⟨hfH, Finset.mem_union_left _ huC,
          Finset.mem_union_right _ (Finset.mem_insert_self _ _)⟩)
      · exact Or.inl ((mem_edgesWithin_of_eq hab).mpr ⟨hfH,
          Finset.mem_union_right _ (Finset.mem_insert_self _ _), Finset.mem_union_left _ huC⟩)
    -- An end in `C` puts the other end in `U₁`.
    have hother : ∀ {a b : V}, (f : Sym2 V) = s(a, b) → a ∈ C → b ∈ U₁ := by
      intro a b hab haC
      obtain ⟨-, hbW⟩ := mem_of_mem_edgesWithin hf hab
      by_cases hbX : b ∈ X
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hbX, hbW⟩))
      · obtain ⟨-, haX, hua⟩ := hmemC.mp haC
        exact Finset.mem_union_left _ (hmemC.mpr ⟨hbW, hbX,
          hua.trans (hRadj f hf hfe a b hab haX hbX).reachable⟩)
    by_cases haC : a ∈ C
    · exact Or.inl ((mem_edgesWithin_of_eq hab).mpr ⟨hfH, Finset.mem_union_left _ haC,
        hother hab haC⟩)
    by_cases hbC : b ∈ C
    · have hba : (f : Sym2 V) = s(b, a) := hab.trans Sym2.eq_swap
      exact Or.inl ((mem_edgesWithin_of_eq hab).mpr ⟨hfH, hother hba hbC,
        Finset.mem_union_left _ hbC⟩)
    · exact Or.inr ((mem_edgesWithin_of_eq hab).mpr ⟨hfH, Finset.mem_sdiff.mpr ⟨haW, haC⟩,
        Finset.mem_sdiff.mpr ⟨hbW, hbC⟩⟩)
  have hTle : T.card ≤ (edgesWithin U₁ H).card + (edgesWithin U₂ H).card := by
    refine (Finset.card_le_card fun f hf => ?_).trans (Finset.card_union_le _ _)
    rcases hsplit f hf with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  -- A vertex outside `U₂` has all its edges inside `U₁`, and one outside `U₁` inside `U₂`.
  have hdeg₁ : ∀ x ∈ W, x ∉ U₂ →
      (T.filter fun f : Edge V => x ∈ (f : Sym2 V)).card ≤ (U₁.erase x).card :=
    fun x _ hxU₂ => card_filter_mem_le fun f hf y hxy => by
      have hyx := ne_of_edge_eq_mk hxy
      rcases hsplit f hf with h | h
      · exact Finset.mem_erase.mpr ⟨hyx, (mem_of_mem_edgesWithin h hxy).2⟩
      · exact absurd (mem_of_mem_edgesWithin h hxy).1 hxU₂
  have hdeg₂ : ∀ x ∈ W, x ∉ U₁ →
      (T.filter fun f : Edge V => x ∈ (f : Sym2 V)).card ≤ (U₂.erase x).card :=
    fun x _ hxU₁ => card_filter_mem_le fun f hf y hxy => by
      have hyx := ne_of_edge_eq_mk hxy
      rcases hsplit f hf with h | h
      · exact absurd (mem_of_mem_edgesWithin h hxy).1 hxU₁
      · exact Finset.mem_erase.mpr ⟨hyx, (mem_of_mem_edgesWithin h hxy).2⟩
  -- `u` lies in `U₁` only.
  have huU₁ : u ∈ U₁ := Finset.mem_union_left _ huC
  have huU₂ : u ∉ U₂ := fun h => (Finset.mem_sdiff.mp h).2 huC
  have hU₁card : 2 * k + 2 ≤ U₁.card := by
    have h₁ := hdeg₁ u huW huU₂
    have h₂ := hdeg u huW
    rw [Finset.card_erase_of_mem huU₁] at h₁
    omega
  -- Some neighbour of `w` lies outside `U₁`: inside `C` its only neighbour is `u`.
  have hout : ∃ z ∈ W, z ∉ U₁ := by
    by_contra hno
    have hWU₁ : ∀ z ∈ W, z ∈ U₁ := fun z hz => by
      by_contra h
      exact hno ⟨z, hz, h⟩
    have hle : (T.filter fun f : Edge V => w ∈ (f : Sym2 V)).card ≤ (insert u X).card :=
      card_filter_mem_le fun f hf y hwy => by
        have hyw := ne_of_edge_eq_mk hwy
        have hyW := (mem_of_mem_edgesWithin hf hwy).2
        rcases Finset.mem_union.mp (hWU₁ y hyW) with hyC | hy
        · -- An edge from `w` into `C` is `e`, so its other end is `u`.
          by_cases hfe : f = e
          · subst hfe
            rcases Sym2.eq_iff.mp (hwy.symm.trans hew) with ⟨-, h⟩ | ⟨-, rfl⟩
            · exact absurd (h ▸ hyC : w ∈ C) hwC
            · exact Finset.mem_insert_self _ _
          · obtain ⟨-, hyX, huy⟩ := hmemC.mp hyC
            exact absurd (huy.trans (hRadj f hf hfe y w (hwy.trans Sym2.eq_swap) hyX hw).reachable)
              hsep
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact absurd rfl hyw
          · exact Finset.mem_insert_of_mem (Finset.mem_inter.mp hy).1
    have h₁ := hdeg w hwW
    have h₂ : (insert u X).card ≤ X.card + 1 := Finset.card_insert_le _ _
    omega
  obtain ⟨z, hzW, hzU₁⟩ := hout
  have hzU₂ : z ∈ U₂ := by
    rw [← hunion] at hzW
    exact (Finset.mem_union.mp hzW).resolve_left hzU₁
  have hU₂card : 2 * k + 2 ≤ U₂.card := by
    have h₁ := hdeg₂ z hzW hzU₁
    have h₂ := hdeg z hzW
    rw [Finset.card_erase_of_mem hzU₂] at h₁
    omega
  -- Both parts are smaller candidates.
  have hU₁lt : U₁.card < W.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hU₁W, fun h => hzU₁ (h ▸ hzW)⟩)
  have hU₂lt : U₂.card < W.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hU₂W, fun h => huU₂ (h ▸ huW)⟩)
  have hih₁ := ih U₁.card hU₁lt U₁ rfl (by omega)
  have hih₂ := ih U₂.card hU₂lt U₂ rfl (by omega)
  have hsum : U₁.card + U₂.card ≤ W.card + k := by
    have := Finset.card_union_add_card_inter U₁ U₂
    rw [hunion] at this
    omega
  have hab : (U₁.card - k) + (U₂.card - k) ≤ W.card - k := by omega
  have hmul := Nat.mul_le_mul_left (2 * k) hab
  rw [Nat.mul_add] at hmul
  omega

/-- **The counting argument** (Diestel's proof of Mader's theorem, adapted to blocking edge
sets): for `k ≥ 1`, every vertex set `W` with `|W| ≥ 2k` has at most `2k(|W| - k)` edges of a
blocking `H` inside it. -/
theorem card_edgesWithin_le_of_blocking {k : ℕ} {H : Finset (Edge V)} (hk : 1 ≤ k)
    (hH : Blocking k H) {W : Finset V} (hW : 2 * k ≤ W.card) :
    (edgesWithin W H).card ≤ 2 * k * (W.card - k) :=
  card_edgesWithin_le_of_blocking_aux hk hH _ W rfl hW

/-- **Blocking edge sets have at most `2kv` edges.** -/
theorem card_le_of_blocking {k : ℕ} {H : Finset (Edge V)} (h : Blocking k H) :
    H.card ≤ 2 * k * Fintype.card V := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rcases H.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨e, -, X, hX, -⟩ := h H subset_rfl hne
      exact absurd hX (Nat.not_lt_zero _)
  · by_cases hv : 2 * k ≤ Fintype.card V
    · have hW := card_edgesWithin_le_of_blocking hk h (W := Finset.univ)
        (by rw [Finset.card_univ]; exact hv)
      rw [edgesWithin_univ, Finset.card_univ] at hW
      exact hW.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    · calc H.card ≤ (Fintype.card V).choose 2 := (Finset.card_le_univ H).trans card_edge.le
        _ ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _
        _ = Fintype.card V * Fintype.card V := sq _
        _ ≤ 2 * k * Fintype.card V := Nat.mul_le_mul_right _ (by omega)

/-- **The greedy certificate has at most `2kv` edges.** -/
theorem card_greedyCert_le (k : ℕ) (S : Finset (Edge V)) :
    (greedyCert k S).card ≤ 2 * k * Fintype.card V :=
  card_le_of_blocking (blocking_greedyCert k S)

/-- **The sparse vertex-connectivity certificate** (`sec:failure-profiles`, "Vertex failures"):
every graph has a subgraph with at most `2kv` edges and the same partition after deleting any set
of fewer than `k` vertices. -/
theorem exists_vertexFailureCertificate (k : ℕ) (S : Finset (Edge V)) :
    ∃ H ⊆ S, H.card ≤ 2 * k * Fintype.card V ∧
      vertexFailureProfile k H = vertexFailureProfile k S :=
  ⟨greedyCert k S, greedyCert_subset k S, card_greedyCert_le k S,
    vertexFailureProfile_greedyCert k S⟩

/-! ## The certificate size -/

/-- **Every graph has a strong certificate for its vertex profile with at most `2kv` edges.** -/
theorem hasStrongCertificateBound_vertexFailureProfile (k : ℕ) :
    HasStrongCertificateBound (vertexFailureProfile (V := V) k) (2 * k * Fintype.card V) :=
  fun S => ⟨greedyCert k S, isStrongCertificate_greedyCert k S, card_greedyCert_le k S⟩

/-- **The vertex-failure profile** (`sec:failure-profiles`, "Vertex failures"):
`b_{Σ^V_k} ≤ min{C(v, 2), 2kv}`, for every `k`. -/
theorem vertexFailureProfile_strongCertificateSize_le (k : ℕ) :
    strongCertificateSize (vertexFailureProfile (V := V) k) ≤
      min ((Fintype.card V).choose 2) (2 * k * Fintype.card V) := by
  refine le_min ?_ (strongCertificateSize_le (hasStrongCertificateBound_vertexFailureProfile k))
  rw [← card_edge]
  exact strongCertificateSize_le_card _

/-- **Certificates for the vertex profile within `min{C(v, 2), 2kv}` edges.** -/
theorem hasStrongCertificateBound_min_vertexFailureProfile (k : ℕ) :
    HasStrongCertificateBound (vertexFailureProfile (V := V) k)
      (min ((Fintype.card V).choose 2) (2 * k * Fintype.card V)) :=
  hasStrongCertificateBound_iff_size_le.mpr (vertexFailureProfile_strongCertificateSize_le k)

/-- Truncation does not increase the certificate size. -/
theorem vertexFailureProfile_strongCertificateSize_mono {k k' : ℕ} (h : k' ≤ k) :
    strongCertificateSize (vertexFailureProfile (V := V) k') ≤
      strongCertificateSize (vertexFailureProfile (V := V) k) :=
  strongCertificateSize_le_of_determined fun _ _ hST =>
    funext fun X => congrFun hST ⟨X.1, X.2.trans_le h⟩

/-- **`k = 0`**: there are no failure sets, so the profile is constant and needs no
certificate. -/
theorem vertexFailureProfile_zero_strongCertificateSize :
    strongCertificateSize (vertexFailureProfile (V := V) 0) = 0 :=
  strongCertificateSize_eq_zero_iff.mpr vertexFailureProfile_zero

/-- **`k = 1`**: the profile has the certificate size of the component partition. -/
theorem vertexFailureProfile_one_strongCertificateSize :
    strongCertificateSize (vertexFailureProfile (V := V) 1) =
      strongCertificateSize (connectedComponents (V := V)) :=
  le_antisymm
    (strongCertificateSize_le_of_determined fun _ _ h => vertexFailureProfile_one_eq_iff.mpr h)
    (strongCertificateSize_le_of_determined fun _ _ h => vertexFailureProfile_one_eq_iff.mp h)

end MonoidProduct.Graph
