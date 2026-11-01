import MonoidProduct.Graph.RotationInsert
import MonoidProduct.Graph.PlanarSubgraphAcceptance
set_option linter.style.header false

/-!
# Acceptance statements for insertions into faces

The statements of `Graph/RotationChord.lean` and `Graph/RotationInsert.lean`, restated, followed
by a sanity check.  Lean checks every `example` here against the library's statement.

* Chords: the graph with one more edge, the two new faces as darts and as walks, the counts, and
  sphericality; planarity of `G ⊔ edge a.fst b.fst` for two darts of one face.
* `attachVertex` and its adjacency, and leaves: the face through the corner, and sphericality.
* The marked fan, keeping the closed interval between two consecutive attachments, and the
  unmarked fan.

The sanity check joins a new vertex to both vertices of `K₂`, a leaf followed by a chord: the
result, a triangle, has a spherical rotation system with a face whose walk is the new vertex,
`0` and `1`.
-/

namespace MonoidProduct.Graph

open SimpleGraph RotationSystem

/-! ## Statements -/

section Statements

variable {V : Type*} {G G' : SimpleGraph V}

/-- **`G ⊔ edge u v` is `G` with the edge `uv` added**, and then its darts are those of `G`, the
new dart and its reversal. -/
example {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v) :
    IsAddEdge G (G ⊔ edge u v) u v ∧
      Nonempty (G.Dart ≃ {d : (G ⊔ edge u v).Dart //
        d ≠ (isAddEdge_sup_edge huv).dart ∧ d ≠ (isAddEdge_sup_edge huv).dart.symm}) :=
  ⟨isAddEdge_sup_edge huv, ⟨(isAddEdge_sup_edge huv).dartEquiv hn⟩⟩

/-- **The two new faces of a chord**, as darts: the face through `a`, read as `a :: P ++ b :: Q`,
splits into `c.symm :: a :: P` and `c :: b :: Q`. -/
example [DecidableEq V] [Finite V] (ρ : RotationSystem G) {a b : G.Dart}
    (h : IsAddEdge G G' a.fst b.fst) (hn : ¬ G.Adj a.fst b.fst) {P Q : List G.Dart}
    (hPQ : ρ.faceDarts a = a :: P ++ b :: Q) :
    (ρ.insertChord h hn).faceDarts h.dart.symm = h.dart.symm :: (a :: P).map h.incl ∧
      (ρ.insertChord h hn).faceDarts h.dart = h.dart :: (b :: Q).map h.incl :=
  ρ.faceDarts_insertChord h hn hPQ

/-- **The two new faces of a chord**, as walks: `[u] ++ P' ++ [v] ++ Q'` splits into
`[v, u] ++ P'` and `[u, v] ++ Q'`. -/
example [DecidableEq V] [Finite V] (ρ : RotationSystem G) {a b : G.Dart}
    (h : IsAddEdge G G' a.fst b.fst) (hn : ¬ G.Adj a.fst b.fst) {P Q : List G.Dart}
    (hPQ : ρ.faceDarts a = a :: P ++ b :: Q) :
    ρ.faceWalk a = [a.fst] ++ P.map (·.fst) ++ [b.fst] ++ Q.map (·.fst) ∧
      (ρ.insertChord h hn).faceWalk h.dart.symm = [b.fst, a.fst] ++ P.map (·.fst) ∧
      (ρ.insertChord h hn).faceWalk h.dart = [a.fst, b.fst] ++ Q.map (·.fst) :=
  ⟨by simp [RotationSystem.faceWalk, hPQ], ρ.faceWalk_insertChord h hn hPQ⟩

/-- **The other faces of a chord**: a face without `a` keeps its darts. -/
example [DecidableEq V] [Finite V] (ρ : RotationSystem G) {a b : G.Dart}
    (h : IsAddEdge G G' a.fst b.fst) (hn : ¬ G.Adj a.fst b.fst) (hab : ρ.face.SameCycle a b)
    {e : G.Dart} (he : ¬ ρ.face.SameCycle a e) :
    (ρ.insertChord h hn).faceDarts (h.incl e) = (ρ.faceDarts e).map h.incl :=
  ρ.faceDarts_insertChord_of_not_sameCycle h hn hab he

/-- **A chord inside one face** adds one face and keeps the Euler defect, so a spherical rotation
system stays spherical. -/
example [DecidableEq V] [Finite V] (ρ : RotationSystem G) {a b : G.Dart}
    (h : IsAddEdge G G' a.fst b.fst) (hn : ¬ G.Adj a.fst b.fst) (hab : ρ.face.SameCycle a b) :
    Nat.card (ρ.insertChord h hn).Face = Nat.card ρ.Face + 1 ∧
      (ρ.insertChord h hn).eulerDefect = ρ.eulerDefect ∧
      (ρ.IsSpherical → (ρ.insertChord h hn).IsSpherical) :=
  ⟨ρ.natCard_face_insertChord h hn hab, ρ.eulerDefect_insertChord h hn hab,
    fun hρ => hρ.insertChord h hn hab⟩

/-- **Joining the tails of two darts of one face keeps planarity.** -/
example [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) {a b : G.Dart}
    (hab : ρ.face.SameCycle a b) (hne : a.fst ≠ b.fst) : IsPlanar (G ⊔ edge a.fst b.fst) :=
  isPlanar_sup_edge_of_sameCycle hρ hab hne

/-- **Attaching a new vertex** `none` to the vertices of `A`. -/
example (A : Set V) (u w : V) :
    ((attachVertex G A).Adj none (some w) ↔ w ∈ A) ∧
      ((attachVertex G A).Adj (some w) none ↔ w ∈ A) ∧
      ((attachVertex G A).Adj (some u) (some w) ↔ G.Adj u w) ∧
      ¬ (attachVertex G A).Adj none none :=
  ⟨attachVertex_adj_none_some, attachVertex_adj_some_none, attachVertex_adj_some_some,
    attachVertex_adj_none_none⟩

/-- **Attaching one more vertex** adds one edge from the new vertex. -/
example (A : Set V) (r : V) :
    attachVertex G (insert r A) = attachVertex G A ⊔ edge none (some r) :=
  attachVertex_insert r A

/-- **A leaf at a corner**: the face through `a`, read from the leaf dart, goes to the new vertex
and back and then around the old face; the rotation system stays spherical. -/
example [DecidableEq V] [Finite V] (ρ : RotationSystem G) {S : Set V} {a : G.Dart}
    (hS : ∀ x, x ∈ S ↔ x = a.fst) :
    (ρ.insertLeaf hS).faceDarts (leafDart hS) =
        leafDart hS :: (leafDart hS).symm :: (ρ.faceDarts a).map (attachDart S) ∧
      (leafDart hS).fst = some a.fst ∧ (leafDart hS).snd = none ∧
      (ρ.IsSpherical → (ρ.insertLeaf hS).IsSpherical) :=
  ⟨ρ.faceDarts_insertLeaf hS, rfl, rfl, fun hρ => hρ.insertLeaf hS⟩

/-- **The marked fan**: joining the new vertex to `A ⊆ C`, with `p`, `q` consecutive in `A` around
the face walk `C`, keeps a face whose walk is the new vertex and the closed interval from `p` to
`q`. -/
example [Finite V] [DecidableEq V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) {d : G.Dart}
    (hC : (ρ.faceWalk d).Nodup) {A : Finset V} (hA : ∀ a ∈ A, a ∈ ρ.faceWalk d)
    (hA2 : 2 ≤ A.card) {p q : V} (hpq : IsConsecutive (ρ.faceWalk d) A p q) :
    ∃ τ : RotationSystem (attachVertex G ↑A), τ.IsSpherical ∧
      ∃ d' : (attachVertex G ↑A).Dart,
        τ.faceWalk d' ~r none :: (closedArc (ρ.faceWalk d) p q).map some :=
  exists_isSpherical_attachVertex_faceWalk hρ hC hA hA2 hpq

/-- **The unmarked fan**: a new vertex joined to at least two vertices of a face with distinct
vertices keeps planarity. -/
example [Finite V] {ρ : RotationSystem G} (hρ : ρ.IsSpherical) {d : G.Dart}
    (hC : (ρ.faceWalk d).Nodup) {A : Finset V} (hA : ∀ a ∈ A, a ∈ ρ.faceWalk d)
    (hA2 : 2 ≤ A.card) : IsPlanar (attachVertex G ↑A) :=
  isPlanar_attachVertex_of_subset_faceWalk hρ hC hA hA2

end Statements

/-! ## Sanity check -/

/-- Of three vertices of `K₂`, two avoiding the third are equal. -/
private theorem fin_two_eq_of_ne : ∀ x y z : Fin 2, x ≠ z → y ≠ z → x = y := by decide

/-- `K₂` is a tree, so acyclic. -/
private theorem isAcyclic_top_fin_two : (⊤ : SimpleGraph (Fin 2)).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro v w h
  rw [isBridge_iff]
  have hiso : v ∈ isolatedVerts ((⊤ : SimpleGraph (Fin 2)).deleteEdges {s(v, w)}) := by
    intro z hz
    rw [deleteEdges_adj, Set.mem_singleton_iff] at hz
    exact hz.2 (by rw [fin_two_eq_of_ne z w v hz.1.ne.symm h.ne.symm])
  exact fun hr => h.ne (eq_of_reachable_of_mem_isolatedVerts hiso hr)

/-- The dart from `0` to `1` in `K₂`. -/
private abbrev k2dart01 : (⊤ : SimpleGraph (Fin 2)).Dart := ⟨(0, 1), (top_adj 0 1).mpr (by decide)⟩

/-- The dart from `1` to `0` in `K₂`. -/
private abbrev k2dart10 : (⊤ : SimpleGraph (Fin 2)).Dart := ⟨(1, 0), (top_adj 1 0).mpr (by decide)⟩

/-- **A fan with two attachments on `K₂`**: a leaf at `0` and then a chord to `1`, giving the
triangle, with a spherical rotation system and a face that reads the new vertex, `0` and `1`. -/
example : ∃ τ : RotationSystem (attachVertex (⊤ : SimpleGraph (Fin 2)) ↑({0, 1} : Finset (Fin 2))),
    τ.IsSpherical ∧ ∃ d', τ.faceWalk d' ~r [none, some 0, some 1] := by
  have hρ : k2Rotation.IsSpherical := IsSpherical.of_isAcyclic _ isAcyclic_top_fin_two
  have hface : ∀ d, k2Rotation.face d = d.symm := fun _ => rfl
  have hD : k2Rotation.faceDarts k2dart01 = [k2dart01, k2dart10] :=
    orbitList_eq_of_getElem (L := [k2dart01, k2dart10]) (by decide) (by decide) fun i hi => by
      rw [hface]
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i <;> rfl
  have hW : k2Rotation.faceWalk k2dart01 = [0, 1] := by simp [RotationSystem.faceWalk, hD]
  have hpq : IsConsecutive (k2Rotation.faceWalk k2dart01) {0, 1} 0 1 := by
    rw [hW]
    unfold IsConsecutive
    decide
  obtain ⟨τ, hτ, d', hd'⟩ := exists_isSpherical_attachVertex_faceWalk hρ (by rw [hW]; decide)
    (by rw [hW]; decide) (by decide) hpq
  have harc : closedArc [0, 1] (0 : Fin 2) 1 = [0, 1] := by decide
  rw [hW, harc] at hd'
  exact ⟨τ, hτ, d', by simpa using hd'⟩

end MonoidProduct.Graph
