import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MonoidProduct.Graph.Basic
set_option linter.style.header false

/-!
# Planar graphs through rotation systems

`monoid.tex`, section `sec:graph-certificates`, paragraph "Planarity and minor-closed
properties": a simple planar graph on `v ≥ 3` vertices has at most `3v - 6` edges.

Mathlib has no planar graphs.  Planarity is defined here combinatorially, by rotation systems
(combinatorial embeddings), the standard finite description of embeddings of graphs in surfaces
(Mohar and Thomassen, *Graphs on Surfaces*; Gross and Tucker, *Topological Graph Theory*).
Gonthier's formal proof of the Four Colour Theorem defines planar maps the same way, by the
Euler characteristic of their faces.

* `RotationSystem G`: a permutation `rot` of the darts of `G` (Mathlib's `SimpleGraph.Dart`,
  the ordered pairs of adjacent vertices) that keeps the tail of every dart and cycles through
  all the darts at each vertex.  Equivalently, a cyclic order of the edges at every vertex.
* Its faces are the orbits of the face permutation `face d = rot (d.symm)`: arriving at `w` along
  the dart `uw`, leave along the dart after `wu` around `w` (`RotationSystem.Face`).  A face lies
  in the component of the tails of its darts (`Face.component`).
* `RotationSystem.IsSpherical`: every connected component with an edge satisfies Euler's formula
  `V − E + F = 2`, with `V`, `E` and `F` its numbers of vertices, edges and faces.  For a connected
  graph, a rotation system determines a cellular embedding in an orientable surface of genus `g`
  with `V − E + F = 2 − 2g` (the Heffter–Edmonds rotation principle); spherical means genus `0`.
* `IsPlanar G`: `G` has a spherical rotation system.  A graph is planar in the topological sense
  exactly when each of its components is, and a connected graph exactly when it has a cellular
  embedding in the sphere; so this is the usual planarity.  That equivalence with topological
  drawings is cited, not formalized.  Isolated vertices impose no condition.  The counts are
  `Set.ncard`, so the definition is meant for finite `V`, as in every result below.

The edge bound uses only face lengths.  A face has no dart of length one (no loops), and has
length two only for an isolated edge.  So in a component with at least three vertices every face
has at least three darts (`three_mul_ncard_facesIn_le`), and at least four if `G` is
two-colourable, since a face of length three would be a triangle (`four_mul_ncard_facesIn_le`).
With `2E = Σ |faces|` per component (`ncard_dartsIn_eq`), Euler's formula gives `E ≤ 3V - 6`, or
`E ≤ 2V - 4`, for every component with at least three vertices.  Summing over the components,
with the components of one or two vertices counted separately, gives:

* `IsPlanar.ncard_edgeSet_le`: a planar graph on `v ≥ 3` vertices has at most `3v - 6` edges,
  connected or not, with bridges and isolated vertices;
* `IsPlanar.ncard_edgeSet_le_of_colorable`: a two-colourable planar graph on `v ≥ 3` vertices
  has at most `2v - 4` edges.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## Rotation systems and faces -/

variable (G) in
/-- **A rotation system** of `G`: a permutation `rot` of the darts that keeps the tail of every
dart and cycles through all the darts at each vertex, that is, a cyclic order of the edges at
every vertex. -/
structure RotationSystem where
  /-- The next dart around the same vertex. -/
  rot : Equiv.Perm G.Dart
  fst_rot : ∀ d, (rot d).fst = d.fst
  sameCycle_rot : ∀ d d' : G.Dart, d.fst = d'.fst → rot.SameCycle d d'

variable (G) in
/-- The reversal of darts, as a permutation. -/
def dartReverse : Equiv.Perm G.Dart := Function.Involutive.toPerm Dart.symm Dart.symm_involutive

@[simp] theorem dartReverse_apply (d : G.Dart) : dartReverse G d = d.symm := rfl

/-- A function constant along `f` is constant on the cycles of `f`. -/
theorem eq_of_sameCycle_of_forall {α β : Type*} {f : Equiv.Perm α} {g : α → β}
    (hg : ∀ x, g (f x) = g x) {x y : α} (h : f.SameCycle x y) : g x = g y := by
  obtain ⟨i, rfl⟩ := h
  suffices H : ∀ i : ℤ, ∀ x, g ((f ^ i) x) = g x from (H i x).symm
  intro i
  induction i with
  | zero => intro x; simp
  | succ n ih => intro x; rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hg]
  | pred n ih =>
      intro x
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      have := hg (f.symm x)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm

namespace RotationSystem

variable (ρ : RotationSystem G)

/-- **The face permutation**: from a dart `uw`, the dart after `wu` around `w`.  Its orbits are
the faces of the embedding. -/
def face : Equiv.Perm G.Dart := ρ.rot * dartReverse G

theorem face_apply (d : G.Dart) : ρ.face d = ρ.rot d.symm := rfl

/-- The next dart of a face starts at the head of the current one. -/
theorem fst_face (d : G.Dart) : (ρ.face d).fst = d.snd := by
  rw [face_apply, ρ.fst_rot]
  rfl

/-- **The faces**: the orbits of the face permutation. -/
abbrev Face : Type _ := Quotient (Equiv.Perm.SameCycle.setoid ρ.face)

/-- A face stays in one component. -/
theorem connectedComponentMk_fst_face (d : G.Dart) :
    G.connectedComponentMk (ρ.face d).fst = G.connectedComponentMk d.fst := by
  rw [fst_face]
  exact ConnectedComponent.eq.mpr d.adj.reachable.symm

/-- **The component of a face**: that of the tails of its darts. -/
def Face.component {ρ : RotationSystem G} : ρ.Face → G.ConnectedComponent :=
  Quotient.lift (fun d : G.Dart => G.connectedComponentMk d.fst) fun _ _ h =>
    eq_of_sameCycle_of_forall (g := fun d : G.Dart => G.connectedComponentMk d.fst)
      ρ.connectedComponentMk_fst_face h

@[simp] theorem Face.component_mk (d : G.Dart) :
    Face.component (⟦d⟧ : ρ.Face) = G.connectedComponentMk d.fst := rfl

/-- The faces in the component `c`. -/
def facesIn (c : G.ConnectedComponent) : Set ρ.Face := {f | f.component = c}

end RotationSystem

variable (G) in
/-- **The edges of a connected component**: those with both ends in it. -/
def componentEdges (c : G.ConnectedComponent) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∀ v ∈ e, G.connectedComponentMk v = c}

variable (G) in
/-- The darts of a connected component: those with their tail in it. -/
def dartsIn (c : G.ConnectedComponent) : Set G.Dart := {d | G.connectedComponentMk d.fst = c}

/-- **A spherical rotation system**: every connected component with an edge satisfies Euler's
formula `V − E + F = 2`, written `V + F = E + 2`. -/
def RotationSystem.IsSpherical (ρ : RotationSystem G) : Prop :=
  ∀ c : G.ConnectedComponent, (componentEdges G c).Nonempty →
    c.supp.ncard + (ρ.facesIn c).ncard = (componentEdges G c).ncard + 2

variable (G) in
/-- **Planarity**: `G` has a spherical rotation system, that is, a combinatorial embedding of
genus `0` of each of its components.  It is meant for finite `V`. -/
def IsPlanar : Prop := ∃ ρ : RotationSystem G, ρ.IsSpherical

/-! ## Counting darts, edges and faces in a component -/

section Counting

variable [Finite V]

/-- **Each edge of a component has two darts**: `|darts in c| = 2·|edges in c|`. -/
theorem ncard_dartsIn_eq (c : G.ConnectedComponent) :
    (dartsIn G c).ncard = 2 * (componentEdges G c).ncard := by
  classical
  have := Fintype.ofFinite V
  set D := Finset.univ.filter fun d : G.Dart => G.connectedComponentMk d.fst = c with hDdef
  set E := Finset.univ.filter fun e : Sym2 V => e ∈ componentEdges G c with hEdef
  have hD : dartsIn G c = ↑D := by ext; simp [D, dartsIn]
  have hE : componentEdges G c = ↑E := by ext; simp [E]
  rw [hD, hE, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := Dart.edge) (t := E) fun d hd => ?_]
  · rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun e he => ?_
    have he' : e ∈ componentEdges G c := (Finset.mem_filter.mp he).2
    have hfib : D.filter (fun d => d.edge = e) =
        Finset.univ.filter fun d : G.Dart => d.edge = e := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, D, and_iff_right_iff_imp]
      intro hde
      exact he'.2 d.fst (hde ▸ Sym2.mem_mk_left _ _)
    rw [hfib, dart_edge_fiber_card G e he'.1]
  · have hd' : G.connectedComponentMk d.fst = c := (Finset.mem_filter.mp hd).2
    refine Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.edge_mem, fun v hv => ?_⟩)
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hd'
    · exact (ConnectedComponent.eq.mpr d.adj.reachable.symm).trans hd'

/-- At most `C(|c|, 2)` edges lie in a component `c`. -/
theorem ncard_componentEdges_le (c : G.ConnectedComponent) :
    (componentEdges G c).ncard ≤ c.supp.ncard.choose 2 := by
  classical
  have := Fintype.ofFinite V
  set s := c.supp.toFinset
  have hsub : componentEdges G c ⊆ ↑(s.offDiag.image (Function.uncurry Sym2.mk)) := by
    rintro e ⟨he, hc⟩
    induction e using Sym2.ind with
    | h a b =>
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr
      ⟨?_, ?_, G.ne_of_adj he⟩, rfl⟩)
    · exact Set.mem_toFinset.mpr ((c.mem_supp_iff a).mpr (hc a (Sym2.mem_mk_left a b)))
    · exact Set.mem_toFinset.mpr ((c.mem_supp_iff b).mpr (hc b (Sym2.mem_mk_right a b)))
  calc (componentEdges G c).ncard
      ≤ (↑(s.offDiag.image (Function.uncurry Sym2.mk)) : Set (Sym2 V)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (s.offDiag.image (Function.uncurry Sym2.mk)).card := Set.ncard_coe_finset _
    _ = s.card.choose 2 := Sym2.card_image_offDiag s
    _ = c.supp.ncard.choose 2 := by rw [Set.ncard_eq_toFinset_card']

/-- A component with two vertices has an edge. -/
theorem componentEdges_nonempty {c : G.ConnectedComponent} (hc : 1 < c.supp.ncard) :
    (componentEdges G c).Nonempty := by
  obtain ⟨u, w, hu, hw, huw⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hc
  have hu' : G.connectedComponentMk u = c := (c.mem_supp_iff u).mp hu
  have hw' : G.connectedComponentMk w = c := (c.mem_supp_iff w).mp hw
  obtain ⟨p⟩ := ConnectedComponent.eq.mp (hu'.trans hw'.symm)
  cases p with
  | nil => exact absurd rfl huw
  | cons hadj _ =>
      refine ⟨_, G.mem_edgeSet.mpr hadj, fun v hv => ?_⟩
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hu'
      · exact (ConnectedComponent.eq.mpr hadj.reachable.symm).trans hu'

/-- Every component has a vertex. -/
theorem one_le_ncard_supp (c : G.ConnectedComponent) : 1 ≤ c.supp.ncard := by
  obtain ⟨v, rfl⟩ := c.exists_rep
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, (ConnectedComponent.mem_supp_iff _ v).mpr rfl⟩

end Counting

/-! ## Face lengths -/

namespace RotationSystem

variable (ρ : RotationSystem G)

/-- A face does not return after one step: there are no loops. -/
theorem face_ne (d : G.Dart) : ρ.face d ≠ d := fun h =>
  d.fst_ne_snd ((ρ.fst_face d).symm.trans (congrArg (fun d : G.Dart => d.fst) h)).symm

/-- **A face returns after two steps only around an isolated edge**: in a component with at
least three vertices, `face (face d) ≠ d`. -/
theorem face_face_ne [Finite V] (d : G.Dart)
    (hc : 3 ≤ (G.connectedComponentMk d.fst).supp.ncard) : ρ.face (ρ.face d) ≠ d := by
  intro h
  set u := d.fst
  set w := d.snd
  -- The second dart of the face is the reversal of `d`.
  have h1 : ρ.face d = d.symm := by
    have hsnd : (ρ.face d).snd = u := by
      have := congrArg (fun d : G.Dart => d.fst) h
      simp only [fst_face] at this
      exact this
    exact Dart.ext _ _ (Prod.ext (ρ.fst_face d) hsnd)
  -- So `rot` fixes `d.symm` and `d`.
  have hfix_symm : ρ.rot d.symm = d.symm := h1
  have hfix : ρ.rot d = d := by
    have := h
    rw [h1, face_apply, Dart.symm_symm] at this
    exact this
  -- `u` and `w` have no other neighbours.
  have hnu : ∀ y, G.Adj u y → y = w := fun y hy => by
    have := (ρ.sameCycle_rot d ⟨(u, y), hy⟩ rfl).eq_of_left hfix
    exact (congrArg (fun d : G.Dart => d.snd) this).symm
  have hnw : ∀ y, G.Adj w y → y = u := fun y hy => by
    have := (ρ.sameCycle_rot d.symm ⟨(w, y), hy⟩ rfl).eq_of_left hfix_symm
    exact (congrArg (fun d : G.Dart => d.snd) this).symm
  -- Hence the component is `{u, w}`.
  have hreach : ∀ z, G.Reachable u z → z ∈ ({u, w} : Set V) := by
    intro z hz
    rw [reachable_iff_reflTransGen] at hz
    induction hz with
    | refl => exact Set.mem_insert u _
    | tail _ hab ih =>
        rcases Set.mem_insert_iff.mp ih with hb | hb
        · rw [hb] at hab
          exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (hnu _ hab))
        · rw [Set.mem_singleton_iff.mp hb] at hab
          exact Set.mem_insert_iff.mpr (Or.inl (hnw _ hab))
  have hsub : (G.connectedComponentMk u).supp ⊆ {u, w} := fun z hz =>
    hreach z (ConnectedComponent.eq.mp ((ConnectedComponent.mem_supp_iff _ z).mp hz).symm)
  have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_insert_le u {w})
  rw [Set.ncard_singleton] at this
  omega

/-- Three darts of a face, the start and the next two, are distinct in a component with at least
three vertices. -/
theorem three_le_ncard_sameCycle [Finite V] (d : G.Dart)
    (hc : 3 ≤ (G.connectedComponentMk d.fst).supp.ncard) :
    3 ≤ {d' | ρ.face.SameCycle d d'}.ncard := by
  classical
  have := Fintype.ofFinite V
  have h1 := ρ.face_ne d
  have h2 := ρ.face_face_ne d hc
  have h3 := ρ.face_ne (ρ.face d)
  have hsub : (↑({d, ρ.face d, ρ.face (ρ.face d)} : Finset G.Dart) : Set G.Dart) ⊆
      {d' | ρ.face.SameCycle d d'} := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.rfl
    · exact Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl
    · exact Equiv.Perm.sameCycle_apply_right.mpr
        (Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl)
  have hcard : ({d, ρ.face d, ρ.face (ρ.face d)} : Finset G.Dart).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm h1, Ne.symm h2]),
      Finset.card_pair (Ne.symm h3)]
  rw [← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **In a two-colourable graph a face has at least four darts**, in a component with at least
three vertices: a face of length three would be a triangle. -/
theorem four_le_ncard_sameCycle [Finite V] (hcol : G.Colorable 2) (d : G.Dart)
    (hc : 3 ≤ (G.connectedComponentMk d.fst).supp.ncard) :
    4 ≤ {d' | ρ.face.SameCycle d d'}.ncard := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨C⟩ := hcol
  set d₁ := ρ.face d
  set d₂ := ρ.face d₁
  set d₃ := ρ.face d₂
  have hc₁ : 3 ≤ (G.connectedComponentMk d₁.fst).supp.ncard := by
    rw [ρ.connectedComponentMk_fst_face]
    exact hc
  have h01 : d₁ ≠ d := ρ.face_ne d
  have h02 : d₂ ≠ d := ρ.face_face_ne d hc
  have h12 : d₂ ≠ d₁ := ρ.face_ne d₁
  have h13 : d₃ ≠ d₁ := ρ.face_face_ne d₁ hc₁
  have h23 : d₃ ≠ d₂ := ρ.face_ne d₂
  -- A face of length three would be a triangle.
  have h03 : d₃ ≠ d := by
    intro h
    have ha : d₁.fst = d.snd := ρ.fst_face d
    have hb : d₂.fst = d₁.snd := ρ.fst_face d₁
    have hcl : d₂.snd = d.fst := by
      have := ρ.fst_face d₂
      rw [show ρ.face d₂ = d from h] at this
      exact this.symm
    have e1 := C.valid d.adj
    have e2 := C.valid d₁.adj
    have e3 := C.valid d₂.adj
    rw [ha] at e2
    rw [hb, hcl] at e3
    have key : ∀ x y z : Fin 2, x ≠ y → y ≠ z → z ≠ x → False := by decide
    exact key _ _ _ e1 e2 e3
  have hsub : (↑({d, d₁, d₂, d₃} : Finset G.Dart) : Set G.Dart) ⊆
      {d' | ρ.face.SameCycle d d'} := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    have s1 : ρ.face.SameCycle d d₁ := Equiv.Perm.sameCycle_apply_right.mpr .rfl
    have s2 : ρ.face.SameCycle d d₂ := Equiv.Perm.sameCycle_apply_right.mpr s1
    have s3 : ρ.face.SameCycle d d₃ := Equiv.Perm.sameCycle_apply_right.mpr s2
    rcases hx with rfl | rfl | rfl | rfl
    exacts [.rfl, s1, s2, s3]
  have hcard : ({d, d₁, d₂, d₃} : Finset G.Dart).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm h01, Ne.symm h02, Ne.symm h03]),
      Finset.card_insert_of_notMem (by simp [Ne.symm h12, Ne.symm h13]),
      Finset.card_pair (Ne.symm h23)]
  rw [← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **Counting faces by their darts**: if every face in `c` has at least `n` darts, then
`n·|faces in c| ≤ |darts in c|`. -/
theorem mul_ncard_facesIn_le [Finite V] (c : G.ConnectedComponent) (n : ℕ)
    (h : ∀ d : G.Dart, G.connectedComponentMk d.fst = c →
      n ≤ {d' | ρ.face.SameCycle d d'}.ncard) :
    n * (ρ.facesIn c).ncard ≤ (dartsIn G c).ncard := by
  classical
  have := Fintype.ofFinite V
  have : Fintype ρ.Face := Fintype.ofFinite _
  set D := Finset.univ.filter fun d : G.Dart => G.connectedComponentMk d.fst = c with hDdef
  set Fc := Finset.univ.filter fun f : ρ.Face => f.component = c with hFcdef
  have hD : dartsIn G c = ↑D := by ext; simp [D, dartsIn]
  have hF : ρ.facesIn c = ↑Fc := by ext; simp [Fc, facesIn]
  rw [hD, hF, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := fun d : G.Dart => (⟦d⟧ : ρ.Face)) (s := D) (t := Fc)
      fun d hd => Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hd).2⟩)]
  rw [mul_comm, ← smul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun q hq => ?_
  induction q using Quotient.inductionOn with
  | h d₀ =>
  have hd₀ : G.connectedComponentMk d₀.fst = c := (Finset.mem_filter.mp hq).2
  have hfib : {d' | ρ.face.SameCycle d₀ d'} =
      ↑(D.filter fun d => (⟦d⟧ : ρ.Face) = ⟦d₀⟧) := by
    ext d'
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, D, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hs
      refine ⟨?_, Quotient.sound hs.symm⟩
      rw [← hd₀]
      exact (eq_of_sameCycle_of_forall (g := fun d : G.Dart => G.connectedComponentMk d.fst)
        ρ.connectedComponentMk_fst_face hs).symm
    · rintro ⟨-, hq'⟩
      exact (Quotient.exact hq').symm
  rw [← Set.ncard_coe_finset, ← hfib]
  exact h d₀ hd₀

end RotationSystem

/-! ## The edge bounds -/

/-- **Euler's formula with faces of at least `g` darts**, in a component with at least three
vertices: `g·E + 2g ≤ g·V + 2E`. -/
theorem RotationSystem.IsSpherical.mul_le_of_faces [Finite V] {ρ : RotationSystem G}
    (hρ : ρ.IsSpherical) {g : ℕ} {c : G.ConnectedComponent} (hc : 3 ≤ c.supp.ncard)
    (hface : g * (ρ.facesIn c).ncard ≤ (dartsIn G c).ncard) :
    g * (componentEdges G c).ncard + 2 * g ≤ g * c.supp.ncard + 2 * (componentEdges G c).ncard := by
  have h1 := hρ c (componentEdges_nonempty (by omega))
  have h2 := ncard_dartsIn_eq c
  calc g * (componentEdges G c).ncard + 2 * g = g * ((componentEdges G c).ncard + 2) := by ring
    _ = g * (c.supp.ncard + (ρ.facesIn c).ncard) := by rw [h1]
    _ = g * c.supp.ncard + g * (ρ.facesIn c).ncard := by ring
    _ ≤ g * c.supp.ncard + 2 * (componentEdges G c).ncard := by omega

/-- A component with at most two vertices has fewer edges than vertices. -/
theorem ncard_componentEdges_lt_of_le_two [Finite V] {c : G.ConnectedComponent}
    (hc : c.supp.ncard ≤ 2) : (componentEdges G c).ncard < c.supp.ncard := by
  have h1 := ncard_componentEdges_le c
  have h2 := one_le_ncard_supp c
  rcases (show c.supp.ncard = 1 ∨ c.supp.ncard = 2 by omega) with h | h
  · rw [h] at h1 ⊢
    have : Nat.choose 1 2 = 0 := by decide
    omega
  · rw [h] at h1 ⊢
    have : Nat.choose 2 2 = 1 := by decide
    omega

/-- **Summing over the components**: per-component bounds `a·E_c + b ≤ b·V_c`, improved to
`a·E_c + 2b ≤ b·V_c` on the components with at least three vertices, give `a·E + 2b ≤ b·V` for
`V ≥ 3`. -/
theorem mul_ncard_edgeSet_add_le [Fintype V] {a b : ℕ}
    (hsmall : ∀ c : G.ConnectedComponent,
      a * (componentEdges G c).ncard + b ≤ b * c.supp.ncard)
    (hbig : ∀ c : G.ConnectedComponent, 3 ≤ c.supp.ncard →
      a * (componentEdges G c).ncard + 2 * b ≤ b * c.supp.ncard)
    (hv : 3 ≤ Fintype.card V) : a * G.edgeSet.ncard + 2 * b ≤ b * Fintype.card V := by
  classical
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  -- The vertices and the edges are the sums over the components.
  have hV : ∑ c : G.ConnectedComponent, c.supp.ncard = Fintype.card V := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := G.connectedComponentMk)
      (t := Finset.univ) fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp [ConnectedComponent.mem_supp_iff]
  have hE : ∑ c : G.ConnectedComponent, (componentEdges G c).ncard = G.edgeSet.ncard := by
    have hD : ∑ c : G.ConnectedComponent, (dartsIn G c).ncard = Fintype.card G.Dart := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
        (f := fun d : G.Dart => G.connectedComponentMk d.fst) (t := Finset.univ)
        fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Set.ncard_coe_finset]
      congr 1
      ext d
      simp [dartsIn]
    simp only [ncard_dartsIn_eq, ← Finset.mul_sum] at hD
    rw [dart_card_eq_twice_card_edges, ← coe_edgeFinset, Set.ncard_coe_finset] at *
    omega
  by_cases hone : Fintype.card G.ConnectedComponent ≤ 1
  · -- One component, holding every vertex and every edge.
    obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hall : ∀ c, c = G.connectedComponentMk v₀ := fun c =>
      Fintype.card_le_one_iff.mp hone c _
    have hsum : ∀ f : G.ConnectedComponent → ℕ, ∑ c, f c = f (G.connectedComponentMk v₀) :=
      fun f => Fintype.sum_eq_single _ fun c hc => absurd (hall c) hc
    rw [hsum] at hV hE
    have := hbig _ (by rw [hV]; exact hv)
    rwa [hV, hE] at this
  · -- At least two components: sum the per-component bounds.
    have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hsmall c
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hE, hV, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] at hsum
    have h2 : 2 * b ≤ Fintype.card G.ConnectedComponent * b :=
      Nat.mul_le_mul_right b (by omega)
    omega

/-- **`|E| ≤ 3v - 6`** (`sec:graph-certificates`): a planar graph on `v ≥ 3` vertices has at
most `3v - 6` edges, whether or not it is connected. -/
theorem IsPlanar.ncard_edgeSet_le [Fintype V] (h : IsPlanar G) (hv : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨ρ, hρ⟩ := h
  have hbig : ∀ c : G.ConnectedComponent, 3 ≤ c.supp.ncard →
      1 * (componentEdges G c).ncard + 2 * 3 ≤ 3 * c.supp.ncard := fun c hc => by
    have := hρ.mul_le_of_faces hc (ρ.mul_ncard_facesIn_le c 3 fun d hd =>
      ρ.three_le_ncard_sameCycle d (by rw [hd]; exact hc))
    omega
  have := mul_ncard_edgeSet_add_le (a := 1) (b := 3) (fun c => by
    by_cases hc : 3 ≤ c.supp.ncard
    · have := hbig c hc
      omega
    · have := ncard_componentEdges_lt_of_le_two (G := G) (c := c) (by omega)
      omega) hbig hv
  omega

/-- **`|E| ≤ 2v - 4` for two-colourable planar graphs** on `v ≥ 3` vertices. -/
theorem IsPlanar.ncard_edgeSet_le_of_colorable [Fintype V] (h : IsPlanar G)
    (hcol : G.Colorable 2) (hv : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 2 * Fintype.card V - 4 := by
  obtain ⟨ρ, hρ⟩ := h
  have hbig : ∀ c : G.ConnectedComponent, 3 ≤ c.supp.ncard →
      2 * (componentEdges G c).ncard + 2 * 4 ≤ 4 * c.supp.ncard := fun c hc => by
    have := hρ.mul_le_of_faces hc (ρ.mul_ncard_facesIn_le c 4 fun d hd =>
      ρ.four_le_ncard_sameCycle hcol d (by rw [hd]; exact hc))
    omega
  have := mul_ncard_edgeSet_add_le (a := 2) (b := 4) (fun c => by
    by_cases hc : 3 ≤ c.supp.ncard
    · have := hbig c hc
      omega
    · have := ncard_componentEdges_lt_of_le_two (G := G) (c := c) (by omega)
      omega) hbig hv
  omega

end MonoidProduct.Graph
