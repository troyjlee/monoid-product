import MonoidProduct.Graph.PlanarContraction
import MonoidProduct.Graph.WagnerConnectivity
set_option linter.style.header false

/-!
# Splitting a vertex of a rotation system

A transposition of two darts `a` and `b` at a vertex, applied on the left of the rotation, splits
the rotation cycle at that vertex in two.  The result is a rotation system of the graph in which
the vertex is split into two vertices, each keeping the neighbours along one of the two cycles.
When `a` and `b` lie on one face, that face splits too; if the graph is `2`-connected, the split
graph stays connected and the Euler defect drops by two.

* **Left multiplication by a transposition**: `swap a b * p` is `p * swap a b` conjugated by
  `swap a b` (`swap_mul_eq_permCongr`).  So it splits the cycle through `a ≠ b` when they lie in
  one cycle (`not_sameCycle_swap_mul_of_sameCycle`, `cycleCount_swap_mul_of_sameCycle`), and two
  elements of one cycle of `p` stay in one cycle unless they fall into the cycles of `a` and `b`
  (`sameCycle_swap_mul_or`).
* `dartGraph ψ hψ`: **the graph presented by relabelled darts**, on a type `W`, with an edge from
  `ψ d` to `ψ d.symm` for every dart `d` of `G`; `ψ d` is the new tail of `d`.  When `ψ d` and
  `ψ d.symm` determine `d`, its darts are those of `G` (`dartGraphEquiv`), so it has as many edges
  as `G` (`ncard_edgeSet_dartGraph`), and a permutation of the darts of `G` that keeps the new
  tails and is transitive on each set of darts with one new tail is a rotation system of it
  (`RotationSystem.ofDartGraph`), with face permutation `r * dartReverse G` on the old darts
  (`ofDartGraph_face`).
* `RotationSystem.splitTail ρ a b`: the darts with the tail of `b` that lie in the cycle of `b` for
  `swap a b * ρ.rot` get the new vertex `none`; the others keep their tails.  `splitGraph ρ a b`
  is the graph on `Option V` that it presents: the tail of `b` is split into `some` of it and
  `none`.  For darts `a` and `b` with one tail, `splitRotation ρ a b` is the rotation
  `swap a b * ρ.rot` as a rotation system of the split graph.
* `eulerDefect_splitRotation`: for distinct darts `a` and `b` with one tail on one face of a
  `2`-connected graph, the split graph is connected (`splitGraph_connected`), with one vertex and
  one face more, the same number of edges and no isolated vertex, so **its Euler defect is that
  of `ρ` less two**.
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm

/-! ## Left multiplication by a transposition -/

section SwapMul

variable {α : Type*} [DecidableEq α]

/-- **A transposition on the left is a conjugate of a transposition on the right**:
`swap a b * p` is `p * swap a b` conjugated by `swap a b`. -/
theorem swap_mul_eq_permCongr (p : Perm α) (a b : α) :
    swap a b * p = (swap a b).permCongr (p * swap a b) := by
  ext x
  simp only [Equiv.permCongr_apply, symm_swap, mul_apply, swap_apply_self]

/-- The cycles of `swap a b * p` are those of `p * swap a b`, moved by `swap a b`. -/
theorem sameCycle_swap_mul_iff (p : Perm α) (a b x y : α) :
    (swap a b * p).SameCycle x y ↔ (p * swap a b).SameCycle (swap a b x) (swap a b y) := by
  have h := sameCycle_permCongr (swap a b) (p * swap a b) (x := swap a b x) (y := swap a b y)
  rwa [swap_apply_self, swap_apply_self, ← swap_mul_eq_permCongr] at h

variable [Finite α]

/-- **Splitting by a transposition on the left**: if `a ≠ b` lie in one cycle of `p`, they lie in
different cycles of `swap a b * p`. -/
theorem not_sameCycle_swap_mul_of_sameCycle {p : Perm α} {a b : α} (hne : a ≠ b)
    (hab : p.SameCycle a b) : ¬ (swap a b * p).SameCycle a b := by
  rw [sameCycle_swap_mul_iff, swap_apply_left, swap_apply_right]
  exact fun h => not_sameCycle_mul_swap_of_sameCycle hne hab h.symm

/-- **A transposition on the left inside a cycle splits it**: if `a ≠ b` lie in one cycle of `p`,
then `swap a b * p` has one cycle more. -/
theorem cycleCount_swap_mul_of_sameCycle {p : Perm α} {a b : α} (hne : a ≠ b)
    (hab : p.SameCycle a b) : cycleCount (swap a b * p) = cycleCount p + 1 := by
  rw [swap_mul_eq_permCongr, cycleCount_permCongr, cycleCount_mul_swap_of_sameCycle hne hab]

/-- **Two elements of one cycle of `p`** lie in one cycle of `swap a b * p`, or each of them lies
in the cycle of `a` or of `b`, when `a` and `b` lie in one cycle of `p`. -/
theorem sameCycle_swap_mul_or {p : Perm α} {a b : α} (hab : p.SameCycle a b) {x y : α}
    (h : p.SameCycle x y) :
    (swap a b * p).SameCycle x y ∨
      (((swap a b * p).SameCycle x a ∨ (swap a b * p).SameCycle x b) ∧
        ((swap a b * p).SameCycle y a ∨ (swap a b * p).SameCycle y b)) := by
  have hsw : ∀ x, p.SameCycle (swap a b x) x := fun x => by
    rcases eq_or_ne x a with rfl | hxa
    · rw [swap_apply_left]
      exact hab.symm
    rcases eq_or_ne x b with rfl | hxb
    · rw [swap_apply_right]
      exact hab
    rw [swap_apply_of_ne_of_ne hxa hxb]
  have h' : p.SameCycle (swap a b x) (swap a b y) := (hsw x).trans (h.trans (hsw y).symm)
  simp only [sameCycle_swap_mul_iff, swap_apply_left, swap_apply_right]
  rcases sameCycle_or_of_agree (fun z ha hb => mul_swap_apply_of_ne p ha hb) h' with
    h'' | ⟨hx, hy⟩
  · exact Or.inl h''
  · exact Or.inr ⟨hx.symm, hy.symm⟩

end SwapMul

/-! ## Graphs presented by relabelled darts -/

section DartGraph

variable {V W : Type*} {G : SimpleGraph V}

/-- **The graph presented by relabelled darts**: for a map `ψ` from the darts of `G` to `W` with
`ψ d ≠ ψ d.symm`, the graph on `W` with an edge from `ψ d` to `ψ d.symm` for every dart `d`.  Here
`ψ d` is the new tail of `d` and `ψ d.symm` its new head. -/
def dartGraph (ψ : G.Dart → W) (hψ : ∀ d, ψ d ≠ ψ d.symm) : SimpleGraph W where
  Adj p q := ∃ d : G.Dart, ψ d = p ∧ ψ d.symm = q
  symm := ⟨fun _ _ ⟨d, h1, h2⟩ => ⟨d.symm, h2, h1⟩⟩
  loopless := ⟨fun _ ⟨d, h1, h2⟩ => hψ d (h1.trans h2.symm)⟩

variable (ψ : G.Dart → W) (hψ : ∀ d, ψ d ≠ ψ d.symm)

theorem dartGraph_adj {p q : W} :
    (dartGraph ψ hψ).Adj p q ↔ ∃ d : G.Dart, ψ d = p ∧ ψ d.symm = q :=
  Iff.rfl

/-- The dart of `dartGraph ψ hψ` given by a dart of `G`. -/
def toDartGraph (d : G.Dart) : (dartGraph ψ hψ).Dart := ⟨(ψ d, ψ d.symm), d, rfl, rfl⟩

@[simp] theorem fst_toDartGraph (d : G.Dart) : (toDartGraph ψ hψ d).fst = ψ d := rfl

@[simp] theorem snd_toDartGraph (d : G.Dart) : (toDartGraph ψ hψ d).snd = ψ d.symm := rfl

/-- The relabelling commutes with reversal. -/
theorem toDartGraph_symm (d : G.Dart) :
    toDartGraph ψ hψ d.symm = (toDartGraph ψ hψ d).symm :=
  rfl

/-- Every dart of `dartGraph ψ hψ` comes from a dart of `G`. -/
theorem toDartGraph_surjective : Function.Surjective (toDartGraph ψ hψ) := by
  rintro ⟨⟨p, q⟩, d, h1, h2⟩
  exact ⟨d, Dart.ext _ _ (Prod.ext h1 h2)⟩

variable {ψ} in
theorem toDartGraph_injective (hinj : ∀ d d', ψ d = ψ d' → ψ d.symm = ψ d'.symm → d = d') :
    Function.Injective (toDartGraph ψ hψ) := fun d d' h =>
  hinj d d' (congrArg (fun e : (dartGraph ψ hψ).Dart => e.fst) h)
    (congrArg (fun e : (dartGraph ψ hψ).Dart => e.snd) h)

variable (hinj : ∀ d d', ψ d = ψ d' → ψ d.symm = ψ d'.symm → d = d')

/-- **The darts of `dartGraph ψ hψ` are those of `G`**, when `ψ d` and `ψ d.symm` determine `d`. -/
noncomputable def dartGraphEquiv : G.Dart ≃ (dartGraph ψ hψ).Dart :=
  Equiv.ofBijective (toDartGraph ψ hψ) ⟨toDartGraph_injective hψ hinj, toDartGraph_surjective ψ hψ⟩

theorem dartGraphEquiv_apply (d : G.Dart) : dartGraphEquiv ψ hψ hinj d = toDartGraph ψ hψ d :=
  rfl

/-- **`dartGraph ψ hψ` has the edges of `G`**: both have half as many edges as darts. -/
theorem ncard_edgeSet_dartGraph [Finite V] [Finite W]
    (hinj : ∀ d d', ψ d = ψ d' → ψ d.symm = ψ d'.symm → d = d') :
    (dartGraph ψ hψ).edgeSet.ncard = G.edgeSet.ncard := by
  have h1 := two_mul_ncard_edgeSet_eq_natCard_dart (G := dartGraph ψ hψ)
  have h2 := two_mul_ncard_edgeSet_eq_natCard_dart (G := G)
  have h3 := Nat.card_congr (dartGraphEquiv ψ hψ hinj)
  omega

namespace RotationSystem

/-- **A rotation system of `dartGraph ψ hψ`**: a permutation of the darts of `G` that keeps the new
tails and is transitive on the darts with one new tail. -/
noncomputable def ofDartGraph (r : Perm G.Dart) (hr : ∀ d, ψ (r d) = ψ d)
    (hsc : ∀ d d', ψ d = ψ d' → r.SameCycle d d') : RotationSystem (dartGraph ψ hψ) where
  rot := (dartGraphEquiv ψ hψ hinj).permCongr r
  fst_rot d := by
    obtain ⟨x, rfl⟩ := (dartGraphEquiv ψ hψ hinj).surjective d
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact hr x
  sameCycle_rot d d' h := by
    obtain ⟨x, rfl⟩ := (dartGraphEquiv ψ hψ hinj).surjective d
    obtain ⟨x', rfl⟩ := (dartGraphEquiv ψ hψ hinj).surjective d'
    rw [sameCycle_permCongr]
    exact hsc x x' h

variable (r : Perm G.Dart) (hr : ∀ d, ψ (r d) = ψ d) (hsc : ∀ d d', ψ d = ψ d' → r.SameCycle d d')

theorem ofDartGraph_rot :
    (ofDartGraph ψ hψ hinj r hr hsc).rot = (dartGraphEquiv ψ hψ hinj).permCongr r :=
  rfl

/-- **The faces of `ofDartGraph`**: the face permutation is `r * dartReverse G` on the darts of
`G`. -/
theorem ofDartGraph_face :
    (ofDartGraph ψ hψ hinj r hr hsc).face =
      (dartGraphEquiv ψ hψ hinj).permCongr (r * dartReverse G) := by
  refine Equiv.ext fun d => ?_
  obtain ⟨x, rfl⟩ := (dartGraphEquiv ψ hψ hinj).surjective d
  have hs : (dartGraphEquiv ψ hψ hinj x).symm = dartGraphEquiv ψ hψ hinj x.symm := rfl
  rw [face_apply, ofDartGraph_rot, hs, Equiv.permCongr_apply, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

/-- The faces of `ofDartGraph` are the cycles of `r * dartReverse G`. -/
theorem natCard_face_ofDartGraph :
    Nat.card (ofDartGraph ψ hψ hinj r hr hsc).Face = cycleCount (r * dartReverse G) := by
  change cycleCount (ofDartGraph ψ hψ hinj r hr hsc).face = _
  rw [ofDartGraph_face, cycleCount_permCongr]

end RotationSystem

end DartGraph

/-! ## Splitting a vertex -/

/-- **A connected graph has one component.** -/
theorem natCard_connectedComponent_eq_one {W : Type*} {H : SimpleGraph W} (h : H.Connected) :
    Nat.card H.ConnectedComponent = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨h.preconnected.subsingleton_connectedComponent,
    ⟨H.connectedComponentMk h.nonempty.some⟩⟩

section Split

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

namespace RotationSystem

variable (ρ : RotationSystem G) (a b : G.Dart)

open Classical in
/-- **The tails after splitting the tail of `b`**: the darts with the tail of `b` in the cycle of
`b` for `swap a b * ρ.rot` go to the new vertex `none`; the other darts keep their tails. -/
noncomputable def splitTail (d : G.Dart) : Option V :=
  if (swap a b * ρ.rot).SameCycle b d ∧ d.fst = b.fst then none else some d.fst

variable {ρ a b}

theorem splitTail_eq_none {d : G.Dart} (h : (swap a b * ρ.rot).SameCycle b d)
    (hd : d.fst = b.fst) : ρ.splitTail a b d = none :=
  ite_eq_left ⟨h, hd⟩

theorem splitTail_eq_some {d : G.Dart}
    (h : ¬ ((swap a b * ρ.rot).SameCycle b d ∧ d.fst = b.fst)) :
    ρ.splitTail a b d = some d.fst :=
  ite_eq_right h

/-- A dart away from the tail of `b` keeps its tail. -/
theorem splitTail_of_fst_ne {d : G.Dart} (hd : d.fst ≠ b.fst) : ρ.splitTail a b d = some d.fst :=
  splitTail_eq_some fun h => hd h.2

theorem splitTail_self : ρ.splitTail a b b = none :=
  splitTail_eq_none (SameCycle.refl _ _) rfl

/-- **The new tail determines the old one.** -/
theorem fst_eq_of_splitTail_eq {d d' : G.Dart} (h : ρ.splitTail a b d = ρ.splitTail a b d') :
    d.fst = d'.fst := by
  by_cases h1 : (swap a b * ρ.rot).SameCycle b d ∧ d.fst = b.fst <;>
    by_cases h2 : (swap a b * ρ.rot).SameCycle b d' ∧ d'.fst = b.fst
  · exact h1.2.trans h2.2.symm
  · rw [splitTail_eq_none h1.1 h1.2, splitTail_eq_some h2] at h
    exact (Option.some_ne_none _ h.symm).elim
  · rw [splitTail_eq_some h1, splitTail_eq_none h2.1 h2.2] at h
    exact (Option.some_ne_none _ h).elim
  · rw [splitTail_eq_some h1, splitTail_eq_some h2] at h
    exact Option.some.inj h

variable (ρ a b)

theorem splitTail_ne_symm (d : G.Dart) : ρ.splitTail a b d ≠ ρ.splitTail a b d.symm := fun h =>
  d.adj.ne (fst_eq_of_splitTail_eq h)

theorem splitTail_inj (d d' : G.Dart) (h : ρ.splitTail a b d = ρ.splitTail a b d')
    (h' : ρ.splitTail a b d.symm = ρ.splitTail a b d'.symm) : d = d' :=
  Dart.ext _ _ (Prod.ext (fst_eq_of_splitTail_eq h) (fst_eq_of_splitTail_eq h'))

/-- **The split graph**: the tail of `b` is split into two vertices, `some` of it, keeping the
neighbours whose darts lie outside the cycle of `b` for `swap a b * ρ.rot`, and the new vertex
`none`, taking the others. -/
noncomputable def splitGraph : SimpleGraph (Option V) :=
  dartGraph (ρ.splitTail a b) (splitTail_ne_symm ρ a b)

variable {ρ a b}

/-- The split rotation keeps tails, since `a` and `b` have one tail. -/
theorem fst_swap_mul_rot (hfst : a.fst = b.fst) (d : G.Dart) :
    ((swap a b * ρ.rot) d).fst = d.fst :=
  (apply_swap_eq_self (v := fun d : G.Dart => d.fst) hfst (ρ.rot d)).trans (ρ.fst_rot d)

/-- The split rotation keeps the new tails. -/
theorem splitTail_swap_mul_rot (hfst : a.fst = b.fst) (d : G.Dart) :
    ρ.splitTail a b ((swap a b * ρ.rot) d) = ρ.splitTail a b d := by
  unfold splitTail
  rw [sameCycle_apply_right, fst_swap_mul_rot hfst]

/-- **The split rotation is transitive on the darts with one new tail**: the darts at `none` form
the cycle of `b`, and the other darts at the tail of `b` lie in the cycle of `a`. -/
theorem sameCycle_of_splitTail_eq [Finite V] (hfst : a.fst = b.fst) {d d' : G.Dart}
    (h : ρ.splitTail a b d = ρ.splitTail a b d') : (swap a b * ρ.rot).SameCycle d d' := by
  have := finite_dart (G := G)
  have hrot : ρ.rot.SameCycle a b := ρ.sameCycle_rot a b hfst
  have hdd' : ρ.rot.SameCycle d d' := ρ.sameCycle_rot d d' (fst_eq_of_splitTail_eq h)
  -- The darts of the cycle of `b` have the tail of `b`.
  have hb : ∀ {x : G.Dart}, (swap a b * ρ.rot).SameCycle x b → x.fst = b.fst := fun hx =>
    eq_of_sameCycle_of_forall (g := fun d : G.Dart => d.fst) (fst_swap_mul_rot hfst) hx
  by_cases h1 : (swap a b * ρ.rot).SameCycle b d ∧ d.fst = b.fst
  · have h2 : (swap a b * ρ.rot).SameCycle b d' ∧ d'.fst = b.fst := by
      by_contra h2
      rw [splitTail_eq_none h1.1 h1.2, splitTail_eq_some h2] at h
      exact Option.some_ne_none _ h.symm
    exact h1.1.symm.trans h2.1
  · have h2 : ¬ ((swap a b * ρ.rot).SameCycle b d' ∧ d'.fst = b.fst) := by
      intro h2
      rw [splitTail_eq_some h1, splitTail_eq_none h2.1 h2.2] at h
      exact Option.some_ne_none _ h
    rcases sameCycle_swap_mul_or hrot hdd' with h' | ⟨hx, hy⟩
    · exact h'
    · have hxa := hx.resolve_right fun hxb => h1 ⟨hxb.symm, hb hxb⟩
      have hya := hy.resolve_right fun hyb => h2 ⟨hyb.symm, hb hyb⟩
      exact hxa.trans hya.symm

variable (ρ a b) in
/-- **The split rotation system**: `swap a b * ρ.rot` as a rotation system of the split graph, for
darts `a` and `b` with one tail. -/
noncomputable def splitRotation [Finite V] (hfst : a.fst = b.fst) :
    RotationSystem (ρ.splitGraph a b) :=
  ofDartGraph (ρ.splitTail a b) (splitTail_ne_symm ρ a b) (splitTail_inj ρ a b)
    (swap a b * ρ.rot) (splitTail_swap_mul_rot hfst) fun _ _ => sameCycle_of_splitTail_eq hfst

/-! ### The counts after splitting -/

/-- `a` keeps its tail: it is not in the cycle of `b` for the split rotation. -/
theorem splitTail_left [Finite V] (hab : a ≠ b) (hfst : a.fst = b.fst) :
    ρ.splitTail a b a = some a.fst := by
  have := finite_dart (G := G)
  exact splitTail_eq_some fun h =>
    not_sameCycle_swap_mul_of_sameCycle hab (ρ.sameCycle_rot a b hfst) h.1.symm

/-- Edges away from the tail of `b` stay. -/
theorem splitGraph_adj_some_some {u w : V} (hu : u ≠ b.fst) (hw : w ≠ b.fst) (h : G.Adj u w) :
    (ρ.splitGraph a b).Adj (some u) (some w) :=
  ⟨⟨(u, w), h⟩, splitTail_of_fst_ne hu, splitTail_of_fst_ne hw⟩

/-- The new vertex keeps the edge of `b`. -/
theorem splitGraph_adj_none : (ρ.splitGraph a b).Adj none (some b.snd) :=
  ⟨b, splitTail_self, splitTail_of_fst_ne b.adj.ne.symm⟩

/-- The old vertex keeps the edge of `a`. -/
theorem splitGraph_adj_some_fst [Finite V] (hab : a ≠ b) (hfst : a.fst = b.fst) :
    (ρ.splitGraph a b).Adj (some b.fst) (some a.snd) :=
  ⟨a, by rw [splitTail_left hab hfst, hfst],
    splitTail_of_fst_ne fun h => a.adj.ne (hfst.trans h.symm)⟩

/-- **The split graph of a `2`-connected graph is connected**: deleting the split vertex leaves a
connected graph, and each half of it keeps a neighbour there. -/
theorem splitGraph_connected [Finite V] (hab : a ≠ b) (hfst : a.fst = b.fst)
    (hG : IsKConnected G 2) : (ρ.splitGraph a b).Connected := by
  have hconn := hG.2 {b.fst} (by rw [Finset.card_singleton]; norm_num)
  let φ : G.induce {v | v ∉ ({b.fst} : Finset V)} →g ρ.splitGraph a b :=
    { toFun := fun v => some v.1
      map_rel' := fun {u w} h => splitGraph_adj_some_some (by simpa using u.2)
        (by simpa using w.2) h }
  have hreach : ∀ u w : V, u ≠ b.fst → w ≠ b.fst →
      (ρ.splitGraph a b).Reachable (some u) (some w) := fun u w hu hw =>
    (hconn.preconnected ⟨u, by simpa using hu⟩ ⟨w, by simpa using hw⟩).map φ
  have hv₀ : a.snd ≠ b.fst := fun h => a.adj.ne (hfst.trans h.symm)
  have hall : ∀ p : Option V, (ρ.splitGraph a b).Reachable p (some a.snd) := by
    rintro (_ | u)
    · exact splitGraph_adj_none.reachable.trans (hreach _ _ b.adj.ne.symm hv₀)
    · by_cases hu : u = b.fst
      · rw [hu]
        exact (splitGraph_adj_some_fst hab hfst).reachable
      · exact hreach _ _ hu hv₀
  exact (connected_iff _).mpr ⟨fun p q => (hall p).trans (hall q).symm, ⟨none⟩⟩

/-- **The split graph has no isolated vertex** when `G` has none. -/
theorem isolatedVerts_splitGraph [Finite V] (hab : a ≠ b) (hfst : a.fst = b.fst)
    (hdeg : ∀ v, ∃ w, G.Adj v w) : isolatedVerts (ρ.splitGraph a b) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p hp => ?_
  rcases p with _ | u
  · exact hp _ splitGraph_adj_none
  · by_cases hu : u = b.fst
    · rw [hu] at hp
      exact hp _ (splitGraph_adj_some_fst hab hfst)
    · obtain ⟨w, hw⟩ := hdeg u
      exact hp _ ⟨⟨(u, w), hw⟩, splitTail_of_fst_ne hu, rfl⟩

/-- **The split graph has the edges of `G`.** -/
theorem ncard_edgeSet_splitGraph [Finite V] :
    (ρ.splitGraph a b).edgeSet.ncard = G.edgeSet.ncard :=
  ncard_edgeSet_dartGraph _ _ (splitTail_inj ρ a b)

/-- **Splitting a face**: when `a ≠ b` lie on one face, the split rotation system has one face
more. -/
theorem natCard_face_splitRotation [Finite V] (hab : a ≠ b) (hfst : a.fst = b.fst)
    (hface : ρ.face.SameCycle a b) :
    Nat.card (ρ.splitRotation a b hfst).Face = Nat.card ρ.Face + 1 := by
  have := finite_dart (G := G)
  refine (natCard_face_ofDartGraph (ρ.splitTail a b) (splitTail_ne_symm ρ a b)
    (splitTail_inj ρ a b) (swap a b * ρ.rot) (splitTail_swap_mul_rot hfst)
    fun _ _ => sameCycle_of_splitTail_eq hfst).trans ?_
  rw [mul_assoc]
  exact cycleCount_swap_mul_of_sameCycle hab hface

/-- **Splitting a vertex at two darts of one face lowers the Euler defect by two**, in a
`2`-connected graph: the split graph is connected, with one vertex and one face more, the same
edges, and no isolated vertex. -/
theorem eulerDefect_splitRotation [Finite V] (hab : a ≠ b) (hfst : a.fst = b.fst)
    (hface : ρ.face.SameCycle a b) (hG : IsKConnected G 2) :
    (ρ.splitRotation a b hfst).eulerDefect = ρ.eulerDefect - 2 := by
  have hdeg : ∀ v, ∃ w, G.Adj v w := fun v => by
    have := hG.le_ncard_neighborSet v
    obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (s := G.neighborSet v) (by omega)
    exact ⟨w, hw⟩
  have hC := natCard_connectedComponent_eq_one (hG.connected (by norm_num))
  have hC' := natCard_connectedComponent_eq_one (ρ.splitGraph_connected hab hfst hG)
  have hI : isolatedVerts G = ∅ := Set.eq_empty_of_forall_notMem fun v hv =>
    let ⟨w, hw⟩ := hdeg v
    hv w hw
  have hI' := ρ.isolatedVerts_splitGraph hab hfst hdeg
  have hF := ρ.natCard_face_splitRotation hab hfst hface
  have hE := ρ.ncard_edgeSet_splitGraph (a := a) (b := b)
  have hV : Nat.card (Option V) = Nat.card V + 1 := Finite.card_option
  unfold eulerDefect completedFaceCount
  rw [hC, hC', hI, hI', hF, hE, hV, Set.ncard_empty, Set.ncard_empty]
  push_cast
  ring

end RotationSystem

end Split

end MonoidProduct.Graph
