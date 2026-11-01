import MonoidProduct.Graph.Planar
set_option linter.style.header false

/-!
# Embeddings in surfaces

`monoid.tex`, section `sec:graph-certificates`, paragraph "Planarity and minor-closed
properties", which lists embeddability in a fixed surface among the proper minor-closed classes.

Embeddings of graphs in arbitrary surfaces, orientable or not, are described by embedding
schemes (Mohar and Thomassen, *Graphs on Surfaces*, Section 3.3): a rotation system together with
a twist on every edge.  Every cellular embedding of a connected graph arises from a scheme, and
the scheme determines the surface through Euler's formula `V − E + F = 2 − eg`, where `eg` is the
Euler genus: `2g` for the orientable surface of genus `g`, and `k` for the nonorientable surface
with `k` crosscaps.  A graph embeds in a surface of Euler genus at most `k` exactly when it has a
scheme whose components have Euler genera summing to at most `k`; this equivalence is cited, not
formalized.

* `EmbeddingScheme G`: a rotation system with a twist `twist d = twist d.symm` on every edge.
* `EmbeddingScheme.trace`: face tracing on darts with a local orientation, `G.Dart × Bool`.  From
  `(d, ε)` it crosses `d`, flipping `ε` on a twisted edge, and leaves the head of `d` along the
  next dart after `d.symm` around it, in the current orientation.  Each face is traced twice, once
  in each direction, so the `F` faces of a component give `2F` orbits of `trace` there.
* `EmbeddingScheme.twiceEulerGenus c`: `2·eg = 4 + 2E − 2V − (number of orbits)` for a component
  `c` with an edge, and `0` for an isolated vertex.
* `EulerGenusLE k G`: some scheme has total Euler genus at most `k`.  `GenusLE g G`: the same
  with no twisted edge and total Euler genus at most `2g`, that is orientable genus at most `g`.
* Orbits of `trace` have at least three elements in a component with at least three vertices
  (`three_le_ncard_sameCycle_trace`).  Euler's formula then gives `2E_c + 12 ≤ 6V_c + 3·(2 eg_c)`
  per component, and summing (`mul_ncard_edgeSet_add_le_add`):
  `EulerGenusLE.ncard_edgeSet_le`: `|E| ≤ 3v − 6 + 3k` for `v ≥ 3`, and
  `GenusLE.ncard_edgeSet_le`: `|E| ≤ 3v − 6 + 6g`.
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## Embedding schemes and face tracing -/

variable (G) in
/-- **An embedding scheme** of `G` (Mohar and Thomassen, *Graphs on Surfaces*, Section 3.3): a
rotation system with a twist on every edge. -/
structure EmbeddingScheme extends RotationSystem G where
  /-- Whether the edge of a dart is twisted. -/
  twist : G.Dart → Bool
  twist_symm : ∀ d, twist d.symm = twist d

namespace EmbeddingScheme

variable (σ : EmbeddingScheme G)

/-- **One step of face tracing**: cross `d`, flipping the orientation `ε` on a twisted edge,
then leave the head of `d` along the next dart after `d.symm` around it, in the new
orientation. -/
def traceStep (p : G.Dart × Bool) : G.Dart × Bool :=
  (if xor p.2 (σ.twist p.1) then σ.rot.symm p.1.symm else σ.rot p.1.symm, xor p.2 (σ.twist p.1))

/-- The inverse step. -/
def traceStepInv (q : G.Dart × Bool) : G.Dart × Bool :=
  ((if q.2 then σ.rot q.1 else σ.rot.symm q.1).symm,
    xor q.2 (σ.twist (if q.2 then σ.rot q.1 else σ.rot.symm q.1).symm))

/-- **The face-tracing permutation** of darts with a local orientation. -/
def trace : Equiv.Perm (G.Dart × Bool) where
  toFun := σ.traceStep
  invFun := σ.traceStepInv
  left_inv p := by
    obtain ⟨d, ε⟩ := p
    cases h : xor ε (σ.twist d) <;>
      simp [traceStep, traceStepInv, h] <;> cases ε <;> cases ht : σ.twist d <;> simp_all
  right_inv q := by
    obtain ⟨e, ε⟩ := q
    cases ε <;> simp [traceStep, traceStepInv]

theorem fst_traceStep (p : G.Dart × Bool) : (σ.traceStep p).1.fst = p.1.snd := by
  unfold traceStep
  split_ifs
  · change (σ.rot.symm p.1.symm).fst = p.1.snd
    have := σ.fst_rot (σ.rot.symm p.1.symm)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  · exact σ.fst_rot p.1.symm

/-- A traced face stays in one component. -/
theorem connectedComponentMk_fst_trace (p : G.Dart × Bool) :
    G.connectedComponentMk (σ.trace p).1.fst = G.connectedComponentMk p.1.fst := by
  change G.connectedComponentMk (σ.traceStep p).1.fst = _
  rw [fst_traceStep]
  exact ConnectedComponent.eq.mpr p.1.adj.reachable.symm

/-- **The orbits of face tracing.** -/
abbrev Orbit : Type _ := Quotient (Equiv.Perm.SameCycle.setoid σ.trace)

/-- The component of an orbit. -/
def Orbit.component {σ : EmbeddingScheme G} : σ.Orbit → G.ConnectedComponent :=
  Quotient.lift (fun p : G.Dart × Bool => G.connectedComponentMk p.1.fst) fun _ _ h =>
    eq_of_sameCycle_of_forall (g := fun p : G.Dart × Bool => G.connectedComponentMk p.1.fst)
      σ.connectedComponentMk_fst_trace h

/-- The orbits in the component `c`. -/
def orbitsIn (c : G.ConnectedComponent) : Set σ.Orbit := {q | q.component = c}

open Classical in
/-- **Twice the Euler genus of a component**: `4 + 2E − 2V − (number of orbits)` for a component
with an edge, since its `F` faces give `2F` orbits; `0` for an isolated vertex. -/
noncomputable def twiceEulerGenus (c : G.ConnectedComponent) : ℕ :=
  if (componentEdges G c).Nonempty then
    (2 * (componentEdges G c).ncard + 4) - (2 * c.supp.ncard + (σ.orbitsIn c).ncard)
  else 0

end EmbeddingScheme

variable (G) in
/-- **Euler genus at most `k`**: an embedding scheme whose components have Euler genera summing
to at most `k`; equivalently, an embedding in a surface of Euler genus at most `k`. -/
def EulerGenusLE (k : ℕ) : Prop :=
  ∃ σ : EmbeddingScheme G, ∑ᶠ c, σ.twiceEulerGenus c ≤ 2 * k

variable (G) in
/-- **Orientable genus at most `g`**: an embedding scheme without twisted edges, whose components
have genera summing to at most `g`, that is Euler genera (twice the genera) summing to at most
`2g`; equivalently, an embedding in the orientable surface of genus `g`.  The sum is of twice
the Euler genera, hence the bound `4g`. -/
def GenusLE (g : ℕ) : Prop :=
  ∃ σ : EmbeddingScheme G, (∀ d, σ.twist d = false) ∧ ∑ᶠ c, σ.twiceEulerGenus c ≤ 4 * g

/-- Orientable genus at most `g` is Euler genus at most `2g`. -/
theorem GenusLE.eulerGenusLE {g : ℕ} (h : GenusLE G g) : EulerGenusLE G (2 * g) := by
  obtain ⟨σ, -, hσ⟩ := h
  exact ⟨σ, hσ.trans (by omega)⟩

/-! ## Orbit lengths -/

/-- A vertex whose rotation fixes a dart has only that dart: its unique neighbour. -/
private theorem eq_snd_of_rot_eq (ρ : RotationSystem G) {d : G.Dart} (h : ρ.rot d = d) {y : V}
    (hy : G.Adj d.fst y) : y = d.snd := by
  have := (ρ.sameCycle_rot d ⟨(d.fst, y), hy⟩ rfl).eq_of_left h
  exact (congrArg (fun d : G.Dart => d.snd) this).symm

/-- **A dart fixed by the rotation at both ends** is an isolated edge: its component has at most
two vertices. -/
theorem ncard_supp_le_two_of_rot_eq [Finite V] (ρ : RotationSystem G) {d : G.Dart}
    (h₁ : ρ.rot d = d) (h₂ : ρ.rot d.symm = d.symm) :
    (G.connectedComponentMk d.fst).supp.ncard ≤ 2 := by
  have hnu : ∀ y, G.Adj d.fst y → y = d.snd := fun y hy => eq_snd_of_rot_eq ρ h₁ hy
  have hnw : ∀ y, G.Adj d.snd y → y = d.fst := fun y hy => eq_snd_of_rot_eq ρ h₂ hy
  have hreach : ∀ z, G.Reachable d.fst z → z ∈ ({d.fst, d.snd} : Set V) := by
    intro z hz
    rw [reachable_iff_reflTransGen] at hz
    induction hz with
    | refl => exact Set.mem_insert _ _
    | tail _ hab ih =>
        rcases Set.mem_insert_iff.mp ih with hb | hb
        · rw [hb] at hab
          exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (hnu _ hab))
        · rw [Set.mem_singleton_iff.mp hb] at hab
          exact Set.mem_insert_iff.mpr (Or.inl (hnw _ hab))
  have hsub : (G.connectedComponentMk d.fst).supp ⊆ {d.fst, d.snd} := fun z hz =>
    hreach z (ConnectedComponent.eq.mp ((ConnectedComponent.mem_supp_iff _ z).mp hz).symm)
  have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_insert_le d.fst {d.snd})
  rwa [Set.ncard_singleton] at this

namespace EmbeddingScheme

variable (σ : EmbeddingScheme G)

theorem trace_apply (p : G.Dart × Bool) : σ.trace p = σ.traceStep p := rfl

/-- Tracing moves to another dart: there are no loops. -/
theorem trace_ne (p : G.Dart × Bool) : σ.trace p ≠ p := fun h =>
  p.1.fst_ne_snd (((σ.fst_traceStep p).symm.trans
    (congrArg (fun q : G.Dart × Bool => q.1.fst) h))).symm

/-- **Tracing returns after two steps only around an isolated edge.** -/
theorem trace_trace_ne [Finite V] (p : G.Dart × Bool)
    (hc : 3 ≤ (G.connectedComponentMk p.1.fst).supp.ncard) : σ.trace (σ.trace p) ≠ p := by
  intro h
  obtain ⟨d, ε⟩ := p
  set q := σ.trace (d, ε) with hq
  -- The second dart is the reversal of the first.
  have hq1 : q.1 = d.symm := by
    have hfst : q.1.fst = d.snd := σ.fst_traceStep (d, ε)
    have hsnd : q.1.snd = d.fst := by
      have := congrArg (fun r : G.Dart × Bool => r.1.fst) h
      simp only [trace_apply, fst_traceStep] at this
      exact this
    exact Dart.ext _ _ (Prod.ext hfst hsnd)
  -- Both darts are fixed by the rotation.
  have hfix : ∀ (b : Bool) (e : G.Dart), (if b then σ.rot.symm e else σ.rot e) = e →
      σ.rot e = e := by
    intro b e he
    cases b
    · simpa using he
    · simp only [ite_true] at he
      have := congrArg σ.rot he
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
  have h1 : σ.rot d.symm = d.symm := by
    have he : q.1 = if xor ε (σ.twist d) then σ.rot.symm d.symm else σ.rot d.symm := rfl
    rw [hq1] at he
    exact hfix _ _ he.symm
  have h2 : σ.rot d = d := by
    have hf : (σ.trace q).1 =
        if xor q.2 (σ.twist q.1) then σ.rot.symm q.1.symm else σ.rot q.1.symm := rfl
    rw [h, hq1, Dart.symm_symm] at hf
    exact hfix _ _ hf.symm
  have hc' : 3 ≤ (G.connectedComponentMk d.fst).supp.ncard := hc
  have := ncard_supp_le_two_of_rot_eq σ.toRotationSystem h2 h1
  omega

/-- **Orbits of face tracing have at least three states** in a component with at least three
vertices. -/
theorem three_le_ncard_sameCycle_trace [Finite V] (p : G.Dart × Bool)
    (hc : 3 ≤ (G.connectedComponentMk p.1.fst).supp.ncard) :
    3 ≤ {q | σ.trace.SameCycle p q}.ncard := by
  classical
  have := Fintype.ofFinite V
  have h1 := σ.trace_ne p
  have h2 := σ.trace_trace_ne p hc
  have h3 := σ.trace_ne (σ.trace p)
  have hsub : (↑({p, σ.trace p, σ.trace (σ.trace p)} : Finset (G.Dart × Bool)) :
      Set (G.Dart × Bool)) ⊆ {q | σ.trace.SameCycle p q} := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.rfl
    · exact Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl
    · exact Equiv.Perm.sameCycle_apply_right.mpr
        (Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl)
  have hcard : ({p, σ.trace p, σ.trace (σ.trace p)} : Finset (G.Dart × Bool)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm h1, Ne.symm h2]),
      Finset.card_pair (Ne.symm h3)]
  rw [← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- The states in a component: its darts, with either orientation. -/
def statesIn (c : G.ConnectedComponent) : Set (G.Dart × Bool) :=
  {p | G.connectedComponentMk p.1.fst = c}

/-- A component has twice as many states as darts, so four times as many as edges. -/
theorem ncard_statesIn [Finite V] (c : G.ConnectedComponent) :
    (statesIn (G := G) c).ncard = 4 * (componentEdges G c).ncard := by
  have : statesIn (G := G) c = dartsIn G c ×ˢ Set.univ := by
    ext p
    simp [statesIn, dartsIn]
  rw [this, Set.ncard_prod, ncard_dartsIn_eq, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_bool]
  ring

/-- **Counting orbits by their states**: if every orbit in `c` has at least `n` states, then
`n·|orbits in c| ≤ |states in c|`. -/
theorem mul_ncard_orbitsIn_le [Finite V] (c : G.ConnectedComponent) (n : ℕ)
    (h : ∀ p : G.Dart × Bool, G.connectedComponentMk p.1.fst = c →
      n ≤ {q | σ.trace.SameCycle p q}.ncard) :
    n * (σ.orbitsIn c).ncard ≤ (statesIn (G := G) c).ncard := by
  classical
  have := Fintype.ofFinite V
  have : Fintype σ.Orbit := Fintype.ofFinite _
  set D := Finset.univ.filter fun p : G.Dart × Bool => G.connectedComponentMk p.1.fst = c
    with hDdef
  set Fc := Finset.univ.filter fun f : σ.Orbit => f.component = c with hFcdef
  have hD : statesIn (G := G) c = ↑D := by ext; simp [D, statesIn]
  have hF : σ.orbitsIn c = ↑Fc := by ext; simp [Fc, orbitsIn]
  rw [hD, hF, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := fun p : G.Dart × Bool => (⟦p⟧ : σ.Orbit)) (s := D)
      (t := Fc) fun p hp => Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hp).2⟩)]
  rw [mul_comm, ← smul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun q hq => ?_
  induction q using Quotient.inductionOn with
  | h p₀ =>
  have hp₀ : G.connectedComponentMk p₀.1.fst = c := (Finset.mem_filter.mp hq).2
  have hfib : {q | σ.trace.SameCycle p₀ q} = ↑(D.filter fun p => (⟦p⟧ : σ.Orbit) = ⟦p₀⟧) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, D, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hs
      refine ⟨?_, Quotient.sound hs.symm⟩
      rw [← hp₀]
      exact (eq_of_sameCycle_of_forall
        (g := fun p : G.Dart × Bool => G.connectedComponentMk p.1.fst)
        σ.connectedComponentMk_fst_trace hs).symm
    · rintro ⟨-, hq'⟩
      exact (Quotient.exact hq').symm
  rw [← Set.ncard_coe_finset, ← hfib]
  exact h p₀ hp₀

end EmbeddingScheme

/-! ## The edge bounds -/

/-- **Summing over the components, with a correction**: per-component bounds
`a·E_c + b ≤ b·V_c + x_c`, improved to `a·E_c + 2b ≤ b·V_c + x_c` on components with at least
three vertices, give `a·E + 2b ≤ b·V + Σ x_c` for `V ≥ 3`. -/
theorem mul_ncard_edgeSet_add_le_add [Fintype V] {a b : ℕ} (x : G.ConnectedComponent → ℕ)
    (hsmall : ∀ c : G.ConnectedComponent,
      a * (componentEdges G c).ncard + b ≤ b * c.supp.ncard + x c)
    (hbig : ∀ c : G.ConnectedComponent, 3 ≤ c.supp.ncard →
      a * (componentEdges G c).ncard + 2 * b ≤ b * c.supp.ncard + x c)
    (hv : 3 ≤ Fintype.card V) : a * G.edgeSet.ncard + 2 * b ≤ b * Fintype.card V + ∑ᶠ c, x c := by
  classical
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
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
  · obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hall : ∀ c, c = G.connectedComponentMk v₀ := fun c =>
      Fintype.card_le_one_iff.mp hone c _
    have hsum : ∀ f : G.ConnectedComponent → ℕ, ∑ c, f c = f (G.connectedComponentMk v₀) :=
      fun f => Fintype.sum_eq_single _ fun c hc => absurd (hall c) hc
    rw [hsum] at hV hE
    rw [hsum]
    have := hbig _ (by rw [hV]; exact hv)
    rwa [hV, hE] at this
  · have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hsmall c
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hE,
      hV, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
    have h2 : 2 * b ≤ Fintype.card G.ConnectedComponent * b :=
      Nat.mul_le_mul_right b (by omega)
    omega

/-- **Euler's formula with traced faces**, in a component with at least three vertices:
`2E + 12 ≤ 6V + 3·(2 eg)`. -/
theorem EmbeddingScheme.edges_le [Finite V] (σ : EmbeddingScheme G) {c : G.ConnectedComponent}
    (hc : 3 ≤ c.supp.ncard) :
    2 * (componentEdges G c).ncard + 12 ≤ 6 * c.supp.ncard + 3 * σ.twiceEulerGenus c := by
  classical
  have hne := componentEdges_nonempty (G := G) (c := c) (by omega)
  have horb := σ.mul_ncard_orbitsIn_le c 3 fun p hp =>
    σ.three_le_ncard_sameCycle_trace p (by rw [hp]; exact hc)
  rw [EmbeddingScheme.ncard_statesIn] at horb
  have heg : σ.twiceEulerGenus c =
      (2 * (componentEdges G c).ncard + 4) - (2 * c.supp.ncard + (σ.orbitsIn c).ncard) := by
    unfold EmbeddingScheme.twiceEulerGenus
    rw [ite_eq_left hne]
  rw [heg]
  omega

/-- The total Euler-genus correction over all components. -/
private theorem sum_le_of_eulerGenus [Finite V] (σ : EmbeddingScheme G) :
    ∀ c : G.ConnectedComponent,
      2 * (componentEdges G c).ncard + 6 ≤ 6 * c.supp.ncard + 3 * σ.twiceEulerGenus c := by
  intro c
  by_cases hc : 3 ≤ c.supp.ncard
  · have := σ.edges_le hc
    omega
  · have := ncard_componentEdges_lt_of_le_two (G := G) (c := c) (by omega)
    have := one_le_ncard_supp c
    omega

/-- **`|E| ≤ 3v − 6 + 3k` for Euler genus at most `k`** (`sec:graph-certificates`), for
`v ≥ 3`. -/
theorem EulerGenusLE.ncard_edgeSet_le [Fintype V] {k : ℕ} (h : EulerGenusLE G k)
    (hv : 3 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 + 3 * k := by
  classical
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨σ, hσ⟩ := h
  have := mul_ncard_edgeSet_add_le_add (G := G) (a := 2) (b := 6)
    (fun c => 3 * σ.twiceEulerGenus c) (sum_le_of_eulerGenus σ) (fun c hc => σ.edges_le hc) hv
  rw [finsum_eq_sum_of_fintype, ← Finset.mul_sum, ← finsum_eq_sum_of_fintype] at this
  omega

/-! ## Planar graphs have genus `0` -/

/-- **Cycles under a semiconjugacy**: if `F ∘ g = g ∘ H` and `g` is injective, then `g` maps the
cycles of `H` onto the cycles of `F` through its image. -/
theorem sameCycle_iff_of_semiconj {α β : Type*} {F : Equiv.Perm β} {H : Equiv.Perm α}
    {g : α → β} (hg : ∀ x, F (g x) = g (H x)) (hinj : Function.Injective g) {x y : α} :
    F.SameCycle (g x) (g y) ↔ H.SameCycle x y := by
  have hinv : ∀ x, F⁻¹ (g x) = g (H⁻¹ x) := fun x => by
    rw [Equiv.Perm.inv_def, Equiv.Perm.inv_def, Equiv.symm_apply_eq, hg, Equiv.apply_symm_apply]
  have hpow : ∀ (i : ℤ) (x : α), (F ^ i) (g x) = g ((H ^ i) x) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg, ih]
    | pred n ih =>
      intro x
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, ih]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hinj (by rw [← hpow, hi])⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hpow, hi]⟩

/-- **The scheme of a rotation system**, without twisted edges. -/
def RotationSystem.toScheme (ρ : RotationSystem G) : EmbeddingScheme G :=
  { toRotationSystem := ρ, twist := fun _ => false, twist_symm := fun _ => rfl }

namespace RotationSystem

variable (ρ : RotationSystem G)

theorem trace_toScheme_false (d : G.Dart) : ρ.toScheme.trace (d, false) = (ρ.face d, false) :=
  rfl

theorem trace_toScheme_true (d : G.Dart) :
    ρ.toScheme.trace (d.symm, true) = ((ρ.face⁻¹ d).symm, true) := by
  have : ρ.face⁻¹ d = (ρ.rot⁻¹ d).symm := by
    rw [Equiv.Perm.inv_eq_iff_eq, face_apply, Dart.symm_symm, Equiv.Perm.inv_def,
      Equiv.apply_symm_apply]
  rw [this, Dart.symm_symm]
  rfl

/-- Without twists, tracing keeps the orientation. -/
theorem snd_trace_toScheme (p : G.Dart × Bool) : (ρ.toScheme.trace p).2 = p.2 := by
  change xor p.2 false = p.2
  simp

/-- **Each face is traced twice**, once in each direction: a rotation system without twists has
at least twice as many orbits of face tracing as faces, in every component. -/
theorem two_mul_ncard_facesIn_le [Finite V] (c : G.ConnectedComponent) :
    2 * (ρ.facesIn c).ncard ≤ (ρ.toScheme.orbitsIn c).ncard := by
  classical
  have := Fintype.ofFinite V
  have hfwd : ∀ x : G.Dart, ρ.toScheme.trace ((fun d : G.Dart => (d, false)) x) =
      (fun d : G.Dart => (d, false)) (ρ.face x) := ρ.trace_toScheme_false
  have hbwd : ∀ x : G.Dart, ρ.toScheme.trace ((fun d : G.Dart => (d.symm, true)) x) =
      (fun d : G.Dart => (d.symm, true)) (ρ.face⁻¹ x) := ρ.trace_toScheme_true
  have hinjf : Function.Injective fun d : G.Dart => (d, false) := fun _ _ h =>
    congrArg Prod.fst h
  have hinjb : Function.Injective fun d : G.Dart => (d.symm, true) := fun _ _ h => by
    have := congrArg (fun p : G.Dart × Bool => p.1.symm) h
    simpa using this
  let α : ρ.Face → ρ.toScheme.Orbit := Quotient.map (fun d => (d, false)) fun _ _ h =>
    (sameCycle_iff_of_semiconj hfwd hinjf).mpr h
  let β : ρ.Face → ρ.toScheme.Orbit := Quotient.map (fun d => (d.symm, true)) fun _ _ h =>
    (sameCycle_iff_of_semiconj hbwd hinjb).mpr (Equiv.Perm.sameCycle_inv.mpr h)
  have hα : Function.Injective α := by
    intro f f' h
    induction f using Quotient.inductionOn
    induction f' using Quotient.inductionOn
    exact Quotient.sound ((sameCycle_iff_of_semiconj hfwd hinjf).mp (Quotient.exact h))
  have hβ : Function.Injective β := by
    intro f f' h
    induction f using Quotient.inductionOn
    induction f' using Quotient.inductionOn
    exact Quotient.sound (Equiv.Perm.sameCycle_inv.mp
      ((sameCycle_iff_of_semiconj hbwd hinjb).mp (Quotient.exact h)))
  have hdisj : Disjoint (α '' ρ.facesIn c) (β '' ρ.facesIn c) := by
    rw [Set.disjoint_left]
    rintro _ ⟨f, -, rfl⟩ ⟨f', -, hf⟩
    induction f using Quotient.inductionOn with
    | h d =>
    induction f' using Quotient.inductionOn with
    | h d' =>
    have hs := Quotient.exact hf
    have := eq_of_sameCycle_of_forall (g := Prod.snd) ρ.snd_trace_toScheme hs
    exact absurd this.symm Bool.false_ne_true
  have hsub : α '' ρ.facesIn c ∪ β '' ρ.facesIn c ⊆ ρ.toScheme.orbitsIn c := by
    rintro _ (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩)
    · induction f using Quotient.inductionOn with
      | h d => exact hf
    · induction f using Quotient.inductionOn with
      | h d =>
      change G.connectedComponentMk d.symm.fst = c
      rw [← hf]
      exact ConnectedComponent.eq.mpr d.adj.reachable.symm
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj, hα.injOn.ncard_image, hβ.injOn.ncard_image] at this
  omega

end RotationSystem

/-- **Planar graphs have orientable genus `0`**: a spherical rotation system, without twists,
has total Euler genus `0`. -/
theorem IsPlanar.genusLE_zero [Finite V] (h : IsPlanar G) : GenusLE G 0 := by
  obtain ⟨ρ, hρ⟩ := h
  refine ⟨ρ.toScheme, fun _ => rfl, ?_⟩
  have hzero : ∀ c, ρ.toScheme.twiceEulerGenus c = 0 := by
    intro c
    unfold EmbeddingScheme.twiceEulerGenus
    split_ifs with hne
    · have h1 := hρ c hne
      have h2 := ρ.two_mul_ncard_facesIn_le c
      change (2 * (componentEdges G c).ncard + 4) -
        (2 * c.supp.ncard + (ρ.toScheme.orbitsIn c).ncard) = 0
      omega
    · rfl
  simp [hzero]

/-- **`|E| ≤ 3v − 6 + 6g` for orientable genus at most `g`**, for `v ≥ 3`. -/
theorem GenusLE.ncard_edgeSet_le [Fintype V] {g : ℕ} (h : GenusLE G g)
    (hv : 3 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 + 6 * g := by
  have := h.eulerGenusLE.ncard_edgeSet_le hv
  omega

end MonoidProduct.Graph
