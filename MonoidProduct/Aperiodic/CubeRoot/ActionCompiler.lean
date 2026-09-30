import MonoidProduct.Aperiodic.CubeRoot.AxisPacket
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The action compiler

Part of the regular-action simulation (Section `sec:ags-actions` of the
paper).  The compiler turns axis packets for the **regular owners** of an
action's components into the endpoint-and-first-death packet of the action
itself (`hasDual_actionPacket`).  It has to: the assembly of `ActionCost.lean` consumes the
per-cut *state test* of the action, and for the target-reachability action that
test is the ordinary target test at states `p` with `MtM ⊆ MpM` — which need
not be strict parents, so feeding that assembly directly would be circular.  Owners
are the way out, because their regular height is strictly smaller
(`regHeight_drop`).

This file lays the two foundations first.

**Windows.**  A packet run from position `p` is the packet of the sub-word,
and `HasDual.pullback` along `winEmb` says that costs the same.

**What the axis sees.**  Take the owner at the *current state* `y` rather than
at a component representative: `MinimalOwner A (some y) e` gives `y · e = y`,
so `e` is its own lift under `π_e` and no representative has to be chosen.
Then

* `act_eq_of_minimalOwner` — `y · (e · p) = y · p`, so the killed `R_e`-axis
  started at `e` **tracks the ambient trajectory from `y`**, and
* `rEq_iff_sameComp` — the axis dies exactly when the trajectory **leaves the
  component**.

The second is the distinction the statements must keep: leaving the component
is *not* dying.  A trajectory that leaves `R_e` may well still be alive, in
the next component; that is precisely the case the compiler's outer loop
handles, by reading the boundary letter.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Window

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M]

/-- **The axis packet on a window.**  Running a packet from position `p` for
`len` letters is running it on the sub-word, and freezing everything outside
an injective window is free. -/
theorem hasDual_axisPacket_win (letter : σ → M) (e : M) (r : RState e)
    {n p len : ℕ} (h : p + len ≤ n) {c : ℝ}
    (hpk : HasDual (axisPacket e letter r (n := len)) c) :
    HasDual (fun x : Fin n → σ =>
      axisPacket e letter r (fun t => x (winEmb p len h t))) c :=
  (hpk.pullback (winEmb_injective h)).ofEq fun _ => rfl

end Window

section Track

variable {σ M X : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M]
variable (A : RightAction M (Option X)) (letter : σ → M)

/-- **The owner at the current state is its own lift.**  With the base point
taken at `y` itself, `y · e = y`, so prefixing the owner changes nothing and
the killed `R_e`-axis started at `e` tracks the ambient trajectory from `y`. -/
theorem act_eq_of_minimalOwner {y : X} {e : M}
    (hown : MinimalOwner A (some y) e) (p : M) :
    A.act (some y) (e * p) = A.act (some y) p := by
  rw [ownerCover_map, hown.ret]

/-- **Leaving the axis is leaving the component** — not dying.  This is
`ownerCover_intertwine` at the base point `y`, with the owner's own return
identity absorbed. -/
theorem rEq_iff_sameComp {y : X} {e : M} (hown : MinimalOwner A (some y) e)
    (p : M) : REq (e * p) e ↔ A.SameComp (some y) (A.act (some y) p) := by
  have h := ownerCover_intertwine hown (rEq_refl e) p
  rwa [act_eq_of_minimalOwner A hown p] at h

variable {A}

/-- **The axis state, spelled out.**  Along the axis started at the owner, the
state after `j` letters is `e · φ(x₀⋯x_{j-1})`, live exactly while the ambient
trajectory stays in the component. -/
theorem cutState_ownerAxis {e : M} {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    cutState (killedAction e) (⟨e, rEq_refl e⟩ : RState e) letter x j
      = if h : REq (e * winProd letter x 0 j) e then
          some ⟨e * winProd letter x 0 j, h⟩ else none := rfl

/-- **The liveness correspondence.**  The axis is live at cut `j` exactly when
the ambient trajectory is still in the component of `y` at cut `j`. -/
theorem cutState_ownerAxis_isSome_iff {y : X} {e : M}
    (hown : MinimalOwner A (some y) e) {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    (cutState (killedAction e) (⟨e, rEq_refl e⟩ : RState e) letter x j).isSome
      ↔ A.SameComp (some y) (cutState A y letter x j) := by
  rw [cutState_ownerAxis letter x j]
  by_cases h : REq (e * winProd letter x 0 j) e
  · rw [dif_pos h]
    exact ⟨fun _ => (rEq_iff_sameComp A hown _).1 h, fun _ => rfl⟩
  · rw [dif_neg h]
    exact ⟨fun hc => absurd hc (by simp), fun hc => absurd ((rEq_iff_sameComp A hown _).2 hc) h⟩

/-- **The state correspondence.**  While the axis is live, the ambient state is
the axis state acted on `y`. -/
theorem act_cutState_ownerAxis {y : X} {e : M} (hown : MinimalOwner A (some y) e)
    {n : ℕ} (x : Fin n → σ) (j : ℕ) {r : RState e}
    (hr : cutState (killedAction e) (⟨e, rEq_refl e⟩ : RState e) letter x j = some r) :
    A.act (some y) r.val = cutState A y letter x j := by
  rw [cutState_ownerAxis letter x j] at hr
  by_cases h : REq (e * winProd letter x 0 j) e
  · rw [dif_pos h] at hr
    have hval : r.val = e * winProd letter x 0 j :=
      congrArg Subtype.val (Option.some_injective _ hr).symm
    rw [hval, act_eq_of_minimalOwner A hown]
    rfl
  · rw [dif_neg h] at hr
    exact absurd hr (by simp)

end Track

/-! ## Why finitely many components suffice

A trajectory visits each strongly connected component at most once, so the
compiler's outer loop needs at most `|M|` levels — a reachable orbit is the
image of the monoid, so the ambient state count never enters.  The manuscript states that
by contracting the components; here the same fact comes from a **measure**,
which is cheaper: when the trajectory leaves a component it moves to a state
`w` reachable from `z` but from which `z` is *not* reachable, and then the
reachable set strictly shrinks.  No quotient is constructed. -/

section Reach

variable {M X : Type} [Monoid M] [Fintype M] [Fintype X] [DecidableEq X]
variable (A : RightAction M X)

/-- Reachability is decidable: it is an existential over a finite monoid. -/
instance instDecidableReaches (z w : X) : Decidable (A.Reaches z w) :=
  inferInstanceAs (Decidable (∃ a : M, A.act z a = w))

/-- The states reachable from `z`. -/
def reachSet (z : X) : Finset X :=
  Finset.univ.filter fun w => A.Reaches z w

lemma mem_reachSet {z w : X} : w ∈ reachSet A z ↔ A.Reaches z w := by
  simp [reachSet]

lemma self_mem_reachSet (z : X) : z ∈ reachSet A z :=
  (mem_reachSet A).2 (A.reaches_refl z)

lemma reachSet_subset {z w : X} (h : A.Reaches z w) : reachSet A w ⊆ reachSet A z :=
  fun _ hu => (mem_reachSet A).2 (h.trans A ((mem_reachSet A).1 hu))

/-- **The measure.**  Moving to a state one cannot come back from strictly
shrinks the reachable set — which is what bounds the number of components a
trajectory meets. -/
theorem reachSet_ssubset {z w : X} (h : A.Reaches z w) (h' : ¬ A.Reaches w z) :
    reachSet A w ⊂ reachSet A z :=
  ⟨reachSet_subset A h, fun hc =>
    h' ((mem_reachSet A).1 (hc (self_mem_reachSet A z)))⟩

theorem card_reachSet_lt {z w : X} (h : A.Reaches z w) (h' : ¬ A.Reaches w z) :
    (reachSet A w).card < (reachSet A z).card :=
  Finset.card_lt_card (reachSet_ssubset A h h')

/-- A component change is exactly a move that is not `SameComp`. -/
theorem card_reachSet_lt_of_not_sameComp {z w : X} (h : A.Reaches z w)
    (h' : ¬ A.SameComp z w) : (reachSet A w).card < (reachSet A z).card :=
  card_reachSet_lt A h fun hc => h' ⟨h, hc⟩

lemma card_reachSet_le (z : X) : (reachSet A z).card ≤ Fintype.card X :=
  (reachSet A z).card_le_univ.trans_eq Finset.card_univ

/-- The reachable set is the **orbit** of `z` — the image of the monoid acting
on it. -/
lemma reachSet_eq_image (z : X) : reachSet A z = Finset.univ.image (A.act z) := by
  ext w
  simp [mem_reachSet, RightAction.Reaches]

/-- **A reachable orbit is no bigger than the acting monoid.**  This is the
bound the manuscript's action compiler runs on — `|M|`, not the ambient number
of states — and it is what keeps the compiler's cost independent of how large a
set the action happens to be defined on.

`M` here is the **acting** monoid.  The action need not be faithful, so its
transition monoid may be a proper quotient of `M`; `|M|` upper-bounds the
manuscript's `q`, which is what the compiler needs. -/
lemma card_reachSet_le_card_monoid (z : X) :
    (reachSet A z).card ≤ Fintype.card M := by
  rw [reachSet_eq_image]
  exact le_trans Finset.card_image_le (le_of_eq Finset.card_univ)

end Reach

/-! ## One level of the compiler

A level runs the axis packet of the current component on the window from the
current entry position, and then reads the **boundary letter** at the exit cut
— the one letter that carries the trajectory into the next component.  The
read is an *adaptive* call: its position is the packet's own output, so only
the branch actually taken is paid for and the letter costs `2`, not `2(len+1)`.
-/

section Level

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M]

/-- The letter at an absolute cut, and `none` past the end of the word. -/
def boundaryLetter {n : ℕ} (x : Fin n → σ) (q : ℕ) : Option σ :=
  if h : q < n then some (x ⟨q, h⟩) else none

/-- Reading one letter costs `2`; past the end it is constant and costs
nothing. -/
theorem hasDual_boundaryLetter {n : ℕ} (q : ℕ) :
    HasDual (fun x : Fin n → σ => boundaryLetter x q) 2 := by
  by_cases h : q < n
  · refine (hasDual_ofCoord (⟨q, h⟩ : Fin n) fun c => (some c : Option σ)).ofEq
      fun x => ?_
    rw [boundaryLetter, dif_pos h]
  · refine (hasDual_const (f := fun x : Fin n → σ => boundaryLetter x q)
      fun x y => ?_).mono (by norm_num)
    rw [boundaryLetter, boundaryLetter, dif_neg h, dif_neg h]

/-- **One level.**  From a known entry position `p` and a known axis, the exit
cut with its exact state, together with the boundary letter there. -/
theorem hasDual_levelStep (letter : σ → M) (e : M) (r : RState e)
    {n p len : ℕ} (h : p + len ≤ n) {c : ℝ}
    (hpk : HasDual (axisPacket e letter r (n := len)) c) :
    HasDual (fun x : Fin n → σ =>
        (axisPacket e letter r (fun t => x (winEmb p len h t)),
          boundaryLetter x
            (p + (axisPacket e letter r (fun t => x (winEmb p len h t))).1)))
      (c + 2) :=
  HasDual.adaptiveCall (hasDual_axisPacket_win letter e r h hpk)
    fun d => hasDual_boundaryLetter (p + (d.1 : ℕ))

end Level

/-! ## The uniform level record

Different levels run the axes of different owners, so their raw outputs live
in different types.  The compiler's transcript needs one type, and this is it:
the **absolute** exit cut, the exit state as a plain element of `M`, and the
boundary letter there.  Both coordinate changes — shifting the window's cut to
an absolute position, and forgetting that the state lies on the axis — are
**injective**, so `HasDual.ofKer` makes the recoding free.  It is the one
change of output type in this file that is not paid for. -/

/-- What one level reports. -/
abbrev LevelRec (M σ : Type) (n : ℕ) : Type := Fin (n + 1) × Option M × Option σ

section Record

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M]

/-- The recoding of a level's raw output into the uniform record. -/
def levelRec {e : M} {len n : ℕ} (p : ℕ) (hp : p + len ≤ n)
    (z : (Fin (len + 1) × Option (RState e)) × Option σ) : LevelRec M σ n :=
  (⟨p + (z.1.1 : ℕ), by have := z.1.1.isLt; omega⟩, z.1.2.map Subtype.val, z.2)

lemma levelRec_injective {e : M} {len n : ℕ} (p : ℕ) (hp : p + len ≤ n) :
    Function.Injective (levelRec (M := M) (σ := σ) (e := e) (len := len) p hp) := by
  rintro ⟨⟨k, r⟩, b⟩ ⟨⟨k', r'⟩, b'⟩ hz
  simp only [levelRec, Prod.mk.injEq, Fin.mk.injEq] at hz
  obtain ⟨hk, hr, hb⟩ := hz
  have hk' : k = k' := Fin.ext (by omega)
  have hr' : r = r' := Option.map_injective Subtype.val_injective hr
  subst hk'
  subst hr'
  subst hb
  rfl

/-- **One level, in the uniform record.**  The recoding is injective, so the
cost is the level's own. -/
theorem hasDual_levelRec (letter : σ → M) (e : M) (r : RState e)
    {n p len : ℕ} (h : p + len ≤ n) {c : ℝ}
    (hpk : HasDual (axisPacket e letter r (n := len)) c) :
    HasDual (fun x : Fin n → σ =>
        levelRec p h
          (axisPacket e letter r (fun t => x (winEmb p len h t)),
            boundaryLetter x
              (p + (axisPacket e letter r (fun t => x (winEmb p len h t))).1)))
      (c + 2) :=
  (hasDual_levelStep letter e r h hpk).ofKer fun x y =>
    ⟨fun hxy => by rw [hxy], fun hxy => levelRec_injective p h hxy⟩

end Record

/-! ## The configuration recursion

The compiler processes one component per level.  Its **configuration** is the
entry position and entry state of the component currently being processed, or
`none` once the run has finished — either because the trajectory survived to
the end of the word, or because it died.

The point of the recursion is that `confStep` is *defined* as `stepOfRec`
applied to the level record, so the next configuration depends on the word
**only through that record**.  Hence
`conf_eq_confOf` — the configuration after `j` levels is a function of the
first `j` records — which is what makes each level's dual a *total* dual
restricted to a fiber, and so mechanical. -/

/-- The compiler's configuration. -/
abbrev Conf (X : Type) : Type := Option (ℕ × X)

section Compile

variable {σ M X : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M] [Fintype X] [DecidableEq X]
variable (A : RightAction M (Option X)) (letter : σ → M) (owner : X → M)

/-- The window a level runs on, clamped so that no side condition survives:
the recursion only ever produces positions `≤ n`, and clamping the rest away
keeps every definition total. -/
lemma clamp_add (n p : ℕ) : min p n + (n - min p n) ≤ n := by omega

/-- The axis packet a level runs, from the entry position of a configuration. -/
noncomputable def confPacket {n : ℕ} (x : Fin n → σ) (p : ℕ) (y : X) :
    Fin (n - min p n + 1) × Option (RState (owner y)) :=
  axisPacket (owner y) letter ⟨owner y, rEq_refl _⟩
    fun t => x (winEmb (min p n) (n - min p n) (clamp_add n p) t)

/-- The level record a configuration produces.  On a finished run it is a
constant. -/
noncomputable def confLevel {n : ℕ} (x : Fin n → σ) : Conf X → LevelRec M σ n
  | none => (⟨0, Nat.zero_lt_succ n⟩, none, none)
  | some (p, y) =>
      levelRec (min p n) (clamp_add n p)
        (confPacket letter owner x p y,
          boundaryLetter x (min p n + ((confPacket letter owner x p y).1 : ℕ)))

/-- **The next configuration, read off the record.**  This is the whole point:
the step looks at the word only through the level record. -/
def stepOfRec {n : ℕ} (pc : ℕ × X) (L : LevelRec M σ n) : Conf X :=
  L.2.2.bind fun c =>
    (A.act (A.act (some pc.2) (L.2.1.getD 1)) (letter c)).map fun y' => ((L.1 : ℕ) + 1, y')

/-- One step of the configuration. -/
noncomputable def confStep {n : ℕ} (x : Fin n → σ) (pc : ℕ × X) : Conf X :=
  stepOfRec A letter pc (confLevel letter owner x (some pc))

/-- The configuration after `j` levels. -/
noncomputable def conf (v₀ : X) {n : ℕ} (x : Fin n → σ) : ℕ → Conf X
  | 0 => some (0, v₀)
  | j + 1 => (conf v₀ x j).bind (confStep A letter owner x)

@[simp] lemma conf_zero (v₀ : X) {n : ℕ} (x : Fin n → σ) :
    conf A letter owner v₀ x 0 = some (0, v₀) := rfl

lemma conf_succ (v₀ : X) {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    conf A letter owner v₀ x (j + 1)
      = (conf A letter owner v₀ x j).bind (confStep A letter owner x) := rfl

/-- The level record at level `j`. -/
noncomputable def levelAt (v₀ : X) {n : ℕ} (x : Fin n → σ) (j : ℕ) : LevelRec M σ n :=
  confLevel letter owner x (conf A letter owner v₀ x j)

/-- **The reconstruction**: the same recursion, run on a supplied sequence of
records instead of on the word. -/
def confOf (v₀ : X) {n : ℕ} (t : ℕ → LevelRec M σ n) : ℕ → Conf X
  | 0 => some (0, v₀)
  | j + 1 => (confOf v₀ t j).bind fun pc => stepOfRec A letter pc (t j)

/-- **Determinism.**  The configuration after `j` levels is a function of the
first `j` records — no further access to the word. -/
theorem conf_eq_confOf (v₀ : X) {n : ℕ} (x : Fin n → σ) (t : ℕ → LevelRec M σ n)
    (j : ℕ) (ht : ∀ i, i < j → levelAt A letter owner v₀ x i = t i) :
    conf A letter owner v₀ x j = confOf A letter v₀ t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hprev := ih fun i hi => ht i (by omega)
      rw [conf_succ, confOf, hprev]
      rcases hc : confOf A letter v₀ t j with _ | pc
      · rfl
      · have hlvl : confLevel letter owner x (some pc) = t j := by
          have := ht j (by omega)
          rwa [levelAt, hprev, hc] at this
        simp only [Option.bind_some, confStep, hlvl]

/-- The record at a level is likewise determined. -/
theorem levelAt_eq (v₀ : X) {n : ℕ} (x : Fin n → σ) (t : ℕ → LevelRec M σ n)
    (j : ℕ) (ht : ∀ i, i < j → levelAt A letter owner v₀ x i = t i) :
    levelAt A letter owner v₀ x j
      = confLevel letter owner x (confOf A letter v₀ t j) := by
  rw [levelAt, conf_eq_confOf A letter owner v₀ x t j ht]

end Compile

/-! ## The transcript

Each level is a *total* function of the word once its configuration is fixed —
and `conf_eq_confOf` says the configuration is fixed on the fiber where the
earlier records are.  So every level's dual is the total dual of
`hasDual_levelRec`, restricted to a fiber, and the transcript costs
`m(B√n + 2)` by `HasDual.adaptiveTranscript`. -/

/-- The record padding a transcript past the end of the run. -/
def padRec (M σ : Type) (n : ℕ) : LevelRec M σ n := (⟨0, Nat.zero_lt_succ n⟩, none, none)

section Transcript

variable {σ M X : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M] [Fintype X] [DecidableEq X]
variable (A : RightAction M (Option X)) (letter : σ → M) (owner : X → M)

/-- **The compiler's input**: an axis packet for the owner of every live state,
at every horizon, in the normal form of `AxisPacket.lean`. -/
def HasOwnerPackets (n₀ : ℕ) (B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ (y : X) (len : ℕ), len ≤ n₀ →
    HasDual (axisPacket (owner y) letter
      (⟨owner y, rEq_refl (owner y)⟩ : RState (owner y)) (n := len))
      (B * Real.sqrt (len : ℝ))

variable {letter owner}

/-- **One level, from a fixed configuration.**  A finished run costs nothing;
a live one costs its window's axis packet plus the boundary letter. -/
theorem hasDual_confLevel {n : ℕ} {B : ℝ}
    (hpk : HasOwnerPackets letter owner n B) (c₀ : Conf X) :
    HasDual (fun x : Fin n → σ => confLevel letter owner x c₀)
      (B * Real.sqrt (n : ℝ) + 2) := by
  have hB0 : (0 : ℝ) ≤ B * Real.sqrt (n : ℝ) + 2 := by
    have := Real.sqrt_nonneg (n : ℝ)
    have := hpk.1
    positivity
  rcases c₀ with _ | ⟨p, y⟩
  · exact (hasDual_const (f := fun x : Fin n → σ => confLevel letter owner x none)
      fun _ _ => rfl).mono hB0
  · refine (hasDual_levelRec letter (owner y) ⟨owner y, rEq_refl (owner y)⟩
      (clamp_add n p) (hpk.2 y (n - min p n) (by omega))).mono ?_
    have hs : Real.sqrt ((n - min p n : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      exact_mod_cast Nat.sub_le n (min p n)
    have := hpk.1
    nlinarith [Real.sqrt_nonneg ((n - min p n : ℕ) : ℝ)]

/-- **The transcript**, at `m` levels.  Every level is the same total dual on a
different fiber, so there is no factor in the number of components beyond the
level count itself. -/
theorem hasDual_transcript {n : ℕ} {B : ℝ} (hpk : HasOwnerPackets letter owner n B)
    (v₀ : X) (m : ℕ) :
    HasDual (fun (x : Fin n → σ) (j : Fin m) => levelAt A letter owner v₀ x (j : ℕ))
      ((m : ℝ) * (B * Real.sqrt (n : ℝ) + 2)) := by
  refine HasDual.adaptiveTranscript
    (Dfun := fun (j : Fin m) (x : Fin n → σ) => levelAt A letter owner v₀ x (j : ℕ))
    (padRec M σ n) ?_
  intro j t
  set t' : ℕ → LevelRec M σ n :=
    fun i => if h : i < m then t ⟨i, h⟩ else padRec M σ n with ht'def
  refine ((hasDual_confLevel hpk (confOf A letter v₀ t' (j : ℕ))).restrictToOn
    (fiberRead (id : (Fin n → σ) → Fin n → σ) _ t)).ofEq fun z => ?_
  refine (levelAt_eq A letter owner v₀ z.val t' (j : ℕ) ?_).symm
  intro i hi
  have him : i < m := lt_trans hi j.isLt
  have hz := congrFun z.2 ⟨i, him⟩
  rw [preTrans, if_pos hi] at hz
  rw [ht'def]
  simpa only [dif_pos him] using hz

end Transcript

/-! ## What a level means

The definitions above are deliberately syntactic — they had to be, for the
transcript's fiber bookkeeping.  Here they are given their meaning: the
configuration's entry pair really is a cut of the ambient run together with
the state there, and the level's exit state really is the ambient state at the
exit cut. -/

section Semantics

variable {σ M X : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M] [Fintype X] [DecidableEq X]
variable (A : RightAction M (Option X)) (letter : σ → M) (owner : X → M)

/-- **Cuts compose**: the run to `p + k` is the run to `p` continued by the
window's product. -/
lemma cutState_split (v₀ : X) {n : ℕ} (x : Fin n → σ) (p k : ℕ) :
    cutState A v₀ letter x (p + k)
      = A.act (cutState A v₀ letter x p) (winProd letter x p (p + k)) := by
  simp only [cutState]
  rw [A.act_mul]
  congr 1
  simp only [winProd]
  exact (rangeProd_split _ (Nat.zero_le p) (Nat.le_add_right p k)).symm

/-- The sub-word a level's axis reads. -/
def winWord {n : ℕ} (x : Fin n → σ) (p : ℕ) : Fin (n - min p n) → σ :=
  fun t => x (winEmb (min p n) (n - min p n) (clamp_add n p) t)

lemma confPacket_eq {n : ℕ} (x : Fin n → σ) (p : ℕ) (y : X) :
    confPacket letter owner x p y
      = axisPacket (owner y) letter ⟨owner y, rEq_refl (owner y)⟩ (winWord x p) := rfl

/-- Reading a prefix of the sub-word is reading a window of the word. -/
lemma winProd_winWord {n : ℕ} (x : Fin n → σ) {p : ℕ} (hp : p ≤ n) {k : ℕ}
    (hk : k ≤ n - p) :
    winProd letter (winWord x p) 0 k = winProd letter x p (p + k) := by
  have hmin : min p n = p := min_eq_left hp
  have h : winProd letter (winWord x p) 0 k
      = winProd letter x (min p n + 0) (min p n + k) :=
    winProd_winEmb letter x (clamp_add n p) (Nat.zero_le k) (by omega)
  rw [h, hmin, Nat.add_zero]

/-- **The window's run is the ambient run.**  Whatever the axis sees at cut `j`
of the sub-word, the action is in at cut `p + j` of the whole word. -/
theorem cutState_winWord (v₀ y : X) {n : ℕ} (x : Fin n → σ) {p : ℕ} (hp : p ≤ n)
    (hy : cutState A v₀ letter x p = some y) {j : ℕ} (hj : j ≤ n - p) :
    cutState A y letter (winWord x p) j = cutState A v₀ letter x (p + j) := by
  rw [cutState, winProd_winWord letter x hp hj, cutState_split A letter v₀ x p j, hy]

/-! ### The level's exit, semantically -/

/-- The greatest live cut of a level's axis. -/
noncomputable def levelCut {n : ℕ} (x : Fin n → σ) (p : ℕ) (y : X) : ℕ :=
  liveCut (killedAction (owner y)) ⟨owner y, rEq_refl (owner y)⟩ letter (winWord x p)

/-- The axis state there. -/
noncomputable def levelState {n : ℕ} (x : Fin n → σ) (p : ℕ) (y : X) :
    Option (RState (owner y)) :=
  cutState (killedAction (owner y)) ⟨owner y, rEq_refl (owner y)⟩ letter (winWord x p)
    (levelCut letter owner x p y)

lemma confLevel_fst {n : ℕ} (x : Fin n → σ) (p : ℕ) (y : X) :
    ((confLevel letter owner x (some (p, y))).1 : ℕ)
      = min p n + levelCut letter owner x p y := rfl

lemma confLevel_snd_fst {n : ℕ} (x : Fin n → σ) (p : ℕ) (y : X) :
    (confLevel letter owner x (some (p, y))).2.1
      = (levelState letter owner x p y).map Subtype.val := rfl

lemma confLevel_snd_snd {n : ℕ} (x : Fin n → σ) (p : ℕ) (y : X) :
    (confLevel letter owner x (some (p, y))).2.2
      = boundaryLetter x (min p n + levelCut letter owner x p y) := rfl

lemma levelCut_le {n : ℕ} (x : Fin n → σ) (p : ℕ) (y : X) :
    levelCut letter owner x p y ≤ n - min p n :=
  liveCut_le _ _ _ _

/-- **The level's exit state is the ambient state at the exit cut.** -/
theorem act_levelState (y : X) (hown : MinimalOwner A (some y) (owner y)) (v₀ : X)
    {n : ℕ} (x : Fin n → σ) {p : ℕ} (hp : p ≤ n)
    (hy : cutState A v₀ letter x p = some y) :
    A.act (some y) (((levelState letter owner x p y).map Subtype.val).getD 1)
      = cutState A v₀ letter x (p + levelCut letter owner x p y) := by
  have hmin : min p n = p := min_eq_left hp
  have hlvl : levelCut letter owner x p y
      = liveCut (killedAction (owner y)) ⟨owner y, rEq_refl (owner y)⟩ letter
        (winWord x p) := rfl
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1
    (liveCut_isSome (killedAction (owner y)) ⟨owner y, rEq_refl (owner y)⟩ letter
      (winWord x p))
  have hst : levelState letter owner x p y = some r := hr
  rw [hst]
  have hgd : ((some r).map Subtype.val).getD (1 : M) = r.val := rfl
  rw [hgd, act_cutState_ownerAxis letter hown (winWord x p) _ hr,
    cutState_winWord A letter v₀ y x hp hy
      (by have := levelCut_le letter owner x p y; omega)]
  rw [← hlvl]


/-- **The exit really leaves the component.**  One cut past the level's exit,
the run is no longer in the component it started in — the axis died there, and
`rEq_iff_sameComp` says that is what dying means. -/
theorem not_sameComp_succ (y : X) (hown : MinimalOwner A (some y) (owner y)) (v₀ : X)
    {n : ℕ} (x : Fin n → σ) {p : ℕ} (hp : p ≤ n)
    (hy : cutState A v₀ letter x p = some y)
    (hlt : p + levelCut letter owner x p y < n) :
    ¬ A.SameComp (some y)
        (cutState A v₀ letter x (p + levelCut letter owner x p y + 1)) := by
  have hmin : min p n = p := min_eq_left hp
  have hlt' : levelCut letter owner x p y < n - min p n := by omega
  have hdead : cutState (killedAction (owner y))
      (⟨owner y, rEq_refl (owner y)⟩ : RState (owner y)) letter (winWord x p)
      (levelCut letter owner x p y + 1) = none :=
    cutState_succ_eq_none _ _ letter (winWord x p) hlt'
  have hiff := cutState_ownerAxis_isSome_iff letter hown (winWord x p)
    (levelCut letter owner x p y + 1)
  rw [hdead] at hiff
  rw [Nat.add_assoc, ← cutState_winWord A letter v₀ y x hp hy
    (show levelCut letter owner x p y + 1 ≤ n - p by omega)]
  intro hc
  exact absurd (hiff.2 hc) (by simp)

/-! ### The invariant, and termination

The configuration carries one fact: its entry pair is a cut of the ambient run
together with the state there.  The step preserves it, and — by the same
reading of the level — strictly shrinks the reachable set, so the loop is over
within `|M|` levels.  `|M|`, not the ambient state count: the measure starts at
the size of `v₀`'s reachable orbit, which is the image of the acting monoid
(`card_reachSet_le_card_monoid`). -/

/-- Reading a boundary letter that exists. -/
lemma boundaryLetter_eq_some {n : ℕ} {x : Fin n → σ} {q : ℕ} {c : σ}
    (h : boundaryLetter x q = some c) : ∃ hq : q < n, x ⟨q, hq⟩ = c := by
  rw [boundaryLetter] at h
  by_cases hq : q < n
  · rw [dif_pos hq] at h
    exact ⟨hq, Option.some_injective _ h⟩
  · rw [dif_neg hq] at h
    exact absurd h (by simp)

/-- One letter of the ambient run. -/
lemma cutState_succ (v₀ : X) {n : ℕ} (x : Fin n → σ) {q : ℕ} (hq : q < n) :
    cutState A v₀ letter x (q + 1)
      = A.act (cutState A v₀ letter x q) (letter (x ⟨q, hq⟩)) := by
  rw [cutState_split A letter v₀ x q 1]
  congr 1
  rw [winProd, rangeProd_singleton _ hq]

/-- The invariant the configuration carries. -/
def ConfOk (v₀ : X) {n : ℕ} (x : Fin n → σ) : Conf X → Prop
  | none => True
  | some (p, y) => p ≤ n ∧ cutState A v₀ letter x p = some y

/-- **The step preserves the invariant and strictly shrinks the reachable
set.**  Both halves are the same reading of the level: its exit state is the
ambient state at the exit cut (`act_levelState`), and one letter further the
run has left the component (`not_sameComp_succ`). -/
theorem confOk_step (hown : ∀ z : X, MinimalOwner A (some z) (owner z)) (v₀ : X)
    {n : ℕ} (x : Fin n → σ) {p : ℕ} {y : X} (hp : p ≤ n)
    (hy : cutState A v₀ letter x p = some y) {p' : ℕ} {y' : X}
    (hstep : confStep A letter owner x (p, y) = some (p', y')) :
    (p' ≤ n ∧ cutState A v₀ letter x p' = some y')
      ∧ (reachSet A (some y')).card < (reachSet A (some y)).card := by
  have hmin : min p n = p := min_eq_left hp
  rw [confStep, stepOfRec, confLevel_snd_snd, confLevel_snd_fst, confLevel_fst,
    hmin] at hstep
  obtain ⟨c, hb, hstep⟩ := Option.bind_eq_some_iff.1 hstep
  obtain ⟨y'', hact, hstep⟩ := Option.map_eq_some_iff.1 hstep
  obtain ⟨hq, hxc⟩ := boundaryLetter_eq_some hb
  have hpair : p + levelCut letter owner x p y + 1 = p' ∧ y'' = y' := by
    exact ⟨congrArg Prod.fst hstep, congrArg Prod.snd hstep⟩
  obtain ⟨hp', rfl⟩ := hpair
  have hexit : A.act (some y)
      (((levelState letter owner x p y).map Subtype.val).getD 1)
      = cutState A v₀ letter x (p + levelCut letter owner x p y) :=
    act_levelState A letter owner y (hown y) v₀ x hp hy
  have hnext : cutState A v₀ letter x (p + levelCut letter owner x p y + 1)
      = some y'' := by
    rw [cutState_succ A letter v₀ x hq, ← hexit, hxc]
    exact hact
  refine ⟨⟨by omega, by rw [← hp']; exact hnext⟩, ?_⟩
  refine card_reachSet_lt_of_not_sameComp A
    ⟨((levelState letter owner x p y).map Subtype.val).getD 1 * letter c, ?_⟩ ?_
  · rw [← A.act_mul]
    exact hact
  · intro hc
    exact not_sameComp_succ A letter owner y (hown y) v₀ x hp hy (by omega)
      (by rw [hnext]; exact hc)

/-- The invariant, along the whole recursion. -/
theorem confOk_conf (hown : ∀ z : X, MinimalOwner A (some z) (owner z)) (v₀ : X)
    {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    ConfOk A letter v₀ x (conf A letter owner v₀ x j) := by
  induction j with
  | zero => exact ⟨Nat.zero_le n, by rw [cutState_zero]⟩
  | succ j ih =>
      rcases hc : conf A letter owner v₀ x j with _ | ⟨p, y⟩
      · have hb : conf A letter owner v₀ x (j + 1) = none := by
          rw [conf_succ, hc]
          rfl
        rw [hb]
        exact trivial
      · rw [hc] at ih
        have hb : conf A letter owner v₀ x (j + 1)
            = confStep A letter owner x (p, y) := by
          rw [conf_succ, hc]
          rfl
        rw [hb]
        rcases hs : confStep A letter owner x (p, y) with _ | ⟨p', y'⟩
        · exact trivial
        · exact (confOk_step A letter owner hown v₀ x ih.1 ih.2 hs).1

/-- The measure: how much of the state space is still reachable. -/
def confMeasure : Conf X → ℕ
  | none => 0
  | some (_, y) => (reachSet A (some y)).card

lemma confMeasure_pos {c : Conf X} (h : c ≠ none) : 0 < confMeasure A c := by
  rcases c with _ | ⟨p, y⟩
  · exact absurd rfl h
  · exact Finset.card_pos.2 ⟨some y, self_mem_reachSet A (some y)⟩

/-- **The loop makes progress.**  While the run has not finished, each level
has consumed one unit of the measure. -/
theorem confMeasure_add_le (hown : ∀ z : X, MinimalOwner A (some z) (owner z))
    (v₀ : X) {n : ℕ} (x : Fin n → σ) (j : ℕ)
    (hne : conf A letter owner v₀ x j ≠ none) :
    confMeasure A (conf A letter owner v₀ x j) + j
      ≤ confMeasure A (conf A letter owner v₀ x 0) := by
  induction j with
  | zero => omega
  | succ j ih =>
      rcases hc : conf A letter owner v₀ x j with _ | ⟨p, y⟩
      · exact absurd (by rw [conf_succ, hc]; rfl) hne
      · have hne' : conf A letter owner v₀ x j ≠ none := by rw [hc]; simp
        have hprev := ih hne'
        rw [hc] at hprev
        have hb : conf A letter owner v₀ x (j + 1)
            = confStep A letter owner x (p, y) := by
          rw [conf_succ, hc]
          rfl
        rcases hs : confStep A letter owner x (p, y) with _ | ⟨p', y'⟩
        · exact absurd (by rw [hb, hs]) hne
        · have hok := confOk_conf A letter owner hown v₀ x j
          rw [hc] at hok
          have hlt := (confOk_step A letter owner hown v₀ x hok.1 hok.2 hs).2
          rw [hb, hs]
          simp only [confMeasure] at hprev ⊢
          omega

/-- **Termination.**  After `|M|` levels the run has finished — it has either
reached the end of the word or died.  `|M|`, not the number of states: the
measure starts at the size of `v₀`'s reachable orbit, which is the image of
the monoid. -/
theorem conf_eq_none (hown : ∀ z : X, MinimalOwner A (some z) (owner z)) (v₀ : X)
    {n : ℕ} (x : Fin n → σ) {j : ℕ} (hj : Fintype.card M ≤ j) :
    conf A letter owner v₀ x j = none := by
  by_contra hne
  have hle := confMeasure_add_le A letter owner hown v₀ x j hne
  have hpos := confMeasure_pos A hne
  have h0 : confMeasure A (conf A letter owner v₀ x 0) ≤ Fintype.card M := by
    rw [conf_zero]
    exact card_reachSet_le_card_monoid A (some v₀)
  omega

end Semantics

/-! ## The packet, read off the transcript

The transcript determines the ambient packet: the run's greatest live cut is
the **last level's exit cut**, and the state there is that level's exit state.
Reading it off is not free — projecting a joint onto a coarsening is what the
joint-output discipline forbids — but it is only a factor two
(`HasDual.postcomp`). -/

section Answer

variable {σ M X : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M] [Fintype X] [DecidableEq X]
variable (A : RightAction M (Option X)) (letter : σ → M) (owner : X → M)

/-- A boundary letter that does not exist means the word is over. -/
lemma boundaryLetter_eq_none {n : ℕ} {x : Fin n → σ} {q : ℕ}
    (h : boundaryLetter x q = none) : n ≤ q := by
  by_contra hq
  rw [boundaryLetter, dif_pos (by omega)] at h
  exact absurd h (by simp)

/-- **Pinning the greatest live cut.**  A cut that is live, with nothing live
past it, *is* the greatest live cut. -/
theorem liveCut_eq_of (hnone : ∀ a, A.act none a = none) (v₀ : X) {n : ℕ}
    (x : Fin n → σ) {q : ℕ} (hq : q ≤ n)
    (hlive : (cutState A v₀ letter x q).isSome)
    (hdead : n ≤ q ∨ cutState A v₀ letter x (q + 1) = none) :
    liveCut A v₀ letter x = q :=
  le_antisymm ((liveCut_le_iff A v₀ letter hnone x q).2 hdead)
    ((liveSet A v₀ letter x).le_max' q ((mem_liveSet A v₀ letter).2 ⟨hq, hlive⟩))

/-- **A level's exit is live in the ambient action.**  It is in the component
of `y`, and `none` is a component of its own — nothing reaches out of it. -/
theorem cutState_exit_isSome (hnone : ∀ a, A.act none a = none) (y : X)
    (hown : MinimalOwner A (some y) (owner y)) (v₀ : X) {n : ℕ} (x : Fin n → σ)
    {p : ℕ} (hp : p ≤ n) (hy : cutState A v₀ letter x p = some y) :
    (cutState A v₀ letter x (p + levelCut letter owner x p y)).isSome := by
  have hklen := levelCut_le letter owner x p y
  have hmin : min p n = p := min_eq_left hp
  have hsc : A.SameComp (some y)
      (cutState A v₀ letter x (p + levelCut letter owner x p y)) := by
    have h1 := (cutState_ownerAxis_isSome_iff letter hown (winWord x p)
      (levelCut letter owner x p y)).1
      (liveCut_isSome (killedAction (owner y)) ⟨owner y, rEq_refl (owner y)⟩ letter
        (winWord x p))
    rwa [cutState_winWord A letter v₀ y x hp hy (by omega)] at h1
  rcases hc : cutState A v₀ letter x (p + levelCut letter owner x p y) with _ | z
  · rw [hc] at hsc
    obtain ⟨a, ha⟩ := hsc.2
    rw [hnone] at ha
    exact absurd ha (by simp)
  · rfl

/-- **The last level carries the answer.**  When the run finishes at level `j`,
the ambient greatest live cut is that level's exit cut. -/
theorem liveCut_eq_finish (hnone : ∀ a, A.act none a = none)
    (hown : ∀ z : X, MinimalOwner A (some z) (owner z)) (v₀ : X)
    {n : ℕ} (x : Fin n → σ) {j p : ℕ} {y : X}
    (hj : conf A letter owner v₀ x j = some (p, y))
    (hj1 : conf A letter owner v₀ x (j + 1) = none) :
    liveCut A v₀ letter x = p + levelCut letter owner x p y := by
  have hok := confOk_conf A letter owner hown v₀ x j
  rw [hj] at hok
  obtain ⟨hp, hy⟩ := hok
  have hmin : min p n = p := min_eq_left hp
  have hklen := levelCut_le letter owner x p y
  have hstep : confStep A letter owner x (p, y) = none := by
    rw [conf_succ, hj] at hj1
    exact hj1
  refine liveCut_eq_of A letter hnone v₀ x (by omega)
    (cutState_exit_isSome A letter owner hnone y (hown y) v₀ x hp hy) ?_
  rw [confStep, stepOfRec, confLevel_snd_snd, confLevel_snd_fst, confLevel_fst,
    hmin] at hstep
  rcases hb : boundaryLetter x (p + levelCut letter owner x p y) with _ | c
  · exact Or.inl (boundaryLetter_eq_none hb)
  · refine Or.inr ?_
    obtain ⟨hq, hxc⟩ := boundaryLetter_eq_some hb
    rw [hb] at hstep
    have hact : A.act (A.act (some y)
        (((levelState letter owner x p y).map Subtype.val).getD 1)) (letter c) = none := by
      simpa using hstep
    rw [cutState_succ A letter v₀ x hq,
      ← act_levelState A letter owner y (hown y) v₀ x hp hy, hxc]
    exact hact

/-- The run does finish, and at a level with a live predecessor. -/
theorem exists_finish (hown : ∀ z : X, MinimalOwner A (some z) (owner z)) (v₀ : X)
    {n : ℕ} (x : Fin n → σ) :
    ∃ (j p : ℕ) (y : X), j < Fintype.card M
      ∧ conf A letter owner v₀ x j = some (p, y)
      ∧ conf A letter owner v₀ x (j + 1) = none := by
  classical
  have hex : ∃ j, conf A letter owner v₀ x (j + 1) = none :=
    ⟨Fintype.card M, conf_eq_none A letter owner hown v₀ x (by omega)⟩
  have hj1 : conf A letter owner v₀ x (Nat.find hex + 1) = none := Nat.find_spec hex
  have hjne : conf A letter owner v₀ x (Nat.find hex) ≠ none := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hpos
    · rw [hz, conf_zero]
      simp
    · intro hc
      exact Nat.find_min hex (m := Nat.find hex - 1) (by omega)
        (by rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]; exact hc)
  have hlt : Nat.find hex < Fintype.card M := by
    by_contra hge
    exact hjne (conf_eq_none A letter owner hown v₀ x (by omega))
  obtain ⟨⟨p, y⟩, hpy⟩ :=
    Option.isSome_iff_exists.1 (Option.isSome_iff_ne_none.2 hjne)
  exact ⟨Nat.find hex, p, y, hlt, hpy, hj1⟩

set_option maxHeartbeats 1000000 in
-- The configuration recursion unfolds through the axis packet, so the
-- induction comparing two words' configurations is elaboration-heavy.
/-- **The transcript determines the packet.**  Two words with the same
transcript have the same configurations throughout, finish at the same level,
and so share that level's exit cut and exit state — which `liveCut_eq_finish`
and `act_levelState` say *is* the packet. -/
theorem packet_determined (hnone : ∀ a, A.act none a = none)
    (hown : ∀ z : X, MinimalOwner A (some z) (owner z)) (v₀ : X) {n m : ℕ}
    (hm : Fintype.card M ≤ m) (x x' : Fin n → σ)
    (h : (fun j : Fin m => levelAt A letter owner v₀ x (j : ℕ))
        = fun j : Fin m => levelAt A letter owner v₀ x' (j : ℕ)) :
    (liveCutIdx A v₀ letter x, cutState A v₀ letter x (liveCut A v₀ letter x))
      = (liveCutIdx A v₀ letter x',
          cutState A v₀ letter x' (liveCut A v₀ letter x')) := by
  have hlvl : ∀ i, i < m →
      levelAt A letter owner v₀ x i = levelAt A letter owner v₀ x' i :=
    fun i hi => congrFun h ⟨i, hi⟩
  have hconf : ∀ j, j ≤ m →
      conf A letter owner v₀ x j = conf A letter owner v₀ x' j := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [conf_zero, conf_zero]
    | succ i ih =>
        intro hj
        have hi := ih (by omega)
        rw [conf_succ, conf_succ, hi]
        rcases hc : conf A letter owner v₀ x' i with _ | ⟨p, y⟩
        · rw [show (none : Conf X).bind (confStep A letter owner x) = none from rfl,
            show (none : Conf X).bind (confStep A letter owner x') = none from rfl]
        · have hb : ∀ z : Fin n → σ,
              (some (p, y)).bind (confStep A letter owner z)
                = confStep A letter owner z (p, y) := fun _ => rfl
          rw [hb, hb, confStep, confStep]
          congr 1
          have hrec := hlvl i (by omega)
          rw [levelAt, levelAt, hi, hc] at hrec
          exact hrec
  obtain ⟨j, p, y, hjlt, hj, hj1⟩ := exists_finish A letter owner hown v₀ x
  have hjm : j < m := lt_of_lt_of_le hjlt hm
  have hj' : conf A letter owner v₀ x' j = some (p, y) := by
    rw [← hconf j (by omega)]
    exact hj
  have hj1' : conf A letter owner v₀ x' (j + 1) = none := by
    rw [← hconf (j + 1) (by omega)]
    exact hj1
  have hrec : confLevel letter owner x (some (p, y))
      = confLevel letter owner x' (some (p, y)) := by
    have hr := hlvl j hjm
    rw [levelAt, levelAt, hj, hj'] at hr
    exact hr
  have hcut : levelCut letter owner x p y = levelCut letter owner x' p y := by
    have h1 : ((confLevel letter owner x (some (p, y))).1 : ℕ)
        = ((confLevel letter owner x' (some (p, y))).1 : ℕ) := by rw [hrec]
    rw [confLevel_fst, confLevel_fst] at h1
    omega
  have hstate : (levelState letter owner x p y).map Subtype.val
      = (levelState letter owner x' p y).map Subtype.val := by
    have h2 : (confLevel letter owner x (some (p, y))).2.1
        = (confLevel letter owner x' (some (p, y))).2.1 := by rw [hrec]
    rwa [confLevel_snd_fst, confLevel_snd_fst] at h2
  have hlc := liveCut_eq_finish A letter owner hnone hown v₀ x hj hj1
  have hlc' := liveCut_eq_finish A letter owner hnone hown v₀ x' hj' hj1'
  have hok := confOk_conf A letter owner hown v₀ x j
  rw [hj] at hok
  have hok' := confOk_conf A letter owner hown v₀ x' j
  rw [hj'] at hok'
  refine Prod.ext ?_ ?_
  · exact Fin.ext (by rw [liveCutIdx_val, liveCutIdx_val, hlc, hlc', hcut])
  · have hst : cutState A v₀ letter x (liveCut A v₀ letter x)
        = A.act (some y) (((levelState letter owner x p y).map Subtype.val).getD 1) := by
      rw [hlc]
      exact (act_levelState A letter owner y (hown y) v₀ x hok.1 hok.2).symm
    have hst' : cutState A v₀ letter x' (liveCut A v₀ letter x')
        = A.act (some y)
          (((levelState letter owner x' p y).map Subtype.val).getD 1) := by
      rw [hlc']
      exact (act_levelState A letter owner y (hown y) v₀ x' hok'.1 hok'.2).symm
    rw [hst, hst', hstate]

/-- **The compiler's interface.**  *Anything* the transcript determines is
available at the transcript's cost times two — the packet below, and the
target test of `ActionTarget.lean`, each paying that postcomposition **once**.  Consumers
should go through this rather than postprocess `hasDual_actionPacket`, which
would pay it twice. -/
theorem hasDual_of_transcript_determined {O : Type} [DecidableEq O] [Nonempty O]
    {n : ℕ} {B : ℝ} (hpk : HasOwnerPackets letter owner n B) (v₀ : X) (m : ℕ)
    (g : (Fin n → σ) → O)
    (hdet : ∀ x x', (fun j : Fin m => levelAt A letter owner v₀ x (j : ℕ))
        = (fun j : Fin m => levelAt A letter owner v₀ x' (j : ℕ)) → g x = g x') :
    HasDual g (2 * ((m : ℝ) * (B * Real.sqrt (n : ℝ) + 2))) := by
  have hB := hpk.1
  have hs := Real.sqrt_nonneg (n : ℝ)
  exact HasDual.postcomp_of_determined (by positivity)
    (hasDual_transcript A hpk v₀ m) hdet

/-- **The action compiler** (the paper's `lem:ags-action-compiler`).  Axis
packets for the regular owners of an action's components compile into the
action's own endpoint-and-first-death packet, at `2|M|(B√n + 2)` — one level
per component, each an axis packet on the window from that component's entry
position plus one boundary letter, and one postcomposition for reading the
answer off the transcript.  The level count is `|M|`, which **upper-bounds**
the manuscript's `q`, because a **reachable orbit is the image of the acting
monoid** (`card_reachSet_le_card_monoid`); the ambient number of states never
enters.  (`q` is the order of the *transition* monoid, a quotient of `M` when
the action is not faithful.)

**What the packet says on death** is the *last live predecessor*, not the dead
state: `cut < n` means letter `cut` killed the run and the state is where it
was just before.  A consumer testing an endpoint must therefore check the cut
as well; see `ActionTarget.lean`. -/
theorem hasDual_actionPacket (hnone : ∀ a, A.act none a = none)
    (hown : ∀ z : X, MinimalOwner A (some z) (owner z)) {n : ℕ} {B : ℝ}
    (hpk : HasOwnerPackets letter owner n B) (v₀ : X) :
    HasDual (fun x : Fin n → σ =>
        (liveCutIdx A v₀ letter x, cutState A v₀ letter x (liveCut A v₀ letter x)))
      (2 * ((Fintype.card M : ℝ) * (B * Real.sqrt (n : ℝ) + 2))) :=
  hasDual_of_transcript_determined A letter owner hpk v₀ _ _ fun x x' hxx' =>
    packet_determined A letter owner hnone hown v₀ le_rfl x x' hxx'

end Answer

end MonoidProduct
