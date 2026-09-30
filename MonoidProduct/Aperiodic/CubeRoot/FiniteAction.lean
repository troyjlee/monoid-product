import MonoidProduct.Aperiodic.CubeRoot.Green
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Right actions, killed `R`-axes, components, and return elements

Part of the regular-action simulation (Section `sec:ags-actions` of the
paper).  The regular-action compiler runs a word against a **killed
right action**: the live states are one `R`-class `R_e`, and the moment the
trajectory leaves that class it enters a single absorbing state `†` and stays
there.  The paper justifies the "stays there" by the one line that right
ideals only decrease under right multiplication, and that is exactly how it
is proved here (`killedStep_dead`).

The file has three layers:

* `RightAction M X`, a bare bundled right action of a monoid on a type, with
  its run along a word.  The useful identity is
  `RightAction.run_eq_act_prod`: running a word *is* acting by its product,
  so a trajectory is determined by the prefix products — which is what lets
  the AGS packets read a trajectory off the products they already test.
* `Reaches`, its preorder laws, and `SameComp`, the strongly connected
  components of the action graph.
* **Return elements** `A.act v u = v`: closed under products and positive
  powers, so in an aperiodic monoid every return element has an *idempotent*
  return power (`exists_idempotent_isReturn`).  The set of idempotent return
  elements is therefore nonempty — it contains `1` — and has a `J`-minimal
  member (`exists_minimal_returnIdem`).  That minimal idempotent is the `e`
  whose `R`-class owns the component in the regular-owner cover below.

The killed action of a fixed idempotent `e` is `killedAction e`, on
`Option (RState e)` with `none` the absorbing `†`.
-/

namespace MonoidProduct

/-! ## Bundled right actions -/

/-- A right action of a monoid on a type. -/
structure RightAction (M X : Type) [Monoid M] where
  /-- The action. -/
  act : X → M → X
  /-- The identity acts trivially. -/
  act_one : ∀ x, act x 1 = x
  /-- Actions compose. -/
  act_mul : ∀ x a b, act (act x a) b = act x (a * b)

namespace RightAction

variable {M X : Type} [Monoid M] (A : RightAction M X)

/-- Running a word of letters, left to right. -/
def run (x : X) : List M → X := List.foldl A.act x

@[simp] lemma run_nil (x : X) : A.run x [] = x := rfl

@[simp] lemma run_cons (x : X) (a : M) (w : List M) :
    A.run x (a :: w) = A.run (A.act x a) w := rfl

/-- **Running a word is acting by its product.**  So a killed trajectory is
determined by the prefix products of the word — the quantities the AGS target
tests already speak about. -/
theorem run_eq_act_prod (x : X) (w : List M) : A.run x w = A.act x w.prod := by
  induction w generalizing x with
  | nil => rw [run_nil, List.prod_nil, A.act_one]
  | cons a w ih => rw [run_cons, ih, List.prod_cons, A.act_mul]

lemma run_append (x : X) (w₁ w₂ : List M) :
    A.run x (w₁ ++ w₂) = A.run (A.run x w₁) w₂ := by
  simp only [run_eq_act_prod, List.prod_append, A.act_mul]

/-! ## Reachability and components -/

/-- `y` is reachable from `x` under the action. -/
def Reaches (x y : X) : Prop := ∃ a : M, A.act x a = y

lemma reaches_refl (x : X) : A.Reaches x x := ⟨1, A.act_one x⟩

lemma Reaches.trans {x y z : X} (hxy : A.Reaches x y) (hyz : A.Reaches y z) :
    A.Reaches x z := by
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyz
  exact ⟨a * b, by rw [← A.act_mul, ha, hb]⟩

/-- Two states lie in the same strongly connected component. -/
def SameComp (x y : X) : Prop := A.Reaches x y ∧ A.Reaches y x

lemma sameComp_refl (x : X) : A.SameComp x x := ⟨A.reaches_refl x, A.reaches_refl x⟩

lemma SameComp.symm {x y : X} (h : A.SameComp x y) : A.SameComp y x := ⟨h.2, h.1⟩

lemma SameComp.trans {x y z : X} (hxy : A.SameComp x y) (hyz : A.SameComp y z) :
    A.SameComp x z :=
  ⟨hxy.1.trans A hyz.1, hyz.2.trans A hxy.2⟩

/-! ## Return elements -/

/-- `u` returns `v` to itself. -/
def IsReturn (v : X) (u : M) : Prop := A.act v u = v

lemma isReturn_one (v : X) : A.IsReturn v 1 := A.act_one v

lemma IsReturn.mul {v : X} {u u' : M} (h : A.IsReturn v u) (h' : A.IsReturn v u') :
    A.IsReturn v (u * u') := by
  change A.act v (u * u') = v
  rw [← A.act_mul, h, h']

/-- **Every power of a return element is a return element**, the empty one
included (`u ^ 0 = 1`). -/
lemma IsReturn.pow {v : X} {u : M} (h : A.IsReturn v u) : ∀ k : ℕ, A.IsReturn v (u ^ k)
  | 0 => by simpa using A.isReturn_one v
  | k + 1 => by
      have := (IsReturn.pow h k).mul A h
      rwa [← pow_succ] at this

end RightAction

/-! ## Idempotent return elements -/

section Return

variable {M X : Type} [Monoid M] [Fintype M] [DecidableEq M]
variable (A : RightAction M X) (v : X)

/-- **Every return element has an idempotent return power**, in an aperiodic
monoid — **and the power is exported**.  Item 4's owner-chain opens with
`MfM ⊆ MuM`, which is available only because `f` is a *positive power* of
`u`; the exponent must therefore survive into the statement. -/
theorem exists_idempotent_pow_isReturn [IsAperiodicMonoid M] {u : M}
    (h : A.IsReturn v u) :
    ∃ N : ℕ, 0 < N ∧ IsIdempotentElem (u ^ N) ∧ A.IsReturn v (u ^ N) := by
  obtain ⟨N, hN, hidem⟩ := exists_idempotent_pow u
  exact ⟨N, hN, hidem, h.pow A N⟩

/-- The first link of the owner-cover chain, packaged: an idempotent return
power of `u` generates no more than `u` does. -/
theorem exists_idempotent_isReturn_twoIdeal_subset [IsAperiodicMonoid M] {u : M}
    (h : A.IsReturn v u) :
    ∃ f : M, IsIdempotentElem f ∧ A.IsReturn v f ∧ twoIdeal f ⊆ twoIdeal u := by
  obtain ⟨N, hN, hidem, hret⟩ := exists_idempotent_pow_isReturn A v h
  exact ⟨u ^ N, hidem, hret, twoIdeal_pow_subset hN⟩

/-- The witness-free corollary. -/
theorem exists_idempotent_isReturn [IsAperiodicMonoid M] {u : M}
    (h : A.IsReturn v u) :
    ∃ f : M, IsIdempotentElem f ∧ A.IsReturn v f := by
  obtain ⟨f, hidem, hret, _⟩ := exists_idempotent_isReturn_twoIdeal_subset A v h
  exact ⟨f, hidem, hret⟩

section Minimal

variable [DecidableEq X]

/-- The idempotent return elements of `v`. -/
def returnIdems : Finset M :=
  Finset.univ.filter fun f => f * f = f ∧ A.act v f = v

lemma mem_returnIdems {f : M} :
    f ∈ returnIdems A v ↔ IsIdempotentElem f ∧ A.IsReturn v f := by
  simp [returnIdems, IsIdempotentElem, RightAction.IsReturn]

/-- The set is nonempty for the direct reason that it contains `1`; this does
not go through the idempotent-power theorem. -/
lemma returnIdems_nonempty : (returnIdems A v).Nonempty :=
  ⟨1, (mem_returnIdems A v).2 ⟨by simp [IsIdempotentElem], A.isReturn_one v⟩⟩

/-- **A `J`-minimal idempotent return element exists.**  This is the `e` whose
`R`-class owns the component of `v`; the minimality is what forces the chain
`MfM ⊆ MuM ⊆ MrM ⊆ MeM` of the owner cover to collapse. -/
theorem exists_minimal_returnIdem :
    ∃ e : M, IsIdempotentElem e ∧ A.IsReturn v e ∧
      ∀ f : M, IsIdempotentElem f → A.IsReturn v f →
        twoIdeal f ⊆ twoIdeal e → twoIdeal f = twoIdeal e := by
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image (returnIdems A v)
    (fun f => (twoIdeal f).card) (returnIdems_nonempty A v)
  obtain ⟨hidem, hret⟩ := (mem_returnIdems A v).1 he
  refine ⟨e, hidem, hret, fun f hf hfr hsub => ?_⟩
  exact Finset.eq_of_subset_of_card_le hsub
    (hmin f ((mem_returnIdems A v).2 ⟨hf, hfr⟩))

end Minimal

end Return

/-! ## The killed right action of an `R`-class -/

section Killed

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- The live states of the killed axis at `e`: its `R`-class. -/
abbrev RState (e : M) : Type := {r : M // REq r e}

variable (e : M)

/-- One step of the **killed right action**: stay in `R_e` if the product does,
otherwise die.  `none` is the absorbing state `†`. -/
def killedStep : Option (RState e) → M → Option (RState e)
  | none, _ => none
  | some r, a => if h : REq (r.val * a) e then some ⟨r.val * a, h⟩ else none

@[simp] lemma killedStep_none (a : M) : killedStep e none a = none := rfl

lemma killedStep_some (r : RState e) (a : M) :
    killedStep e (some r) a
      = if h : REq (r.val * a) e then some ⟨r.val * a, h⟩ else none := rfl

/-- **Death is permanent.**  If `r · a` has left `R_e` then no further right
multiple returns: principal right ideals only decrease, and `R_e` is the top
of that order inside the class. -/
theorem killedStep_dead {r : RState e} {a : M} (h : ¬ REq (r.val * a) e) (b : M) :
    ¬ REq (r.val * a * b) e := by
  intro hab
  refine h ?_
  have h1 : rightIdeal (r.val * a * b) ⊆ rightIdeal (r.val * a) :=
    rightIdeal_mul_subset _ _
  have h2 : rightIdeal (r.val * a) ⊆ rightIdeal r.val :=
    rightIdeal_mul_subset _ _
  have h3 : rightIdeal r.val = rightIdeal e := r.2
  refine Finset.Subset.antisymm (h3 ▸ h2) ?_
  calc rightIdeal e = rightIdeal (r.val * a * b) := hab.symm
    _ ⊆ rightIdeal (r.val * a) := h1

/-- **The killed action.** -/
def killedAction : RightAction M (Option (RState e)) where
  act := killedStep e
  act_one := by
    rintro (_ | r)
    · rfl
    · rw [killedStep_some, dif_pos (by rw [mul_one]; exact r.2)]
      simp
  act_mul := by
    rintro (_ | r) a b
    · rfl
    · rw [killedStep_some]
      by_cases h : REq (r.val * a) e
      · rw [dif_pos h, killedStep_some, killedStep_some]
        simp only [mul_assoc]
      · rw [dif_neg h, killedStep_none, killedStep_some,
          dif_neg (by rw [← mul_assoc]; exact killedStep_dead e h b)]

@[simp] lemma killedAction_act (s : Option (RState e)) (a : M) :
    (killedAction e).act s a = killedStep e s a := rfl

/-- Once dead, the whole remaining run is dead. -/
lemma killedAction_run_none (w : List M) : (killedAction e).run none w = none := by
  rw [RightAction.run_eq_act_prod]
  rfl

/-- **The live branch reads the product**: a run that survives ends at the
product, and it survives exactly when the product keeps the state in `R_e`. -/
lemma killedAction_run_some (r : RState e) (w : List M) :
    (killedAction e).run (some r) w
      = if h : REq (r.val * w.prod) e then some ⟨r.val * w.prod, h⟩ else none := by
  rw [RightAction.run_eq_act_prod]
  rfl

end Killed

/-! ## The regular-owner cover

The paper's regular-owner cover (`lem:ags-owner-cover`).  Fix a component `D`
of the action graph, a point `v ∈ D`, and let `e` be a `J`-minimal idempotent
return element of `v` — the return-element construction above produces one.  Then

    π_e : R_e → D,   π_e r = v · r

is **onto**, and it **intertwines the killed action on `R_e` with the action
on `D`**: `r · a` stays live exactly when `(v·r)·a` stays in the component,
and then `π_e (r a) = (v r) a`.  That is what turns a packet for one regular
`R`-class into a packet for an arbitrary finite action.

Surjectivity and the *reverse* implication of the intertwining run the same
argument: exhibit a return element `w` whose ideal is squeezed under `MeM`,
let minimality collapse the squeeze, and read off an `R`-equivalence by
stability (`lem:ags-green-stability`).  `twoIdeal_eq_of_isReturn_le` is that shared step,
isolated.  The forward implication — a live state maps into the component —
is elementary and uses no minimality at all. -/

section Owner

variable {M X : Type} [Monoid M] [Fintype M] [DecidableEq M]
variable (A : RightAction M X) (v : X)

/-- A `J`-minimal idempotent return element of `v`: the **owner** of its
component. -/
structure MinimalOwner (e : M) : Prop where
  /-- The owner is idempotent. -/
  idem : IsIdempotentElem e
  /-- It returns `v` to itself. -/
  ret : A.IsReturn v e
  /-- Its `J`-class is minimal among idempotent return elements. -/
  min : ∀ f : M, IsIdempotentElem f → A.IsReturn v f →
    twoIdeal f ⊆ twoIdeal e → twoIdeal f = twoIdeal e

/-- Every point has an owner.  The finite minimization needs the
states to be comparable, but no aperiodicity. -/
theorem exists_minimalOwner [DecidableEq X] : ∃ e : M, MinimalOwner A v e := by
  obtain ⟨e, hidem, hret, hmin⟩ := exists_minimal_returnIdem A v
  exact ⟨e, ⟨hidem, hret, hmin⟩⟩

variable {A v} {e : M}

/-- **The live states land in the component.**  If `r R e` then `v·r` is
reachable from `v`, and a relation `e = r·b` sends it back.  Elementary: no
minimality, no aperiodicity. -/
theorem sameComp_act_of_rEq (hown : MinimalOwner A v e) {r : M} (hr : REq r e) :
    A.SameComp v (A.act v r) := by
  obtain ⟨b, hb⟩ := rLe_iff_exists.1 (rEq_iff.1 hr).2
  refine ⟨⟨r, rfl⟩, ⟨b, ?_⟩⟩
  rw [A.act_mul, hb, hown.ret]

section Aperiodic

variable [IsAperiodicMonoid M]

/-- **Minimality collapses a squeezed return element.**  If `w` returns `v`
and `MwM ⊆ MeM`, then already `MwM = MeM`: an idempotent power of `w` is an
idempotent return element inside `MwM`, so minimality pins it at `MeM`, and
the squeeze closes. -/
theorem twoIdeal_eq_of_isReturn_le (hown : MinimalOwner A v e) {w : M}
    (hret : A.IsReturn v w) (hsub : twoIdeal w ⊆ twoIdeal e) :
    twoIdeal w = twoIdeal e := by
  obtain ⟨f, hfidem, hfret, hfsub⟩ :=
    exists_idempotent_isReturn_twoIdeal_subset A v hret
  have hfe : twoIdeal f = twoIdeal e := hown.min f hfidem hfret (hfsub.trans hsub)
  exact Finset.Subset.antisymm hsub (hfe ▸ hfsub)

/-- **Surjectivity of the owner cover.**  For `y` in the component of `v`,
with `v · a = y` and `y · b = v`, the element `r = e·a` lands in `R_e`.  The
element `u = r·b` returns `v`, and with `f = u^N` its exported idempotent
power the chain reads

    `MfM ⊆ MuM ⊆ MrM ⊆ MeM`

*before* any minimality is used.  Minimality applies to `f` and gives
`MfM = MeM`, which is what closes the chain and yields `MuM = MrM = MeM`.
Stability then upgrades `rM ⊆ eM` to `r R e`, and `v·r = v·e·a = v·a = y`. -/
theorem ownerCover_surjective (hown : MinimalOwner A v e) {y : X}
    (hy : A.SameComp v y) : ∃ r : M, REq r e ∧ A.act v r = y := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hy
  refine ⟨e * a, ?_, ?_⟩
  · -- the squeeze, then stability
    have hva : A.act v (e * a) = y := by rw [← A.act_mul, hown.ret, ha]
    have hret : A.IsReturn v (e * a * b) := by
      change A.act v (e * a * b) = v
      rw [← A.act_mul, hva, hb]
    have hsub₁ : twoIdeal (e * a * b) ⊆ twoIdeal (e * a) := twoIdeal_mul_subset_left _ _
    have hsub₂ : twoIdeal (e * a) ⊆ twoIdeal e := twoIdeal_mul_subset_left _ _
    have hcollapse : twoIdeal (e * a * b) = twoIdeal e :=
      twoIdeal_eq_of_isReturn_le hown hret (hsub₁.trans hsub₂)
    have hJ : twoIdeal (e * a) = twoIdeal e :=
      Finset.Subset.antisymm hsub₂ (hcollapse ▸ hsub₁)
    exact rEq_of_twoIdeal_eq_of_rLe hJ (rLe_iff_subset.2 (rightIdeal_mul_subset _ _))
  · rw [← A.act_mul, hown.ret, ha]

/-- **The converse.**  If `(v·r)·a` is back in the component, then `r·a` is
still live.  The return element is `w = r·a·b`, and with `f = w^N` its
exported idempotent power the chain reads
`MfM ⊆ MwM ⊆ M(ra)M ⊆ MrM = MeM` before minimality; minimality at `f` closes
it, and stability upgrades `raM ⊆ rM` to `r a R r R e`. -/
theorem rEq_of_sameComp_act (hown : MinimalOwner A v e) {r : M} (hr : REq r e)
    (a : M) (h : A.SameComp v (A.act v (r * a))) : REq (r * a) e := by
  obtain ⟨-, ⟨b, hb⟩⟩ := h
  have hret : A.IsReturn v (r * a * b) := by
    change A.act v (r * a * b) = v
    rw [← A.act_mul, hb]
  have hre : twoIdeal r = twoIdeal e := twoIdeal_eq_of_rEq hr
  have hsub₁ : twoIdeal (r * a * b) ⊆ twoIdeal (r * a) := twoIdeal_mul_subset_left _ _
  have hsub₂ : twoIdeal (r * a) ⊆ twoIdeal r := twoIdeal_mul_subset_left _ _
  have hcollapse : twoIdeal (r * a * b) = twoIdeal e :=
    twoIdeal_eq_of_isReturn_le hown hret (hsub₁.trans (hsub₂.trans hre.subset))
  have hJ : twoIdeal (r * a) = twoIdeal r :=
    Finset.Subset.antisymm hsub₂ (hre ▸ hcollapse ▸ hsub₁)
  exact rEq_trans
    (rEq_of_twoIdeal_eq_of_rLe hJ (rLe_iff_subset.2 (rightIdeal_mul_subset _ _))) hr

/-- **The intertwining.**  From a live state, the killed step survives exactly
when the component step stays in the component. -/
theorem ownerCover_intertwine (hown : MinimalOwner A v e) {r : M} (hr : REq r e)
    (a : M) : REq (r * a) e ↔ A.SameComp v (A.act v (r * a)) :=
  ⟨fun h => sameComp_act_of_rEq hown h, fun h => rEq_of_sameComp_act hown hr a h⟩

end Aperiodic

end Owner

/-- **The raw ambient identity** `v·(r·a) = (v·r)·a`: pure associativity in
the action, needing nothing but the action laws, and holding on the dead
branch as well as the live one.

Under the live hypothesis `r·a ∈ R_e` this *is* the cover's intertwining
identity `π_e (r·a) = (v·r)·a`; off the live branch `π_e (r·a)` is not
defined, so only the ambient equation survives.  It is stated separately for
that reason. -/
theorem ownerCover_map {M X : Type} [Monoid M] {A : RightAction M X} {v : X}
    (r a : M) : A.act v (r * a) = A.act (A.act v r) a :=
  (A.act_mul v r a).symm

end MonoidProduct
