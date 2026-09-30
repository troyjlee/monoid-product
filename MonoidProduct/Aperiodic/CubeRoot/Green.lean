import MonoidProduct.Aperiodic.Ideals
import Mathlib.Algebra.Group.Idempotent

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Green's `R` and `L` relations, regularity, and regular classes

The development already carries Green's `J` in the form the
AGS decomposition uses — principal two-sided ideals `twoIdeal`, with
`Simon/Defs.lean` naming `JLe`/`JEq` on top of them.  What the regular-action
compiler needs in addition is the **one-sided** structure: `R` and `L`, von
Neumann regularity, and the notion of a *regular* `J`-class.

Everything here is stated over `Aperiodic/Ideals.lean`'s `Finset` ideals, in
the same idiom, so that the AGS files and the cube-root peel share one
vocabulary.  (`Simon/Defs.lean` is not imported: it drags in the Boolean
unitriangular development, which this cone does not need.)

The content:

* `RLe`/`LLe` preorders and `REq`/`LEq` equivalences, with principal-ideal
  bridges and the passage to `J`;
* `IsVonNeumannRegular a := ∃ x, a * x * a = a`, and the two idempotents it produces:
  `x * a` is idempotent and `L`-equivalent to `a`, `a * x` is idempotent and
  `R`-equivalent to `a`;
* the converse — an element `R`- or `L`-equivalent to an idempotent is
  regular — hence regularity is an `R`- and `L`-class invariant;
* `IsRegularClass`: a `J`-class is regular iff it contains a regular element
  iff it contains an idempotent;
* in an aperiodic monoid every element has an idempotent positive power, so
  every element's *own* powers reach a regular class.

**Stability** (`lem:ags-green-stability`) closes the section: inside one `J`-class a one-sided
containment is already a one-sided *equivalence*, and every element of a
regular `J`-class is regular.  Both come straight from the aperiodic sandwich
lemmas of `Aperiodic/Defs.lean`, so they cost a few lines rather than a
development.  Green's lemma proper is still not here, and is not needed.

Calibration on the small monoids lives in `GreenCalibration.lean`, so that
this module depends only on the ideals and Mathlib's idempotents.
-/

namespace MonoidProduct

section Green

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The one-sided preorders -/

/-- Green's `≤_R`: `a` lies in the principal right ideal of `b`. -/
def RLe (a b : M) : Prop := a ∈ rightIdeal b

/-- Green's `≤_L`. -/
def LLe (a b : M) : Prop := a ∈ leftIdeal b

/-- Green's `R`: equal principal right ideals. -/
def REq (a b : M) : Prop := rightIdeal a = rightIdeal b

/-- Green's `L`: equal principal left ideals. -/
def LEq (a b : M) : Prop := leftIdeal a = leftIdeal b

instance (a b : M) : Decidable (RLe a b) :=
  inferInstanceAs (Decidable (a ∈ rightIdeal b))

instance (a b : M) : Decidable (LLe a b) :=
  inferInstanceAs (Decidable (a ∈ leftIdeal b))

instance (a b : M) : Decidable (REq a b) :=
  inferInstanceAs (Decidable (rightIdeal a = rightIdeal b))

instance (a b : M) : Decidable (LEq a b) :=
  inferInstanceAs (Decidable (leftIdeal a = leftIdeal b))

lemma rLe_iff_exists {a b : M} : RLe a b ↔ ∃ q, b * q = a := mem_rightIdeal

lemma lLe_iff_exists {a b : M} : LLe a b ↔ ∃ p, p * b = a := mem_leftIdeal

lemma rLe_iff_subset {a b : M} : RLe a b ↔ rightIdeal a ⊆ rightIdeal b :=
  ⟨rightIdeal_subset_of_mem, fun h => h (self_mem_rightIdeal a)⟩

lemma lLe_iff_subset {a b : M} : LLe a b ↔ leftIdeal a ⊆ leftIdeal b :=
  ⟨leftIdeal_subset_of_mem, fun h => h (self_mem_leftIdeal a)⟩

lemma rLe_refl (a : M) : RLe a a := self_mem_rightIdeal a

lemma lLe_refl (a : M) : LLe a a := self_mem_leftIdeal a

lemma rLe_trans {a b c : M} (hab : RLe a b) (hbc : RLe b c) : RLe a c :=
  rLe_iff_subset.2 ((rLe_iff_subset.1 hab).trans (rLe_iff_subset.1 hbc))

lemma lLe_trans {a b c : M} (hab : LLe a b) (hbc : LLe b c) : LLe a c :=
  lLe_iff_subset.2 ((lLe_iff_subset.1 hab).trans (lLe_iff_subset.1 hbc))

lemma rEq_iff {a b : M} : REq a b ↔ RLe a b ∧ RLe b a := by
  rw [REq, rLe_iff_subset, rLe_iff_subset]
  exact ⟨fun h => ⟨h.subset, h.symm.subset⟩, fun h => Finset.Subset.antisymm h.1 h.2⟩

lemma lEq_iff {a b : M} : LEq a b ↔ LLe a b ∧ LLe b a := by
  rw [LEq, lLe_iff_subset, lLe_iff_subset]
  exact ⟨fun h => ⟨h.subset, h.symm.subset⟩, fun h => Finset.Subset.antisymm h.1 h.2⟩

lemma rEq_refl (a : M) : REq a a := rfl

lemma rEq_symm {a b : M} (h : REq a b) : REq b a := h.symm

lemma rEq_trans {a b c : M} (hab : REq a b) (hbc : REq b c) : REq a c := hab.trans hbc

lemma lEq_refl (a : M) : LEq a a := rfl

lemma lEq_symm {a b : M} (h : LEq a b) : LEq b a := h.symm

lemma lEq_trans {a b c : M} (hab : LEq a b) (hbc : LEq b c) : LEq a c := hab.trans hbc

/-! ## Passage to `J` -/

lemma twoIdeal_subset_of_rLe {a b : M} (h : RLe a b) : twoIdeal a ⊆ twoIdeal b := by
  obtain ⟨q, hq⟩ := rLe_iff_exists.1 h
  exact twoIdeal_subset_of_mem (mem_twoIdeal.2 ⟨1, q, by rw [one_mul]; exact hq⟩)

lemma twoIdeal_subset_of_lLe {a b : M} (h : LLe a b) : twoIdeal a ⊆ twoIdeal b := by
  obtain ⟨p, hp⟩ := lLe_iff_exists.1 h
  exact twoIdeal_subset_of_mem (mem_twoIdeal.2 ⟨p, 1, by rw [mul_one]; exact hp⟩)

lemma twoIdeal_eq_of_rEq {a b : M} (h : REq a b) : twoIdeal a = twoIdeal b := by
  obtain ⟨h1, h2⟩ := rEq_iff.1 h
  exact Finset.Subset.antisymm (twoIdeal_subset_of_rLe h1) (twoIdeal_subset_of_rLe h2)

lemma twoIdeal_eq_of_lEq {a b : M} (h : LEq a b) : twoIdeal a = twoIdeal b := by
  obtain ⟨h1, h2⟩ := lEq_iff.1 h
  exact Finset.Subset.antisymm (twoIdeal_subset_of_lLe h1) (twoIdeal_subset_of_lLe h2)

/-- **A positive power generates no more than its base.**  Needed wherever an
idempotent power has to be compared with the element it came from — the owner
cover's chain `MfM ⊆ MuM` is exactly this. -/
lemma twoIdeal_pow_subset {a : M} {N : ℕ} (hN : 0 < N) :
    twoIdeal (a ^ N) ⊆ twoIdeal a := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  rw [pow_succ]
  exact twoIdeal_mul_subset_right _ _

/-! ## Regularity -/

/-- **Von Neumann regularity**: `a` has an inner inverse.

Spelled out rather than called `IsRegular`, which in Mathlib means
*cancellable* (`IsLeftRegular ∧ IsRightRegular`) — a different property, and
one that would make every `open QuantumQueryComplexity` consumer ambiguous. -/
def IsVonNeumannRegular (a : M) : Prop := ∃ x : M, a * x * a = a

lemma IsIdempotentElem.isVonNeumannRegular {e : M} (he : IsIdempotentElem e) :
    IsVonNeumannRegular e :=
  ⟨e, by rw [he, he]⟩

lemma isVonNeumannRegular_one : IsVonNeumannRegular (1 : M) := ⟨1, by simp⟩

/-- From an inner inverse, the **left** idempotent `x · a`. -/
lemma IsVonNeumannRegular.idem_left {a x : M} (h : a * x * a = a) : IsIdempotentElem (x * a) := by
  change x * a * (x * a) = x * a
  calc x * a * (x * a) = x * (a * x * a) := by simp only [mul_assoc]
    _ = x * a := by rw [h]

/-- From an inner inverse, the **right** idempotent `a · x`. -/
lemma IsVonNeumannRegular.idem_right {a x : M} (h : a * x * a = a) : IsIdempotentElem (a * x) := by
  change a * x * (a * x) = a * x
  calc a * x * (a * x) = (a * x * a) * x := by simp only [mul_assoc]
    _ = a * x := by rw [h]

/-- The left idempotent is `L`-equivalent to `a`: `a = a · (x · a)`. -/
lemma IsVonNeumannRegular.lEq_idem_left {a x : M} (h : a * x * a = a) : LEq a (x * a) :=
  lEq_iff.2 ⟨lLe_iff_exists.2 ⟨a, by rw [← mul_assoc]; exact h⟩,
    lLe_iff_exists.2 ⟨x, rfl⟩⟩

/-- The right idempotent is `R`-equivalent to `a`: `a = (a · x) · a`. -/
lemma IsVonNeumannRegular.rEq_idem_right {a x : M} (h : a * x * a = a) : REq a (a * x) :=
  rEq_iff.2 ⟨rLe_iff_exists.2 ⟨a, h⟩, rLe_iff_exists.2 ⟨x, rfl⟩⟩

/-! ## The converse: `R`- or `L`-equivalence to an idempotent

An element `R`-equivalent to an idempotent `e` is regular, and the inner
inverse is read off the equivalence: if `a · s = e` and `e · t = a` then
`a · s · a = e · a = a`, the last step because `e` absorbs on the left of
anything it generates. -/

lemma isVonNeumannRegular_of_rEq_idem {a e : M} (he : IsIdempotentElem e) (h : REq a e) :
    IsVonNeumannRegular a := by
  obtain ⟨h1, h2⟩ := rEq_iff.1 h
  obtain ⟨t, ht⟩ := rLe_iff_exists.1 h1
  obtain ⟨s, hs⟩ := rLe_iff_exists.1 h2
  refine ⟨s, ?_⟩
  calc a * s * a = e * a := by rw [hs]
    _ = e * (e * t) := by rw [ht]
    _ = e * e * t := by rw [mul_assoc]
    _ = e * t := by rw [he.eq]
    _ = a := ht

lemma isVonNeumannRegular_of_lEq_idem {a e : M} (he : IsIdempotentElem e) (h : LEq a e) :
    IsVonNeumannRegular a := by
  obtain ⟨h1, h2⟩ := lEq_iff.1 h
  obtain ⟨p, hp⟩ := lLe_iff_exists.1 h1
  obtain ⟨q, hq⟩ := lLe_iff_exists.1 h2
  refine ⟨q, ?_⟩
  calc a * q * a = a * (q * a) := mul_assoc _ _ _
    _ = a * e := by rw [hq]
    _ = p * e * e := by rw [hp]
    _ = p * (e * e) := mul_assoc _ _ _
    _ = p * e := by rw [he.eq]
    _ = a := hp

/-- **Regularity is an `R`-class invariant.** -/
lemma IsVonNeumannRegular.of_rEq {a b : M} (ha : IsVonNeumannRegular a)
    (h : REq a b) : IsVonNeumannRegular b := by
  obtain ⟨x, hx⟩ := ha
  exact isVonNeumannRegular_of_rEq_idem (IsVonNeumannRegular.idem_right hx)
    (rEq_trans (rEq_symm h) (IsVonNeumannRegular.rEq_idem_right hx))

/-- **Regularity is an `L`-class invariant.** -/
lemma IsVonNeumannRegular.of_lEq {a b : M} (ha : IsVonNeumannRegular a)
    (h : LEq a b) : IsVonNeumannRegular b := by
  obtain ⟨x, hx⟩ := ha
  exact isVonNeumannRegular_of_lEq_idem (IsVonNeumannRegular.idem_left hx)
    (lEq_trans (lEq_symm h) (IsVonNeumannRegular.lEq_idem_left hx))

/-! ## Regular `J`-classes -/

/-- A `J`-class is **regular** when it contains a regular element. -/
def IsRegularClass (a : M) : Prop := ∃ b : M, twoIdeal b = twoIdeal a ∧ IsVonNeumannRegular b

/-- **A `J`-class is regular exactly when it contains an idempotent.**  The
forward direction is the left idempotent `x · a`, which is `L`-equivalent to
`a` and therefore `J`-equivalent to it. -/
theorem isRegularClass_iff_exists_idem {a : M} :
    IsRegularClass a ↔ ∃ e : M, twoIdeal e = twoIdeal a ∧ IsIdempotentElem e := by
  constructor
  · rintro ⟨b, hb, x, hx⟩
    refine ⟨x * b, ?_, IsVonNeumannRegular.idem_left hx⟩
    rw [← hb]
    exact (twoIdeal_eq_of_lEq (IsVonNeumannRegular.lEq_idem_left hx)).symm
  · rintro ⟨e, he, hidem⟩
    exact ⟨e, he, IsIdempotentElem.isVonNeumannRegular hidem⟩

lemma IsVonNeumannRegular.isRegularClass {a : M} (h : IsVonNeumannRegular a) : IsRegularClass a :=
  ⟨a, rfl, h⟩

/-- The `J`-class of the identity is regular. -/
lemma isRegularClass_one : IsRegularClass (1 : M) := isVonNeumannRegular_one.isRegularClass

/-! ## Regular height

The paper's `h(K)`: the length of the longest strictly increasing chain
of **regular** `J`-classes starting at `K`.  This is `jLevel` with the
ascent restricted to regular classes, and it is defined by the same
well-founded recursion on the size of the principal ideal.

**Scope.**  The paper defines `h(K)` only for *regular* classes `K`; the
recursion below is defined at every element, and agrees with `h(K)` whenever
the base class is regular — only the classes strictly *above* the base are
required to be regular either way.  At a non-regular base it is still the
longest regular chain above that base, which is what the height-drop lemma
uses and is why the definition is left total. -/

instance (a : M) : Decidable (IsVonNeumannRegular a) :=
  inferInstanceAs (Decidable (∃ x : M, a * x * a = a))

instance (a : M) : Decidable (IsRegularClass a) :=
  inferInstanceAs (Decidable (∃ b : M, twoIdeal b = twoIdeal a ∧ IsVonNeumannRegular b))

/-- The **regular** classes strictly above `a`. -/
def regAboveJ (a : M) : Finset M :=
  Finset.univ.filter fun b => twoIdeal a ⊂ twoIdeal b ∧ IsRegularClass b

lemma mem_regAboveJ {a b : M} :
    b ∈ regAboveJ a ↔ twoIdeal a ⊂ twoIdeal b ∧ IsRegularClass b := by
  simp [regAboveJ]

/-- **The regular height** of `a`: the longest strictly increasing chain of
regular `J`-classes above `MaM`.  Larger ideals have smaller height, the same
orientation `jLevel` uses. -/
def regHeight (a : M) : ℕ :=
  (regAboveJ a).attach.sup fun b => regHeight b.1 + 1
termination_by Fintype.card M - (twoIdeal a).card
decreasing_by
  have h1 : (twoIdeal a).card < (twoIdeal b.1).card :=
    Finset.card_lt_card (mem_regAboveJ.1 b.2).1
  have h2 : (twoIdeal b.1).card ≤ Fintype.card M := Finset.card_le_univ _
  omega

lemma regHeight_eq (a : M) :
    regHeight a = (regAboveJ a).sup fun b => regHeight b + 1 := by
  rw [regHeight]
  exact Finset.sup_attach (regAboveJ a) (fun b : M => regHeight b + 1)

lemma regHeight_congr {a b : M} (h : twoIdeal a = twoIdeal b) :
    regHeight a = regHeight b := by
  have haux : regAboveJ a = regAboveJ b := by
    ext c
    simp [mem_regAboveJ, h]
  rw [regHeight_eq, regHeight_eq, haux]

/-- **Strict ascent through a regular class lowers the regular height.**  The
regular-axis recurrence descends along this.

Note the asymmetry: only the *upper* class `b` must be regular.  The lower
one is unconstrained, which makes this — and `regHeight_drop` downstream —
stronger than the paper-shaped use, where the lower class is regular too. -/
theorem regHeight_lt_of_ssubset {a b : M} (h : twoIdeal a ⊂ twoIdeal b)
    (hb : IsRegularClass b) : regHeight b < regHeight a := by
  have hmem : b ∈ regAboveJ a := mem_regAboveJ.2 ⟨h, hb⟩
  have := Finset.le_sup (f := fun c : M => regHeight c + 1) hmem
  rw [← regHeight_eq] at this
  omega

/-! ### The base of the recurrence -/

lemma regAboveJ_one : regAboveJ (1 : M) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun b hb => ?_
  obtain ⟨h, -⟩ := mem_regAboveJ.1 hb
  rw [twoIdeal_one] at h
  exact absurd (lt_of_lt_of_le h (Finset.subset_univ _)) (lt_irrefl _)

/-- **The base case**: nothing is strictly above the identity. -/
@[simp] theorem regHeight_one : regHeight (1 : M) = 0 := by
  rw [regHeight_eq, regAboveJ_one, Finset.sup_empty]
  rfl

/-- In an aperiodic monoid only the identity generates everything. -/
theorem one_mem_twoIdeal_iff [IsAperiodicMonoid M] {a : M} :
    (1 : M) ∈ twoIdeal a ↔ a = 1 := by
  constructor
  · intro h
    obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 h
    exact (mul_eq_one_iff'.1 (mul_eq_one_iff'.1 hpq).1).2
  · rintro rfl
    exact self_mem_twoIdeal 1

/-- **The base case, characterized**: in an aperiodic monoid the regular
height vanishes exactly at the identity.  This pins the action compiler's
base case — the only class with nothing regular above it is `[1]`. -/
theorem regHeight_eq_zero_iff [IsAperiodicMonoid M] {a : M} :
    regHeight a = 0 ↔ a = 1 := by
  refine ⟨fun h => by_contra fun hne => ?_, fun h => by rw [h, regHeight_one]⟩
  have hne' : twoIdeal a ≠ Finset.univ := fun hc =>
    hne (one_mem_twoIdeal_iff.1 (by rw [hc]; exact Finset.mem_univ 1))
  have hlt : twoIdeal a ⊂ twoIdeal (1 : M) := by
    rw [twoIdeal_one]
    exact lt_of_le_of_ne (Finset.subset_univ _) hne'
  have hpos := regHeight_lt_of_ssubset hlt isRegularClass_one
  rw [regHeight_one, h] at hpos
  omega

/-! ## Aperiodic monoids: idempotent powers

Every element of an aperiodic monoid has an idempotent positive power.

**This is not where apex representatives come from.**  An idempotent power
can sit in a *strictly lower* `J`-class than its source — in `N₂`, `a² = 0`
is idempotent while `MaM ⊋ M0M` — so `a ^ N` need not represent `a`'s class
at all.  Idempotent representatives *of a given regular class* come from
`isRegularClass_iff_exists_idem`; idempotent powers are for return
elements, where the drop is harmless. -/

lemma pow_eq_pow_of_stab {a : M} {N : ℕ} (h : a ^ N = a ^ (N + 1)) :
    ∀ {k : ℕ}, N ≤ k → a ^ k = a ^ N := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => rfl
  | succ d ih =>
      have hstep : a ^ (N + d) = a ^ (N + d + 1) := pow_stab h (by omega)
      calc a ^ (N + (d + 1)) = a ^ (N + d + 1) := by rw [show N + (d + 1) = N + d + 1 by omega]
        _ = a ^ (N + d) := hstep.symm
        _ = a ^ N := ih (by omega)

/-- **Every element of an aperiodic monoid has an idempotent positive
power.** -/
theorem exists_idempotent_pow [IsAperiodicMonoid M] (a : M) :
    ∃ N : ℕ, 0 < N ∧ IsIdempotentElem (a ^ N) := by
  obtain ⟨N, hN, h⟩ := IsAperiodicMonoid.stabilizes a
  refine ⟨N, hN, ?_⟩
  change a ^ N * a ^ N = a ^ N
  rw [← pow_add]
  exact pow_eq_pow_of_stab h (by omega)

/-- Consequently every element has a positive power lying in *some* regular
`J`-class — not, in general, in its own. -/
theorem exists_pow_isRegularClass [IsAperiodicMonoid M] (a : M) :
    ∃ N : ℕ, 0 < N ∧ IsRegularClass (a ^ N) := by
  obtain ⟨N, hN, he⟩ := exists_idempotent_pow a
  exact ⟨N, hN, IsVonNeumannRegular.isRegularClass (IsIdempotentElem.isVonNeumannRegular he)⟩

/-! ## Stability

The aperiodic sandwich lemmas `sandwich_left`/`sandwich_right` say that a
factorisation `p · q · r = q` collapses on each side separately.  That is
exactly the content of Green's stability, and it gives both orientations the
action compiler consumes. -/

variable [IsAperiodicMonoid M]

/-- **Stability, `R`-form**: inside one `J`-class, `≤_R` is already `R`.
From `b · u = a` and `p · a · q = b` we get `p · b · (u·q) = b`, so
`b · (u·q) = b` by the sandwich, i.e. `a · q = b`. -/
theorem rEq_of_twoIdeal_eq_of_rLe {a b : M} (hJ : twoIdeal a = twoIdeal b)
    (hR : RLe a b) : REq a b := by
  obtain ⟨u, hu⟩ := rLe_iff_exists.1 hR
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 (hJ ▸ self_mem_twoIdeal b)
  have hsand : p * b * (u * q) = b := by
    calc p * b * (u * q) = p * (b * u) * q := by simp only [mul_assoc]
      _ = p * a * q := by rw [hu]
      _ = b := hpq
  refine rEq_iff.2 ⟨hR, rLe_iff_exists.2 ⟨q, ?_⟩⟩
  calc a * q = b * u * q := by rw [hu]
    _ = b * (u * q) := mul_assoc _ _ _
    _ = b := sandwich_right hsand

/-- **Stability, `L`-form**. -/
theorem lEq_of_twoIdeal_eq_of_lLe {a b : M} (hJ : twoIdeal a = twoIdeal b)
    (hL : LLe a b) : LEq a b := by
  obtain ⟨u, hu⟩ := lLe_iff_exists.1 hL
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 (hJ ▸ self_mem_twoIdeal b)
  have hsand : p * u * b * q = b := by
    calc p * u * b * q = p * (u * b) * q := by simp only [mul_assoc]
      _ = p * a * q := by rw [hu]
      _ = b := hpq
  refine lEq_iff.2 ⟨hL, lLe_iff_exists.2 ⟨p, ?_⟩⟩
  calc p * a = p * (u * b) := by rw [hu]
    _ = p * u * b := (mul_assoc _ _ _).symm
    _ = b := sandwich_left hsand

/-- **Every element of a regular `J`-class is regular.**  With `e` an
idempotent of the class, `x · a · y = e` and `p · e · q = a` give
`(x·p) · e · (q·y) = e`, so the sandwich collapses both sides to
`(x·p)·e = e` and `e·(q·y) = e`; then

  `a · (y·x) · a = p · (e·(q·y)) · ((x·p)·e) · q = p · e · e · q = a`,

so `y · x` is an inner inverse for `a`. -/
theorem isVonNeumannRegular_of_isRegularClass {a : M} (h : IsRegularClass a) :
    IsVonNeumannRegular a := by
  obtain ⟨e, he, hidem⟩ := isRegularClass_iff_exists_idem.1 h
  obtain ⟨x, y, hxy⟩ := mem_twoIdeal.1 (he ▸ self_mem_twoIdeal e)
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 (he.symm ▸ self_mem_twoIdeal a)
  have hsand : x * p * e * (q * y) = e := by
    calc x * p * e * (q * y) = x * (p * e * q) * y := by simp only [mul_assoc]
      _ = x * a * y := by rw [hpq]
      _ = e := hxy
  have hleft : x * p * e = e := sandwich_left hsand
  have hright : e * (q * y) = e := sandwich_right hsand
  refine ⟨y * x, ?_⟩
  calc a * (y * x) * a = p * (e * (q * y)) * (x * p * e) * q := by
        rw [← hpq]; simp only [mul_assoc]
    _ = p * e * e * q := by rw [hleft, hright]
    _ = p * e * q := by rw [mul_assoc p e e, hidem.eq]
    _ = a := hpq

/-- The class-wide form: a `J`-class is regular exactly when **all** of its
elements are. -/
theorem isRegularClass_iff_forall {a : M} :
    IsRegularClass a ↔ ∀ b : M, twoIdeal b = twoIdeal a → IsVonNeumannRegular b := by
  constructor
  · rintro ⟨c, hc, hcreg⟩ b hb
    exact isVonNeumannRegular_of_isRegularClass ⟨c, hc.trans hb.symm, hcreg⟩
  · intro h
    exact ⟨a, rfl, h a rfl⟩

/-- **A class meeting its own square is regular** — the null/regular
dichotomy, in the direction the kernel filtration consumes: if a product of
two elements of a `J`-class stays in the class, the class contains an
idempotent.  Stability turns `x·y J x` into `x R x·y`, so `x = x·(y·u)` for
some `u`; the idempotent power `e = (y·u)^N` then fixes `x` on the right,
which pins `twoIdeal e` to the class from both sides. -/
theorem isRegularClass_of_mul_mem {a x y : M} (hx : twoIdeal x = twoIdeal a)
    (hy : twoIdeal y = twoIdeal a) (hmul : twoIdeal (x * y) = twoIdeal a) :
    IsRegularClass a := by
  have hReq : REq (x * y) x :=
    rEq_of_twoIdeal_eq_of_rLe (hmul.trans hx.symm) (rLe_iff_exists.2 ⟨y, rfl⟩)
  have hreq' : rightIdeal (x * y) = rightIdeal x := hReq
  have hxmem : x ∈ rightIdeal (x * y) := by
    rw [hreq']; exact self_mem_rightIdeal x
  obtain ⟨u, hu⟩ := mem_rightIdeal.1 hxmem
  have hfix : x * (y * u) = x := by rw [← mul_assoc]; exact hu
  obtain ⟨N, hN, hidem⟩ := exists_idempotent_pow (y * u)
  have hfixpow : ∀ k : ℕ, x * (y * u) ^ k = x := by
    intro k
    induction k with
    | zero => rw [pow_zero, mul_one]
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hfix]
  refine isRegularClass_iff_exists_idem.2 ⟨(y * u) ^ N, ?_, hidem⟩
  refine Finset.Subset.antisymm ?_ ?_
  · calc twoIdeal ((y * u) ^ N) ⊆ twoIdeal (y * u) := twoIdeal_pow_subset hN
      _ ⊆ twoIdeal y := twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨u, rfl⟩)
      _ = twoIdeal a := hy
  · rw [← hx]
    exact twoIdeal_subset_of_mem
      (mem_twoIdeal.2 ⟨x, 1, by rw [mul_one]; exact hfixpow N⟩)

end Green

end MonoidProduct
