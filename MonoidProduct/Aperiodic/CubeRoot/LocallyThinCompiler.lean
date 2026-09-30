import MonoidProduct.Aperiodic.CubeRoot.LocallyThin
import QuantumQueryComplexity.Adaptive
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Compiling certificates through the dyadic recursion

The structural half of the square-zero lift is in `LocallyThin.lean`: the
category, local thinness, the cut path, and the counting.  What remains is the
query cost, and this file builds it.

**The horizon is sealed first.**  The recursion runs on a dyadic index range,
which is a power of two and so generally *longer* than the word.  The
hypothesis must never be consulted at that padded length: every query is the
`T`-image of a window of the **original** word, of length at most `ℓ`, and
`HasWordProdDualPoly` is instantiated there.  `hasDual_winImage` is that
statement and `hasDual_cutObj` is the only *quotient-product* query the
recursion makes — the two global contexts at a cut, jointly, at `2D√ℓ`.  It is
not the only query: an active leaf reads its raw letter, and must, since cut
objects alone do not determine the product.

Doing this before the transcript is deliberate.  A padded-horizon query would
type-check against a contract at horizon `2^L`, and the resulting bound would
be quietly wrong in a way no later step would catch; the clipped statement
cannot be written down at the wrong horizon at all.

**Then the search itself.**  The paper's proof of `lem:ags-square-zero-lift`
runs a dyadic recursion over a
frontier of active nodes; what is built here is that search *sequentialized*,
which meets the same bound with a flat state.  The compiler's only real job is
to find the **change set** — the cuts at which the path leaves its component —
because a run of cuts inside one component contributes a tabled arrow and a
crossing contributes its raw letter.  `sameComp_of_between` makes "still in the
boundary's component" antitone along the path, so each change point is found by
one binary search, and `changeSet_card_le` caps the number of searches at
`|T|² - 1`.  Fixed budget: `|T|²` rounds of `L + 3` levels, one cut query and one
raw read each.

The file then follows `FirstEntry`'s shape exactly — `conf` / `confOf` /
`conf_eq_confOf`, a structural `IsValid`, the semantic invariants
`InSearch` / `Resolved`, the padded trace, and one `postcomp_of_determined`
collapse — ending at `liftsWordProd_of_locallyThin`, the lift's endpoint.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace LocallyThin

/-! ## The horizon-safe query -/

section Query

variable {α S T : Type} [Fintype α] [DecidableEq α]
  [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T]

/-- A monoid hom commutes with the padded letter. -/
lemma map_padAt (φ : S →* T) {ℓ : ℕ} (w : Fin ℓ → S) (i : ℕ) :
    φ (padAt w i) = padAt (fun j => φ (w j)) i := by
  simp only [padAt]
  split
  · rfl
  · exact map_one φ

/-- A monoid hom commutes with interval products. -/
lemma map_rangeProd (φ : S →* T) {ℓ : ℕ} (w : Fin ℓ → S) (lo hi : ℕ) :
    φ (rangeProd w lo hi) = rangeProd (fun i => φ (w i)) lo hi := by
  simp only [rangeProd]
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun k _ => map_padAt φ w (lo + k)

/-- **The window query, at the clipped horizon.**  The image of the window
`[lo, lo + len)` of the input word, priced by the alphabet-uniform contract at
horizon `len`.

Two things are load-bearing in this signature.  `len ≤ ℓ ≤ n₀`: the contract is
consulted about a subword of the original word and never about the padded
dyadic range.  And the **input alphabet is an arbitrary `α`**, with a letter
map that need not be injective — which is what `HasWordProdDualPoly` actually
quantifies over, and which no `alphaMap` could transport to afterwards. -/
theorem hasDual_winImage (φ : S →* T) (letter : α → S) {n₀ : ℕ} {D : ℝ}
    (hPoly : HasWordProdDualPoly T n₀ D) {ℓ lo len : ℕ}
    (hwin : lo + len ≤ ℓ) (hℓ : ℓ ≤ n₀) :
    HasDual (fun x : Fin ℓ → α =>
        rangeProd (fun i => φ (letter (x i))) lo (lo + len))
      (D * Real.sqrt (len : ℝ)) := by
  refine (((hPoly.toUpTo (fun a : α => φ (letter a))).apply
    (le_trans (by omega : len ≤ ℓ) hℓ)).pullback
    (winEmb_injective hwin)).ofEq fun x => ?_
  rw [pullbackFun_apply]
  exact wordProd_winEmb (fun a : α => φ (letter a)) x hwin

/-- **The cut object is a pair of window images**, so both of its components
are horizon-safe. -/
lemma cutObj_eq (φ : S →* T) (letter : α → S) {ℓ : ℕ} (x : Fin ℓ → α) {m : ℕ}
    (hm : m ≤ ℓ) :
    cutObj φ (fun i => letter (x i)) m
      = (rangeProd (fun i => φ (letter (x i))) 0 (0 + m),
         rangeProd (fun i => φ (letter (x i))) m (m + (ℓ - m))) := by
  rw [show (0 : ℕ) + m = m from by omega, show m + (ℓ - m) = ℓ from by omega]
  simp only [cutObj]
  rw [map_rangeProd, map_rangeProd]

/-- **The only *quotient-product* query the recursion makes**: the two global
contexts at a cut, jointly, at `2D√ℓ`.

It is not the only query.  An active leaf must also read its raw letter — cut
objects alone do not determine the source product, and
`LocallyThinCalibration.cutObj_not_determining` exhibits two one-letter words
with identical cut objects and different products. -/
theorem hasDual_cutObj (φ : S →* T) (letter : α → S) {n₀ : ℕ} {D : ℝ}
    (hPoly : HasWordProdDualPoly T n₀ D) {ℓ : ℕ} (hℓ : ℓ ≤ n₀) {m : ℕ}
    (hm : m ≤ ℓ) :
    HasDual (fun x : Fin ℓ → α => cutObj φ (fun i => letter (x i)) m)
      (2 * D * Real.sqrt (ℓ : ℝ)) := by
  have hD0 : (0 : ℝ) ≤ D := hPoly.nonneg
  have h1 := hasDual_winImage φ letter hPoly (lo := 0) (len := m) (by omega) hℓ
  have h2 := hasDual_winImage φ letter hPoly (lo := m) (len := ℓ - m) (by omega) hℓ
  refine ((HasDual.adaptiveCall_const h1 h2).ofEq
    fun x => (cutObj_eq φ letter x hm).symm).mono ?_
  have hm1 : Real.sqrt (m : ℝ) ≤ Real.sqrt (ℓ : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hm)
  have hm2 : Real.sqrt ((ℓ - m : ℕ) : ℝ) ≤ Real.sqrt (ℓ : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le ℓ m)
  nlinarith [Real.sqrt_nonneg (m : ℝ), Real.sqrt_nonneg ((ℓ - m : ℕ) : ℝ)]

/-- **The active leaf's raw read**, at cost `2`.  This is the query the cut
objects cannot replace. -/
theorem hasDual_leaf (letter : α → S) {ℓ : ℕ} (a : Fin ℓ) :
    HasDual (fun x : Fin ℓ → α => letter (x a)) 2 :=
  hasDual_ofCoord a letter

/-- **The compiler's slot type**: a queried cut object and a **raw** letter,
jointly.  The letter is not decoration — without it a transcript cannot
determine the source product, so `HasDual.postcomp_of_determined` would have a
false determinacy hypothesis, and
`LocallyThinCalibration.cutObj_not_determining` is the machine-checked
counterexample.

A padded slot `Option ((T × T) ⊕ S)` holding *one* of the two would also
work.  Since every level is priced for both anyway — `slot_cost_le` — the slot
carries both, which removes the padding and the case split. -/
abbrev Slot (S T : Type) : Type := (T × T) × S

/-- **The per-slot cost**: one cut query plus one raw leaf read, folded into a
single bound.  `2` is absorbed by `2√ℓ` as soon as `ℓ ≥ 1`, which is why the
`D + 1` built into `thinStep` is exactly the room the raw leaf read needs. -/
lemma slot_cost_le (D : ℝ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    2 * D * Real.sqrt (ℓ : ℝ) + 2 ≤ 2 * (D + 1) * Real.sqrt (ℓ : ℝ) := by
  have h1 : (1 : ℝ) ≤ Real.sqrt (ℓ : ℝ) := by
    have hc : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (ℓ : ℝ) := Real.sqrt_le_sqrt hc
  nlinarith

/-! ### The dyadic depth

`2 ^ L ≥ ℓ` alone does **not** bound `L` by the horizon; minimality does.
Taking `Nat.clog` is what makes `L ≤ clog 2 (n₀ + 2)`, the form `thinStep` is
stated in. -/

/-- The dyadic depth: the least `L` with `2 ^ L ≥ ℓ`. -/
def dyadicDepth (ℓ : ℕ) : ℕ := Nat.clog 2 ℓ

lemma le_two_pow_dyadicDepth (ℓ : ℕ) : ℓ ≤ 2 ^ dyadicDepth ℓ :=
  Nat.le_pow_clog (by norm_num) ℓ

lemma dyadicDepth_le {ℓ n₀ : ℕ} (hℓ : ℓ ≤ n₀) :
    dyadicDepth ℓ ≤ Nat.clog 2 (n₀ + 2) :=
  Nat.clog_mono_right 2 (by omega)

end Query

/-! ## The node invariant

The recursion carries, at every node `[a, b)`, a decoded representative `u`
together with

    `IsArrow (cutObj a) (cutObj b) u  ∧  SameArrow … (segment a b) u`

— the arrow is correctly typed, and it acts like the real segment in every
compatible context.  There are exactly three ways a node establishes it, and
one way the root consumes it.  All four are here, so the recursion itself has
only bookkeeping left to do.

* `sameArrow_segment_tabled` — a node whose endpoints share a component needs
  no query: thinness pins the arrow to any correctly typed representative;
* `sameArrow_segment_comp` — an internal node composes its children, with the
  types threading through `IsArrow` on the right child;
* `sameArrow_segment_leaf` — a width-one active node *is* its letter;
* `rangeProd_eq_of_sameArrow_root` — at the root an identified arrow is the
  product itself.
-/

section NodeInvariant

variable {S T : Type} [Monoid S] [Monoid T] (φ : S →* T) {ℓ : ℕ} (x : Fin ℓ → S)

/-- **A tabled node.**  When the endpoints of `[a, b)` share a component, the
segment agrees with *any* correctly typed representative — so the recursion may
read one off the table instead of querying. -/
theorem sameArrow_segment_tabled (h : LocallyThinKernel φ) {a b : ℕ}
    (hab : a ≤ b) (hbn : b ≤ ℓ)
    (hcomp : SameComp φ (cutObj φ x a) (cutObj φ x b))
    {v : S} (hv : IsArrow φ (cutObj φ x a) (cutObj φ x b) v) :
    SameArrow φ (cutObj φ x a).1 (cutObj φ x b).2 (segment x a b) v := by
  obtain ⟨w, hw⟩ := hcomp.2
  exact SameArrow.of_thin h (isArrow_segment φ x hab hbn) hv hw

/-- **An internal node.**  Children compose: the types thread through the right
child's `IsArrow`, which is what turns `SameArrow.comp`'s bookkeeping into the
statement the recursion wants. -/
theorem sameArrow_segment_comp {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcn : c ≤ ℓ) {u v : S}
    (hvarr : IsArrow φ (cutObj φ x b) (cutObj φ x c) v)
    (h₁ : SameArrow φ (cutObj φ x a).1 (cutObj φ x b).2 (segment x a b) u)
    (h₂ : SameArrow φ (cutObj φ x b).1 (cutObj φ x c).2 (segment x b c) v) :
    SameArrow φ (cutObj φ x a).1 (cutObj φ x c).2 (segment x a c) (u * v) := by
  have harr := isArrow_segment φ x hab (le_trans hbc hcn)
  have h₁' : SameArrow φ (cutObj φ x a).1 (φ v * (cutObj φ x c).2)
      (segment x a b) u := by
    rw [hvarr.right]; exact h₁
  have h₂' : SameArrow φ ((cutObj φ x a).1 * φ (segment x a b))
      (cutObj φ x c).2 (segment x b c) v := by
    rw [harr.left]; exact h₂
  have hcomp := SameArrow.comp h₁' h₂'
  rwa [show segment x a b * segment x b c = segment x a c from
    rangeProd_split x hab hbc] at hcomp

/-- **An active leaf of width one is its own letter.**  This is where the
crossing letter enters, and it costs one coordinate read. -/
theorem sameArrow_segment_leaf {a : ℕ} (ha : a < ℓ) :
    SameArrow φ (cutObj φ x a).1 (cutObj φ x (a + 1)).2
      (segment x a (a + 1)) (x ⟨a, ha⟩) := by
  simp only [segment, rangeProd_singleton x ha]
  exact SameArrow.refl _ _ _

/-- **The root consumes the invariant.**  An identified arrow spanning the
whole word is the product itself — no component hypothesis needed, because at
the root `1` is a compatible lift on both sides. -/
theorem rangeProd_eq_of_sameArrow_root {v : S}
    (h : SameArrow φ (cutObj φ x 0).1 (cutObj φ x ℓ).2 (segment x 0 ℓ) v) :
    rangeProd x 0 ℓ = v := by
  rw [cutObj_zero_fst, cutObj_last_snd] at h
  exact eq_of_sameArrow_root h

end NodeInvariant

/-! ## The root seed

A seam that the active-node count does **not** fund.  Before the recursion can
test whether the root's endpoints share a component it has to know `φ` of the
whole product — the root objects are `(1, φ W)` and `(φ W, 1)`.  If the root
turns out to be tabled, `activeNodes` is *empty* and pays for nothing, so that
first piece of information has to be bought outright.

One cut buys it, and the same cut is the root's split when the root is active:
the two components of any cut object multiply to `φ W`.  The degenerate lengths
and the degenerate `T` are handled separately, and neither needs funding.
-/

section RootSeed

variable {α S T : Type} [Fintype α] [DecidableEq α]
  [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T]

/-- **One cut determines the whole quotient product.**  Its two components are
the images of complementary halves, so they multiply to `φ W`. -/
theorem cutObj_mul (φ : S →* T) {ℓ : ℕ} (w : Fin ℓ → S) {m : ℕ} (hm : m ≤ ℓ) :
    (cutObj φ w m).1 * (cutObj φ w m).2 = φ (rangeProd w 0 ℓ) := by
  simp only [cutObj]
  rw [← map_mul, rangeProd_split w (Nat.zero_le m) hm]

/-- **The root's source object, from any single cut.** -/
theorem cutObj_zero_eq (φ : S →* T) {ℓ : ℕ} (w : Fin ℓ → S) {m : ℕ} (hm : m ≤ ℓ) :
    cutObj φ w 0 = (1, (cutObj φ w m).1 * (cutObj φ w m).2) := by
  rw [cutObj_mul φ w hm]
  simp [cutObj]

/-- **The root's target object, from the same cut.**  So the unconditional
midpoint query seeds both endpoints at once. -/
theorem cutObj_last_eq (φ : S →* T) {ℓ : ℕ} (w : Fin ℓ → S) {m : ℕ} (hm : m ≤ ℓ) :
    cutObj φ w ℓ = ((cutObj φ w m).1 * (cutObj φ w m).2, 1) := by
  rw [cutObj_mul φ w hm]
  simp [cutObj]

/-! ### The degenerate cases, which need no funding -/

/-- **`ℓ = 1`: one raw read is the whole product** — and, through `φ`, its
quotient image too, so no cut query is needed at all. -/
theorem hasDual_rangeProd_one (letter : α → S) :
    HasDual (fun x : Fin 1 → α => rangeProd (fun i => letter (x i)) 0 1) 2 := by
  refine (hasDual_leaf letter (0 : Fin 1)).ofEq fun x => ?_
  exact (rangeProd_singleton (fun i => letter (x i)) (by norm_num)).symm

/-- **A trivial image forces a trivial source.**  This is the derived
`fibre_one` doing real work: with `T` subsingleton every `φ s = 1`, hence every
`s = 1`. -/
theorem subsingleton_of_subsingleton_cod {φ : S →* T} (h : LocallyThinKernel φ)
    [Subsingleton T] : Subsingleton S :=
  ⟨fun a b => by
    rw [h.fibre_one a (Subsingleton.elim _ _), h.fibre_one b (Subsingleton.elim _ _)]⟩

/-- **`K = 0`: the case the count cannot fund, and need not.**  `K = 0` means
`|T| = 1`, which makes `S` trivial, so the product is constant and free. -/
theorem hasDual_rangeProd_of_card_eq_one {φ : S →* T} (h : LocallyThinKernel φ)
    (hT : Fintype.card T = 1) (letter : α → S) {ℓ : ℕ} :
    HasDual (fun x : Fin ℓ → α => rangeProd (fun i => letter (x i)) 0 ℓ) 0 := by
  have : Subsingleton T := Fintype.card_le_one_iff_subsingleton.1 (le_of_eq hT)
  have : Subsingleton S := subsingleton_of_subsingleton_cod h
  exact hasDual_const fun x y => Subsingleton.elim _ _

/-- **The seed fits in the existing capacity.**  A nontrivial `T` gives
`K = |T|² - 1 ≥ 3`, so the root's unconditional cut occupies one of the `K`
slots the budget already pays for — no extra term is needed. -/
theorem three_le_slotCapacity (hT : 2 ≤ Fintype.card T) :
    3 ≤ Fintype.card (T × T) - 1 := by
  rw [Fintype.card_prod]
  have h4 : 4 ≤ Fintype.card T * Fintype.card T := Nat.mul_le_mul hT hT
  omega

end RootSeed

/-! ## The sequential search

The transcript.  The paper's proof runs a dyadic recursion over a frontier of
active nodes; the recursion implemented here is the same search *sequentialized*,
and it is materially simpler to state, to reconstruct and to price.

What the compiler has to find is the **change set**: the cuts at which the path
leaves its component.  Everything else is free — a run of cuts inside one
component contributes a tabled arrow (`sameArrow_segment_tabled`), and a
crossing contributes its raw letter (`sameArrow_segment_leaf`).  So the search
is: from the current boundary `p`, binary-search for the **last** cut still in
`p`'s component, take the tabled arrow up to it, read the crossing letter, and
repeat.  The predicate is monotone by `sameComp_of_between`, which is what makes
the binary search legal, and `changeSet_card_le` bounds the number of rounds.

The cost is the same `N^{O(1)} L(n)^{O(1)}` as the frontier version, with the two
exponents where `sum_activeNodes_card_le` put them: `|T|²` rounds of `L + 3`
levels, each level one cut query and one raw read.  What is gained is that the
recursion carries a **flat** state — one boundary, one bracket, one accumulator —
instead of a set of live nodes, so the reconstruction is `FirstEntry`'s
`conf`/`confOf` pattern verbatim rather than a new one.
-/

section Table

variable {S T : Type} [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T]

instance decidableIsArrow (φ : S →* T) (o o' : T × T) (s : S) :
    Decidable (IsArrow φ o o' s) :=
  decidable_of_iff (o.1 * φ s = o'.1 ∧ φ s * o'.2 = o.2)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.left, h.right⟩⟩

instance decidableReach (φ : S →* T) (o o' : T × T) : Decidable (Reach φ o o') :=
  decidable_of_iff (∃ s : S, IsArrow φ o o' s) Iff.rfl

instance decidableSameComp (φ : S →* T) (o o' : T × T) :
    Decidable (SameComp φ o o') :=
  decidable_of_iff (Reach φ o o' ∧ Reach φ o' o) Iff.rfl

/-- **The arrow table.**  A canonical representative of the arrows from `o` to
`o'`, chosen from the objects alone.  Inside a component thinness says every
arrow agrees with it in context (`sameArrow_segment_tabled`), so the compiler
may read it off instead of querying — which is the whole reason the change set
is the only thing the search has to find. -/
noncomputable def tableArrow (φ : S →* T) (o o' : T × T) : S :=
  if h : ∃ s : S, IsArrow φ o o' s then h.choose else 1

lemma isArrow_tableArrow {φ : S →* T} {o o' : T × T} (h : Reach φ o o') :
    IsArrow φ o o' (tableArrow φ o o') := by
  have h' : ∃ s : S, IsArrow φ o o' s := h
  rw [tableArrow, dif_pos h']
  exact h'.choose_spec

end Table

/-! ### The configuration and the step -/

/-- **The search configuration.**  `pos` is the resolved boundary — everything
to its left has been folded into `acc` — and `[lo, hi]` is the bracket of the
binary search for the last cut in `pos`'s component.  `objPos` and `objLo` cache
the two cut objects the step needs; both are re-queried, never inferred. -/
structure ThinConf (S T : Type) where
  /-- The resolved boundary. -/
  pos : ℕ
  /-- The bracket's low end, always in `pos`'s component. -/
  lo : ℕ
  /-- The bracket's high end. -/
  hi : ℕ
  /-- The cut object at `pos`. -/
  objPos : T × T
  /-- The cut object at `lo`. -/
  objLo : T × T
  /-- The arrow accumulated for `[0, pos)`. -/
  acc : S

namespace ThinConf

section Defs

variable {S T : Type} [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T]

/-- The bracket's midpoint, rounded **up** — rounding down would stall at
`hi = lo + 1`. -/
def midOf (c : ThinConf S T) : ℕ := (c.lo + c.hi + 1) / 2

/-- The initial configuration: nothing resolved, the bracket the whole word. -/
def initConf (ℓ : ℕ) : ThinConf S T := ⟨0, 0, ℓ, (1, 1), (1, 1), 1⟩

/-- **The cut the level queries.**  A round opens by re-reading the object at
its own boundary; every later level of the round reads the bracket's midpoint.
The finish level's cut answer is unused, and reading the midpoint there costs
nothing extra — every level is priced identically anyway. -/
def cutPos (L : ℕ) (c : ThinConf S T) (j : ℕ) : ℕ :=
  if j % (L + 3) = 0 then c.pos else midOf c

/-- **The letter the level reads**, clamped to a genuine position.  The finish
level of a round that ends at a crossing needs `lo`; every other level's read is
discarded. -/
def letIdx (ℓ : ℕ) (hℓ : 0 < ℓ) (c : ThinConf S T) : Fin ℓ :=
  ⟨min c.lo (ℓ - 1), lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

lemma letIdx_val {ℓ : ℕ} (hℓ : 0 < ℓ) {c : ThinConf S T} (h : c.lo < ℓ) :
    ((letIdx ℓ hℓ c : Fin ℓ) : ℕ) = c.lo := by
  simp only [letIdx]
  omega

/-- **What a closing round contributes**: the tabled arrow of the run from the
round's boundary to the collapsed bracket point.  A round that ends at a genuine
crossing multiplies the crossing letter on afterwards. -/
noncomputable def closeAcc (φ : S →* T) (c : ThinConf S T) : S :=
  c.acc * tableArrow φ c.objPos c.objLo

/-- **The step, read off the level record.**  Three phases inside a round of
`L + 3` levels: open the round at its boundary, run `L + 1` bisections, then
close — taking the tabled arrow up to the bracket's now-collapsed point and, if
that point is a genuine crossing, the raw letter that crosses.

The bisection branches on `SameComp objPos b.1`, the *component* test between
the round's boundary and the queried midpoint — not on any property of the
midpoint alone.  A round whose boundary is already the end of the word is a
no-op, which is what lets the level count be a fixed multiple of `|T|²`. -/
noncomputable def step (φ : S →* T) (ℓ L : ℕ) (j : ℕ) (c : ThinConf S T)
    (b : Slot S T) : ThinConf S T :=
  if j % (L + 3) = 0 then
    { pos := c.pos, lo := c.pos, hi := ℓ, objPos := b.1, objLo := b.1, acc := c.acc }
  else if j % (L + 3) ≤ L + 1 then
    if c.lo = c.hi then c
    else if SameComp φ c.objPos b.1 then { c with lo := midOf c, objLo := b.1 }
    else { c with hi := midOf c - 1 }
  else
    if c.pos = ℓ then c
    else if c.lo = ℓ then { c with pos := ℓ, acc := closeAcc φ c }
    else { c with pos := c.lo + 1, acc := closeAcc φ c * b.2 }

/-- The round a level belongs to is `j / (L + 3)`, and its phase `j % (L + 3)`. -/
lemma mod_round (L t r : ℕ) (hr : r < L + 3) : (t * (L + 3) + r) % (L + 3) = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt hr

end Defs

/-! ### The structural interval invariant

Every reconstructed configuration satisfies it, promise or not: the branch
family of `HasDual.adaptiveCall` is indexed by all trace values, so the query
positions must be legal at every one of them. -/

section Valid

variable {S T : Type} [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T] {φ : S →* T} {ℓ L : ℕ}

/-- The interval invariant. -/
structure IsValid (ℓ : ℕ) (c : ThinConf S T) : Prop where
  /-- The boundary is a cut of the word. -/
  pos_le : c.pos ≤ ℓ
  /-- The bracket is not inverted. -/
  lo_le_hi : c.lo ≤ c.hi
  /-- The bracket stays inside the word. -/
  hi_le : c.hi ≤ ℓ

theorem isValid_step {c : ThinConf S T} (h : IsValid ℓ c) (j : ℕ)
    (b : Slot S T) : IsValid ℓ (step φ ℓ L j c b) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [step, midOf]
  split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> · (try dsimp only); omega

/-! #### The three phases, as rewriting rules

Every later proof branches on the phase, so the `if`-tower is unfolded once and
never again. -/

/-- Level `0` of a round re-reads the object at the round's own boundary and
opens the bracket on the whole remaining word. -/
lemma step_of_mod_zero {j : ℕ} (hj : j % (L + 3) = 0) (c : ThinConf S T)
    (b : Slot S T) :
    step φ ℓ L j c b =
      { pos := c.pos, lo := c.pos, hi := ℓ, objPos := b.1, objLo := b.1,
        acc := c.acc } := by
  simp only [step, if_pos hj]

/-- Levels `1` through `L + 1` bisect. -/
lemma step_of_search {j : ℕ} (hj0 : j % (L + 3) ≠ 0) (hj1 : j % (L + 3) ≤ L + 1)
    (c : ThinConf S T) (b : Slot S T) :
    step φ ℓ L j c b =
      if c.lo = c.hi then c
      else if SameComp φ c.objPos b.1 then { c with lo := midOf c, objLo := b.1 }
      else { c with hi := midOf c - 1 } := by
  simp only [step, if_neg hj0, if_pos hj1]

/-- Level `L + 2` closes the round. -/
lemma step_of_finish {j : ℕ} (hj0 : j % (L + 3) ≠ 0) (hj1 : ¬ j % (L + 3) ≤ L + 1)
    (c : ThinConf S T) (b : Slot S T) :
    step φ ℓ L j c b =
      if c.pos = ℓ then c
      else if c.lo = ℓ then { c with pos := ℓ, acc := closeAcc φ c }
      else { c with pos := c.lo + 1, acc := closeAcc φ c * b.2 } := by
  simp only [step, if_neg hj0, if_neg hj1]

/-- The bracket's width — the search's measure. -/
def gap (c : ThinConf S T) : ℕ := c.hi - c.lo

/-- **A bisection at least halves the bracket.**  What halves is the bracket,
not the queried length: a cut query reads two windows whose lengths add up to
the whole word however deep the search has gone, which is why the level cost is
uniform and the level *count* is what the budget pays for. -/
theorem gap_step_search {c : ThinConf S T} (h : IsValid ℓ c) {j : ℕ}
    (hj0 : j % (L + 3) ≠ 0) (hj1 : j % (L + 3) ≤ L + 1) (b : Slot S T) :
    gap (step φ ℓ L j c b) ≤ gap c / 2 := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [step_of_search hj0 hj1]
  simp only [gap, midOf]
  split_ifs <;> · (try dsimp only); omega

/-- **The queried cut is a cut of the word**, at every configuration the
invariant holds at — which is every reconstructed one. -/
theorem cutPos_le {c : ThinConf S T} (h : IsValid ℓ c) (j : ℕ) :
    cutPos L c j ≤ ℓ := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [cutPos, midOf]
  split_ifs <;> omega

end Valid

end ThinConf


/-! ### The run, and its reconstruction

`FirstEntry`'s pattern verbatim: the search is defined once on the word and
once on a supplied record sequence, and `conf_eq_confOf` says the two agree as
far as the records do.  That is what turns each level into a *total* dual
restricted to a fiber. -/

namespace ThinConf

section Run

variable {α S T : Type} [Fintype α] [DecidableEq α]
  [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T]

/-- **The level record**: the queried cut object and the letter read, jointly.
Every level pays for both — the cut answer is discarded at a closing level and
the letter at every other one — which is what keeps the per-level cost
uniform. -/
noncomputable def recOf (φ : S →* T) (letter : α → S) {ℓ : ℕ} (hℓ : 0 < ℓ) (L : ℕ)
    (x : Fin ℓ → α) (c : ThinConf S T) (j : ℕ) : Slot S T :=
  (cutObj φ (fun i => letter (x i)) (cutPos L c j), letter (x (letIdx ℓ hℓ c)))

/-- The configuration after `j` levels of the search on the word `x`. -/
noncomputable def conf (φ : S →* T) (letter : α → S) {ℓ : ℕ} (hℓ : 0 < ℓ) (L : ℕ)
    (x : Fin ℓ → α) : ℕ → ThinConf S T
  | 0 => initConf ℓ
  | j + 1 =>
      step φ ℓ L j (conf φ letter hℓ L x j)
        (recOf φ letter hℓ L x (conf φ letter hℓ L x j) j)

/-- The record at level `j`. -/
noncomputable def levelAt (φ : S →* T) (letter : α → S) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (L : ℕ) (x : Fin ℓ → α) (j : ℕ) : Slot S T :=
  recOf φ letter hℓ L x (conf φ letter hℓ L x j) j

variable (φ : S →* T) (letter : α → S) {ℓ : ℕ} (hℓ : 0 < ℓ) (L : ℕ)
  (x : Fin ℓ → α)

@[simp] lemma conf_zero : conf φ letter hℓ L x 0 = initConf ℓ := rfl

lemma conf_succ (j : ℕ) :
    conf φ letter hℓ L x (j + 1)
      = step φ ℓ L j (conf φ letter hℓ L x j) (levelAt φ letter hℓ L x j) := rfl

/-- **The reconstruction**: the same recursion run on a supplied record sequence
instead of on the word. -/
noncomputable def confOf (φ : S →* T) (ℓ L : ℕ) (t : ℕ → Slot S T) :
    ℕ → ThinConf S T
  | 0 => initConf ℓ
  | j + 1 => step φ ℓ L j (confOf φ ℓ L t j) (t j)

@[simp] lemma confOf_zero (ℓ L : ℕ) (t : ℕ → Slot S T) :
    confOf φ ℓ L t 0 = initConf ℓ := rfl

lemma confOf_succ (ℓ L : ℕ) (t : ℕ → Slot S T) (j : ℕ) :
    confOf φ ℓ L t (j + 1) = step φ ℓ L j (confOf φ ℓ L t j) (t j) := rfl

/-- **Determinism.**  The configuration after `j` levels is a function of the
first `j` records — no further access to the word. -/
theorem conf_eq_confOf (t : ℕ → Slot S T) (j : ℕ)
    (ht : ∀ i, i < j → levelAt φ letter hℓ L x i = t i) :
    conf φ letter hℓ L x j = confOf φ ℓ L t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hprev := ih fun i hi => ht i (by omega)
      have hj := ht j (Nat.lt_succ_self j)
      rw [levelAt, hprev] at hj
      rw [conf_succ, confOf_succ, hprev, levelAt, hprev, hj]

/-! #### The structural invariant, and the search's termination -/

theorem isValid_confOf (ℓ L : ℕ) (t : ℕ → Slot S T) (j : ℕ) :
    IsValid ℓ (confOf φ ℓ L t j) := by
  induction j with
  | zero => exact ⟨Nat.zero_le ℓ, Nat.zero_le ℓ, le_rfl⟩
  | succ j ih => exact isValid_step ih j (t j)

theorem isValid_conf (j : ℕ) : IsValid ℓ (conf φ letter hℓ L x j) := by
  rw [conf_eq_confOf φ letter hℓ L x (levelAt φ letter hℓ L x) j fun i _ => rfl]
  exact isValid_confOf φ ℓ L _ j

lemma mod_round_zero (L t : ℕ) : (t * (L + 3)) % (L + 3) = 0 := Nat.mul_mod_left t (L + 3)

/-- **The bracket is empty by the closing level.**  A round opens its bracket at
width at most `ℓ ≤ 2 ^ L` and bisects `L + 1` times, so `2 ^ L / 2 ^ (L+1) = 0`
levels before the close — which is why `L + 3` levels per round suffice and the
horizon may be taken as `Nat.clog`. -/
theorem gap_confOf_search {ℓ L : ℕ} (hL : ℓ ≤ 2 ^ L) (t : ℕ → Slot S T)
    (r : ℕ) : ∀ k, k ≤ L + 1 →
      gap (confOf φ ℓ L t (r * (L + 3) + 1 + k)) ≤ 2 ^ L / 2 ^ k := by
  intro k
  induction k with
  | zero =>
      intro _
      have hv := (isValid_confOf φ ℓ L t (r * (L + 3))).pos_le
      rw [show r * (L + 3) + 1 + 0 = r * (L + 3) + 1 from rfl, confOf_succ,
        step_of_mod_zero (mod_round_zero L r)]
      simp only [pow_zero, Nat.div_one, gap]
      omega
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hmod : (r * (L + 3) + 1 + k) % (L + 3) = k + 1 := by
        rw [show r * (L + 3) + 1 + k = r * (L + 3) + (k + 1) from by omega]
        exact mod_round L r (k + 1) (by omega)
      rw [show r * (L + 3) + 1 + (k + 1) = (r * (L + 3) + 1 + k) + 1 from by omega,
        confOf_succ]
      refine le_trans (gap_step_search (isValid_confOf φ ℓ L t _)
        (by rw [hmod]; omega) (by rw [hmod]; omega) _) ?_
      calc gap (confOf φ ℓ L t (r * (L + 3) + 1 + k)) / 2 ≤ 2 ^ L / 2 ^ k / 2 :=
            Nat.div_le_div_right hprev
        _ = 2 ^ L / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ]

/-- **At a closing level the bracket has collapsed to a point.** -/
theorem lo_eq_hi_finish {ℓ L : ℕ} (hL : ℓ ≤ 2 ^ L) (t : ℕ → Slot S T) (r : ℕ) :
    (confOf φ ℓ L t (r * (L + 3) + (L + 2))).lo
      = (confOf φ ℓ L t (r * (L + 3) + (L + 2))).hi := by
  have hg := gap_confOf_search φ hL t r (L + 1) le_rfl
  rw [show r * (L + 3) + 1 + (L + 1) = r * (L + 3) + (L + 2) from by omega] at hg
  have hpos : 0 < 2 ^ L := pow_pos (by norm_num) L
  have hz : 2 ^ L / 2 ^ (L + 1) = 0 := Nat.div_eq_of_lt (by rw [pow_succ]; omega)
  rw [hz] at hg
  have hv := (isValid_confOf φ ℓ L t (r * (L + 3) + (L + 2))).lo_le_hi
  simp only [gap] at hg
  omega

end Run

end ThinConf


/-! ### What the search means

Two invariants.  `InSearch` is the bracket's: the round's boundary and the
bracket's low end lie in one component, and nothing above the bracket does.
`Resolved` is the accumulator's, and it is the dyadic recursion's node invariant read on a
prefix — a correctly typed arrow that agrees with the real prefix product *in
context*.  Only at the very end, where both contexts are trivial, does an
identified arrow become an equal element (`rangeProd_eq_of_sameArrow_root`),
which is why the accumulator is never claimed to equal a partial product. -/

namespace ThinConf

section Semantics

variable {S T : Type} [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T]

/-- **The bracket invariant.**  The low end is still in the boundary's
component, and every cut above the bracket has already left it — so the last
cut in the component lies in `[lo, hi]`. -/
structure InSearch (φ : S →* T) {ℓ : ℕ} (w : Fin ℓ → S) (c : ThinConf S T) : Prop where
  /-- The bracket starts at the boundary. -/
  pos_le_lo : c.pos ≤ c.lo
  /-- The cached boundary object is the real one. -/
  objPos_eq : c.objPos = cutObj φ w c.pos
  /-- The cached low object is the real one. -/
  objLo_eq : c.objLo = cutObj φ w c.lo
  /-- The low end is in the boundary's component. -/
  same_lo : SameComp φ (cutObj φ w c.pos) (cutObj φ w c.lo)
  /-- Nothing above the bracket is. -/
  none_above : ∀ k, c.hi < k → k ≤ ℓ →
    ¬ SameComp φ (cutObj φ w c.pos) (cutObj φ w k)

/-- **The accumulator invariant**: a correctly typed arrow that agrees with the
resolved prefix in every compatible context. -/
structure Resolved (φ : S →* T) {ℓ : ℕ} (w : Fin ℓ → S) (c : ThinConf S T) : Prop where
  /-- The accumulator is typed as an arrow from the root object. -/
  arr : IsArrow φ (cutObj φ w 0) (cutObj φ w c.pos) c.acc
  /-- And it is the prefix's arrow. -/
  same : SameArrow φ (cutObj φ w 0).1 (cutObj φ w c.pos).2 (segment w 0 c.pos) c.acc

variable {φ : S →* T} {ℓ L : ℕ} {w : Fin ℓ → S}

theorem resolved_initConf : Resolved φ w (initConf ℓ : ThinConf S T) := by
  refine ⟨isArrow_one _, ?_⟩
  simp only [initConf, segment, rangeProd_self]
  exact SameArrow.refl _ _ _

/-! #### The three phases, semantically -/

lemma cutPos_of_mod_zero {c : ThinConf S T} {j : ℕ} (hj : j % (L + 3) = 0) :
    cutPos L c j = c.pos := by simp only [cutPos, if_pos hj]

lemma cutPos_of_mod_ne {c : ThinConf S T} {j : ℕ} (hj : j % (L + 3) ≠ 0) :
    cutPos L c j = midOf c := by simp only [cutPos, if_neg hj]

/-- Opening a round establishes the bracket invariant: the bracket is the whole
remaining word, so nothing lies above it. -/
theorem inSearch_step_phase0 {c : ThinConf S T} {j : ℕ} (hj : j % (L + 3) = 0)
    {b : Slot S T} (hb : b.1 = cutObj φ w c.pos) :
    InSearch φ w (step φ ℓ L j c b) := by
  rw [step_of_mod_zero hj]
  refine ⟨le_rfl, hb, hb, SameComp.refl _, fun k hk hkl => absurd hkl ?_⟩
  dsimp only at hk
  omega

/-- Opening a round moves neither the boundary nor the accumulator. -/
theorem resolved_step_phase0 {c : ThinConf S T} (hres : Resolved φ w c) {j : ℕ}
    (hj : j % (L + 3) = 0) (b : Slot S T) :
    Resolved φ w (step φ ℓ L j c b) := by
  rw [step_of_mod_zero hj]
  exact ⟨hres.arr, hres.same⟩

/-- **A bisection preserves the bracket invariant.**  The `SameComp` branch is
what the invariant records; the other branch uses `sameComp_of_between`, the
interval property, to push the failure up past the whole discarded half. -/
theorem inSearch_step_search {c : ThinConf S T} (hval : IsValid ℓ c)
    (hin : InSearch φ w c) {j : ℕ} (hj0 : j % (L + 3) ≠ 0) (hj1 : j % (L + 3) ≤ L + 1)
    {b : Slot S T} (hb : b.1 = cutObj φ w (midOf c)) :
    InSearch φ w (step φ ℓ L j c b) := by
  obtain ⟨hp, hop, hol, hsame, hnone⟩ := hin
  obtain ⟨v1, v2, v3⟩ := hval
  rw [step_of_search hj0 hj1]
  split_ifs with h1 h2
  · exact ⟨hp, hop, hol, hsame, hnone⟩
  · rw [hop, hb] at h2
    refine ⟨?_, hop, hb, h2, hnone⟩
    simp only [midOf]
    omega
  · refine ⟨hp, hop, hol, hsame, ?_⟩
    dsimp only
    intro k hk hkl hc
    refine h2 ?_
    rw [hop, hb]
    refine sameComp_of_between φ w (by simp only [midOf] at *; omega)
      (by simp only [midOf] at *; omega) hkl hc
  
/-- **A closing round extends the resolved prefix.**  The tabled arrow runs from
the boundary to the collapsed bracket point — legal because the two share a
component — and, when that point is a genuine crossing, the raw letter carries
one step further.  Both compositions are `sameArrow_segment_comp`. -/
theorem resolved_step_finish (h : LocallyThinKernel φ) {c : ThinConf S T}
    (hval : IsValid ℓ c) (hin : InSearch φ w c) (hres : Resolved φ w c)
    {j : ℕ} (hj0 : j % (L + 3) ≠ 0)
    (hj1 : ¬ j % (L + 3) ≤ L + 1) {b : Slot S T}
    (hb : ∀ hlt : c.lo < ℓ, b.2 = w ⟨c.lo, hlt⟩) :
    Resolved φ w (step φ ℓ L j c b) := by
  have hlo : c.lo ≤ ℓ := le_trans hval.lo_le_hi hval.hi_le
  have hreach : Reach φ (cutObj φ w c.pos) (cutObj φ w c.lo) := hin.same_lo.1
  set v : S := tableArrow φ (cutObj φ w c.pos) (cutObj φ w c.lo) with hv
  have hvarr : IsArrow φ (cutObj φ w c.pos) (cutObj φ w c.lo) v :=
    isArrow_tableArrow hreach
  have htab : SameArrow φ (cutObj φ w c.pos).1 (cutObj φ w c.lo).2
      (segment w c.pos c.lo) v :=
    sameArrow_segment_tabled φ w h hin.pos_le_lo hlo hin.same_lo hvarr
  have hacc : closeAcc φ c = c.acc * v := by
    rw [closeAcc, hin.objPos_eq, hin.objLo_eq]
  have hstep1 : SameArrow φ (cutObj φ w 0).1 (cutObj φ w c.lo).2
      (segment w 0 c.lo) (c.acc * v) :=
    sameArrow_segment_comp φ w (Nat.zero_le _) hin.pos_le_lo hlo hvarr hres.same htab
  have harr1 : IsArrow φ (cutObj φ w 0) (cutObj φ w c.lo) (c.acc * v) :=
    hres.arr.comp hvarr
  rw [step_of_finish hj0 hj1]
  split_ifs with h1 h2
  · exact hres
  · rw [h2] at harr1 hstep1
    refine ⟨?_, ?_⟩ <;> dsimp only <;> rw [hacc]
    · exact harr1
    · exact hstep1
  · have hlt : c.lo < ℓ := lt_of_le_of_ne hlo h2
    have hleaf : IsArrow φ (cutObj φ w c.lo) (cutObj φ w (c.lo + 1)) (w ⟨c.lo, hlt⟩) := by
      have := isArrow_segment φ w (Nat.le_succ c.lo) hlt
      rwa [segment, rangeProd_singleton w hlt] at this
    have hleafs : SameArrow φ (cutObj φ w c.lo).1 (cutObj φ w (c.lo + 1)).2
        (segment w c.lo (c.lo + 1)) (w ⟨c.lo, hlt⟩) := sameArrow_segment_leaf φ w hlt
    refine ⟨?_, ?_⟩ <;> dsimp only <;> rw [hacc, hb hlt]
    · exact harr1.comp hleaf
    · exact sameArrow_segment_comp φ w (Nat.zero_le _) (Nat.le_succ c.lo) hlt
        hleaf hstep1 hleafs

/-- A bisection moves neither the boundary nor the accumulator. -/
theorem resolved_step_search {c : ThinConf S T} (hres : Resolved φ w c) {j : ℕ}
    (hj0 : j % (L + 3) ≠ 0) (hj1 : j % (L + 3) ≤ L + 1) (b : Slot S T) :
    Resolved φ w (step φ ℓ L j c b) := by
  rw [step_of_search hj0 hj1]
  split_ifs <;> exact ⟨hres.arr, hres.same⟩

lemma step_pos_phase0 {c : ThinConf S T} {j : ℕ} (hj : j % (L + 3) = 0)
    (b : Slot S T) : (step φ ℓ L j c b).pos = c.pos := by
  rw [step_of_mod_zero hj]

lemma step_pos_search {c : ThinConf S T} {j : ℕ} (hj0 : j % (L + 3) ≠ 0)
    (hj1 : j % (L + 3) ≤ L + 1) (b : Slot S T) :
    (step φ ℓ L j c b).pos = c.pos := by
  rw [step_of_search hj0 hj1]
  split_ifs <;> rfl

/-- **A closing round either finishes the word or consumes a change point.**
The consumed point is `lo`: it is in the boundary's component while `lo + 1` is
not, so the component changes exactly there. -/
theorem finish_progress {c : ThinConf S T} (hval : IsValid ℓ c)
    (hin : InSearch φ w c) (hcol : c.lo = c.hi) {j : ℕ} (hj0 : j % (L + 3) ≠ 0)
    (hj1 : ¬ j % (L + 3) ≤ L + 1) (b : Slot S T) :
    (step φ ℓ L j c b).pos = ℓ
      ∨ (c.lo ∈ changeSet φ w ∧ c.pos ≤ c.lo
          ∧ (step φ ℓ L j c b).pos = c.lo + 1) := by
  have hlo : c.lo ≤ ℓ := le_trans hval.lo_le_hi hval.hi_le
  rw [step_of_finish hj0 hj1]
  split_ifs with h1 h2
  · exact Or.inl (by rw [h1])
  · exact Or.inl rfl
  · have hlt : c.lo < ℓ := lt_of_le_of_ne hlo h2
    refine Or.inr ⟨(mem_changeSet φ w).2 ⟨hlt, fun hc => ?_⟩, hin.pos_le_lo, rfl⟩
    exact hin.none_above (c.lo + 1) (by omega) (by omega) (hin.same_lo.trans hc)

/-- **`pos = ℓ` is absorbing.**  Once the word is resolved every later level is
a no-op, which is what lets the level count be a fixed multiple of `|T|²`
instead of tracking how many rounds were actually needed. -/
theorem step_pos_eq_of_eq {c : ThinConf S T} (hc : c.pos = ℓ) (j : ℕ)
    (b : Slot S T) : (step φ ℓ L j c b).pos = ℓ := by
  simp only [step]
  split_ifs <;> · (try dsimp only); omega

end Semantics

end ThinConf


/-! ### The rounds, and what the whole run computes

`|T|²` rounds of `L + 3` levels.  The count is `changeSet_card_le` read as a
budget: a round that does not finish the word consumes a change point, and there
are fewer change points than objects.  Every later round is then a no-op, which
is why a *fixed* level count works and the compiler never has to know how many
rounds were actually needed. -/

namespace ThinConf

section Rounds

variable {α S T : Type} [Fintype α] [DecidableEq α]
  [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T]

variable (φ : S →* T) (letter : α → S) {ℓ : ℕ} (hℓ : 0 < ℓ) (L : ℕ)
  (x : Fin ℓ → α)

lemma levelAt_fst (j : ℕ) :
    (levelAt φ letter hℓ L x j).1
      = cutObj φ (fun i => letter (x i)) (cutPos L (conf φ letter hℓ L x j) j) := rfl

lemma levelAt_snd (j : ℕ) :
    (levelAt φ letter hℓ L x j).2
      = letter (x (letIdx ℓ hℓ (conf φ letter hℓ L x j))) := rfl

/-- **The body of a round**: open the bracket, then bisect `L + 1` times.  The
boundary and the accumulator do not move, and the bracket invariant holds
throughout. -/
theorem round_search (r : ℕ)
    (hres : Resolved φ (fun i => letter (x i)) (conf φ letter hℓ L x (r * (L + 3)))) :
    ∀ k, k ≤ L + 1 →
      InSearch φ (fun i => letter (x i)) (conf φ letter hℓ L x (r * (L + 3) + 1 + k))
        ∧ Resolved φ (fun i => letter (x i))
            (conf φ letter hℓ L x (r * (L + 3) + 1 + k))
        ∧ (conf φ letter hℓ L x (r * (L + 3) + 1 + k)).pos
            = (conf φ letter hℓ L x (r * (L + 3))).pos := by
  intro k
  induction k with
  | zero =>
      intro _
      have hz := mod_round_zero L r
      rw [show r * (L + 3) + 1 + 0 = r * (L + 3) + 1 from rfl, conf_succ]
      refine ⟨inSearch_step_phase0 hz ?_, resolved_step_phase0 hres hz _,
        step_pos_phase0 hz _⟩
      rw [levelAt_fst, cutPos_of_mod_zero hz]
  | succ k ih =>
      intro hk
      obtain ⟨hin, hre, hpos⟩ := ih (by omega)
      have hmod : (r * (L + 3) + 1 + k) % (L + 3) = k + 1 := by
        rw [show r * (L + 3) + 1 + k = r * (L + 3) + (k + 1) from by omega]
        exact mod_round L r (k + 1) (by omega)
      have hne : (r * (L + 3) + 1 + k) % (L + 3) ≠ 0 := by rw [hmod]; omega
      have hle : (r * (L + 3) + 1 + k) % (L + 3) ≤ L + 1 := by rw [hmod]; omega
      rw [show r * (L + 3) + 1 + (k + 1) = (r * (L + 3) + 1 + k) + 1 from by omega,
        conf_succ]
      refine ⟨inSearch_step_search (isValid_conf φ letter hℓ L x _) hin hne hle ?_,
        resolved_step_search hre hne hle _, ?_⟩
      · rw [levelAt_fst, cutPos_of_mod_ne hne]
      · rw [step_pos_search hne hle, hpos]

/-- **One round.**  Either it finishes the word, or it consumes a change point
at or after the round's own boundary. -/
theorem round_step (h : LocallyThinKernel φ) (hL : ℓ ≤ 2 ^ L) (r : ℕ)
    (hres : Resolved φ (fun i => letter (x i)) (conf φ letter hℓ L x (r * (L + 3)))) :
    Resolved φ (fun i => letter (x i)) (conf φ letter hℓ L x ((r + 1) * (L + 3)))
      ∧ ((conf φ letter hℓ L x ((r + 1) * (L + 3))).pos = ℓ
         ∨ ∃ q, q ∈ changeSet φ (fun i => letter (x i))
              ∧ (conf φ letter hℓ L x (r * (L + 3))).pos ≤ q
              ∧ (conf φ letter hℓ L x ((r + 1) * (L + 3))).pos = q + 1) := by
  obtain ⟨hin, hre, hpos⟩ := round_search φ letter hℓ L x r hres (L + 1) le_rfl
  rw [show r * (L + 3) + 1 + (L + 1) = r * (L + 3) + (L + 2) from by omega]
    at hin hre hpos
  have hcol : (conf φ letter hℓ L x (r * (L + 3) + (L + 2))).lo
      = (conf φ letter hℓ L x (r * (L + 3) + (L + 2))).hi := by
    rw [conf_eq_confOf φ letter hℓ L x (levelAt φ letter hℓ L x) _ fun i _ => rfl]
    exact lo_eq_hi_finish φ hL _ r
  have hmod : (r * (L + 3) + (L + 2)) % (L + 3) = L + 2 :=
    mod_round L r (L + 2) (by omega)
  have hne : (r * (L + 3) + (L + 2)) % (L + 3) ≠ 0 := by rw [hmod]; omega
  have hnle : ¬ (r * (L + 3) + (L + 2)) % (L + 3) ≤ L + 1 := by rw [hmod]; omega
  have hb : ∀ hlt : (conf φ letter hℓ L x (r * (L + 3) + (L + 2))).lo < ℓ,
      (levelAt φ letter hℓ L x (r * (L + 3) + (L + 2))).2
        = letter (x ⟨(conf φ letter hℓ L x (r * (L + 3) + (L + 2))).lo, hlt⟩) := by
    intro hlt
    have hidx : letIdx ℓ hℓ (conf φ letter hℓ L x (r * (L + 3) + (L + 2)))
        = ⟨(conf φ letter hℓ L x (r * (L + 3) + (L + 2))).lo, hlt⟩ :=
      Fin.val_injective (letIdx_val hℓ hlt)
    rw [levelAt_snd, hidx]
  rw [show (r + 1) * (L + 3) = (r * (L + 3) + (L + 2)) + 1 from by ring,
    conf_succ]
  refine ⟨resolved_step_finish h (isValid_conf φ letter hℓ L x _) hin hre hne hnle hb,
    ?_⟩
  rcases finish_progress (isValid_conf φ letter hℓ L x _) hin hcol hne hnle
    (levelAt φ letter hℓ L x (r * (L + 3) + (L + 2))) with hfin | ⟨hmem, hple, heq⟩
  · exact Or.inl hfin
  · exact Or.inr ⟨_, hmem, by rw [← hpos]; exact hple, heq⟩

/-- **`pos = ℓ` is absorbing along the run.** -/
theorem pos_eq_of_pos_eq {j : ℕ} (hj : (conf φ letter hℓ L x j).pos = ℓ) :
    ∀ k, (conf φ letter hℓ L x (j + k)).pos = ℓ := by
  intro k
  induction k with
  | zero => exact hj
  | succ k ih =>
      rw [show j + (k + 1) = (j + k) + 1 from by omega, conf_succ]
      exact step_pos_eq_of_eq ih _ _

/-- **The round budget.**  After `r` rounds either the word is resolved, or `r`
change points lie strictly below the boundary — so `|T|²` rounds is more than
enough, since there are at most `|T|² - 1` change points in all. -/
theorem run_rounds (h : LocallyThinKernel φ) (hL : ℓ ≤ 2 ^ L) : ∀ r : ℕ,
    Resolved φ (fun i => letter (x i)) (conf φ letter hℓ L x (r * (L + 3)))
      ∧ ((conf φ letter hℓ L x (r * (L + 3))).pos = ℓ
         ∨ r ≤ ((changeSet φ (fun i => letter (x i))).filter
              (· < (conf φ letter hℓ L x (r * (L + 3))).pos)).card) := by
  intro r
  induction r with
  | zero =>
      refine ⟨?_, Or.inr (Nat.zero_le _)⟩
      rw [Nat.zero_mul]
      exact resolved_initConf
  | succ r ih =>
      obtain ⟨hres, hprog⟩ := ih
      obtain ⟨hres', hstep⟩ := round_step φ letter hℓ L x h hL r hres
      refine ⟨hres', ?_⟩
      rcases hstep with hfin | ⟨q, hmem, hple, heq⟩
      · exact Or.inl hfin
      · have hqlt : q < ℓ := ((mem_changeSet φ _).1 hmem).1
        have hposr : (conf φ letter hℓ L x (r * (L + 3))).pos ≠ ℓ := by
          intro hc; omega
        have hr : r ≤ ((changeSet φ (fun i => letter (x i))).filter
            (· < (conf φ letter hℓ L x (r * (L + 3))).pos)).card :=
          hprog.resolve_left hposr
        refine Or.inr (le_trans (Nat.succ_le_succ hr) ?_)
        have hss : (changeSet φ (fun i => letter (x i))).filter
              (· < (conf φ letter hℓ L x (r * (L + 3))).pos)
            ⊂ (changeSet φ (fun i => letter (x i))).filter
              (· < (conf φ letter hℓ L x ((r + 1) * (L + 3))).pos) := by
          refine Finset.ssubset_iff_of_subset (fun i hi => ?_) |>.2 ⟨q, ?_, ?_⟩
          · rw [Finset.mem_filter] at hi ⊢
            exact ⟨hi.1, by omega⟩
          · rw [Finset.mem_filter]
            exact ⟨hmem, by omega⟩
          · rw [Finset.mem_filter]
            rintro ⟨-, hlt⟩
            omega
        exact Finset.card_lt_card hss

/-- **The run resolves the word.**  `Fintype.card (T × T)` rounds suffice: one
more than the number of change points there can be. -/
theorem pos_eq_horizon (h : LocallyThinKernel φ) (hL : ℓ ≤ 2 ^ L) :
    (conf φ letter hℓ L x (Fintype.card (T × T) * (L + 3))).pos = ℓ := by
  obtain ⟨-, hprog⟩ := run_rounds φ letter hℓ L x h hL (Fintype.card (T × T))
  rcases hprog with hfin | hcnt
  · exact hfin
  · exfalso
    have h1 := le_trans hcnt (Finset.card_filter_le _ _)
    have h2 := changeSet_card_le φ (fun i => letter (x i))
    have h3 : 0 < Fintype.card (T × T) := Fintype.card_pos
    omega

/-- **What the transcript computes.**  At the last level the accumulator *is*
the word's product — the one place an identified arrow becomes an equal element,
because at the root both contexts are trivial. -/
theorem acc_eq_wordProd (h : LocallyThinKernel φ) (hL : ℓ ≤ 2 ^ L) :
    (conf φ letter hℓ L x (Fintype.card (T × T) * (L + 3))).acc = wordProd letter x := by
  obtain ⟨hres, -⟩ := run_rounds φ letter hℓ L x h hL (Fintype.card (T × T))
  have hpos := pos_eq_horizon φ letter hℓ L x h hL
  have hsame := hres.same
  rw [hpos] at hsame
  have hroot := rangeProd_eq_of_sameArrow_root φ (fun i => letter (x i)) hsame
  rw [wordProd, orderedProd_eq_rangeProd]
  exact hroot.symm

end Rounds

end ThinConf


/-! ## The transcript, its cost, and the collapse

The per-level cost is *uniform* — a cut query reads two windows whose lengths
add to `ℓ` however deep the search has gone — so unlike `FirstEntry`'s geometric
search this is a flat `m · g`, and the level count is exactly what the budget
pays for.  The collapse at the end is `HasDual.postcomp_of_determined`, not
`ofKer`: equal transcripts force equal products, but equal products certainly do
not force equal transcripts, so the biconditional `ofKer` wants is false in one
direction.  That factor two is spent explicitly. -/

section Compile

variable {α S T : Type} [Fintype α] [DecidableEq α]
  [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T]

/-- **The level count**: `|T|²` rounds of `L + 3` levels. -/
def levelCount (T : Type) [Fintype T] (L : ℕ) : ℕ := Fintype.card (T × T) * (L + 3)

/-- The pad the transcript is filled with past the level it has reached. -/
def padSlot (S T : Type) [Monoid S] [Monoid T] : Slot S T := ((1, 1), 1)

namespace ThinConf

/-- **One level's query, at the uniform cost.**  The configuration is a
parameter, not read off the word, so the bound holds at every reconstructed
value — which is what `HasDual.adaptiveCall` requires of a branch family. -/
theorem hasDual_recOf (φ : S →* T) (letter : α → S) {ℓ : ℕ} (hℓ : 0 < ℓ) (L : ℕ)
    {n₀ : ℕ} {D : ℝ} (hPoly : HasWordProdDualPoly T n₀ D) (hℓn : ℓ ≤ n₀)
    {c : ThinConf S T} (hval : IsValid ℓ c) (j : ℕ) :
    HasDual (fun x : Fin ℓ → α => recOf φ letter hℓ L x c j)
      (2 * D * Real.sqrt (ℓ : ℝ) + 2) :=
  HasDual.adaptiveCall_const
    (hasDual_cutObj φ letter hPoly hℓn (cutPos_le hval j))
    (hasDual_leaf letter (letIdx ℓ hℓ c))

variable (φ : S →* T) (letter : α → S) {ℓ : ℕ} (hℓ : 0 < ℓ) (L : ℕ)

/-- The level family the padded trace is built from. -/
noncomputable def traceLevel (i : Fin (levelCount T L)) (x : Fin ℓ → α) :
    Slot S T := levelAt φ letter hℓ L x (i : ℕ)

/-- Reading a padded trace as a sequence: past the horizon it is the pad. -/
def unpad {m : ℕ} (d : Fin m → Slot S T) (i : ℕ) : Slot S T :=
  if h : i < m then d ⟨i, h⟩ else padSlot S T

/-- **The trace the algorithm exports**, as one function of the word. -/
noncomputable def traceOf (x : Fin ℓ → α) : Fin (levelCount T L) → Slot S T :=
  fun i => levelAt φ letter hℓ L x (i : ℕ)

/-- **Determinism at the fiber**: on the fiber where the first `j` slots are
fixed, the level-`j` configuration is fixed too. -/
lemma conf_eq_confOf_preTrans (x : Fin ℓ → α) {j : ℕ} (hj : j ≤ levelCount T L) :
    conf φ letter hℓ L x j
      = confOf φ ℓ L
          (unpad (preTrans (traceLevel φ letter hℓ L) (padSlot S T) j x)) j := by
  refine conf_eq_confOf φ letter hℓ L x _ j fun i hi => ?_
  have hin : i < levelCount T L := lt_of_lt_of_le hi hj
  simp only [unpad, dif_pos hin, preTrans, if_pos hi, traceLevel]

/-- **The prefix trace, at `j` times the uniform level cost.** -/
theorem hasDual_preTrans {n₀ : ℕ} {D : ℝ} (hPoly : HasWordProdDualPoly T n₀ D)
    (hℓn : ℓ ≤ n₀) : ∀ j : ℕ, j ≤ levelCount T L →
      HasDual (preTrans (traceLevel φ letter hℓ L) (padSlot S T) j)
        ((j : ℝ) * (2 * D * Real.sqrt (ℓ : ℝ) + 2)) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine (hasDual_const (f := preTrans (traceLevel φ letter hℓ L)
        (padSlot S T) 0) fun x y => ?_).mono (by simp)
      funext i
      simp [preTrans]
  | succ j ih =>
      intro hj
      have hjm : j < levelCount T L := hj
      have hcall := HasDual.adaptiveCall (ih (Nat.le_of_succ_le hj))
        (T := fun d x => recOf φ letter hℓ L x (confOf φ ℓ L (unpad d) j) j)
        (fun d => hasDual_recOf φ letter hℓ L hPoly hℓn
          (isValid_confOf φ ℓ L (unpad d) j) j)
      have hpair := hcall.ofEq fun x => by
        rw [← conf_eq_confOf_preTrans φ letter hℓ L x (le_of_lt hjm)]
      have hker := hpair.ofKer
        (f' := preTrans (traceLevel φ letter hℓ L) (padSlot S T) (j + 1))
        fun x y => by
          rw [Prod.mk.injEq]
          exact preTrans_succ_iff (traceLevel φ letter hℓ L) (padSlot S T) hjm x y
      exact hker.mono (le_of_eq (by push_cast; ring))

/-- **The full padded trace**, at `m` times the level cost. -/
theorem hasDual_trace {n₀ : ℕ} {D : ℝ} (hPoly : HasWordProdDualPoly T n₀ D)
    (hℓn : ℓ ≤ n₀) :
    HasDual (fun x : Fin ℓ → α => traceOf φ letter hℓ L x)
      ((levelCount T L : ℝ) * (2 * D * Real.sqrt (ℓ : ℝ) + 2)) := by
  refine (hasDual_preTrans φ letter hℓ L hPoly hℓn _ le_rfl).ofEq fun x => ?_
  funext i
  simp [preTrans, i.isLt, traceLevel, traceOf]

/-- **The transcript determines the product.**  This is the determinacy
`HasDual.postcomp_of_determined` needs, and it is exactly `acc_eq_wordProd` read
through `conf_eq_confOf`: equal traces give equal configurations, hence equal
accumulators, hence — at the last level — equal products. -/
theorem wordProd_determined (h : LocallyThinKernel φ) (hL : ℓ ≤ 2 ^ L)
    (hcount : levelCount T L = Fintype.card (T × T) * (L + 3))
    (x y : Fin ℓ → α)
    (hxy : traceOf φ letter hℓ L x = traceOf φ letter hℓ L y) :
    wordProd letter x = wordProd letter y := by
  have hx : conf φ letter hℓ L x (levelCount T L)
      = confOf φ ℓ L (unpad (traceOf φ letter hℓ L x)) (levelCount T L) :=
    conf_eq_confOf φ letter hℓ L x _ _ fun i hi => by
      simp only [unpad, dif_pos hi, traceOf]
  have hy : conf φ letter hℓ L y (levelCount T L)
      = confOf φ ℓ L (unpad (traceOf φ letter hℓ L y)) (levelCount T L) :=
    conf_eq_confOf φ letter hℓ L y _ _ fun i hi => by
      simp only [unpad, dif_pos hi, traceOf]
  have hconf : conf φ letter hℓ L x (levelCount T L)
      = conf φ letter hℓ L y (levelCount T L) := by rw [hx, hy, hxy]
  rw [← acc_eq_wordProd φ letter hℓ L x h hL, ← acc_eq_wordProd φ letter hℓ L y h hL,
    ← hcount, hconf]

end ThinConf

end Compile


/-! ## The endpoint

`LiftsWordProd`, discharged.  The arithmetic is where `thinStep`'s provisional
body is cashed: `4 |T|² ≤ (N+1)⁴` and `L + 3 ≤ (clog₂(n₀+2) + 2)²`, with the
`D + 1` absorbing the raw leaf read's `+ 2` against `√ℓ ≥ 1`.  That `D + 1` is
the reason the coefficient is defined with a `D + 1` and not a `D`. -/

section Endpoint

variable {α S T : Type} [Fintype α] [DecidableEq α]
  [Monoid S] [Fintype S] [DecidableEq S]
  [Monoid T] [Fintype T] [DecidableEq T]

/-- **The level count fits the coefficient.**  `L` is bounded through
`dyadicDepth_le`, i.e. through the *minimality* of the depth — `2 ^ L ≥ ℓ` alone
would not do it. -/
theorem four_mul_levelCount_le {n₀ ℓ N : ℕ} (hℓn : ℓ ≤ n₀)
    (hT : Fintype.card T ≤ N) :
    4 * levelCount T (dyadicDepth ℓ)
      ≤ (N + 1) ^ 4 * (Nat.clog 2 (n₀ + 2) + 2) ^ 2 := by
  have ha : 2 * N ≤ (N + 1) ^ 2 := by
    calc 2 * N ≤ N * N + 2 * N + 1 := by omega
      _ = (N + 1) ^ 2 := by ring
  have h1 : 4 * Fintype.card (T × T) ≤ (N + 1) ^ 4 := by
    rw [Fintype.card_prod]
    calc 4 * (Fintype.card T * Fintype.card T) ≤ 4 * (N * N) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul hT hT)
      _ = (2 * N) ^ 2 := by ring
      _ ≤ ((N + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left ha 2
      _ = (N + 1) ^ 4 := by ring
  have h2 : dyadicDepth ℓ + 3 ≤ (Nat.clog 2 (n₀ + 2) + 2) ^ 2 := by
    have hd := dyadicDepth_le (n₀ := n₀) hℓn
    have he : (Nat.clog 2 (n₀ + 2) + 2) ^ 2
        = Nat.clog 2 (n₀ + 2) * Nat.clog 2 (n₀ + 2) + 4 * Nat.clog 2 (n₀ + 2) + 4 := by
      ring
    omega
  calc 4 * levelCount T (dyadicDepth ℓ)
      = 4 * Fintype.card (T × T) * (dyadicDepth ℓ + 3) := by rw [levelCount]; ring
    _ ≤ (N + 1) ^ 4 * (Nat.clog 2 (n₀ + 2) + 2) ^ 2 := Nat.mul_le_mul h1 h2

/-- **The square-zero lift at one length.**  From the image monoid's word-product
contract alone — and over an arbitrary alphabet, including a non-injective letter
map, which is what `HasWordProdDualPoly` quantifies over. -/
theorem hasDual_wordProd_of_locallyThin {φ : S →* T} (h : LocallyThinKernel φ)
    (letter : α → S) {n₀ : ℕ} {D : ℝ} (hPoly : HasWordProdDualPoly T n₀ D)
    {ℓ : ℕ} (hℓn : ℓ ≤ n₀) :
    HasDual (fun x : Fin ℓ → α => wordProd letter x)
      (thinStep n₀ (max (Fintype.card S) (Fintype.card T)) D * Real.sqrt (ℓ : ℝ)) := by
  have hD := hPoly.nonneg
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · refine (hasDual_const (f := fun x : Fin 0 → α => wordProd letter x)
      fun x y => ?_).mono ?_
    · rw [show x = y from funext fun i => i.elim0]
    · simp
  · have hL : ℓ ≤ 2 ^ dyadicDepth ℓ := le_two_pow_dyadicDepth ℓ
    have htr := ThinConf.hasDual_trace φ letter hℓ (dyadicDepth ℓ) hPoly hℓn
    have hs0 : (0 : ℝ) ≤ Real.sqrt (ℓ : ℝ) := Real.sqrt_nonneg _
    have hs1 : (1 : ℝ) ≤ Real.sqrt (ℓ : ℝ) := by
      have hc : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (ℓ : ℝ) := Real.sqrt_le_sqrt hc
    have hm0 : (0 : ℝ) ≤ (levelCount T (dyadicDepth ℓ) : ℝ) := Nat.cast_nonneg _
    have hc0 : (0 : ℝ) ≤ (levelCount T (dyadicDepth ℓ) : ℝ)
        * (2 * D * Real.sqrt (ℓ : ℝ) + 2) := by positivity
    refine (HasDual.postcomp_of_determined (g := fun x : Fin ℓ → α => wordProd letter x)
      hc0 htr (ThinConf.wordProd_determined φ letter hℓ (dyadicDepth ℓ) h hL rfl)).mono ?_
    -- the arithmetic
    set N := max (Fintype.card S) (Fintype.card T) with hNdef
    set B : ℝ := ((N : ℝ) + 1) ^ 4 * ((Nat.clog 2 (n₀ + 2) : ℝ) + 2) ^ 2 with hBdef
    have hB0 : (0 : ℝ) ≤ B := by
      rw [hBdef]; positivity
    have hnum : 4 * (levelCount T (dyadicDepth ℓ) : ℝ) ≤ B := by
      have := four_mul_levelCount_le (T := T) (N := N) hℓn (le_max_right _ _)
      rw [hBdef]
      exact_mod_cast this
    have hBm : (0 : ℝ) ≤ B - 4 * (levelCount T (dyadicDepth ℓ) : ℝ) := by linarith
    have h1 : 4 * (levelCount T (dyadicDepth ℓ) : ℝ) * D * Real.sqrt (ℓ : ℝ)
        ≤ B * D * Real.sqrt (ℓ : ℝ) := by
      nlinarith [mul_nonneg (mul_nonneg hBm hD) hs0]
    have h2 : 4 * (levelCount T (dyadicDepth ℓ) : ℝ) ≤ B * Real.sqrt (ℓ : ℝ) := by
      nlinarith [mul_nonneg hB0 (by linarith : (0 : ℝ) ≤ Real.sqrt (ℓ : ℝ) - 1)]
    calc 2 * ((levelCount T (dyadicDepth ℓ) : ℝ) * (2 * D * Real.sqrt (ℓ : ℝ) + 2))
        = 4 * (levelCount T (dyadicDepth ℓ) : ℝ) * D * Real.sqrt (ℓ : ℝ)
            + 4 * (levelCount T (dyadicDepth ℓ) : ℝ) := by ring
      _ ≤ B * D * Real.sqrt (ℓ : ℝ) + B * Real.sqrt (ℓ : ℝ) := by linarith
      _ = thinStep n₀ N D * Real.sqrt (ℓ : ℝ) := by rw [thinStep, hBdef]; ring

/-- **The square-zero lift's endpoint, discharged.**  A locally thin quotient lifts the
word-product contract from the image monoid to the source monoid, in
`HasWordProdDualPoly` form on both sides — so alphabet uniformity and horizon
uniformity are preserved, and the lift composes with the fixed-apex peel with no adapter
between them.

Combined with `locallyThinKernel_of_squareZero`, this is the paper's
square-zero product lift (`lem:ags-square-zero-lift`); and by the two
departures from that proof recorded in `LocallyThin.lean` it needs neither
characteristic zero nor a separate identity-fibre argument. -/
theorem liftsWordProd_of_locallyThin {φ : S →* T} (h : LocallyThinKernel φ)
    (n₀ : ℕ) (D : ℝ) : LiftsWordProd S T n₀ D := fun hPoly =>
  ⟨thinStep_nonneg n₀ _ hPoly.nonneg,
   fun _ _ _ letter _ℓ hℓ => hasDual_wordProd_of_locallyThin h letter hPoly hℓ⟩

end Endpoint

end LocallyThin

end MonoidProduct
