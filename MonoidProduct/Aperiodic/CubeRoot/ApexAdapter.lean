import MonoidProduct.Aperiodic.CubeRoot.FixedApex
import MonoidProduct.Aperiodic.CubeRoot.MatrixWord
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The quotient-to-fixed-context-test adapter

The apex-class branch of the fixed-apex peel needs an *axis-ready*
induction hypothesis — every `RState h`, the augmented alphabet
`prependLetter letter h`, the shifted horizon `n₀ + 1`.  This file supplies
it from a quotient contract, in three steps that are worth keeping apart
because each is a place the accounting can go wrong.

1. **Which targets the quotient can see.**  The axis's *own* targets are
   `J`-equivalent to `h`, hence inside the collapsed ideal
   (`FixedApex.proj_rState_eq_zero`): there the quotient reports `0 = 0` and
   decides nothing, so no amount of quotient contract prices the axis directly.
   What the localized AGS step asks about instead are the **strict parents** of
   those targets, and `FixedApex.proj_strictParent_ne_zero` puts every one of
   them *outside* the ideal.  That is the whole reason the route exists.

2. **The coarsening, at factor two.**  Off the ideal, the exact quotient
   product *determines* the Boolean equality test
   (`ReesQuot.proj_eq_iff_of_ne_zero`).  Determinacy is one implication;
   `HasDual.ofKer` needs both, and the Boolean identifies every word whose
   product misses the target, which the exact quotient separates.  So the
   conversion is `HasDual.postcomp_of_determined` at `2c` — **not** a free
   recoding.  `hasDual_eqProd_of_quot` is that step, and the `2` in its
   conclusion is the whole content.

3. **The alphabet and the horizon.**  The tests live over `Option σ` at
   horizon `n₀ + 1`, not over `σ` at `n₀`.  The alphabet shift is *not* free
   and is not derivable from a `σ`-only contract, so it is paid for by asking
   the recursion hypothesis to be alphabet-uniform: `HasWordProdDualPoly`,
   instantiated at `Option σ`.  The horizon shift is absorbed where it always
   is, in `axisStep`'s leading `2`.

The endpoint is `hasDual_apexAxisPacket_of_quotPoly`: the axis packet at an
apex-class first entry, priced from the quotient contract alone, at
`2D · axisStep (n₀+1) M · √ℓ`.  The `2` is step 2's, carried explicitly rather
than folded into a constant, so that the final joint-to-coordinate collapse
is visibly a *separate* spend.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace ApexAdapter

/-! ## The one-test adapter -/

section OneTest

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- **A Boolean equality test against an off-ideal target, from the exact
quotient product** — at **factor two**.

`ReesQuot.proj_eq_iff_of_ne_zero` makes the quotient value *determine* the
test, which is what `HasDual.postcomp_of_determined` consumes.  It does not
make the conversion free: the test identifies every word whose product misses
`u`, and the exact quotient separates those, so the partition is strictly
coarser and `HasDual.ofKer` does not apply.  Budgeting this at `c` rather than
`2c` is a real error. -/
theorem hasDual_eqProd_of_quot {α : Type} [Fintype α] [DecidableEq α]
    {I : ReesIdeal M} (L : α → M) {u : M}
    (hu : ReesQuot.proj I u ≠ ReesQuot.zero) {ℓ : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hq : HasDual (fun y : Fin ℓ → α =>
        wordProd (fun t => ReesQuot.proj I (L t)) y) c) :
    HasDual (eqProd L u (n := ℓ)) (2 * c) := by
  refine hq.postcomp_of_determined hc ?_
  intro y z hyz
  rw [ReesQuot.wordProd_proj, ReesQuot.wordProd_proj] at hyz
  simp only [eqProd]
  refine decide_eq_decide.2 ⟨fun hy => ?_, fun hz => ?_⟩
  · have hu' : ReesQuot.proj I u = ReesQuot.proj I (wordProd L z) := by
      rw [← hy]; exact hyz
    exact ((ReesQuot.proj_eq_iff_of_ne_zero hu).1 hu').symm
  · have hu' : ReesQuot.proj I u = ReesQuot.proj I (wordProd L y) := by
      rw [← hz]; exact hyz.symm
    exact ((ReesQuot.proj_eq_iff_of_ne_zero hu).1 hu').symm

end OneTest

/-! ## The axis-ready induction hypothesis -/

section AxisIH

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M]

/-- **The strict-parent tests of an apex-class target, from the augmented
quotient contract.**  Stated against exactly the contract it needs — the
augmented alphabet at the shifted horizon — so that where that contract comes
from stays a separate question. -/
theorem strictParentIH_of_quot (c : ApexCoordinate M) (hc : c.IsProper)
    (letter : σ → M) {h : M} (hh : twoIdeal h = twoIdeal c.apex)
    {n₀ : ℕ} {D : ℝ}
    (hAug : HasWordProdDualUpTo
      (fun t : Option σ => ReesQuot.proj (ReesQuot.apexIdeal c hc)
        (prependLetter letter h t)) (n₀ + 1) D)
    (s : RState h) :
    StrictParentIH (prependLetter letter h) s.val (n₀ + 1) (2 * D) := by
  intro u hu ℓ hℓ
  have hs : twoIdeal s.val = twoIdeal c.apex := (twoIdeal_eq_of_rEq s.2).trans hh
  have hune := FixedApex.proj_strictParent_ne_zero c hc hs hu
  have hD0 := hAug.nonneg
  refine (hasDual_eqProd_of_quot (prependLetter letter h) hune ?_
    (hAug.apply hℓ)).mono (le_of_eq (by ring))
  have := Real.sqrt_nonneg (ℓ : ℝ)
  positivity

/-- **The axis-ready induction hypothesis, from the alphabet-uniform
contract.**  The alphabet polymorphism is spent exactly here: the tests live
over `Option σ`, and `HasWordProdDualPoly.toUpTo` is what makes that an
instance rather than a gap. -/
theorem axisIH_of_quotPoly (c : ApexCoordinate M) (hc : c.IsProper)
    (letter : σ → M) {h : M} (hh : twoIdeal h = twoIdeal c.apex)
    {n₀ : ℕ} {D : ℝ}
    (hPoly : HasWordProdDualPoly (ReesQuot (ReesQuot.apexIdeal c hc)) (n₀ + 1) D)
    (s : RState h) :
    StrictParentIH (prependLetter letter h) s.val (n₀ + 1) (2 * D) :=
  strictParentIH_of_quot c hc letter hh (hPoly.toUpTo _) s

/-- **The axis packet at an apex-class first entry, priced from the quotient
contract alone.**

The `2` is the coarsening of step 2, carried in the open: the final
joint-to-coordinate collapse of the assembly is a *separate* factor two and
must be counted separately.  The coefficient still mentions only the horizon, the
monoid and the contract constant — no `c.degree` — which is the
degree-independence the adapter and the assembly have to preserve. -/
theorem hasDual_apexAxisPacket_of_quotPoly (c : ApexCoordinate M)
    (hc : c.IsProper) (letter : σ → M) {h : M}
    (hh : twoIdeal h = twoIdeal c.apex) {n₀ : ℕ} {D : ℝ} (hD : 1 ≤ 2 * D)
    (hPoly : HasWordProdDualPoly (ReesQuot (ReesQuot.apexIdeal c hc)) (n₀ + 1) D)
    {ℓ : ℕ} (hℓ : ℓ ≤ n₀) :
    HasDual (axisPacket h letter (FixedApex.apexState h) (n := ℓ))
      (2 * D * axisStep (n₀ + 1) M * Real.sqrt (ℓ : ℝ)) :=
  FixedApex.hasDual_apexAxisPacket c hc letter (le_of_eq hh) hD
    (axisIH_of_quotPoly c hc letter hh hPoly) hℓ

end AxisIH

/-! ## The tail window, in a uniform record

The assembly's first obligation.  The continuation runs on the window `[k, k+len)`,
whose bounds are decoded from the paid joint — so `h`, `k` and `len` all vary
with the descriptor, and with them the *type* `Fin (len+1) × Option (RState h)`
of the packet.  `HasDual.adaptiveCall` needs one branch type for the whole
family, so the packet is recoded into `ApexRec M n`: the exit cut as an
absolute position of the whole word, and the exit state's underlying element.

The recoding is injective, so it is free (`ofKer`), and freezing the
coordinates outside the window is free too (`pullback`) — exactly the pair of
moves `ActionCompiler.hasDual_levelRec` makes for its level transcript.
`rep_of_apexRec` then says the recoded record still determines the
coordinate. -/

section Window

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M]

/-- **The uniform packet record**: an absolute exit cut, and the exit state's
element.  Uniform in the descriptor, which the raw packet's type is not. -/
abbrev ApexRec (M : Type) (n : ℕ) : Type := Fin (n + 1) × Option M

/-- The recoding of a window's packet into the uniform record. -/
def apexRec {h : M} {len n : ℕ} (k : ℕ) (hk : k + len ≤ n)
    (z : Fin (len + 1) × Option (RState h)) : ApexRec M n :=
  (⟨k + (z.1 : ℕ), by have := z.1.isLt; omega⟩, z.2.map Subtype.val)

lemma apexRec_injective {h : M} {len n : ℕ} (k : ℕ) (hk : k + len ≤ n) :
    Function.Injective (apexRec (M := M) (h := h) (len := len) (n := n) k hk) := by
  rintro ⟨j, r⟩ ⟨j', r'⟩ hz
  simp only [apexRec, Prod.mk.injEq, Fin.mk.injEq] at hz
  obtain ⟨hj, hr⟩ := hz
  have hj' : j = j' := Fin.ext (by omega)
  have hr' : r = r' := Option.map_injective Subtype.val_injective hr
  subst hj'
  subst hr'
  rfl

private lemma elim_map_val {h : M} {γ : Type} (o : Option (RState h)) (b : γ)
    (f : M → γ) : (o.map Subtype.val).elim b f = o.elim b fun s => f s.val := by
  cases o <;> rfl

/-- **The window's packet, in the uniform record.**  The bound `k ≤ n` is a
proof argument rather than a clamp: it is derivable from the descriptor
structurally (`FirstEntry.cutOf_le`), so nothing is lost and no `min` has to be
unwound later. -/
noncomputable def windowRec (letter : σ → M) {n : ℕ} (h : M) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → σ) : ApexRec M n :=
  apexRec k (by omega)
    (axisPacket h letter (FixedApex.apexState h)
      fun t => x (winEmb k (n - k) (by omega) t))

/-- **The window's packet, on the whole word, at the packet's own cost.**  Both
adjustments are free: `pullback` freezes the coordinates outside the window,
`ofKer` recodes an injective output. -/
theorem hasDual_windowRec (c : ApexCoordinate M) (hc : c.IsProper)
    (letter : σ → M) {h : M} (hh : twoIdeal h = twoIdeal c.apex)
    {n : ℕ} {D : ℝ} (hD : 1 ≤ 2 * D)
    (hPoly : HasWordProdDualPoly (ReesQuot (ReesQuot.apexIdeal c hc)) n D)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) :
    HasDual (fun x : Fin n → σ => windowRec letter h k hk x)
      (2 * D * axisStep n M * Real.sqrt (n : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpk := hasDual_apexAxisPacket_of_quotPoly c hc letter hh hD hPoly
    (ℓ := m + 1 - k) (by omega)
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hstep : (0 : ℝ) ≤ 2 * D * axisStep (m + 1) M := by
    have h1 := axisStep_nonneg (m + 1) M
    nlinarith
  refine ((hpk.pullback
    (winEmb_injective (show k + (m + 1 - k) ≤ m + 1 by omega))).ofKer
    fun u v => ?_).mono ?_
  · simp only [pullbackFun_apply, windowRec]
    exact ⟨fun huv => by rw [huv],
      fun huv => apexRec_injective k (by omega) huv⟩
  · have hle : Real.sqrt ((m + 1 - k : ℕ) : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le (m + 1) k)
    nlinarith [Real.sqrt_nonneg ((m + 1 - k : ℕ) : ℝ)]

/-- **The recoded record determines the coordinate**, on the whole word: the
continuation from an apex-class `h` across `[k, n)` is `c.rep` of the recorded
exit state when the axis survives the window, and `0` otherwise. -/
theorem rep_of_windowRec (c : ApexCoordinate M) (letter : σ → M) {h : M}
    (hh : twoIdeal h = twoIdeal c.apex) {n k : ℕ} (hk : k ≤ n) (x : Fin n → σ) :
    c.rep (h * winProd letter x k n)
      = (if ((windowRec letter h k hk x).1 : ℕ) = n then
          (windowRec letter h k hk x).2.elim 0 fun m => c.rep m
        else 0) := by
  have hy := FixedApex.rep_of_axisPacket c letter hh
    (fun t => x (winEmb k (n - k) (show k + (n - k) ≤ n by omega) t))
  have hw : wordProd letter
        (fun t => x (winEmb k (n - k) (show k + (n - k) ≤ n by omega) t))
      = winProd letter x k n := by
    rw [wordProd_winEmb letter x (show k + (n - k) ≤ n by omega)]
    congr 1
    omega
  rw [← hw, hy]
  simp only [windowRec, apexRec, elim_map_val]
  by_cases hj : ((axisPacket h letter (FixedApex.apexState h)
      fun t => x (winEmb k (n - k) (show k + (n - k) ≤ n by omega) t)).1 : ℕ)
      = n - k
  · rw [if_pos hj, if_pos (by omega)]
  · rw [if_neg hj, if_neg (by omega)]

end Window

/-! ## The peel's cost coefficient

`apexStep` is fixed here, and what it does **not** take is the point: no
coordinate.  A reconstruction whose cost scaled with `c.degree` could not be
stated against this signature at all, so the assembly's degree-independence is
enforced by the type rather than checked afterwards — and the
`∑_J d_J² ≤ |M|` accounting downstream depends on exactly that.

One contract constant suffices for the whole peel: the alphabet-uniform
`HasWordProdDualPoly` gives the `σ`-instance of the first entry and the `Option σ`
instance of the axis alike (`HasWordProdDualPoly.toUpTo`), so there is no
second constant to thread.

The **body** is provisional in the sense this development already uses for
`cubeRootFactor` — downstream theorems are stated against the name, not the
body — but it is not arbitrary.  It is the budget the assembly has to fit into:

* the whole word's quotient product, `D√n`, for the outer nonzero/zero split
  (nonzero: the value is a free table lookup off the unique lift);
* the paid joint of the first entry (`FirstEntry`), `4D√n + 2`;
* the axis packet above, `2D · axisStep n M · √n` — whose `2` is the adapter's
  quotient-to-Boolean coarsening.  The horizon is `n`, not `n + 1`: the first
  entry consumes a letter (`FirstEntry.one_le_cutOf`), so the continuation runs
  at horizon `n - 1` and `axisStep ((n-1)+1) M = axisStep n M`;
* one final joint-to-coordinate collapse, `× 2`, counted **separately** from
  that coarsening.

Summing and absorbing the additive `2` with `2 ≤ 2√n` at `n ≥ 1` gives the
body below. -/
noncomputable def apexStep (n : ℕ) (M : Type) [Fintype M] (D : ℝ) : ℝ :=
  10 * D + 4 + 4 * D * axisStep n M

lemma apexStep_nonneg (n : ℕ) (M : Type) [Fintype M] [Nonempty M] {D : ℝ}
    (hD : 0 ≤ D) : 0 ≤ apexStep n M D := by
  have h := one_le_axisStep n M
  simp only [apexStep]
  nlinarith

lemma one_le_apexStep (n : ℕ) (M : Type) [Fintype M] [Nonempty M] {D : ℝ}
    (hD : 0 ≤ D) : 1 ≤ apexStep n M D := by
  have h := one_le_axisStep n M
  simp only [apexStep]
  nlinarith

lemma apexStep_mono_cost (n : ℕ) (M : Type) [Fintype M] [Nonempty M] {D D' : ℝ}
    (h : D ≤ D') : apexStep n M D ≤ apexStep n M D' := by
  have h1 := one_le_axisStep n M
  simp only [apexStep]
  nlinarith

/-- **`apexStep` is monotone in the horizon**, so one certificate at `n₀`
covers every `ℓ ≤ n₀` — which is what a horizon-uniform output needs. -/
lemma apexStep_mono_horizon {n₁ n₀ : ℕ} (hn : n₁ ≤ n₀) (M : Type) [Fintype M]
    {D : ℝ} (hD : 0 ≤ D) : apexStep n₁ M D ≤ apexStep n₀ M D := by
  have h1 := axisStep_mono_horizon hn M
  simp only [apexStep]
  nlinarith

/-! ## The assembly

The peel's endpoint: the coordinate value of a whole word, from the
alphabet-uniform quotient contract alone, at `apexStep n M D · √n`.

One adaptive call over one descriptor, then one collapse:

* the **descriptor** `apexDesc` — the whole word's quotient product together
  with the first entry's paid joint — at `D√n + (4D√n + 2)`;
* the **branch** `apexBranch` — the window packet of the decoded first entry,
  in the uniform record.  It is *total*: where the decoded entry is not
  apex-class it is a constant, because a branch family is indexed by every
  descriptor value and not only by the ones the promise admits;
* the **collapse** `HasDual.postcomp_of_determined` — the second and last
  factor two.  The first was the adapter's quotient-to-Boolean coarsening,
  already inside the branch cost; they are separate spends and both are
  counted.

Determinacy is where the semantics is spent, in exactly three cases: the
quotient product is nonzero, and the value is a table lookup off
`ReesQuot.lift`; it is zero and the decoded entry is strictly below the apex,
where `rep` annihilates; or it is zero and the entry is apex-class, where
`rep_of_windowRec` reads the value off the record. -/

section Assembly

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M]

/-- **The descriptor the peel branches on**: the whole word's quotient product,
and the first entry's paid joint. -/
def apexDesc (c : ApexCoordinate M) (hc : c.IsProper) (letter : σ → M) {n : ℕ}
    (hn : 0 < n) (x : Fin n → σ) :
    ReesQuot (ReesQuot.apexIdeal c hc)
      × ((Fin n → ReesQuot (ReesQuot.apexIdeal c hc)) × σ) :=
  (ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter x),
    FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x)

@[simp] lemma apexDesc_fst (c : ApexCoordinate M) (hc : c.IsProper)
    (letter : σ → M) {n : ℕ} (hn : 0 < n) (x : Fin n → σ) :
    (apexDesc c hc letter hn x).1
      = ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter x) := rfl

@[simp] lemma apexDesc_snd (c : ApexCoordinate M) (hc : c.IsProper)
    (letter : σ → M) {n : ℕ} (hn : 0 < n) (x : Fin n → σ) :
    (apexDesc c hc letter hn x).2
      = FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x := rfl

/-- **The continuation branch, total in the descriptor.**  Off the apex class
there is nothing to run, and a constant is what the branch family needs
there. -/
noncomputable def apexBranch (c : ApexCoordinate M) (hc : c.IsProper)
    (letter : σ → M) {n : ℕ} (hn : 0 < n)
    (d : ReesQuot (ReesQuot.apexIdeal c hc)
      × ((Fin n → ReesQuot (ReesQuot.apexIdeal c hc)) × σ))
    (x : Fin n → σ) : ApexRec M n :=
  if twoIdeal (FirstEntry.entryOf letter d.2) = twoIdeal c.apex then
    windowRec letter (FirstEntry.entryOf letter d.2) (FirstEntry.cutOf d.2.1)
      (FirstEntry.cutOf_le hn d.2.1) x
  else (⟨0, Nat.zero_lt_succ n⟩, none)

lemma apexBranch_pos (c : ApexCoordinate M) (hc : c.IsProper) (letter : σ → M)
    {n : ℕ} (hn : 0 < n)
    {d : ReesQuot (ReesQuot.apexIdeal c hc)
      × ((Fin n → ReesQuot (ReesQuot.apexIdeal c hc)) × σ)}
    (hd : twoIdeal (FirstEntry.entryOf letter d.2) = twoIdeal c.apex)
    (x : Fin n → σ) :
    apexBranch c hc letter hn d x
      = windowRec letter (FirstEntry.entryOf letter d.2) (FirstEntry.cutOf d.2.1)
          (FirstEntry.cutOf_le hn d.2.1) x :=
  if_pos hd

lemma apexBranch_neg (c : ApexCoordinate M) (hc : c.IsProper) (letter : σ → M)
    {n : ℕ} (hn : 0 < n)
    {d : ReesQuot (ReesQuot.apexIdeal c hc)
      × ((Fin n → ReesQuot (ReesQuot.apexIdeal c hc)) × σ)}
    (hd : ¬ twoIdeal (FirstEntry.entryOf letter d.2) = twoIdeal c.apex)
    (x : Fin n → σ) :
    apexBranch c hc letter hn d x = (⟨0, Nat.zero_lt_succ n⟩, none) :=
  if_neg hd

/-- **The paid joint determines the coordinate.**  Three cases and no more: the
quotient product is nonzero, and the value is a table lookup off
`ReesQuot.lift`; it is zero and the decoded first entry is strictly below the
apex, where `rep` annihilates; or it is zero and the entry is apex-class, where
`rep_of_windowRec` reads the value off the record.

Every branch condition is phrased on `apexDesc`'s own projections rather than
on their reducts: `twoIdeal` of a decoded entry is a `Finset`, and asking the
unifier to see through one is what makes this expensive. -/
theorem rep_determined (c : ApexCoordinate M) (hc : c.IsProper) (letter : σ → M)
    {n : ℕ} (hn : 0 < n) (x y : Fin n → σ)
    (hxy : (apexDesc c hc letter hn x,
              apexBranch c hc letter hn (apexDesc c hc letter hn x) x)
        = (apexDesc c hc letter hn y,
              apexBranch c hc letter hn (apexDesc c hc letter hn y) y)) :
    c.rep (wordProd letter x) = c.rep (wordProd letter y) := by
  have hdeq : apexDesc c hc letter hn x = apexDesc c hc letter hn y :=
    congrArg Prod.fst hxy
  have hqeq : ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter x)
      = ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter y) :=
    congrArg Prod.fst hdeq
  have hpeq : FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x
      = FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn y :=
    congrArg Prod.snd hdeq
  by_cases hz : ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter x)
      = ReesQuot.zero
  · have hzy : ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter y)
        = ReesQuot.zero := by rw [← hqeq]; exact hz
    obtain ⟨hsubx, hfx⟩ := FixedApex.entryOf_spec c hc letter hn x hz
    obtain ⟨hsuby, hfy⟩ := FixedApex.entryOf_spec c hc letter hn y hzy
    rw [← hpeq] at hfy hsuby
    by_cases hcls : twoIdeal (FirstEntry.entryOf letter
        (apexDesc c hc letter hn x).2) = twoIdeal c.apex
    · have hb0 : apexBranch c hc letter hn (apexDesc c hc letter hn x) x
          = apexBranch c hc letter hn (apexDesc c hc letter hn x) y :=
        (congrArg Prod.snd hxy).trans
          (congrArg (fun d => apexBranch c hc letter hn d y) hdeq.symm)
      rw [apexBranch_pos c hc letter hn hcls x,
        apexBranch_pos c hc letter hn hcls y] at hb0
      simp only [apexDesc_snd] at hb0 hcls
      rw [hfx, hfy,
        rep_of_windowRec c letter hcls (FirstEntry.cutOf_le hn _) x,
        rep_of_windowRec c letter hcls (FirstEntry.cutOf_le hn _) y, hb0]
    · simp only [apexDesc_snd] at hcls
      have hss := Finset.ssubset_iff_subset_ne.2 ⟨hsubx, hcls⟩
      rw [hfx, hfy, FixedApex.rep_mul_eq_zero_of_ssubset c hss,
        FixedApex.rep_mul_eq_zero_of_ssubset c hss]
  · have hzy : ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter y)
        ≠ ReesQuot.zero := by rw [← hqeq]; exact hz
    have hwx : wordProd letter x
        = (ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter x)).lift :=
      (ReesQuot.lift_proj hz).symm
    have hwy : wordProd letter y
        = (ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter y)).lift :=
      (ReesQuot.lift_proj hzy).symm
    rw [hwx, hwy, hqeq]

/-- **The fixed-apex coordinate**, from the alphabet-uniform quotient contract
alone, at `apexStep n M D · √n` — a coefficient with no `c.degree` in it. -/
theorem hasDual_apexCoord (c : ApexCoordinate M) (hc : c.IsProper)
    (letter : σ → M) {n : ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hPoly : HasWordProdDualPoly (ReesQuot (ReesQuot.apexIdeal c hc)) n D) :
    HasDual (fun x : Fin n → σ => c.rep (wordProd letter x))
      (apexStep n M D * Real.sqrt (n : ℝ)) := by
  have : Nonempty M := ⟨1⟩
  have hD0 : (0 : ℝ) ≤ D := le_trans zero_le_one hD
  have hax := one_le_axisStep n M
  have hA0 : (0 : ℝ) ≤ 2 * D * axisStep n M :=
    mul_nonneg (by linarith) (by linarith)
  have hsq := Real.sqrt_nonneg (n : ℝ)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (hasDual_const fun x y => ?_).mono ?_
    · rw [show x = y from funext fun i => i.elim0]
    · simp
  have hUp : HasWordProdDualUpTo
      (fun t : σ => ReesQuot.proj (ReesQuot.apexIdeal c hc) (letter t)) n D :=
    hPoly.toUpTo _
  have hq : HasDual (fun x : Fin n → σ =>
      ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter x))
      (D * Real.sqrt (n : ℝ)) :=
    (hUp.apply le_rfl).ofEq fun x => ReesQuot.wordProd_proj letter x
  have hp := FirstEntry.hasDual_paidOf
    (I := ReesQuot.apexIdeal c hc) letter hn hUp
  have hdesc : HasDual (apexDesc c hc letter hn)
      (D * Real.sqrt (n : ℝ) + (4 * D * Real.sqrt (n : ℝ) + 2)) :=
    HasDual.adaptiveCall_const hq hp
  have hbr : ∀ d, HasDual (apexBranch c hc letter hn d)
      (2 * D * axisStep n M * Real.sqrt (n : ℝ)) := by
    intro d
    by_cases hd : twoIdeal (FirstEntry.entryOf letter d.2) = twoIdeal c.apex
    · refine (hasDual_windowRec c hc letter hd (by linarith) hPoly
        (FirstEntry.one_le_cutOf d.2.1)
        (FirstEntry.cutOf_le hn d.2.1)).ofEq fun x => ?_
      exact (apexBranch_pos c hc letter hn hd x).symm
    · refine (hasDual_const (f := apexBranch c hc letter hn d)
        fun x y => ?_).mono ?_
      · rw [apexBranch_neg c hc letter hn hd x, apexBranch_neg c hc letter hn hd y]
      · exact mul_nonneg hA0 hsq
  have hjoint := hdesc.adaptiveCall hbr
  have hcost : (0 : ℝ) ≤ D * Real.sqrt (n : ℝ) + (4 * D * Real.sqrt (n : ℝ) + 2)
      + 2 * D * axisStep n M * Real.sqrt (n : ℝ) := by
    have h1 : (0 : ℝ) ≤ D * Real.sqrt (n : ℝ) := mul_nonneg hD0 hsq
    have h3 : (0 : ℝ) ≤ 2 * D * axisStep n M * Real.sqrt (n : ℝ) :=
      mul_nonneg hA0 hsq
    linarith
  refine (hjoint.postcomp_of_determined hcost
    (rep_determined c hc letter hn)).mono ?_
  have h1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hn1
  simp only [apexStep]
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

/-- **The coordinate bound is alphabet-uniform.**  `hasDual_apexCoord` is
already polymorphic in the alphabet; naming that is what the recursion needs,
since its hypothesis is alphabet-uniform (`HasWordProdDualPoly` on the
quotient) and its conclusion has to be too before it can be fed back in. -/
theorem hasDual_apexCoord_poly (c : ApexCoordinate M) (hc : c.IsProper)
    {n : ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hPoly : HasWordProdDualPoly (ReesQuot (ReesQuot.apexIdeal c hc)) n D)
    (α : Type) [Fintype α] [DecidableEq α] (letter : α → M) :
    HasDual (fun x : Fin n → α => c.rep (wordProd letter x))
      (apexStep n M D * Real.sqrt (n : ℝ)) :=
  hasDual_apexCoord c hc letter hD hPoly

/-! ## The horizon-uniform output

`hasDual_apexCoord` bounds the coordinate at one length and one alphabet; the
recursion consumes a `HasWordProdDualPoly`, so the bound has to be packaged
uniformly in **both**, and over the coordinate's own monoid, since that is the
object the next layer composes.  Three things make the packaging free:

* `apexStep_mono_horizon`, so one constant at `n₀` covers every `ℓ ≤ n₀`;
* `repImage c.rep = MonoidHom.mrange c.rep` as the carrier — a submonoid, hence
  a monoid, and its `mrangeRestrict` differs from `c.rep` only by an injective
  `Subtype.val`, so the recoding is an `ofKer` and costs nothing;
* the alphabet quantifier, which `hasDual_apexCoord` already satisfies — every
  letter map into the image is `c.rep ∘ letter` for some `letter`, by choice on
  the range membership.
-/

section Uniform

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- A monoid hom commutes with word products. -/
lemma wordProd_hom {A B : Type} [Monoid A] [Monoid B] (f : A →* B)
    {α : Type} [Fintype α] [DecidableEq α] (L : α → A) {ℓ : ℕ} (x : Fin ℓ → α) :
    f (wordProd L x) = wordProd (fun t => f (L t)) x := by
  rw [wordProd, wordProd, orderedProd_eq_prod_ofFn, orderedProd_eq_prod_ofFn,
    map_list_prod, List.map_ofFn]
  simp [Function.comp_def]

/-- **The coordinate's image monoid carries the alphabet- and horizon-uniform
contract.**  This is the form the peel's recursion consumes — and the form
`hasDual_apexCoord` alone was not: it fixed both the length and the alphabet,
and spoke about ambient matrices rather than a monoid. -/
theorem hasWordProdDualPoly_apexCoord (c : ApexCoordinate M) (hc : c.IsProper)
    {n₀ : ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hPoly : HasWordProdDualPoly (ReesQuot (ReesQuot.apexIdeal c hc)) n₀ D) :
    HasWordProdDualPoly (repImage c.rep) n₀ (apexStep n₀ M D) := by
  classical
  have : Nonempty M := ⟨1⟩
  have hD0 : (0 : ℝ) ≤ D := le_trans zero_le_one hD
  refine ⟨le_trans zero_le_one (one_le_apexStep n₀ M hD0), ?_⟩
  intro α _ _ L ℓ hℓ
  have hex : ∀ t : α, ∃ a : M, c.rep a = (L t : Matrix (Fin c.degree) (Fin c.degree) ℚ) :=
    fun t => MonoidHom.mem_mrange.1 (L t).2
  choose letter hletter using hex
  have hword : ∀ x : Fin ℓ → α,
      wordProd L x = MonoidHom.mrangeRestrict c.rep (wordProd letter x) := by
    intro x
    rw [wordProd_hom (MonoidHom.mrangeRestrict c.rep) letter x]
    congr 1
    funext t
    exact Subtype.ext (hletter t).symm
  refine ((hasDual_apexCoord c hc letter hD (hPoly.mono_horizon hℓ)).ofKer
    fun u v => ?_).mono ?_
  · rw [hword, hword]
    exact ⟨fun huv => Subtype.ext huv, fun huv => congrArg Subtype.val huv⟩
  · exact mul_le_mul_of_nonneg_right (apexStep_mono_horizon hℓ M hD0)
      (Real.sqrt_nonneg _)

end Uniform

end Assembly

end ApexAdapter

end MonoidProduct
