import MonoidProduct.Aperiodic.CubeRoot.FirstEntry
import MonoidProduct.Aperiodic.CubeRoot.AxisPacket
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The fixed-apex split: the first-entry value, below-apex zero, the killed axis

`FirstEntry.lean` located the first entry and returned the crossing letter;
this file turns that into the **value** `h = p·a` and splits on where it lands.

* `entryOf_spec` — **the value, decoded from what the algorithm pays for.**
  The algorithm buys the joint `(trace, crossing letter)`, so `h` must be a
  function of *that*, not an existential over the input: `FirstEntry.entryOf`
  computes it, `FirstEntry.cutOf` computes the window bound the continuation
  runs from, and both are total, since an adaptive branch family is indexed by
  every descriptor value.  Recovering `p` from the stored `qlo` costs nothing —
  `ReesQuot.proj_lift` is the injectivity `proj_eq_iff_of_ne_zero`, not a
  query.  (`firstEntry_value` is the same content as a statement about the
  input, and is what `entryOf_spec` is proved from.);
* `apexSplit` — **the split**, on the decoded value: either `h` lies strictly
  below the apex class, and the coordinate of the whole word is `0` with
  nothing left to query (`rep_mul_eq_zero_of_ssubset`: `rep` is a hom, so
  annihilating `h` annihilates every continuation); or `h` lies *in* the apex
  class.  Branch condition and value are both descriptor functions;
* `proj_rState_eq_zero` / `proj_strictParent_ne_zero` — **what the quotient can
  and cannot decide**, the pair that fixes the route of `ApexAdapter.lean`.  The axis's own
  targets are `J`-equivalent to `h`, hence inside the collapsed ideal, so the
  quotient reports `0 = 0` and decides nothing: `hQ` alone cannot price the
  continuation.  The *strict parents* the localized AGS step asks about lie
  outside the ideal, so there the exact quotient value determines the Boolean
  test — at factor two through `HasDual.postcomp_of_determined`, never as a
  free `ofKer`;
* `rEq_or_rep_eq_zero` — **the dichotomy** that makes the second branch an
  axis.  From an apex-class element a right multiple either stays in the killed
  `R`-axis or drops strictly below `J`, where the coordinate is `0` again.
  Green stability (`rEq_of_twoIdeal_eq_of_rLe`) is what rules out a third
  possibility: `h·u ≤_R h` always holds, and inside one `J`-class `≤_R` is
  already `R`.  There is no induction here — the dichotomy already speaks about
  `h·u` for arbitrary `u`;
* `rep_of_axisPacket` — **the packet determines the coordinate**, and
  `hasDual_apexAxisPacket` — the feed into
  `hasDual_axisPacket_of_strictParentIH`.  The price is
  `D · axisStep (n₀+1) M · √ℓ`, whose coefficient mentions the horizon and the
  monoid but **not** the coordinate's degree; that is the degree-independence
  the apex adapter and its assembly have to preserve.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace FixedApex

/-! ## Below the apex, and the continuation dichotomy -/

section Algebra

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- **Below the apex the coordinate vanishes — and so does everything after
it.**  `rep` is a monoid hom, so once the first entry is annihilated the whole
continuation is, and this branch of the split queries nothing further. -/
theorem rep_mul_eq_zero_of_ssubset (c : ApexCoordinate M) {h : M}
    (hh : twoIdeal h ⊂ twoIdeal c.apex) (u : M) : c.rep (h * u) = 0 := by
  rw [map_mul, c.annihilate h hh, zero_mul]

/-- **An element at or below the apex is not the identity.**  Properness of the
apex ideal, transported along the containment; it holds in both branches of the
split, and it is what `hasDual_axisPacket_of_strictParentIH` asks for. -/
theorem apexClass_ne_one (c : ApexCoordinate M) (hc : c.IsProper) {h : M}
    (hh : twoIdeal h ⊆ twoIdeal c.apex) : h ≠ 1 := by
  intro h1
  refine hc.ideal_proper ?_
  have hmem : h ∈ twoIdeal c.apex := hh (self_mem_twoIdeal h)
  rwa [h1] at hmem

variable [IsAperiodicMonoid M]

/-- **The continuation dichotomy.**  From an apex-class element a right
multiple either stays in the killed `R`-axis, or drops strictly below `J`,
where the coordinate is zero.  `h·u ≤_R h` always; Green stability says that
inside one `J`-class `≤_R` is already `R`, so the only alternative to staying
is a strict drop. -/
theorem rEq_or_rep_eq_zero (c : ApexCoordinate M) {h : M}
    (hh : twoIdeal h = twoIdeal c.apex) (u : M) :
    REq (h * u) h ∨ c.rep (h * u) = 0 := by
  have hrle : RLe (h * u) h := rLe_iff_exists.2 ⟨u, rfl⟩
  by_cases hJ : twoIdeal (h * u) = twoIdeal h
  · exact Or.inl (rEq_of_twoIdeal_eq_of_rLe hJ hrle)
  · refine Or.inr (c.annihilate (h * u) ?_)
    rw [← hh]
    exact Finset.ssubset_iff_subset_ne.2 ⟨twoIdeal_subset_of_rLe hrle, hJ⟩

end Algebra

/-! ## The killed axis carries the coordinate -/

section Axis

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M]

/-- The axis start at an apex-class first entry: `h` itself. -/
def apexState (h : M) : RState h := ⟨h, rEq_refl h⟩

@[simp] lemma apexState_val (h : M) : (apexState h).val = h := rfl

/-- **The axis state is the coordinate, at every cut.**  While the axis is
alive its state is the actual product; once it is dead the coordinate is `0`.
No induction: `rEq_or_rep_eq_zero` already covers an arbitrary right
multiple. -/
theorem rep_of_cutState (c : ApexCoordinate M) (letter : σ → M) {h : M}
    (hh : twoIdeal h = twoIdeal c.apex) {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    c.rep (h * winProd letter x 0 j)
      = (cutState (killedAction h) (apexState h) letter x j).elim 0
          fun s => c.rep s.val := by
  rw [cutState_killedAction]
  by_cases hr : REq ((apexState h).val * winProd letter x 0 j) h
  · rw [dif_pos hr]
    rfl
  · rw [dif_neg hr]
    exact (rEq_or_rep_eq_zero c hh _).resolve_left hr

/-- **The packet determines the coordinate.**  If the axis survives to the end
of the word the coordinate is the representation of the exit state; if it dies
anywhere, the coordinate is `0`.  Both branches are read off the packet alone,
which is what lets the next item pay for the packet and nothing else. -/
theorem rep_of_axisPacket (c : ApexCoordinate M) (letter : σ → M) {h : M}
    (hh : twoIdeal h = twoIdeal c.apex) {n : ℕ} (x : Fin n → σ) :
    c.rep (h * wordProd letter x)
      = if ((axisPacket h letter (apexState h) x).1 : ℕ) = n then
          (axisPacket h letter (apexState h) x).2.elim 0 fun s => c.rep s.val
        else 0 := by
  have hpk1 : ((axisPacket h letter (apexState h) x).1 : ℕ)
      = liveCut (killedAction h) (apexState h) letter x := rfl
  have hpk2 : (axisPacket h letter (apexState h) x).2
      = cutState (killedAction h) (apexState h) letter x
          (liveCut (killedAction h) (apexState h) letter x) := rfl
  rw [wordProd_eq_winProd, rep_of_cutState c letter hh x n, hpk1, hpk2]
  by_cases hlc : liveCut (killedAction h) (apexState h) letter x = n
  · rw [if_pos hlc, hlc]
  · have hlt : liveCut (killedAction h) (apexState h) letter x < n := by
      have := liveCut_le (killedAction h) (apexState h) letter x
      omega
    rw [if_neg hlc, cutState_eq_none_of_gt (killedAction h) (apexState h) letter x
      hlt le_rfl]
    rfl

/-- **The axis's own targets are inside the collapsed ideal.**  Every state of
the killed `R_h`-axis is `J`-equivalent to `h`, hence in the apex ideal, hence
projected to zero — as is every `h · w`.  So the quotient reports `0 = 0` on
both sides of the axis's fixed-context tests and decides **nothing**: `hQ`
alone cannot price the continuation, and the localized AGS step, whose targets
are the strict parents *above* the class, is the only route. -/
theorem proj_rState_eq_zero (c : ApexCoordinate M) (hc : c.IsProper) {h : M}
    (hh : twoIdeal h = twoIdeal c.apex) (s : RState h) :
    ReesQuot.proj (ReesQuot.apexIdeal c hc) s.val = ReesQuot.zero :=
  (ReesQuot.proj_apexIdeal_eq_zero_iff c hc).2
    (le_of_eq ((twoIdeal_eq_of_rEq s.2).trans hh))

/-- **Strict parents of an apex-class target are off the ideal.**  This is the
other half, and it is what makes the adapter of `ApexAdapter.lean` possible at all: where the
axis's own targets are invisible to the quotient, the strict parents the
localized AGS step asks about are outside the ideal, so
`ReesQuot.proj_eq_iff_of_ne_zero` applies and the exact quotient value
*determines* the Boolean test — at factor two, by
`HasDual.postcomp_of_determined`, never by a free `ofKer`. -/
theorem proj_strictParent_ne_zero (c : ApexCoordinate M) (hc : c.IsProper)
    {s u : M} (hs : twoIdeal s = twoIdeal c.apex)
    (hu : twoIdeal s ⊂ twoIdeal u) :
    ReesQuot.proj (ReesQuot.apexIdeal c hc) u ≠ ReesQuot.zero := by
  intro hzero
  have hsub := (ReesQuot.proj_apexIdeal_eq_zero_iff c hc).1 hzero
  rw [← hs] at hsub
  exact hu.ne (Finset.Subset.antisymm hu.1 hsub)

/-- **The feed into the axis packet's dual.**  At an apex-class first entry the
packet is priced by `hasDual_axisPacket_of_strictParentIH`.  Note the
coefficient: `axisStep (n₀+1) M` mentions the horizon and the monoid and
**not** `c.degree` — the degree-independence the apex adapter and its
assembly must preserve. -/
theorem hasDual_apexAxisPacket (c : ApexCoordinate M) (hc : c.IsProper)
    (letter : σ → M) {h : M} (hh : twoIdeal h ⊆ twoIdeal c.apex)
    {n₀ : ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hIH : ∀ s : RState h,
      StrictParentIH (prependLetter letter h) s.val (n₀ + 1) D)
    {ℓ : ℕ} (hℓ : ℓ ≤ n₀) :
    HasDual (axisPacket h letter (apexState h) (n := ℓ))
      (D * axisStep (n₀ + 1) M * Real.sqrt (ℓ : ℝ)) :=
  hasDual_axisPacket_of_strictParentIH letter (apexClass_ne_one c hc hh)
    (apexState h) hD hIH hℓ

end Axis

/-! ## The first-entry value, and the split -/

section Split

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M]

/-- The continuation after a cut, as a word in its own right — the bridge that
lets the axis run on it. -/
lemma winProd_eq_wordProd_window (letter : σ → M) {n : ℕ} (x : Fin n → σ)
    {k len : ℕ} (h : k + len ≤ n) :
    winProd letter x k (k + len)
      = wordProd letter fun t : Fin len => x (winEmb k len h t) :=
  (wordProd_winEmb letter x h).symm

/-- **The first-entry value `h = p·a`.**  `p = winProd x 0 lo` is the prefix
product at the located cut — the unique lift of the stored nonzero `qlo`,
recovered by injectivity rather than by a query — and `a` is the crossing
letter of the trace joint.  All four conjuncts are what `ApexAdapter.lean` consumes: `p` is
still off the ideal, `h` factors as `p·a`, `h` is inside the apex ideal, and
the word factors through `h`. -/
theorem firstEntry_value (c : ApexCoordinate M) (hc : c.IsProper)
    (letter : σ → M) {n : ℕ} (x : Fin n → σ)
    (hz : ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter x) = ReesQuot.zero) :
    ∃ lo : Fin n,
      (FirstEntry.conf (ReesQuot.apexIdeal c hc) letter x n).1 = (lo : ℕ)
        ∧ ReesQuot.proj (ReesQuot.apexIdeal c hc) (winProd letter x 0 (lo : ℕ))
            ≠ ReesQuot.zero
        ∧ winProd letter x 0 ((lo : ℕ) + 1)
            = winProd letter x 0 (lo : ℕ) * letter (x lo)
        ∧ twoIdeal (winProd letter x 0 ((lo : ℕ) + 1)) ⊆ twoIdeal c.apex
        ∧ wordProd letter x
            = winProd letter x 0 ((lo : ℕ) + 1)
              * winProd letter x ((lo : ℕ) + 1) n := by
  obtain ⟨lo, hlo, -, -, hne, hkill⟩ :=
    FirstEntry.conf_horizon_spec (I := ReesQuot.apexIdeal c hc) letter x hz
  have hsucc : winProd letter x 0 ((lo : ℕ) + 1)
      = winProd letter x 0 (lo : ℕ) * letter (x lo) :=
    FirstEntry.winProd_succ letter x lo
  refine ⟨lo, hlo, hne, hsucc, ?_, ?_⟩
  · refine (ReesQuot.proj_apexIdeal_eq_zero_iff c hc).1 ?_
    rw [hsucc, ReesQuot.proj_mul]
    exact hkill
  · rw [wordProd_eq_winProd]
    simp only [winProd]
    exact (rangeProd_split (fun i => letter (x i)) (Nat.zero_le _) lo.isLt).symm

variable [IsAperiodicMonoid M]

/-! ### The operational form: everything below is a function of the paid joint

`firstEntry_value` is a fact about the input; an adaptive consumer branches on
the **descriptor**.  These restate it there: `FirstEntry.entryOf` computes `h`
from `(trace, crossing letter)` alone — the joint `hasDual_paidOf` prices — and
`FirstEntry.cutOf` computes the window bound the continuation runs from. -/

/-- **The decoded first entry is inside the apex ideal, and the word factors
through it.**  Both facts are stated about the value the algorithm can actually
compute, not about an existential witness. -/
theorem entryOf_spec (c : ApexCoordinate M) (hc : c.IsProper) (letter : σ → M)
    {n : ℕ} (hn : 0 < n) (x : Fin n → σ)
    (hz : ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter x)
        = ReesQuot.zero) :
    twoIdeal (FirstEntry.entryOf letter
        (FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x))
        ⊆ twoIdeal c.apex
      ∧ wordProd letter x
          = FirstEntry.entryOf letter
              (FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x)
            * winProd letter x
                (FirstEntry.cutOf
                  (FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x).1) n := by
  obtain ⟨lo, hlo, -, -, hsub, hfactor⟩ := firstEntry_value c hc letter x hz
  have hdec := FirstEntry.entryOf_paidOf (I := ReesQuot.apexIdeal c hc) letter hn x hz
  have hcut := FirstEntry.cutOf_paidOf (I := ReesQuot.apexIdeal c hc) letter hn x
  rw [hdec, hcut, hlo]
  exact ⟨hsub, hfactor⟩

/-- **The fixed-apex split, on the decoded value.**  Either the first entry
lies strictly below the apex class — and the coordinate of the whole word is
`0`, with nothing further to query — or it lies *in* the apex class, where the
continuation is a killed `R_h`-axis run and `hasDual_apexAxisPacket` prices it.
There is no third case: that is `rEq_or_rep_eq_zero`.  Both the branch
condition and the value are functions of the paid joint. -/
theorem apexSplit (c : ApexCoordinate M) (hc : c.IsProper) (letter : σ → M)
    {n : ℕ} (hn : 0 < n) (x : Fin n → σ)
    (hz : ReesQuot.proj (ReesQuot.apexIdeal c hc) (wordProd letter x)
        = ReesQuot.zero) :
    c.rep (wordProd letter x) = 0
      ∨ (twoIdeal (FirstEntry.entryOf letter
              (FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x))
            = twoIdeal c.apex
          ∧ FirstEntry.entryOf letter
              (FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x) ≠ 1
          ∧ c.rep (wordProd letter x)
              = c.rep (FirstEntry.entryOf letter
                    (FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x)
                  * winProd letter x
                      (FirstEntry.cutOf
                        (FirstEntry.paidOf
                          (ReesQuot.apexIdeal c hc) letter hn x).1) n)) := by
  obtain ⟨hsub, hfactor⟩ := entryOf_spec c hc letter hn x hz
  by_cases heq : twoIdeal (FirstEntry.entryOf letter
      (FirstEntry.paidOf (ReesQuot.apexIdeal c hc) letter hn x)) = twoIdeal c.apex
  · exact Or.inr ⟨heq, apexClass_ne_one c hc hsub, by rw [← hfactor]⟩
  · left
    rw [hfactor]
    exact rep_mul_eq_zero_of_ssubset c
      (Finset.ssubset_iff_subset_ne.2 ⟨hsub, heq⟩) _

end Split

end FixedApex

end MonoidProduct
