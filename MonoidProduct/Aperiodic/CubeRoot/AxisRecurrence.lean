import MonoidProduct.Aperiodic.CubeRoot.ActionTarget
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The regular-axis recurrence

The paper's `prop:ags-axis-recurrence` (*Regular-axis recurrence*).
`AxisPacket.lean` prices an axis packet from certificates for the strict
two-sided parents of its states; `ActionTarget.lean` produces exactly such a
certificate from axis packets of the target action's owners; and
`TargetAction.lean`'s `regHeight_drop` — through its wrapper
`regHeight_targetOwner_lt` — says those owners sit strictly lower.  Closing
that loop is this file, which ends with the **regular-action compiler by
height** (`prop:ags-action-height`).

Two things shape the statement.

**Alphabet-polymorphism.**  The virtual prepend of `StrictParent.lean` moves the alphabet from
`σ` to `Option σ` at every level, so a statement fixed to one alphabet cannot
be the induction hypothesis.  `AxisBoundUpTo` therefore quantifies over the
alphabet *inside*.

**The horizon budget is an invariant, not a measure.**  A recursive call
prepends one letter and drops one regular height, so `ℓ + h` is *preserved*;
`H` is a fixed budget the recursion spends on one side and regains on the
other.  The well-founded induction is on the height `h` alone.  (`H` rather
than `N`, which the paper already spends on `|M|`.)

The recurrence proved here is **exact** — `axisNext`, one height in terms of
the height below — and no numerical majorant is chosen yet.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## Monotonicity of the step constants -/

lemma agsStep_mono (M : Type) [Fintype M] {N N' : ℕ} (h : N ≤ N') :
    agsStep N M ≤ agsStep N' M := by
  have hc : (Nat.clog 2 (N + 1) : ℝ) ≤ (Nat.clog 2 (N' + 1) : ℝ) := by
    exact_mod_cast Nat.clog_mono_right 2 (by omega)
  have h0 : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := Nat.cast_nonneg _
  have hsq : ((Nat.clog 2 (N + 1) : ℝ) + 2) ^ 2
      ≤ ((Nat.clog 2 (N' + 1) : ℝ) + 2) ^ 2 := by nlinarith
  rw [agsStep, agsStep]
  exact mul_le_mul_of_nonneg_left hsq
    (by positivity : (0 : ℝ) ≤ 2 ^ 40 * ((Fintype.card M : ℝ) + 1) ^ 5)

lemma axisStep_mono (M : Type) [Fintype M] {N N' : ℕ} (h : N ≤ N') :
    axisStep N M ≤ axisStep N' M := by
  have hc : (Nat.clog 2 (N + 1) : ℝ) ≤ (Nat.clog 2 (N' + 1) : ℝ) := by
    exact_mod_cast Nat.clog_mono_right 2 (by omega)
  have hA := agsStep_mono M h
  have hA1 := one_le_agsStep N M
  have hcard : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
  have hsq : (0 : ℝ) ≤ 24 * Real.sqrt ((Fintype.card M : ℝ) + 1) := by positivity
  have h0 : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := Nat.cast_nonneg _
  rw [axisStep, axisStep]
  refine mul_le_mul (by linarith) ?_ (by nlinarith) (by nlinarith)
  nlinarith

/-! ## The bound, and the exact recurrence -/

section Recurrence

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **The axis-packet bound at regular height `h`, under horizon budget `H`.**

The alphabet is quantified *inside*: the recursion prepends a letter, so the
induction hypothesis has to hold at `Option σ` as well as at `σ`.  The
hypothesis `ℓ + h ≤ H` is the budget invariant — a call spends one unit of
length and regains one unit of height, leaving the sum unchanged. -/
def AxisBoundUpTo (M : Type) [Monoid M] [Fintype M] [DecidableEq M]
    (H h : ℕ) (D : ℝ) : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (letter : σ → M) (e : M) (r : RState e)
    (ℓ : ℕ), regHeight e ≤ h → ℓ + h ≤ H →
      HasDual (axisPacket e letter r (n := ℓ)) (D * Real.sqrt (ℓ : ℝ))

/-- **The base**: regular height `0` is the identity axis, which is a minimum
finding and calls nothing. -/
theorem axisBoundUpTo_zero (H : ℕ) : AxisBoundUpTo M H 0 (axisBase H) := by
  intro σ _ _ letter e r ℓ hh hb
  obtain rfl : e = 1 := regHeight_eq_zero_iff.1 (Nat.le_zero.1 hh)
  exact hasDual_axisPacket_one letter r (by omega)

/-- **One height, exactly.**  The cost of a height in terms of the height below:
the localized AGS step's own multiplier `axisStep (H+1) M`, times the target
test of `ActionTarget.lean` at `2|M|(D + 2)`. -/
noncomputable def axisNext (H : ℕ) (M : Type) [Fintype M] (D : ℝ) : ℝ :=
  axisStep (H + 1) M * (2 * (Fintype.card M : ℝ) * (D + 2))

/-- **The recurrence step.**  Height `h + 1` costs `axisNext` of height `h` —
or the base, when the axis happens to sit at the identity. -/
theorem axisBoundUpTo_succ {H h : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hIH : AxisBoundUpTo M H h D) :
    AxisBoundUpTo M H (h + 1) (max (axisBase H) (axisNext H M D)) := by
  classical
  intro σ _ _ letter e r ℓ hh hb
  have hcard1 : (1 : ℝ) ≤ (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsq := Real.sqrt_nonneg (ℓ : ℝ)
  by_cases he : e = 1
  · subst he
    refine (hasDual_axisPacket_one letter r (show ℓ ≤ H by omega)).mono ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hsq
  -- the recursive branch
  set Dstep : ℝ := 2 * (Fintype.card M : ℝ) * (D + 2) with hDstep
  have hDstep1 : 1 ≤ Dstep := by rw [hDstep]; nlinarith
  have hIHstep : ∀ s : RState e,
      StrictParentIH (prependLetter letter r.val) s.val (ℓ + 1) Dstep := by
    intro s t ht len hlen
    obtain ⟨owner, hown⟩ := exists_targetOwner t
    have hpk : HasOwnerPackets (prependLetter letter r.val) owner len D := by
      refine ⟨hD, fun z len' hlen' => ?_⟩
      refine hIH (Option σ) (prependLetter letter r.val) (owner z)
        ⟨owner z, rEq_refl (owner z)⟩ len' ?_ (by omega)
      have hlt := regHeight_targetOwner_lt s ht (hown z)
      omega
    exact hasDual_eqProd_uniform (prependLetter letter r.val) hown hpk
  refine (hasDual_axisPacket_of_strictParentIH letter he r hDstep1 hIHstep
    (le_refl ℓ)).mono ?_
  have hmono : axisStep (ℓ + 1) M ≤ axisStep (H + 1) M :=
    axisStep_mono M (by omega)
  have hstep0 : (0 : ℝ) ≤ Dstep := le_trans zero_le_one hDstep1
  have hnext : Dstep * axisStep (ℓ + 1) M ≤ axisNext H M D := by
    rw [axisNext, hDstep]
    nlinarith [axisStep_nonneg (ℓ + 1) M]
  calc Dstep * axisStep (ℓ + 1) M * Real.sqrt (ℓ : ℝ)
      ≤ axisNext H M D * Real.sqrt (ℓ : ℝ) := mul_le_mul_of_nonneg_right hnext hsq
    _ ≤ max (axisBase H) (axisNext H M D) * Real.sqrt (ℓ : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hsq

/-- The coefficient at each height, by the exact recurrence — no majorant. -/
noncomputable def axisCoeff (H : ℕ) (M : Type) [Fintype M] : ℕ → ℝ
  | 0 => axisBase H
  | h + 1 => max (axisBase H) (axisNext H M (axisCoeff H M h))

lemma axisCoeff_nonneg (H : ℕ) (M : Type) [Fintype M] (h : ℕ) :
    0 ≤ axisCoeff H M h := by
  induction h with
  | zero => exact axisBase_nonneg H
  | succ h ih =>
      rw [axisCoeff]
      exact le_trans (axisBase_nonneg H) (le_max_left _ _)

/-- **The regular-axis recurrence.**  Every regular height is priced, exactly,
by the recursion of `axisNext` from the identity axis. -/
theorem axisBoundUpTo_axisCoeff (H : ℕ) :
    ∀ h : ℕ, AxisBoundUpTo M H h (axisCoeff H M h) := by
  intro h
  induction h with
  | zero => exact axisBoundUpTo_zero H
  | succ h ih => exact axisBoundUpTo_succ (axisCoeff_nonneg H M h) ih

/-! ## The numerical majorant

Only now, with the recurrence proved exactly, is a closed form chosen.  One
height multiplies the coefficient by at most `6·axisStep(H+1)·|M|` — the `6`
is `2` from the target test's `2|M|` and `3` from `D + 2 ≤ 3D` once `D ≥ 1` —
so a single constant raised to `h + 1` dominates. -/

/-- `axisBase` is at least `192`. -/
lemma one_le_axisBase (N : ℕ) : 1 ≤ axisBase N := by
  have h : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := Nat.cast_nonneg _
  rw [axisBase]
  nlinarith

/-- **The per-height constant.** -/
noncomputable def axisConst (H : ℕ) (M : Type) [Fintype M] : ℝ :=
  max (axisBase H) (6 * axisStep (H + 1) M * (Fintype.card M : ℝ))

lemma one_le_axisConst (H : ℕ) (M : Type) [Fintype M] : 1 ≤ axisConst H M :=
  le_trans (one_le_axisBase H) (le_max_left _ _)

/-- **The recurrence, solved.** -/
lemma axisCoeff_le_pow (H : ℕ) (M : Type) [Fintype M] :
    ∀ h : ℕ, axisCoeff H M h ≤ axisConst H M ^ (h + 1) := by
  have hC1 : 1 ≤ axisConst H M := one_le_axisConst H M
  have hC0 : (0 : ℝ) ≤ axisConst H M := le_trans zero_le_one hC1
  intro h
  induction h with
  | zero =>
      rw [axisCoeff, pow_one]
      exact le_max_left _ _
  | succ h ih =>
      have hCp : (1 : ℝ) ≤ axisConst H M ^ (h + 1) := one_le_pow₀ hC1
      have hCp0 : (0 : ℝ) ≤ axisConst H M ^ (h + 1) := le_trans zero_le_one hCp
      rw [axisCoeff]
      refine max_le ?_ ?_
      · calc axisBase H ≤ axisConst H M := le_max_left _ _
          _ = axisConst H M ^ 1 := (pow_one _).symm
          _ ≤ axisConst H M ^ (h + 1 + 1) := pow_le_pow_right₀ hC1 (by omega)
      · have hA0 : (0 : ℝ) ≤ axisStep (H + 1) M := axisStep_nonneg _ _
        have hc0 : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
        have hD0 := axisCoeff_nonneg H M h
        have hstep : axisNext H M (axisCoeff H M h)
            ≤ (6 * axisStep (H + 1) M * (Fintype.card M : ℝ))
              * axisConst H M ^ (h + 1) := by
          rw [axisNext]
          have h2 : axisCoeff H M h + 2 ≤ 3 * axisConst H M ^ (h + 1) := by linarith
          nlinarith [mul_nonneg hA0 hc0]
        calc axisNext H M (axisCoeff H M h)
            ≤ (6 * axisStep (H + 1) M * (Fintype.card M : ℝ))
              * axisConst H M ^ (h + 1) := hstep
          _ ≤ axisConst H M * axisConst H M ^ (h + 1) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hCp0
          _ = axisConst H M ^ (h + 1 + 1) := by ring

/-- The bound is monotone in its coefficient. -/
lemma AxisBoundUpTo.mono {H h : ℕ} {D D' : ℝ} (hD : D ≤ D')
    (hb : AxisBoundUpTo M H h D) : AxisBoundUpTo M H h D' :=
  fun σ _ _ letter e r ℓ hh hbud =>
    (hb σ letter e r ℓ hh hbud).mono
      (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg _))

/-- **The regular-axis recurrence, in closed form** (the paper's
`prop:ags-axis-recurrence`).  Under the horizon budget `ℓ + h ≤ H`, an axis at
regular height `≤ h` has a packet of cost `C^{h+1}·√ℓ`, uniformly in the
alphabet. -/
theorem axisBoundUpTo_pow (H h : ℕ) :
    AxisBoundUpTo M H h (axisConst H M ^ (h + 1)) :=
  (axisBoundUpTo_axisCoeff H h).mono (axisCoeff_le_pow H M h)

/-- The same, unfolded to the shape a consumer calls it at. -/
theorem hasDual_axisPacket_of_regHeight {H h : ℕ} {σ : Type} [Fintype σ]
    [DecidableEq σ] (letter : σ → M) (e : M) (r : RState e) (ℓ : ℕ)
    (hh : regHeight e ≤ h) (hbud : ℓ + h ≤ H) :
    HasDual (axisPacket e letter r (n := ℓ))
      (axisConst H M ^ (h + 1) * Real.sqrt (ℓ : ℝ)) :=
  axisBoundUpTo_pow H h σ letter e r ℓ hh hbud

/-! ## The regular-action compiler by height

The paper states this separately from the axis recurrence, and it is the
form every consumer wants: not "one killed `R_e`-axis", but "an arbitrary
finite action all of whose component owners sit at bounded regular height".
The composition is short — choose owners, price each one's axis by the
recurrence, and hand the family to the action compiler — but it is the
endpoint the paper names, so it is stated. -/

/-- **Regular-action compiler by height** (the paper's
`prop:ags-action-height`).  If every component owner of `A` has
regular height at most `h`, then `A`'s own endpoint-and-first-death packet
costs `2|M|(C^{h+1} + 2)·√n` under the horizon budget `n + h ≤ H`.

The owners are chosen **internally**, so a caller supplies only the height
ceiling; the hypothesis quantifies over every `MinimalOwner`, which is what
makes that choice irrelevant.  Length zero is split off before the additive
constant is folded into the `√n` coefficient. -/
theorem hasDual_actionPacket_of_regHeight {X : Type} [Fintype X] [DecidableEq X]
    {σ : Type} [Fintype σ] [DecidableEq σ] (A : RightAction M (Option X))
    (letter : σ → M) (hnone : ∀ a, A.act none a = none) {H h n : ℕ}
    (hh : ∀ (z : X) (e : M), MinimalOwner A (some z) e → regHeight e ≤ h)
    (hbud : n + h ≤ H) (v₀ : X) :
    HasDual (fun x : Fin n → σ =>
        (liveCutIdx A v₀ letter x, cutState A v₀ letter x (liveCut A v₀ letter x)))
      (2 * (Fintype.card M : ℝ) * (axisConst H M ^ (h + 1) + 2)
        * Real.sqrt (n : ℝ)) := by
  classical
  have hC1 : 1 ≤ axisConst H M := one_le_axisConst H M
  have hCp : (1 : ℝ) ≤ axisConst H M ^ (h + 1) := one_le_pow₀ hC1
  have hcard : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
  obtain ⟨owner, hown⟩ : ∃ owner : X → M, ∀ z, MinimalOwner A (some z) (owner z) :=
    ⟨fun z => (exists_minimalOwner A (some z)).choose,
      fun z => (exists_minimalOwner A (some z)).choose_spec⟩
  have hpk : HasOwnerPackets letter owner n (axisConst H M ^ (h + 1)) := by
    refine ⟨le_trans zero_le_one hCp, fun y len hlen => ?_⟩
    exact hasDual_axisPacket_of_regHeight letter (owner y)
      ⟨owner y, rEq_refl (owner y)⟩ len (hh y (owner y) (hown y)) (by omega)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (hasDual_const (f := fun x : Fin 0 → σ =>
      (liveCutIdx A v₀ letter x, cutState A v₀ letter x (liveCut A v₀ letter x)))
      fun x y => ?_).mono (by simp)
    rw [show x = y from funext fun i => i.elim0]
  · refine (hasDual_actionPacket A letter owner hnone hown hpk v₀).mono ?_
    have h1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simpa using Real.sqrt_le_sqrt hn1
    nlinarith [mul_nonneg hcard (sub_nonneg.2 h1)]

end Recurrence

end MonoidProduct
