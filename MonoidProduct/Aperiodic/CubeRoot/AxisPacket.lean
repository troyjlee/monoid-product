import MonoidProduct.Aperiodic.CubeRoot.ActionCost
import MonoidProduct.Aperiodic.CubeRoot.StrictParent
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The killed `R_e`-axis packet

The first step of the action compiler.  `ActionCost.lean` priced an axis packet from **one supplied
primitive** — a dual for the equality test "the state after `j` letters is
`s`".  On the killed axis of an `R`-class that primitive is not abstract: the
state after `j` letters is `r · φ(x₀⋯x_{j-1})` while that stays in `R_e`, so
the test is literally the **fixed-left-context test** of `StrictParent.lean` read on the
prefix of length `j`,

    `x ↦ [r · φ(x₀⋯x_{j-1}) = s]`,

and freezing the coordinates past `j` costs nothing.  So the axis packet
of Section `sec:ags-actions` of the paper is priced by the localized AGS step, and this file
is the bridge.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Axis

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M]

/-! ## The fixed-left-context test on a prefix -/

/-- **The fixed-context test on a prefix window.**  A test about the first `j`
letters of a length-`n` word costs what it costs on a word of length `j`:
`HasDual.pullback` freezes the rest. -/
theorem hasDual_eqProdLeftPrefix (letter : σ → M) (a m : M) {n j : ℕ} (hj : j ≤ n)
    {c : ℝ} (h : HasDual (fun y : Fin j → σ => eqProdLeft letter a m y) c) :
    HasDual (fun x : Fin n → σ => decide (a * winProd letter x 0 j = m)) c := by
  have hsum : 0 + j ≤ n := by omega
  refine (h.pullback (winEmb_injective hsum)).ofEq fun x => ?_
  rw [pullbackFun_apply]
  simp only [eqProdLeft, wordProd_winEmb letter x hsum, Nat.zero_add]

/-! ## The cut test of the killed axis *is* that test -/

variable (e : M)

/-- The state of the killed axis after `j` letters, spelled out. -/
lemma cutState_killedAction (r : RState e) (letter : σ → M) {n : ℕ}
    (x : Fin n → σ) (j : ℕ) :
    cutState (killedAction e) r letter x j
      = if h : REq (r.val * winProd letter x 0 j) e then
          some ⟨r.val * winProd letter x 0 j, h⟩ else none := rfl

/-- **The identification.**  The one-hot cut test of the killed axis at `e` is
the fixed-left-context test with context `r`, target `s`, read on the prefix of
length `j`.  No liveness side condition survives: a target `s` is in `R_e` by
construction, so the product landing on it is already live. -/
theorem cutTest_killedAction (r : RState e) (letter : σ → M) {n : ℕ}
    (x : Fin n → σ) (j : ℕ) (s : RState e) :
    cutTest (killedAction e) r letter x j s
      = decide (r.val * winProd letter x 0 j = s.val) := by
  rw [cutTest, cutState_killedAction]
  by_cases h : REq (r.val * winProd letter x 0 j) e
  · rw [dif_pos h]
    simp [Subtype.ext_iff]
  · rw [dif_neg h]
    refine (decide_eq_false ?_).trans (decide_eq_false ?_).symm
    · exact fun hc => absurd hc (by simp)
    · exact fun hc => h (by rw [hc]; exact s.2)

/-! ## The packet -/

/-- **The axis packet at `e` from the incoming state `r`**: the greatest live
cut of the killed `R_e`-action together with the exact state there.  This is
the paper's `R_e`-axis packet from `r` (Section `sec:ags-actions`), as a
function rather than a cost. -/
noncomputable def axisPacket (letter : σ → M) (r : RState e) {n : ℕ}
    (x : Fin n → σ) : Fin (n + 1) × Option (RState e) :=
  (liveCutIdx (killedAction e) r letter x,
    cutState (killedAction e) r letter x (liveCut (killedAction e) r letter x))

/-- **The axis packet, priced by the fixed-context tests.**  The assembly of
`ActionCost.lean`, with its abstract primitive discharged by `cutTest_killedAction`. -/
theorem hasDual_axisPacket_killed (letter : σ → M) (r : RState e) {n : ℕ} {c : ℝ}
    (hc : 0 ≤ c)
    (htest : ∀ j, j ≤ n → ∀ s : RState e,
      HasDual (fun y : Fin j → σ => eqProdLeft letter r.val s.val y) c) :
    HasDual (axisPacket e letter r (n := n))
      ((Nat.clog 2 (n + 1) : ℝ)
          * (c * (24 * Real.sqrt ((Fintype.card (RState e) : ℝ) + 1)))
        + 2 * ((Fintype.card (RState e) : ℝ) * c)) :=
  hasDual_axisPacket (killedAction e) r letter (fun _ => rfl) hc
    fun j hj s =>
      (hasDual_eqProdLeftPrefix letter r.val s.val hj (htest j hj s)).ofEq
        fun x => (cutTest_killedAction e r letter x j s).symm

/-- On the empty word the packet is constant. -/
theorem hasDual_axisPacket_zero (letter : σ → M) (r : RState e) :
    HasDual (axisPacket e letter r (n := 0)) 0 :=
  hasDual_packet_zero_length (killedAction e) r letter

end Axis

/-! ## The normalized axis-packet cost

The packet is priced in the same normal form as everything else in the AGS
cone: a coefficient times `√ℓ`, uniformly over the horizon.  `axisStep` is the
multiplier the axis pays over the localized AGS step it calls — one
`⌈log₂⌉`-deep threshold search over the dead-prefix predicate, plus one
one-hot family for the state — and the factor `2` absorbs the horizon shift
`√(ℓ+1) ≤ 2√ℓ` created by the virtual prepend. -/

/-- The multiplier one regular height costs an axis packet. -/
noncomputable def axisStep (N : ℕ) (M : Type) [Fintype M] : ℝ :=
  2 * agsStep N M
    * ((Nat.clog 2 (N + 1) : ℝ) * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
        + 2 * (Fintype.card M : ℝ))

lemma one_le_axisStep (N : ℕ) (M : Type) [Fintype M] [Nonempty M] :
    1 ≤ axisStep N M := by
  have hA : (1 : ℝ) ≤ agsStep N M := one_le_agsStep N M
  have hC : (1 : ℝ) ≤ (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  have hL : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) := by
    positivity
  rw [axisStep]
  nlinarith

/-- **The AGS step is monotone in the horizon** — both its factors are, through
`Nat.clog`. -/
lemma agsStep_mono_horizon {N₁ N₀ : ℕ} (h : N₁ ≤ N₀) (M : Type) [Fintype M] :
    agsStep N₁ M ≤ agsStep N₀ M := by
  have hc : (Nat.clog 2 (N₁ + 1) : ℝ) ≤ (Nat.clog 2 (N₀ + 1) : ℝ) := by
    exact_mod_cast Nat.clog_mono_right 2 (by omega)
  have h0 : (0 : ℝ) ≤ (Nat.clog 2 (N₁ + 1) : ℝ) := Nat.cast_nonneg _
  have hsq : ((Nat.clog 2 (N₁ + 1) : ℝ) + 2) ^ 2
      ≤ ((Nat.clog 2 (N₀ + 1) : ℝ) + 2) ^ 2 := by nlinarith
  have hA : (0 : ℝ) ≤ 2 ^ 40 * ((Fintype.card M : ℝ) + 1) ^ 5 := by positivity
  rw [agsStep, agsStep]
  exact mul_le_mul_of_nonneg_left hsq hA

/-- **The axis step is monotone in the horizon.**  A shorter horizon is never
more expensive, which is what lets one certificate cover every `ℓ ≤ n₀`. -/
lemma axisStep_mono_horizon {N₁ N₀ : ℕ} (h : N₁ ≤ N₀) (M : Type) [Fintype M] :
    axisStep N₁ M ≤ axisStep N₀ M := by
  have hags := agsStep_mono_horizon h M
  have hags0 : (0 : ℝ) ≤ agsStep N₁ M := le_trans zero_le_one (one_le_agsStep N₁ M)
  have hc : (Nat.clog 2 (N₁ + 1) : ℝ) ≤ (Nat.clog 2 (N₀ + 1) : ℝ) := by
    exact_mod_cast Nat.clog_mono_right 2 (by omega)
  have hs : (0 : ℝ) ≤ 24 * Real.sqrt ((Fintype.card M : ℝ) + 1) := by positivity
  have h0 : (0 : ℝ) ≤ (Nat.clog 2 (N₁ + 1) : ℝ) := Nat.cast_nonneg _
  have hcard : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
  rw [axisStep, axisStep]
  refine mul_le_mul (by linarith) ?_ (by nlinarith) (by linarith)
  nlinarith

lemma axisStep_nonneg (N : ℕ) (M : Type) [Fintype M] : 0 ≤ axisStep N M := by
  have hA : (1 : ℝ) ≤ agsStep N M := one_le_agsStep N M
  rw [axisStep]
  have : (0 : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
      + 2 * (Fintype.card M : ℝ) := by positivity
  nlinarith

section Normalized

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M]

/-- **A nonidentity `R`-class has no identity state.**  Only `1` generates the
whole monoid as a right ideal, so `REq s e` with `s = 1` would force `e = 1` —
which is what lets the AGS step, whose target must differ from `1`, run at
every state of the axis. -/
lemma RState.val_ne_one {e : M} (he : e ≠ 1) (s : RState e) : s.val ≠ 1 := by
  intro h
  refine he (eq_one_of_rightIdeal_eq_univ ?_)
  have hs : rightIdeal s.val = rightIdeal e := s.2
  rw [← hs, h, rightIdeal_one]

/-- **The axis packet from the localized contract.**  Certificates for the
strict two-sided parents of every state of the axis — over the alphabet
augmented by the incoming context — price the whole `R_e`-axis packet, in the
`D·√ℓ` normal form, uniformly over the horizon. -/
theorem hasDual_axisPacket_of_strictParentIH (letter : σ → M) {e : M} (he : e ≠ 1)
    (r : RState e) {n₀ : ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hIH : ∀ s : RState e,
      StrictParentIH (prependLetter letter r.val) s.val (n₀ + 1) D)
    {ℓ : ℕ} (hℓ : ℓ ≤ n₀) :
    HasDual (axisPacket e letter r (n := ℓ))
      (D * axisStep (n₀ + 1) M * Real.sqrt (ℓ : ℝ)) := by
  have hA : (1 : ℝ) ≤ agsStep (n₀ + 1) M := one_le_agsStep _ _
  have hD0 : (0 : ℝ) ≤ D := le_trans zero_le_one hD
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓpos
  · exact (hasDual_axisPacket_zero e letter r).mono (by simp)
  set c : ℝ := D * agsStep (n₀ + 1) M * Real.sqrt ((ℓ : ℝ) + 1) with hc_def
  have hc : 0 ≤ c := by
    rw [hc_def]
    exact mul_nonneg (mul_nonneg hD0 (le_trans zero_le_one hA)) (Real.sqrt_nonneg _)
  have htest : ∀ j, j ≤ ℓ → ∀ s : RState e,
      HasDual (fun y : Fin j → σ => eqProdLeft letter r.val s.val y) c := by
    intro j hj s
    refine (hasDual_eqProdLeft_of_strictParentIH letter r.val
      (RState.val_ne_one he s) hD0 ((hIH s).mono_horizon (by omega))).mono ?_
    refine le_trans (stepBound_le M (n := j + 1) (N := n₀ + 1) (by omega) (by omega) hD) ?_
    rw [hc_def]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hD0 (le_trans zero_le_one hA))
    refine Real.sqrt_le_sqrt ?_
    push_cast
    have : (j : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hj
    linarith
  refine (hasDual_axisPacket_killed e letter r hc htest).mono ?_
  have hK : (Fintype.card (RState e) : ℝ) ≤ (Fintype.card M : ℝ) := by
    exact_mod_cast Fintype.card_subtype_le (fun r : M => REq r e)
  have hsqK : Real.sqrt ((Fintype.card (RState e) : ℝ) + 1)
      ≤ Real.sqrt ((Fintype.card M : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have hlog : (Nat.clog 2 (ℓ + 1) : ℝ) ≤ (Nat.clog 2 (n₀ + 1 + 1) : ℝ) := by
    exact_mod_cast Nat.clog_mono_right 2 (by omega)
  have hS1 : Real.sqrt ((ℓ : ℝ) + 1) ≤ 2 * Real.sqrt (ℓ : ℝ) := by
    have hone : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓpos
    calc Real.sqrt ((ℓ : ℝ) + 1) ≤ Real.sqrt ((2 : ℝ) ^ 2 * (ℓ : ℝ)) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * Real.sqrt (ℓ : ℝ) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hP : (0 : ℝ) ≤ (Nat.clog 2 (n₀ + 1 + 1) : ℝ)
      * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2 * (Fintype.card M : ℝ) := by
    positivity
  have hclaim : (Nat.clog 2 (ℓ + 1) : ℝ)
        * (24 * Real.sqrt ((Fintype.card (RState e) : ℝ) + 1))
        + 2 * (Fintype.card (RState e) : ℝ)
      ≤ (Nat.clog 2 (n₀ + 1 + 1) : ℝ)
        * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2 * (Fintype.card M : ℝ) := by
    have h1 : (Nat.clog 2 (ℓ + 1) : ℝ)
          * (24 * Real.sqrt ((Fintype.card (RState e) : ℝ) + 1))
        ≤ (Nat.clog 2 (n₀ + 1 + 1) : ℝ)
          * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) :=
      mul_le_mul hlog (by linarith) (by positivity) (by positivity)
    linarith
  rw [axisStep, show (Nat.clog 2 (ℓ + 1) : ℝ)
        * (c * (24 * Real.sqrt ((Fintype.card (RState e) : ℝ) + 1)))
      + 2 * ((Fintype.card (RState e) : ℝ) * c)
    = c * ((Nat.clog 2 (ℓ + 1) : ℝ)
        * (24 * Real.sqrt ((Fintype.card (RState e) : ℝ) + 1))
      + 2 * (Fintype.card (RState e) : ℝ)) from by ring]
  calc c * ((Nat.clog 2 (ℓ + 1) : ℝ)
          * (24 * Real.sqrt ((Fintype.card (RState e) : ℝ) + 1))
        + 2 * (Fintype.card (RState e) : ℝ))
      ≤ c * ((Nat.clog 2 (n₀ + 1 + 1) : ℝ)
          * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
        + 2 * (Fintype.card M : ℝ)) := mul_le_mul_of_nonneg_left hclaim hc
    _ = D * agsStep (n₀ + 1) M * Real.sqrt ((ℓ : ℝ) + 1)
        * ((Nat.clog 2 (n₀ + 1 + 1) : ℝ)
          * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
        + 2 * (Fintype.card M : ℝ)) := by rw [hc_def]
    _ ≤ D * agsStep (n₀ + 1) M * (2 * Real.sqrt (ℓ : ℝ))
        * ((Nat.clog 2 (n₀ + 1 + 1) : ℝ)
          * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
        + 2 * (Fintype.card M : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS1
          (mul_nonneg hD0 (le_trans zero_le_one hA))) hP
    _ = D * (2 * agsStep (n₀ + 1) M
        * ((Nat.clog 2 (n₀ + 1 + 1) : ℝ)
          * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))
        + 2 * (Fintype.card M : ℝ))) * Real.sqrt (ℓ : ℝ) := by ring

end Normalized

/-! ## The base of the recurrence: the axis at the identity

`regHeight e = 0` says `e = 1` (`regHeight_eq_zero_iff`), and the `R`-class of
`1` is `{1}` — only the identity generates the whole monoid as a right ideal.
So the killed axis at `1` dies at the first letter whose value is not `1`, and
the whole packet is a **minimum finding over the coordinates**: no AGS step and
no recursion.  This is the base case of the paper's regular-axis recurrence
(`prop:ags-axis-recurrence`). -/

/-- The base coefficient: what the identity axis costs, normalized. -/
noncomputable def axisBase (N : ℕ) : ℝ := 96 * (48 * (Nat.clog 2 (N + 1) : ℝ) + 2)

lemma axisBase_nonneg (N : ℕ) : 0 ≤ axisBase N := by
  rw [axisBase]; positivity

/-- The base case's arithmetic, with every quantity abstract: one threshold
level costs `L·(c·24T)`, the state costs `2(1·c)`, and `c = 48·S1` with
`S1 ≤ 2S` and `T ≤ 2`. -/
private lemma axisBase_arith {L L₀ S S1 T : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ L₀)
    (hS : 0 ≤ S) (hS1 : 0 ≤ S1) (hT2 : T ≤ 2) (hS12 : S1 ≤ 2 * S) :
    L * (2 * (24 * S1) * (24 * T)) + 2 * (1 * (2 * (24 * S1)))
      ≤ 96 * (48 * L₀ + 2) * S := by
  have ha : L * S1 * T ≤ L * S1 * 2 :=
    mul_le_mul_of_nonneg_left hT2 (mul_nonneg hL0 hS1)
  have hb : L * S1 ≤ L * (2 * S) := mul_le_mul_of_nonneg_left hS12 hL0
  have hc : L * S ≤ L₀ * S := mul_le_mul_of_nonneg_right hL hS
  nlinarith [ha, hb, hc, hS12]

section Base

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M]

/-- **The identity axis has one state.** -/
lemma RState.val_eq_one (s : RState (1 : M)) : s.val = 1 :=
  eq_one_of_rightIdeal_eq_univ (by rw [s.2, rightIdeal_one])

lemma card_rState_one : Fintype.card (RState (1 : M)) = 1 :=
  Fintype.card_eq_one_iff.2 ⟨⟨1, rfl⟩, fun s => Subtype.ext (RState.val_eq_one s)⟩

/-- The search for a nonidentity letter, as a `Finset.sup`. -/
lemma sup_ne_one_eq_true (letter : σ → M) {j : ℕ} (y : Fin j → σ) :
    ((Finset.univ : Finset (Fin j)).sup fun i => decide (letter (y i) ≠ 1)) = true
      ↔ ∃ i, letter (y i) ≠ 1 := by
  rw [sup_bool_eq_true]
  constructor
  · rintro ⟨i, -, hi⟩
    exact ⟨i, by simpa using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, by simpa using hi⟩

/-- **The identity target test is the complement of that search** (the paper's
`prop:identity`: a product is `1` exactly when every letter is). -/
lemma eqProdOne_eq_not_sup (letter : σ → M) {j : ℕ} (y : Fin j → σ) :
    decide (wordProd letter y = 1)
      = !((Finset.univ : Finset (Fin j)).sup fun i => decide (letter (y i) ≠ 1)) := by
  rcases hs : ((Finset.univ : Finset (Fin j)).sup fun i =>
      decide (letter (y i) ≠ 1)) with _ | _
  · simp only [Bool.not_false]
    refine decide_eq_true ?_
    rw [wordProd, orderedProd_eq_one_iff]
    intro i
    by_contra hi
    exact absurd ((sup_ne_one_eq_true letter y).2 ⟨i, hi⟩) (by rw [hs]; simp)
  · simp only [Bool.not_true]
    refine decide_eq_false ?_
    intro hw
    obtain ⟨i, hi⟩ := (sup_ne_one_eq_true letter y).1 hs
    rw [wordProd, orderedProd_eq_one_iff] at hw
    exact hi (hw i)

/-- **The identity target test, priced**: one square-root search. -/
theorem hasDual_eqProdOne (letter : σ → M) {j : ℕ} :
    HasDual (fun y : Fin j → σ => decide (wordProd letter y = 1))
      (2 * (24 * Real.sqrt ((j : ℝ) + 1))) := by
  have hsup : HasDual (fun y : Fin j → σ =>
      (Finset.univ : Finset (Fin j)).sup fun i => decide (letter (y i) ≠ 1))
      (2 * (24 * Real.sqrt (((Finset.univ : Finset (Fin j)).card : ℝ) + 1))) :=
    HasDual.finsetSup Finset.univ (by norm_num)
      fun i _ => hasDual_ofCoord i fun cc => decide (letter cc ≠ 1)
  rw [Finset.card_univ, Fintype.card_fin] at hsup
  refine hsup.ofKer fun x y => ?_
  rw [eqProdOne_eq_not_sup, eqProdOne_eq_not_sup]
  cases (Finset.univ : Finset (Fin j)).sup fun i => decide (letter (x i) ≠ 1) <;>
    cases (Finset.univ : Finset (Fin j)).sup fun i => decide (letter (y i) ≠ 1) <;>
      simp

/-- **The base case of the axis recurrence.**  The identity axis costs one
square-root search per threshold level and one for the state, with no call to
the AGS step at all. -/
theorem hasDual_axisPacket_one (letter : σ → M) (r : RState (1 : M)) {n₀ ℓ : ℕ}
    (hℓ : ℓ ≤ n₀) :
    HasDual (axisPacket (1 : M) letter r (n := ℓ))
      (axisBase n₀ * Real.sqrt (ℓ : ℝ)) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓpos
  · exact (hasDual_axisPacket_zero (1 : M) letter r).mono (by simp)
  set c : ℝ := 2 * (24 * Real.sqrt ((ℓ : ℝ) + 1)) with hc_def
  have hc : 0 ≤ c := by rw [hc_def]; positivity
  have htest : ∀ j, j ≤ ℓ → ∀ s : RState (1 : M),
      HasDual (fun y : Fin j → σ => eqProdLeft letter r.val s.val y) c := by
    intro j hj s
    refine ((hasDual_eqProdOne letter (j := j)).ofEq fun y => ?_).mono ?_
    · rw [eqProdLeft, RState.val_eq_one r, RState.val_eq_one s, one_mul]
    · rw [hc_def]
      have hjl : Real.sqrt ((j : ℝ) + 1) ≤ Real.sqrt ((ℓ : ℝ) + 1) := by
        refine Real.sqrt_le_sqrt ?_
        have : (j : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hj
        linarith
      linarith
  refine (hasDual_axisPacket_killed (1 : M) letter r hc htest).mono ?_
  have hsqrt2 : Real.sqrt ((1 : ℝ) + 1) ≤ 2 := by
    have h1 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h1]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hS1 : Real.sqrt ((ℓ : ℝ) + 1) ≤ 2 * Real.sqrt (ℓ : ℝ) := by
    have hone : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓpos
    calc Real.sqrt ((ℓ : ℝ) + 1) ≤ Real.sqrt ((2 : ℝ) ^ 2 * (ℓ : ℝ)) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * Real.sqrt (ℓ : ℝ) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hlog : (Nat.clog 2 (ℓ + 1) : ℝ) ≤ (Nat.clog 2 (n₀ + 1) : ℝ) := by
    exact_mod_cast Nat.clog_mono_right 2 (by omega)
  rw [card_rState_one, axisBase, hc_def, Nat.cast_one]
  exact axisBase_arith (Nat.cast_nonneg _) hlog (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hsqrt2 hS1

end Base

end MonoidProduct
