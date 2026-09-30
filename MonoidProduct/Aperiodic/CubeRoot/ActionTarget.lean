import MonoidProduct.Aperiodic.CubeRoot.ActionCompiler
import MonoidProduct.Aperiodic.CubeRoot.TargetAction
import MonoidProduct.Aperiodic.Examples
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The target test, through the action compiler

Part of the regular-action simulation (Section `sec:ags-actions` of the paper).
The target-reachability action of `TargetAction.lean` turns the
equality `φ(w) = t` into an **endpoint computation**, and the action compiler
(`ActionCompiler.lean`) computes that endpoint from axis packets of the
action's regular owners.  This file is the
join.

**The decoder must read the cut as well as the state.**  The compiler's packet
returns the greatest live cut together with the state *there*, so on death it
reports the **last live predecessor**, not the dead state.  The target test is
therefore

    `φ(w) = t   ↔   cut = n ∧ state = some t`,

and comparing only the state is unsound.  The `N₂` regression at the end
pins that: with target `a` and the word `[a, a]` the run dies at the second
letter and the predecessor it returns is `a` itself, while the product is `0`.

**Cost.**  The test goes through `hasDual_of_transcript_determined`, not
through `hasDual_actionPacket`: the packet and the test are two different
things the transcript determines, and each should pay the postcomposition
once.  Routing the test through the packet would pay it twice.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Target

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M]
variable (letter : σ → M)

/-- The target action's run from `1`, cut by cut. -/
lemma cutState_targetAction (t : M) {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    cutState (targetAction t) (targetStart t) letter x j
      = if h : RLe t (winProd letter x 0 j) then
          some ⟨winProd letter x 0 j, h⟩ else none := by
  rw [cutState, targetAction_act, targetStep_some]
  simp only [targetStart_val, one_mul]

/-- **The decoder.**  `φ(w) = t` exactly when the packet's cut is the whole
word *and* its state is `t`.  The cut is not redundant: on death the state is
the last live predecessor, which may itself be `t` — see `n2_state_alone_unsound`. -/
theorem eqProd_iff_target (t : M) {n : ℕ} (x : Fin n → σ) :
    eqProd letter t x = true
      ↔ ((liveCutIdx (targetAction t) (targetStart t) letter x : ℕ) = n
          ∧ cutState (targetAction t) (targetStart t) letter x
              (liveCut (targetAction t) (targetStart t) letter x)
            = some ⟨t, rLe_refl t⟩) := by
  constructor
  · intro h
    rw [eqProd_eq_true] at h
    have hn : cutState (targetAction t) (targetStart t) letter x n
        = some ⟨t, rLe_refl t⟩ := by
      rw [cutState_targetAction letter t x n, ← wordProd_eq_winProd, h,
        dif_pos (rLe_refl t)]
    have hcut : liveCut (targetAction t) (targetStart t) letter x = n :=
      le_antisymm (liveCut_le _ _ _ _)
        ((liveSet (targetAction t) (targetStart t) letter x).le_max' n
          ((mem_liveSet (targetAction t) (targetStart t) letter).2
            ⟨le_rfl, by rw [hn]; rfl⟩))
    exact ⟨by rw [liveCutIdx_val, hcut], by rw [hcut]; exact hn⟩
  · rintro ⟨hcut, hst⟩
    rw [liveCutIdx_val] at hcut
    rw [hcut, cutState_targetAction letter t x n] at hst
    by_cases hr : RLe t (winProd letter x 0 n)
    · rw [dif_pos hr] at hst
      rw [eqProd_eq_true, wordProd_eq_winProd]
      exact congrArg Subtype.val (Option.some_injective _ hst)
    · rw [dif_neg hr] at hst
      exact absurd hst (by simp)

/-- Every state of the target action has an owner. -/
theorem exists_targetOwner (t : M) :
    ∃ owner : TState t → M,
      ∀ z : TState t, MinimalOwner (targetAction t) (some z) (owner z) := by
  classical
  exact ⟨fun z => (exists_minimalOwner (targetAction t) (some z)).choose,
    fun z => (exists_minimalOwner (targetAction t) (some z)).choose_spec⟩

/-- **Item 7c.**  Axis packets for the regular owners of the target action
compile into the target test itself.  The postcomposition is paid **once**:
the test is read off the transcript directly, not off the packet. -/
theorem hasDual_eqProd_of_ownerPackets {t : M} {owner : TState t → M}
    (hown : ∀ z : TState t, MinimalOwner (targetAction t) (some z) (owner z))
    {n : ℕ} {B : ℝ} (hpk : HasOwnerPackets letter owner n B) :
    HasDual (eqProd (n := n) letter t)
      (2 * ((Fintype.card M : ℝ) * (B * Real.sqrt (n : ℝ) + 2))) := by
  refine hasDual_of_transcript_determined (targetAction t) letter owner hpk
    (targetStart t) (Fintype.card M) _ fun x x' hxx' => ?_
  have hpd := packet_determined (targetAction t) letter owner (fun _ => rfl) hown
    (targetStart t) le_rfl x x' hxx'
  have h1 := congrArg Prod.fst hpd
  have h2 := congrArg Prod.snd hpd
  simp only at h1 h2
  rw [Bool.eq_iff_iff, eqProd_iff_target letter t x, eqProd_iff_target letter t x',
    h1, h2]

/-- The same, normalized as a coefficient times `√n`.

**Length zero is split off**, and has to be: the empty word's product is `1`,
so the test is constant there and costs nothing, while the raw bound
`2|M|(B·0 + 2)` is positive.  Any conversion of a `c₁√n + c₀` bound into a
`C√n` one has to make that split. -/
theorem hasDual_eqProd_sqrt {t : M} {owner : TState t → M}
    (hown : ∀ z : TState t, MinimalOwner (targetAction t) (some z) (owner z))
    {n : ℕ} {B : ℝ} (hpk : HasOwnerPackets letter owner n B) :
    HasDual (eqProd (n := n) letter t)
      (2 * (Fintype.card M : ℝ) * (B + 2) * Real.sqrt (n : ℝ)) := by
  have hB := hpk.1
  have hcard : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (hasDual_const (f := eqProd (n := 0) letter t) fun x y => ?_).mono (by simp)
    rw [show x = y from funext fun i => i.elim0]
  · refine (hasDual_eqProd_of_ownerPackets letter hown hpk).mono ?_
    have h1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simpa using Real.sqrt_le_sqrt hn1
    nlinarith [mul_nonneg hcard (sub_nonneg.2 h1)]

end Target

/-! ## Why the decoder must check the cut

The packet reports the **last live predecessor** when the action dies.  In `N₂`
with target `a` and the word `[a, a]`, the run is live at cut `1` with state
`a`, and letter `1` kills it — so the packet returns `(1, some a)` while the
product is `0`.  A decoder comparing only the state would accept. -/

section Regression

/-- The word `[a, a]` over `N₂`. -/
def n2word : Fin 2 → N2 := ![N2.a, N2.a]

lemma n2_win1 : winProd (id : N2 → N2) n2word 0 1 = N2.a := by decide

lemma n2_win2 : winProd (id : N2 → N2) n2word 0 2 = N2.zero := by decide

lemma n2_not_rLe : ¬ RLe N2.a N2.zero := by decide

/-- The run dies at the second letter. -/
theorem n2_liveCut : liveCut (targetAction N2.a) (targetStart N2.a) id n2word = 1 := by
  refine liveCut_eq_of (targetAction N2.a) id (fun _ => rfl) (targetStart N2.a)
    n2word (q := 1) (by omega) ?_ (Or.inr ?_)
  · rw [cutState_targetAction, n2_win1, dif_pos (rLe_refl N2.a)]
    rfl
  · rw [cutState_targetAction, n2_win2, dif_neg n2_not_rLe]

/-- **The state alone is not a decoder.**  The packet's state is `some a`, yet
the product is `0`. -/
theorem n2_state_alone_unsound :
    cutState (targetAction N2.a) (targetStart N2.a) id n2word
        (liveCut (targetAction N2.a) (targetStart N2.a) id n2word)
      = some ⟨N2.a, rLe_refl N2.a⟩
    ∧ wordProd (id : N2 → N2) n2word ≠ N2.a := by
  refine ⟨?_, by decide⟩
  rw [n2_liveCut, cutState_targetAction, n2_win1, dif_pos (rLe_refl N2.a)]

/-- **The cut is what rejects it.** -/
theorem n2_decoder_rejects :
    (liveCutIdx (targetAction N2.a) (targetStart N2.a) id n2word : ℕ) ≠ 2 := by
  rw [liveCutIdx_val, n2_liveCut]
  omega

/-- And so the target test is `false`, as it must be. -/
theorem n2_eqProd_false : eqProd (id : N2 → N2) N2.a n2word = false := by
  rcases h : eqProd (id : N2 → N2) N2.a n2word with _ | _
  · rfl
  · exact absurd ((eqProd_iff_target id N2.a n2word).1 h).1 n2_decoder_rejects

end Regression

/-! ## Wrappers for the recurrence

Four small facts, in the shape 7d consumes them: the target action's state
space is bounded by the monoid, so the target test has an `|M|`-uniform cost;
the regular height is constant along an `R`-class; and the target action's
owners drop that height. -/

section Wrappers

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] [IsAperiodicMonoid M]

/-- The target action has at most `|M| + 1` states.  Recorded for what it is;
the compiler's *cost* uses the sharper reachable-orbit bound
`card_reachSet_le_card_monoid` instead, which is why nothing downstream carries
the `+ 1`. -/
lemma card_option_tState_le (t : M) :
    Fintype.card (Option (TState t)) ≤ Fintype.card M + 1 := by
  rw [Fintype.card_option]
  exact Nat.succ_le_succ (Fintype.card_subtype_le _)

/-- **The target test, uniformly in the target** — the name the recurrence
calls.  Since the compiler's level count is the reachable-orbit bound `|M|`,
the cost never mentions `TState t` at all, so this *is* `hasDual_eqProd_sqrt`;
it is kept as a separate name because uniformity in the target is the property
the recursion depends on, not an incidental one. -/
theorem hasDual_eqProd_uniform (letter : σ → M) {t : M} {owner : TState t → M}
    (hown : ∀ z : TState t, MinimalOwner (targetAction t) (some z) (owner z))
    {n : ℕ} {B : ℝ} (hpk : HasOwnerPackets letter owner n B) :
    HasDual (eqProd (n := n) letter t)
      (2 * (Fintype.card M : ℝ) * (B + 2) * Real.sqrt (n : ℝ)) :=
  hasDual_eqProd_sqrt letter hown hpk

/-- **The regular height is constant along an `R`-class**: `R`-equivalent
elements are `J`-equivalent, and the height sees only the `J`-class. -/
lemma regHeight_rState {e : M} (r : RState e) : regHeight r.val = regHeight e :=
  regHeight_congr (twoIdeal_eq_of_rEq r.2)

/-- **The height drop, packaged for the axis.**  Running the target action of a
strict two-sided parent `t` of a state of the `R_e`-axis, every owner of that
action has regular height strictly below `e`'s.  This is what makes the
recurrence descend. -/
theorem regHeight_targetOwner_lt {e : M} (r : RState e) {t : M}
    (ht : twoIdeal r.val ⊂ twoIdeal t) {p : TState t} {e' : M}
    (hown : MinimalOwner (targetAction t) (some p) e') :
    regHeight e' < regHeight e := by
  have h := (regHeight_drop hown ht).2
  rwa [regHeight_rState r] at h

end Wrappers

end MonoidProduct
