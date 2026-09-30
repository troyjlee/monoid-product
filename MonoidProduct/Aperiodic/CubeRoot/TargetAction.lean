import MonoidProduct.Aperiodic.CubeRoot.FiniteAction
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The target-reachability action, and the regular-height drop

The paper's target-reachability action (`lem:ags-target-action`).  To decide
`φ(w) = t` one runs the word against the action whose live states are the
elements that can **still reach** `t` on the right,

    `A_t = {p : t ∈ pM}`,

killed the moment reachability is lost.  Two facts make it useful:

* the run from `1` is exactly `φ(w)` when the target is still reachable and
  dead otherwise, so `φ(w) = t` **iff** the endpoint is `t`
  (`targetAction_run_eq_iff`) — the equality test becomes an endpoint
  computation, which is what the action compiler can price;
* on a live state `p` with an owner `e` **at `p`**, the ideals chain

      `MtM ⊆ MpM ⊆ MeM`,

  so any regular class strictly below `t` is strictly below `e`, and the
  regular height drops (`regHeight_drop`).  That is the descent the
  regular-axis recurrence runs on.

A caution the paper's phrasing compresses: "the owner is a return
element at `p`" means the owner taken with **base point `p` itself**.  An
owner at some other point `v` of the same component need not satisfy
`p · e = p`: in `U₂` the two right zeros are `R`-equivalent while
`e₁ · e₂ = e₂ ≠ e₁`.  The statements below therefore take
`MinimalOwner (targetAction t) (some p) e` directly.
-/

namespace MonoidProduct

section Target

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- The live states of the target action: those that can still reach `t`. -/
abbrev TState (t : M) : Type := {p : M // RLe t p}

variable (t : M)

/-- One step of the **target-reachability action**. -/
def targetStep : Option (TState t) → M → Option (TState t)
  | none, _ => none
  | some p, a => if h : RLe t (p.val * a) then some ⟨p.val * a, h⟩ else none

@[simp] lemma targetStep_none (a : M) : targetStep t none a = none := rfl

lemma targetStep_some (p : TState t) (a : M) :
    targetStep t (some p) a
      = if h : RLe t (p.val * a) then some ⟨p.val * a, h⟩ else none := rfl

/-- **Loss of reachability is permanent**: `(pab)M ⊆ (pa)M`, so a
continuation cannot bring the target back. -/
theorem targetStep_dead {p : TState t} {a : M} (h : ¬ RLe t (p.val * a)) (b : M) :
    ¬ RLe t (p.val * a * b) := by
  intro hab
  exact h (rLe_iff_subset.2
    ((rLe_iff_subset.1 hab).trans (rightIdeal_mul_subset _ _)))

/-- **The target-reachability action.** -/
def targetAction : RightAction M (Option (TState t)) where
  act := targetStep t
  act_one := by
    rintro (_ | p)
    · rfl
    · rw [targetStep_some, dif_pos (by rw [mul_one]; exact p.2)]
      simp
  act_mul := by
    rintro (_ | p) a b
    · rfl
    · rw [targetStep_some]
      by_cases h : RLe t (p.val * a)
      · rw [dif_pos h, targetStep_some, targetStep_some]
        simp only [mul_assoc]
      · rw [dif_neg h, targetStep_none, targetStep_some,
          dif_neg (by rw [← mul_assoc]; exact targetStep_dead t h b)]

@[simp] lemma targetAction_act (s : Option (TState t)) (a : M) :
    (targetAction t).act s a = targetStep t s a := rfl

/-- The initial state `1`: the target is reachable from it, being `1 · t`. -/
def targetStart : TState t := ⟨1, rLe_iff_exists.2 ⟨t, one_mul t⟩⟩

@[simp] lemma targetStart_val : (targetStart t).val = 1 := rfl

/-- **The endpoint formula**: from `1`, the run on `w` is `φ(w)` when the
target is still reachable from it, and dead otherwise. -/
theorem targetAction_run_start (w : List M) :
    (targetAction t).run (some (targetStart t)) w
      = if h : RLe t w.prod then some ⟨w.prod, h⟩ else none := by
  rw [RightAction.run_eq_act_prod, targetAction_act, targetStep_some]
  simp only [targetStart_val, one_mul]

/-- **The equality test is an endpoint computation**: `φ(w) = t` exactly when
the run ends at `t`.  This is what lets the action compiler price a
strict-parent equality test. -/
theorem targetAction_run_eq_iff (w : List M) :
    (targetAction t).run (some (targetStart t)) w
        = some ⟨t, rLe_refl t⟩
      ↔ w.prod = t := by
  rw [targetAction_run_start]
  constructor
  · intro h
    by_cases hr : RLe t w.prod
    · rw [dif_pos hr] at h
      exact congrArg Subtype.val (Option.some_injective _ h)
    · rw [dif_neg hr] at h
      exact absurd h (by simp)
  · intro h
    subst h
    rw [dif_pos (rLe_refl _)]

/-! ## The ideal chain and the height drop -/

variable {t}

/-- A live state can reach the target, so it generates at least as much. -/
theorem twoIdeal_subset_of_tState (p : TState t) : twoIdeal t ⊆ twoIdeal p.val :=
  twoIdeal_subset_of_rLe p.2

/-- A return element of the target action at a **live** state acts on the
right as the identity there. -/
theorem val_mul_eq_of_isReturn {p : TState t} {e : M}
    (h : (targetAction t).IsReturn (some p) e) : p.val * e = p.val := by
  rw [RightAction.IsReturn, targetAction_act, targetStep_some] at h
  by_cases hr : RLe t (p.val * e)
  · rw [dif_pos hr] at h
    exact congrArg Subtype.val (Option.some_injective _ h)
  · rw [dif_neg hr] at h
    exact absurd h (by simp)

/-- **The chain** `MtM ⊆ MpM ⊆ MeM`, for a live `p` and an owner at `p`. -/
theorem twoIdeal_chain {p : TState t} {e : M}
    (hown : MinimalOwner (targetAction t) (some p) e) :
    twoIdeal t ⊆ twoIdeal p.val ∧ twoIdeal p.val ⊆ twoIdeal e := by
  refine ⟨twoIdeal_subset_of_tState p, ?_⟩
  calc twoIdeal p.val = twoIdeal (p.val * e) := by rw [val_mul_eq_of_isReturn hown.ret]
    _ ⊆ twoIdeal e := twoIdeal_mul_subset_right _ _

/-- **The regular-height drop.**  A regular class strictly below the target is
strictly below the owner, so the owner's regular height is strictly smaller —
which is the descent the regular-axis recurrence runs on. -/
theorem regHeight_drop {p : TState t} {e : M}
    (hown : MinimalOwner (targetAction t) (some p) e)
    {k : M} (hk : twoIdeal k ⊂ twoIdeal t) :
    twoIdeal k ⊂ twoIdeal e ∧ regHeight e < regHeight k := by
  obtain ⟨h1, h2⟩ := twoIdeal_chain hown
  have hke : twoIdeal k ⊂ twoIdeal e := lt_of_lt_of_le hk (h1.trans h2)
  refine ⟨hke, regHeight_lt_of_ssubset hke ?_⟩
  exact IsVonNeumannRegular.isRegularClass (IsIdempotentElem.isVonNeumannRegular hown.idem)

end Target

end MonoidProduct
