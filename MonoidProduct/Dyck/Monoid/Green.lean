import MonoidProduct.Dyck.Monoid.NormalForm
import MonoidProduct.Aperiodic.Ideals
import Mathlib.Algebra.Order.Ring.Int

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.show false

/-!
# Aperiodicity of the Dyck transition monoid (`prop:dyck-monoid`)

Powers stabilise with the **uniform** exponent `k + 1`:

  `pow_stabilizes_at_k_add_one : x ^ (k+1) = x ^ (k+2)`.

There are three cases: zero is absorbing; a live triple with
`e = 0` is idempotent (its square has the same domain and shift, seen
semantically — no max-computation); and a live triple with `e ≠ 0` shifts
every surviving height by `e` per application (`pow_run_shift`), so `k + 1`
applications overshoot the `[0, k]` height range and the power is zero.

This gives the `IsAperiodicMonoid (DyckNF k)` instance in the exact form the
AGS development consumes (`Aperiodic/Defs.lean`), which is what lets the
upper-bound machinery and this hard family meet in one statement.

The Green structure is the second half of the file: `dyckLevel` (zero at
`k+1`, a live triple at `a + b`), multiplication monotonicity, the exact ideal
characterisation

  `mem_twoIdeal_iff_dyckLevel : y ∈ twoIdeal x ↔ dyckLevel x ≤ dyckLevel y`,

and hence `jLevel_dyckNF : jLevel x = dyckLevel x` and
`jDepth_dyckNF : jDepth (DyckNF k) = k + 1`.

**The same-level equivalence needs no canonical representatives.**  Rather
than normalising `e` by right letters and sliding `(a, b)` by left
letters, there is a single uniform two-sided witness: for
`a + b ≤ a' + b'`,

  `live (a', (a−a')⁺, a−a') * live (a,b,e) * live ((a+e)⁺, (b'−e−a+a')⁺, e'−e−a+a') = live (a',b',e')`,

where `z⁺ = z.toNat`.  The left factor relocates `[a', ·]` onto `[a, ·]`, the
right factor's parameters are forced by the target, and every validity and
evaluation side condition is a `max`/`toNat` identity that `omega` closes —
the level inequality enters exactly twice (`b_pt ≤ b'` and `q`'s budget
`= a' + b' ≤ k`).  So the whole reverse inclusion of the ideal characterisation
is one lemma
(`live_mem_twoIdeal_live`) with no case analysis.
-/

namespace MonoidProduct

variable {k : ℕ}

namespace DyckNF

@[simp] lemma toEndHom_apply (x : DyckNF k) : toEndHom k x = x.toEnd := rfl

lemma toEnd_pow (x : DyckNF k) (n : ℕ) : (x ^ n).toEnd = x.toEnd ^ n := by
  simpa using map_pow (toEndHom k) x n

/-- Each application of a live triple shifts a surviving height by `e`; `j`
applications shift by `j·e`. -/
lemma pow_run_shift {t : DyckTriple k} {j : ℕ} {h h' : Fin (k + 1)}
    (hr : ((DyckNF.live t).toEnd ^ j).run (some h) = some h') :
    ((h' : ℕ) : ℤ) = ((h : ℕ) : ℤ) + (j : ℤ) * t.e := by
  induction j generalizing h with
  | zero =>
      rw [ThenEnd.pow_zero_run] at hr
      obtain rfl := Option.some.inj hr
      omega
  | succ j ih =>
      rw [ThenEnd.pow_succ_run, toEnd_live_run_some] at hr
      cases hx : t.apply h with
      | none =>
          rw [hx, ThenEnd.pow_run_fixed (toEnd_run_none _)] at hr
          simp at hr
      | some h₁ =>
          rw [hx] at hr
          have hih := ih hr
          have hstep := (DyckTriple.lives_of_apply_eq_some hx).2
          push_cast
          push_cast at hih
          rw [add_mul, one_mul]
          omega

/-- A live triple with nonzero shift dies within `k + 1` steps: the height
range has width `k`, and every step moves by at least `1`. -/
lemma pow_succ_k_run_none {t : DyckTriple k} (he : t.e ≠ 0)
    (s : DyckState k) :
    ((DyckNF.live t).toEnd ^ (k + 1)).run s = none := by
  cases s with
  | none => exact ThenEnd.pow_run_fixed (toEnd_live_run_none t) _
  | some h =>
      cases hr : ((DyckNF.live t).toEnd ^ (k + 1)).run (some h) with
      | none => rfl
      | some h' =>
          exfalso
          have hv := pow_run_shift hr
          push_cast at hv
          have h1 := h.isLt
          have h2 := h'.isLt
          rcases lt_or_gt_of_ne he with hneg | hpos
          · have hb : ((k : ℤ) + 1) * t.e ≤ ((k : ℤ) + 1) * (-1) :=
              mul_le_mul_of_nonneg_left (by omega) (by omega)
            omega
          · have hb : ((k : ℤ) + 1) * 1 ≤ ((k : ℤ) + 1) * t.e :=
              mul_le_mul_of_nonneg_left (by omega) (by omega)
            omega

/-- **Aperiodicity**: powers stabilise at the uniform exponent `k + 1`. -/
theorem pow_stabilizes_at_k_add_one (x : DyckNF k) :
    x ^ (k + 1) = x ^ (k + 2) := by
  cases x with
  | zero =>
      have hz : ∀ n : ℕ, (DyckNF.zero : DyckNF k) ^ (n + 1) = DyckNF.zero :=
        fun n => by rw [pow_succ, mul_zero_eq]
      rw [hz k, show k + 2 = (k + 1) + 1 from rfl, hz (k + 1)]
  | live t =>
      by_cases he : t.e = 0
      · have hsq : DyckNF.live t * DyckNF.live t = DyckNF.live t := by
          apply toEnd_injective
          rw [toEnd_mul]
          refine ThenEnd.ext fun s => ?_
          rw [ThenEnd.mul_run]
          cases s with
          | none => rw [toEnd_run_none, toEnd_run_none]
          | some h =>
              rw [toEnd_live_run_some]
              cases hx : t.apply h with
              | none => rw [toEnd_run_none]
              | some h₁ =>
                  obtain ⟨hL, hv⟩ := DyckTriple.lives_of_apply_eq_some hx
                  obtain rfl : h₁ = h := Fin.ext (by omega)
                  rw [toEnd_live_run_some]
                  exact hx
        have hn : ∀ n : ℕ, DyckNF.live t ^ (n + 1) = DyckNF.live t := by
          intro n
          induction n with
          | zero => rw [pow_one]
          | succ n ih => rw [pow_succ, ih, hsq]
        rw [hn k, show k + 2 = (k + 1) + 1 from rfl, hn (k + 1)]
      · have hzero : DyckNF.live t ^ (k + 1) = DyckNF.zero := by
          apply toEnd_injective
          rw [toEnd_pow]
          refine ThenEnd.ext fun s => ?_
          rw [pow_succ_k_run_none he s, toEnd_zero_run]
        rw [hzero, show k + 2 = (k + 1) + 1 from rfl, pow_succ, hzero,
          zero_mul_eq]

end DyckNF

/-- **Aperiodicity** (`prop:dyck-monoid`): the Dyck transition monoid is
aperiodic, in exactly the stabilisation form the AGS upper-bound development consumes. -/
instance : IsAperiodicMonoid (DyckNF k) :=
  ⟨fun x => ⟨k + 1, by omega, DyckNF.pow_stabilizes_at_k_add_one x⟩⟩

/-! ## Green structure -/

/-- The `J`-class datum: the total width `a + b` of a live triple, `k + 1`
for the zero map. -/
def dyckLevel : DyckNF k → ℕ
  | .zero => k + 1
  | .live t => t.a + t.b

@[simp] lemma dyckLevel_zero : dyckLevel (DyckNF.zero : DyckNF k) = k + 1 :=
  rfl

@[simp] lemma dyckLevel_live (t : DyckTriple k) :
    dyckLevel (DyckNF.live t) = t.a + t.b := rfl

lemma dyckLevel_le (x : DyckNF k) : dyckLevel x ≤ k + 1 := by
  cases x with
  | zero => exact le_refl _
  | live t =>
      have := t.budget
      show t.a + t.b ≤ k + 1
      omega

/-- Every level up to `k + 1` is inhabited (by `(l, 0, 0)`, or zero). -/
lemma exists_dyckLevel_eq {l : ℕ} (hl : l ≤ k + 1) :
    ∃ x : DyckNF k, dyckLevel x = l := by
  rcases Nat.lt_or_ge l (k + 1) with hlt | hge
  · exact ⟨.live ⟨l, 0, 0, by omega, by omega, by omega⟩, by
      show l + 0 = l
      omega⟩
  · exact ⟨.zero, by show k + 1 = l; omega⟩

/-- `comp` in the live case, for rewriting. -/
lemma DyckTriple.comp_of_le (t₁ t₂ : DyckTriple k)
    (hk : max (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e)
      + max (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e) ≤ (k : ℤ)) :
    t₁.comp t₂ = .live (t₁.compT t₂ hk) := dif_pos hk

/-- **Level monotonicity**, left factor. -/
lemma dyckLevel_le_mul_left (x y : DyckNF k) :
    dyckLevel x ≤ dyckLevel (x * y) := by
  cases x with
  | zero => rw [DyckNF.zero_mul_eq]
  | live t₁ =>
      cases y with
      | zero =>
          rw [DyckNF.mul_zero_eq]
          exact dyckLevel_le _
      | live t₂ =>
          rw [DyckNF.live_mul_live]
          unfold DyckTriple.comp
          split_ifs with hk
          · have hTa := DyckTriple.compT_a t₁ t₂ hk
            have hTb := DyckTriple.compT_b t₁ t₂ hk
            show t₁.a + t₁.b ≤ (t₁.compT t₂ hk).a + (t₁.compT t₂ hk).b
            omega
          · exact dyckLevel_le _

/-- **Level monotonicity**, right factor. -/
lemma dyckLevel_le_mul_right (x y : DyckNF k) :
    dyckLevel y ≤ dyckLevel (x * y) := by
  cases x with
  | zero => rw [DyckNF.zero_mul_eq]; exact dyckLevel_le _
  | live t₁ =>
      cases y with
      | zero => rw [DyckNF.mul_zero_eq]
      | live t₂ =>
          rw [DyckNF.live_mul_live]
          unfold DyckTriple.comp
          split_ifs with hk
          · have hTa := DyckTriple.compT_a t₁ t₂ hk
            have hTb := DyckTriple.compT_b t₁ t₂ hk
            have hlo1 := t₁.lower
            have hup1 := t₁.upper
            show t₂.a + t₂.b ≤ (t₁.compT t₂ hk).a + (t₁.compT t₂ hk).b
            omega
          · exact dyckLevel_le _

/-- **The reverse inclusion in one stroke**: a live target of at
least the source's level is reached by one explicit left and one explicit
right multiplier.  See the module docstring for the construction. -/
lemma live_mem_twoIdeal_live {t t' : DyckTriple k}
    (hlev : t.a + t.b ≤ t'.a + t'.b) :
    DyckNF.live t' ∈ twoIdeal (DyckNF.live t) := by
  have hb := t.budget
  have hlo := t.lower
  have hup := t.upper
  have hb' := t'.budget
  have hlo' := t'.lower
  have hup' := t'.upper
  refine mem_twoIdeal.mpr
    ⟨.live ⟨t'.a, ((t.a : ℤ) - t'.a).toNat, (t.a : ℤ) - t'.a,
        by omega, by omega, by omega⟩,
      .live ⟨((t.a : ℤ) + t.e).toNat, ((t'.b : ℤ) - t.e - t.a + t'.a).toNat,
        t'.e - t.e - (t.a : ℤ) + t'.a,
        by omega, by omega, by omega⟩, ?_⟩
  rw [DyckNF.live_mul_live,
    DyckTriple.comp_of_le _ _ (by dsimp only; omega),
    DyckNF.live_mul_live,
    DyckTriple.comp_of_le _ _ (by
      simp only [DyckTriple.compT_a, DyckTriple.compT_b, DyckTriple.compT_e]
      omega)]
  congr 1
  refine DyckTriple.ext ?_ ?_ ?_ <;>
    simp only [DyckTriple.compT_a, DyckTriple.compT_b, DyckTriple.compT_e] <;>
    omega

/-- **Ideal characterisation**: the two-sided ideals are exactly the level tails. -/
theorem mem_twoIdeal_iff_dyckLevel (x y : DyckNF k) :
    y ∈ twoIdeal x ↔ dyckLevel x ≤ dyckLevel y := by
  constructor
  · intro h
    obtain ⟨p, q, hpq⟩ := mem_twoIdeal.mp h
    calc dyckLevel x ≤ dyckLevel (p * x) := dyckLevel_le_mul_right p x
      _ ≤ dyckLevel (p * x * q) := dyckLevel_le_mul_left _ q
      _ = dyckLevel y := by rw [hpq]
  · intro hlev
    cases y with
    | zero =>
        exact mem_twoIdeal.mpr ⟨.zero, .zero,
          by rw [DyckNF.zero_mul_eq, DyckNF.zero_mul_eq]⟩
    | live t' =>
        cases x with
        | zero =>
            exfalso
            have hb' := t'.budget
            have h1 : k + 1 ≤ t'.a + t'.b := hlev
            omega
        | live t => exact live_mem_twoIdeal_live hlev

private lemma jLevel_eq_dyckLevel_aux :
    ∀ n, ∀ x : DyckNF k, dyckLevel x = n → jLevel x = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro x hx
      rw [jLevel_eq]
      apply le_antisymm
      · refine Finset.sup_le fun b hb => ?_
        rw [mem_aboveJ] at hb
        obtain ⟨y, hyb, hyx⟩ := Finset.exists_of_ssubset hb
        rw [mem_twoIdeal_iff_dyckLevel] at hyb
        have hyx' : ¬ dyckLevel x ≤ dyckLevel y := fun hc =>
          hyx ((mem_twoIdeal_iff_dyckLevel x y).mpr hc)
        have hlt : dyckLevel b < n := by omega
        rw [ih (dyckLevel b) hlt b rfl]
        omega
      · cases n with
        | zero => exact Nat.zero_le _
        | succ m =>
            have hxle := dyckLevel_le x
            obtain ⟨b, hbl⟩ := exists_dyckLevel_eq (k := k) (l := m) (by omega)
            have hmem : b ∈ aboveJ x := by
              rw [mem_aboveJ, Finset.ssubset_def]
              constructor
              · intro y hy
                rw [mem_twoIdeal_iff_dyckLevel] at hy ⊢
                omega
              · intro hcon
                have hself := hcon (self_mem_twoIdeal b)
                rw [mem_twoIdeal_iff_dyckLevel] at hself
                omega
            have hsup := Finset.le_sup (f := fun b => jLevel b + 1) hmem
            rw [ih m (by omega) b hbl] at hsup
            omega

/-- **`J`-levels**: the recursive `jLevel` is the explicit level datum. -/
theorem jLevel_dyckNF (x : DyckNF k) : jLevel x = dyckLevel x :=
  jLevel_eq_dyckLevel_aux (dyckLevel x) x rfl

/-- **`J`-depth** (`prop:dyck-monoid`): the Dyck transition monoid has `J`-depth
exactly `k + 1`. -/
theorem jDepth_dyckNF : jDepth (DyckNF k) = k + 1 := by
  apply le_antisymm
  · refine Finset.sup_le fun x _ => ?_
    rw [jLevel_dyckNF x]
    exact dyckLevel_le x
  · have h := jLevel_le_jDepth (DyckNF.zero : DyckNF k)
    rwa [jLevel_dyckNF, dyckLevel_zero] at h

/-! ## Finite checks

Aperiodicity and the ideal classification by brute force at `k = 1`: `DyckNF`
has decidable equality and a `Fintype` instance built from explicit
equivalences, so `decide` can enumerate all six elements.  (`jLevel` itself is
defined by well-founded recursion, which the kernel does not reduce, so the
brute-force check targets `twoIdeal` and `dyckLevel` directly.) -/

example : ∀ x : DyckNF 1, x ^ 2 = x ^ 3 := by decide

example : ∀ x y : DyckNF 1,
    (y ∈ twoIdeal x ↔ dyckLevel x ≤ dyckLevel y) := by decide

end MonoidProduct
