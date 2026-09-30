import MonoidProduct.Dyck.Lower
import MonoidProduct.Dyck.Monoid.NormalForm
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.show false

/-!
# Dyck recognition as a postprocessing of the ordered product (the paper's `cor:dyck`)

The two letters act on the counter as normal-form elements (`dyckLetter`), the
word's ordered product is `dyckProduct`, and acceptance reads the product:
`dyckAccept (live (a, b, e)) = (a = 0 ∧ e = 0)` — the start height `0` survives
iff the prefix deficit is `0`, and returns to `0` iff the shift is `0`; the
height cap is already enforced by nonzeroness.  The bridge is semantic:

* `toEnd_dyckLetter` — the normal-form letters act as `upE`/`downE` (at
  `k = 0` both letters are the zero map, which is why `dyckLetter` cases on
  `1 ≤ k`);
* `run_word_of_bounds` / `run_word_dead` — running the first `t` letters from
  height `0` computes `prefixBalance` while it stays in `[0, k]`, and dies the
  moment it leaves;
* `dyck_eq_accept_product` — hence `dyck k n = dyckAccept ∘ dyckProduct k n`;
* `advPM_dyck_le_product` — by `advPM_postcompose_le`, every Dyck adversary
  lower bound transfers to the monoid-valued ordered-product problem, giving
  the `cor:dyck` bounds `dyckMonoid_product_lower_block` and
  `dyckMonoid_product_lower_fixedBase` with no new witness.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {k : ℕ}

/-! ## The letters as normal-form elements -/

/-- The opening parenthesis: `(0, 1, 1)`, defined when the counter has room. -/
def upT (k : ℕ) (hk : 1 ≤ k) : DyckTriple k :=
  ⟨0, 1, 1, by omega, by norm_num, by norm_num⟩

/-- The closing parenthesis: `(1, 0, -1)`. -/
def downT (k : ℕ) (hk : 1 ≤ k) : DyckTriple k :=
  ⟨1, 0, -1, by omega, by norm_num, by norm_num⟩

/-- The letter actions in normal form; at `k = 0` both letters kill the only
height, so they are the zero map. -/
def dyckLetter (k : ℕ) : Bool → DyckNF k
  | false => if hk : 1 ≤ k then .live (upT k hk) else .zero
  | true => if hk : 1 ≤ k then .live (downT k hk) else .zero

lemma dyckLetter_false (k : ℕ) :
    dyckLetter k false
      = if hk : 1 ≤ k then .live (upT k hk) else .zero := rfl

lemma dyckLetter_true (k : ℕ) :
    dyckLetter k true
      = if hk : 1 ≤ k then .live (downT k hk) else .zero := rfl

@[simp] lemma letterE_false (k : ℕ) : letterE k false = upE k := rfl

@[simp] lemma letterE_true (k : ℕ) : letterE k true = downE k := rfl

lemma letterE_run_none (k : ℕ) (b : Bool) : (letterE k b).run none = none := by
  cases b
  · exact upE_run_none k
  · exact downE_run_none k

/-- The normal-form letters act as the letter actions. -/
theorem toEnd_dyckLetter (k : ℕ) (b : Bool) :
    (dyckLetter k b).toEnd = letterE k b := by
  cases b with
  | false =>
      refine ThenEnd.ext fun s => ?_
      rw [dyckLetter_false, letterE_false]
      by_cases hk : 1 ≤ k
      · rw [dif_pos hk]
        cases s with
        | none => rw [DyckNF.toEnd_live_run_none, upE_run_none]
        | some h =>
            rw [DyckNF.toEnd_live_run_some]
            have hh := h.isLt
            by_cases hup : (h : ℕ) + 1 ≤ k
            · rw [upE_run_some_of_le hup]
              have hL : (upT k hk).Lives h :=
                ⟨Nat.zero_le _, by show (h : ℕ) + 1 ≤ k; exact hup⟩
              obtain ⟨h', hs, hv⟩ := DyckTriple.apply_of_lives hL
              rw [hs]
              have he : (upT k hk).e = 1 := rfl
              exact congrArg some (Fin.ext (by
                show (h' : ℕ) = (h : ℕ) + 1
                omega))
            · rw [upE_run_some_of_gt (by omega),
                DyckTriple.apply_of_not_lives (fun hL => hup hL.2)]
      · rw [dif_neg hk]
        cases s with
        | none => rw [DyckNF.toEnd_zero_run, upE_run_none]
        | some h =>
            have hh := h.isLt
            rw [DyckNF.toEnd_zero_run, upE_run_some_of_gt (by omega)]
  | true =>
      refine ThenEnd.ext fun s => ?_
      rw [dyckLetter_true, letterE_true]
      by_cases hk : 1 ≤ k
      · rw [dif_pos hk]
        cases s with
        | none => rw [DyckNF.toEnd_live_run_none, downE_run_none]
        | some h =>
            rw [DyckNF.toEnd_live_run_some]
            have hh := h.isLt
            by_cases hdn : 1 ≤ (h : ℕ)
            · rw [downE_run_some_of_le hdn]
              have hL : (downT k hk).Lives h :=
                ⟨by show 1 ≤ (h : ℕ); exact hdn,
                  by show (h : ℕ) + 0 ≤ k; omega⟩
              obtain ⟨h', hs, hv⟩ := DyckTriple.apply_of_lives hL
              rw [hs]
              have he : (downT k hk).e = -1 := rfl
              exact congrArg some (Fin.ext (by
                show (h' : ℕ) = (h : ℕ) - 1
                omega))
            · rw [downE_run_some_of_lt (by omega),
                DyckTriple.apply_of_not_lives (fun hL => hdn hL.1)]
      · rw [dif_neg hk]
        cases s with
        | none => rw [DyckNF.toEnd_zero_run, downE_run_none]
        | some h =>
            have hh := h.isLt
            rw [DyckNF.toEnd_zero_run, downE_run_some_of_lt (by omega)]

/-! ## The product and acceptance -/

/-- The monoid-valued ordered-product problem for the depth-`k` counter. -/
def dyckProduct (k n : ℕ) (x : Fin n → Bool) : DyckNF k :=
  orderedProd fun i => dyckLetter k (x i)

/-- Acceptance: the start height `0` survives and returns to `0`. -/
def dyckAccept : DyckNF k → Bool
  | .zero => false
  | .live t => decide (t.a = 0 ∧ t.e = 0)

/-- The semantic map commutes with ordered products. -/
lemma toEnd_orderedProd {n : ℕ} (f : Fin n → DyckNF k) :
    (orderedProd f).toEnd = orderedProd fun i => (f i).toEnd := by
  rw [orderedProd_eq_prod_ofFn, orderedProd_eq_prod_ofFn,
    show (List.ofFn f).prod.toEnd = DyckNF.toEndHom k (List.ofFn f).prod
      from rfl,
    map_list_prod (DyckNF.toEndHom k), List.map_ofFn]
  rfl

lemma toEnd_dyckProduct (k n : ℕ) (x : Fin n → Bool) :
    (dyckProduct k n x).toEnd = orderedProd fun i => letterE k (x i) := by
  rw [dyckProduct, toEnd_orderedProd]
  congr 1
  funext i
  exact toEnd_dyckLetter k (x i)

/-! ## Running a word computes the prefix balance -/

/-- While every prefix balance stays in `[0, k]`, the run from height `0`
survives and sits at the prefix balance. -/
lemma run_word_of_bounds {n : ℕ} (x : Fin n → Bool) :
    ∀ t, t ≤ n →
      (∀ s, s ≤ t → 0 ≤ prefixBalance x s ∧ prefixBalance x s ≤ (k : ℤ)) →
      ∃ h' : Fin (k + 1),
        (rangeProd (fun i => letterE k (x i)) 0 t).run
            (some ⟨0, Nat.succ_pos k⟩) = some h'
          ∧ ((h' : ℕ) : ℤ) = prefixBalance x t := by
  intro t
  induction t with
  | zero =>
      intro _ _
      refine ⟨⟨0, Nat.succ_pos k⟩, ?_, ?_⟩
      · rw [rangeProd_self, ThenEnd.one_run]
      · show ((0 : ℕ) : ℤ) = prefixBalance x 0
        rw [prefixBalance_zero]
        rfl
  | succ t ih =>
      intro ht hb
      have htn : t < n := by omega
      obtain ⟨h₁, hr₁, hv₁⟩ := ih (by omega) (fun s hs => hb s (by omega))
      have hpb := prefixBalance_succ x t
      rw [stepAt_of_lt x htn] at hpb
      have h0t : 0 ≤ prefixBalance x t := (hb t (by omega)).1
      have hkt : prefixBalance x t ≤ (k : ℤ) := (hb t (by omega)).2
      have h0s : 0 ≤ prefixBalance x (t + 1) := (hb (t + 1) le_rfl).1
      have hks : prefixBalance x (t + 1) ≤ (k : ℤ) := (hb (t + 1) le_rfl).2
      rw [rangeProd_succ_right _ (Nat.zero_le t), ThenEnd.mul_run, hr₁,
        padAt_of_lt _ htn]
      cases hxt : x ⟨t, htn⟩ with
      | false =>
          rw [hxt, show parenStep false = (1 : ℤ) from rfl] at hpb
          rw [letterE_false, upE_run_some_of_le (by omega)]
          refine ⟨⟨(h₁ : ℕ) + 1, by omega⟩, rfl, ?_⟩
          show (((h₁ : ℕ) + 1 : ℕ) : ℤ) = prefixBalance x (t + 1)
          omega
      | true =>
          rw [hxt, show parenStep true = (-1 : ℤ) from rfl] at hpb
          rw [letterE_true, downE_run_some_of_le (by omega)]
          refine ⟨⟨(h₁ : ℕ) - 1, by omega⟩, rfl, ?_⟩
          show (((h₁ : ℕ) - 1 : ℕ) : ℤ) = prefixBalance x (t + 1)
          omega

/-- A bound violation somewhere in the first `t` prefixes kills the run. -/
lemma exists_violation {n : ℕ} {x : Fin n → Bool} {t : ℕ}
    (hb : ¬ ∀ s, s ≤ t → 0 ≤ prefixBalance x s ∧ prefixBalance x s ≤ (k : ℤ)) :
    ∃ s, s ≤ t ∧ (prefixBalance x s < 0 ∨ (k : ℤ) < prefixBalance x s) := by
  obtain ⟨s, hs⟩ := not_forall.mp hb
  by_cases hsn : s ≤ t
  · refine ⟨s, hsn, ?_⟩
    have hna : ¬(0 ≤ prefixBalance x s ∧ prefixBalance x s ≤ (k : ℤ)) :=
      fun hc => hs fun _ => hc
    rcases lt_or_ge (prefixBalance x s) 0 with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra hk'
      exact hna ⟨h, by omega⟩
  · exact absurd (fun hle => absurd hle hsn) hs

lemma run_word_dead {n : ℕ} (x : Fin n → Bool) :
    ∀ t, t ≤ n →
      (∃ s, s ≤ t ∧ (prefixBalance x s < 0 ∨ (k : ℤ) < prefixBalance x s)) →
      (rangeProd (fun i => letterE k (x i)) 0 t).run
        (some ⟨0, Nat.succ_pos k⟩) = none := by
  intro t
  induction t with
  | zero =>
      rintro _ ⟨s, hs, hv⟩
      exfalso
      obtain rfl : s = 0 := by omega
      rw [prefixBalance_zero] at hv
      rcases hv with h | h <;> omega
  | succ t ih =>
      rintro ht ⟨s, hs, hv⟩
      have htn : t < n := by omega
      rw [rangeProd_succ_right _ (Nat.zero_le t), ThenEnd.mul_run]
      by_cases hbt : ∀ s', s' ≤ t →
          0 ≤ prefixBalance x s' ∧ prefixBalance x s' ≤ (k : ℤ)
      · obtain ⟨h₁, hr₁, hv₁⟩ := run_word_of_bounds x t (by omega) hbt
        rw [hr₁, padAt_of_lt _ htn]
        have hst : s = t + 1 := by
          by_contra hc
          have hs' : s ≤ t := by omega
          rcases hv with h | h
          · exact absurd h (by have := (hbt s hs').1; omega)
          · exact absurd h (by have := (hbt s hs').2; omega)
        subst hst
        have hpb := prefixBalance_succ x t
        rw [stepAt_of_lt x htn] at hpb
        have h0t := (hbt t le_rfl).1
        have hkt := (hbt t le_rfl).2
        cases hxt : x ⟨t, htn⟩ with
        | false =>
            rw [hxt, show parenStep false = (1 : ℤ) from rfl] at hpb
            rw [letterE_false]
            refine upE_run_some_of_gt ?_
            rcases hv with h | h <;> omega
        | true =>
            rw [hxt, show parenStep true = (-1 : ℤ) from rfl] at hpb
            rw [letterE_true]
            refine downE_run_some_of_lt ?_
            rcases hv with h | h <;> omega
      · rw [ih (by omega) (exists_violation hbt), padAt_of_lt _ htn,
          letterE_run_none]

/-! ## Acceptance reads the run -/

lemma dyckAccept_eq_true_iff (m : DyckNF k) :
    dyckAccept m = true
      ↔ m.toEnd.run (some ⟨0, Nat.succ_pos k⟩)
          = some ⟨0, Nat.succ_pos k⟩ := by
  cases m with
  | zero =>
      rw [show dyckAccept (DyckNF.zero : DyckNF k) = false from rfl,
        DyckNF.toEnd_zero_run]
      simp
  | live t =>
      rw [show dyckAccept (DyckNF.live t) = decide (t.a = 0 ∧ t.e = 0)
          from rfl,
        decide_eq_true_iff, DyckNF.toEnd_live_run_some]
      have hb := t.budget
      have h00 : ((⟨0, Nat.succ_pos k⟩ : Fin (k + 1)) : ℕ) = 0 := rfl
      constructor
      · rintro ⟨ha, he⟩
        have hL : t.Lives ⟨0, Nat.succ_pos k⟩ :=
          ⟨by show t.a ≤ 0; omega, by show 0 + t.b ≤ k; omega⟩
        obtain ⟨h', hs, hv⟩ := DyckTriple.apply_of_lives hL
        rw [hs]
        exact congrArg some (Fin.ext (by
          show (h' : ℕ) = 0
          omega))
      · intro hs
        obtain ⟨hL, hv⟩ := DyckTriple.lives_of_apply_eq_some hs
        have h1 := hL.1
        exact ⟨by omega, by omega⟩

/-- **The reduction**: depth-`k` Dyck recognition is a Boolean postprocessing
of the monoid-valued ordered product. -/
theorem dyck_eq_accept_product (k n : ℕ) :
    dyck k n = fun x => dyckAccept (dyckProduct k n x) := by
  funext x
  rw [Bool.eq_iff_iff, dyck_eq_true, dyckAccept_eq_true_iff,
    toEnd_dyckProduct, orderedProd_eq_rangeProd, isDyck_iff]
  have htn : prefixBalance x n = totalBalance x := rfl
  constructor
  · rintro ⟨htot, hbound⟩
    obtain ⟨h', hr, hv⟩ := run_word_of_bounds x n le_rfl fun s _ => hbound s
    rw [hr]
    exact congrArg some (Fin.ext (by
      show (h' : ℕ) = 0
      omega))
  · intro hr
    by_cases hbound : ∀ s, s ≤ n →
        0 ≤ prefixBalance x s ∧ prefixBalance x s ≤ (k : ℤ)
    · obtain ⟨h', hr', hv⟩ := run_word_of_bounds x n le_rfl hbound
      rw [hr'] at hr
      have hval : (h' : ℕ) = 0 := congrArg Fin.val (Option.some.inj hr)
      refine ⟨by omega, fun t => ?_⟩
      rcases Nat.lt_or_ge t (n + 1) with hle | hgt
      · exact hbound t (by omega)
      · rw [prefixBalance_of_ge x (by omega)]
        constructor <;> omega
    · exfalso
      rw [run_word_dead x n le_rfl (exists_violation hbound)] at hr
      simp at hr

/-! ## The transfer (`cor:dyck`) -/

/-- **The transfer**: every Dyck adversary lower bound applies to the
monoid-valued ordered-product problem. -/
theorem advPM_dyck_le_product (k n : ℕ) :
    advPM (dyck k n) ≤ advPM (dyckProduct k n) := by
  have h := advPM_postcompose_le (g := dyckProduct k n) dyckAccept
  rwa [← dyck_eq_accept_product k n] at h

/-- **`cor:dyck`**, block form: `m^ℓ` against the product problem at the
encoding lengths. -/
theorem dyckMonoid_product_lower_block (m ℓ : ℕ) (hm : 0 < m) :
    (m : ℝ) ^ ℓ
      ≤ advPM (dyckProduct (blockHeight m ℓ) (blockWidth m ℓ)) :=
  (pow_le_advPM_dyck_block m ℓ hm).trans (advPM_dyck_le_product _ _)

/-- **`cor:dyck`**, fixed-base form: `√n · √2^ℓ` against the product
problem at every sufficiently large even length and depth `≥ 4 + 10ℓ`. -/
theorem dyckMonoid_product_lower_fixedBase (ℓ n dk : ℕ) (heven : Even n)
    (hfit : 4 * 8 ^ ℓ ≤ n) (hk : 4 + 10 * ℓ ≤ dk) :
    Real.sqrt n * Real.sqrt 2 ^ ℓ
      ≤ 2 * Real.sqrt 2 * advPM (dyckProduct dk n) := by
  refine (sqrt_mul_sqrt_two_pow_le_advPM_dyck ℓ n dk heven hfit hk).trans ?_
  exact mul_le_mul_of_nonneg_left (advPM_dyck_le_product dk n) (by positivity)

/-- **`cor:dyck`**, near-linear form: the integer-exponent `1 − 1/q` bound
against the product problem at the encoding lengths. -/
theorem dyckMonoid_product_lower_nearLinear (m q ℓ : ℕ) (hm : 0 < m)
    (hmq : (2 * m) ^ (q - 1) ≤ m ^ q) :
    (blockWidth m ℓ : ℝ) ^ (q - 1)
      ≤ 4 ^ (q - 1)
        * advPM (dyckProduct (blockHeight m ℓ) (blockWidth m ℓ)) ^ q := by
  refine (advPM_dyck_nearLinear_int m q ℓ hm hmq).trans ?_
  refine mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (advPM_nonneg _) (advPM_dyck_le_product _ _) q)
    (by positivity)

/-! ## Finite checks -/

example : ∀ x : Fin 2 → Bool, dyck 1 2 x = dyckAccept (dyckProduct 1 2 x) := by
  decide

example : ∀ x : Fin 4 → Bool, dyck 2 4 x = dyckAccept (dyckProduct 2 4 x) := by
  decide

end MonoidProduct
