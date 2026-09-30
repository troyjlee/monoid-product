import MonoidProduct.Infix.Code
import MonoidProduct.Infix.Dual
import QuantumQueryComplexity.LetterCode
import QuantumQueryComplexity.Scan.Potential
import QuantumQueryComplexity.Adaptive
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.Plurality
import QuantumQueryComplexity.OrAnd
import QuantumQueryComplexity.Promise.Transport
import QuantumQueryComplexity.Promise.Post

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option synthInstance.maxSize 2048

/-!
# Products in Rees zero-matrix monoids

The product of a word over `R(P)¹` is determined by three tests: the explicit
zero test, the coded clean-infix tests of the zero entries of `P` (through the
letter maps `psi` and the two-letter code), and the first and last
non-identity letters.  Each is a dual: the infix tests by `hasDual_inf` pulled
back along the code (`hasDual_letterCode`), the other three by one-change
scans.  Their joint is collapsed onto the product (`HasDual.postcomp_of_determined`):

* `hasDual_wordProd_rees` — `ADV±(Prod_{R(P)¹,n}) ≤ 2·(Z·√3·11·√(2n)·λ(2n) + 24√n)`,
  `Z` the number of zero entries of `P`;
* `rees_qQuery_upper`, `rees_qQuery_lower` — `Q_{1/3}` is `O_P(√n·λ(n))` and
  `Ω(√n)`; `A2` (`Z = 1`) and `B2` (`Z = 2`) are the six-element monoids.
-/

namespace MonoidProduct.Infix

open Finset QuantumQueryComplexity

variable {I Λ : Type} [Fintype I] [DecidableEq I] [Fintype Λ] [DecidableEq Λ]
variable (P : Λ → I → Bool)

/-- The zero entries of the sandwich. -/
abbrev ZE := {p : Λ × I // P p.1 p.2 = false}

/-! ## The coded infix test of a zero entry -/

/-- The flattening of `Fin (2n)` into blocks of two. -/
def flatEmb (n : ℕ) : Fin (2 * n) → Fin n × Fin 2 := fun k =>
  (⟨k / 2, by have := k.isLt; omega⟩, ⟨k % 2, Nat.mod_lt _ (by norm_num)⟩)

lemma flatEmb_injective (n : ℕ) : Function.Injective (flatEmb n) := by
  intro k k' h
  simp only [flatEmb, Prod.mk.injEq, Fin.mk.injEq] at h
  ext; omega

variable {P}

/-- The `A₂¹`-coded infix test of the zero entry `p`. -/
def zeTest (n : ℕ) (p : ZE P) (w : Fin n → Rees1 P) : Bool :=
  inf (2 * n) (flatA fun k => psi P p.1.1 p.1.2 (w k))

lemma zeTest_eq_true_iff (n : ℕ) (p : ZE P) (w : Fin n → Rees1 P) :
    zeTest n p w = true ↔ Bad (fun k => psi P p.1.1 p.1.2 (w k)) n :=
  (bad_iff_inf_flatA _).symm

/-- The cost of one coded infix test. -/
noncomputable def cA (n : ℕ) : ℝ :=
  Real.sqrt 3 * (11 * Real.sqrt ((2 * n : ℕ) : ℝ) * lam (2 * n))

lemma cA_nonneg (n : ℕ) : 0 ≤ cA n := by
  unfold cA
  have := two_le_lam (2 * n)
  have h1 : (0 : ℝ) ≤ 11 * Real.sqrt ((2 * n : ℕ) : ℝ) := by positivity
  exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg h1 (by linarith))

theorem hasDual_zeTest (n : ℕ) (p : ZE P) : HasDual (zeTest n p) (cA n) := by
  have h1 := (hasDual_inf (2 * n)).pullback (flatEmb_injective n)
  have hc : (0 : ℝ) ≤ 11 * Real.sqrt ((2 * n : ℕ) : ℝ) * lam (2 * n) := by
    have := two_le_lam (2 * n)
    exact mul_nonneg (by positivity) (by linarith)
  have h2 := hasDual_letterCode (σ := Rees1 P) (κ := Fin 2) (σ' := Fin 3)
    (fun a => codeA (psi P p.1.1 p.1.2 a)) hc h1
  refine (h2.ofEq fun w => rfl).mono ?_
  unfold cA
  rw [Fintype.card_fin]
  push_cast
  exact le_rfl

/-! ## The explicit zero test and the first non-identity letter, as scans -/

/-- Remember whether a zero has been seen. -/
def zStep (n : ℕ) : Fin n → Bool → Rees1 P → Bool :=
  fun _ b a => b || decide (a = ↑(ReesZero.zero P))

lemma scanState_zStep {n : ℕ} (w : Fin n → Rees1 P) (t : ℕ) :
    scanState false (zStep (P := P) n) w t
      = decide (∃ s, s < t ∧ padAt w s = ↑(ReesZero.zero P)) := by
  induction t with
  | zero => simp
  | succ t ih =>
      by_cases ht : t < n
      · rw [scanState, dif_pos ht, ih]
        simp only [zStep]
        rw [← padAt_of_lt w ht]
        by_cases h : ∃ s, s < t ∧ padAt w s = ↑(ReesZero.zero P)
        · rw [decide_eq_true h, Bool.true_or]
          symm; rw [decide_eq_true_iff]
          obtain ⟨s, hs, h⟩ := h; exact ⟨s, by omega, h⟩
        · rw [decide_eq_false h, Bool.false_or]
          by_cases h2 : padAt w t = ↑(ReesZero.zero P)
          · rw [decide_eq_true h2]; symm; rw [decide_eq_true_iff]; exact ⟨t, Nat.lt_succ_self t, h2⟩
          · rw [decide_eq_false h2]; symm; rw [decide_eq_false_iff_not]
            rintro ⟨s, hs, hs2⟩
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hs) with h' | h'
            · exact h ⟨s, h', hs2⟩
            · subst h'; exact h2 hs2
      · rw [scanState_succ_of_not_lt _ _ _ ht, ih]
        congr 1
        apply propext
        constructor
        · rintro ⟨s, hs, h⟩; exact ⟨s, by omega, h⟩
        · rintro ⟨s, hs, h⟩
          refine ⟨s, ?_, h⟩
          by_contra hcon
          rw [padAt_of_le _ (by omega)] at h
          exact WithOne.one_ne_coe h

/-- The explicit zero test. -/
def zeroTest (n : ℕ) (w : Fin n → Rees1 P) : Bool :=
  decide (∃ s, s < n ∧ padAt w s = ↑(ReesZero.zero P))

theorem hasDual_zeroTest (n : ℕ) : HasDual (zeroTest (P := P) n) (8 * Real.sqrt n) := by
  have h := hasDual_scan (n := n) (q₀ := false) (δ := zStep (P := P) n) id (C := 1) fun w => by
    refine (changeCount_le_of_potential false (zStep n) w (fun b => if b then 0 else 1) ?_ ?_).trans
      ?_
    · intro i
      simp only [scanState_zStep, decide_eq_true_eq]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · norm_num
      · exact absurd (by obtain ⟨s, hs, h⟩ := h2; exact ⟨s, by omega, h⟩) h1
      · exact le_rfl
    · intro i hne
      simp only [scanState_zStep, ne_eq, decide_eq_decide] at hne
      simp only [scanState_zStep, decide_eq_true_eq]
      split_ifs with h1 h2 h2
      · exact absurd ⟨fun _ => h2, fun _ => h1⟩ hne
      · norm_num
      · exact absurd (by obtain ⟨s, hs, h⟩ := h2; exact ⟨s, by omega, h⟩) h1
      · exact absurd ⟨fun h => absurd h h1, fun h => absurd h h2⟩ hne
    · simp
  refine (h.ofEq fun w => ?_).mono (by rw [Nat.cast_one, mul_one])
  simp only [id, scanState_zStep, zeroTest]

/-- Remember the first non-identity letter. -/
def fnStep (n : ℕ) : Fin n → Option (ReesZero P) → Rees1 P → Option (ReesZero P) :=
  fun _ q a => Option.elim q (show Option (ReesZero P) from a) some

/-- The first non-identity letter of a word. -/
def firstNonId {n : ℕ} (w : Fin n → Rees1 P) : Option (ReesZero P) :=
  scanState none (fnStep (P := P) n) w n

lemma one_eq_none : ((1 : Rees1 P) : Option (ReesZero P)) = none := rfl

lemma coe_eq_some (a : ReesZero P) : ((↑a : Rees1 P) : Option (ReesZero P)) = some a := rfl

lemma scanState_fnStep {n : ℕ} (w : Fin n → Rees1 P) (t : ℕ) :
    (scanState none (fnStep (P := P) n) w t = none ↔ ∀ s, s < t → padAt w s = 1) ∧
    ∀ a, scanState none (fnStep (P := P) n) w t = some a →
      ∃ s, s < t ∧ padAt w s = ↑a ∧ ∀ q, q < s → padAt w q = 1 := by
  induction t with
  | zero =>
      refine ⟨⟨fun _ s hs => absurd hs (by omega), fun _ => rfl⟩, fun a h => ?_⟩
      rw [scanState_zero] at h; exact absurd h (by simp)
  | succ t ih =>
      obtain ⟨ih1, ih2⟩ := ih
      by_cases ht : t < n
      · rw [scanState, dif_pos ht]
        rcases hq : scanState none (fnStep (P := P) n) w t with _ | b
        · -- nothing seen yet: the state becomes the letter at `t`
          simp only [fnStep, Option.elim]
          have hall := ih1.1 hq
          rcases Rees1.cases P (w ⟨t, ht⟩) with ha | ha | ⟨i, l, ha⟩ <;> rw [ha]
          · refine ⟨⟨fun _ s hs => ?_, fun _ => rfl⟩, fun a h => absurd h (by simp [one_eq_none])⟩
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hs) with h' | h'
            · exact hall s h'
            · subst h'; rw [padAt_of_lt _ ht, ha]
          · refine ⟨⟨fun h => absurd h (Option.some_ne_none _), fun h => ?_⟩, fun a h => ?_⟩
            · have := h t (Nat.lt_succ_self t); rw [padAt_of_lt _ ht, ha] at this
              exact absurd this WithOne.coe_ne_one
            · refine ⟨t, Nat.lt_succ_self t, ?_, hall⟩
              rw [padAt_of_lt _ ht, ha]
              have e : ReesZero.zero P = a := Option.some.inj h
              rw [e]
          · refine ⟨⟨fun h => absurd h (Option.some_ne_none _), fun h => ?_⟩, fun a h => ?_⟩
            · have := h t (Nat.lt_succ_self t); rw [padAt_of_lt _ ht, ha] at this
              exact absurd this WithOne.coe_ne_one
            · refine ⟨t, Nat.lt_succ_self t, ?_, hall⟩
              rw [padAt_of_lt _ ht, ha]
              have e : ReesZero.cell P i l = a := Option.some.inj h
              rw [e]
        · -- already seen: frozen
          simp only [fnStep, Option.elim]
          refine ⟨⟨fun h => absurd h (by simp), fun h => ?_⟩, fun a h => ?_⟩
          · obtain ⟨s, hs, hs1, -⟩ := ih2 b hq
            have := h s (by omega); rw [hs1] at this; exact absurd this WithOne.coe_ne_one
          · obtain ⟨s, hs, hs1, hs2⟩ := ih2 b hq
            rw [Option.some.inj h] at hs1
            exact ⟨s, by omega, hs1, hs2⟩
      · rw [scanState_succ_of_not_lt _ _ _ ht]
        refine ⟨⟨fun h s hs => ?_, fun h => ih1.2 fun s hs => h s (by omega)⟩, fun a h => ?_⟩
        · rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hs) with h' | h'
          · exact ih1.1 h s h'
          · subst h'; exact padAt_of_le _ (by omega)
        · obtain ⟨s, hs, h1, h2⟩ := ih2 a h
          exact ⟨s, by omega, h1, h2⟩

lemma firstNonId_eq_none_iff {n : ℕ} (w : Fin n → Rees1 P) :
    firstNonId w = none ↔ ∀ s, s < n → padAt w s = 1 :=
  (scanState_fnStep w n).1

lemma firstNonId_eq_some {n : ℕ} (w : Fin n → Rees1 P) {a : ReesZero P}
    (h : firstNonId w = some a) :
    ∃ s, s < n ∧ padAt w s = ↑a ∧ ∀ q, q < s → padAt w q = 1 :=
  (scanState_fnStep w n).2 a h

theorem hasDual_firstNonId (n : ℕ) :
    HasDual (firstNonId (P := P) (n := n)) (8 * Real.sqrt n) := by
  have h := hasDual_scan (n := n) (q₀ := (none : Option (ReesZero P))) (δ := fnStep (P := P) n) id
    (C := 1) fun w => by
    refine (changeCount_le_of_potential none (fnStep n) w
      (fun q => Option.elim q 1 (fun _ => 0)) ?_ ?_).trans ?_
    · intro i
      rw [scanState_succ_fin]
      rcases hq : scanState none (fnStep n) w i with _ | b
      · rcases Rees1.cases P (w i) with ha | ha | ⟨j, l, ha⟩ <;> rw [ha] <;>
          simp [fnStep, one_eq_none, coe_eq_some]
      · exact le_rfl
    · intro i hne
      rw [scanState_succ_fin] at hne ⊢
      rcases hq : scanState none (fnStep n) w i with _ | b
      · rw [hq] at hne
        rcases Rees1.cases P (w i) with ha | ha | ⟨j, l, ha⟩ <;> rw [ha] at hne ⊢
        · exact absurd rfl hne
        · simp [fnStep, coe_eq_some]
        · simp [fnStep, coe_eq_some]
      · rw [hq] at hne
        exact absurd rfl hne
    · simp
  refine (h.ofEq fun w => rfl).mono (by rw [Nat.cast_one, mul_one])

/-- The last non-identity letter: the first one of the reversed word. -/
def lastNonId {n : ℕ} (w : Fin n → Rees1 P) : Option (ReesZero P) :=
  firstNonId fun k => w (Fin.rev k)

theorem hasDual_lastNonId (n : ℕ) :
    HasDual (lastNonId (P := P) (n := n)) (8 * Real.sqrt n) :=
  (hasDual_firstNonId n).pullback Fin.rev_injective

lemma padAt_rev {n : ℕ} (w : Fin n → Rees1 P) {s : ℕ} (hs : s < n) :
    padAt (fun k => w (Fin.rev k)) s = padAt w (n - 1 - s) := by
  rw [padAt_of_lt _ hs, padAt_of_lt _ (by omega)]
  congr 1; ext; simp [Fin.val_rev]; omega

lemma lastNonId_eq_none_iff {n : ℕ} (w : Fin n → Rees1 P) :
    lastNonId w = none ↔ ∀ s, s < n → padAt w s = 1 := by
  rw [lastNonId, firstNonId_eq_none_iff]
  constructor
  · intro h s hs
    have := h (n - 1 - s) (by omega)
    rwa [padAt_rev _ (by omega), show n - 1 - (n - 1 - s) = s by omega] at this
  · intro h s hs
    rw [padAt_rev _ hs]; exact h _ (by omega)

lemma lastNonId_eq_some {n : ℕ} (w : Fin n → Rees1 P) {a : ReesZero P} (h : lastNonId w = some a) :
    ∃ s, s < n ∧ padAt w s = ↑a ∧ ∀ q, s < q → q < n → padAt w q = 1 := by
  obtain ⟨s, hs, h1, h2⟩ := firstNonId_eq_some _ h
  rw [padAt_rev _ hs] at h1
  refine ⟨n - 1 - s, by omega, h1, fun q hq1 hq2 => ?_⟩
  have := h2 (n - 1 - q) (by omega)
  rwa [padAt_rev _ (by omega), show n - 1 - (n - 1 - q) = q by omega] at this

/-! ## The product is determined by the tests -/

/-- The least non-identity position is unique. -/
lemma first_unique {n : ℕ} {w : Fin n → Rees1 P} {s s' : ℕ} {a a' : ReesZero P}
    (h1 : padAt w s = ↑a) (h2 : ∀ q, q < s → padAt w q = 1)
    (h1' : padAt w s' = ↑a') (h2' : ∀ q, q < s' → padAt w q = 1) : s = s' ∧ a = a' := by
  have hss : s = s' := by
    rcases lt_trichotomy s s' with h | h | h
    · have := h2' s h; rw [h1] at this; exact absurd this WithOne.coe_ne_one
    · exact h
    · have := h2 s' h; rw [h1'] at this; exact absurd this WithOne.coe_ne_one
  subst hss
  rw [h1] at h1'
  exact ⟨rfl, WithOne.coe_inj.1 h1'⟩

lemma last_unique {n : ℕ} {w : Fin n → Rees1 P} {s s' : ℕ} {a a' : ReesZero P}
    (h1 : padAt w s = ↑a) (h2 : ∀ q, s < q → q < n → padAt w q = 1)
    (h1' : padAt w s' = ↑a') (h2' : ∀ q, s' < q → q < n → padAt w q = 1)
    (hs : s < n) (hs' : s' < n) : s = s' ∧ a = a' := by
  have hss : s = s' := by
    rcases lt_trichotomy s s' with h | h | h
    · have := h2 s' h hs'; rw [h1'] at this; exact absurd this WithOne.coe_ne_one
    · exact h
    · have := h2' s h hs; rw [h1] at this; exact absurd this WithOne.coe_ne_one
  subst hss
  rw [h1] at h1'
  exact ⟨rfl, WithOne.coe_inj.1 h1'⟩

/-- **The product is determined** by badness and the first and last
non-identity letters. -/
theorem wordProd_eq_of_data {n : ℕ} {w w' : Fin n → Rees1 P} (hb : Bad w n ↔ Bad w' n)
    (hf : firstNonId w = firstNonId w') (hl : lastNonId w = lastNonId w') :
    wordProd (id : Rees1 P → Rees1 P) w = wordProd (id : Rees1 P → Rees1 P) w' := by
  by_cases hbad : Bad w n
  · rw [(wordProd_eq_zero_iff w).2 hbad, (wordProd_eq_zero_iff w').2 (hb.1 hbad)]
  have hbad' : ¬ Bad w' n := fun h => hbad (hb.2 h)
  have hN := (prefix_spec w n).2 hbad
  have hN' := (prefix_spec w' n).2 hbad'
  rw [wordProd, orderedProd_eq_rangeProd, wordProd, orderedProd_eq_rangeProd]
  change rangeProd w 0 n = rangeProd w' 0 n
  rcases hN with ⟨h1, h2⟩ | ⟨s₁, s₂, i, l, i', m, h1, h2, h3, h4, h5, h6, h7⟩
  · -- `w` is all identities, hence so is `w'`
    have hnone : firstNonId w = none := (firstNonId_eq_none_iff w).2 h1
    rw [hnone] at hf
    have h1' := (firstNonId_eq_none_iff w').1 hf.symm
    rcases hN' with ⟨-, h2'⟩ | ⟨s₁', -, i₂, l₂, -, -, -, -, -, -, h5', -, -⟩
    · rw [h2, h2']
    · have := h1' s₁' (by
        by_contra hcon; rw [padAt_of_le w' (not_lt.1 hcon)] at h5'; exact WithOne.one_ne_coe h5')
      rw [h5'] at this; exact absurd this WithOne.coe_ne_one
  · -- `w` has cells: read off the first row and the last column
    have hs₁ : s₁ < n := by
      by_contra hcon; rw [padAt_of_le _ (not_lt.1 hcon)] at h5; exact WithOne.one_ne_coe h5
    have hfirst : firstNonId w = some (ReesZero.cell P i l) := by
      rcases hfw : firstNonId w with _ | a
      · have := (firstNonId_eq_none_iff w).1 hfw s₁ hs₁
        rw [h5] at this; exact absurd this WithOne.coe_ne_one
      · obtain ⟨s, hs, hs1, hs2⟩ := firstNonId_eq_some w hfw
        obtain ⟨-, e⟩ := first_unique hs1 hs2 h5 h3
        rw [e]
    have hlast : lastNonId w = some (ReesZero.cell P i' m) := by
      rcases hlw : lastNonId w with _ | a
      · have := (lastNonId_eq_none_iff w).1 hlw s₂ h2
        rw [h6] at this; exact absurd this WithOne.coe_ne_one
      · obtain ⟨s, hs, hs1, hs2⟩ := lastNonId_eq_some w hlw
        obtain ⟨-, e⟩ := last_unique hs1 hs2 h6 h4 hs h2
        rw [e]
    rcases hN' with ⟨h1', -⟩ | ⟨s₁', s₂', i₂, l₂, i₂', m₂, h1', h2', h3', h4', h5', h6', h7'⟩
    · rw [hfirst, (firstNonId_eq_none_iff w').2 h1'] at hf
      exact absurd hf (by simp)
    · have hs₁' : s₁' < n := by
        by_contra hcon; rw [padAt_of_le w' (not_lt.1 hcon)] at h5'; exact WithOne.one_ne_coe h5'
      have hfirst' : firstNonId w' = some (ReesZero.cell P i₂ l₂) := by
        rcases hfw : firstNonId w' with _ | a
        · have := (firstNonId_eq_none_iff w').1 hfw s₁' hs₁'
          rw [h5'] at this; exact absurd this WithOne.coe_ne_one
        · obtain ⟨s, hs, hs1, hs2⟩ := firstNonId_eq_some w' hfw
          obtain ⟨-, e⟩ := first_unique hs1 hs2 h5' h3'
          rw [e]
      have hlast' : lastNonId w' = some (ReesZero.cell P i₂' m₂) := by
        rcases hlw : lastNonId w' with _ | a
        · have := (lastNonId_eq_none_iff w').1 hlw s₂' h2'
          rw [h6'] at this; exact absurd this WithOne.coe_ne_one
        · obtain ⟨s, hs, hs1, hs2⟩ := lastNonId_eq_some w' hlw
          obtain ⟨-, e⟩ := last_unique hs1 hs2 h6' h4' hs h2'
          rw [e]
      rw [hfirst, hfirst'] at hf
      rw [hlast, hlast'] at hl
      have e1 := Rees1.cell_inj P (WithOne.coe_inj.2 (Option.some.inj hf) :
        (↑(ReesZero.cell P i l) : Rees1 P) = ↑(ReesZero.cell P i₂ l₂))
      have e2 := Rees1.cell_inj P (WithOne.coe_inj.2 (Option.some.inj hl) :
        (↑(ReesZero.cell P i' m) : Rees1 P) = ↑(ReesZero.cell P i₂' m₂))
      rw [h7, h7', e1.1, e2.2]

/-! ## The product -/

variable (P) in
/-- The number of zero entries of the sandwich. -/
noncomputable def numZero : ℕ := Fintype.card (ZE P)

/-- The joint of the zero-entry tests. -/
theorem hasDual_zeFamily (n : ℕ) :
    HasDual (fun w : Fin n → Rees1 P => fun p : ZE P => zeTest n p w) ((numZero P : ℝ) * cA n) := by
  classical
  let e := Fintype.equivFin (ZE P)
  have h := hasDualOn_family (X := Fin n → Rees1 P) (read := id)
    (fun k w => zeTest n (e.symm k) w) false (g := cA n)
    (fun k => (hasDual_zeTest n (e.symm k)).hasDualOn)
  have h2 := HasDual.of_hasDualOn_id h
  refine (h2.ofKer fun w w' => ?_).mono (le_of_eq ?_)
  · constructor
    · intro hf
      funext p
      have := congrFun hf (e p)
      simpa using this
    · intro hf
      funext k
      exact congrFun hf (e.symm k)
  · unfold numZero; rfl

/-- The joint of all four tests. -/
theorem hasDual_joint (n : ℕ) :
    HasDual (fun w : Fin n → Rees1 P =>
        (((fun p : ZE P => zeTest n p w, zeroTest n w), firstNonId w), lastNonId w))
      ((numZero P : ℝ) * cA n + 8 * Real.sqrt n + 8 * Real.sqrt n + 8 * Real.sqrt n) :=
  (((hasDual_zeFamily n).adaptiveCall_const (hasDual_zeroTest n)).adaptiveCall_const
    (hasDual_firstNonId n)).adaptiveCall_const (hasDual_lastNonId n)

lemma bad_iff_tests {n : ℕ} (w : Fin n → Rees1 P) :
    Bad w n ↔ zeroTest n w = true ∨ ∃ p : ZE P, zeTest n p w = true := by
  rw [bad_iff_exists_psi]
  simp only [zeroTest, decide_eq_true_eq, zeTest_eq_true_iff]
  constructor
  · rintro (h | ⟨l₀, j₀, hP, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨(l₀, j₀), hP⟩, h⟩
  · rintro (h | ⟨p, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p.1.1, p.1.2, p.2, h⟩

/-- **Rees products, dual form**: the product in `R(P)¹` has a dual of cost
`2·(Z·√3·11·√(2n)·λ(2n) + 24√n)`, `Z` the number of zero entries of `P`. -/
theorem hasDual_wordProd_rees (n : ℕ) :
    HasDual (fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w)
      (2 * ((numZero P : ℝ) * cA n + 24 * Real.sqrt n)) := by
  have hc : (0 : ℝ) ≤ (numZero P : ℝ) * cA n + 8 * Real.sqrt n + 8 * Real.sqrt n
      + 8 * Real.sqrt n := by
    have := cA_nonneg n
    have : (0 : ℝ) ≤ (numZero P : ℝ) * cA n := mul_nonneg (by positivity) this
    positivity
  have h := (hasDual_joint (P := P) n).postcomp_of_determined hc fun w w' hww' => by
    simp only [Prod.mk.injEq] at hww'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hww'
    refine wordProd_eq_of_data ?_ h3 h4
    rw [bad_iff_tests, bad_iff_tests, h2]
    constructor
    · rintro (h | ⟨p, hp⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p, by rw [← congrFun h1 p]; exact hp⟩
    · rintro (h | ⟨p, hp⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p, by rw [congrFun h1 p]; exact hp⟩
  refine h.mono (le_of_eq ?_)
  ring

/-- **Rees products**: `Q_{1/3}(Prod_{R(P)¹,n}) ≤ 8192·(1 + 2(Z·√3·11√(2n)·λ(2n) + 24√n))`. -/
theorem rees_qQuery_upper (n : ℕ) :
    (qQuery (fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + 2 * ((numZero P : ℝ) * cA n + 24 * Real.sqrt n)) := by
  have : Nonempty (Rees1 P) := ⟨1⟩
  refine qQueryOn_third_le_of_hasDualOn_uniform (hasDual_wordProd_rees n).hasDualOn ?_
  have := cA_nonneg n
  have : (0 : ℝ) ≤ (numZero P : ℝ) * cA n := mul_nonneg (by positivity) this
  positivity

/-- **The `Ω(√n)` lower bound**: words over `{1, 0}` compute `OR`. -/
theorem rees_qQuery_lower (n : ℕ) :
    (7 / 1376 : ℝ) * Real.sqrt n
      ≤ (qQuery (fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w) (1 / 3) : ℝ) := by
  classical
  let φ : Bool → Rees1 P := fun b => if b then ↑(ReesZero.zero P) else 1
  have hφ : Function.Injective φ := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact absurd h (show φ false ≠ φ true from WithOne.one_ne_coe)
    · exact absurd h (show φ true ≠ φ false from WithOne.coe_ne_one)
    · rfl
  let encode : (Fin n → Bool) → (Fin n → Rees1 P) := fun x j => φ (x j)
  have henc : Function.Injective encode := fun x y h => funext fun j => hφ (congrFun h j)
  have hout : ∀ x, orN x
      = decide (wordProd (id : Rees1 P → Rees1 P) (encode x) = ↑(ReesZero.zero P)) := by
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_eq, wordProd_eq_zero_iff]
    simp only [orN, decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact Or.inl ⟨i, i.isLt, by rw [padAt_of_lt _ i.isLt]; simp [encode, φ, hi]⟩
    · rintro (⟨s, hs, h⟩ | ⟨s, s', -, -, -, i, l, -, -, h4, -, -⟩)
      · refine ⟨⟨s, hs⟩, ?_⟩
        rw [padAt_of_lt _ hs] at h
        simp only [encode, φ] at h
        by_contra hc
        rw [if_neg (by simpa using hc)] at h
        exact WithOne.one_ne_coe h
      · exfalso
        unfold padAt at h4
        split_ifs at h4 with hs
        · simp only [encode, φ] at h4
          split_ifs at h4 with hx
          · exact Rees1.cell_ne_zero P _ _ h4.symm
          · exact WithOne.one_ne_coe h4
        · exact WithOne.one_ne_coe h4
  have h1 : Real.sqrt n ≤ advPM (orN : (Fin n → Bool) → Bool) := by
    have := sqrt_card_le_advPM_orN (ι := Fin n)
    rwa [Fintype.card_fin] at this
  have h2 : advPM (orN : (Fin n → Bool) → Bool) = advPMOn encode orN := by
    rw [← advPMOn_id]
    exact (advPMOn_comp_injective hφ id orN).symm
  have h3 : advPMOn encode orN
      ≤ advPM (fun w : Fin n → Rees1 P =>
          decide (wordProd (id : Rees1 P → Rees1 P) w = ↑(ReesZero.zero P))) :=
    advPMOn_le_advPM_of_injective henc hout
  have h4 : advPM (fun w : Fin n → Rees1 P =>
        decide (wordProd (id : Rees1 P → Rees1 P) w = ↑(ReesZero.zero P)))
      ≤ advPM (fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w) := by
    rw [← advPMOn_id, ← advPMOn_id]
    exact advPMOn_comp_le (read := fun x => x)
      (f := fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w)
      (fun x y h => by rw [show x = y from h]) (fun a => decide (a = ↑(ReesZero.zero P)))
  have h5 := mul_advPMOn_le_qQueryOn_third_finiteOutput
    (read := fun x : Fin n → Rees1 P => x)
    (f := fun w => wordProd (id : Rees1 P → Rees1 P) w) (fun x y h => by rw [show x = y from h])
  rw [advPMOn_id] at h5
  calc (7 / 1376 : ℝ) * Real.sqrt n
      ≤ (7 / 1376 : ℝ)
          * advPM (fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w) := by
        gcongr
        rw [h2] at h1
        exact h1.trans (h3.trans h4)
    _ ≤ _ := h5

/-! ## The six-element monoids -/

/-- The sandwich matrix of `B₂¹` (the identity). -/
def PB : Fin 2 → Fin 2 → Bool := fun l i => decide (l = i)

/-- **`B₂¹`**, the Brandt monoid. -/
abbrev B2 := Rees1 PB

lemma numZero_PA : numZero PA = 1 := by
  unfold numZero ZE; decide

lemma numZero_PB : numZero PB = 2 := by
  unfold numZero ZE; decide

/-- **Products in `A₂¹`**: `Q_{1/3}(Prod_{A₂¹,n}) ≤ 8192·(1 + 2(√3·11√(2n)·λ(2n) + 24√n))`. -/
theorem A2_qQuery_upper (n : ℕ) :
    (qQuery (fun w : Fin n → A2 => wordProd (id : A2 → A2) w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + 2 * (cA n + 24 * Real.sqrt n)) := by
  have := rees_qQuery_upper (P := PA) n
  rwa [numZero_PA, Nat.cast_one, one_mul] at this

/-- **Products in `B₂¹`**: `Q_{1/3}(Prod_{B₂¹,n}) ≤ 8192·(1 + 2(2·√3·11√(2n)·λ(2n) + 24√n))`. -/
theorem B2_qQuery_upper (n : ℕ) :
    (qQuery (fun w : Fin n → B2 => wordProd (id : B2 → B2) w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + 2 * (2 * cA n + 24 * Real.sqrt n)) := by
  have := rees_qQuery_upper (P := PB) n
  rwa [numZero_PB, Nat.cast_ofNat] at this

theorem A2_qQuery_lower (n : ℕ) :
    (7 / 1376 : ℝ) * Real.sqrt n
      ≤ (qQuery (fun w : Fin n → A2 => wordProd (id : A2 → A2) w) (1 / 3) : ℝ) :=
  rees_qQuery_lower n

theorem B2_qQuery_lower (n : ℕ) :
    (7 / 1376 : ℝ) * Real.sqrt n
      ≤ (qQuery (fun w : Fin n → B2 => wordProd (id : B2 → B2) w) (1 / 3) : ℝ) :=
  rees_qQuery_lower n

end MonoidProduct.Infix
