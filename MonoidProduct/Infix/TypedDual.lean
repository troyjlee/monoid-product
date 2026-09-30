import MonoidProduct.Infix.Typed
import MonoidProduct.Infix.Dual

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The uniform adversary for typed clean gaps (decision form)

`hasDual_infZ`: for every alphabet `Ω`, projection `π : Ω → Fin 3` and relation
`Z`, the typed clean-infix predicate `infZ π Z` on words of length `m` has a
dual of cost `13·√m·λ(m)` — independent of `Ω` and `Z`.  This is the decision
form of the typed longest-gap bound, built on the structural completion
identity `typed_completion`:

* **structural sectors** (interior, two saturation columns, equality and
  containment corrections) reproduce the identity's left side; wherever a
  positive and a negative structural vector are both nonzero at a position,
  the projected letters differ, so the query filter is automatically satisfied;
* **repair sectors** (a position tag at the left end, a position ⊗ letter tag
  at the right end) contribute exactly `[gap preserved]`: a negative word that
  preserves the gap structurally carries an endpoint pair outside `Z`, so it
  differs from the positive word at one of the two ends.
-/

namespace MonoidProduct.Infix

open Finset QuantumQueryComplexity

variable {m : ℕ}

/-- Structural index: interior, left column, right column, equality `(t, tag)`,
containment `tag`. -/
abbrev SIdx (m : ℕ) := Fin m ⊕ SatIdx m ⊕ SatIdx m ⊕ (Fin m × Fin m) ⊕ Fin m

/-- Repair index: position tag, position ⊗ letter tag. -/
abbrev RIdx (m : ℕ) (Ω : Type) := Fin m ⊕ (Fin m × Ω)

abbrev TIdx (m : ℕ) (Ω : Type) := SIdx m ⊕ RIdx m Ω

/-! ## Cell predicates of a projected word -/

/-- `q` is a blocking letter carrying its cell. -/
def CarrierOne (p : Word m) (q : ℕ) : Prop :=
  isOne p q ∧ HasTwoLE p q ∧ HasTwoGT p q ∧ carrierAt p q = q

/-- `q` is an endpoint letter ending a clean cell. -/
def CarrierTwo (p : Word m) (q : ℕ) : Prop :=
  isTwo p q ∧ 1 ≤ q ∧ HasTwoLE p (q - 1) ∧ IsClean p (lastTwoLE p (q - 1)) q

/-- `q` is an endpoint letter starting a clean cell. -/
def CleanStart (p : Word m) (q : ℕ) : Prop :=
  isTwo p q ∧ HasTwoGT p q ∧ IsClean p q (firstTwoGT p q)

/-- `q` is a neutral letter strictly inside a clean cell. -/
def InteriorClean (p : Word m) (q : ℕ) : Prop :=
  ¬ isTwo p q ∧ ¬ isOne p q ∧ HasTwoLE p q ∧ HasTwoGT p q
    ∧ IsClean p (lastTwoLE p q) (firstTwoGT p q)

/-- The negative interior vector at `q` covers `t`. -/
def Cov (p : Word m) (q t : ℕ) : Prop :=
  (CarrierOne p q ∧ lastTwoLE p q ≤ t ∧ t < firstTwoGT p q)
    ∨ (CarrierTwo p q ∧ lastTwoLE p (q - 1) ≤ t ∧ t < q)

noncomputable instance (p : Word m) (q : ℕ) : Decidable (CarrierOne p q) := Classical.dec _
noncomputable instance (p : Word m) (q : ℕ) : Decidable (CarrierTwo p q) := Classical.dec _
noncomputable instance (p : Word m) (q : ℕ) : Decidable (CleanStart p q) := Classical.dec _
noncomputable instance (p : Word m) (q : ℕ) : Decidable (InteriorClean p q) := Classical.dec _
noncomputable instance (p : Word m) (q t : ℕ) : Decidable (Cov p q t) := Classical.dec _

/-- Every position of a cell `[a, b)` (consecutive endpoint letters) has that cell. -/
lemma cell_data {p : Word m} {a b t : ℕ} (ha : isTwo p a) (hb : isTwo p b) (hab : a < b)
    (hno : ∀ q, a < q → q < b → ¬ isTwo p q) (h1 : a ≤ t) (h2 : t < b) :
    HasTwoLE p t ∧ HasTwoGT p t ∧ lastTwoLE p t = a ∧ firstTwoGT p t = b := by
  have hLt : HasTwoLE p t := ⟨a, h1, ha⟩
  have hGt : HasTwoGT p t := ⟨b, h2, hb⟩
  refine ⟨hLt, hGt, le_antisymm ?_ (le_lastTwoLE h1 ha), le_antisymm (firstTwoGT_le h2 hb) ?_⟩
  · by_contra hcon
    push Not at hcon
    exact hno _ hcon (by have := lastTwoLE_le p t; omega) (isTwo_lastTwoLE hLt)
  · by_contra hcon
    push Not at hcon
    exact hno _ (by have := lt_firstTwoGT p t (lt_m_of_hasTwoGT hGt); omega) hcon
      (isTwo_firstTwoGT hGt)

lemma no_two_in_cell {p : Word m} {t : ℕ} :
    ∀ q, lastTwoLE p t < q → q < firstTwoGT p t → ¬ isTwo p q :=
  fun _ h1 h2 => not_isTwo_of_mem_gap h1 h2

/-- **Covering lemma**: `q` covers `t` iff `t` lies in a cell and `q` is its carrier. -/
lemma cov_iff {p : Word m} {q t : ℕ} :
    Cov p q t ↔ HasTwoLE p t ∧ HasTwoGT p t ∧ q = carrierAt p t := by
  constructor
  · rintro (⟨⟨h1, hL, hG, hc⟩, ht1, ht2⟩ | ⟨⟨h2, hq1, hL, hcl⟩, ht1, ht2⟩)
    · obtain ⟨hLt, hGt, e3, e4⟩ := cell_data (isTwo_lastTwoLE hL) (isTwo_firstTwoGT hG)
        (lt_of_le_of_lt (lastTwoLE_le p q) (lt_firstTwoGT p q (lt_m_of_hasTwoGT hG)))
        no_two_in_cell ht1 ht2
      refine ⟨hLt, hGt, ?_⟩
      unfold carrierAt at hc ⊢
      rw [e3, e4, hc]
    · have hA := isTwo_lastTwoLE hL
      have hAq : lastTwoLE p (q - 1) < q := by have := lastTwoLE_le p (q - 1); omega
      obtain ⟨hLt, hGt, e3, e4⟩ := cell_data hA h2 hAq
        (fun s hs1 hs2 => not_isTwo_of_lastTwoLE_lt hs1 (by omega)) ht1 ht2
      refine ⟨hLt, hGt, ?_⟩
      unfold carrierAt
      rw [e3, e4, carrier_of_clean hcl]
  · rintro ⟨hL, hG, hq⟩
    have hA := isTwo_lastTwoLE hL
    have hB := isTwo_firstTwoGT hG
    have hAt := lastTwoLE_le p t
    have htB := lt_firstTwoGT p t (lt_m_of_hasTwoGT hG)
    by_cases hcl : IsClean p (lastTwoLE p t) (firstTwoGT p t)
    · right
      have hqB : q = firstTwoGT p t := by rw [hq]; unfold carrierAt; exact carrier_of_clean hcl
      obtain ⟨_, _, e3, _⟩ := cell_data hA hB (hAt.trans_lt htB) no_two_in_cell
        (t := firstTwoGT p t - 1) (by omega) (by omega)
      refine ⟨⟨hqB ▸ hB, by omega, ?_, ?_⟩, ?_, ?_⟩
      · rw [hqB]; exact ⟨_, by omega, hA⟩
      · rw [hqB, e3]; exact hcl
      · rw [hqB, e3]; exact hAt
      · omega
    · left
      obtain ⟨hc1, hc2, hc3, _⟩ := carrier_of_not_clean hcl
      have hqc : q = carrier p (lastTwoLE p t) (firstTwoGT p t) := hq
      obtain ⟨hLc, hGc, e3, e4⟩ := cell_data hA hB (hAt.trans_lt htB) no_two_in_cell
        (t := carrier p (lastTwoLE p t) (firstTwoGT p t)) hc1.le hc2
      refine ⟨⟨hqc ▸ hc3, hqc ▸ hLc, hqc ▸ hGc, ?_⟩, ?_, ?_⟩
      · rw [hqc]; unfold carrierAt; rw [e3, e4]
      · rw [hqc, e3]; exact hAt
      · rw [hqc, e4]; exact htB

/-! ## Witness ends of a positive word -/

section Vectors

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (π : Ω → Fin 3) (Z : Ω → Ω → Bool)

/-- The letter at a natural-number position (`none` off the word). -/
def letterAt (x : Fin m → Ω) (i : ℕ) : Option Ω := if h : i < m then some (x ⟨i, h⟩) else none

lemma letterAt_of_lt (x : Fin m → Ω) {i : ℕ} (h : i < m) : letterAt x i = some (x ⟨i, h⟩) := by
  unfold letterAt; rw [dif_pos h]

/-- A chosen `Z`-clean witness of a positive word. -/
noncomputable def zwit {x : Fin m → Ω} (h : infZ π Z x = true) : Fin m × Fin m :=
  (Classical.choose ((infZ_eq_true_iff π Z).1 h),
    Classical.choose (Classical.choose_spec ((infZ_eq_true_iff π Z).1 h)))

lemma zwit_spec {x : Fin m → Ω} (h : infZ π Z x = true) :
    IsZWitness π Z x (zwit π Z h).1 (zwit π Z h).2 :=
  Classical.choose_spec (Classical.choose_spec ((infZ_eq_true_iff π Z).1 h))

/-- The left end of the chosen witness (`0` for negative words). -/
noncomputable def zl (x : Fin m → Ω) : ℕ :=
  if h : infZ π Z x = true then ((zwit π Z h).1 : ℕ) else 0

/-- The right end of the chosen witness. -/
noncomputable def zr (x : Fin m → Ω) : ℕ :=
  if h : infZ π Z x = true then ((zwit π Z h).2 : ℕ) else 0

variable {π Z}

lemma zl_eq {x : Fin m → Ω} (h : infZ π Z x = true) : zl π Z x = (zwit π Z h).1 := by
  unfold zl; rw [dif_pos h]

lemma zr_eq {x : Fin m → Ω} (h : infZ π Z x = true) : zr π Z x = (zwit π Z h).2 := by
  unfold zr; rw [dif_pos h]

lemma zl_lt_zr {x : Fin m → Ω} (h : infZ π Z x = true) : zl π Z x < zr π Z x := by
  rw [zl_eq h, zr_eq h]; exact (zwit_spec π Z h).1

lemma zr_lt {x : Fin m → Ω} (h : infZ π Z x = true) : zr π Z x < m := by
  rw [zr_eq h]; exact Fin.isLt _

lemma zl_two {x : Fin m → Ω} (h : infZ π Z x = true) : isTwo (proj π x) (zl π Z x) := by
  refine ⟨(zl_lt_zr h).trans (zr_lt h), ?_⟩
  rw [show (⟨zl π Z x, (zl_lt_zr h).trans (zr_lt h)⟩ : Fin m) = (zwit π Z h).1 from
    Fin.ext (zl_eq h)]
  exact (zwit_spec π Z h).2.1

lemma zr_two {x : Fin m → Ω} (h : infZ π Z x = true) : isTwo (proj π x) (zr π Z x) := by
  refine ⟨zr_lt h, ?_⟩
  rw [show (⟨zr π Z x, zr_lt h⟩ : Fin m) = (zwit π Z h).2 from Fin.ext (zr_eq h)]
  exact (zwit_spec π Z h).2.2.1

lemma z_rel {x : Fin m → Ω} (h : infZ π Z x = true) :
    Z (x ⟨zl π Z x, (zl_lt_zr h).trans (zr_lt h)⟩) (x ⟨zr π Z x, zr_lt h⟩) = true := by
  rw [show (⟨zl π Z x, (zl_lt_zr h).trans (zr_lt h)⟩ : Fin m) = (zwit π Z h).1 from
    Fin.ext (zl_eq h), show (⟨zr π Z x, zr_lt h⟩ : Fin m) = (zwit π Z h).2 from Fin.ext (zr_eq h)]
  exact (zwit_spec π Z h).2.2.2.1

lemma z_mid {x : Fin m → Ω} (h : infZ π Z x = true) {q : ℕ} (h1 : zl π Z x < q)
    (h2 : q < zr π Z x) (hq : q < m) : proj π x ⟨q, hq⟩ = 0 := by
  have := (zwit_spec π Z h).2.2.2.2 ⟨q, hq⟩
  simp only [Fin.lt_def] at this
  rw [← zl_eq h, ← zr_eq h] at this
  exact this h1 h2
lemma z_mid_not_two {x : Fin m → Ω} (h : infZ π Z x = true) {q : ℕ} (h1 : zl π Z x < q)
    (h2 : q < zr π Z x) : ¬ isTwo (proj π x) q := by
  rintro ⟨hq, h2'⟩
  rw [z_mid h h1 h2 hq] at h2'
  exact absurd h2' (by decide)

lemma z_mid_not_one {x : Fin m → Ω} (h : infZ π Z x = true) {q : ℕ} (h1 : zl π Z x < q)
    (h2 : q < zr π Z x) : ¬ isOne (proj π x) q := by
  rintro ⟨hq, h2'⟩
  rw [z_mid h h1 h2 hq] at h2'
  exact absurd h2' (by decide)

/-- **The negative words**: every structurally clean pair is outside `Z`. -/
lemma neg_not_rel {y : Fin m → Ω} (hy : infZ π Z y = false) {a b : ℕ} (ha : isTwo (proj π y) a)
    (hb : isTwo (proj π y) b) (hab : a < b)
    (hcl : ∀ q, a < q → q < b → ∀ h : q < m, proj π y ⟨q, h⟩ = 0) :
    Z (y ⟨a, isTwo_lt ha⟩) (y ⟨b, isTwo_lt hb⟩) = false := by
  by_contra hcon
  have hZ : Z (y ⟨a, isTwo_lt ha⟩) (y ⟨b, isTwo_lt hb⟩) = true := by
    cases h : Z (y ⟨a, isTwo_lt ha⟩) (y ⟨b, isTwo_lt hb⟩)
    · exact absurd h hcon
    · rfl
  refine ((infZ_eq_false_iff π Z).1 hy) ⟨a, isTwo_lt ha⟩ ⟨b, isTwo_lt hb⟩ ⟨hab, ha.2, hb.2, hZ, ?_⟩
  intro q h1 h2
  exact hcl q h1 h2 q.isLt

/-! ## The vectors -/

variable (π Z)

/-- The positive vectors. -/
noncomputable def uT (x : Fin m → Ω) (q : Fin m) : TIdx m Ω → ℝ
  | Sum.inl (Sum.inl t) =>
      if zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
      then 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) else 0
  | Sum.inl (Sum.inr (Sum.inl s)) =>
      if (q : ℕ) = zl π Z x then satA m (zr π Z x - zl π Z x) s else 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl s))) =>
      if (q : ℕ) = zr π Z x then satA m (zr π Z x - zl π Z x) s else 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))) =>
      if zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
          ∧ (b : ℕ) = zr π Z x
      then 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) else 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))) =>
      if (q : ℕ) = zl π Z x ∧ (b : ℕ) = zr π Z x then 1 else 0
  | Sum.inr (Sum.inl b) => if (q : ℕ) = zl π Z x ∧ (b : ℕ) = zr π Z x then 1 else 0
  | Sum.inr (Sum.inr (t, a)) =>
      if (q : ℕ) = zr π Z x ∧ (t : ℕ) = zl π Z x ∧ letterAt x (zl π Z x) = some a then 1 else 0

/-- The negative vectors. -/
noncomputable def vT (y : Fin m → Ω) (q : Fin m) : TIdx m Ω → ℝ
  | Sum.inl (Sum.inl t) => if Cov (proj π y) q t then 1 else 0
  | Sum.inl (Sum.inr (Sum.inl s)) =>
      if NoTwo (proj π y) then satBInf m s
      else if ActL (proj π y) q then satB m (max 1 (DL (proj π y) q)) s else 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl s))) =>
      if ActR (proj π y) q then satB m (max 1 (DR (proj π y) q)) s else 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))) =>
      if CleanStart (proj π y) q ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < firstTwoGT (proj π y) q
          ∧ (b : ℕ) = firstTwoGT (proj π y) q
      then 1 else 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))) =>
      if InteriorClean (proj π y) q ∧ (b : ℕ) = firstTwoGT (proj π y) q then 1 else 0
  | Sum.inr (Sum.inl b) =>
      if CleanStart (proj π y) q ∧ (b : ℕ) = firstTwoGT (proj π y) q then 1 else 0
  | Sum.inr (Sum.inr (t, a)) =>
      if CarrierTwo (proj π y) q ∧ (t : ℕ) = lastTwoLE (proj π y) (q - 1)
          ∧ letterAt y (lastTwoLE (proj π y) (q - 1)) = some a
      then 1 else 0

variable {π Z}

/-- Whenever a positive and a negative structural vector are both nonzero at `q`, the
projected letters differ; so equal letters kill every structural product. -/
lemma struct_zero_of_eq {x y : Fin m → Ω} (hx : infZ π Z x = true) {q : Fin m}
    (hq : x q = y q) (k : SIdx m) : uT π Z x q (Sum.inl k) * vT π y q (Sum.inl k) = 0 := by
  have hpq : proj π x q = proj π y q := by simp [proj, hq]
  rcases k with t | s | s | ⟨t, b⟩ | b
  · -- interior: `π x_q = 0`, so `q` is neither blocking nor an endpoint in `y`
    simp only [uT, vT]
    by_cases h1 : zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
    · rw [if_pos h1, if_neg, mul_zero]
      have h0 : proj π y q = 0 := by rw [← hpq]; exact z_mid hx h1.1 h1.2.1 q.isLt
      rintro (⟨⟨⟨_, h1'⟩, _⟩, _⟩ | ⟨⟨⟨_, h2'⟩, _⟩, _⟩)
      · simp only [Fin.eta] at h1'; rw [h0] at h1'; exact absurd h1' (by decide)
      · simp only [Fin.eta] at h2'; rw [h0] at h2'; exact absurd h2' (by decide)
    · rw [if_neg h1, zero_mul]
  · -- left column: `q = zl`, so `y_q` is an endpoint letter
    simp only [uT, vT]
    by_cases h1 : (q : ℕ) = zl π Z x
    · have h2 : isTwo (proj π y) q := by
        refine ⟨q.isLt, ?_⟩
        have := zl_two hx
        rw [← h1] at this
        obtain ⟨_, h2⟩ := this
        simp only [Fin.eta] at h2
        rw [← hpq]; exact h2
      rw [if_pos h1, if_neg (fun h => noTwo_iff.1 h _ h2), if_neg (fun h => h.1 h2), mul_zero]
    · rw [if_neg h1, zero_mul]
  · simp only [uT, vT]
    by_cases h1 : (q : ℕ) = zr π Z x
    · have h2 : isTwo (proj π y) q := by
        refine ⟨q.isLt, ?_⟩
        have := zr_two hx
        rw [← h1] at this
        obtain ⟨_, h2⟩ := this
        simp only [Fin.eta] at h2
        rw [← hpq]; exact h2
      rw [if_pos h1, if_neg (fun h => h.1 h2), mul_zero]
    · rw [if_neg h1, zero_mul]
  · simp only [uT, vT]
    by_cases h1 : zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
        ∧ (b : ℕ) = zr π Z x
    · rw [if_pos h1, if_neg, mul_zero]
      have h0 : proj π y q = 0 := by rw [← hpq]; exact z_mid hx h1.1 h1.2.1 q.isLt
      rintro ⟨⟨⟨_, h2'⟩, _⟩, _⟩
      simp only [Fin.eta] at h2'; rw [h0] at h2'; exact absurd h2' (by decide)
    · rw [if_neg h1, zero_mul]
  · simp only [uT, vT]
    by_cases h1 : (q : ℕ) = zl π Z x ∧ (b : ℕ) = zr π Z x
    · have h2 : isTwo (proj π y) q := by
        refine ⟨q.isLt, ?_⟩
        have := zl_two hx
        rw [← h1.1] at this
        obtain ⟨_, h2⟩ := this
        simp only [Fin.eta] at h2
        rw [← hpq]; exact h2
      rw [if_pos h1, if_neg (fun h => h.1.1 h2), mul_zero]
    · rw [if_neg h1, zero_mul]

end Vectors

/-! ## The constraint -/

section Constraint

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {π : Ω → Fin 3} {Z : Ω → Ω → Bool}

/-- A sum over `Fin m` of a summand supported at the position `c`. -/
lemma sum_fin_eq (c : ℕ) (g : Fin m → ℝ) :
    ∑ q : Fin m, (if (q : ℕ) = c then g q else 0) = if h : c < m then g ⟨c, h⟩ else 0 := by
  by_cases h : c < m
  · rw [dif_pos h, Finset.sum_eq_single ⟨c, h⟩]
    · rw [if_pos rfl]
    · intro q _ hq; rw [if_neg]; intro e; exact hq (Fin.ext e)
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [dif_neg h]
    exact Finset.sum_eq_zero fun q _ => by rw [if_neg]; intro e; exact h (e ▸ q.isLt)

lemma lastTwoLE_self {p : Word m} {q : ℕ} (h : isTwo p q) : lastTwoLE p q = q :=
  le_antisymm (lastTwoLE_le p q) (le_lastTwoLE le_rfl h)

/-- The equality correction fires at exactly one position. -/
lemma eqCase_char (p : Word m) {l r q : ℕ} (hlr : l < r) :
    (l < q ∧ q < r ∧ CleanStart p q ∧ firstTwoGT p q = r)
      ↔ (EqCase p l r ∧ q = lastTwoLE p (r - 1)) := by
  constructor
  · rintro ⟨h1, h2, ⟨hq2, hG, hcl⟩, hB⟩
    have hL1 : HasTwoLE p (r - 1) := ⟨q, by omega, hq2⟩
    have hqa : q ≤ lastTwoLE p (r - 1) := le_lastTwoLE (by omega) hq2
    have haq : lastTwoLE p (r - 1) ≤ q := by
      by_contra hcon
      push Not at hcon
      exact @not_isTwo_of_lt_firstTwoGT m p q (lastTwoLE p (r - 1)) hcon
        (by rw [hB]; have := lastTwoLE_le p (r - 1); omega) (isTwo_lastTwoLE hL1)
    have e : lastTwoLE p (r - 1) = q := le_antisymm haq hqa
    refine ⟨⟨hB ▸ isTwo_firstTwoGT hG, hL1, by omega, ?_⟩, e.symm⟩
    rw [e, ← hB]; exact hcl
  · rintro ⟨⟨hr2, hL1, hla, hcl⟩, rfl⟩
    have ha2 := isTwo_lastTwoLE hL1
    have har : lastTwoLE p (r - 1) < r := by have := lastTwoLE_le p (r - 1); omega
    have hB : firstTwoGT p (lastTwoLE p (r - 1)) = r := by
      apply le_antisymm (firstTwoGT_le har hr2)
      by_contra hcon
      push Not at hcon
      exact not_isTwo_of_lastTwoLE_lt (lt_firstTwoGT p _ (isTwo_lt ha2)) (by omega)
        (isTwo_firstTwoGT ⟨r, har, hr2⟩)
    exact ⟨hla, har, ⟨ha2, ⟨r, har, hr2⟩, by rw [hB]; exact hcl⟩, hB⟩

lemma ctCase_iff (p : Word m) {l r : ℕ} :
    CtCase p l r ↔ InteriorClean p l ∧ firstTwoGT p l = r := by
  constructor
  · rintro ⟨hL, hG, hl2, hB, hcl⟩
    refine ⟨⟨hl2, ?_, hL, hG, by rw [hB]; exact hcl⟩, hB⟩
    intro h1
    have hA : lastTwoLE p l < l := lastTwoLE_lt_of_not_isTwo hL hl2
    exact hcl l hA (by rw [← hB]; exact lt_firstTwoGT p l (isOne_lt h1)) h1
  · rintro ⟨⟨hl2, _, hL, hG, hcl⟩, hB⟩
    exact ⟨hL, hG, hl2, hB, by rw [← hB]; exact hcl⟩

lemma strPres_iff_left (p : Word m) {l r : ℕ} (hlr : l < r) (hr : r < m) :
    StrPres p l r ↔ CleanStart p l ∧ firstTwoGT p l = r := by
  constructor
  · rintro ⟨hl2, hr2, h0⟩
    have hG : HasTwoGT p l := ⟨r, hlr, hr2⟩
    have hB : firstTwoGT p l = r := by
      apply le_antisymm (firstTwoGT_le hlr hr2)
      by_contra hcon
      push Not at hcon
      obtain ⟨hlt, h2⟩ := isTwo_firstTwoGT hG
      have := h0 _ (lt_firstTwoGT p l (isTwo_lt hl2)) hcon hlt
      rw [this] at h2; exact absurd h2 (by decide)
    refine ⟨⟨hl2, hG, ?_⟩, hB⟩
    rw [hB]
    rintro q h1 h2 ⟨hq, h1'⟩
    have := h0 q h1 h2 hq
    rw [this] at h1'; exact absurd h1' (by decide)
  · rintro ⟨⟨hl2, hG, hcl⟩, hB⟩
    refine ⟨hl2, hB ▸ isTwo_firstTwoGT hG, fun q h1 h2 hq => ?_⟩
    exact isOne_or_zero hq (not_isTwo_of_lt_firstTwoGT h1 (by omega)) (hcl q h1 (by omega))

lemma strPres_iff_right (p : Word m) {l r : ℕ} (hlr : l < r) (hr : r < m) :
    StrPres p l r ↔ CarrierTwo p r ∧ lastTwoLE p (r - 1) = l := by
  constructor
  · rintro ⟨hl2, hr2, h0⟩
    have hL : HasTwoLE p (r - 1) := ⟨l, by omega, hl2⟩
    have hA : lastTwoLE p (r - 1) = l := by
      apply le_antisymm _ (le_lastTwoLE (by omega) hl2)
      by_contra hcon
      push Not at hcon
      obtain ⟨hlt, h2⟩ := isTwo_lastTwoLE hL
      have := h0 _ hcon (by have := lastTwoLE_le p (r - 1); omega) hlt
      rw [this] at h2; exact absurd h2 (by decide)
    refine ⟨⟨hr2, by omega, hL, ?_⟩, hA⟩
    rw [hA]
    rintro q h1 h2 ⟨hq, h1'⟩
    have := h0 q h1 h2 hq
    rw [this] at h1'; exact absurd h1' (by decide)
  · rintro ⟨⟨hr2, _, hL, hcl⟩, hA⟩
    refine ⟨hA ▸ isTwo_lastTwoLE hL, hr2, fun q h1 h2 hq => ?_⟩
    rw [hA] at hcl
    exact isOne_or_zero hq (@not_isTwo_of_lastTwoLE_lt m p (r - 1) q (by omega) (by omega))
      (hcl q h1 h2)

variable {x y : Fin m → Ω}

/-- The interior contribution at a fixed coordinate `t`. -/
lemma t_interior_at (hx : infZ π Z x = true) (t : Fin m) :
    ∑ q : Fin m, uT π Z x q (Sum.inl (Sum.inl t)) * vT π y q (Sum.inl (Sum.inl t))
      = if zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
        then phiC (proj π y) (zl π Z x) (zr π Z x) t / ((zr π Z x - zl π Z x : ℕ) : ℝ)
        else 0 := by
  have key : ∀ q : Fin m, uT π Z x q (Sum.inl (Sum.inl t)) * vT π y q (Sum.inl (Sum.inl t))
      = if (q : ℕ) = carrierAt (proj π y) t then
          (if (zl π Z x < carrierAt (proj π y) t ∧ carrierAt (proj π y) t < zr π Z x
                ∧ zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x)
              ∧ (HasTwoLE (proj π y) t ∧ HasTwoGT (proj π y) t)
            then 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) else 0)
        else 0 := by
    intro q
    simp only [uT, vT]
    by_cases hcov : Cov (proj π y) q t
    · obtain ⟨hL, hG, hq⟩ := cov_iff.1 hcov
      rw [if_pos hcov, mul_one, if_pos hq, ← hq]
      by_cases h1 : zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
      · rw [if_pos h1, if_pos ⟨h1, hL, hG⟩]
      · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    · rw [if_neg hcov, mul_zero]
      by_cases hq : (q : ℕ) = carrierAt (proj π y) t
      · rw [if_pos hq, if_neg (fun h => hcov (cov_iff.2 ⟨h.2.1, h.2.2, hq⟩))]
      · rw [if_neg hq]
  rw [Finset.sum_congr rfl (fun q _ => key q), sum_fin_eq]
  unfold phiC
  by_cases ht : zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
  · rw [if_pos ht]
    by_cases hc : HasTwoLE (proj π y) t ∧ HasTwoGT (proj π y) t
        ∧ zl π Z x < carrierAt (proj π y) t ∧ carrierAt (proj π y) t < zr π Z x
    · have hcm : carrierAt (proj π y) t < m := hc.2.2.2.trans (zr_lt hx)
      rw [dif_pos hcm, if_pos ⟨⟨hc.2.2.1, hc.2.2.2, ht⟩, hc.1, hc.2.1⟩, if_pos hc]
    · rw [if_neg hc, zero_div]
      split_ifs with h1 h2
      · exact absurd ⟨h2.2.1, h2.2.2, h2.1.1, h2.1.2.1⟩ hc
      · rfl
      · rfl
  · rw [if_neg ht]
    split_ifs with h1 h2
    · exact absurd ⟨h2.1.2.2.1, h2.1.2.2.2⟩ ht
    · rfl
    · rfl

lemma t_interior_sum (hx : infZ π Z x = true) :
    ∑ q : Fin m, ∑ t : Fin m, uT π Z x q (Sum.inl (Sum.inl t)) * vT π y q (Sum.inl (Sum.inl t))
      = (∑ t ∈ Ico (zl π Z x) (zr π Z x), phiC (proj π y) (zl π Z x) (zr π Z x) t)
          / ((zr π Z x - zl π Z x : ℕ) : ℝ) := by
  classical
  rw [Finset.sum_comm]
  simp only [t_interior_at hx]
  rw [Fin.sum_univ_eq_sum_range (fun t => if zl π Z x ≤ t ∧ t < zr π Z x
    then phiC (proj π y) (zl π Z x) (zr π Z x) t / ((zr π Z x - zl π Z x : ℕ) : ℝ) else 0) m,
    ← Finset.sum_filter]
  have hfilt : (range m).filter (fun t => zl π Z x ≤ t ∧ t < zr π Z x)
      = Ico (zl π Z x) (zr π Z x) := by
    ext t
    simp only [mem_filter, mem_range, mem_Ico]
    have := zr_lt hx
    omega
  rw [hfilt, Finset.sum_div]

/-- The left column. -/
lemma t_left_sum (hx : infZ π Z x = true) :
    ∑ q : Fin m, ∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inl s)))
        * vT π y q (Sum.inl (Sum.inr (Sum.inl s)))
      = if NoTwo (proj π y) then 1
        else if ActL (proj π y) (zl π Z x)
          then min 1 ((DL (proj π y) (zl π Z x) : ℝ) / ((zr π Z x - zl π Z x : ℕ) : ℝ)) else 0 := by
  have hlm : zl π Z x < m := (zl_lt_zr hx).trans (zr_lt hx)
  have hG1 : 1 ≤ zr π Z x - zl π Z x := by have := zl_lt_zr hx; omega
  have hGm : zr π Z x - zl π Z x ≤ m := by have := zr_lt hx; omega
  have key : ∀ q : Fin m, ∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inl s)))
        * vT π y q (Sum.inl (Sum.inr (Sum.inl s)))
      = if (q : ℕ) = zl π Z x then
          ∑ s, satA m (zr π Z x - zl π Z x) s * vT π y q (Sum.inl (Sum.inr (Sum.inl s))) else 0 := by
    intro q
    by_cases hq : (q : ℕ) = zl π Z x
    · rw [if_pos hq]; refine Finset.sum_congr rfl fun s _ => ?_; simp only [uT]; rw [if_pos hq]
    · rw [if_neg hq]; refine Finset.sum_eq_zero fun s _ => ?_; simp only [uT]
      rw [if_neg hq, zero_mul]
  rw [Finset.sum_congr rfl (fun q _ => key q), sum_fin_eq, dif_pos hlm]
  simp only [vT]
  by_cases hno : NoTwo (proj π y)
  · simp only [if_pos hno]
    exact satA_mul_satBInf hGm
  · simp only [if_neg hno]
    by_cases hact : ActL (proj π y) (zl π Z x)
    · simp only [if_pos hact]
      have hD1 : 1 ≤ DL (proj π y) (zl π Z x) := by
        have := lt_firstTwoGT (proj π y) (zl π Z x) hlm; unfold DL; omega
      have hDm : DL (proj π y) (zl π Z x) ≤ m := by
        have := firstTwoGT_le_m (proj π y) (zl π Z x); unfold DL; omega
      rw [max_eq_right hD1, satA_mul_satB hG1 hGm hD1 hDm]
    · simp only [if_neg hact, mul_zero, Finset.sum_const_zero]

/-- The right column. -/
lemma t_right_sum (hx : infZ π Z x = true) :
    ∑ q : Fin m, ∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
        * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
      = if ActR (proj π y) (zr π Z x)
          then min 1 ((DR (proj π y) (zr π Z x) : ℝ) / ((zr π Z x - zl π Z x : ℕ) : ℝ)) else 0 := by
  have hrm : zr π Z x < m := zr_lt hx
  have hG1 : 1 ≤ zr π Z x - zl π Z x := by have := zl_lt_zr hx; omega
  have hGm : zr π Z x - zl π Z x ≤ m := by omega
  have key : ∀ q : Fin m, ∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
        * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
      = if (q : ℕ) = zr π Z x then
          ∑ s, satA m (zr π Z x - zl π Z x) s * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
        else 0 := by
    intro q
    by_cases hq : (q : ℕ) = zr π Z x
    · rw [if_pos hq]; refine Finset.sum_congr rfl fun s _ => ?_; simp only [uT]; rw [if_pos hq]
    · rw [if_neg hq]; refine Finset.sum_eq_zero fun s _ => ?_; simp only [uT]
      rw [if_neg hq, zero_mul]
  rw [Finset.sum_congr rfl (fun q _ => key q), sum_fin_eq, dif_pos hrm]
  simp only [vT]
  by_cases hact : ActR (proj π y) (zr π Z x)
  · simp only [if_pos hact]
    have hD1 : 1 ≤ DR (proj π y) (zr π Z x) := by
      have := lastTwoLE_lt_of_not_isTwo hact.2.1 hact.1; unfold DR; omega
    have hDm : DR (proj π y) (zr π Z x) ≤ m := by unfold DR; omega
    rw [max_eq_right hD1, satA_mul_satB hG1 hGm hD1 hDm]
  · simp only [if_neg hact, mul_zero, Finset.sum_const_zero]

/-- The equality correction. -/
lemma t_eq_sum (hx : infZ π Z x = true) :
    ∑ q : Fin m, ∑ k : Fin m × Fin m,
        uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
          * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
      = if EqCase (proj π y) (zl π Z x) (zr π Z x)
        then ((zr π Z x - lastTwoLE (proj π y) (zr π Z x - 1) : ℕ) : ℝ)
          / ((zr π Z x - zl π Z x : ℕ) : ℝ)
        else 0 := by
  have hrm := zr_lt hx
  have hlr := zl_lt_zr hx
  have key : ∀ q : Fin m, ∑ k : Fin m × Fin m,
        uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
          * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
      = if (q : ℕ) = lastTwoLE (proj π y) (zr π Z x - 1) then
          (if EqCase (proj π y) (zl π Z x) (zr π Z x)
            then ((zr π Z x - (q : ℕ) : ℕ) : ℝ) / ((zr π Z x - zl π Z x : ℕ) : ℝ) else 0)
        else 0 := by
    intro q
    rw [Fintype.sum_prod_type]
    have inner : ∀ t : Fin m, ∑ b : Fin m,
        uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
          * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
        = if (zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ CleanStart (proj π y) q
              ∧ firstTwoGT (proj π y) q = zr π Z x) ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < zr π Z x
          then 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) else 0 := by
      intro t
      have : ∀ b : Fin m,
          uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
            * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
          = if (b : ℕ) = zr π Z x then
              (if (zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ CleanStart (proj π y) q
                  ∧ firstTwoGT (proj π y) q = zr π Z x) ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < zr π Z x
                then 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) else 0)
            else 0 := by
        intro b
        simp only [uT, vT]
        by_cases hb : (b : ℕ) = zr π Z x
        · rw [if_pos hb]
          by_cases hC : (zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ CleanStart (proj π y) q
              ∧ firstTwoGT (proj π y) q = zr π Z x) ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < zr π Z x
          · rw [if_pos hC, if_pos ⟨hC.1.1, hC.1.2.1, by omega, hC.2.2, hb⟩,
              if_pos ⟨hC.1.2.2.1, hC.2.1, by rw [hC.1.2.2.2]; exact hC.2.2, by rw [hb, hC.1.2.2.2]⟩,
              mul_one]
          · rw [if_neg hC]
            by_cases h1 : zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
                ∧ (b : ℕ) = zr π Z x
            · rw [if_pos h1, if_neg, mul_zero]
              rintro ⟨hcs, hqt, _, hbB⟩
              exact hC ⟨⟨h1.1, h1.2.1, hcs, by omega⟩, hqt, h1.2.2.2.1⟩
            · rw [if_neg h1, zero_mul]
        · rw [if_neg hb, if_neg (fun h => hb h.2.2.2.2), zero_mul]
      rw [Finset.sum_congr rfl (fun b _ => this b), sum_fin_eq, dif_pos hrm]
    rw [Finset.sum_congr rfl (fun t _ => inner t)]
    by_cases hC : zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ CleanStart (proj π y) q
        ∧ firstTwoGT (proj π y) q = zr π Z x
    · obtain ⟨heq, hq⟩ := (eqCase_char (proj π y) hlr).1 hC
      rw [if_pos hq, if_pos heq]
      have : ∀ t : Fin m, (if (zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ CleanStart (proj π y) q
              ∧ firstTwoGT (proj π y) q = zr π Z x) ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < zr π Z x
            then 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) else 0)
          = 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ)
              * (if (q : ℕ) ≤ t ∧ (t : ℕ) < zr π Z x then 1 else 0) := by
        intro t
        by_cases h : (q : ℕ) ≤ t ∧ (t : ℕ) < zr π Z x
        · rw [if_pos ⟨hC, h⟩, if_pos h, mul_one]
        · rw [if_neg (fun h' => h h'.2), if_neg h, mul_zero]
      rw [Finset.sum_congr rfl (fun t _ => this t), ← Finset.mul_sum, sum_ite_Ico m q _ hrm.le]
      ring
    · have hz : ∀ t : Fin m, (if (zl π Z x < q ∧ (q : ℕ) < zr π Z x ∧ CleanStart (proj π y) q
              ∧ firstTwoGT (proj π y) q = zr π Z x) ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < zr π Z x
            then 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) else 0) = 0 := fun t => by
        rw [if_neg (fun h => hC h.1)]
      rw [Finset.sum_eq_zero (fun t _ => hz t)]
      by_cases hq : (q : ℕ) = lastTwoLE (proj π y) (zr π Z x - 1)
      · rw [if_pos hq, if_neg (fun heq => hC ((eqCase_char (proj π y) hlr).2 ⟨heq, hq⟩))]
      · rw [if_neg hq]
  rw [Finset.sum_congr rfl (fun q _ => key q), sum_fin_eq]
  by_cases heq : EqCase (proj π y) (zl π Z x) (zr π Z x)
  · have ham : lastTwoLE (proj π y) (zr π Z x - 1) < m := by
      have := lastTwoLE_le (proj π y) (zr π Z x - 1); omega
    rw [dif_pos ham, if_pos heq]
  · rw [if_neg heq]
    split_ifs <;> rfl

/-- The containment correction. -/
lemma t_ct_sum (hx : infZ π Z x = true) :
    ∑ q : Fin m, ∑ b : Fin m,
        uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))
          * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))
      = if CtCase (proj π y) (zl π Z x) (zr π Z x) then 1 else 0 := by
  have hrm := zr_lt hx
  have hlm : zl π Z x < m := (zl_lt_zr hx).trans hrm
  have key : ∀ q : Fin m, ∑ b : Fin m,
        uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))
          * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))
      = if (q : ℕ) = zl π Z x then
          (if InteriorClean (proj π y) q ∧ firstTwoGT (proj π y) q = zr π Z x then 1 else 0)
        else 0 := by
    intro q
    have : ∀ b : Fin m,
        uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))
          * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))
        = if (b : ℕ) = zr π Z x then
            (if (q : ℕ) = zl π Z x ∧ InteriorClean (proj π y) q
                ∧ firstTwoGT (proj π y) q = zr π Z x then 1 else 0)
          else 0 := by
      intro b
      simp only [uT, vT]
      by_cases hb : (b : ℕ) = zr π Z x
      · rw [if_pos hb]
        by_cases hC : (q : ℕ) = zl π Z x ∧ InteriorClean (proj π y) q
            ∧ firstTwoGT (proj π y) q = zr π Z x
        · rw [if_pos hC, if_pos ⟨hC.1, hb⟩, if_pos ⟨hC.2.1, by rw [hb, hC.2.2]⟩, mul_one]
        · rw [if_neg hC]
          by_cases h1 : (q : ℕ) = zl π Z x ∧ (b : ℕ) = zr π Z x
          · rw [if_pos h1, if_neg, mul_zero]
            rintro ⟨hic, hbB⟩
            exact hC ⟨h1.1, hic, by omega⟩
          · rw [if_neg h1, zero_mul]
      · rw [if_neg hb, if_neg (fun h => hb h.2), zero_mul]
    rw [Finset.sum_congr rfl (fun b _ => this b), sum_fin_eq, dif_pos hrm]
    by_cases hq : (q : ℕ) = zl π Z x
    · rw [if_pos hq]
      by_cases hC : InteriorClean (proj π y) q ∧ firstTwoGT (proj π y) q = zr π Z x
      · rw [if_pos hC, if_pos ⟨hq, hC⟩]
      · rw [if_neg hC, if_neg (fun h => hC h.2)]
    · rw [if_neg hq, if_neg (fun h => hq h.1)]
  rw [Finset.sum_congr rfl (fun q _ => key q), sum_fin_eq, dif_pos hlm]
  by_cases hct : CtCase (proj π y) (zl π Z x) (zr π Z x)
  · rw [if_pos hct, if_pos ((ctCase_iff (proj π y)).1 hct)]
  · rw [if_neg hct, if_neg (fun h => hct ((ctCase_iff (proj π y)).2 h))]

/-- **The structural sectors** reproduce the completion identity. -/
lemma t_struct_sum (hx : infZ π Z x = true) :
    ∑ q : Fin m, ∑ k : SIdx m, uT π Z x q (Sum.inl k) * vT π y q (Sum.inl k)
      = 1 - (if StrPres (proj π y) (zl π Z x) (zr π Z x) then 1 else 0) := by
  have hsplit : ∀ q : Fin m, ∑ k : SIdx m, uT π Z x q (Sum.inl k) * vT π y q (Sum.inl k)
      = (∑ t : Fin m, uT π Z x q (Sum.inl (Sum.inl t)) * vT π y q (Sum.inl (Sum.inl t)))
        + (∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inl s)))
            * vT π y q (Sum.inl (Sum.inr (Sum.inl s))))
        + (∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
            * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s)))))
        + (∑ k : Fin m × Fin m, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
            * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))
        + (∑ b : Fin m, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))
            * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))) := by
    intro q
    rw [Fintype.sum_sum_type (α₁ := Fin m),
      Fintype.sum_sum_type (α₁ := SatIdx m) (α₂ := SatIdx m ⊕ (Fin m × Fin m) ⊕ Fin m),
      Fintype.sum_sum_type (α₁ := SatIdx m) (α₂ := (Fin m × Fin m) ⊕ Fin m),
      Fintype.sum_sum_type (α₁ := Fin m × Fin m) (α₂ := Fin m)]
    ring
  simp only [hsplit, Finset.sum_add_distrib]
  rw [t_interior_sum hx, t_left_sum hx, t_right_sum hx, t_eq_sum hx, t_ct_sum hx]
  have hc := typed_completion (proj π y) (zl_lt_zr hx) (zr_lt hx)
  by_cases hno : NoTwo (proj π y)
  · rw [if_pos hno] at hc ⊢
    have hactL : ¬ ActL (proj π y) (zl π Z x) :=
      fun h => noTwo_iff.1 hno _ (isTwo_firstTwoGT h.2.1)
    rw [if_neg hactL] at hc
    linarith
  · rw [if_neg hno] at hc ⊢
    linarith

/-- **The repair sectors** contribute exactly `[gap preserved]`. -/
lemma t_repair_sum (hx : infZ π Z x = true) (hy : infZ π Z y = false) :
    ∑ q : Fin m, (if x q = y q then (0 : ℝ)
        else ∑ k : RIdx m Ω, uT π Z x q (Sum.inr k) * vT π y q (Sum.inr k))
      = if StrPres (proj π y) (zl π Z x) (zr π Z x) then 1 else 0 := by
  have hrm := zr_lt hx
  have hlr := zl_lt_zr hx
  have hlm : zl π Z x < m := hlr.trans hrm
  have key : ∀ q : Fin m, (if x q = y q then (0 : ℝ)
        else ∑ k : RIdx m Ω, uT π Z x q (Sum.inr k) * vT π y q (Sum.inr k))
      = (if (q : ℕ) = zl π Z x then
          (if x q = y q then 0
            else if CleanStart (proj π y) q ∧ firstTwoGT (proj π y) q = zr π Z x then 1 else 0)
          else 0)
        + (if (q : ℕ) = zr π Z x then
          (if x q = y q then 0
            else if CarrierTwo (proj π y) q ∧ lastTwoLE (proj π y) (q - 1) = zl π Z x
                ∧ letterAt x (zl π Z x) = letterAt y (zl π Z x) then 1 else 0)
          else 0) := by
    intro q
    have htag : ∑ b : Fin m, uT π Z x q (Sum.inr (Sum.inl b)) * vT π y q (Sum.inr (Sum.inl b))
        = if (q : ℕ) = zl π Z x ∧ CleanStart (proj π y) q ∧ firstTwoGT (proj π y) q = zr π Z x
          then 1 else 0 := by
      have : ∀ b : Fin m, uT π Z x q (Sum.inr (Sum.inl b)) * vT π y q (Sum.inr (Sum.inl b))
          = if (b : ℕ) = zr π Z x then
              (if (q : ℕ) = zl π Z x ∧ CleanStart (proj π y) q
                  ∧ firstTwoGT (proj π y) q = zr π Z x then 1 else 0)
            else 0 := by
        intro b
        simp only [uT, vT]
        by_cases hb : (b : ℕ) = zr π Z x
        · rw [if_pos hb]
          by_cases hC : (q : ℕ) = zl π Z x ∧ CleanStart (proj π y) q
              ∧ firstTwoGT (proj π y) q = zr π Z x
          · rw [if_pos hC, if_pos ⟨hC.1, hb⟩, if_pos ⟨hC.2.1, by rw [hb, hC.2.2]⟩, mul_one]
          · rw [if_neg hC]
            by_cases h1 : (q : ℕ) = zl π Z x ∧ (b : ℕ) = zr π Z x
            · rw [if_pos h1, if_neg, mul_zero]
              rintro ⟨hcs, hbB⟩
              exact hC ⟨h1.1, hcs, by omega⟩
            · rw [if_neg h1, zero_mul]
        · rw [if_neg hb, if_neg (fun h => hb h.2), zero_mul]
      rw [Finset.sum_congr rfl (fun b _ => this b), sum_fin_eq, dif_pos hrm]
    have hlet : ∑ k : Fin m × Ω, uT π Z x q (Sum.inr (Sum.inr k)) * vT π y q (Sum.inr (Sum.inr k))
        = if (q : ℕ) = zr π Z x ∧ CarrierTwo (proj π y) q
            ∧ lastTwoLE (proj π y) (q - 1) = zl π Z x
            ∧ letterAt x (zl π Z x) = letterAt y (zl π Z x) then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      have hxl : letterAt x (zl π Z x) = some (x ⟨zl π Z x, hlm⟩) := letterAt_of_lt x hlm
      have inner : ∀ t : Fin m, ∑ a : Ω,
          uT π Z x q (Sum.inr (Sum.inr (t, a))) * vT π y q (Sum.inr (Sum.inr (t, a)))
          = if (t : ℕ) = zl π Z x then
              (if (q : ℕ) = zr π Z x ∧ CarrierTwo (proj π y) q
                ∧ lastTwoLE (proj π y) (q - 1) = zl π Z x
                ∧ letterAt x (zl π Z x) = letterAt y (zl π Z x) then 1 else 0)
            else 0 := by
        intro t
        by_cases ht : (t : ℕ) = zl π Z x
        · rw [if_pos ht]
          by_cases hC : (q : ℕ) = zr π Z x ∧ CarrierTwo (proj π y) q
              ∧ lastTwoLE (proj π y) (q - 1) = zl π Z x
              ∧ letterAt x (zl π Z x) = letterAt y (zl π Z x)
          · rw [if_pos hC, Finset.sum_eq_single (x ⟨zl π Z x, hlm⟩)]
            · simp only [uT, vT]
              rw [if_pos ⟨hC.1, ht, hxl⟩, if_pos ⟨hC.2.1, by rw [ht, hC.2.2.1],
                by rw [hC.2.2.1, ← hC.2.2.2, hxl]⟩, mul_one]
            · intro a _ ha
              simp only [uT, vT]
              rw [if_neg, zero_mul]
              rintro ⟨_, _, h⟩
              rw [hxl] at h
              exact ha (Option.some.inj h).symm
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [if_neg hC]
            refine Finset.sum_eq_zero fun a _ => ?_
            simp only [uT, vT]
            by_cases h1 : (q : ℕ) = zr π Z x ∧ (t : ℕ) = zl π Z x ∧ letterAt x (zl π Z x) = some a
            · rw [if_pos h1, if_neg, mul_zero]
              rintro ⟨hc2, hta, hya⟩
              have hA : lastTwoLE (proj π y) (q - 1) = zl π Z x := by omega
              exact hC ⟨h1.1, hc2, hA, by rw [h1.2.2, ← hya, hA]⟩
            · rw [if_neg h1, zero_mul]
        · rw [if_neg ht]
          refine Finset.sum_eq_zero fun a _ => ?_
          simp only [uT, vT]
          rw [if_neg (fun h => ht h.2.1), zero_mul]
      rw [Finset.sum_congr rfl (fun t _ => inner t), sum_fin_eq, dif_pos hlm]
    rw [Fintype.sum_sum_type, htag, hlet]
    by_cases hq : x q = y q
    · rw [if_pos hq, if_pos hq, if_pos hq]; simp only [ite_self, add_zero]
    · rw [if_neg hq, if_neg hq, if_neg hq]
      by_cases hql : (q : ℕ) = zl π Z x
      · have hqr : (q : ℕ) ≠ zr π Z x := by omega
        have h2 : ¬ ((q : ℕ) = zr π Z x ∧ CarrierTwo (proj π y) q
            ∧ lastTwoLE (proj π y) (q - 1) = zl π Z x
            ∧ letterAt x (zl π Z x) = letterAt y (zl π Z x)) := fun h => hqr h.1
        rw [if_pos hql, if_neg hqr, if_neg h2, add_zero, add_zero]
        by_cases hC : CleanStart (proj π y) q ∧ firstTwoGT (proj π y) q = zr π Z x
        · rw [if_pos hC, if_pos ⟨hql, hC⟩]
        · rw [if_neg hC, if_neg (fun h => hC h.2)]
      · have h1 : ¬ ((q : ℕ) = zl π Z x ∧ CleanStart (proj π y) q
            ∧ firstTwoGT (proj π y) q = zr π Z x) := fun h => hql h.1
        rw [if_neg hql, if_neg h1, zero_add, zero_add]
        by_cases hqr : (q : ℕ) = zr π Z x
        · rw [if_pos hqr]
          by_cases hC : CarrierTwo (proj π y) q ∧ lastTwoLE (proj π y) (q - 1) = zl π Z x
              ∧ letterAt x (zl π Z x) = letterAt y (zl π Z x)
          · rw [if_pos hC, if_pos ⟨hqr, hC⟩]
          · rw [if_neg hC, if_neg (fun h => hC h.2)]
        · have h2 : ¬ ((q : ℕ) = zr π Z x ∧ CarrierTwo (proj π y) q
              ∧ lastTwoLE (proj π y) (q - 1) = zl π Z x
              ∧ letterAt x (zl π Z x) = letterAt y (zl π Z x)) := fun h => hqr h.1
          rw [if_neg hqr, if_neg h2]
  rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, sum_fin_eq, sum_fin_eq,
    dif_pos hlm, dif_pos hrm]
  by_cases hsp : StrPres (proj π y) (zl π Z x) (zr π Z x)
  · rw [if_pos hsp]
    have h1 := (strPres_iff_left (proj π y) hlr hrm).1 hsp
    have h2 := (strPres_iff_right (proj π y) hlr hrm).1 hsp
    have hZ : ¬ (x ⟨zl π Z x, hlm⟩ = y ⟨zl π Z x, hlm⟩ ∧ x ⟨zr π Z x, hrm⟩ = y ⟨zr π Z x, hrm⟩) := by
      rintro ⟨e1, e2⟩
      have hzx := z_rel hx
      have hzy := neg_not_rel hy hsp.1 hsp.2.1 hlr hsp.2.2
      rw [e1, e2] at hzx
      rw [hzx] at hzy
      exact absurd hzy (by decide)
    by_cases e1 : x ⟨zl π Z x, hlm⟩ = y ⟨zl π Z x, hlm⟩
    · have e2 : x ⟨zr π Z x, hrm⟩ ≠ y ⟨zr π Z x, hrm⟩ := fun e2 => hZ ⟨e1, e2⟩
      rw [if_pos e1, if_neg e2,
        if_pos ⟨h2.1, h2.2, by rw [letterAt_of_lt x hlm, letterAt_of_lt y hlm, e1]⟩]
      ring
    · rw [if_neg e1, if_pos h1]
      have hne : letterAt x (zl π Z x) ≠ letterAt y (zl π Z x) := by
        rw [letterAt_of_lt x hlm, letterAt_of_lt y hlm]
        intro h; exact e1 (Option.some.inj h)
      by_cases e2 : x ⟨zr π Z x, hrm⟩ = y ⟨zr π Z x, hrm⟩
      · rw [if_pos e2]; ring
      · rw [if_neg e2, if_neg (fun h => hne h.2.2)]; ring
  · rw [if_neg hsp]
    have h1 : ¬ (CleanStart (proj π y) (zl π Z x) ∧ firstTwoGT (proj π y) (zl π Z x) = zr π Z x) :=
      fun h => hsp ((strPres_iff_left (proj π y) hlr hrm).2 h)
    have h2 : ¬ (CarrierTwo (proj π y) (zr π Z x)
        ∧ lastTwoLE (proj π y) (zr π Z x - 1) = zl π Z x
        ∧ letterAt x (zl π Z x) = letterAt y (zl π Z x)) :=
      fun h => hsp ((strPres_iff_right (proj π y) hlr hrm).2 ⟨h.1, h.2.1⟩)
    rw [if_neg h1, if_neg h2, ite_self, ite_self, add_zero]

/-- **The oriented constraint**. -/
theorem t_filteredSum_eq_one (hx : infZ π Z x = true) (hy : infZ π Z y = false) :
    filteredSum (uT π Z) (vT π) x y = 1 := by
  unfold filteredSum
  have hsplit : ∀ q : Fin m, (if x q = y q then (0 : ℝ) else ∑ k, uT π Z x q k * vT π y q k)
      = (∑ k : SIdx m, uT π Z x q (Sum.inl k) * vT π y q (Sum.inl k))
        + (if x q = y q then 0
            else ∑ k : RIdx m Ω, uT π Z x q (Sum.inr k) * vT π y q (Sum.inr k)) := by
    intro q
    by_cases hq : x q = y q
    · rw [if_pos hq, if_pos hq, Finset.sum_eq_zero (fun k _ => struct_zero_of_eq hx hq k)]; ring
    · rw [if_neg hq, if_neg hq, Fintype.sum_sum_type]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [t_struct_sum hx, t_repair_sum hx hy]; ring

end Constraint

/-! ## The loads -/

section Loads

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {π : Ω → Fin 3} {Z : Ω → Ω → Bool}

/-- An indicator sum over `Fin m` whose support is contained in a single position. -/
lemma sum_ite_le_one (c : ℕ) (P : Fin m → Prop) [DecidablePred P] (h : ∀ q, P q → (q : ℕ) = c) :
    ∑ q : Fin m, (if P q then (1 : ℝ) else 0) ≤ 1 := by
  calc ∑ q : Fin m, (if P q then (1 : ℝ) else 0)
      ≤ ∑ q : Fin m, (if (q : ℕ) = c then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun q _ => ?_
        by_cases hq : P q
        · rw [if_pos hq, if_pos (h q hq)]
        · rw [if_neg hq]; split_ifs <;> norm_num
    _ = if hc : c < m then 1 else 0 := sum_fin_eq c (fun _ => 1)
    _ ≤ 1 := by split_ifs <;> norm_num

lemma sum_letter_le_one (o : Option Ω) (P : Prop) [Decidable P] :
    ∑ a : Ω, (if P ∧ o = some a then (1 : ℝ) else 0) ≤ 1 := by
  rcases o with _ | c
  · simp
  · calc ∑ a : Ω, (if P ∧ some c = some a then (1 : ℝ) else 0)
        ≤ ∑ a : Ω, (if c = a then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun a _ => ?_
          by_cases h : P ∧ some c = some a
          · rw [if_pos h, if_pos (Option.some.inj h.2)]
          · rw [if_neg h]; split_ifs <;> norm_num
      _ = 1 := by rw [Finset.sum_ite_eq]; simp

variable {x y : Fin m → Ω}

/-- A sum over `Fin m` of a summand supported at `c` with constant value. -/
lemma sum_fin_eq_const (c : ℕ) (hc : c < m) (v : ℝ) :
    ∑ q : Fin m, (if (q : ℕ) = c then v else 0) = v := by
  rw [sum_fin_eq c (fun _ => v), dif_pos hc]

/-- **The positive load** is at most `17·λ(m)`. -/
theorem uT_load (hx : infZ π Z x = true) :
    ∑ q : Fin m, ∑ k, uT π Z x q k * uT π Z x q k ≤ 17 * lam m := by
  have hlr := zl_lt_zr hx
  have hrm := zr_lt hx
  have hlm : zl π Z x < m := hlr.trans hrm
  have hG1 : 1 ≤ zr π Z x - zl π Z x := by omega
  have hGm : zr π Z x - zl π Z x ≤ m := by omega
  have hGpos : (0 : ℝ) < ((zr π Z x - zl π Z x : ℕ) : ℝ) := by exact_mod_cast hG1
  have hsplit : ∀ q : Fin m, ∑ k, uT π Z x q k * uT π Z x q k
      = (∑ t : Fin m, uT π Z x q (Sum.inl (Sum.inl t)) * uT π Z x q (Sum.inl (Sum.inl t)))
        + (∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inl s)))
            * uT π Z x q (Sum.inl (Sum.inr (Sum.inl s))))
        + (∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
            * uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s)))))
        + (∑ k : Fin m × Fin m, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
            * uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))
        + (∑ b : Fin m, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))
            * uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b))))))
        + (∑ b : Fin m, uT π Z x q (Sum.inr (Sum.inl b)) * uT π Z x q (Sum.inr (Sum.inl b)))
        + (∑ k : Fin m × Ω, uT π Z x q (Sum.inr (Sum.inr k)) * uT π Z x q (Sum.inr (Sum.inr k))) := by
    intro q
    rw [Fintype.sum_sum_type (α₁ := SIdx m), Fintype.sum_sum_type (α₁ := Fin m)
        (α₂ := SatIdx m ⊕ SatIdx m ⊕ (Fin m × Fin m) ⊕ Fin m),
      Fintype.sum_sum_type (α₁ := SatIdx m) (α₂ := SatIdx m ⊕ (Fin m × Fin m) ⊕ Fin m),
      Fintype.sum_sum_type (α₁ := SatIdx m) (α₂ := (Fin m × Fin m) ⊕ Fin m),
      Fintype.sum_sum_type (α₁ := Fin m × Fin m) (α₂ := Fin m),
      Fintype.sum_sum_type (α₁ := Fin m) (α₂ := Fin m × Ω)]
    ring
  simp only [hsplit, Finset.sum_add_distrib]
  -- interior
  have hint : ∑ q : Fin m, ∑ t : Fin m,
      uT π Z x q (Sum.inl (Sum.inl t)) * uT π Z x q (Sum.inl (Sum.inl t)) ≤ 1 := by
    have h1 : ∀ q : Fin m, ∑ t : Fin m,
        uT π Z x q (Sum.inl (Sum.inl t)) * uT π Z x q (Sum.inl (Sum.inl t))
        = 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ)
            * (if zl π Z x < q ∧ (q : ℕ) < zr π Z x then 1 else 0) := by
      intro q
      by_cases hq : zl π Z x < q ∧ (q : ℕ) < zr π Z x
      · rw [if_pos hq, mul_one]
        have : ∀ t : Fin m, uT π Z x q (Sum.inl (Sum.inl t)) * uT π Z x q (Sum.inl (Sum.inl t))
            = 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) * (1 / ((zr π Z x - zl π Z x : ℕ) : ℝ))
              * (if zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x then 1 else 0) := by
          intro t
          simp only [uT]
          by_cases ht : zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
          · rw [if_pos ⟨hq.1, hq.2, ht⟩, if_pos ht, mul_one]
          · rw [if_neg (fun h => ht ⟨h.2.2.1, h.2.2.2⟩), if_neg ht, mul_zero, mul_zero]
        rw [Finset.sum_congr rfl (fun t _ => this t), ← Finset.mul_sum, sum_ite_Ico m _ _ hrm.le]
        field_simp
      · rw [if_neg hq, mul_zero]
        exact Finset.sum_eq_zero fun t _ => by
          simp only [uT]; rw [if_neg (fun h => hq ⟨h.1, h.2.1⟩), mul_zero]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), ← Finset.mul_sum, sum_ite_Ioo m _ _ hrm.le,
      div_mul_eq_mul_div, one_mul, div_le_one hGpos]
    exact_mod_cast (by omega : zr π Z x - zl π Z x - 1 ≤ zr π Z x - zl π Z x)
  -- left column
  have hleft : ∑ q : Fin m, ∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inl s)))
      * uT π Z x q (Sum.inl (Sum.inr (Sum.inl s))) ≤ 7 * lam m := by
    have h1 : ∀ q : Fin m, ∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inl s)))
        * uT π Z x q (Sum.inl (Sum.inr (Sum.inl s)))
        = if (q : ℕ) = zl π Z x then
            ∑ s, satA m (zr π Z x - zl π Z x) s * satA m (zr π Z x - zl π Z x) s else 0 := by
      intro q
      by_cases hq : (q : ℕ) = zl π Z x
      · rw [if_pos hq]; refine Finset.sum_congr rfl fun s _ => ?_; simp only [uT]; rw [if_pos hq]
      · rw [if_neg hq]; refine Finset.sum_eq_zero fun s _ => ?_; simp only [uT]
        rw [if_neg hq, mul_zero]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), sum_fin_eq_const _ hlm]
    exact satA_sq_le hG1 hGm
  -- right column
  have hright : ∑ q : Fin m, ∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
      * uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s)))) ≤ 7 * lam m := by
    have h1 : ∀ q : Fin m, ∑ s, uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
        * uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
        = if (q : ℕ) = zr π Z x then
            ∑ s, satA m (zr π Z x - zl π Z x) s * satA m (zr π Z x - zl π Z x) s else 0 := by
      intro q
      by_cases hq : (q : ℕ) = zr π Z x
      · rw [if_pos hq]; refine Finset.sum_congr rfl fun s _ => ?_; simp only [uT]; rw [if_pos hq]
      · rw [if_neg hq]; refine Finset.sum_eq_zero fun s _ => ?_; simp only [uT]
        rw [if_neg hq, mul_zero]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), sum_fin_eq_const _ hrm]
    exact satA_sq_le hG1 hGm
  -- equality correction
  have heq : ∑ q : Fin m, ∑ k : Fin m × Fin m,
      uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        * uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))) ≤ 1 := by
    have h1 : ∀ q : Fin m, ∑ k : Fin m × Fin m,
        uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
          * uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        = 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ)
            * (if zl π Z x < q ∧ (q : ℕ) < zr π Z x then 1 else 0) := by
      intro q
      rw [Fintype.sum_prod_type]
      by_cases hq : zl π Z x < q ∧ (q : ℕ) < zr π Z x
      · rw [if_pos hq, mul_one]
        have inner : ∀ t : Fin m, ∑ b : Fin m,
            uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
              * uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
            = 1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) * (1 / ((zr π Z x - zl π Z x : ℕ) : ℝ))
              * (if zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x then 1 else 0) := by
          intro t
          have : ∀ b : Fin m,
              uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
                * uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
              = if (b : ℕ) = zr π Z x then
                  1 / ((zr π Z x - zl π Z x : ℕ) : ℝ) * (1 / ((zr π Z x - zl π Z x : ℕ) : ℝ))
                    * (if zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x then 1 else 0)
                else 0 := by
            intro b
            simp only [uT]
            by_cases hb : (b : ℕ) = zr π Z x
            · rw [if_pos hb]
              by_cases ht : zl π Z x ≤ t ∧ (t : ℕ) < zr π Z x
              · rw [if_pos ⟨hq.1, hq.2, ht.1, ht.2, hb⟩, if_pos ht, mul_one]
              · rw [if_neg (fun h => ht ⟨h.2.2.1, h.2.2.2.1⟩), if_neg ht, mul_zero, mul_zero]
            · rw [if_neg hb, if_neg (fun h => hb h.2.2.2.2), mul_zero]
          rw [Finset.sum_congr rfl (fun b _ => this b), sum_fin_eq_const _ hrm]
        rw [Finset.sum_congr rfl (fun t _ => inner t), ← Finset.mul_sum, sum_ite_Ico m _ _ hrm.le]
        field_simp
      · rw [if_neg hq, mul_zero]
        refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun b _ => ?_
        simp only [uT]; rw [if_neg (fun h => hq ⟨h.1, h.2.1⟩), mul_zero]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), ← Finset.mul_sum, sum_ite_Ioo m _ _ hrm.le,
      div_mul_eq_mul_div, one_mul, div_le_one hGpos]
    exact_mod_cast (by omega : zr π Z x - zl π Z x - 1 ≤ zr π Z x - zl π Z x)
  -- containment correction and repair tag: one unit vector each
  have hunit : ∀ (F : Fin m → Fin m → ℝ) (c : ℕ) (hc : c < m),
      (∀ q b, F q b = if (q : ℕ) = c ∧ (b : ℕ) = zr π Z x then 1 else 0) →
      ∑ q : Fin m, ∑ b : Fin m, F q b * F q b ≤ 1 := by
    intro F c hc hF
    have h1 : ∀ q : Fin m, ∑ b : Fin m, F q b * F q b
        = if (q : ℕ) = c then ∑ b : Fin m, (if (b : ℕ) = zr π Z x then (1 : ℝ) else 0) else 0 := by
      intro q
      by_cases hq : (q : ℕ) = c
      · rw [if_pos hq]; refine Finset.sum_congr rfl fun b _ => ?_; rw [hF]
        by_cases hb : (b : ℕ) = zr π Z x
        · rw [if_pos ⟨hq, hb⟩, if_pos hb, mul_one]
        · rw [if_neg (fun h => hb h.2), if_neg hb, mul_zero]
      · rw [if_neg hq]; refine Finset.sum_eq_zero fun b _ => ?_; rw [hF, if_neg (fun h => hq h.1),
          mul_zero]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), sum_fin_eq_const _ hc, sum_fin_eq_const _ hrm]
  have hct := hunit (fun q b => uT π Z x q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b))))))
    _ hlm (fun q b => by simp only [uT])
  have htag := hunit (fun q b => uT π Z x q (Sum.inr (Sum.inl b))) _ hlm
    (fun q b => by simp only [uT])
  -- repair letter tag
  have hlet : ∑ q : Fin m, ∑ k : Fin m × Ω,
      uT π Z x q (Sum.inr (Sum.inr k)) * uT π Z x q (Sum.inr (Sum.inr k)) ≤ 1 := by
    have h1 : ∀ q : Fin m, ∑ k : Fin m × Ω,
        uT π Z x q (Sum.inr (Sum.inr k)) * uT π Z x q (Sum.inr (Sum.inr k))
        = if (q : ℕ) = zr π Z x then
            ∑ t : Fin m, (if (t : ℕ) = zl π Z x then
              ∑ a : Ω, (if letterAt x (zl π Z x) = some a then (1 : ℝ) else 0) else 0)
          else 0 := by
      intro q
      rw [Fintype.sum_prod_type]
      by_cases hq : (q : ℕ) = zr π Z x
      · rw [if_pos hq]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases ht : (t : ℕ) = zl π Z x
        · rw [if_pos ht]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [uT]
          by_cases ha : letterAt x (zl π Z x) = some a
          · rw [if_pos ⟨hq, ht, ha⟩, if_pos ha, mul_one]
          · rw [if_neg (fun h => ha h.2.2), if_neg ha, mul_zero]
        · rw [if_neg ht]
          refine Finset.sum_eq_zero fun a _ => ?_
          simp only [uT]; rw [if_neg (fun h => ht h.2.1), mul_zero]
      · rw [if_neg hq]
        refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun a _ => ?_
        simp only [uT]; rw [if_neg (fun h => hq h.1), mul_zero]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), sum_fin_eq_const _ hrm, sum_fin_eq_const _ hlm]
    have := sum_letter_le_one (Ω := Ω) (letterAt x (zl π Z x)) True
    simpa only [true_and] using this
  have hl := two_le_lam m
  linarith

/-- **The negative load** is at most `9·m·λ(m)`. -/
theorem vT_load (y : Fin m → Ω) :
    ∑ q : Fin m, ∑ k, vT π y q k * vT π y q k ≤ 9 * m * lam m := by
  have hsplit : ∀ q : Fin m, ∑ k, vT π y q k * vT π y q k
      = (∑ t : Fin m, vT π y q (Sum.inl (Sum.inl t)) * vT π y q (Sum.inl (Sum.inl t)))
        + (∑ s, vT π y q (Sum.inl (Sum.inr (Sum.inl s)))
            * vT π y q (Sum.inl (Sum.inr (Sum.inl s))))
        + (∑ s, vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
            * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s)))))
        + (∑ k : Fin m × Fin m, vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
            * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))
        + (∑ b : Fin m, vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))))
            * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b))))))
        + (∑ b : Fin m, vT π y q (Sum.inr (Sum.inl b)) * vT π y q (Sum.inr (Sum.inl b)))
        + (∑ k : Fin m × Ω, vT π y q (Sum.inr (Sum.inr k)) * vT π y q (Sum.inr (Sum.inr k))) := by
    intro q
    rw [Fintype.sum_sum_type (α₁ := SIdx m), Fintype.sum_sum_type (α₁ := Fin m)
        (α₂ := SatIdx m ⊕ SatIdx m ⊕ (Fin m × Fin m) ⊕ Fin m),
      Fintype.sum_sum_type (α₁ := SatIdx m) (α₂ := SatIdx m ⊕ (Fin m × Fin m) ⊕ Fin m),
      Fintype.sum_sum_type (α₁ := SatIdx m) (α₂ := (Fin m × Fin m) ⊕ Fin m),
      Fintype.sum_sum_type (α₁ := Fin m × Fin m) (α₂ := Fin m),
      Fintype.sum_sum_type (α₁ := Fin m) (α₂ := Fin m × Ω)]
    ring
  simp only [hsplit, Finset.sum_add_distrib]
  have hl := two_le_lam m
  have hm : (0 : ℝ) ≤ m := by positivity
  -- interior: each coordinate is covered at most once
  have hint : ∑ q : Fin m, ∑ t : Fin m,
      vT π y q (Sum.inl (Sum.inl t)) * vT π y q (Sum.inl (Sum.inl t)) ≤ m := by
    rw [Finset.sum_comm]
    calc ∑ t : Fin m, ∑ q : Fin m, vT π y q (Sum.inl (Sum.inl t)) * vT π y q (Sum.inl (Sum.inl t))
        ≤ ∑ _t : Fin m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun t _ => ?_
          have : ∀ q : Fin m, vT π y q (Sum.inl (Sum.inl t)) * vT π y q (Sum.inl (Sum.inl t))
              = if Cov (proj π y) q t then 1 else 0 := by
            intro q; simp only [vT]; split_ifs <;> ring
          rw [Finset.sum_congr rfl (fun q _ => this q)]
          exact sum_ite_le_one (carrierAt (proj π y) t) _ fun q hq => (cov_iff.1 hq).2.2
      _ = m := by simp
  -- columns
  have hleft : ∑ q : Fin m, ∑ s, vT π y q (Sum.inl (Sum.inr (Sum.inl s)))
      * vT π y q (Sum.inl (Sum.inr (Sum.inl s))) ≤ m * (3 * lam m) := by
    calc ∑ q : Fin m, ∑ s, vT π y q (Sum.inl (Sum.inr (Sum.inl s)))
          * vT π y q (Sum.inl (Sum.inr (Sum.inl s)))
        ≤ ∑ _q : Fin m, 3 * lam m := by
          refine Finset.sum_le_sum fun q _ => ?_
          simp only [vT]
          by_cases hno : NoTwo (proj π y)
          · simp only [if_pos hno]; exact satBInf_sq_le
          · simp only [if_neg hno]
            by_cases hact : ActL (proj π y) q
            · simp only [if_pos hact]
              refine satB_sq_le (le_max_left _ _) (max_le ?_ ?_)
              · exact q.pos
              · have := firstTwoGT_le_m (proj π y) q; unfold DL; omega
            · simp only [if_neg hact, mul_zero, Finset.sum_const_zero]; positivity
      _ = m * (3 * lam m) := by simp
  have hright : ∑ q : Fin m, ∑ s, vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
      * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s)))) ≤ m * (3 * lam m) := by
    calc ∑ q : Fin m, ∑ s, vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
          * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inl s))))
        ≤ ∑ _q : Fin m, 3 * lam m := by
          refine Finset.sum_le_sum fun q _ => ?_
          simp only [vT]
          by_cases hact : ActR (proj π y) q
          · simp only [if_pos hact]
            refine satB_sq_le (le_max_left _ _) (max_le ?_ ?_)
            · exact q.pos
            · have := q.isLt; unfold DR; omega
          · simp only [if_neg hact, mul_zero, Finset.sum_const_zero]; positivity
      _ = m * (3 * lam m) := by simp
  -- equality correction: each coordinate lies in at most one clean cell
  have heq : ∑ q : Fin m, ∑ k : Fin m × Fin m,
      vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))) ≤ m := by
    have h1 : ∀ q : Fin m, ∑ k : Fin m × Fin m,
        vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
          * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        ≤ ∑ t : Fin m, (if CleanStart (proj π y) q ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < firstTwoGT (proj π y) q
            then (1 : ℝ) else 0) := by
      intro q
      rw [Fintype.sum_prod_type]
      refine Finset.sum_le_sum fun t _ => ?_
      have : ∀ b : Fin m,
          vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
            * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, b))))))
          = if (CleanStart (proj π y) q ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < firstTwoGT (proj π y) q)
              ∧ (b : ℕ) = firstTwoGT (proj π y) q then 1 else 0 := by
        intro b; simp only [vT]
        by_cases h : CleanStart (proj π y) q ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < firstTwoGT (proj π y) q
            ∧ (b : ℕ) = firstTwoGT (proj π y) q
        · rw [if_pos h, if_pos ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩, mul_one]
        · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.1, h'.1.2.1, h'.1.2.2, h'.2⟩), mul_zero]
      rw [Finset.sum_congr rfl (fun b _ => this b)]
      by_cases hC : CleanStart (proj π y) q ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < firstTwoGT (proj π y) q
      · rw [if_pos hC]
        calc ∑ b : Fin m, (if (CleanStart (proj π y) q ∧ (q : ℕ) ≤ t
                ∧ (t : ℕ) < firstTwoGT (proj π y) q) ∧ (b : ℕ) = firstTwoGT (proj π y) q
              then (1 : ℝ) else 0)
            = ∑ b : Fin m, (if (b : ℕ) = firstTwoGT (proj π y) q then (1 : ℝ) else 0) := by
              refine Finset.sum_congr rfl fun b _ => ?_
              by_cases hb : (b : ℕ) = firstTwoGT (proj π y) q
              · rw [if_pos ⟨hC, hb⟩, if_pos hb]
              · rw [if_neg (fun h => hb h.2), if_neg hb]
          _ ≤ 1 := sum_ite_le_one _ _ fun b hb => hb
      · rw [if_neg hC]
        exact le_of_eq (Finset.sum_eq_zero fun b _ => by rw [if_neg (fun h => hC h.1)])
    calc ∑ q : Fin m, ∑ k : Fin m × Fin m,
          vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
            * vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        ≤ ∑ q : Fin m, ∑ t : Fin m,
            (if CleanStart (proj π y) q ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < firstTwoGT (proj π y) q
              then (1 : ℝ) else 0) := Finset.sum_le_sum fun q _ => h1 q
      _ = ∑ t : Fin m, ∑ q : Fin m,
            (if CleanStart (proj π y) q ∧ (q : ℕ) ≤ t ∧ (t : ℕ) < firstTwoGT (proj π y) q
              then (1 : ℝ) else 0) := Finset.sum_comm
      _ ≤ ∑ _t : Fin m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun t _ => ?_
          refine sum_ite_le_one (lastTwoLE (proj π y) t) _ fun q hq => ?_
          obtain ⟨⟨hq2, hG, _⟩, h1, h2⟩ := hq
          have hqq : lastTwoLE (proj π y) q = q := lastTwoLE_self hq2
          obtain ⟨_, _, e3, _⟩ := cell_data hq2 (isTwo_firstTwoGT hG)
            (lt_firstTwoGT (proj π y) q q.isLt)
            (fun s hs1 hs2 => not_isTwo_of_lt_firstTwoGT hs1 hs2) h1 h2
          exact e3.symm
      _ = m := by simp
  -- containment correction and repair tag: at most one unit per position
  have hone : ∀ (P : Fin m → Prop) [DecidablePred P] (F : Fin m → Fin m → ℝ),
      (∀ q b, F q b = if P q ∧ (b : ℕ) = firstTwoGT (proj π y) q then 1 else 0) →
      ∑ q : Fin m, ∑ b : Fin m, F q b * F q b ≤ m := by
    intro P _ F hF
    calc ∑ q : Fin m, ∑ b : Fin m, F q b * F q b ≤ ∑ _q : Fin m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun q _ => ?_
          have : ∀ b : Fin m, F q b * F q b
              = if P q ∧ (b : ℕ) = firstTwoGT (proj π y) q then 1 else 0 := by
            intro b; rw [hF]; split_ifs <;> ring
          rw [Finset.sum_congr rfl (fun b _ => this b)]
          exact sum_ite_le_one _ _ fun b hb => hb.2
      _ = m := by simp
  have hct := hone (fun q => InteriorClean (proj π y) q)
    (fun q b => vT π y q (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b))))))
    (fun q b => by simp only [vT])
  have htag := hone (fun q => CleanStart (proj π y) q) (fun q b => vT π y q (Sum.inr (Sum.inl b)))
    (fun q b => by simp only [vT])
  -- repair letter tag
  have hlet : ∑ q : Fin m, ∑ k : Fin m × Ω,
      vT π y q (Sum.inr (Sum.inr k)) * vT π y q (Sum.inr (Sum.inr k)) ≤ m := by
    calc ∑ q : Fin m, ∑ k : Fin m × Ω,
          vT π y q (Sum.inr (Sum.inr k)) * vT π y q (Sum.inr (Sum.inr k))
        ≤ ∑ _q : Fin m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [Fintype.sum_prod_type]
          calc ∑ t : Fin m, ∑ a : Ω,
                vT π y q (Sum.inr (Sum.inr (t, a))) * vT π y q (Sum.inr (Sum.inr (t, a)))
              ≤ ∑ t : Fin m, (if (t : ℕ) = lastTwoLE (proj π y) (q - 1) then (1 : ℝ) else 0) := by
                refine Finset.sum_le_sum fun t _ => ?_
                have : ∀ a : Ω,
                    vT π y q (Sum.inr (Sum.inr (t, a))) * vT π y q (Sum.inr (Sum.inr (t, a)))
                    = if (CarrierTwo (proj π y) q ∧ (t : ℕ) = lastTwoLE (proj π y) (q - 1))
                        ∧ letterAt y (lastTwoLE (proj π y) (q - 1)) = some a then 1 else 0 := by
                  intro a; simp only [vT]
                  by_cases h : CarrierTwo (proj π y) q ∧ (t : ℕ) = lastTwoLE (proj π y) (q - 1)
                      ∧ letterAt y (lastTwoLE (proj π y) (q - 1)) = some a
                  · rw [if_pos h, if_pos ⟨⟨h.1, h.2.1⟩, h.2.2⟩, mul_one]
                  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.1, h'.1.2, h'.2⟩), mul_zero]
                rw [Finset.sum_congr rfl (fun a _ => this a)]
                by_cases ht : (t : ℕ) = lastTwoLE (proj π y) (q - 1)
                · rw [if_pos ht]; exact sum_letter_le_one _ _
                · rw [if_neg ht]
                  exact le_of_eq (Finset.sum_eq_zero fun a _ => by rw [if_neg (fun h => ht h.1.2)])
            _ ≤ 1 := sum_ite_le_one _ _ fun t ht => ht
      _ = m := by simp
  nlinarith [hint, hleft, hright, heq, hct, htag, hlet, hl, hm]

end Loads

/-! ## The theorem -/

/-- **Uniform typed clean-gap dual** (decision form of the typed longest-gap
bound): for every alphabet, projection and relation, `ADV±(infZ) ≤ 13·√m·λ(m)`. -/
theorem hasDual_infZ {Ω : Type} [Fintype Ω] [DecidableEq Ω] (π : Ω → Fin 3) (Z : Ω → Ω → Bool)
    (m : ℕ) : HasDual (infZ (m := m) π Z) (13 * Real.sqrt m * lam m) := by
  have h := hasDual_of_oriented (infZ (m := m) π Z) (uT π Z) (vT π)
    (fun x y hx hy => t_filteredSum_eq_one hx hy) (P := 17 * lam m) (N := 9 * m * lam m)
    (by have := two_le_lam m; positivity) (by have := two_le_lam m; positivity)
    (fun x hx => uT_load hx) (fun y _ => vT_load y)
  refine h.mono ?_
  have hl := two_le_lam m
  have hm : (0 : ℝ) ≤ m := by positivity
  rw [show 17 * lam m * (9 * m * lam m) = (Real.sqrt m * lam m) ^ 2 * 153 by
    rw [mul_pow, Real.sq_sqrt hm]; ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]
  have h153 : Real.sqrt 153 ≤ 13 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc Real.sqrt m * lam m * Real.sqrt 153 ≤ Real.sqrt m * lam m * 13 :=
        mul_le_mul_of_nonneg_left h153 (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
    _ = 13 * Real.sqrt m * lam m := by ring

end MonoidProduct.Infix
