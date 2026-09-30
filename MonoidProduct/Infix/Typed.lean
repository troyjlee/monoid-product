import MonoidProduct.Infix.Negative

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Typed clean gaps (decision form)

Letters of an alphabet `Ω` are projected by `π : Ω → Fin 3` onto `0` (neutral,
`E`), `1` (blocking, `B`) and `2` (endpoint, `A`); a public relation `Z` on
`Ω` says which ordered endpoint pairs are forbidden.  A **`Z`-clean witness**
is a pair `l < r` of endpoint letters with `Z (x l) (x r)`, all letters between
them neutral (`IsZWitness`); `infZ` decides whether one exists.

The adversary for `infZ` (next file) uses the **cells** of a word: the
intervals between consecutive endpoint letters of the projected word.  A cell
`(a, b)` has a **carrier**, its first blocking letter, or its right end `b`
when it is **clean** (`carrier`, `IsClean`).  The structural completion
identity `typed_completion` is the carrier form of the clean-infix completion
identity (`completion`): for
the interval `[l, r)` of any witness of the positive word and any projected
word `p`, the per-position sum of carrier indicators plus the two endpoint
corrections, the equality and containment corrections and the no-endpoint
term equals `1 − [p preserves the gap [l, r] structurally]`.
-/

namespace MonoidProduct.Infix

open Finset

variable {m : ℕ}

/-! ## Witnesses -/

section Defs

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (π : Ω → Fin 3) (Z : Ω → Ω → Bool)

/-- The projected word. -/
def proj (x : Fin m → Ω) : Word m := fun i => π (x i)

/-- A `Z`-clean witness. -/
def IsZWitness (x : Fin m → Ω) (l r : Fin m) : Prop :=
  l < r ∧ π (x l) = 2 ∧ π (x r) = 2 ∧ Z (x l) (x r) = true ∧ ∀ q, l < q → q < r → π (x q) = 0

instance (x : Fin m → Ω) (l r : Fin m) : Decidable (IsZWitness π Z x l r) := by
  unfold IsZWitness; infer_instance

/-- **Typed clean infix.** -/
def infZ (x : Fin m → Ω) : Bool := decide (∃ l r : Fin m, IsZWitness π Z x l r)

lemma infZ_eq_true_iff {x : Fin m → Ω} :
    infZ π Z x = true ↔ ∃ l r : Fin m, IsZWitness π Z x l r := by simp [infZ]

lemma infZ_eq_false_iff {x : Fin m → Ω} :
    infZ π Z x = false ↔ ∀ l r : Fin m, ¬ IsZWitness π Z x l r := by simp [infZ]

end Defs

/-! ## Cells and carriers of a projected word -/

/-- The carrier of the cell `(a, b)`: its first blocking letter, else `b`. -/
noncomputable def carrier (p : Word m) (a b : ℕ) : ℕ :=
  open Classical in if h : ∃ q, a < q ∧ q < b ∧ isOne p q then Nat.find h else b

/-- The cell `(a, b)` is clean: no blocking letter strictly inside. -/
def IsClean (p : Word m) (a b : ℕ) : Prop := ∀ q, a < q → q < b → ¬ isOne p q

instance (p : Word m) (a b : ℕ) : Decidable (IsClean p a b) := by
  unfold IsClean
  exact decidable_of_iff (∀ q ∈ Finset.Ioo a b, ¬ isOne p q)
    ⟨fun h q h1 h2 => h q (Finset.mem_Ioo.2 ⟨h1, h2⟩), fun h q hq => h q (Finset.mem_Ioo.1 hq).1
      (Finset.mem_Ioo.1 hq).2⟩

lemma carrier_of_clean {p : Word m} {a b : ℕ} (h : IsClean p a b) : carrier p a b = b := by
  unfold carrier
  rw [dif_neg]
  rintro ⟨q, h1, h2, h3⟩
  exact h q h1 h2 h3

lemma carrier_of_not_clean {p : Word m} {a b : ℕ} (h : ¬ IsClean p a b) :
    a < carrier p a b ∧ carrier p a b < b ∧ isOne p (carrier p a b)
      ∧ ∀ q, a < q → q < carrier p a b → ¬ isOne p q := by
  have hex : ∃ q, a < q ∧ q < b ∧ isOne p q := by
    by_contra hcon
    push Not at hcon
    exact h fun q h1 h2 h3 => hcon q h1 h2 h3
  unfold carrier
  rw [dif_pos hex]
  refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.1, (Nat.find_spec hex).2.2,
    fun q h1 h2 h3 => ?_⟩
  exact Nat.find_min hex h2 ⟨h1, (h2.trans (Nat.find_spec hex).2.1), h3⟩

lemma carrier_gt {p : Word m} {a b : ℕ} (hab : a < b) : a < carrier p a b := by
  by_cases h : IsClean p a b
  · rw [carrier_of_clean h]; exact hab
  · exact (carrier_of_not_clean h).1

lemma carrier_le {p : Word m} {a b : ℕ} : carrier p a b ≤ b := by
  by_cases h : IsClean p a b
  · rw [carrier_of_clean h]
  · exact (carrier_of_not_clean h).2.1.le

lemma carrier_lt_iff {p : Word m} {a b : ℕ} : carrier p a b < b ↔ ¬ IsClean p a b := by
  constructor
  · intro h hc; rw [carrier_of_clean hc] at h; exact lt_irrefl _ h
  · exact fun h => (carrier_of_not_clean h).2.1

/-- The carrier of the cell containing `t`. -/
noncomputable def carrierAt (p : Word m) (t : ℕ) : ℕ :=
  carrier p (lastTwoLE p t) (firstTwoGT p t)

/-- The interior indicator at `t`: `t` lies in a cell whose carrier is in `(l, r)`. -/
noncomputable def phiC (p : Word m) (l r t : ℕ) : ℝ :=
  if HasTwoLE p t ∧ HasTwoGT p t ∧ l < carrierAt p t ∧ carrierAt p t < r then 1 else 0

/-- The left endpoint column is active at `q`. -/
def ActL (p : Word m) (q : ℕ) : Prop :=
  ¬ isTwo p q ∧ HasTwoGT p q ∧ (¬ HasTwoLE p q ∨ carrierAt p q ≤ q)

/-- The right endpoint column is active at `q`. -/
def ActR (p : Word m) (q : ℕ) : Prop :=
  ¬ isTwo p q ∧ HasTwoLE p q ∧ (¬ HasTwoGT p q ∨ q ≤ carrierAt p q)

noncomputable instance (p : Word m) (q : ℕ) : Decidable (ActL p q) := by
  unfold ActL; infer_instance
noncomputable instance (p : Word m) (q : ℕ) : Decidable (ActR p q) := by
  unfold ActR; infer_instance

/-- The equality correction: a clean cell `[a, r)` with `l < a`. -/
def EqCase (p : Word m) (l r : ℕ) : Prop :=
  isTwo p r ∧ HasTwoLE p (r - 1) ∧ l < lastTwoLE p (r - 1) ∧ IsClean p (lastTwoLE p (r - 1)) r

/-- The containment correction: a clean cell `[a, r)` with `a < l`. -/
def CtCase (p : Word m) (l r : ℕ) : Prop :=
  HasTwoLE p l ∧ HasTwoGT p l ∧ ¬ isTwo p l ∧ firstTwoGT p l = r ∧ IsClean p (lastTwoLE p l) r

noncomputable instance (p : Word m) (l r : ℕ) : Decidable (EqCase p l r) := by
  unfold EqCase; infer_instance
noncomputable instance (p : Word m) (l r : ℕ) : Decidable (CtCase p l r) := by
  unfold CtCase; infer_instance

/-- Structural preservation of the gap `[l, r]`. -/
def StrPres (p : Word m) (l r : ℕ) : Prop :=
  isTwo p l ∧ isTwo p r ∧ ∀ q, l < q → q < r → ∀ h : q < m, p ⟨q, h⟩ = 0

instance (p : Word m) (l r : ℕ) : Decidable (StrPres p l r) := by
  unfold StrPres
  exact decidable_of_iff (isTwo p l ∧ isTwo p r ∧ ∀ q ∈ Finset.Ioo l r, ∀ h : q < m, p ⟨q, h⟩ = 0)
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun q hq1 hq2 => h3 q (Finset.mem_Ioo.2 ⟨hq1, hq2⟩)⟩,
     fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun q hq => h3 q (Finset.mem_Ioo.1 hq).1 (Finset.mem_Ioo.1 hq).2⟩⟩

/-- `p` has no endpoint letter at all. -/
def NoTwo (p : Word m) : Prop := ∀ q : Fin m, p q ≠ 2

instance (p : Word m) : Decidable (NoTwo p) := by unfold NoTwo; infer_instance

lemma noTwo_iff {p : Word m} : NoTwo p ↔ ∀ q, ¬ isTwo p q :=
  ⟨fun h q ⟨hq, h2⟩ => h ⟨q, hq⟩ h2, fun h q h2 => h q ⟨q.isLt, h2⟩⟩

/-- Positions strictly inside a cell are neutral or blocking, never endpoints. -/
lemma not_two_of_mem_cell {p : Word m} {t q : ℕ}
    (h1 : lastTwoLE p t < q) (h2 : q < firstTwoGT p t) : ¬ isTwo p q :=
  not_isTwo_of_mem_gap h1 h2

lemma isOne_or_zero {p : Word m} {q : ℕ} (hq : q < m) (h2 : ¬ isTwo p q) (h1 : ¬ isOne p q) :
    p ⟨q, hq⟩ = 0 := by
  simp only [isTwo, isOne, not_exists] at h1 h2
  have h1' := h1 hq
  have h2' := h2 hq
  revert h1' h2'
  generalize p ⟨q, hq⟩ = c
  revert c; decide

end MonoidProduct.Infix

namespace MonoidProduct.Infix

open Finset

variable {m : ℕ}

/-! ## The structural completion identity -/

lemma carrierAt_eq_of_gap_eq {p : Word m} {s t : ℕ} (hL : HasTwoLE p s) (hG : HasTwoGT p s)
    (h1 : lastTwoLE p t = lastTwoLE p s) (h2 : firstTwoGT p t = firstTwoGT p s) :
    carrierAt p t = carrierAt p s := by
  unfold carrierAt; rw [h1, h2]

/-- `phiC` is constant along a `2`-free stretch. -/
lemma phiC_eq_of_no_two {p : Word m} {l r s t : ℕ} (hst : s ≤ t)
    (hno : ∀ q, s ≤ q → q ≤ t → ¬ isTwo p q) : phiC p l r t = phiC p l r s := by
  obtain ⟨e1, e2, e3, e4⟩ := gap_eq_of_no_two (y := p) hst hno
  unfold phiC
  by_cases hL : HasTwoLE p s <;> by_cases hG : HasTwoGT p s
  · rw [carrierAt_eq_of_gap_eq hL hG (e3 hL) (e4 hG)]
    by_cases h : l < carrierAt p s ∧ carrierAt p s < r
    · rw [if_pos ⟨e1.2 hL, e2.2 hG, h⟩, if_pos ⟨hL, hG, h⟩]
    · rw [if_neg (fun h' => h h'.2.2), if_neg (fun h' => h h'.2.2)]
  · rw [if_neg (fun h => hG (e2.1 h.2.1)), if_neg (fun h => hG h.2.1)]
  · rw [if_neg (fun h => hL (e1.1 h.1)), if_neg (fun h => hL h.1)]
  · rw [if_neg (fun h => hL (e1.1 h.1)), if_neg (fun h => hL h.1)]

lemma phiC_of_not_hasTwoLE {p : Word m} {l r t : ℕ} (h : ¬ HasTwoLE p t) : phiC p l r t = 0 := by
  unfold phiC; rw [if_neg (fun h' => h h'.1)]

lemma phiC_of_not_hasTwoGT {p : Word m} {l r t : ℕ} (h : ¬ HasTwoGT p t) : phiC p l r t = 0 := by
  unfold phiC; rw [if_neg (fun h' => h h'.2.1)]

/-- The left piece `[l, b)` with `b = firstTwoGT p l < r`. -/
lemma left_piece (p : Word m) {l r : ℕ} (hlr : l < r) (hl2 : ¬ isTwo p l) (hGl : HasTwoGT p l)
    (hbr : firstTwoGT p l < r) :
    (∑ t ∈ Ico l (firstTwoGT p l), phiC p l r t) / ((r - l : ℕ) : ℝ)
      + (if ActL p l then min 1 ((DL p l : ℝ) / ((r - l : ℕ) : ℝ)) else 0)
      = ((firstTwoGT p l - l : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) := by
  have hG : (0 : ℝ) < ((r - l : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - l)
  have hlb : l < firstTwoGT p l := lt_firstTwoGT p l (lt_m_of_hasTwoGT hGl)
  have hmin : min 1 ((DL p l : ℝ) / ((r - l : ℕ) : ℝ))
      = ((firstTwoGT p l - l : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) := by
    rw [DL, min_eq_right]
    rw [div_le_one hG]
    exact_mod_cast (by omega : firstTwoGT p l - l ≤ r - l)
  have hconst : ∀ t ∈ Ico l (firstTwoGT p l), phiC p l r t = phiC p l r l := by
    intro t ht
    rw [mem_Ico] at ht
    refine phiC_eq_of_no_two ht.1 fun q h1 h2 => ?_
    rcases eq_or_lt_of_le h1 with e | e
    · exact e ▸ hl2
    · exact not_isTwo_of_lt_firstTwoGT e (by omega)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hmin]
  by_cases hL : HasTwoLE p l
  · have hc : carrierAt p l ≤ firstTwoGT p l := carrier_le
    by_cases hcl : carrierAt p l ≤ l
    · rw [if_pos ⟨hl2, hGl, Or.inr hcl⟩]
      unfold phiC
      rw [if_neg (fun h => absurd h.2.2.1 (not_lt.2 hcl))]
      ring
    · rw [if_neg (fun h => h.2.2.elim (fun h' => h' hL) hcl)]
      unfold phiC
      rw [if_pos ⟨hL, hGl, not_le.1 hcl, hc.trans_lt hbr⟩]
      ring
  · rw [if_pos ⟨hl2, hGl, Or.inl hL⟩, phiC_of_not_hasTwoLE hL]
    ring

/-- Cells ending at a `2` at `a < r` and starting at or after `l` have `phiC = 1`. -/
lemma phiC_eq_one_of_cell {p : Word m} {l r t a : ℕ} (hLt : HasTwoLE p t) (hGt : HasTwoGT p t)
    (h1 : l ≤ lastTwoLE p t) (h2 : firstTwoGT p t ≤ a) (har : a < r) : phiC p l r t = 1 := by
  have hgt := carrier_gt (p := p) (a := lastTwoLE p t) (b := firstTwoGT p t)
    (lt_of_le_of_lt (lastTwoLE_le p t) (lt_firstTwoGT p t (lt_m_of_hasTwoGT hGt)))
  have hle := carrier_le (p := p) (a := lastTwoLE p t) (b := firstTwoGT p t)
  unfold phiC carrierAt
  rw [if_pos ⟨hLt, hGt, by omega, by omega⟩]

/-- The left part `[l, a)` up to a `2` at `a < r`, with the left endpoint column. -/
lemma left_to (p : Word m) {l r a : ℕ} (hlr : l < r) (hr : r < m) (ha2 : isTwo p a)
    (hla : l ≤ a) (har : a < r) :
    (∑ t ∈ Ico l a, phiC p l r t) / ((r - l : ℕ) : ℝ)
      + (if ActL p l then min 1 ((DL p l : ℝ) / ((r - l : ℕ) : ℝ)) else 0)
      = ((a - l : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) := by
  by_cases hl2 : isTwo p l
  · rw [if_neg (fun h => h.1 hl2), add_zero]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)), Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul, mul_one]
    intro t ht
    rw [mem_Ico] at ht
    exact phiC_eq_one_of_cell ⟨l, ht.1, hl2⟩ ⟨a, ht.2, ha2⟩ (le_lastTwoLE ht.1 hl2)
      (firstTwoGT_le ht.2 ha2) har
  · have hGl : HasTwoGT p l := ⟨a, lt_of_le_of_ne hla (fun e => hl2 (e ▸ ha2)), ha2⟩
    have hb2 : isTwo p (firstTwoGT p l) := isTwo_firstTwoGT hGl
    have hlb : l < firstTwoGT p l := lt_firstTwoGT p l (by omega)
    have hba : firstTwoGT p l ≤ a := firstTwoGT_le (lt_of_le_of_ne hla (fun e => hl2 (e ▸ ha2))) ha2
    rw [← Finset.sum_Ico_consecutive _ hlb.le hba]
    have hmid : ∑ t ∈ Ico (firstTwoGT p l) a, phiC p l r t = ((a - firstTwoGT p l : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)), Finset.sum_const, Nat.card_Ico,
        nsmul_eq_mul, mul_one]
      intro t ht
      rw [mem_Ico] at ht
      exact phiC_eq_one_of_cell ⟨_, ht.1, hb2⟩ ⟨a, ht.2, ha2⟩ (hlb.le.trans (le_lastTwoLE ht.1 hb2))
        (firstTwoGT_le ht.2 ha2) har
    have hleft := left_piece p hlr hl2 hGl (by omega)
    rw [add_div, hmid, add_right_comm, hleft, ← add_div, ← Nat.cast_add,
      show (firstTwoGT p l - l) + (a - firstTwoGT p l) = a - l by omega]

/-- The right piece `[a', r)` with `a' = lastTwoLE p r ≥ l` and `p r ≠ 2`. -/
lemma right_piece (p : Word m) {l r : ℕ} (hlr : l < r) (hr : r < m) (hr2 : ¬ isTwo p r)
    (hLr : HasTwoLE p r) (hla' : l ≤ lastTwoLE p r) :
    (∑ t ∈ Ico (lastTwoLE p r) r, phiC p l r t) / ((r - l : ℕ) : ℝ)
      + (if ActR p r then min 1 ((DR p r : ℝ) / ((r - l : ℕ) : ℝ)) else 0)
      = ((r - lastTwoLE p r : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) := by
  have hG : (0 : ℝ) < ((r - l : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - l)
  have ha'r : lastTwoLE p r < r := lastTwoLE_lt_of_not_isTwo hLr hr2
  have hmin : min 1 ((DR p r : ℝ) / ((r - l : ℕ) : ℝ))
      = ((r - lastTwoLE p r : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) := by
    rw [DR, min_eq_right]
    rw [div_le_one hG]
    exact_mod_cast (by omega : r - lastTwoLE p r ≤ r - l)
  have hnoa' : ∀ q, lastTwoLE p r < q → q ≤ r → ¬ isTwo p q := fun q h1 h2 =>
    not_isTwo_of_lastTwoLE_lt h1 h2
  have hconst : ∀ t ∈ Ico (lastTwoLE p r) r, phiC p l r t = phiC p l r r := by
    intro t ht
    rw [mem_Ico] at ht
    obtain ⟨eG, eB⟩ := firstTwoGT_eq_of_no_two (y := p) ht.2.le
      (fun q h1 h2 => hnoa' q (by omega) h2)
    obtain ⟨_, eA⟩ := lastTwoLE_eq_of_no_two (y := p) ht.1 (fun q h1 h2 => hnoa' q h1 (by omega))
    have hAa' : lastTwoLE p (lastTwoLE p r) = lastTwoLE p r :=
      le_antisymm (lastTwoLE_le _ _) (le_lastTwoLE le_rfl (isTwo_lastTwoLE hLr))
    have hLt : HasTwoLE p t := ⟨_, ht.1, isTwo_lastTwoLE hLr⟩
    unfold phiC carrierAt
    rw [eA, hAa', ← eB]
    by_cases hGr : HasTwoGT p r
    · have hGt : HasTwoGT p t := eG.1 hGr
      by_cases h : l < carrier p (lastTwoLE p r) (firstTwoGT p r)
          ∧ carrier p (lastTwoLE p r) (firstTwoGT p r) < r
      · rw [if_pos ⟨hLt, hGt, h⟩, if_pos ⟨hLr, hGr, h⟩]
      · rw [if_neg (fun h' => h h'.2.2), if_neg (fun h' => h h'.2.2)]
    · rw [if_neg (fun h => hGr (eG.2 h.2.1)), if_neg (fun h => hGr h.2.1)]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hmin]
  by_cases hGr : HasTwoGT p r
  · have hc : lastTwoLE p r < carrierAt p r :=
      carrier_gt (lt_of_le_of_lt (lastTwoLE_le p r) (lt_firstTwoGT p r hr))
    by_cases hcr : r ≤ carrierAt p r
    · rw [if_pos ⟨hr2, hLr, Or.inr hcr⟩]
      unfold phiC
      rw [if_neg (fun h => absurd h.2.2.2 (not_lt.2 hcr))]
      ring
    · rw [if_neg (fun h => h.2.2.elim (fun h' => h' hGr) hcr)]
      unfold phiC
      rw [if_pos ⟨hLr, hGr, lt_of_le_of_lt hla' hc, not_le.1 hcr⟩]
      ring
  · rw [if_pos ⟨hr2, hLr, Or.inl hGr⟩, phiC_of_not_hasTwoGT hGr]
    ring

/-- **Structural completion identity** (carrier form of `completion`). -/
theorem typed_completion (p : Word m) {l r : ℕ} (hlr : l < r) (hr : r < m) :
    (∑ t ∈ Ico l r, phiC p l r t) / ((r - l : ℕ) : ℝ)
      + (if ActL p l then min 1 ((DL p l : ℝ) / ((r - l : ℕ) : ℝ)) else 0)
      + (if ActR p r then min 1 ((DR p r : ℝ) / ((r - l : ℕ) : ℝ)) else 0)
      + (if EqCase p l r then ((r - lastTwoLE p (r - 1) : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) else 0)
      + (if CtCase p l r then 1 else 0)
      + (if NoTwo p then 1 else 0)
      = 1 - (if StrPres p l r then 1 else 0) := by
  have hG : (0 : ℝ) < ((r - l : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r - l)
  have hdiv : ∀ {u v : ℕ}, u + v = r - l →
      ((u : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) + ((v : ℕ) : ℝ) / ((r - l : ℕ) : ℝ) = 1 := by
    intro u v h
    rw [← add_div, ← Nat.cast_add, h]
    exact div_self hG.ne'
  by_cases hin : ∃ q, l ≤ q ∧ q ≤ r ∧ isTwo p q
  · -- Case A: a `2` in `[l, r]`
    obtain ⟨p₀, hp₀l, hp₀r, hp₀⟩ := hin
    have hno2 : ¬ NoTwo p := fun h => noTwo_iff.1 h p₀ hp₀
    rw [if_neg hno2, add_zero]
    have hLr : HasTwoLE p r := ⟨p₀, hp₀r, hp₀⟩
    by_cases hr2 : isTwo p r
    · -- A1: `p r = 2`
      have hactR : ¬ ActR p r := fun h => h.1 hr2
      rw [if_neg hactR, add_zero]
      by_cases hin' : ∃ q, l ≤ q ∧ q < r ∧ isTwo p q
      · -- A1b: a `2` in `[l, r)`; the last cell is `[a, r)`
        obtain ⟨q₁, hq₁l, hq₁r, hq₁⟩ := hin'
        have hLr1 : HasTwoLE p (r - 1) := ⟨q₁, by omega, hq₁⟩
        have ha2 : isTwo p (lastTwoLE p (r - 1)) := isTwo_lastTwoLE hLr1
        have hla : l ≤ lastTwoLE p (r - 1) := hq₁l.trans (le_lastTwoLE (by omega) hq₁)
        have har : lastTwoLE p (r - 1) < r := by have := lastTwoLE_le p (r - 1); omega
        have hnoa : ∀ q, lastTwoLE p (r - 1) < q → q < r → ¬ isTwo p q := fun q h1 h2 =>
          not_isTwo_of_lastTwoLE_lt h1 (by omega)
        have hcell : ∀ t, lastTwoLE p (r - 1) ≤ t → t < r → HasTwoLE p t ∧ HasTwoGT p t
            ∧ lastTwoLE p t = lastTwoLE p (r - 1) ∧ firstTwoGT p t = r := by
          intro t h1 h2
          have hLt : HasTwoLE p t := ⟨_, h1, ha2⟩
          have hGt : HasTwoGT p t := ⟨r, h2, hr2⟩
          refine ⟨hLt, hGt, le_antisymm ?_ (le_lastTwoLE h1 ha2),
            le_antisymm (firstTwoGT_le h2 hr2) ?_⟩
          · by_contra hcon
            push Not at hcon
            exact hnoa _ hcon (by have := lastTwoLE_le p t; omega) (isTwo_lastTwoLE hLt)
          · by_contra hcon
            push Not at hcon
            exact hnoa _ (by have := lt_firstTwoGT p t (by omega); omega) hcon
              (isTwo_firstTwoGT hGt)
        have hct : ¬ CtCase p l r := by
          rintro ⟨_, _, hl2, hfr, _⟩
          have := firstTwoGT_le (lt_of_le_of_ne hq₁l (fun e => hl2 (e ▸ hq₁))) hq₁
          omega
        rw [if_neg hct, add_zero]
        have hgt : lastTwoLE p (r - 1) < carrier p (lastTwoLE p (r - 1)) r := carrier_gt har
        have hlast : ∑ t ∈ Ico (lastTwoLE p (r - 1)) r, phiC p l r t
            = if IsClean p (lastTwoLE p (r - 1)) r then 0 else ((r - lastTwoLE p (r - 1) : ℕ) : ℝ) := by
          have hconst : ∀ t ∈ Ico (lastTwoLE p (r - 1)) r, phiC p l r t
              = if IsClean p (lastTwoLE p (r - 1)) r then 0 else 1 := by
            intro t ht
            rw [mem_Ico] at ht
            obtain ⟨hLt, hGt, e1, e2⟩ := hcell t ht.1 ht.2
            unfold phiC carrierAt
            rw [e1, e2]
            by_cases hcl : IsClean p (lastTwoLE p (r - 1)) r
            · rw [if_pos hcl, if_neg]
              rw [carrier_of_clean hcl]
              exact fun h => lt_irrefl _ h.2.2.2
            · rw [if_neg hcl, if_pos ⟨hLt, hGt, by omega, carrier_lt_iff.2 hcl⟩]
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          split_ifs <;> ring
        rw [← Finset.sum_Ico_consecutive _ hla har.le, add_div, hlast]
        have hleft := left_to p hlr hr ha2 hla har
        by_cases hcl : IsClean p (lastTwoLE p (r - 1)) r
        · rw [if_pos hcl, zero_div, add_zero]
          by_cases hal : l < lastTwoLE p (r - 1)
          · have heq : EqCase p l r := ⟨hr2, hLr1, hal, hcl⟩
            have hsp : ¬ StrPres p l r := by
              rintro ⟨_, _, h0⟩
              obtain ⟨hlt, h2⟩ := ha2
              have := h0 _ hal har hlt
              rw [this] at h2
              exact absurd h2 (by decide)
            rw [if_pos heq, if_neg hsp, sub_zero]
            linear_combination hleft + hdiv (u := lastTwoLE p (r - 1) - l) (v := r - lastTwoLE p (r - 1))
              (by omega)
          · have hal' : lastTwoLE p (r - 1) = l := by omega
            have heq : ¬ EqCase p l r := fun h => hal h.2.2.1
            have hsp : StrPres p l r := by
              refine ⟨hal' ▸ ha2, hr2, fun q hq1 hq2 hq => ?_⟩
              refine isOne_or_zero hq (hnoa q (by omega) hq2) (hcl q (by omega) hq2)
            rw [if_neg heq, if_pos hsp, hal', Finset.Ico_self, Finset.sum_empty, zero_div, zero_add,
              if_neg (fun h => h.1 (hal' ▸ ha2))]
            ring
        · rw [if_neg hcl]
          have heq : ¬ EqCase p l r := fun h => hcl h.2.2.2
          have hsp : ¬ StrPres p l r := by
            rintro ⟨_, _, h0⟩
            obtain ⟨hc1, hc2, ⟨hclt, hc1'⟩, _⟩ := carrier_of_not_clean hcl
            have := h0 _ (by omega) hc2 hclt
            rw [this] at hc1'
            exact absurd hc1' (by decide)
          rw [if_neg heq, if_neg hsp, sub_zero]
          linear_combination hleft + hdiv (u := lastTwoLE p (r - 1) - l) (v := r - lastTwoLE p (r - 1))
            (by omega)
      · -- A1a: no `2` in `[l, r)`: the cell of `l` ends at `r`
        push Not at hin'
        have hno : ∀ q, l ≤ q → q < r → ¬ isTwo p q := fun q h1 h2 h => hin' q h1 h2 h
        have hl2 : ¬ isTwo p l := hno l le_rfl hlr
        have hGl : HasTwoGT p l := ⟨r, hlr, hr2⟩
        have hfr : firstTwoGT p l = r := le_antisymm (firstTwoGT_le hlr hr2) (by
          by_contra hcon
          push Not at hcon
          exact hno _ (lt_firstTwoGT p l (by omega)).le hcon (isTwo_firstTwoGT hGl))
        have hsp : ¬ StrPres p l r := fun h => hl2 h.1
        have hactL : min 1 ((DL p l : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
          rw [DL, hfr, min_eq_left]
          rw [div_self hG.ne']
        have hconst : ∀ t ∈ Ico l r, phiC p l r t = phiC p l r l := by
          intro t ht
          rw [mem_Ico] at ht
          exact phiC_eq_of_no_two ht.1 fun q h1 h2 => hno q h1 (by omega)
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
          mul_div_cancel_left₀ _ hG.ne', if_neg hsp, sub_zero, hactL]
        obtain ⟨e1, e2⟩ := lastTwoLE_eq_of_no_two (y := p) (s := l) (t := r - 1) (by omega)
          (fun q h1 h2 => hno q (by omega) (by omega))
        have heq : ¬ EqCase p l r := by
          rintro ⟨_, hL1, hlt, _⟩
          rw [e2] at hlt
          have := lastTwoLE_le p l
          omega
        rw [if_neg heq, add_zero]
        by_cases hL : HasTwoLE p l
        · have hA : lastTwoLE p l < l := lastTwoLE_lt_of_not_isTwo hL hl2
          have hcA : carrierAt p l = carrier p (lastTwoLE p l) r := by unfold carrierAt; rw [hfr]
          by_cases hcl : IsClean p (lastTwoLE p l) r
          · have hct : CtCase p l r := ⟨hL, hGl, hl2, hfr, hcl⟩
            have hc : carrierAt p l = r := by rw [hcA, carrier_of_clean hcl]
            rw [if_pos hct, if_neg (fun h => h.2.2.elim (fun h' => h' hL) (fun h' => by omega))]
            unfold phiC
            rw [if_neg (fun h => lt_irrefl _ (hc ▸ h.2.2.2))]
            ring
          · have hct : ¬ CtCase p l r := fun h => hcl h.2.2.2.2
            obtain ⟨hc1, hc2, _, _⟩ := carrier_of_not_clean hcl
            rw [← hcA] at hc1 hc2
            rw [if_neg hct, add_zero]
            by_cases hcl' : carrierAt p l ≤ l
            · rw [if_pos ⟨hl2, hGl, Or.inr hcl'⟩]
              unfold phiC
              rw [if_neg (fun h => absurd h.2.2.1 (not_lt.2 hcl'))]
              ring
            · rw [if_neg (fun h => h.2.2.elim (fun h' => h' hL) hcl')]
              unfold phiC
              rw [if_pos ⟨hL, hGl, not_le.1 hcl', hc2⟩]
              ring
        · have hct : ¬ CtCase p l r := fun h => hL h.1
          rw [if_neg hct, if_pos ⟨hl2, hGl, Or.inl hL⟩, phiC_of_not_hasTwoLE hL]
          ring
    · -- A2: `p r ≠ 2`
      have hla' : l ≤ lastTwoLE p r := hp₀l.trans (le_lastTwoLE hp₀r hp₀)
      have heq : ¬ EqCase p l r := fun h => hr2 h.1
      have hct : ¬ CtCase p l r := fun h => hr2 (h.2.2.2.1 ▸ isTwo_firstTwoGT h.2.1)
      have hsp : ¬ StrPres p l r := fun h => hr2 h.2.1
      rw [if_neg heq, if_neg hct, if_neg hsp, add_zero, add_zero, sub_zero]
      have ha'r : lastTwoLE p r < r := lastTwoLE_lt_of_not_isTwo hLr hr2
      have ha'2 : isTwo p (lastTwoLE p r) := isTwo_lastTwoLE hLr
      rw [← Finset.sum_Ico_consecutive _ hla' ha'r.le, add_div]
      have hleft := left_to p hlr hr ha'2 hla' ha'r
      have hright := right_piece p hlr hr hr2 hLr hla'
      linear_combination hleft + hright + hdiv (u := lastTwoLE p r - l) (v := r - lastTwoLE p r)
        (by omega)
  · -- Case B: no `2` in `[l, r]`
    push Not at hin
    have hno : ∀ q, l ≤ q → q ≤ r → ¬ isTwo p q := fun q h1 h2 h => hin q h1 h2 h
    have hl2 : ¬ isTwo p l := hno l le_rfl hlr.le
    have hr2 : ¬ isTwo p r := hno r hlr.le le_rfl
    obtain ⟨e1, e2, e3, e4⟩ := gap_eq_of_no_two (y := p) hlr.le hno
    have heq : ¬ EqCase p l r := fun h => hr2 h.1
    have hct : ¬ CtCase p l r := fun h => hr2 (h.2.2.2.1 ▸ isTwo_firstTwoGT h.2.1)
    have hsp : ¬ StrPres p l r := fun h => hr2 h.2.1
    rw [if_neg heq, if_neg hct, if_neg hsp, add_zero, add_zero, sub_zero]
    have hconst : ∀ t ∈ Ico l r, phiC p l r t = phiC p l r l := by
      intro t ht
      rw [mem_Ico] at ht
      exact phiC_eq_of_no_two ht.1 fun q h1 h2 => hno q h1 (by omega)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      mul_div_cancel_left₀ _ hG.ne']
    by_cases hL : HasTwoLE p l <;> by_cases hGl : HasTwoGT p l
    · -- both sides: one cell around `[l, r]`
      have hno2 : ¬ NoTwo p := fun h => noTwo_iff.1 h _ (isTwo_lastTwoLE hL)
      have hA : lastTwoLE p l < l := lastTwoLE_lt_of_not_isTwo hL hl2
      have hB : r < firstTwoGT p l := by
        by_contra hle
        push Not at hle
        exact hno _ (lt_firstTwoGT p l (by omega)).le hle (isTwo_firstTwoGT hGl)
      have hDLmin : min 1 ((DL p l : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
        rw [min_eq_left]
        rw [le_div_iff₀ hG, one_mul, DL]
        exact_mod_cast (by omega : r - l ≤ firstTwoGT p l - l)
      have hDRmin : min 1 ((DR p r : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
        rw [min_eq_left]
        rw [le_div_iff₀ hG, one_mul, DR, e3 hL]
        exact_mod_cast (by omega : r - l ≤ r - lastTwoLE p l)
      have hcr : carrierAt p r = carrierAt p l := carrierAt_eq_of_gap_eq hL hGl (e3 hL) (e4 hGl)
      rw [hDLmin, hDRmin, if_neg hno2, add_zero]
      have hLr : HasTwoLE p r := e1.2 hL
      have hGr : HasTwoGT p r := e2.2 hGl
      unfold phiC
      rcases lt_trichotomy (carrierAt p l) l with h | h | h
      · rw [if_neg (fun h' => absurd h'.2.2.1 (not_lt.2 h.le)), if_pos ⟨hl2, hGl, Or.inr h.le⟩,
          if_neg (fun h' => h'.2.2.elim (fun h'' => h'' hGr) (fun h'' => by rw [hcr] at h''; omega))]
        ring
      · rw [if_neg (fun h' => absurd h'.2.2.1 (not_lt.2 h.le)), if_pos ⟨hl2, hGl, Or.inr h.le⟩,
          if_neg (fun h' => h'.2.2.elim (fun h'' => h'' hGr) (fun h'' => by rw [hcr] at h''; omega))]
        ring
      · rcases lt_or_ge (carrierAt p l) r with h' | h'
        · rw [if_pos ⟨hL, hGl, h, h'⟩,
            if_neg (fun h'' => h''.2.2.elim (fun e => e hL) (fun e => by omega)),
            if_neg (fun h'' => h''.2.2.elim (fun e => e hGr) (fun e => by rw [hcr] at e; omega))]
          ring
        · rw [if_neg (fun h'' => absurd h''.2.2.2 (not_lt.2 h')),
            if_neg (fun h'' => h''.2.2.elim (fun e => e hL) (fun e => by omega)),
            if_pos ⟨hr2, hLr, Or.inr (hcr ▸ h')⟩]
          ring
    · -- a `2` before, none after
      have hno2 : ¬ NoTwo p := fun h => noTwo_iff.1 h _ (isTwo_lastTwoLE hL)
      have hA : lastTwoLE p l < l := lastTwoLE_lt_of_not_isTwo hL hl2
      have hDRmin : min 1 ((DR p r : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
        rw [min_eq_left]
        rw [le_div_iff₀ hG, one_mul, DR, e3 hL]
        exact_mod_cast (by omega : r - l ≤ r - lastTwoLE p l)
      rw [hDRmin, if_neg hno2, add_zero, phiC_of_not_hasTwoGT hGl, if_neg (fun h => hGl h.2.1),
        if_pos ⟨hr2, e1.2 hL, Or.inl (fun h => hGl (e2.1 h))⟩]
      ring
    · -- a `2` after, none before
      have hno2 : ¬ NoTwo p := fun h => noTwo_iff.1 h _ (isTwo_firstTwoGT hGl)
      have hB : r < firstTwoGT p l := by
        by_contra hle
        push Not at hle
        exact hno _ (lt_firstTwoGT p l (by omega)).le hle (isTwo_firstTwoGT hGl)
      have hDLmin : min 1 ((DL p l : ℝ) / ((r - l : ℕ) : ℝ)) = 1 := by
        rw [min_eq_left]
        rw [le_div_iff₀ hG, one_mul, DL]
        exact_mod_cast (by omega : r - l ≤ firstTwoGT p l - l)
      rw [hDLmin, if_neg hno2, add_zero, phiC_of_not_hasTwoLE hL, if_pos ⟨hl2, hGl, Or.inl hL⟩,
        if_neg (fun h => hL (e1.1 h.2.1))]
      ring
    · -- no `2` at all
      have hno2 : NoTwo p := by
        rw [noTwo_iff]
        intro q hq
        by_cases hql : q ≤ l
        · exact hL ⟨q, hql, hq⟩
        · exact hGl ⟨q, by omega, hq⟩
      rw [if_pos hno2, phiC_of_not_hasTwoLE hL, if_neg (fun h => hGl h.2.1),
        if_neg (fun h => hL (e1.1 h.2.1))]
      ring

end MonoidProduct.Infix
