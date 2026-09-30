import MonoidProduct.Width.StableOrder
import Mathlib.Algebra.Group.WithOne.Defs

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The strict stock-summary monoid (`prop:stock-beta`)

The paper's stock instance: the profit of a price word is `max_{i<j} (x_j − x_i)`, which is
`−∞` (here `⊥ : WithBot ℤ`) on a singleton and negative on a falling word.  A nonempty
summary is `(lo, hi, profit)` with `profit : WithBot ℤ`, the singleton `p` is `(p, p, ⊥)`,
and

    (a, b, c) * (d, e, f) = (min a d, max b e, max c (max f ↑(e − a))).

* `Semigroup`, the stable order `(a,b,c) ≤ (d,e,f) ↔ d ≤ a ∧ b ≤ e ∧ c ≤ f` with the adjoined
  empty summary least (`isStableOrder_summaries`);
* semantics: `wordProd_spec` (attained minimum, maximum and strict best profit, with the
  bounds), `wordProd_profit_eq_strictProfit` identifying the profit coordinate of the monoid
  readout with the strict stock problem `strictProfit`;
* `isBreadthBound_strict`: `β ≤ 4` for every finite price alphabet, with no clipping at
  zero (a minimum position, a maximum position and an optimal pair `i < j` are retained).

This file is self-contained.
-/

namespace MonoidProduct
namespace StrictStock

/-! ## Summaries -/

/-- A nonempty strict stock summary: minimum, maximum, strict best profit (`⊥` if no pair). -/
@[ext] structure SSumm where
  lo : ℤ
  hi : ℤ
  profit : WithBot ℤ
deriving DecidableEq

instance : Mul SSumm :=
  ⟨fun s t => ⟨min s.lo t.lo, max s.hi t.hi,
    max s.profit (max t.profit ((t.hi - s.lo : ℤ) : WithBot ℤ))⟩⟩

@[simp] lemma mul_lo (s t : SSumm) : (s * t).lo = min s.lo t.lo := rfl
@[simp] lemma mul_hi (s t : SSumm) : (s * t).hi = max s.hi t.hi := rfl
@[simp] lemma mul_profit (s t : SSumm) :
    (s * t).profit = max s.profit (max t.profit ((t.hi - s.lo : ℤ) : WithBot ℤ)) := rfl

lemma coe_sub_min (u a b : ℤ) :
    ((u - min a b : ℤ) : WithBot ℤ) = max ((u - a : ℤ) : WithBot ℤ) ((u - b : ℤ) : WithBot ℤ) := by
  rw [← WithBot.coe_max]
  congr 1
  omega

lemma coe_max_sub (a b u : ℤ) :
    ((max a b - u : ℤ) : WithBot ℤ) = max ((a - u : ℤ) : WithBot ℤ) ((b - u : ℤ) : WithBot ℤ) := by
  rw [← WithBot.coe_max]
  congr 1
  omega

instance : Semigroup SSumm where
  mul_assoc a b c := by
    ext
    · simp only [mul_lo]; omega
    · simp only [mul_hi]; omega
    · simp only [mul_profit, mul_hi, mul_lo, coe_sub_min, coe_max_sub]
      ac_rfl

/-- The strict stock monoid: summaries with the empty segment adjoined as identity. -/
abbrev Summaries : Type := WithOne SSumm

instance instDecidableEqSummaries : DecidableEq Summaries :=
  inferInstanceAs (DecidableEq (Option SSumm))

/-- The summary of a single price: no transaction, profit `⊥`. -/
def price (p : ℤ) : SSumm := ⟨p, p, ⊥⟩

/-- The letter of a price. -/
def letter {σ : Type} (pr : σ → ℤ) (a : σ) : Summaries := (price (pr a) : Summaries)

/-- The profit coordinate of the monoid readout; `⊥` for the empty word. -/
def profitOf : Summaries → WithBot ℤ := fun y => y.elim ⊥ SSumm.profit

@[simp] lemma profitOf_one : profitOf (1 : Summaries) = ⊥ := rfl
@[simp] lemma profitOf_coe (s : SSumm) : profitOf (s : Summaries) = s.profit := rfl

/-! ## The order -/

/-- `(a, b, c) ≤ (d, e, f)` iff `a ≥ d`, `b ≤ e`, `c ≤ f`. -/
def SummLE (s t : SSumm) : Prop := t.lo ≤ s.lo ∧ s.hi ≤ t.hi ∧ s.profit ≤ t.profit

/-- The identity is below everything; summaries compare by `SummLE`. -/
def StockLE : Option SSumm → Option SSumm → Prop
  | none, _ => True
  | some _, none => False
  | some s, some t => SummLE s t

instance : LE Summaries := ⟨fun x y => StockLE x y⟩

lemma one_le' (y : Summaries) : (1 : Summaries) ≤ y := trivial

lemma coe_le_coe {s t : SSumm} : (s : Summaries) ≤ (t : Summaries) ↔ SummLE s t := Iff.rfl

lemma not_coe_le_one (s : SSumm) : ¬ (s : Summaries) ≤ 1 := id

/-- Above a summary there are only summaries. -/
lemma coe_le_iff {s : SSumm} {y : Summaries} :
    (s : Summaries) ≤ y ↔ ∃ t : SSumm, y = (t : Summaries) ∧ SummLE s t := by
  induction y using WithOne.recOneCoe with
  | one =>
      exact ⟨fun h => (not_coe_le_one s h).elim, fun ⟨t, ht, _⟩ => (WithOne.one_ne_coe ht).elim⟩
  | coe t =>
      refine ⟨fun h => ⟨t, rfl, h⟩, fun ⟨t', ht', h⟩ => ?_⟩
      rw [WithOne.coe_inj] at ht'
      subst ht'
      exact h

instance : PartialOrder Summaries where
  le_refl x := by
    induction x using WithOne.recOneCoe with
    | one => trivial
    | coe s => exact ⟨le_rfl, le_rfl, le_rfl⟩
  le_trans x y z hxy hyz := by
    induction x using WithOne.recOneCoe with
    | one => trivial
    | coe s =>
        obtain ⟨t, rfl, hst⟩ := coe_le_iff.mp hxy
        obtain ⟨u, rfl, htu⟩ := coe_le_iff.mp hyz
        exact ⟨htu.1.trans hst.1, hst.2.1.trans htu.2.1, hst.2.2.trans htu.2.2⟩
  le_antisymm x y hxy hyx := by
    induction x using WithOne.recOneCoe with
    | one =>
        induction y using WithOne.recOneCoe with
        | one => rfl
        | coe t => exact (not_coe_le_one t hyx).elim
    | coe s =>
        obtain ⟨t, rfl, hst⟩ := coe_le_iff.mp hxy
        have hts : SummLE t s := hyx
        have : s = t := by
          ext
          · exact le_antisymm hts.1 hst.1
          · exact le_antisymm hst.2.1 hts.2.1
          · exact le_antisymm hst.2.2 hts.2.2
        rw [this]

/-- The order is stable with least identity. -/
theorem isStableOrder_summaries : IsStableOrder Summaries where
  one_le := one_le'
  mul_le_mul_left := by
    intro a b c hab
    induction c using WithOne.recOneCoe with
    | one => simpa using hab
    | coe u =>
        induction a using WithOne.recOneCoe with
        | one =>
            induction b using WithOne.recOneCoe with
            | one => exact le_rfl
            | coe t =>
                rw [mul_one, ← WithOne.coe_mul, coe_le_coe]
                refine ⟨?_, ?_, ?_⟩
                · simp only [mul_lo]; omega
                · simp only [mul_hi]; omega
                · simp only [mul_profit]; exact le_max_left _ _
        | coe s =>
            obtain ⟨t, rfl, hst⟩ := coe_le_iff.mp hab
            rw [← WithOne.coe_mul, ← WithOne.coe_mul, coe_le_coe]
            obtain ⟨h1, h2, h3⟩ := hst
            refine ⟨?_, ?_, ?_⟩
            · simp only [mul_lo]; omega
            · simp only [mul_hi]; omega
            · simp only [mul_profit]
              exact max_le_max le_rfl (max_le_max h3 (WithBot.coe_le_coe.2 (by omega)))
  mul_le_mul_right := by
    intro a b c hab
    induction c using WithOne.recOneCoe with
    | one => simpa using hab
    | coe u =>
        induction a using WithOne.recOneCoe with
        | one =>
            induction b using WithOne.recOneCoe with
            | one => exact le_rfl
            | coe t =>
                rw [one_mul, ← WithOne.coe_mul, coe_le_coe]
                refine ⟨?_, ?_, ?_⟩
                · simp only [mul_lo]; omega
                · simp only [mul_hi]; omega
                · simp only [mul_profit]; exact le_max_of_le_right (le_max_left _ _)
        | coe s =>
            obtain ⟨t, rfl, hst⟩ := coe_le_iff.mp hab
            rw [← WithOne.coe_mul, ← WithOne.coe_mul, coe_le_coe]
            obtain ⟨h1, h2, h3⟩ := hst
            refine ⟨?_, ?_, ?_⟩
            · simp only [mul_lo]; omega
            · simp only [mul_hi]; omega
            · simp only [mul_profit]
              exact max_le_max h3 (max_le_max le_rfl (WithBot.coe_le_coe.2 (by omega)))

/-! ## Word products -/

section Words

variable {σ : Type} (pr : σ → ℤ)

lemma wordProd_succ {n : ℕ} (x : Fin (n + 1) → σ) :
    wordProd (letter pr) x = letter pr (x 0) * wordProd (letter pr) (fun i => x i.succ) := by
  rw [wordProd, wordProd, orderedProd_eq_prod_ofFn, orderedProd_eq_prod_ofFn, List.ofFn_succ,
    List.prod_cons]

lemma wordProd_zero (x : Fin 0 → σ) : wordProd (letter pr) x = 1 := by
  rw [wordProd, orderedProd_eq_prod_ofFn, List.ofFn_zero, List.prod_nil]

/-- **Semantics of the strict summary**: a nonempty word's summary has the attained minimum
and maximum of the prices and the attained strict best profit, `⊥` when no pair exists. -/
theorem wordProd_spec {n : ℕ} (x : Fin (n + 1) → σ) :
    ∃ s : SSumm, wordProd (letter pr) x = s
      ∧ (∀ i, s.lo ≤ pr (x i)) ∧ (∃ i, s.lo = pr (x i))
      ∧ (∀ i, pr (x i) ≤ s.hi) ∧ (∃ i, s.hi = pr (x i))
      ∧ (∀ i j, i < j → ((pr (x j) - pr (x i) : ℤ) : WithBot ℤ) ≤ s.profit)
      ∧ (s.profit = ⊥ ∨ ∃ i j, i < j ∧ s.profit = ((pr (x j) - pr (x i) : ℤ) : WithBot ℤ)) := by
  induction n with
  | zero =>
      refine ⟨price (pr (x 0)), ?_, fun i => by rw [Fin.fin_one_eq_zero i]; exact le_rfl, ⟨0, rfl⟩,
        fun i => by rw [Fin.fin_one_eq_zero i]; exact le_rfl, ⟨0, rfl⟩, fun i j hij => ?_,
        Or.inl rfl⟩
      · rw [wordProd_succ, wordProd_zero, mul_one]; rfl
      · exact absurd hij (by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; exact lt_irrefl _)
  | succ n ih =>
      obtain ⟨s, hs, hlo, ⟨il, hl⟩, hhi, ⟨ih', hh⟩, hpb, hp⟩ := ih (fun i => x i.succ)
      have hbot : ∀ c : WithBot ℤ, max (⊥ : WithBot ℤ) c = c := fun c => max_eq_right bot_le
      refine ⟨price (pr (x 0)) * s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [wordProd_succ, hs, letter, WithOne.coe_mul]
      · intro i
        induction i using Fin.cases with
        | zero => simp only [mul_lo, price]; omega
        | succ i => have := hlo i; simp only [mul_lo, price]; omega
      · by_cases h : pr (x 0) ≤ s.lo
        · exact ⟨0, by simp only [mul_lo, price]; omega⟩
        · exact ⟨il.succ, by simp only [mul_lo, price]; omega⟩
      · intro i
        induction i using Fin.cases with
        | zero => simp only [mul_hi, price]; omega
        | succ i => have := hhi i; simp only [mul_hi, price]; omega
      · by_cases h : s.hi ≤ pr (x 0)
        · exact ⟨0, by simp only [mul_hi, price]; omega⟩
        · exact ⟨ih'.succ, by simp only [mul_hi, price]; omega⟩
      · intro i j hij
        simp only [mul_profit, price, hbot]
        induction i using Fin.cases with
        | zero =>
            obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.pos_iff_ne_zero.mp hij)
            refine le_max_of_le_right (WithBot.coe_le_coe.2 ?_)
            have := hhi j'
            omega
        | succ i =>
            obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.pos_iff_ne_zero.mp
              ((Fin.succ_pos i).trans hij))
            exact le_max_of_le_left (hpb i j' (Fin.succ_lt_succ_iff.mp hij))
      · simp only [mul_profit, price, hbot]
        rcases le_total s.profit ((s.hi - pr (x 0) : ℤ) : WithBot ℤ) with h | h
        · refine Or.inr ⟨0, ih'.succ, Fin.succ_pos _, ?_⟩
          rw [max_eq_right h, hh]
        · rw [max_eq_left h]
          rcases hp with hp | ⟨i, j, hij, hij'⟩
          · exact absurd (hp ▸ h) (not_le.2 (WithBot.bot_lt_coe _))
          · exact Or.inr ⟨i.succ, j.succ, Fin.succ_lt_succ_iff.mpr hij, hij'⟩

/-- **The strict stock problem**: the best strict profit `max_{i<j} (x_j − x_i)`, `⊥` when
there is no pair. -/
def strictProfit {n : ℕ} (x : Fin n → σ) : WithBot ℤ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).sup
    fun p => ((pr (x p.2) - pr (x p.1) : ℤ) : WithBot ℤ)

/-- **The monoid readout is the strict stock problem.** -/
theorem profitOf_wordProd_eq_strictProfit {n : ℕ} (x : Fin n → σ) :
    profitOf (wordProd (letter pr) x) = strictProfit pr x := by
  cases n with
  | zero =>
      rw [wordProd_zero, profitOf_one]
      symm
      exact (Finset.sup_eq_bot_iff _ _).2 fun p _ => p.1.elim0
  | succ n =>
      obtain ⟨s, hs, -, -, -, -, hpb, hp⟩ := wordProd_spec pr x
      rw [hs, profitOf_coe]
      apply le_antisymm
      · rcases hp with hp | ⟨i, j, hij, hij'⟩
        · rw [hp]; exact bot_le
        · rw [hij']
          exact Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) =>
            ((pr (x p.2) - pr (x p.1) : ℤ) : WithBot ℤ))
            (Finset.mem_filter.2 ⟨Finset.mem_univ (i, j), hij⟩)
      · exact Finset.sup_le fun p hp => hpb p.1 p.2 (Finset.mem_filter.1 hp).2

/-- The minimum and maximum coordinates are the actual minimum and maximum prices. -/
theorem wordProd_lo_hi {n : ℕ} (x : Fin (n + 1) → σ) :
    ∃ s : SSumm, wordProd (letter pr) x = s
      ∧ s.lo = Finset.univ.inf' Finset.univ_nonempty (fun i => pr (x i))
      ∧ s.hi = Finset.univ.sup' Finset.univ_nonempty (fun i => pr (x i)) := by
  obtain ⟨s, hs, hlo, ⟨il, hl⟩, hhi, ⟨ih, hh⟩, -, -⟩ := wordProd_spec pr x
  refine ⟨s, hs, le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · exact Finset.le_inf' Finset.univ_nonempty (fun i => pr (x i)) fun i _ => hlo i
  · rw [hl]; exact Finset.inf'_le (fun i => pr (x i)) (Finset.mem_univ il)
  · rw [hh]; exact Finset.le_sup' (fun i => pr (x i)) (Finset.mem_univ ih)
  · exact Finset.sup'_le Finset.univ_nonempty (fun i => pr (x i)) fun i _ => hhi i

/-- The cons decomposition of a masked subword product. -/
lemma subwordProd_succ {n : ℕ} (x : Fin (n + 1) → σ) (u : Finset (Fin (n + 1))) :
    subwordProd (letter pr) x u
      = (if (0 : Fin (n + 1)) ∈ u then letter pr (x 0) else 1)
        * subwordProd (letter pr) (fun i => x i.succ) (Finset.univ.filter fun i => i.succ ∈ u) := by
  unfold subwordProd
  rw [List.ofFn_succ, List.prod_cons]
  congr 2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma subwordProd_singleton {n : ℕ} (x : Fin n → σ) (i : Fin n) :
    subwordProd (letter pr) x {i} = letter pr (x i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [subwordProd_succ]
      induction i using Fin.cases with
      | zero =>
          rw [if_pos (Finset.mem_singleton_self _)]
          have : (Finset.univ.filter fun j : Fin n =>
              j.succ ∈ ({0} : Finset (Fin (n + 1)))) = ∅ := by
            ext j; simp [Fin.succ_ne_zero]
          rw [this, subwordProd_empty, mul_one]
      | succ i =>
          rw [if_neg (by simp only [Finset.mem_singleton]; exact (Fin.succ_ne_zero i).symm),
            one_mul]
          have : (Finset.univ.filter fun j : Fin n => j.succ ∈ ({i.succ} : Finset (Fin (n + 1))))
              = {i} := by
            ext j; simp [Fin.succ_inj]
          rw [this, ih]

lemma subwordProd_pair {n : ℕ} (x : Fin n → σ) {i j : Fin n} (hij : i < j) :
    subwordProd (letter pr) x {i, j} = letter pr (x i) * letter pr (x j) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [subwordProd_succ]
      induction i using Fin.cases with
      | zero =>
          obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.pos_iff_ne_zero.mp hij)
          rw [if_pos (Finset.mem_insert_self _ _)]
          have : (Finset.univ.filter fun k : Fin n =>
              k.succ ∈ ({0, j'.succ} : Finset (Fin (n + 1)))) = {j'} := by
            ext k; simp [Fin.succ_ne_zero, Fin.succ_inj]
          rw [this, subwordProd_singleton]
      | succ i =>
          obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.pos_iff_ne_zero.mp
            ((Fin.succ_pos i).trans hij))
          rw [if_neg (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨(Fin.succ_ne_zero i).symm, (Fin.succ_ne_zero j').symm⟩), one_mul]
          have : (Finset.univ.filter fun k : Fin n =>
              k.succ ∈ ({i.succ, j'.succ} : Finset (Fin (n + 1)))) = {i, j'} := by
            ext k; simp [Fin.succ_inj]
          rw [this, ih _ (Fin.succ_lt_succ_iff.mp hij)]

/-- **`prop:stock-beta`, the strict core**: `β ≤ 4`.  A minimum position, a maximum
position and an optimal pair `i < j` are retained; no clipping at zero. -/
theorem isBreadthBound_strict : IsBreadthBound (letter pr) 4 := by
  intro n x
  cases n with
  | zero =>
      refine ⟨∅, by simp, ?_⟩
      unfold IsCore
      rw [← subwordProd_univ, Finset.univ_eq_empty]
  | succ n =>
      obtain ⟨s, hs, -, ⟨il, hl⟩, -, ⟨ih, hh⟩, -, hp⟩ := wordProd_spec pr x
      have hst := isStableOrder_summaries
      -- the retained positions
      obtain ⟨u, hcard, hil, hih, hprof⟩ : ∃ u : Finset (Fin (n + 1)), u.card ≤ 4 ∧ il ∈ u ∧
          ih ∈ u ∧ (s.profit = ⊥ ∨ ∃ i j, i < j
            ∧ s.profit = ((pr (x j) - pr (x i) : ℤ) : WithBot ℤ)
            ∧ ({i, j} : Finset (Fin (n + 1))) ⊆ u) := by
        rcases hp with hp | ⟨i, j, hij, hij'⟩
        · exact ⟨{il, ih}, (Finset.card_insert_le _ _).trans (by simp), by simp, by simp,
            Or.inl hp⟩
        · refine ⟨{il, ih, i, j}, ?_, by simp, by simp, Or.inr ⟨i, j, hij, hij', ?_⟩⟩
          · exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
              ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_two)))
          · intro k hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
            omega
      refine ⟨u, hcard, ?_⟩
      unfold IsCore
      refine le_antisymm (hst.subwordProd_le_wordProd _ _ u) ?_
      rw [hs]
      -- the retained minimum
      have h1 := hst.subwordProd_mono (letter pr) x (Finset.singleton_subset_iff.mpr hil)
      rw [subwordProd_singleton] at h1
      change (price (pr (x il)) : Summaries) ≤ _ at h1
      obtain ⟨t, ht, hlt⟩ := coe_le_iff.mp h1
      -- the retained maximum
      have h2 := hst.subwordProd_mono (letter pr) x (Finset.singleton_subset_iff.mpr hih)
      rw [subwordProd_singleton] at h2
      change (price (pr (x ih)) : Summaries) ≤ _ at h2
      rw [ht, coe_le_coe] at h2
      rw [ht, coe_le_coe]
      -- the retained profit
      have hprofit : s.profit ≤ t.profit := by
        rcases hprof with hp0 | ⟨i, j, hij, hij', hsub⟩
        · rw [hp0]; exact bot_le
        · have h3 := hst.subwordProd_mono (letter pr) x hsub
          rw [subwordProd_pair pr x hij] at h3
          change (price (pr (x i)) : Summaries) * (price (pr (x j)) : Summaries) ≤ _ at h3
          rw [← WithOne.coe_mul, ht, coe_le_coe] at h3
          have := h3.2.2
          simp only [mul_profit, price, max_eq_right bot_le] at this
          rw [hij']
          exact this
      refine ⟨?_, ?_, hprofit⟩ <;> simp only [SummLE, price] at hlt h2 <;> omega

end Words

end StrictStock
end MonoidProduct
