import MonoidProduct.Quantum.StrictStockApplications
import Mathlib.Algebra.Group.WithOne.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The strict stock monoid over a general price set (`prop:stock-beta`)

The paper's Section `sec:stock-beta`, Proposition `prop:stock-beta`: fix a finite set of prices
`P`; the monoid `M_P` of reachable stock summaries (with an identity for the empty
interval) is finite, has a stable partial order with the identity least, and
`β_{G_P}(M_P) ≤ 4`; hence the complete summary costs `O(√n·log¹⁰(n+2))` queries, with an
absolute constant independent of `P`.

`Stock/Strict.lean` proves this for integer prices.  Here the prices lie in an arbitrary
linearly ordered additive commutative group `P` (so `ℝ`, `ℚ`, `ℤ`, …), and the finite price
set is the image of a price map `pr : σ → P` on a finite alphabet `σ`.  A nonempty summary is
`(lo, hi, profit)` with `profit : WithBot P`, the singleton `p` is `(p, p, ⊥)`, and

    (a, b, c) * (d, e, f) = (min a d, max b e, max c (max f ↑(e − a))).

* `GSumm`, `GSummaries P := WithOne (GSumm P)`: the semigroup and the monoid;
  `gstock_isStableOrder`: the stable order with least identity;
* `gstock_wordProd_spec`, `gstock_wordProd_lo_hi`, `gstock_profitOf_wordProd`: semantics —
  the third coordinate is `max_{i<j}(x_j − x_i)` (`gstockProfit`), `⊥` for the empty word and
  for singletons;
* `gstock_reach_finite`: `M_P` (the set of word products) is finite;
* `gstock_isBreadthBound`: `β ≤ 4`;
* `gstock_qQuery_le_five_halves`, `gstock_qQuery_third_le`, `gstockProfit_qQuery_third_le`:
  the query bound via `thm:ordered-beta-product` (`ordered_qQuery_le_five_halves`), with the
  constant `(2^29)^4` independent of `P` and `σ`;
* `gstock_sharp`, `gstock_sharp_real`: the word `(10, 2, 5, 0)` needs all four positions
  whenever the alphabet contains these prices (in any `P`, along a strictly monotone additive
  map `ℤ → P`; in particular for `P = ℝ`), transported from the kernel-checked integer case.
-/

namespace MonoidProduct
namespace GenStock

/-! ## Summaries -/

variable {P : Type} [AddCommGroup P] [LinearOrder P] [IsOrderedAddMonoid P]

/-- A nonempty strict stock summary over the price group `P`: minimum, maximum, strict best
profit (`⊥` if no pair). -/
@[ext] structure GSumm (P : Type) where
  /-- The minimum price. -/
  lo : P
  /-- The maximum price. -/
  hi : P
  /-- The strict best profit `max_{i<j}(x_j − x_i)`, `⊥` when there is no pair. -/
  profit : WithBot P
deriving DecidableEq

instance : Mul (GSumm P) :=
  ⟨fun s t => ⟨min s.lo t.lo, max s.hi t.hi,
    max s.profit (max t.profit ((t.hi - s.lo : P) : WithBot P))⟩⟩

@[simp] lemma mul_lo (s t : GSumm P) : (s * t).lo = min s.lo t.lo := rfl
@[simp] lemma mul_hi (s t : GSumm P) : (s * t).hi = max s.hi t.hi := rfl
@[simp] lemma mul_profit (s t : GSumm P) :
    (s * t).profit = max s.profit (max t.profit ((t.hi - s.lo : P) : WithBot P)) := rfl

lemma gstock_coe_sub_min (u a b : P) :
    ((u - min a b : P) : WithBot P) = max ((u - a : P) : WithBot P) ((u - b : P) : WithBot P) := by
  rw [← WithBot.coe_max, max_sub_sub_left]

lemma gstock_coe_max_sub (a b u : P) :
    ((max a b - u : P) : WithBot P) = max ((a - u : P) : WithBot P) ((b - u : P) : WithBot P) := by
  rw [← WithBot.coe_max, max_sub_sub_right]

instance : Semigroup (GSumm P) where
  mul_assoc a b c := by
    ext
    · simp only [mul_lo, min_assoc]
    · simp only [mul_hi, max_assoc]
    · simp only [mul_profit, mul_hi, mul_lo, gstock_coe_sub_min, gstock_coe_max_sub]
      ac_rfl

/-- The strict stock monoid over `P`: summaries with the empty segment adjoined as identity. -/
abbrev GSummaries (P : Type) : Type := WithOne (GSumm P)

instance instDecidableEqGSummaries : DecidableEq (GSummaries P) :=
  inferInstanceAs (DecidableEq (Option (GSumm P)))

/-- The summary of a single price: no transaction, profit `⊥`. -/
def gprice (p : P) : GSumm P := ⟨p, p, ⊥⟩

/-- The letter of a price (the generator `(p, p, −∞)` of `G_P`). -/
def gletter {σ : Type} (pr : σ → P) (a : σ) : GSummaries P := (gprice (pr a) : GSummaries P)

/-- The profit coordinate of the monoid readout; `⊥` for the empty word. -/
def gprofitOf : GSummaries P → WithBot P := fun y => y.elim ⊥ GSumm.profit

@[simp] lemma gprofitOf_one : gprofitOf (1 : GSummaries P) = ⊥ := rfl
@[simp] lemma gprofitOf_coe (s : GSumm P) : gprofitOf (s : GSummaries P) = s.profit := rfl

/-! ## The order -/

/-- `(a, b, c) ≤ (d, e, f)` iff `a ≥ d`, `b ≤ e`, `c ≤ f`. -/
def GSummLE (s t : GSumm P) : Prop := t.lo ≤ s.lo ∧ s.hi ≤ t.hi ∧ s.profit ≤ t.profit

/-- The identity is below everything; summaries compare by `GSummLE`. -/
def GStockLE : Option (GSumm P) → Option (GSumm P) → Prop
  | none, _ => True
  | some _, none => False
  | some s, some t => GSummLE s t

instance : LE (GSummaries P) := ⟨fun x y => GStockLE x y⟩

lemma gstock_one_le (y : GSummaries P) : (1 : GSummaries P) ≤ y := trivial

lemma gstock_coe_le_coe {s t : GSumm P} :
    (s : GSummaries P) ≤ (t : GSummaries P) ↔ GSummLE s t := Iff.rfl

lemma gstock_not_coe_le_one (s : GSumm P) : ¬ (s : GSummaries P) ≤ 1 := id

/-- Above a summary there are only summaries. -/
lemma gstock_coe_le_iff {s : GSumm P} {y : GSummaries P} :
    (s : GSummaries P) ≤ y ↔ ∃ t : GSumm P, y = (t : GSummaries P) ∧ GSummLE s t := by
  induction y using WithOne.recOneCoe with
  | one =>
      exact ⟨fun h => (gstock_not_coe_le_one s h).elim,
        fun ⟨t, ht, _⟩ => (WithOne.one_ne_coe ht).elim⟩
  | coe t =>
      refine ⟨fun h => ⟨t, rfl, h⟩, fun ⟨t', ht', h⟩ => ?_⟩
      rw [WithOne.coe_inj] at ht'
      subst ht'
      exact h

instance : PartialOrder (GSummaries P) where
  le_refl x := by
    induction x using WithOne.recOneCoe with
    | one => trivial
    | coe s => exact ⟨le_rfl, le_rfl, le_rfl⟩
  le_trans x y z hxy hyz := by
    induction x using WithOne.recOneCoe with
    | one => trivial
    | coe s =>
        obtain ⟨t, rfl, hst⟩ := gstock_coe_le_iff.mp hxy
        obtain ⟨u, rfl, htu⟩ := gstock_coe_le_iff.mp hyz
        exact ⟨htu.1.trans hst.1, hst.2.1.trans htu.2.1, hst.2.2.trans htu.2.2⟩
  le_antisymm x y hxy hyx := by
    induction x using WithOne.recOneCoe with
    | one =>
        induction y using WithOne.recOneCoe with
        | one => rfl
        | coe t => exact (gstock_not_coe_le_one t hyx).elim
    | coe s =>
        obtain ⟨t, rfl, hst⟩ := gstock_coe_le_iff.mp hxy
        have hts : GSummLE t s := hyx
        have : s = t := by
          ext
          · exact le_antisymm hts.1 hst.1
          · exact le_antisymm hst.2.1 hts.2.1
          · exact le_antisymm hst.2.2 hts.2.2
        rw [this]

/-- **`prop:stock-beta`, the order**: stable, with the identity least. -/
theorem gstock_isStableOrder : IsStableOrder (GSummaries P) where
  one_le := gstock_one_le
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
                rw [mul_one, ← WithOne.coe_mul, gstock_coe_le_coe]
                exact ⟨min_le_left _ _, le_max_left _ _, le_max_left _ _⟩
        | coe s =>
            obtain ⟨t, rfl, hst⟩ := gstock_coe_le_iff.mp hab
            rw [← WithOne.coe_mul, ← WithOne.coe_mul, gstock_coe_le_coe]
            obtain ⟨h1, h2, h3⟩ := hst
            refine ⟨min_le_min le_rfl h1, max_le_max le_rfl h2, ?_⟩
            simp only [mul_profit]
            exact max_le_max le_rfl
              (max_le_max h3 (WithBot.coe_le_coe.2 (sub_le_sub_right h2 _)))
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
                rw [one_mul, ← WithOne.coe_mul, gstock_coe_le_coe]
                exact ⟨min_le_right _ _, le_max_right _ _,
                  le_max_of_le_right (le_max_left _ _)⟩
        | coe s =>
            obtain ⟨t, rfl, hst⟩ := gstock_coe_le_iff.mp hab
            rw [← WithOne.coe_mul, ← WithOne.coe_mul, gstock_coe_le_coe]
            obtain ⟨h1, h2, h3⟩ := hst
            refine ⟨min_le_min h1 le_rfl, max_le_max h2 le_rfl, ?_⟩
            simp only [mul_profit]
            exact max_le_max h3
              (max_le_max le_rfl (WithBot.coe_le_coe.2 (sub_le_sub_left h1 _)))

/-! ## Word products -/

section Words

variable {σ : Type} (pr : σ → P)

lemma gstock_wordProd_succ {n : ℕ} (x : Fin (n + 1) → σ) :
    wordProd (gletter pr) x = gletter pr (x 0) * wordProd (gletter pr) (fun i => x i.succ) := by
  rw [wordProd, wordProd, orderedProd_eq_prod_ofFn, orderedProd_eq_prod_ofFn, List.ofFn_succ,
    List.prod_cons]

lemma gstock_wordProd_zero (x : Fin 0 → σ) : wordProd (gletter pr) x = 1 := by
  rw [wordProd, orderedProd_eq_prod_ofFn, List.ofFn_zero, List.prod_nil]

/-- **Semantics of the summary**: a nonempty word's summary has the attained minimum and
maximum of the prices and the attained strict best profit, `⊥` when no pair exists. -/
theorem gstock_wordProd_spec {n : ℕ} (x : Fin (n + 1) → σ) :
    ∃ s : GSumm P, wordProd (gletter pr) x = s
      ∧ (∀ i, s.lo ≤ pr (x i)) ∧ (∃ i, s.lo = pr (x i))
      ∧ (∀ i, pr (x i) ≤ s.hi) ∧ (∃ i, s.hi = pr (x i))
      ∧ (∀ i j, i < j → ((pr (x j) - pr (x i) : P) : WithBot P) ≤ s.profit)
      ∧ (s.profit = ⊥ ∨ ∃ i j, i < j ∧ s.profit = ((pr (x j) - pr (x i) : P) : WithBot P)) := by
  induction n with
  | zero =>
      refine ⟨gprice (pr (x 0)), ?_, fun i => by rw [Fin.fin_one_eq_zero i]; exact le_rfl,
        ⟨0, rfl⟩, fun i => by rw [Fin.fin_one_eq_zero i]; exact le_rfl, ⟨0, rfl⟩,
        fun i j hij => ?_, Or.inl rfl⟩
      · rw [gstock_wordProd_succ, gstock_wordProd_zero, mul_one]; rfl
      · exact absurd hij (by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; exact lt_irrefl _)
  | succ n ih =>
      obtain ⟨s, hs, hlo, ⟨il, hl⟩, hhi, ⟨ih', hh⟩, hpb, hp⟩ := ih (fun i => x i.succ)
      have hbot : ∀ c : WithBot P, max (⊥ : WithBot P) c = c := fun c => max_eq_right bot_le
      refine ⟨gprice (pr (x 0)) * s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [gstock_wordProd_succ, hs, gletter, WithOne.coe_mul]
      · intro i
        induction i using Fin.cases with
        | zero => exact min_le_left _ _
        | succ i => exact min_le_of_right_le (hlo i)
      · by_cases h : pr (x 0) ≤ s.lo
        · exact ⟨0, min_eq_left h⟩
        · exact ⟨il.succ, (min_eq_right (le_of_not_ge h)).trans hl⟩
      · intro i
        induction i using Fin.cases with
        | zero => exact le_max_left _ _
        | succ i => exact le_max_of_le_right (hhi i)
      · by_cases h : s.hi ≤ pr (x 0)
        · exact ⟨0, max_eq_left h⟩
        · exact ⟨ih'.succ, (max_eq_right (le_of_not_ge h)).trans hh⟩
      · intro i j hij
        simp only [mul_profit, gprice, hbot]
        induction i using Fin.cases with
        | zero =>
            obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.pos_iff_ne_zero.mp hij)
            exact le_max_of_le_right (WithBot.coe_le_coe.2 (sub_le_sub_right (hhi j') _))
        | succ i =>
            obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.pos_iff_ne_zero.mp
              ((Fin.succ_pos i).trans hij))
            exact le_max_of_le_left (hpb i j' (Fin.succ_lt_succ_iff.mp hij))
      · simp only [mul_profit, gprice, hbot]
        rcases le_total s.profit ((s.hi - pr (x 0) : P) : WithBot P) with h | h
        · refine Or.inr ⟨0, ih'.succ, Fin.succ_pos _, ?_⟩
          rw [max_eq_right h, hh]
        · rw [max_eq_left h]
          rcases hp with hp | ⟨i, j, hij, hij'⟩
          · exact absurd (hp ▸ h) (not_le.2 (WithBot.bot_lt_coe _))
          · exact Or.inr ⟨i.succ, j.succ, Fin.succ_lt_succ_iff.mpr hij, hij'⟩

/-- **The strict stock problem over `P`**: the best strict profit `max_{i<j} (x_j − x_i)`,
`⊥` when there is no pair. -/
def gstockProfit {n : ℕ} (x : Fin n → σ) : WithBot P :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).sup
    fun p => ((pr (x p.2) - pr (x p.1) : P) : WithBot P)

/-- **The monoid readout is the strict stock problem**: the third coordinate of the summary
is `max_{i<j}(x_j − x_i)`. -/
theorem gstock_profitOf_wordProd {n : ℕ} (x : Fin n → σ) :
    gprofitOf (wordProd (gletter pr) x) = gstockProfit pr x := by
  cases n with
  | zero =>
      rw [gstock_wordProd_zero, gprofitOf_one]
      symm
      exact (Finset.sup_eq_bot_iff _ _).2 fun p _ => p.1.elim0
  | succ n =>
      obtain ⟨s, hs, -, -, -, -, hpb, hp⟩ := gstock_wordProd_spec pr x
      rw [hs, gprofitOf_coe]
      apply le_antisymm
      · rcases hp with hp | ⟨i, j, hij, hij'⟩
        · rw [hp]; exact bot_le
        · rw [hij']
          exact Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) =>
            ((pr (x p.2) - pr (x p.1) : P) : WithBot P))
            (Finset.mem_filter.2 ⟨Finset.mem_univ (i, j), hij⟩)
      · exact Finset.sup_le fun p hp => hpb p.1 p.2 (Finset.mem_filter.1 hp).2

/-- A singleton word has profit `⊥` (no transaction), not `0`. -/
theorem gstockProfit_singleton (x : Fin 1 → σ) : gstockProfit pr x = ⊥ :=
  (Finset.sup_eq_bot_iff _ _).2 fun p hp => by
    have h := (Finset.mem_filter.1 hp).2
    rw [Fin.fin_one_eq_zero p.1, Fin.fin_one_eq_zero p.2] at h
    exact absurd h (lt_irrefl _)

/-- The minimum and maximum coordinates are the actual minimum and maximum prices. -/
theorem gstock_wordProd_lo_hi {n : ℕ} (x : Fin (n + 1) → σ) :
    ∃ s : GSumm P, wordProd (gletter pr) x = s
      ∧ s.lo = Finset.univ.inf' Finset.univ_nonempty (fun i => pr (x i))
      ∧ s.hi = Finset.univ.sup' Finset.univ_nonempty (fun i => pr (x i)) := by
  obtain ⟨s, hs, hlo, ⟨il, hl⟩, hhi, ⟨ih, hh⟩, -, -⟩ := gstock_wordProd_spec pr x
  refine ⟨s, hs, le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · exact Finset.le_inf' Finset.univ_nonempty (fun i => pr (x i)) fun i _ => hlo i
  · rw [hl]; exact Finset.inf'_le (fun i => pr (x i)) (Finset.mem_univ il)
  · rw [hh]; exact Finset.le_sup' (fun i => pr (x i)) (Finset.mem_univ ih)
  · exact Finset.sup'_le Finset.univ_nonempty (fun i => pr (x i)) fun i _ => hhi i

/-! ## `M_P` is finite -/

/-- A code for the reachable summaries: the identity, or `(pr a, pr b, ⊥)`, or
`(pr a, pr b, pr d − pr c)`. -/
def gstockCode : Option (σ × σ × Option (σ × σ)) → GSummaries P
  | none => 1
  | some (a, b, none) => ((⟨pr a, pr b, ⊥⟩ : GSumm P) : GSummaries P)
  | some (a, b, some (c, d)) =>
      ((⟨pr a, pr b, ((pr d - pr c : P) : WithBot P)⟩ : GSumm P) : GSummaries P)

/-- Every word product has a code: its minimum and maximum are prices, and its profit is
`⊥` or a difference of two prices. -/
theorem gstock_wordProd_mem_range {n : ℕ} (x : Fin n → σ) :
    wordProd (gletter pr) x ∈ Set.range (gstockCode pr) := by
  cases n with
  | zero => exact ⟨none, (gstock_wordProd_zero pr x).symm⟩
  | succ n =>
      obtain ⟨s, hs, -, ⟨il, hl⟩, -, ⟨ih, hh⟩, -, hp⟩ := gstock_wordProd_spec pr x
      rw [hs]
      rcases hp with hp | ⟨i, j, -, hij⟩
      · refine ⟨some (x il, x ih, none), ?_⟩
        simp only [gstockCode, WithOne.coe_inj]
        ext <;> simp [hl, hh, hp]
      · refine ⟨some (x il, x ih, some (x i, x j)), ?_⟩
        simp only [gstockCode, WithOne.coe_inj]
        ext <;> simp [hl, hh, hij]

/-- **`M_P` is finite**: over a finite alphabet the reachable summaries (the word products,
the empty word included) form a finite set. -/
theorem gstock_reach_finite [Finite σ] :
    (Set.range fun w : (Σ n, Fin n → σ) => wordProd (gletter pr) w.2).Finite :=
  (Set.finite_range (gstockCode pr)).subset (by
    rintro _ ⟨⟨n, x⟩, rfl⟩
    exact gstock_wordProd_mem_range pr x)

/-! ## The four-position core -/

/-- The cons decomposition of a masked subword product. -/
lemma gstock_subwordProd_succ {n : ℕ} (x : Fin (n + 1) → σ) (u : Finset (Fin (n + 1))) :
    subwordProd (gletter pr) x u
      = (if (0 : Fin (n + 1)) ∈ u then gletter pr (x 0) else 1)
        * subwordProd (gletter pr) (fun i => x i.succ)
            (Finset.univ.filter fun i => i.succ ∈ u) := by
  unfold subwordProd
  rw [List.ofFn_succ, List.prod_cons]
  congr 2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma gstock_subwordProd_singleton {n : ℕ} (x : Fin n → σ) (i : Fin n) :
    subwordProd (gletter pr) x {i} = gletter pr (x i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [gstock_subwordProd_succ]
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
          have : (Finset.univ.filter fun j : Fin n =>
              j.succ ∈ ({i.succ} : Finset (Fin (n + 1)))) = {i} := by
            ext j; simp [Fin.succ_inj]
          rw [this, ih]

lemma gstock_subwordProd_pair {n : ℕ} (x : Fin n → σ) {i j : Fin n} (hij : i < j) :
    subwordProd (gletter pr) x {i, j} = gletter pr (x i) * gletter pr (x j) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [gstock_subwordProd_succ]
      induction i using Fin.cases with
      | zero =>
          obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.pos_iff_ne_zero.mp hij)
          rw [if_pos (Finset.mem_insert_self _ _)]
          have : (Finset.univ.filter fun k : Fin n =>
              k.succ ∈ ({0, j'.succ} : Finset (Fin (n + 1)))) = {j'} := by
            ext k; simp [Fin.succ_ne_zero, Fin.succ_inj]
          rw [this, gstock_subwordProd_singleton]
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

/-- **`prop:stock-beta`, the core**: `β_{G_P}(M_P) ≤ 4`.  A minimum position, a maximum
position and an optimal pair `i < j` are retained; no clipping at zero. -/
theorem gstock_isBreadthBound : IsBreadthBound (gletter pr) 4 := by
  intro n x
  cases n with
  | zero =>
      refine ⟨∅, by simp, ?_⟩
      unfold IsCore
      rw [← subwordProd_univ, Finset.univ_eq_empty]
  | succ n =>
      obtain ⟨s, hs, -, ⟨il, hl⟩, -, ⟨ih, hh⟩, -, hp⟩ := gstock_wordProd_spec pr x
      have hst := (gstock_isStableOrder : IsStableOrder (GSummaries P))
      -- the retained positions
      obtain ⟨u, hcard, hil, hih, hprof⟩ : ∃ u : Finset (Fin (n + 1)), u.card ≤ 4 ∧ il ∈ u ∧
          ih ∈ u ∧ (s.profit = ⊥ ∨ ∃ i j, i < j
            ∧ s.profit = ((pr (x j) - pr (x i) : P) : WithBot P)
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
      have h1 := hst.subwordProd_mono (gletter pr) x (Finset.singleton_subset_iff.mpr hil)
      rw [gstock_subwordProd_singleton] at h1
      change (gprice (pr (x il)) : GSummaries P) ≤ _ at h1
      obtain ⟨t, ht, hlt⟩ := gstock_coe_le_iff.mp h1
      -- the retained maximum
      have h2 := hst.subwordProd_mono (gletter pr) x (Finset.singleton_subset_iff.mpr hih)
      rw [gstock_subwordProd_singleton] at h2
      change (gprice (pr (x ih)) : GSummaries P) ≤ _ at h2
      rw [ht, gstock_coe_le_coe] at h2
      rw [ht, gstock_coe_le_coe]
      -- the retained profit
      have hprofit : s.profit ≤ t.profit := by
        rcases hprof with hp0 | ⟨i, j, hij, hij', hsub⟩
        · rw [hp0]; exact bot_le
        · have h3 := hst.subwordProd_mono (gletter pr) x hsub
          rw [gstock_subwordProd_pair pr x hij] at h3
          change (gprice (pr (x i)) : GSummaries P) * (gprice (pr (x j)) : GSummaries P)
            ≤ _ at h3
          rw [← WithOne.coe_mul, ht, gstock_coe_le_coe] at h3
          have := h3.2.2
          simp only [mul_profit, gprice, max_eq_right bot_le] at this
          rw [hij']
          exact this
      simp only [GSummLE, gprice] at hlt h2
      exact ⟨hl ▸ hlt.1, hh ▸ h2.2.1, hprofit⟩

end Words

/-! ## Query bounds (`thm:ordered-beta-product` at `b = 4`) -/

section Query

open QuantumQueryComplexity

variable {σ : Type} [Fintype σ] [DecidableEq σ] (pr : σ → P)

/-- **The complete summary over `P`** in `O(√n·log¹⁰(n+2))` quantum queries; the constant
`(2^29)^4` does not depend on `P`, `σ` or `pr`. -/
theorem gstock_qQuery_le_five_halves (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd (gletter pr) x) (1 / 10) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 29 : ℝ) ^ 4 * Real.sqrt n * (logLen n : ℝ) ^ 10) := by
  have h := ordered_qQuery_le_five_halves (gletter pr) gstock_isStableOrder
    (gstock_isBreadthBound pr) n
  convert h using 2
  rw [orderedLogFactor_pow_four]
  norm_num

/-- The bounded-error convention `ε = 1/3` for the complete summary. -/
theorem gstock_qQuery_third_le (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd (gletter pr) x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 29 : ℝ) ^ 4 * Real.sqrt n * (logLen n : ℝ) ^ 10) :=
  ordered_qQuery_third_le_of (gletter pr) (gstock_qQuery_le_five_halves pr n)

/-- The strict profit is free postprocessing of the summary. -/
theorem gstockProfit_qQuery_le_wordProd (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → σ => gstockProfit pr x) ε
      ≤ qQuery (fun x : Fin n → σ => wordProd (gletter pr) x) ε := by
  have hne : (QueryCounts (X := Fin n → σ) id
      (fun x => wordProd (gletter pr) x) ε).Nonempty :=
    queryCounts_nonempty (fun x y h => congrArg (fun z => wordProd (gletter pr) z) h) hε
  have h := qQueryOn_postcomp_le (read := (id : (Fin n → σ) → Fin n → σ))
    (f := fun x => wordProd (gletter pr) x) (ε := ε) gprofitOf hne
  simp only [gstock_profitOf_wordProd] at h
  exact h

/-- **The strict stock problem `max_{i<j}(x_j − x_i)` over `P`** in `O(√n·log¹⁰(n+2))`
quantum queries, `ε = 1/3`. -/
theorem gstockProfit_qQuery_third_le (n : ℕ) :
    (qQuery (fun x : Fin n → σ => gstockProfit pr x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 29 : ℝ) ^ 4 * Real.sqrt n * (logLen n : ℝ) ^ 10) :=
  le_trans (by exact_mod_cast gstockProfit_qQuery_le_wordProd pr n (by norm_num))
    (gstock_qQuery_third_le pr n)

end Query

/-! ## Sharpness: `(10, 2, 5, 0)` -/

section Sharp

/-- The integer summaries map into the `P`-summaries along an order-preserving additive map
`φ : ℤ → P`. -/
def gstockMulHom (φ : ℤ →+ P) (hφ : Monotone φ) : StrictStock.SSumm →ₙ* GSumm P where
  toFun s := ⟨φ s.lo, φ s.hi, s.profit.map φ⟩
  map_mul' s t := by
    ext
    · exact hφ.map_min
    · exact hφ.map_max
    · change WithBot.map φ (max s.profit (max t.profit ((t.hi - s.lo : ℤ) : WithBot ℤ))) = _
      rw [hφ.withBot_map.map_max, hφ.withBot_map.map_max, WithBot.map_coe, map_sub]
      rfl

/-- The induced monoid hom `StrictStock.Summaries →* GSummaries P`. -/
def gstockHom (φ : ℤ →+ P) (hφ : Monotone φ) : StrictStock.Summaries →* GSummaries P :=
  WithOne.mapMulHom (gstockMulHom φ hφ)

@[simp] lemma gstockHom_coe (φ : ℤ →+ P) (hφ : Monotone φ) (s : StrictStock.SSumm) :
    gstockHom φ hφ (s : StrictStock.Summaries) = (gstockMulHom φ hφ s : GSummaries P) := rfl

lemma gstockHom_injective (φ : ℤ →+ P) (hφ : StrictMono φ) :
    Function.Injective (gstockHom φ hφ.monotone) := by
  intro a b hab
  induction a using WithOne.recOneCoe with
  | one =>
      induction b using WithOne.recOneCoe with
      | one => rfl
      | coe t => rw [map_one, gstockHom_coe] at hab; exact (WithOne.one_ne_coe hab).elim
  | coe s =>
      induction b using WithOne.recOneCoe with
      | one => rw [map_one, gstockHom_coe] at hab; exact (WithOne.coe_ne_one hab).elim
      | coe t =>
          rw [gstockHom_coe, gstockHom_coe] at hab
          have h : gstockMulHom φ hφ.monotone s = gstockMulHom φ hφ.monotone t :=
            WithOne.coe_inj.1 hab
          have hlo := congrArg GSumm.lo h
          have hhi := congrArg GSumm.hi h
          have hpr := congrArg GSumm.profit h
          change φ s.lo = φ t.lo at hlo
          change φ s.hi = φ t.hi at hhi
          change s.profit.map φ = t.profit.map φ at hpr
          rw [WithOne.coe_inj]
          ext
          · exact hφ.injective hlo
          · exact hφ.injective hhi
          · exact WithBot.map_injective hφ.injective hpr

lemma gstock_letter_eq_hom (φ : ℤ →+ P) (hφ : Monotone φ) (p : ℤ) :
    gletter id (φ p) = gstockHom φ hφ (StrictStock.letter id p) := by
  rw [StrictStock.letter, gstockHom_coe]
  rfl

/-- Letters that are images of integer letters: products are images of integer products. -/
lemma gstock_wordProd_hom {σ τ : Type} (F : StrictStock.Summaries →* GSummaries P)
    (pr : σ → P) (prZ : τ → ℤ) {n : ℕ} (x : Fin n → σ) (y : Fin n → τ)
    (h : ∀ i, gletter pr (x i) = F (StrictStock.letter prZ (y i))) :
    wordProd (gletter pr) x = F (wordProd (StrictStock.letter prZ) y) := by
  rw [wordProd, wordProd, orderedProd_eq_prod_ofFn, orderedProd_eq_prod_ofFn, map_list_prod,
    List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext h))

lemma gstock_subwordProd_hom {σ τ : Type} (F : StrictStock.Summaries →* GSummaries P)
    (pr : σ → P) (prZ : τ → ℤ) {n : ℕ} (x : Fin n → σ) (y : Fin n → τ)
    (h : ∀ i, gletter pr (x i) = F (StrictStock.letter prZ (y i))) (u : Finset (Fin n)) :
    subwordProd (gletter pr) x u = F (subwordProd (StrictStock.letter prZ) y u) := by
  rw [subwordProd, subwordProd, map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  by_cases hi : i ∈ u
  · simp only [Function.comp_apply, if_pos hi, h i]
  · simp only [Function.comp_apply, if_neg hi, map_one]

/-- The integer case, kernel-checked: no three positions of `(10, 2, 5, 0)` carry its
complete summary. -/
theorem gstock_sharp_int : ∀ u : Finset (Fin 4), u.card ≤ 3 →
    subwordProd (StrictStock.letter (id : ℤ → ℤ)) ![10, 2, 5, 0] u
      ≠ wordProd (StrictStock.letter id) ![10, 2, 5, 0] := by
  decide

/-- **Four positions are sometimes necessary**, over any `P`: if the prices of a word are
`φ 10, φ 2, φ 5, φ 0` for a strictly monotone additive `φ : ℤ → P`, its summary is
`(φ 0, φ 10, φ 3)` and no three positions carry it.  So `β_{G_P}(M_P) = 4` whenever `P`
contains these prices. -/
theorem gstock_sharp {σ : Type} (pr : σ → P) (φ : ℤ →+ P) (hφ : StrictMono φ)
    (x : Fin 4 → σ) (hx : ∀ i, pr (x i) = φ (![10, 2, 5, 0] i)) :
    wordProd (gletter pr) x
        = ((⟨φ 0, φ 10, ((φ 3 : P) : WithBot P)⟩ : GSumm P) : GSummaries P)
      ∧ ∀ u : Finset (Fin 4), u.card ≤ 3 →
          subwordProd (gletter pr) x u ≠ wordProd (gletter pr) x := by
  have hlet : ∀ i, gletter pr (x i)
      = gstockHom φ hφ.monotone (StrictStock.letter id (![10, 2, 5, 0] i)) := fun i => by
    rw [← gstock_letter_eq_hom]
    simp only [gletter, hx, id]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [gstock_wordProd_hom _ pr id x _ hlet]
    have hz : wordProd (StrictStock.letter (id : ℤ → ℤ)) ![10, 2, 5, 0]
        = ((⟨0, 10, ((3 : ℤ) : WithBot ℤ)⟩ : StrictStock.SSumm) : StrictStock.Summaries) := by
      decide
    rw [hz, gstockHom_coe]
    rfl
  · rw [gstock_wordProd_hom _ pr id x _ hlet, gstock_subwordProd_hom _ pr id x _ hlet]
    exact fun h => gstock_sharp_int u hu (gstockHom_injective φ hφ h)

/-- **Sharpness for real prices** (`P = ℝ`): the price word `(10, 2, 5, 0)` has summary
`(0, 10, 3)` and needs all four positions. -/
theorem gstock_sharp_real :
    wordProd (gletter (id : ℝ → ℝ)) ![10, 2, 5, 0]
        = ((⟨0, 10, ((3 : ℝ) : WithBot ℝ)⟩ : GSumm ℝ) : GSummaries ℝ)
      ∧ ∀ u : Finset (Fin 4), u.card ≤ 3 →
          subwordProd (gletter (id : ℝ → ℝ)) ![10, 2, 5, 0] u
            ≠ wordProd (gletter id) ![10, 2, 5, 0] := by
  have h := gstock_sharp (id : ℝ → ℝ) (Int.castAddHom ℝ) (fun a b hab => by
    simp only [Int.coe_castAddHom]; exact_mod_cast hab) ![10, 2, 5, 0] (fun i => by
      fin_cases i <;> simp)
  simpa using h

end Sharp

end GenStock
end MonoidProduct
