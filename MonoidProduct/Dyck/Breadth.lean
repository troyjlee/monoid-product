import MonoidProduct.Dyck.Final
import MonoidProduct.Width.Breadth
import MonoidProduct.Aperiodic.RTrivial

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Product breadth of the Dyck monoid (`prop:dyck-breadth`), and the missing
clauses of `prop:dyck-monoid`

The paper's `prop:dyck-breadth`: for `k ≥ 1` and `G = {u, d}`,

  `β_G(M_k) = β_{M_k}(M_k) = max{2k, 3k-2}`

(`breadth_dyckLetter`, `breadth_dyckNF_id`, `breadth_dyck`).  The upper bound
`isBreadthBound_dyckNF` holds for an **arbitrary** letter map `σ → M_k`.

## Proof layout

Everything is phrased through lists: a core of a word is the same thing as a
sublist of its letter list with the same product (`dyck_exists_core_of_sublist`,
`dyck_exists_sublist_of_core`), so the monoid statement is
`dyck_exists_sublist_core`: every list over `M_k` has a same-product sublist
of length `≤ max (2k) (3k-2)`.

* **Walks.**  A list of live triples has a walk: `dyckLoW`, `dyckHiW`,
  `dyckSumE` (overall low, high, final height), boundary heights `dyckHt`,
  and per-factor extremes `dyckLowAt`, `dyckHighAt`.  The product formula
  `dyck_prod_map_live` identifies the ordered product with `dyckWalkNF`, the
  triple `(-low, high, sum)` (or zero if the span exceeds `k`) — the paper's
  "represent each factor by a word over `G` and concatenate".
* **Nonzero products** (`dyck_live_core`).  Take a shortest same-product
  sublist.  Deleting a closed segment (between equal boundary heights) keeps
  all other local extremes (`dyck_delete_closed`), so by minimality each
  closed segment loses every occurrence of the minimum or of the maximum.  The
  abstract counting lemma `DyckCombHyp.length_le` then gives
  `ℓ ≤ max (2s) (3s-2)` for span `s ≤ k`: every height occurs at most three
  times at factor boundaries (`card_fiber_le_three`), an extreme at most twice
  (`card_fiber_hi_le_two`), and if an extreme repeats, every height occurs at
  most twice and the other extreme once (`of_hi_repeat`).
* **Zero products** (`dyck_zero_core`): a core of at most `k + 1` factors.
  Instead of the paper's greedy truncation of positive intervening factors we
  induct on the list: with `x · L` zero and `L` live, the overflow is either
  a rise `a_x + e_x + high(L) > k` or a fall `b_x - e_x - low(L) > k`, and a
  walk rising (falling) to `D` has a sub-walk of at most `D` factors doing the
  same (`dyck_hiW_sublist`, `dyck_loW_sublist`).
* **Lower bounds** (`dyckMountain_core_card`, `dyckValley_core_card`, and the
  `_id` versions over the alphabet `M_k`): every core of `u^k d^k` has `2k`
  positions and, for `k ≥ 2`, every core of `u^(k-1) d^k u^(k-1)` has
  `3k - 2`, via `List.sublist_replicate_iff` and the walk parameters.

## `prop:dyck-monoid`, remaining clauses

* `not_isRTrivialMonoid_dyckNF`: `ud` and `u` have the same right ideal.
* `not_isLTrivial_dyckNF`: `du` and `u` have the same left ideal (stated
  concretely; the library has no `L`-trivial predicate).  The paper's text
  names the mirror pair "`du` and `d`"; that pair is another right-ideal
  witness (`du·d = d`, `d·u = du`), not a left one, so the left witness used
  here is the reversal `(du, u)` of `(ud, u)`.
* `card_dyckNF_cube_lower`, `card_dyckNF_theta`: `(k+1)³ < 3|M_k|` and
  `|M_k| ≤ (k+2)³`.
* `dyckNF_not_commutative`: `ud ≠ du` (`ex:dyck-breadth`).
-/

open scoped List

namespace MonoidProduct

/-! ## The boundary-height counting lemma -/

section Comb

/-- The hypotheses of the counting argument, abstracted from the monoid.
`H p` is the height at factor boundary `p ≤ ℓ`; `LA i`, `LB i` are the lowest
and highest heights reached inside factor `i < ℓ`; `lo ≤ 0 ≤ hi` are the
extremes of the whole walk.  `closed` is the minimality of the core: deleting
the factors `p, …, q-1` between two equal boundary heights must lose every
occurrence of the (nonzero) minimum or of the (nonzero) maximum. -/
structure DyckCombHyp (ℓ : ℕ) (H LA LB : ℕ → ℤ) (lo hi : ℤ) : Prop where
  h0 : H 0 = 0
  lo_nonpos : lo ≤ 0
  hi_nonneg : 0 ≤ hi
  la : ∀ i < ℓ, lo ≤ LA i ∧ LA i ≤ H (i + 1)
  lb : ∀ i < ℓ, H (i + 1) ≤ LB i ∧ LB i ≤ hi
  attA : lo < 0 → ∃ i < ℓ, LA i = lo
  attB : 0 < hi → ∃ i < ℓ, LB i = hi
  closed : ∀ p q, p < q → q ≤ ℓ → H p = H q →
    (lo < 0 ∧ ∀ i < ℓ, (i < p ∨ q ≤ i) → LA i ≠ lo)
      ∨ (0 < hi ∧ ∀ i < ℓ, (i < p ∨ q ≤ i) → LB i ≠ hi)

variable {ℓ : ℕ} {H LA LB : ℕ → ℤ} {lo hi : ℤ}

namespace DyckCombHyp

/-- The up/down mirror of the hypotheses. -/
lemma neg (hC : DyckCombHyp ℓ H LA LB lo hi) :
    DyckCombHyp ℓ (fun p => -H p) (fun i => -LB i) (fun i => -LA i) (-hi) (-lo) where
  h0 := by simp [hC.h0]
  lo_nonpos := by have := hC.hi_nonneg; omega
  hi_nonneg := by have := hC.lo_nonpos; omega
  la i hi' := by have := hC.lb i hi'; constructor <;> omega
  lb i hi' := by have := hC.la i hi'; constructor <;> omega
  attA h := by
    obtain ⟨i, hi', he⟩ := hC.attB (by omega)
    exact ⟨i, hi', by simp [he]⟩
  attB h := by
    obtain ⟨i, hi', he⟩ := hC.attA (by omega)
    exact ⟨i, hi', by simp [he]⟩
  closed p q hpq hq hH := by
    rcases hC.closed p q hpq hq (by simpa using hH) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨by omega, fun i hi' ho => by have := h2 i hi' ho; omega⟩
    · exact Or.inl ⟨by omega, fun i hi' ho => by have := h2 i hi' ho; omega⟩

variable (hC : DyckCombHyp ℓ H LA LB lo hi)
include hC

/-- Boundary heights lie between the extremes. -/
lemma mem_Icc {p : ℕ} (hp : p ≤ ℓ) : lo ≤ H p ∧ H p ≤ hi := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [hC.h0]; exact ⟨hC.lo_nonpos, hC.hi_nonneg⟩
  · have h1 := hC.la (p - 1) (by omega)
    have h2 := hC.lb (p - 1) (by omega)
    rw [Nat.sub_add_cancel hp0] at h1 h2
    exact ⟨h1.1.trans h1.2, h2.1.trans h2.2⟩

/-- Two disjoint segments cannot both lose the minimum. -/
lemma disjA {p q p' q' : ℕ}
    (h : lo < 0 ∧ ∀ i < ℓ, (i < p ∨ q ≤ i) → LA i ≠ lo)
    (h' : lo < 0 ∧ ∀ i < ℓ, (i < p' ∨ q' ≤ i) → LA i ≠ lo) (hqp : q ≤ p') :
    False := by
  obtain ⟨i, hi', he⟩ := hC.attA h.1
  by_cases hq : q ≤ i
  · exact h.2 i hi' (Or.inr hq) he
  · exact h'.2 i hi' (Or.inl (by omega)) he

/-- Two disjoint segments cannot both lose the maximum. -/
lemma disjB {p q p' q' : ℕ}
    (h : 0 < hi ∧ ∀ i < ℓ, (i < p ∨ q ≤ i) → LB i ≠ hi)
    (h' : 0 < hi ∧ ∀ i < ℓ, (i < p' ∨ q' ≤ i) → LB i ≠ hi) (hqp : q ≤ p') :
    False := by
  obtain ⟨i, hi', he⟩ := hC.attB h.1
  by_cases hq : q ≤ i
  · exact h.2 i hi' (Or.inr hq) he
  · exact h'.2 i hi' (Or.inl (by omega)) he

/-- A closed segment based at the top height cannot lose the top: it loses
the bottom. -/
lemma hiPair {p q : ℕ} (hpq : p < q) (hq : q ≤ ℓ) (hp : H p = hi) (hq' : H q = hi) :
    lo < 0 ∧ ∀ i < ℓ, (i < p ∨ q ≤ i) → LA i ≠ lo := by
  rcases hC.closed p q hpq hq (hp.trans hq'.symm) with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hp0 : p ≠ 0 := by rintro rfl; rw [hC.h0] at hp; omega
    have hb := hC.lb (p - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hb
    exact h2 (p - 1) (by omega) (Or.inl (by omega)) (by omega)

/-- Mirror of `hiPair`. -/
lemma loPair {p q : ℕ} (hpq : p < q) (hq : q ≤ ℓ) (hp : H p = lo) (hq' : H q = lo) :
    0 < hi ∧ ∀ i < ℓ, (i < p ∨ q ≤ i) → LB i ≠ hi := by
  rcases hC.closed p q hpq hq (hp.trans hq'.symm) with ⟨h1, h2⟩ | h
  · exfalso
    have hp0 : p ≠ 0 := by rintro rfl; rw [hC.h0] at hp; omega
    have ha := hC.la (p - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at ha
    exact h2 (p - 1) (by omega) (Or.inl (by omega)) (by omega)
  · exact h

end DyckCombHyp

/-- Strictly increasing enumeration of `m` elements of a finset of naturals. -/
lemma dyck_exists_strictMono (s : Finset ℕ) {m : ℕ} (h : m ≤ s.card) :
    ∃ f : Fin m → ℕ, StrictMono f ∧ ∀ i, f i ∈ s :=
  ⟨fun i => s.orderEmbOfFin rfl (Fin.castLE h i),
    fun _ _ hab => (s.orderEmbOfFin rfl).strictMono (by simpa using hab),
    fun _ => s.orderEmbOfFin_mem rfl _⟩

/-- The boundary indices at height `v`. -/
def dyckFiber (ℓ : ℕ) (H : ℕ → ℤ) (v : ℤ) : Finset ℕ :=
  (Finset.range (ℓ + 1)).filter fun p => H p = v

lemma mem_dyckFiber {p : ℕ} {v : ℤ} : p ∈ dyckFiber ℓ H v ↔ p ≤ ℓ ∧ H p = v := by
  simp [dyckFiber]

lemma dyckFiber_neg (v : ℤ) : dyckFiber ℓ (fun p => -H p) v = dyckFiber ℓ H (-v) := by
  ext p
  simp only [mem_dyckFiber]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

namespace DyckCombHyp

variable (hC : DyckCombHyp ℓ H LA LB lo hi)
include hC

/-- Every height occurs at most three times at the boundaries. -/
lemma card_fiber_le_three (v : ℤ) : (dyckFiber ℓ H v).card ≤ 3 := by
  by_contra hlt
  obtain ⟨f, hf, hmem⟩ := dyck_exists_strictMono (dyckFiber ℓ H v) (m := 4) (by omega)
  have m := fun i => mem_dyckFiber.mp (hmem i)
  have h01 := hf (show (0 : Fin 4) < 1 by decide)
  have h12 := hf (show (1 : Fin 4) < 2 by decide)
  have h23 := hf (show (2 : Fin 4) < 3 by decide)
  have c1 := hC.closed _ _ h01 (m 1).1 ((m 0).2.trans (m 1).2.symm)
  have c2 := hC.closed _ _ h12 (m 2).1 ((m 1).2.trans (m 2).2.symm)
  have c3 := hC.closed _ _ h23 (m 3).1 ((m 2).2.trans (m 3).2.symm)
  rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> rcases c3 with c3 | c3 <;>
    first
    | exact hC.disjA c1 c2 le_rfl
    | exact hC.disjA c1 c3 h12.le
    | exact hC.disjA c2 c3 le_rfl
    | exact hC.disjB c1 c2 le_rfl
    | exact hC.disjB c1 c3 h12.le
    | exact hC.disjB c2 c3 le_rfl

/-- The top height occurs at most twice. -/
lemma card_fiber_hi_le_two : (dyckFiber ℓ H hi).card ≤ 2 := by
  by_contra hlt
  obtain ⟨f, hf, hmem⟩ := dyck_exists_strictMono (dyckFiber ℓ H hi) (m := 3) (by omega)
  have m := fun i => mem_dyckFiber.mp (hmem i)
  have h01 := hf (show (0 : Fin 3) < 1 by decide)
  have h12 := hf (show (1 : Fin 3) < 2 by decide)
  exact hC.disjA (hC.hiPair h01 (m 1).1 (m 0).2 (m 1).2)
    (hC.hiPair h12 (m 2).1 (m 1).2 (m 2).2) le_rfl

/-- If the top height repeats, every height occurs at most twice and the
bottom height at most once. -/
lemma of_hi_repeat (h2 : 2 ≤ (dyckFiber ℓ H hi).card) :
    (∀ v, (dyckFiber ℓ H v).card ≤ 2) ∧ (dyckFiber ℓ H lo).card ≤ 1 := by
  obtain ⟨g, hg, hgm⟩ := dyck_exists_strictMono (dyckFiber ℓ H hi) h2
  have gm := fun i => mem_dyckFiber.mp (hgm i)
  have hpq := hg (show (0 : Fin 2) < 1 by decide)
  set p := g 0
  set q := g 1
  have hA := hC.hiPair hpq (gm 1).1 (gm 0).2 (gm 1).2
  obtain ⟨i₀, hi₀, hei₀⟩ := hC.attA hA.1
  have hi₀pq : p ≤ i₀ ∧ i₀ < q := by
    by_contra hn
    exact hA.2 i₀ hi₀ (by omega) hei₀
  -- `p, q ≥ 1` and the factors ending at `p, q` attain the top
  have topAt : ∀ r, r ≤ ℓ → H r = hi → 0 < hi → 1 ≤ r ∧ LB (r - 1) = hi := by
    intro r hr hHr hpos
    have hr0 : r ≠ 0 := by rintro rfl; rw [hC.h0] at hHr; omega
    have hb := hC.lb (r - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hb
    exact ⟨by omega, by omega⟩
  -- a segment that loses the top contains `[p, q)`
  have loseB_cover : ∀ r s, (0 < hi ∧ ∀ i < ℓ, (i < r ∨ s ≤ i) → LB i ≠ hi) →
      r < p ∧ q ≤ s := by
    intro r s hB
    obtain ⟨hp1, hpB⟩ := topAt p (gm 0).1 (gm 0).2 hB.1
    obtain ⟨hq1, hqB⟩ := topAt q (gm 1).1 (gm 1).2 hB.1
    constructor
    · by_contra hn; exact hB.2 (p - 1) (by omega) (Or.inl (by omega)) hpB
    · by_contra hn; exact hB.2 (q - 1) (by have := (gm 1).1; omega) (Or.inr (by omega)) hqB
  refine ⟨fun v => ?_, ?_⟩
  · by_contra hlt
    obtain ⟨f, hf, hmem⟩ := dyck_exists_strictMono (dyckFiber ℓ H v) (m := 3) (by omega)
    have m := fun i => mem_dyckFiber.mp (hmem i)
    have h01 := hf (show (0 : Fin 3) < 1 by decide)
    have h12 := hf (show (1 : Fin 3) < 2 by decide)
    have c1 := hC.closed _ _ h01 (m 1).1 ((m 0).2.trans (m 1).2.symm)
    have c2 := hC.closed _ _ h12 (m 2).1 ((m 1).2.trans (m 2).2.symm)
    rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
    · exact hC.disjA c1 c2 le_rfl
    · have := loseB_cover _ _ c2
      exact c1.2 i₀ hi₀ (Or.inr (by omega)) hei₀
    · have := loseB_cover _ _ c1
      exact c2.2 i₀ hi₀ (Or.inl (by omega)) hei₀
    · exact hC.disjB c1 c2 le_rfl
  · by_contra hlt
    obtain ⟨f, hf, hmem⟩ := dyck_exists_strictMono (dyckFiber ℓ H lo) (m := 2) (by omega)
    have m := fun i => mem_dyckFiber.mp (hmem i)
    have h01 := hf (show (0 : Fin 2) < 1 by decide)
    have hB := hC.loPair h01 (m 1).1 (m 0).2 (m 1).2
    have hcov := loseB_cover _ _ hB
    -- the factor ending at `f 0` attains the bottom, so it lies in `[p, q)`
    have hr0 : f 0 ≠ 0 := by
      intro h0; have := (m 0).2; rw [h0, hC.h0] at this; omega
    have ha := hC.la (f 0 - 1) (by have := (m 0).1; omega)
    rw [Nat.sub_add_cancel (by omega)] at ha
    exact hA.2 (f 0 - 1) (by have := (m 0).1; omega) (Or.inl (by omega))
      (by have := (m 0).2; omega)

/-- The counting bound: `ℓ ≤ max (2k) (3k - 2)` whenever the walk spans at
most `k ≥ 1`. -/
theorem length_le (k : ℕ) (hk : 1 ≤ k) (hspan : hi - lo ≤ k) :
    ℓ ≤ max (2 * k) (3 * k - 2) := by
  classical
  set Mid := (Finset.range (ℓ + 1)).filter fun p => lo < H p ∧ H p < hi
  have hcover : (Finset.range (ℓ + 1)).card
      ≤ (dyckFiber ℓ H lo).card + (dyckFiber ℓ H hi).card + Mid.card := by
    refine (Finset.card_le_card (t := dyckFiber ℓ H lo ∪ dyckFiber ℓ H hi ∪ Mid)
      ?_).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    intro p hp
    have hp' : p ≤ ℓ := by simpa [Nat.lt_succ_iff] using hp
    have := hC.mem_Icc hp'
    simp only [Finset.mem_union, mem_dyckFiber, Mid, Finset.mem_filter, Finset.mem_range]
    omega
  have hmid : ∀ c, (∀ v, (dyckFiber ℓ H v).card ≤ c) →
      Mid.card ≤ c * (hi - lo - 1).toNat := by
    intro c hc
    rw [← Int.card_Ioo]
    refine Finset.card_le_mul_card_image_of_maps_to (f := H) ?_ c ?_
    · intro p hp
      simp only [Mid, Finset.mem_filter] at hp
      exact Finset.mem_Ioo.mpr hp.2
    · intro v _
      refine le_trans (Finset.card_le_card ?_) (hc v)
      intro p hp
      simp only [Mid, Finset.mem_filter] at hp
      exact mem_dyckFiber.mpr ⟨by simpa [Nat.lt_succ_iff] using hp.1.1, hp.2⟩
  rw [Finset.card_range] at hcover
  have htn : (((hi - lo - 1).toNat : ℕ) : ℤ) = max (hi - lo - 1) 0 := by omega
  by_cases hrh : 2 ≤ (dyckFiber ℓ H hi).card
  · obtain ⟨hall, hlo1⟩ := hC.of_hi_repeat hrh
    have := hmid 2 hall
    have := hall hi
    omega
  by_cases hrl : 2 ≤ (dyckFiber ℓ H lo).card
  · obtain ⟨hall, hlo1⟩ := hC.neg.of_hi_repeat (by rwa [dyckFiber_neg, neg_neg])
    rw [dyckFiber_neg, neg_neg] at hlo1
    have := hmid 2 (fun v => by simpa [dyckFiber_neg] using hall (-v))
    have := hall (-lo)
    rw [dyckFiber_neg, neg_neg] at this
    omega
  · have := hmid 3 hC.card_fiber_le_three
    omega

end DyckCombHyp

end Comb

/-! ## Walks of normal-form factors -/

section Walk

variable {k : ℕ}

/-- The lowest height (relative to the start) of the walk of a list of
triples, the start included. -/
def dyckLoW : List (DyckTriple k) → ℤ
  | [] => 0
  | t :: T => min (-(t.a : ℤ)) (t.e + dyckLoW T)

/-- The highest height of the walk of a list of triples, the start included. -/
def dyckHiW : List (DyckTriple k) → ℤ
  | [] => 0
  | t :: T => max (t.b : ℤ) (t.e + dyckHiW T)

/-- The final height (total displacement) of a list of triples. -/
def dyckSumE : List (DyckTriple k) → ℤ
  | [] => 0
  | t :: T => t.e + dyckSumE T

/-- The height at the `i`-th factor boundary. -/
def dyckHt : List (DyckTriple k) → ℕ → ℤ
  | [], _ => 0
  | _ :: _, 0 => 0
  | t :: T, i + 1 => t.e + dyckHt T i

/-- The lowest height reached inside the `i`-th factor. -/
def dyckLowAt : List (DyckTriple k) → ℕ → ℤ
  | [], _ => 0
  | t :: _, 0 => -(t.a : ℤ)
  | t :: T, i + 1 => t.e + dyckLowAt T i

/-- The highest height reached inside the `i`-th factor. -/
def dyckHighAt : List (DyckTriple k) → ℕ → ℤ
  | [], _ => 0
  | t :: _, 0 => (t.b : ℤ)
  | t :: T, i + 1 => t.e + dyckHighAt T i

lemma dyckLoW_nonpos (T : List (DyckTriple k)) : dyckLoW T ≤ 0 := by
  cases T with
  | nil => simp [dyckLoW]
  | cons t T => simp only [dyckLoW]; omega

lemma dyckHiW_nonneg (T : List (DyckTriple k)) : 0 ≤ dyckHiW T := by
  cases T with
  | nil => simp [dyckHiW]
  | cons t T => simp only [dyckHiW]; omega

lemma dyckLoW_le_sumE (T : List (DyckTriple k)) : dyckLoW T ≤ dyckSumE T := by
  induction T with
  | nil => simp [dyckLoW, dyckSumE]
  | cons t T ih => simp only [dyckLoW, dyckSumE]; omega

lemma dyckSumE_le_hiW (T : List (DyckTriple k)) : dyckSumE T ≤ dyckHiW T := by
  induction T with
  | nil => simp [dyckHiW, dyckSumE]
  | cons t T ih => simp only [dyckHiW, dyckSumE]; omega

/-- The normal form of the walk: live with parameters `(-low, high, sum)`
when the span is at most `k`, zero otherwise. -/
def dyckWalkNF (T : List (DyckTriple k)) : DyckNF k :=
  if h : dyckHiW T - dyckLoW T ≤ k then
    .live
      { a := (-dyckLoW T).toNat
        b := (dyckHiW T).toNat
        e := dyckSumE T
        budget := by have := dyckLoW_nonpos T; have := dyckHiW_nonneg T; omega
        lower := by have := dyckLoW_nonpos T; have := dyckLoW_le_sumE T; omega
        upper := by have := dyckHiW_nonneg T; have := dyckSumE_le_hiW T; omega }
  else .zero

/-- **The product formula**: an ordered product of live factors is the
normal form of its walk (the composition rule of `prop:dyck-monoid`, iterated). -/
theorem dyck_prod_map_live (T : List (DyckTriple k)) :
    (T.map DyckNF.live).prod = dyckWalkNF T := by
  induction T with
  | nil =>
      rw [List.map_nil, List.prod_nil, DyckNF.one_def, dyckWalkNF,
        dif_pos (by simp [dyckHiW, dyckLoW])]
      rfl
  | cons t T ih =>
      rw [List.map_cons, List.prod_cons, ih]
      have ht1 := t.budget
      have ht2 := t.lower
      have ht3 := t.upper
      have l0 := dyckLoW_nonpos T
      have h0 := dyckHiW_nonneg T
      by_cases hT : dyckHiW T - dyckLoW T ≤ k
      · rw [dyckWalkNF, dif_pos hT, DyckNF.live_mul_live]
        unfold DyckTriple.comp
        split
        · rename_i h1
          dsimp only at h1
          have h2 : dyckHiW (t :: T) - dyckLoW (t :: T) ≤ k := by
            simp only [dyckHiW, dyckLoW]; omega
          rw [dyckWalkNF, dif_pos h2]
          congr 1
          apply DyckTriple.ext <;> simp only [DyckTriple.compT_a, DyckTriple.compT_b,
            DyckTriple.compT_e, dyckLoW, dyckHiW, dyckSumE] <;> omega
        · rename_i h1
          dsimp only at h1
          rw [dyckWalkNF, dif_neg (by simp only [dyckHiW, dyckLoW]; omega)]
      · rw [dyckWalkNF, dif_neg hT, DyckNF.mul_zero_eq, dyckWalkNF, dif_neg]
        simp only [dyckLoW, dyckHiW]
        omega

lemma dyckWalkNF_eq_zero {T : List (DyckTriple k)} (h : (k : ℤ) < dyckHiW T - dyckLoW T) :
    dyckWalkNF T = .zero := dif_neg (by omega)

lemma dyckWalkNF_ne_zero {T : List (DyckTriple k)} (h : dyckWalkNF T ≠ .zero) :
    dyckHiW T - dyckLoW T ≤ k := by
  by_contra hn
  exact h (dif_neg hn)

/-- Walks with the same low, high and final heights have the same normal form. -/
lemma dyckWalkNF_congr {T T' : List (DyckTriple k)} (h1 : dyckLoW T' = dyckLoW T)
    (h2 : dyckHiW T' = dyckHiW T) (h3 : dyckSumE T' = dyckSumE T) :
    dyckWalkNF T' = dyckWalkNF T := by
  unfold dyckWalkNF
  split_ifs with ha hb hb
  · congr 1
    apply DyckTriple.ext <;> simp only [h1, h2, h3]
  · exfalso; apply hb; omega
  · exfalso; apply ha; omega
  · rfl

/-- Conversely, equal live normal forms have equal walk parameters. -/
lemma dyckWalkNF_inj {T T' : List (DyckTriple k)} (h : dyckWalkNF T' = dyckWalkNF T)
    (hT : dyckHiW T - dyckLoW T ≤ k) :
    dyckLoW T' = dyckLoW T ∧ dyckHiW T' = dyckHiW T ∧ dyckSumE T' = dyckSumE T := by
  have hT' : dyckHiW T' - dyckLoW T' ≤ k := by
    apply dyckWalkNF_ne_zero
    rw [h, dyckWalkNF, dif_pos hT]
    simp
  rw [dyckWalkNF, dyckWalkNF, dif_pos hT, dif_pos hT'] at h
  have h' := DyckNF.live.inj h
  have ha := congrArg DyckTriple.a h'
  have hb := congrArg DyckTriple.b h'
  have he := congrArg DyckTriple.e h'
  simp only at ha hb he
  have := dyckLoW_nonpos T
  have := dyckLoW_nonpos T'
  have := dyckHiW_nonneg T
  have := dyckHiW_nonneg T'
  omega

/-! ### Boundary heights and local extremes -/

lemma dyckHt_zero (T : List (DyckTriple k)) : dyckHt T 0 = 0 := by
  cases T <;> rfl

lemma dyckHt_length (T : List (DyckTriple k)) : dyckHt T T.length = dyckSumE T := by
  induction T with
  | nil => rfl
  | cons t T ih => simp only [List.length_cons, dyckHt, dyckSumE, ih]

lemma dyckLowAt_bounds (T : List (DyckTriple k)) :
    ∀ i < T.length, dyckLoW T ≤ dyckLowAt T i ∧ dyckLowAt T i ≤ dyckHt T (i + 1) := by
  induction T with
  | nil => intro i hi; simp at hi
  | cons t T ih =>
      intro i hi
      have := t.lower
      cases i with
      | zero => simp only [dyckLowAt, dyckLoW, dyckHt, dyckHt_zero]; omega
      | succ i =>
          have := ih i (by simpa using hi)
          simp only [dyckLowAt, dyckLoW, dyckHt]
          omega

lemma dyckHighAt_bounds (T : List (DyckTriple k)) :
    ∀ i < T.length, dyckHt T (i + 1) ≤ dyckHighAt T i ∧ dyckHighAt T i ≤ dyckHiW T := by
  induction T with
  | nil => intro i hi; simp at hi
  | cons t T ih =>
      intro i hi
      have := t.upper
      cases i with
      | zero => simp only [dyckHighAt, dyckHiW, dyckHt, dyckHt_zero]; omega
      | succ i =>
          have := ih i (by simpa using hi)
          simp only [dyckHighAt, dyckHiW, dyckHt]
          omega

lemma dyckLoW_attained (T : List (DyckTriple k)) :
    dyckLoW T < 0 → ∃ i < T.length, dyckLowAt T i = dyckLoW T := by
  induction T with
  | nil => intro h; simp [dyckLoW] at h
  | cons t T ih =>
      intro h
      have := t.lower
      simp only [dyckLoW] at h ⊢
      by_cases hc : -(t.a : ℤ) ≤ t.e + dyckLoW T
      · exact ⟨0, by simp, by simp only [dyckLowAt]; omega⟩
      · obtain ⟨i, hi, he⟩ := ih (by omega)
        exact ⟨i + 1, by simpa using hi, by simp only [dyckLowAt]; omega⟩

lemma dyckHiW_attained (T : List (DyckTriple k)) :
    0 < dyckHiW T → ∃ i < T.length, dyckHighAt T i = dyckHiW T := by
  induction T with
  | nil => intro h; simp [dyckHiW] at h
  | cons t T ih =>
      intro h
      have := t.upper
      simp only [dyckHiW] at h ⊢
      by_cases hc : t.e + dyckHiW T ≤ (t.b : ℤ)
      · exact ⟨0, by simp, by simp only [dyckHighAt]; omega⟩
      · obtain ⟨i, hi, he⟩ := ih (by omega)
        exact ⟨i + 1, by simpa using hi, by simp only [dyckHighAt]; omega⟩

/-! ### Appending walks -/

lemma dyckSumE_append (A B : List (DyckTriple k)) :
    dyckSumE (A ++ B) = dyckSumE A + dyckSumE B := by
  induction A with
  | nil => simp [dyckSumE]
  | cons t A ih => simp only [List.cons_append, dyckSumE, ih]; ring

lemma dyckLoW_append (A B : List (DyckTriple k)) :
    dyckLoW (A ++ B) = min (dyckLoW A) (dyckSumE A + dyckLoW B) := by
  induction A with
  | nil => have := dyckLoW_nonpos B; simp only [List.nil_append, dyckLoW, dyckSumE]; omega
  | cons t A ih =>
      have := t.lower
      simp only [List.cons_append, dyckLoW, dyckSumE, ih]
      omega

lemma dyckHiW_append (A B : List (DyckTriple k)) :
    dyckHiW (A ++ B) = max (dyckHiW A) (dyckSumE A + dyckHiW B) := by
  induction A with
  | nil => have := dyckHiW_nonneg B; simp only [List.nil_append, dyckHiW, dyckSumE]; omega
  | cons t A ih =>
      have := t.upper
      simp only [List.cons_append, dyckHiW, dyckSumE, ih]
      omega

lemma dyckHt_append (A B : List (DyckTriple k)) (i : ℕ) :
    dyckHt (A ++ B) i
      = if i ≤ A.length then dyckHt A i else dyckSumE A + dyckHt B (i - A.length) := by
  induction A generalizing i with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.sub_zero, dyckSumE, zero_add]
      split_ifs with h
      · rw [Nat.le_zero.mp h, dyckHt_zero, dyckHt_zero]
      · rfl
  | cons t A ih =>
      cases i with
      | zero => simp [dyckHt]
      | succ i =>
          simp only [List.cons_append, dyckHt, ih, List.length_cons, dyckSumE,
            Nat.add_sub_add_right, Nat.add_le_add_iff_right]
          split_ifs <;> ring

lemma dyckLowAt_append (A B : List (DyckTriple k)) (i : ℕ) :
    dyckLowAt (A ++ B) i
      = if i < A.length then dyckLowAt A i else dyckSumE A + dyckLowAt B (i - A.length) := by
  induction A generalizing i with
  | nil => simp [dyckSumE]
  | cons t A ih =>
      cases i with
      | zero => simp [dyckLowAt]
      | succ i =>
          simp only [List.cons_append, dyckLowAt, ih, List.length_cons, dyckSumE,
            Nat.add_sub_add_right, Nat.add_lt_add_iff_right]
          split_ifs <;> ring

lemma dyckHighAt_append (A B : List (DyckTriple k)) (i : ℕ) :
    dyckHighAt (A ++ B) i
      = if i < A.length then dyckHighAt A i else dyckSumE A + dyckHighAt B (i - A.length) := by
  induction A generalizing i with
  | nil => simp [dyckSumE]
  | cons t A ih =>
      cases i with
      | zero => simp [dyckHighAt]
      | succ i =>
          simp only [List.cons_append, dyckHighAt, ih, List.length_cons, dyckSumE,
            Nat.add_sub_add_right, Nat.add_lt_add_iff_right]
          split_ifs <;> ring

end Walk

/-! ## Deleting a closed segment -/

section Delete

variable {k : ℕ}

/-- If every local low of `T'` is a local low of `T`, and a negative low of
`T` is attained in `T'`, the two walks have the same low. -/
lemma dyckLoW_eq_of {T T' : List (DyckTriple k)}
    (hsub : ∀ j < T'.length, ∃ i < T.length, dyckLowAt T' j = dyckLowAt T i)
    (hatt : dyckLoW T < 0 → ∃ j < T'.length, dyckLowAt T' j = dyckLoW T) :
    dyckLoW T' = dyckLoW T := by
  have h1 := dyckLoW_nonpos T
  have h2 := dyckLoW_nonpos T'
  apply le_antisymm
  · by_cases h : dyckLoW T < 0
    · obtain ⟨j, hj, he⟩ := hatt h
      exact ((dyckLowAt_bounds T' j hj).1).trans he.le
    · omega
  · by_cases h : dyckLoW T' < 0
    · obtain ⟨j, hj, he⟩ := dyckLoW_attained T' h
      obtain ⟨i, hi, he'⟩ := hsub j hj
      rw [← he, he']
      exact (dyckLowAt_bounds T i hi).1
    · omega

lemma dyckHiW_eq_of {T T' : List (DyckTriple k)}
    (hsub : ∀ j < T'.length, ∃ i < T.length, dyckHighAt T' j = dyckHighAt T i)
    (hatt : 0 < dyckHiW T → ∃ j < T'.length, dyckHighAt T' j = dyckHiW T) :
    dyckHiW T' = dyckHiW T := by
  have h1 := dyckHiW_nonneg T
  have h2 := dyckHiW_nonneg T'
  apply le_antisymm
  · by_cases h : 0 < dyckHiW T'
    · obtain ⟨j, hj, he⟩ := dyckHiW_attained T' h
      obtain ⟨i, hi, he'⟩ := hsub j hj
      rw [← he, he']
      exact (dyckHighAt_bounds T i hi).2
    · omega
  · by_cases h : 0 < dyckHiW T
    · obtain ⟨j, hj, he⟩ := hatt h
      exact he.symm.le.trans ((dyckHighAt_bounds T' j hj).2)
    · omega

/-- **Deleting a closed segment** (factors `p, …, q-1` between two equal
boundary heights) leaves every other local extreme in place; if some
occurrence of each nonzero extreme survives, the product is unchanged. -/
lemma dyck_delete_closed (T : List (DyckTriple k)) {p q : ℕ} (hpq : p < q)
    (hq : q ≤ T.length) (hH : dyckHt T p = dyckHt T q)
    (hA : dyckLoW T = 0 ∨ ∃ i < T.length, (i < p ∨ q ≤ i) ∧ dyckLowAt T i = dyckLoW T)
    (hB : dyckHiW T = 0 ∨ ∃ i < T.length, (i < p ∨ q ≤ i) ∧ dyckHighAt T i = dyckHiW T) :
    ∃ T', T' <+ T ∧ T'.length < T.length ∧ dyckWalkNF T' = dyckWalkNF T := by
  obtain ⟨A, B, C, rfl, hAl, hBl⟩ :
      ∃ A B C : List (DyckTriple k), T = A ++ (B ++ C) ∧ A.length = p ∧ B.length = q - p :=
    ⟨T.take p, (T.drop p).take (q - p), (T.drop p).drop (q - p),
      by rw [List.take_append_drop, List.take_append_drop],
      by simp; omega, by simp; omega⟩
  have hlen : (A ++ (B ++ C)).length = A.length + B.length + C.length := by
    simp only [List.length_append]; ring
  -- the deleted block has zero displacement
  have hsB : dyckSumE B = 0 := by
    have e1 : dyckHt (A ++ (B ++ C)) p = dyckSumE A := by
      rw [dyckHt_append, if_pos (by omega), ← hAl, dyckHt_length]
    have e2 : dyckHt (A ++ (B ++ C)) q = dyckSumE A + dyckSumE B := by
      rw [dyckHt_append, if_neg (by omega), dyckHt_append, if_pos (by omega),
        show q - A.length = B.length by omega, dyckHt_length]
    omega
  refine ⟨A ++ C, (List.sublist_append_right B C).append_left A, by
    simp only [List.length_append] at hlen ⊢; omega, ?_⟩
  have hlowT : ∀ i, dyckLowAt (A ++ (B ++ C)) i = if i < A.length then dyckLowAt A i
      else if i - A.length < B.length then dyckSumE A + dyckLowAt B (i - A.length)
      else dyckSumE A + dyckLowAt C (i - A.length - B.length) := by
    intro i
    rw [dyckLowAt_append, dyckLowAt_append, hsB]
    split_ifs <;> ring
  have hhighT : ∀ i, dyckHighAt (A ++ (B ++ C)) i = if i < A.length then dyckHighAt A i
      else if i - A.length < B.length then dyckSumE A + dyckHighAt B (i - A.length)
      else dyckSumE A + dyckHighAt C (i - A.length - B.length) := by
    intro i
    rw [dyckHighAt_append, dyckHighAt_append, hsB]
    split_ifs <;> ring
  apply dyckWalkNF_congr
  · apply dyckLoW_eq_of
    · intro j hj
      simp only [List.length_append] at hj
      by_cases hjA : j < A.length
      · exact ⟨j, by omega, by rw [dyckLowAt_append, hlowT, if_pos hjA, if_pos hjA]⟩
      · refine ⟨j + B.length, by omega, ?_⟩
        rw [dyckLowAt_append, hlowT, if_neg hjA, if_neg (by omega), if_neg (by omega)]
        congr 2; omega
    · intro hneg
      rcases hA with h0 | ⟨i, hi, ho, he⟩
      · omega
      rcases ho with ho | ho
      · refine ⟨i, by simp only [List.length_append]; omega, ?_⟩
        rw [← he, dyckLowAt_append, hlowT, if_pos (by omega), if_pos (by omega)]
      · refine ⟨i - B.length, by simp only [List.length_append]; omega, ?_⟩
        rw [← he, dyckLowAt_append, hlowT, if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]
        congr 2; omega
  · apply dyckHiW_eq_of
    · intro j hj
      simp only [List.length_append] at hj
      by_cases hjA : j < A.length
      · exact ⟨j, by omega, by rw [dyckHighAt_append, hhighT, if_pos hjA, if_pos hjA]⟩
      · refine ⟨j + B.length, by omega, ?_⟩
        rw [dyckHighAt_append, hhighT, if_neg hjA, if_neg (by omega), if_neg (by omega)]
        congr 2; omega
    · intro hpos
      rcases hB with h0 | ⟨i, hi, ho, he⟩
      · omega
      rcases ho with ho | ho
      · refine ⟨i, by simp only [List.length_append]; omega, ?_⟩
        rw [← he, dyckHighAt_append, hhighT, if_pos (by omega), if_pos (by omega)]
      · refine ⟨i - B.length, by simp only [List.length_append]; omega, ?_⟩
        rw [← he, dyckHighAt_append, hhighT, if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]
        congr 2; omega
  · rw [dyckSumE_append, dyckSumE_append, dyckSumE_append, hsB, zero_add]

end Delete

/-! ## Short sublists with the same product -/

section Sublists

variable {k : ℕ}

/-- A list with a nonzero product consists of live factors. -/
lemma dyck_exists_map_live (Q : List (DyckNF k)) (hQ : Q.prod ≠ .zero) :
    ∃ T : List (DyckTriple k), Q = T.map DyckNF.live := by
  induction Q with
  | nil => exact ⟨[], rfl⟩
  | cons x Q ih =>
      cases x with
      | zero => exact absurd (by rw [List.prod_cons, DyckNF.zero_mul_eq]) hQ
      | live t =>
          have hQ' : Q.prod ≠ .zero := fun h => hQ (by rw [List.prod_cons, h,
            DyckNF.mul_zero_eq])
          obtain ⟨T, rfl⟩ := ih hQ'
          exact ⟨t :: T, rfl⟩

/-- A walk rising to height `D` has a sub-walk of at most `D` factors that
still rises to `D`. -/
theorem dyck_hiW_sublist (T : List (DyckTriple k)) (D : ℕ) (hD : (D : ℤ) ≤ dyckHiW T) :
    ∃ R, R <+ T ∧ (D : ℤ) ≤ dyckHiW R ∧ R.length ≤ D := by
  induction T generalizing D with
  | nil => exact ⟨[], List.Sublist.slnil, hD, by simp [dyckHiW] at hD; simp [hD]⟩
  | cons t T ih =>
      have := t.upper
      have := t.lower
      simp only [dyckHiW] at hD
      by_cases hb : (D : ℤ) ≤ t.b
      · rcases Nat.eq_zero_or_pos D with rfl | hD0
        · exact ⟨[], List.nil_sublist _, by simp [dyckHiW], by simp⟩
        · refine ⟨[t], (List.nil_sublist T).cons_cons t, ?_, by simp; omega⟩
          simp only [dyckHiW]
          omega
      · by_cases he : t.e ≤ 0
        · obtain ⟨R, hR, h1, h2⟩ := ih D (by omega)
          exact ⟨R, hR.cons t, h1, h2⟩
        · obtain ⟨R, hR, h1, h2⟩ := ih ((D : ℤ) - t.e).toNat (by omega)
          refine ⟨t :: R, hR.cons_cons t, ?_, ?_⟩
          · simp only [dyckHiW]; omega
          · simp only [List.length_cons]; omega

/-- A walk falling to depth `D` has a sub-walk of at most `D` factors that
still falls to `D`. -/
theorem dyck_loW_sublist (T : List (DyckTriple k)) (D : ℕ) (hD : (D : ℤ) ≤ -dyckLoW T) :
    ∃ R, R <+ T ∧ (D : ℤ) ≤ -dyckLoW R ∧ R.length ≤ D := by
  induction T generalizing D with
  | nil => exact ⟨[], List.Sublist.slnil, hD, by simp [dyckLoW] at hD; simp [hD]⟩
  | cons t T ih =>
      have := t.upper
      have := t.lower
      simp only [dyckLoW] at hD
      by_cases hb : (D : ℤ) ≤ t.a
      · rcases Nat.eq_zero_or_pos D with rfl | hD0
        · exact ⟨[], List.nil_sublist _, by simp [dyckLoW], by simp⟩
        · refine ⟨[t], (List.nil_sublist T).cons_cons t, ?_, by simp; omega⟩
          simp only [dyckLoW]
          omega
      · by_cases he : 0 ≤ t.e
        · obtain ⟨R, hR, h1, h2⟩ := ih D (by omega)
          exact ⟨R, hR.cons t, h1, h2⟩
        · obtain ⟨R, hR, h1, h2⟩ := ih ((D : ℤ) + t.e).toNat (by omega)
          refine ⟨t :: R, hR.cons_cons t, ?_, ?_⟩
          · simp only [dyckLoW]; omega
          · simp only [List.length_cons]; omega

/-- **Zero products have short cores** (the last paragraph of the proof of
`prop:dyck-breadth`): every list with product zero has a sublist of at most
`k + 1` factors with product zero. -/
theorem dyck_zero_core (L : List (DyckNF k)) (h : L.prod = .zero) :
    ∃ Q, Q <+ L ∧ Q.prod = .zero ∧ Q.length ≤ k + 1 := by
  induction L with
  | nil => simp [DyckNF.one_def] at h
  | cons x L ih =>
      by_cases hL : L.prod = .zero
      · obtain ⟨Q, h1, h2, h3⟩ := ih hL
        exact ⟨Q, h1.cons x, h2, h3⟩
      cases x with
      | zero => exact ⟨[.zero], (List.nil_sublist L).cons_cons _, by simp, by simp⟩
      | live t =>
          obtain ⟨T, rfl⟩ := dyck_exists_map_live L hL
          rw [dyck_prod_map_live] at hL
          have hspan := dyckWalkNF_ne_zero hL
          have hz : (k : ℤ) < dyckHiW (t :: T) - dyckLoW (t :: T) := by
            have h' : ((t :: T).map DyckNF.live).prod = .zero := h
            rw [dyck_prod_map_live] at h'
            by_contra hn
            rw [dyckWalkNF, dif_pos (by omega)] at h'
            simp at h'
          simp only [dyckHiW, dyckLoW] at hz
          have := t.budget
          have := t.lower
          have := t.upper
          have := dyckLoW_nonpos T
          have := dyckHiW_nonneg T
          by_cases hcase : (k : ℤ) < t.a + t.e + dyckHiW T
          · obtain ⟨R, hR, h1, h2⟩ :=
              dyck_hiW_sublist T ((k : ℤ) + 1 - (t.a + t.e)).toNat (by omega)
            have := dyckLoW_nonpos R
            by_cases hc : 1 ≤ (t.a : ℤ) + t.e
            · refine ⟨(t :: R).map DyckNF.live, (hR.map _).cons_cons _, ?_, ?_⟩
              · rw [dyck_prod_map_live]
                apply dyckWalkNF_eq_zero
                simp only [dyckHiW, dyckLoW]
                omega
              · simp only [List.length_map, List.length_cons]; omega
            · refine ⟨R.map DyckNF.live, (hR.map _).cons _, ?_, ?_⟩
              · rw [dyck_prod_map_live]
                apply dyckWalkNF_eq_zero
                omega
              · simp only [List.length_map]; omega
          · obtain ⟨R, hR, h1, h2⟩ :=
              dyck_loW_sublist T ((k : ℤ) + 1 - (t.b - t.e)).toNat (by omega)
            have := dyckHiW_nonneg R
            by_cases hc : 1 ≤ (t.b : ℤ) - t.e
            · refine ⟨(t :: R).map DyckNF.live, (hR.map _).cons_cons _, ?_, ?_⟩
              · rw [dyck_prod_map_live]
                apply dyckWalkNF_eq_zero
                simp only [dyckHiW, dyckLoW]
                omega
              · simp only [List.length_map, List.length_cons]; omega
            · refine ⟨R.map DyckNF.live, (hR.map _).cons _, ?_, ?_⟩
              · rw [dyck_prod_map_live]
                apply dyckWalkNF_eq_zero
                omega
              · simp only [List.length_map]; omega

/-- **Nonzero products have cores of size at most `max (2k) (3k-2)`**: a
shortest sublist with the same product admits no deletable closed segment,
and the counting lemma bounds its length. -/
theorem dyck_live_core (hk : 1 ≤ k) (L : List (DyckNF k)) (hL : L.prod ≠ .zero) :
    ∃ Q, Q <+ L ∧ Q.prod = L.prod ∧ Q.length ≤ max (2 * k) (3 * k - 2) := by
  classical
  have hex : ∃ m, ∃ Q, Q <+ L ∧ Q.prod = L.prod ∧ Q.length = m :=
    ⟨_, L, List.Sublist.refl _, rfl, rfl⟩
  obtain ⟨Q, hQL, hQp, hQm⟩ := Nat.find_spec hex
  refine ⟨Q, hQL, hQp, ?_⟩
  have hQ0 : Q.prod ≠ .zero := hQp ▸ hL
  obtain ⟨T, rfl⟩ := dyck_exists_map_live Q hQ0
  rw [dyck_prod_map_live] at hQ0
  have hspan := dyckWalkNF_ne_zero hQ0
  rw [List.length_map]
  refine DyckCombHyp.length_le (H := dyckHt T) (LA := dyckLowAt T) (LB := dyckHighAt T)
    ⟨dyckHt_zero T, dyckLoW_nonpos T, dyckHiW_nonneg T,
      fun i hi => ⟨(dyckLowAt_bounds T i hi).1, (dyckLowAt_bounds T i hi).2⟩,
      fun i hi => ⟨(dyckHighAt_bounds T i hi).1, (dyckHighAt_bounds T i hi).2⟩,
      dyckLoW_attained T, dyckHiW_attained T, ?_⟩ k hk hspan
  intro p q hpq hq hH
  by_contra hn
  rw [not_or] at hn
  have hA : dyckLoW T = 0
      ∨ ∃ i < T.length, (i < p ∨ q ≤ i) ∧ dyckLowAt T i = dyckLoW T := by
    by_cases h0 : dyckLoW T < 0
    · right
      by_contra h'
      exact hn.1 ⟨h0, fun i hi ho he => h' ⟨i, hi, ho, he⟩⟩
    · left; have := dyckLoW_nonpos T; omega
  have hB : dyckHiW T = 0
      ∨ ∃ i < T.length, (i < p ∨ q ≤ i) ∧ dyckHighAt T i = dyckHiW T := by
    by_cases h0 : 0 < dyckHiW T
    · right
      by_contra h'
      exact hn.2 ⟨h0, fun i hi ho he => h' ⟨i, hi, ho, he⟩⟩
    · left; have := dyckHiW_nonneg T; omega
  obtain ⟨T', hsub, hlen, heq⟩ := dyck_delete_closed T hpq hq hH hA hB
  have hmin := Nat.find_min' hex ⟨T'.map DyckNF.live, (hsub.map _).trans hQL,
    by rw [dyck_prod_map_live, heq, ← dyck_prod_map_live, hQp], rfl⟩
  rw [List.length_map] at hmin hQm
  omega

/-- **Every list over `M_k` has a core of at most `max (2k) (3k-2)` factors.** -/
theorem dyck_exists_sublist_core (hk : 1 ≤ k) (L : List (DyckNF k)) :
    ∃ Q, Q <+ L ∧ Q.prod = L.prod ∧ Q.length ≤ max (2 * k) (3 * k - 2) := by
  by_cases h : L.prod = .zero
  · obtain ⟨Q, h1, h2, h3⟩ := dyck_zero_core L h
    exact ⟨Q, h1, h2.trans h.symm, by omega⟩
  · exact dyck_live_core hk L h

end Sublists

/-! ## From sublists to cores -/

section Bridge

variable {σ : Type} {M : Type} [Monoid M]

lemma dyck_subwordProd_succ (letter : σ → M) {n : ℕ} (x : Fin (n + 1) → σ)
    (u : Finset (Fin (n + 1))) :
    subwordProd letter x u
      = (if (0 : Fin (n + 1)) ∈ u then letter (x 0) else 1)
        * subwordProd letter (fun i => x i.succ) (Finset.univ.filter fun i => i.succ ∈ u) := by
  unfold subwordProd
  rw [List.ofFn_succ, List.prod_cons]
  congr 2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A sublist of the letter list is the subword of a position set of the
same size. -/
theorem dyck_exists_core_of_sublist (letter : σ → M) {n : ℕ} (x : Fin n → σ) (Q : List M)
    (hQ : Q <+ List.ofFn fun i => letter (x i)) :
    ∃ u : Finset (Fin n), u.card = Q.length ∧ subwordProd letter x u = Q.prod := by
  induction n generalizing Q with
  | zero =>
      rw [List.ofFn_zero, List.sublist_nil] at hQ
      subst hQ
      exact ⟨∅, rfl, subwordProd_empty _ _⟩
  | succ n ih =>
      rw [List.ofFn_succ] at hQ
      rcases List.sublist_cons_iff.mp hQ with hQ | ⟨r, rfl, hr⟩
      · obtain ⟨u, hu, hp⟩ := ih (fun i => x i.succ) Q hQ
        refine ⟨u.map (Fin.succEmb n), by rw [Finset.card_map, hu], ?_⟩
        rw [dyck_subwordProd_succ, if_neg (by simp [Fin.succ_ne_zero]), one_mul]
        have : (Finset.univ.filter fun i : Fin n => i.succ ∈ u.map (Fin.succEmb n)) = u := by
          ext i; simp
        rw [this, hp]
      · obtain ⟨u, hu, hp⟩ := ih (fun i => x i.succ) r hr
        refine ⟨insert 0 (u.map (Fin.succEmb n)), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [Fin.succ_ne_zero]), Finset.card_map, hu,
            List.length_cons]
        · rw [dyck_subwordProd_succ, if_pos (Finset.mem_insert_self _ _)]
          have : (Finset.univ.filter fun i : Fin n =>
              i.succ ∈ insert 0 (u.map (Fin.succEmb n))) = u := by
            ext i; simp [Fin.succ_ne_zero]
          rw [this, hp, List.prod_cons]

/-- The subword of a position set is a sublist of the same size. -/
theorem dyck_exists_sublist_of_core (letter : σ → M) {n : ℕ} (x : Fin n → σ)
    (u : Finset (Fin n)) :
    ∃ Q, Q <+ (List.ofFn fun i => letter (x i)) ∧ Q.length = u.card
      ∧ Q.prod = subwordProd letter x u := by
  induction n with
  | zero =>
      obtain rfl := Finset.eq_empty_of_isEmpty u
      exact ⟨[], List.nil_sublist _, rfl, (subwordProd_empty _ _).symm⟩
  | succ n ih =>
      obtain ⟨Q, hQ, hl, hp⟩ := ih (fun i => x i.succ)
        (Finset.univ.filter fun i : Fin n => i.succ ∈ u)
      have hc := Fin.card_filter_univ_succ (fun i => i ∈ u)
      rw [Finset.filter_univ_mem] at hc
      rw [List.ofFn_succ]
      by_cases h0 : (0 : Fin (n + 1)) ∈ u
      · refine ⟨letter (x 0) :: Q, hQ.cons_cons _, ?_, ?_⟩
        · rw [hc, if_pos h0, List.length_cons, hl]
        · rw [dyck_subwordProd_succ, if_pos h0, List.prod_cons, hp]
      · refine ⟨Q, hQ.cons _, ?_, ?_⟩
        · rw [hc, if_neg h0, hl]
        · rw [dyck_subwordProd_succ, if_neg h0, one_mul, hp]

/-- A uniform bound on short sublists with the same product is a breadth
bound, for any letter map. -/
theorem dyck_isBreadthBound_of_sublist {letter : σ → M} {b : ℕ}
    (h : ∀ L : List M, ∃ Q, Q <+ L ∧ Q.prod = L.prod ∧ Q.length ≤ b) :
    IsBreadthBound letter b := by
  intro n x
  obtain ⟨Q, h1, h2, h3⟩ := h (List.ofFn fun i => letter (x i))
  obtain ⟨u, hu, hp⟩ := dyck_exists_core_of_sublist letter x Q h1
  refine ⟨u, hu ▸ h3, ?_⟩
  rw [IsCore, hp, h2, wordProd, orderedProd_eq_prod_ofFn]

lemma dyck_ofFn_get_map (letter : σ → M) (w : List σ) :
    (List.ofFn fun i : Fin w.length => letter (w.get i)) = w.map letter := by
  conv_rhs => rw [← List.ofFn_get w]
  rw [List.map_ofFn]
  rfl

/-- If every sublist of `w.map letter` with the same product has at least
`c` letters, every core of the word `w` has at least `c` positions. -/
theorem dyck_card_le_of_isCore {letter : σ → M} (w : List σ) {c : ℕ}
    (h : ∀ Q, Q <+ w.map letter → Q.prod = (w.map letter).prod → c ≤ Q.length)
    (u : Finset (Fin w.length)) (hu : IsCore letter (fun i => w.get i) u) : c ≤ u.card := by
  obtain ⟨Q, h1, h2, h3⟩ := dyck_exists_sublist_of_core letter (fun i => w.get i) u
  rw [dyck_ofFn_get_map] at h1
  have := h Q h1 (by
    rw [h3, hu, wordProd, orderedProd_eq_prod_ofFn, dyck_ofFn_get_map])
  omega

end Bridge

/-! ## The breadth of the Dyck monoid -/

section Breadth

variable {k : ℕ}

/-- **Upper bound of `prop:dyck-breadth`, for arbitrary inputs**: for
`k ≥ 1` and *any* letter map into `M_k`, every word has a core of at most
`max (2k) (3k-2)` positions. -/
theorem isBreadthBound_dyckNF (hk : 1 ≤ k) {σ : Type} (letter : σ → DyckNF k) :
    IsBreadthBound letter (max (2 * k) (3 * k - 2)) :=
  dyck_isBreadthBound_of_sublist (dyck_exists_sublist_core hk)

lemma dyckWalk_replicate_up (hk : 1 ≤ k) (n : ℕ) :
    dyckLoW (List.replicate n (upT k hk)) = 0 ∧ dyckHiW (List.replicate n (upT k hk)) = n
      ∧ dyckSumE (List.replicate n (upT k hk)) = n := by
  induction n with
  | zero => simp [dyckLoW, dyckHiW, dyckSumE]
  | succ n ih =>
      simp only [List.replicate_succ, dyckLoW, dyckHiW, dyckSumE, ih]
      simp only [upT]
      omega

lemma dyckWalk_replicate_down (hk : 1 ≤ k) (n : ℕ) :
    dyckLoW (List.replicate n (downT k hk)) = -n ∧ dyckHiW (List.replicate n (downT k hk)) = 0
      ∧ dyckSumE (List.replicate n (downT k hk)) = -n := by
  induction n with
  | zero => simp [dyckLoW, dyckHiW, dyckSumE]
  | succ n ih =>
      simp only [List.replicate_succ, dyckLoW, dyckHiW, dyckSumE, ih]
      simp only [downT]
      omega

lemma dyckLetter_false_eq (hk : 1 ≤ k) : dyckLetter k false = .live (upT k hk) := by
  rw [dyckLetter_false, dif_pos hk]

lemma dyckLetter_true_eq (hk : 1 ≤ k) : dyckLetter k true = .live (downT k hk) := by
  rw [dyckLetter_true, dif_pos hk]

lemma dyck_replicate_live (n : ℕ) (t : DyckTriple k) :
    List.replicate n (DyckNF.live t) = (List.replicate n t).map DyckNF.live :=
  (List.map_replicate ..).symm

/-- The word `u^k d^k` (`false` = up). -/
def dyckMountainWord (k : ℕ) : List Bool :=
  List.replicate k false ++ List.replicate k true

/-- The word `u^(k-1) d^k u^(k-1)`. -/
def dyckValleyWord (k : ℕ) : List Bool :=
  List.replicate (k - 1) false ++ List.replicate k true ++ List.replicate (k - 1) false

/-- Every same-product sublist of `u^k d^k` keeps all `2k` letters. -/
theorem dyckMountain_sublist (hk : 1 ≤ k) (Q : List (DyckNF k))
    (hQ : Q <+ (dyckMountainWord k).map (dyckLetter k))
    (hp : Q.prod = ((dyckMountainWord k).map (dyckLetter k)).prod) : 2 * k ≤ Q.length := by
  rw [dyckMountainWord, List.map_append, List.map_replicate, List.map_replicate,
    dyckLetter_false_eq hk, dyckLetter_true_eq hk] at hQ hp
  obtain ⟨Q1, Q2, rfl, h1, h2⟩ := List.sublist_append_iff.mp hQ
  obtain ⟨i, hi, rfl⟩ := List.sublist_replicate_iff.mp h1
  obtain ⟨j, hj, rfl⟩ := List.sublist_replicate_iff.mp h2
  simp only [dyck_replicate_live, ← List.map_append, dyck_prod_map_live] at hp
  obtain ⟨u1, u2, u3⟩ := dyckWalk_replicate_up hk k
  obtain ⟨d1, d2, d3⟩ := dyckWalk_replicate_down hk k
  obtain ⟨u1', u2', u3'⟩ := dyckWalk_replicate_up hk i
  obtain ⟨d1', d2', d3'⟩ := dyckWalk_replicate_down hk j
  obtain ⟨e1, e2, e3⟩ := dyckWalkNF_inj hp (by
    rw [dyckHiW_append, dyckLoW_append, u1, u2, u3, d1, d2]; omega)
  rw [dyckLoW_append, dyckLoW_append, dyckHiW_append, dyckHiW_append, dyckSumE_append,
    dyckSumE_append, u1, u2, u3, d1, d2, d3, u1', u2', u3', d1', d2', d3'] at *
  simp only [List.length_append, List.length_replicate]
  omega

/-- Every same-product sublist of `u^(k-1) d^k u^(k-1)` keeps all `3k-2`
letters. -/
theorem dyckValley_sublist (hk : 2 ≤ k) (Q : List (DyckNF k))
    (hQ : Q <+ (dyckValleyWord k).map (dyckLetter k))
    (hp : Q.prod = ((dyckValleyWord k).map (dyckLetter k)).prod) : 3 * k - 2 ≤ Q.length := by
  have hk1 : 1 ≤ k := by omega
  rw [dyckValleyWord, List.map_append, List.map_append, List.map_replicate, List.map_replicate,
    dyckLetter_false_eq hk1, dyckLetter_true_eq hk1] at hQ hp
  obtain ⟨Q12, Q3, rfl, h12, h3⟩ := List.sublist_append_iff.mp hQ
  obtain ⟨Q1, Q2, rfl, h1, h2⟩ := List.sublist_append_iff.mp h12
  obtain ⟨i, hi, rfl⟩ := List.sublist_replicate_iff.mp h1
  obtain ⟨j, hj, rfl⟩ := List.sublist_replicate_iff.mp h2
  obtain ⟨l, hl, rfl⟩ := List.sublist_replicate_iff.mp h3
  simp only [dyck_replicate_live, ← List.map_append, dyck_prod_map_live] at hp
  obtain ⟨u1, u2, u3⟩ := dyckWalk_replicate_up hk1 (k - 1)
  obtain ⟨d1, d2, d3⟩ := dyckWalk_replicate_down hk1 k
  obtain ⟨u1', u2', u3'⟩ := dyckWalk_replicate_up hk1 i
  obtain ⟨d1', d2', d3'⟩ := dyckWalk_replicate_down hk1 j
  obtain ⟨v1', v2', v3'⟩ := dyckWalk_replicate_up hk1 l
  obtain ⟨e1, e2, e3⟩ := dyckWalkNF_inj hp (by
    rw [dyckHiW_append, dyckLoW_append, dyckHiW_append, dyckLoW_append, dyckSumE_append,
      u1, u2, u3, d1, d2, d3]
    omega)
  rw [dyckLoW_append, dyckLoW_append, dyckLoW_append, dyckLoW_append, dyckHiW_append,
    dyckHiW_append, dyckHiW_append, dyckHiW_append, dyckSumE_append, dyckSumE_append,
    dyckSumE_append, dyckSumE_append, u1, u2, u3, d1, d2, d3, u1', u2', u3', d1', d2', d3',
    v1', v2', v3'] at *
  simp only [List.length_append, List.length_replicate]
  omega

/-- **Lower-bound witness 1**: every core of `u^k d^k` has all `2k`
positions. -/
theorem dyckMountain_core_card (hk : 1 ≤ k) (u : Finset (Fin (dyckMountainWord k).length))
    (hu : IsCore (dyckLetter k) (fun i => (dyckMountainWord k).get i) u) : 2 * k ≤ u.card :=
  dyck_card_le_of_isCore _ (dyckMountain_sublist hk) u hu

/-- **Lower-bound witness 2** (`k ≥ 2`): every core of `u^(k-1) d^k u^(k-1)`
has all `3k-2` positions. -/
theorem dyckValley_core_card (hk : 2 ≤ k) (u : Finset (Fin (dyckValleyWord k).length))
    (hu : IsCore (dyckLetter k) (fun i => (dyckValleyWord k).get i) u) : 3 * k - 2 ≤ u.card :=
  dyck_card_le_of_isCore _ (dyckValley_sublist hk) u hu

/-- The same two witnesses read as words over the full alphabet `M_k`. -/
theorem dyckMountain_core_card_id (hk : 1 ≤ k)
    (u : Finset (Fin ((dyckMountainWord k).map (dyckLetter k)).length))
    (hu : IsCore (id : DyckNF k → DyckNF k)
      (fun i => ((dyckMountainWord k).map (dyckLetter k)).get i) u) : 2 * k ≤ u.card :=
  dyck_card_le_of_isCore (letter := id) _ (fun Q hQ hp =>
    dyckMountain_sublist hk Q (by simpa using hQ) (by simpa using hp)) u hu

theorem dyckValley_core_card_id (hk : 2 ≤ k)
    (u : Finset (Fin ((dyckValleyWord k).map (dyckLetter k)).length))
    (hu : IsCore (id : DyckNF k → DyckNF k)
      (fun i => ((dyckValleyWord k).map (dyckLetter k)).get i) u) : 3 * k - 2 ≤ u.card :=
  dyck_card_le_of_isCore (letter := id) _ (fun Q hQ hp =>
    dyckValley_sublist hk Q (by simpa using hQ) (by simpa using hp)) u hu

/-- **`prop:dyck-breadth`, generators**: `β_G(M_k) = max (2k) (3k-2)` for
`G = {u, d}` and `k ≥ 1`. -/
theorem breadth_dyckLetter (hk : 1 ≤ k) :
    breadth (dyckLetter k) = max (2 * k) (3 * k - 2) := by
  have hb : ∃ b, IsBreadthBound (dyckLetter k) b := ⟨_, isBreadthBound_dyckNF hk _⟩
  refine le_antisymm (breadth_le (isBreadthBound_dyckNF hk _)) (max_le ?_ ?_)
  · exact le_breadth_of_forall_core hb _ (dyckMountain_core_card hk)
  · by_cases hk2 : 2 ≤ k
    · exact le_breadth_of_forall_core hb _ (dyckValley_core_card hk2)
    · have := le_breadth_of_forall_core hb _ (dyckMountain_core_card hk)
      omega

/-- **`prop:dyck-breadth`, full alphabet**: `β_{M_k}(M_k) = max (2k) (3k-2)`
for `k ≥ 1`. -/
theorem breadth_dyckNF_id (hk : 1 ≤ k) :
    breadth (id : DyckNF k → DyckNF k) = max (2 * k) (3 * k - 2) := by
  have hb : ∃ b, IsBreadthBound (id : DyckNF k → DyckNF k) b :=
    ⟨_, isBreadthBound_dyckNF hk _⟩
  refine le_antisymm (breadth_le (isBreadthBound_dyckNF hk _)) (max_le ?_ ?_)
  · exact le_breadth_of_forall_core hb _ (dyckMountain_core_card_id hk)
  · by_cases hk2 : 2 ≤ k
    · exact le_breadth_of_forall_core hb _ (dyckValley_core_card_id hk2)
    · have := le_breadth_of_forall_core hb _ (dyckMountain_core_card_id hk)
      omega

/-- **`prop:dyck-breadth`** as stated: `β_G(M_k) = β_{M_k}(M_k) = max{2k, 3k-2}`. -/
theorem breadth_dyck (hk : 1 ≤ k) :
    breadth (dyckLetter k) = breadth (id : DyckNF k → DyckNF k)
      ∧ breadth (id : DyckNF k → DyckNF k) = max (2 * k) (3 * k - 2) :=
  ⟨(breadth_dyckLetter hk).trans (breadth_dyckNF_id hk).symm, breadth_dyckNF_id hk⟩

/-- The bound `max (2k) (3k-2)` is optimal, already over `G = {u, d}`. -/
theorem not_isBreadthBound_dyckLetter (hk : 1 ≤ k) {b : ℕ} (hb : b < max (2 * k) (3 * k - 2)) :
    ¬ IsBreadthBound (dyckLetter k) b := fun h => by
  have := breadth_le h
  rw [breadth_dyckLetter hk] at this
  omega

/-- The breadth is `2` at `k = 1` and `3k - 2` for `k ≥ 2`. -/
example : breadth (dyckLetter 1) = 2 := by rw [breadth_dyckLetter le_rfl]; rfl
example (hk : 2 ≤ k) : breadth (dyckLetter k) = 3 * k - 2 := by
  rw [breadth_dyckLetter (by omega)]; omega

end Breadth

/-! ## Structure of `M_k`: Green triviality, commutativity, size -/

section Structure

variable {k : ℕ}

lemma dyck_live_eq_walkNF (t : DyckTriple k) : DyckNF.live t = dyckWalkNF [t] := by
  rw [← dyck_prod_map_live]; simp

lemma dyck_live_mul_live_eq_walkNF (t₁ t₂ : DyckTriple k) :
    DyckNF.live t₁ * DyckNF.live t₂ = dyckWalkNF [t₁, t₂] := by
  rw [← dyck_prod_map_live]; simp

lemma dyck_live_mul_live_mul_live_eq_walkNF (t₁ t₂ t₃ : DyckTriple k) :
    DyckNF.live t₁ * DyckNF.live t₂ * DyckNF.live t₃ = dyckWalkNF [t₁, t₂, t₃] := by
  rw [← dyck_prod_map_live, mul_assoc]; simp only [List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

/-- `u d u = u` in `M_k`. -/
theorem dyckLetter_up_down_up (hk : 1 ≤ k) :
    dyckLetter k false * dyckLetter k true * dyckLetter k false = dyckLetter k false := by
  rw [dyckLetter_false_eq hk, dyckLetter_true_eq hk, dyck_live_mul_live_mul_live_eq_walkNF,
    dyck_live_eq_walkNF]
  apply dyckWalkNF_congr <;> simp [dyckLoW, dyckHiW, dyckSumE, upT, downT]

/-- `u d ≠ u` in `M_k` (the final heights are `0` and `1`). -/
theorem dyckLetter_up_down_ne_up (hk : 1 ≤ k) :
    dyckLetter k false * dyckLetter k true ≠ dyckLetter k false := by
  rw [dyckLetter_false_eq hk, dyckLetter_true_eq hk, dyck_live_mul_live_eq_walkNF,
    dyck_live_eq_walkNF]
  intro h
  have := (dyckWalkNF_inj h (by simp [dyckLoW, dyckHiW, upT]; omega)).2.2
  simp [dyckSumE, upT, downT] at this

/-- `d u ≠ u` in `M_k`. -/
theorem dyckLetter_down_up_ne_up (hk : 1 ≤ k) :
    dyckLetter k true * dyckLetter k false ≠ dyckLetter k false := by
  rw [dyckLetter_false_eq hk, dyckLetter_true_eq hk, dyck_live_mul_live_eq_walkNF,
    dyck_live_eq_walkNF]
  intro h
  have := (dyckWalkNF_inj h (by simp [dyckLoW, dyckHiW, upT]; omega)).2.2
  simp [dyckSumE, upT, downT] at this

/-- **`M_k` is not `R`-trivial** (`prop:dyck-monoid`): `x = ud` and `y = u`
generate the same principal right ideal, since `y·d = x` and `x·u = y`. -/
theorem dyckNF_rightIdeal_up_down_eq (hk : 1 ≤ k) :
    rightIdeal (dyckLetter k false * dyckLetter k true) = rightIdeal (dyckLetter k false) := by
  ext z
  simp only [mem_rightIdeal]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨dyckLetter k true * q, (mul_assoc _ _ _).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨dyckLetter k false * q, by rw [← mul_assoc, dyckLetter_up_down_up hk]⟩

theorem not_isRTrivialMonoid_dyckNF (hk : 1 ≤ k) : ¬ IsRTrivialMonoid (DyckNF k) :=
  fun h => dyckLetter_up_down_ne_up hk (h _ _ (dyckNF_rightIdeal_up_down_eq hk))

/-- **`M_k` is not `L`-trivial** (`prop:dyck-monoid`): `x = du` and `y = u`
generate the same principal left ideal, since `d·y = x` and `u·x = y`.  (The
paper's mirror pair `du, d` is a second *right*-ideal witness: `M·d ≠ M·du`,
as every left multiple of `d` has final height one below its maximum.) -/
theorem dyckNF_leftIdeal_down_up_eq (hk : 1 ≤ k) :
    leftIdeal (dyckLetter k true * dyckLetter k false) = leftIdeal (dyckLetter k false) := by
  ext z
  simp only [mem_leftIdeal]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p * dyckLetter k true, mul_assoc _ _ _⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p * dyckLetter k false, by
      rw [mul_assoc, ← mul_assoc (dyckLetter k false), dyckLetter_up_down_up hk]⟩

theorem not_isLTrivial_dyckNF (hk : 1 ≤ k) :
    ∃ x y : DyckNF k, x ≠ y ∧ leftIdeal x = leftIdeal y :=
  ⟨_, _, dyckLetter_down_up_ne_up hk, dyckNF_leftIdeal_down_up_eq hk⟩

/-- **`M_k` is noncommutative** for `k ≥ 1`: `ud ≠ du`. -/
theorem dyckLetter_up_down_ne_down_up (hk : 1 ≤ k) :
    dyckLetter k false * dyckLetter k true ≠ dyckLetter k true * dyckLetter k false := by
  rw [dyckLetter_false_eq hk, dyckLetter_true_eq hk, dyck_live_mul_live_eq_walkNF,
    dyck_live_mul_live_eq_walkNF]
  intro h
  have := (dyckWalkNF_inj h (by simp [dyckLoW, dyckHiW, upT, downT]; omega)).1
  simp [dyckLoW, upT, downT] at this

theorem dyckNF_not_commutative (hk : 1 ≤ k) : ¬ ∀ x y : DyckNF k, x * y = y * x :=
  fun h => dyckLetter_up_down_ne_down_up hk (h _ _)

/-- **`|M_k| = Θ(k³)`, lower half**: `(k+1)³ < 3·|M_k|`. -/
theorem card_dyckNF_cube_lower (k : ℕ) : (k + 1) ^ 3 < 3 * Fintype.card (DyckNF k) := by
  rw [card_dyckNF_closed]
  have e1 : (k + 1) * (k + 2) * (2 * k + 3) = 2 * k ^ 3 + 9 * k ^ 2 + 13 * k + 6 := by ring
  have e2 : (k + 1) ^ 3 = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := by ring
  rw [e1, e2]
  omega

/-- **`|M_k| = Θ(k³)`**: `(k+1)³ < 3·|M_k|` and `|M_k| ≤ (k+2)³`. -/
theorem card_dyckNF_theta (k : ℕ) :
    (k + 1) ^ 3 < 3 * Fintype.card (DyckNF k) ∧ Fintype.card (DyckNF k) ≤ (k + 2) ^ 3 :=
  ⟨card_dyckNF_cube_lower k, card_dyckNF_le_cube k⟩

end Structure

end MonoidProduct
