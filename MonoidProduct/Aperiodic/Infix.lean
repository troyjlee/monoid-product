import MonoidProduct.Aperiodic.Split
import MonoidProduct.Aperiodic.Grid
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Infix search: correctness

The correctness half of the paper's infix search (`lem:infix`).

The decomposition theorem's (`thm:decomp`) condition `(W)` forbids an infix `a · r · b`.  Searching for one
directly would mean guessing both endpoints; instead the search guesses a
**scale** `ℓ` for the infix's length, a **cut** `c` strictly inside it, and a
factorization `p q = r` at the cut.  The two halves are then found by the
prefix and suffix searches (Section `sec:ags-searches`), run on clipped windows of width `4ℓ` on either side:

* `leftMark` — a suffix search in `[c-4ℓ, c)` for the letter `a` followed by
  product `p`;
* `rightMark` — a prefix search in `[c, min n (c+4ℓ))` for product `q` followed
  by the letter `b`.

Both directions are short.  Marked implies bad because the two window witnesses
concatenate across the cut and `p q = r`.  Bad implies marked because *every*
cut in `(i, j]` is legal — there are `L - 1 ≥ ℓ - 1` of them, at least
`gridStep ℓ`, so the grid meets them — and the split pair to use is simply the
actual pair of products on the two sides of whichever cut the grid supplies.

The `4ℓ` clipping is what keeps the windows small enough for the cost argument
of `lem:infix`: an infix of length in `[ℓ, 2ℓ]` never reaches more than `2ℓ` away from
any of its own cuts.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The marked-cut predicate -/

/-- The left half of a marked cut: within `[c-4ℓ, c)`, the letter `a` followed
by product `p` up to the cut. -/
def leftMark (letter : σ → M) (a p : M) (ℓ c : ℕ) {n : ℕ} (x : Fin n → σ) : Bool :=
  decide (((Finset.Ico (c - 4 * ℓ) c).filter fun i =>
    padAt (fun t => letter (x t)) i = a ∧ winProd letter x (i + 1) c = p).Nonempty)

/-- The right half: within `[c, min n (c+4ℓ))`, product `q` from the cut
followed by the letter `b`. -/
def rightMark (letter : σ → M) (q b : M) (ℓ c : ℕ) {n : ℕ} (x : Fin n → σ) : Bool :=
  decide (((Finset.Ico c (min n (c + 4 * ℓ))).filter fun j =>
    winProd letter x c j = q ∧ padAt (fun t => letter (x t)) j = b).Nonempty)

/-- **A marked cut.** -/
def markedAt (letter : σ → M) (a p q b : M) (ℓ c : ℕ) {n : ℕ} (x : Fin n → σ) :
    Bool :=
  leftMark letter a p ℓ c x && rightMark letter q b ℓ c x

/-- The forbidden infix, for one triple `(a,r,b) ∈ G m`. -/
def badInfixFor (letter : σ → M) (a r b : M) {n : ℕ} (x : Fin n → σ) : Bool :=
  decide ((((Finset.range n) ×ˢ (Finset.range n)).filter fun ij =>
    ij.1 < ij.2 ∧ padAt (fun t => letter (x t)) ij.1 = a ∧
      winProd letter x (ij.1 + 1) ij.2 = r ∧
      padAt (fun t => letter (x t)) ij.2 = b).Nonempty)

lemma leftMark_eq_true {letter : σ → M} {a p : M} {ℓ c n : ℕ} {x : Fin n → σ} :
    leftMark letter a p ℓ c x = true ↔
      ∃ i ∈ Finset.Ico (c - 4 * ℓ) c,
        padAt (fun t => letter (x t)) i = a ∧ winProd letter x (i + 1) c = p := by
  simp [leftMark, Finset.filter_nonempty_iff]

/-- Regrouping all left marks compatible with a fixed right pivot `q` removes
the guessed product `p`: the suffix only has to stabilize `q` on the left. -/
lemma exists_leftMark_mul_eq_right_iff (letter : σ → M) (a q : M) (ℓ c : ℕ)
    {n : ℕ} (x : Fin n → σ) :
    (∃ p : M, p * q = q ∧ leftMark letter a p ℓ c x = true) ↔
      ∃ i ∈ Finset.Ico (c - 4 * ℓ) c,
        padAt (fun t => letter (x t)) i = a ∧
          winProd letter x (i + 1) c * q = q := by
  constructor
  · rintro ⟨p, hpq, hmark⟩
    obtain ⟨i, hi, ha, hp⟩ := leftMark_eq_true.1 hmark
    exact ⟨i, hi, ha, by simpa [hp] using hpq⟩
  · rintro ⟨i, hi, ha, hsurvives⟩
    exact ⟨winProd letter x (i + 1) c, hsurvives,
      leftMark_eq_true.2 ⟨i, hi, ha, rfl⟩⟩

/-- In a one-`R` `J`-class, stabilization of a fixed right pivot by a window
product is the letterwise condition that every window letter stays in that
`J`-class. -/
lemma winProd_mul_eq_right_iff_forall_mem_twoIdeal_eq
    [IsAperiodicMonoid M] (letter : σ → M) (q : M)
    (hR : ∀ y : M, twoIdeal y = twoIdeal q → rightIdeal y = rightIdeal q)
    {n : ℕ} (x : Fin n → σ) (lo hi : ℕ) :
    winProd letter x lo hi * q = q ↔
      ∀ k ∈ List.range (hi - lo),
        twoIdeal (padAt (fun t => letter (x t)) (lo + k) * q) = twoIdeal q := by
  simpa only [winProd, rangeProd, List.forall_mem_map] using
    (list_prod_mul_eq_iff_forall_mem_twoIdeal_eq_of_jClass_one_rightIdeal hR
      ((List.range (hi - lo)).map fun k =>
        padAt (fun t => letter (x t)) (lo + k)))

/-- Fixed-pivot regrouping followed by one-coordinate deletion.  The union of
all compatible left-product searches is a direct search for `a` whose
intervening letters all preserve the `J`-class of `q`; no exact-product child
remains. -/
lemma exists_leftMark_mul_eq_right_iff_letterwise_survival
    [IsAperiodicMonoid M] (letter : σ → M) (a q : M)
    (hR : ∀ y : M, twoIdeal y = twoIdeal q → rightIdeal y = rightIdeal q)
    (ℓ c : ℕ) {n : ℕ} (x : Fin n → σ) :
    (∃ p : M, p * q = q ∧ leftMark letter a p ℓ c x = true) ↔
      ∃ i ∈ Finset.Ico (c - 4 * ℓ) c,
        padAt (fun t => letter (x t)) i = a ∧
          ∀ k ∈ List.range (c - (i + 1)),
            twoIdeal (padAt (fun t => letter (x t)) (i + 1 + k) * q) = twoIdeal q := by
  rw [exists_leftMark_mul_eq_right_iff]
  constructor
  · rintro ⟨i, hi, ha, hprod⟩
    exact ⟨i, hi, ha,
      (winProd_mul_eq_right_iff_forall_mem_twoIdeal_eq letter q hR x (i + 1) c).1
        hprod⟩
  · rintro ⟨i, hi, ha, hletters⟩
    exact ⟨i, hi, ha,
      (winProd_mul_eq_right_iff_forall_mem_twoIdeal_eq letter q hR x (i + 1) c).2
        hletters⟩

lemma rightMark_eq_true {letter : σ → M} {q b : M} {ℓ c n : ℕ} {x : Fin n → σ} :
    rightMark letter q b ℓ c x = true ↔
      ∃ j ∈ Finset.Ico c (min n (c + 4 * ℓ)),
        winProd letter x c j = q ∧ padAt (fun t => letter (x t)) j = b := by
  simp [rightMark, Finset.filter_nonempty_iff]

/-- The right-hand dual of `exists_leftMark_mul_eq_right_iff`: regrouping all
right marks compatible with a fixed left pivot `p` removes the guessed product
`q`. -/
lemma exists_rightMark_left_mul_eq_iff (letter : σ → M) (p b : M) (ℓ c : ℕ)
    {n : ℕ} (x : Fin n → σ) :
    (∃ q : M, p * q = p ∧ rightMark letter q b ℓ c x = true) ↔
      ∃ j ∈ Finset.Ico c (min n (c + 4 * ℓ)),
        p * winProd letter x c j = p ∧
          padAt (fun t => letter (x t)) j = b := by
  constructor
  · rintro ⟨q, hpq, hmark⟩
    obtain ⟨j, hj, hq, hb⟩ := rightMark_eq_true.1 hmark
    exact ⟨j, hj, by simpa [hq] using hpq, hb⟩
  · rintro ⟨j, hj, hsurvives, hb⟩
    exact ⟨winProd letter x c j, hsurvives,
      rightMark_eq_true.2 ⟨j, hj, rfl, hb⟩⟩

lemma badInfixFor_eq_true {letter : σ → M} {a r b : M} {n : ℕ} {x : Fin n → σ} :
    badInfixFor letter a r b x = true ↔
      ∃ i ∈ Finset.range n, ∃ j ∈ Finset.range n, i < j ∧
        padAt (fun t => letter (x t)) i = a ∧ winProd letter x (i + 1) j = r ∧
        padAt (fun t => letter (x t)) j = b := by
  simp only [badInfixFor, decide_eq_true_eq, Finset.filter_nonempty_iff,
    Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨hi, hj⟩, h⟩
    exact ⟨i, hi, j, hj, h⟩
  · rintro ⟨i, hi, j, hj, h⟩
    exact ⟨i, j, ⟨hi, hj⟩, h⟩

/-! ## The equivalence -/

/-- **`lem:infix`, correctness.**  A forbidden infix exists exactly when some
scale, some grid cut and some split pair mark one. -/
theorem badInfixFor_iff (letter : σ → M) (a r b : M) {n : ℕ} (x : Fin n → σ) :
    badInfixFor letter a r b x = true ↔
      ∃ ℓ ∈ scales n, ∃ c ∈ cutGrid n ℓ, ∃ pq ∈ splitPairs r,
        markedAt letter a pq.1 pq.2 b ℓ c x = true := by
  classical
  constructor
  · -- a witness produces a scale, a cut and a split
    intro hbad
    obtain ⟨i, -, j, hjn, hij, hlet_i, hprod, hlet_j⟩ := badInfixFor_eq_true.1 hbad
    rw [Finset.mem_range] at hjn
    simp only [winProd] at hprod
    obtain ⟨ℓ, hℓ, hℓL, hLℓ⟩ :=
      exists_mem_scales (n := n) (L := j - i + 1) (by omega) (by omega)
    have h2ℓ : 2 ≤ ℓ := two_le_of_mem_scales hℓ
    have hstep : gridStep ℓ ≤ ℓ - 1 := gridStep_le_sub_one h2ℓ
    obtain ⟨c, hc, hic, hcj⟩ :=
      exists_mem_cutGrid (n := n) (ℓ := ℓ) (s := i + 1) (e := j)
        (by omega) (by omega)
    refine ⟨ℓ, hℓ, c, hc,
      (winProd letter x (i + 1) c, winProd letter x c j), ?_, ?_⟩
    · rw [mem_splitPairs]
      simp only [winProd]
      rw [rangeProd_split _ (show i + 1 ≤ c by omega) (show c ≤ j by omega)]
      exact hprod
    · rw [markedAt, Bool.and_eq_true, leftMark_eq_true, rightMark_eq_true]
      exact ⟨⟨i, Finset.mem_Ico.2 ⟨by omega, by omega⟩, hlet_i, rfl⟩,
        ⟨j, Finset.mem_Ico.2 ⟨by omega, by omega⟩, rfl, hlet_j⟩⟩
  · -- a marked cut produces a witness
    rintro ⟨ℓ, -, c, -, ⟨p, q⟩, hpq, hmark⟩
    rw [mem_splitPairs] at hpq
    rw [markedAt, Bool.and_eq_true, leftMark_eq_true, rightMark_eq_true] at hmark
    obtain ⟨⟨i, hi, hlet_i, hp⟩, ⟨j, hj, hq, hlet_j⟩⟩ := hmark
    rw [Finset.mem_Ico] at hi hj
    refine badInfixFor_eq_true.2 ⟨i, Finset.mem_range.2 (by omega), j,
      Finset.mem_range.2 (by omega), by omega, hlet_i, ?_, hlet_j⟩
    simp only [winProd] at hp hq ⊢
    rw [← rangeProd_split (fun t => letter (x t)) (show i + 1 ≤ c by omega)
      (show c ≤ j by omega), hp, hq]
    exact hpq

/-! ## The bridge to the decomposition theorem (`thm:decomp`) -/

lemma badInfix_iff (letter : σ → M) (m : M) {n : ℕ} (x : Fin n → σ) :
    badInfix m (fun i => letter (x i))
      ↔ ∃ t ∈ setG m, badInfixFor letter t.1 t.2.1 t.2.2 x = true := by
  constructor
  · rintro ⟨i, j, hij, hjn, a, r, b, hG, hlet_i, hprod, hlet_j⟩
    exact ⟨(a, r, b), hG, badInfixFor_eq_true.2 ⟨i, Finset.mem_range.2 (by omega),
      j, Finset.mem_range.2 hjn, hij, hlet_i, hprod, hlet_j⟩⟩
  · rintro ⟨⟨a, r, b⟩, hG, hbad⟩
    obtain ⟨i, -, j, hjn, hij, hlet_i, hprod, hlet_j⟩ := badInfixFor_eq_true.1 hbad
    exact ⟨i, j, hij, Finset.mem_range.1 hjn, a, r, b, hG, hlet_i, hprod, hlet_j⟩

end

end MonoidProduct
