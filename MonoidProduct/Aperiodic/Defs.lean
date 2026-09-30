import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.List.Range
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Group

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Finite aperiodic monoids and ordered products

The algebraic foundation for the Aaronson–Grier–Schaeffer-style upper bound of
Section `sec:ags` of the paper.  This file is deliberately free of any
adversary machinery: it defines the hypothesis, the ordered product of a word,
and the interval products the search arguments will need.

**Aperiodicity** is taken in exactly the form the paper uses — every element's
powers eventually stabilise.  A finite monoid is aperiodic iff it is `H`-trivial
iff it is star-free, but none of those equivalences is needed, and assuming only
stabilisation keeps the development self-contained.

Two consequences carry the whole dependency of Section `sec:ags` on the
preliminaries (Section `sec:prelim`):

* the **sandwich lemma** `sandwich_left`/`sandwich_right`: `p q r = q` forces
  `q = p q` and `q = q r`.  Its proof is that of `lem:sandwich` — iterate to `pᵏ q rᵏ = q`
  and evaluate at a common stabilisation exponent;
* **`mul_eq_one_iff`**: a product is `1` only if every factor is, which is
  `prop:identity`.  It is the sandwich lemma at `q = 1`.

Products are indexed by half-open intervals `[lo, hi)` throughout, and positions
outside the word contribute the identity (`padAt`).  That convention makes
`rangeProd_split` unconditional in the awkward direction and removes every
clipping side condition from the interval arithmetic later, which
would otherwise be the likeliest time sink.
-/

namespace MonoidProduct

/-! ## Aperiodicity -/

/-- A monoid in which the powers of every element eventually stabilise.  For a
*finite* monoid this is equivalent to aperiodicity, `H`-triviality and
star-freeness; only this form is used. -/
class IsAperiodicMonoid (M : Type*) [Monoid M] : Prop where
  /-- Every element's powers eventually stabilise. -/
  stabilizes : ∀ a : M, ∃ N : ℕ, 0 < N ∧ a ^ N = a ^ (N + 1)

section
variable {M : Type*} [Monoid M]

/-- Once the powers of `a` stabilise they stay stabilised. -/
lemma pow_stab_add {a : M} {N : ℕ} (h : a ^ N = a ^ (N + 1)) (d : ℕ) :
    a ^ (N + d) = a ^ (N + d + 1) := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
      have hstep : a ^ (N + d) * a = a ^ (N + d + 1) * a := by rw [ih]
      calc a ^ (N + (d + 1)) = a ^ (N + d) * a := pow_succ a (N + d)
      _ = a ^ (N + d + 1) * a := hstep
      _ = a ^ (N + (d + 1) + 1) := (pow_succ a (N + d + 1)).symm

lemma pow_stab {a : M} {N : ℕ} (h : a ^ N = a ^ (N + 1)) {k : ℕ} (hk : N ≤ k) :
    a ^ k = a ^ (k + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact pow_stab_add h d

variable [IsAperiodicMonoid M]

/-- Two elements stabilise at a common positive exponent. -/
lemma exists_common_stab (p r : M) :
    ∃ K : ℕ, 0 < K ∧ p ^ K = p ^ (K + 1) ∧ r ^ K = r ^ (K + 1) := by
  obtain ⟨Np, hNp, hp⟩ := IsAperiodicMonoid.stabilizes p
  obtain ⟨Nr, hNr, hr⟩ := IsAperiodicMonoid.stabilizes r
  exact ⟨max Np Nr, by omega, pow_stab hp (le_max_left _ _),
    pow_stab hr (le_max_right _ _)⟩

/-- Iterating a sandwich identity. -/
lemma pow_sandwich {p q r : M} (h : p * q * r = q) (k : ℕ) :
    p ^ k * q * r ^ k = q := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : p ^ (k + 1) * q * r ^ (k + 1)
          = p * (p ^ k * q * r ^ k) * r := by
        rw [pow_succ' p k, pow_succ r k]
        simp [mul_assoc]
      rw [hstep, ih, h]

/-- **The sandwich lemma** (the paper's `lem:sandwich`), left half. -/
theorem sandwich_left {p q r : M} (h : p * q * r = q) : p * q = q := by
  obtain ⟨K, _, hp, hr⟩ := exists_common_stab p r
  have key : p * (p ^ K * q * r ^ K) = p ^ (K + 1) * q * r ^ K := by
    rw [pow_succ' p K]
    simp [mul_assoc]
  calc p * q = p * (p ^ K * q * r ^ K) := by rw [pow_sandwich h K]
    _ = p ^ (K + 1) * q * r ^ K := key
    _ = p ^ K * q * r ^ K := by rw [← hp]
    _ = q := pow_sandwich h K

/-- **The sandwich lemma**, right half. -/
theorem sandwich_right {p q r : M} (h : p * q * r = q) : q * r = q := by
  obtain ⟨K, _, hp, hr⟩ := exists_common_stab p r
  have key : (p ^ K * q * r ^ K) * r = p ^ K * q * r ^ (K + 1) := by
    rw [pow_succ r K]
    simp [mul_assoc]
  calc q * r = (p ^ K * q * r ^ K) * r := by rw [pow_sandwich h K]
    _ = p ^ K * q * r ^ (K + 1) := key
    _ = p ^ K * q * r ^ K := by rw [← hr]
    _ = q := pow_sandwich h K

/-! ## Products equal to the identity -/

/-- **`prop:identity`**: a product is the identity only if both factors are. -/
theorem mul_eq_one_iff' {p q : M} : p * q = 1 ↔ p = 1 ∧ q = 1 := by
  constructor
  · intro h
    have hs : p * 1 * q = 1 := by simpa using h
    exact ⟨by simpa using sandwich_left hs, by simpa using sandwich_right hs⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem List.prod_eq_one_iff' (w : List M) : w.prod = 1 ↔ ∀ a ∈ w, a = 1 := by
  induction w with
  | nil => simp
  | cons a t ih =>
      rw [List.prod_cons, mul_eq_one_iff']
      constructor
      · rintro ⟨ha, ht⟩ b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ha
        · exact (ih.1 ht) b hb
      · intro h
        exact ⟨h a (List.mem_cons_self ..),
          ih.2 fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

end

/-! ## Ordered products over half-open intervals

Nothing in this section uses aperiodicity. -/

section
variable {M : Type*} [Monoid M] {n : ℕ}

/-- The letter at a position, or the identity outside the word.  Padding removes
every clipping side condition from the interval arithmetic. -/
def padAt (x : Fin n → M) (i : ℕ) : M := if h : i < n then x ⟨i, h⟩ else 1

@[simp] lemma padAt_of_lt (x : Fin n → M) {i : ℕ} (h : i < n) :
    padAt x i = x ⟨i, h⟩ := dif_pos h

@[simp] lemma padAt_of_le (x : Fin n → M) {i : ℕ} (h : n ≤ i) : padAt x i = 1 :=
  dif_neg (by omega)

/-- The product of the letters at the positions of `[lo, hi)`, in order. -/
def rangeProd (x : Fin n → M) (lo hi : ℕ) : M :=
  ((List.range (hi - lo)).map fun k => padAt x (lo + k)).prod

/-- The ordered product of the whole word. -/
def orderedProd (x : Fin n → M) : M := rangeProd x 0 n

@[simp] lemma rangeProd_self (x : Fin n → M) (lo : ℕ) : rangeProd x lo lo = 1 := by
  simp [rangeProd]

lemma rangeProd_eq_one_of_le (x : Fin n → M) {lo hi : ℕ} (h : hi ≤ lo) :
    rangeProd x lo hi = 1 := by
  have : hi - lo = 0 := by omega
  simp [rangeProd, this]

lemma rangeProd_succ_right (x : Fin n → M) {lo hi : ℕ} (h : lo ≤ hi) :
    rangeProd x lo (hi + 1) = rangeProd x lo hi * padAt x hi := by
  have hlen : hi + 1 - lo = (hi - lo) + 1 := by omega
  rw [rangeProd, rangeProd, hlen, List.range_succ, List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  congr 2
  omega

/-- **Interval products split**: `φ[lo,hi) = φ[lo,mid) · φ[mid,hi)`. -/
theorem rangeProd_split (x : Fin n → M) {lo mid hi : ℕ} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) :
    rangeProd x lo mid * rangeProd x mid hi = rangeProd x lo hi := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h2
  induction d with
  | zero => simp
  | succ d ih =>
      have hmd : mid ≤ mid + d := by omega
      rw [show mid + (d + 1) = (mid + d) + 1 from by omega,
        rangeProd_succ_right x hmd, rangeProd_succ_right x (by omega : lo ≤ mid + d),
        ← mul_assoc, ih (by omega)]

lemma rangeProd_singleton (x : Fin n → M) {i : ℕ} (h : i < n) :
    rangeProd x i (i + 1) = x ⟨i, h⟩ := by
  rw [rangeProd_succ_right x (le_refl i), rangeProd_self, one_mul, padAt_of_lt x h]

/-- **Only the letters inside the interval matter** — and the two words need not
even have the same length, which is what lets a window of a long word be
compared with a short word. -/
lemma rangeProd_congr {m : ℕ} {x : Fin n → M} {y : Fin m → M} {lo hi : ℕ}
    (h : ∀ i : ℕ, lo ≤ i → i < hi → padAt x i = padAt y i) :
    rangeProd x lo hi = rangeProd y lo hi := by
  refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
  rw [List.mem_range] at hk
  exact h (lo + k) (by omega) (by omega)

lemma orderedProd_eq_rangeProd (x : Fin n → M) :
    orderedProd x = rangeProd x 0 n := rfl

/-- Every letter of an all-`1` word contributes nothing. -/
lemma orderedProd_eq_one_of_forall {x : Fin n → M} (h : ∀ i, x i = 1) :
    orderedProd x = 1 := by
  have hpad : ∀ k, padAt x k = 1 := by
    intro k
    by_cases hk : k < n
    · rw [padAt_of_lt x hk]
      exact h _
    · rw [padAt_of_le x (by omega)]
  rw [orderedProd, rangeProd]
  refine List.prod_eq_one fun a ha => ?_
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 ha
  exact hpad _

/-- The ordered product is the product of the list of letters, in index order. -/
theorem orderedProd_eq_prod_ofFn (x : Fin n → M) :
    orderedProd x = (List.ofFn x).prod := by
  induction n with
  | zero => simp [orderedProd, rangeProd]
  | succ n ih =>
      have hsplit : orderedProd x
          = rangeProd x 0 n * padAt x n := by
        rw [orderedProd, rangeProd_succ_right x (Nat.zero_le n)]
      have hres : rangeProd x 0 n
          = orderedProd (fun i : Fin n => x i.castSucc) := by
        rw [orderedProd]
        refine rangeProd_congr fun i _ hi => ?_
        rw [padAt_of_lt _ (by omega), padAt_of_lt _ hi]
        rfl
      rw [hsplit, hres, ih, padAt_of_lt x (Nat.lt_succ_self n),
        List.ofFn_succ_last, List.prod_append, List.prod_singleton]
      rfl

end

/-! ## Words with product `1` -/

section
variable {M : Type*} [Monoid M] [IsAperiodicMonoid M] {n : ℕ}

/-- **A word has product `1` exactly when every letter is `1`** (`prop:identity`).
This is the base case of the whole recursion. -/
theorem orderedProd_eq_one_iff (x : Fin n → M) :
    orderedProd x = 1 ↔ ∀ i, x i = 1 := by
  refine ⟨fun h i => ?_, orderedProd_eq_one_of_forall⟩
  have h1 : rangeProd x 0 (i : ℕ) * rangeProd x (i : ℕ) n = 1 := by
    rw [rangeProd_split x (Nat.zero_le _) (le_of_lt i.isLt)]
    exact h
  have h2 : rangeProd x (i : ℕ) ((i : ℕ) + 1) * rangeProd x ((i : ℕ) + 1) n
      = rangeProd x (i : ℕ) n :=
    rangeProd_split x (by omega) i.isLt
  have h3 : rangeProd x (i : ℕ) n = 1 := (mul_eq_one_iff'.1 h1).2
  rw [← h2] at h3
  have h4 := (mul_eq_one_iff'.1 h3).1
  rwa [rangeProd_singleton x i.isLt, Fin.eta] at h4

end

end MonoidProduct
