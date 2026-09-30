import MonoidProduct.Aperiodic.Suffix
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The algebra of a marked cut

The splitting step (`prop:split` of the paper).  The infix search
(`lem:infix`) guesses a cut
strictly inside the forbidden infix `a · r · b` and a factorization `p q = r` at
that cut.  Everything to the left of the cut is then found by a *suffix* search
for `a` followed by product `p`; everything to the right by a *prefix* search
for product `q` followed by `b`.

For those two searches to be legitimate they need their strict-inclusion
hypotheses, and this file supplies them:

  `(a,r,b) ∈ G m`, `p q = r`  ⟹  `leftIdeal (a p) ⊊ leftIdeal p`
                              and `rightIdeal (q b) ⊊ rightIdeal q`.

Both come from the same observation.  If `rightIdeal (q b) = rightIdeal q` then
`q = q b u` for some `u`, and substituting that into `m ∈ M a r M` produces
`m ∈ M a r b M` — which is exactly what `G m` forbids.  The left case
substitutes into `m ∈ M r b M` instead.

The file also records that a factorization never leaves the ideal: `MrM ⊆ MpM`
and `MrM ⊆ MqM`, so both halves of a split sit at or above `r`, hence strictly
below `m`, in the `J`-order.  That is what makes the recursion behind `thm:main-ags` descend
through the infix search.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## Factorizations -/

/-- The factorizations of `r`. -/
def splitPairs (r : M) : Finset (M × M) :=
  Finset.univ.filter fun pq => pq.1 * pq.2 = r

@[simp] lemma mem_splitPairs {r p q : M} : (p, q) ∈ splitPairs r ↔ p * q = r := by
  simp [splitPairs]

lemma card_splitPairs_le (r : M) : (splitPairs r).card ≤ Fintype.card M ^ 2 :=
  le_trans (Finset.card_le_univ _) (le_of_eq (by rw [Fintype.card_prod]; ring))

/-- A factorization never leaves the two-sided ideal. -/
lemma twoIdeal_subset_left {r p q : M} (h : p * q = r) : twoIdeal r ⊆ twoIdeal p :=
  twoIdeal_subset_of_mem (mem_twoIdeal.2 ⟨1, q, by rw [one_mul]; exact h⟩)

lemma twoIdeal_subset_right {r p q : M} (h : p * q = r) : twoIdeal r ⊆ twoIdeal q :=
  twoIdeal_subset_of_mem (mem_twoIdeal.2 ⟨p, 1, by rw [mul_one]; exact h⟩)

end

section
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-! ## The two strict inclusions

These are the hypotheses `hasDual_prefixEvent` and `hasDual_suffixEvent` ask
for, delivered at a marked cut. -/

/-- **The right half of a marked cut is a legitimate prefix search.**  If the
right ideal did not drop at `b`, the infix `a r b` would already realise `m`. -/
theorem rightIdeal_lt_of_mem_setG {m a r b p q : M} (hG : (a, r, b) ∈ setG m)
    (hpq : p * q = r) : rightIdeal (q * b) ⊂ rightIdeal q := by
  obtain ⟨har, -, hnarb⟩ := mem_setG.1 hG
  refine lt_of_le_of_ne (rightIdeal_mul_subset q b) fun hcon => ?_
  have hq : q ∈ rightIdeal (q * b) := by rw [hcon]; exact self_mem_rightIdeal q
  obtain ⟨u, hu⟩ := mem_rightIdeal.1 hq
  obtain ⟨w, t, hwt⟩ := mem_twoIdeal.1 har
  have hkey : r * (b * u) = r := by
    rw [← hpq, mul_assoc, ← mul_assoc q b u, hu]
  refine hnarb (mem_twoIdeal.2 ⟨w, u * t, ?_⟩)
  calc w * (a * r * b) * (u * t) = w * (a * (r * (b * u))) * t := by
        simp only [mul_assoc]
    _ = w * (a * r) * t := by rw [hkey]
    _ = m := hwt

/-- **The left half of a marked cut is a legitimate suffix search.** -/
theorem leftIdeal_lt_of_mem_setG {m a r b p q : M} (hG : (a, r, b) ∈ setG m)
    (hpq : p * q = r) : leftIdeal (a * p) ⊂ leftIdeal p := by
  obtain ⟨-, hrb, hnarb⟩ := mem_setG.1 hG
  refine lt_of_le_of_ne (leftIdeal_mul_subset a p) fun hcon => ?_
  have hp : p ∈ leftIdeal (a * p) := by rw [hcon]; exact self_mem_leftIdeal p
  obtain ⟨v, hv⟩ := mem_leftIdeal.1 hp
  obtain ⟨w, t, hwt⟩ := mem_twoIdeal.1 hrb
  have hkey : v * a * r = r := by
    rw [← hpq, ← mul_assoc, mul_assoc v a p, hv]
  refine hnarb (mem_twoIdeal.2 ⟨w * v, t, ?_⟩)
  calc w * v * (a * r * b) * t = w * (v * a * r * b) * t := by simp only [mul_assoc]
    _ = w * (r * b) * t := by rw [hkey]
    _ = m := hwt

/-! ## The level drops

Both halves of a marked split are strictly below the target, so the equality
tests the infix search recurses on are legitimate. -/

theorem twoIdeal_lt_of_split_left {m a r b p q : M} (hG : (a, r, b) ∈ setG m)
    (hpq : p * q = r) : twoIdeal m ⊂ twoIdeal p :=
  lt_of_lt_of_le (twoIdeal_lt_of_mem_setG hG) (twoIdeal_subset_left hpq)

theorem twoIdeal_lt_of_split_right {m a r b p q : M} (hG : (a, r, b) ∈ setG m)
    (hpq : p * q = r) : twoIdeal m ⊂ twoIdeal q :=
  lt_of_lt_of_le (twoIdeal_lt_of_mem_setG hG) (twoIdeal_subset_right hpq)

theorem jLevel_lt_of_split_left {m a r b p q : M} (hG : (a, r, b) ∈ setG m)
    (hpq : p * q = r) : jLevel p < jLevel m :=
  jLevel_lt_of_ssubset (twoIdeal_lt_of_split_left hG hpq)

theorem jLevel_lt_of_split_right {m a r b p q : M} (hG : (a, r, b) ∈ setG m)
    (hpq : p * q = r) : jLevel q < jLevel m :=
  jLevel_lt_of_ssubset (twoIdeal_lt_of_split_right hG hpq)

end

end MonoidProduct
