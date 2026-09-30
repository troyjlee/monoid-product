import MonoidProduct.Trichotomy.Main
import MonoidProduct.Aperiodic.Semigroup
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The nonaperiodic clause for finite **semigroups**

`monoid.tex`'s trichotomy opens with a statement about semigroups: every
finite nonaperiodic semigroup `S` has `Q(Prod_{S,n}) = Θ_S(n)`.  The
`Trichotomy/Main.lean` development proves the monoid case; the obstruction to
transporting it was that its construction uses the neutral letter `1`, which
a semigroup does not have, and the paper obtains a substitute from a
nontrivial subgroup — index/period theory this project has avoided.

**None of that is needed.**  The observation that removes it: the two letters
do not have to be `1` and `g`, only two letters whose products *shift the
exponent by one*.  Take

    s   and   s * s,

both genuine elements of `S`.  A word of length `L` with `r` marked letters
has, in the unitisation `WithOne S`, the product

    g ^ (L + r),        g = ↑s

(`coe_semigroupProd_sLetter`) — every letter contributes one factor and each
marked letter one more.  Adjacent layers `r` and `r+1` therefore give the
*consecutive* powers `g^{L+r}` and `g^{L+r+1}`, distinct because `g` is a
non-stabilising element of `WithOne S`, which is exactly
`¬ IsAperiodicSemigroup S`.  The two-layer certificate of
`MonoidProduct/Layer/Lower.lean` then applies unchanged.

Finiteness is used only for the query-complexity packaging, never for the
witness.  Words are indexed by `Fin (n + 1)`, matching `semigroupProd`, so no
separate nonempty-length hypothesis appears.

Headlines: `half_le_advPMOn_semigroupProd_of_nonaperiodic`,
`half_le_advPM_semigroupProd_of_not_aperiodic`.  The operational corollaries
live in `Quantum/Applications.lean`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix
open scoped Classical

/-! ## Ordered products of powers -/

section Pow

variable {M : Type} [Monoid M]

private lemma rangeProd_pow (g : M) {L : ℕ} (e : Fin L → ℕ) (m : ℕ) :
    rangeProd (fun i : Fin L => g ^ e i) 0 m
      = g ^ (∑ i ∈ Finset.univ.filter fun i : Fin L => (i : ℕ) < m, e i) := by
  classical
  induction m with
  | zero =>
      rw [rangeProd_self, Finset.filter_false_of_mem (fun i _ => by omega),
        Finset.sum_empty, pow_zero]
  | succ m ih =>
      rw [rangeProd_succ_right _ (Nat.zero_le m), ih]
      by_cases hm : m < L
      · rw [padAt_of_lt _ hm]
        have hfil : (Finset.univ.filter fun i : Fin L => (i : ℕ) < m + 1)
            = insert (⟨m, hm⟩ : Fin L)
              (Finset.univ.filter fun i : Fin L => (i : ℕ) < m) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert]
          constructor
          · intro hlt
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
            · exact Or.inr h
            · exact Or.inl (Fin.ext h)
          · rintro (rfl | hlt)
            · exact Nat.lt_succ_self m
            · exact Nat.lt_succ_of_lt hlt
        rw [hfil, Finset.sum_insert (by simp), ← pow_add, Nat.add_comm]
      · rw [padAt_of_le _ (by omega), mul_one]
        congr 2
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hlt
          exact Nat.lt_succ_of_lt hlt
        · intro _
          exact lt_of_lt_of_le i.isLt (not_lt.mp hm)

/-- **An ordered product of powers is the power of the sum.** -/
lemma orderedProd_pow (g : M) {L : ℕ} (e : Fin L → ℕ) :
    orderedProd (fun i : Fin L => g ^ e i) = g ^ (∑ i, e i) := by
  classical
  rw [orderedProd_eq_rangeProd, rangeProd_pow,
    Finset.filter_true_of_mem fun i _ => i.isLt]

end Pow

/-- Each letter contributes one factor, each *marked* letter one more. -/
private lemma sum_exp_eq {L : ℕ} (z : Finset (Fin L)) :
    (∑ i : Fin L, if i ∈ z then 2 else 1) = L + z.card := by
  classical
  have hsplit : ∀ i : Fin L,
      (if i ∈ z then 2 else 1) = 1 + (if i ∈ z then 1 else 0) := by
    intro i
    by_cases h : i ∈ z <;> simp [h]
  have hcount : (∑ _i : Fin L, 1) = L := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
  have hmark : (∑ i : Fin L, if i ∈ z then 1 else 0) = z.card := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, hcount,
    hmark]

/-! ## The two semigroup letters -/

section Semigroup

variable {S : Type} [Semigroup S] [Fintype S] [DecidableEq S]

/-- The bit encoding by genuine semigroup letters: `s` and `s * s`. -/
def sLetter (s : S) : Bool → S := fun b => if b then s * s else s

@[simp] lemma sLetter_false (s : S) : sLetter s false = s := rfl

@[simp] lemma sLetter_true (s : S) : sLetter s true = s * s := rfl

lemma coe_sLetter (s : S) (b : Bool) :
    ((sLetter s b : S) : WithOne S)
      = (s : WithOne S) ^ (if b then 2 else 1) := by
  cases b
  · show ((s : S) : WithOne S) = (s : WithOne S) ^ 1
    rw [pow_one]
  · show ((s * s : S) : WithOne S) = (s : WithOne S) ^ 2
    rw [WithOne.coe_mul, pow_two]

/-- **The shifted-power identity**: a word of length `L = n + 1` with `r`
marked letters has product `g ^ (L + r)` in the unitisation. -/
lemma coe_semigroupProd_sLetter (s : S) {n : ℕ} (z : Finset (Fin (n + 1))) :
    ((semigroupProd n (fun i => sLetter s (decide (i ∈ z))) : S) : WithOne S)
      = (s : WithOne S) ^ ((n + 1) + z.card) := by
  classical
  rw [coe_semigroupProd]
  have h : (fun i : Fin (n + 1) =>
        (((sLetter s (decide (i ∈ z))) : S) : WithOne S))
      = fun i : Fin (n + 1) =>
        (s : WithOne S) ^ (if i ∈ z then 2 else 1) := by
    funext i
    rw [coe_sLetter]
    congr 1
    by_cases hi : i ∈ z <;> simp [hi]
  rw [h, orderedProd_pow, sum_exp_eq]

/-! ## The witness -/

/-- A semigroup that is not aperiodic has an element whose powers never
stabilise in the unitisation.  This is `¬ IsAperiodicSemigroup` unfolded —
no subgroup and no index/period theory. -/
lemma exists_nonaperiodic_semigroup_elem (h : ¬ IsAperiodicSemigroup S) :
    ∃ s : S, ∀ m, 0 < m →
      (s : WithOne S) ^ m ≠ (s : WithOne S) ^ (m + 1) := by
  have h1 : ¬ IsAperiodicMonoid (WithOne S) := fun hh => h ⟨hh⟩
  obtain ⟨g, hg⟩ := exists_nonaperiodic_elem h1
  obtain ⟨s, hs⟩ := WithOne.ne_one_iff_exists.mp (ne_one_of_nonaperiodic hg)
  refine ⟨s, ?_⟩
  rw [hs]
  exact hg

lemma sLetter_injective {s : S}
    (hs : ∀ m, 0 < m → (s : WithOne S) ^ m ≠ (s : WithOne S) ^ (m + 1)) :
    Function.Injective (sLetter s) := by
  have hne : s ≠ s * s := by
    intro h
    refine hs 1 one_pos ?_
    rw [pow_one, pow_two, ← WithOne.coe_mul, ← h]
  intro b b' hbb
  cases b <;> cases b'
  · rfl
  · exact absurd (show s = s * s from hbb) hne
  · exact absurd (show s = s * s from hbb.symm) hne
  · rfl

/-! ## The lower bound -/

/-- Read-determinacy of the promise product. -/
lemma det_semigroupProd_layerRead (s : S) (n r : ℕ) :
    ∀ x y : Layers (n + 1) r,
      layerRead (sLetter s) x = layerRead (sLetter s) y →
      semigroupProd n (layerRead (sLetter s) x)
        = semigroupProd n (layerRead (sLetter s) y) :=
  fun x y h => by rw [h]

/-- **The Boolean postprocessing that recovers the layer**: the two promised
products are the consecutive powers `g^{L+r}` and `g^{L+r+1}`, so testing
against the larger one names the layer. -/
lemma decide_coe_semigroupProd_eq_layerOut {s : S}
    (hs : ∀ m, 0 < m → (s : WithOne S) ^ m ≠ (s : WithOne S) ^ (m + 1))
    (n : ℕ) :
    (fun x : Layers (n + 1) ((n + 1) / 2) => decide
        (((semigroupProd n (layerRead (sLetter s) x) : S) : WithOne S)
          = (s : WithOne S) ^ ((n + 1) + (n + 1) / 2 + 1)))
      = layerOut (n := n + 1) (r := (n + 1) / 2) := by
  classical
  set r : ℕ := (n + 1) / 2 with hr
  funext x
  have hcoe := coe_semigroupProd_sLetter s (n := n) (layerSet x)
  cases x with
  | inl S₀ =>
      rw [layerSet_inl] at hcoe
      rw [show layerRead (sLetter s) (Sum.inl S₀)
          = fun i => sLetter s (decide (i ∈ (S₀.val : Finset (Fin (n + 1)))))
        from rfl, hcoe, S₀.2, layerOut_inl]
      exact decide_eq_false (hs ((n + 1) + r) (by omega))
  | inr T =>
      rw [layerSet_inr] at hcoe
      rw [show layerRead (sLetter s) (Sum.inr T)
          = fun i => sLetter s (decide (i ∈ (T.val : Finset (Fin (n + 1)))))
        from rfl, hcoe, T.2, layerOut_inr]
      exact decide_eq_true (by rw [show (n + 1) + (r + 1) = (n + 1) + r + 1
        from by omega])

/-- **The nonaperiodic semigroup lower bound**: with `s` a non-stabilising
element, the product of `n + 1` letters from `{s, s²}` — on the promise
"Hamming weight `⌊(n+1)/2⌋` or one more" — needs adversary value at least
`(n+1)/2`.  The two promised products are the *consecutive* powers
`g^{L+r}` and `g^{L+r+1}`, which a non-stabilising `g` separates. -/
theorem half_le_advPMOn_semigroupProd_of_nonaperiodic {s : S}
    (hs : ∀ m, 0 < m → (s : WithOne S) ^ m ≠ (s : WithOne S) ^ (m + 1))
    (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) / 2
      ≤ advPMOn (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s))
          (fun x => semigroupProd n
            (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s) x)) := by
  classical
  have hcomp := advPMOn_comp_le
    (f := fun x : Layers (n + 1) ((n + 1) / 2) =>
      semigroupProd n (layerRead (sLetter s) x))
    (det_semigroupProd_layerRead s n ((n + 1) / 2))
    (fun t : S => decide ((t : WithOne S)
      = (s : WithOne S) ^ ((n + 1) + (n + 1) / 2 + 1)))
  rw [decide_coe_semigroupProd_eq_layerOut hs n] at hcomp
  exact (half_le_advPMOn_layerOut (sLetter_injective hs) (by omega)).trans hcomp

/-- The total-function form. -/
theorem half_le_advPM_semigroupProd_of_nonaperiodic {s : S}
    (hs : ∀ m, 0 < m → (s : WithOne S) ^ m ≠ (s : WithOne S) ^ (m + 1))
    (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) / 2
      ≤ advPM (fun w : Fin (n + 1) → S => semigroupProd n w) :=
  (half_le_advPMOn_semigroupProd_of_nonaperiodic hs n).trans
    (advPMOn_le_advPM_of_injective
      (layerRead_injective (sLetter_injective hs)) fun _ => rfl)

/-- **The trichotomy's opening clause, lower half**: every finite
nonaperiodic **semigroup** needs `Ω(n)` adversary value. -/
theorem half_le_advPM_semigroupProd_of_not_aperiodic
    (h : ¬ IsAperiodicSemigroup S) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) / 2
      ≤ advPM (fun w : Fin (n + 1) → S => semigroupProd n w) := by
  obtain ⟨s, hs⟩ := exists_nonaperiodic_semigroup_elem h
  exact half_le_advPM_semigroupProd_of_nonaperiodic hs n

end Semigroup

end MonoidProduct
