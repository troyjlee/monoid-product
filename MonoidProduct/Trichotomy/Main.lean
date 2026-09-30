import MonoidProduct.Layer.Lower
import MonoidProduct.Aperiodic.EqProd
import QuantumQueryComplexity.Promise.Transport
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The fixed finite-monoid trichotomy (finite monoids)

`monoid.tex` Theorem `thm:fixed-monoid-trichotomy`.  At fixed monoid size the
product problem has three regimes,

    0,   Θ̃_M(√n),   Θ_M(n),

according as `M` is trivial, nontrivial aperiodic, or nonaperiodic.  This
file proves all three **lower** bounds at the `ADV±` level
(`trichotomy_lower_bounds`); the headline is the nonaperiodic regime, where a
monoid with a non-stabilising element needs *linear* adversary value, so the
AGS `√n` upper bound cannot extend past aperiodicity.

Not covered here: the paper's opening clause about finite nonaperiodic
**semigroups** (see `trichotomy_lower_bounds`'s docstring).

The construction is the paper's: pick `g` with `gᵐ ≠ gᵐ⁺¹` for every `m > 0`
(this is exactly `¬ IsAperiodicMonoid M`, by `exists_nonaperiodic_elem`; the
paper obtains it from a nontrivial subgroup, where cancellation gives it).
Restrict the letters to `{1, g}` and promise Hamming weight `r` or `r+1`
with `r = ⌊n/2⌋`.  The product of such a word is `g^weight`
(`orderedProd_gLetter`), so the two promised products are `g^r` and `g^{r+1}`
— **distinct**, and told apart by the Boolean postprocessing
`m ↦ decide (m = g^{r+1})`.  The two-layer inclusion-matrix certificate
(`MonoidProduct/Layer/Lower.lean`) then gives `n/2 ≤ ADV±ₚ`, and
`advPMOn_comp_le` moves it from the layer test to the product itself.

Headlines: `half_le_advPMOn_prodFun_of_nonaperiodic` (parametric in `g`),
`half_le_advPMOn_prodFun_of_not_aperiodic` (from `¬ IsAperiodicMonoid`), and
the total-function form `half_le_advPM_prodFun_of_not_aperiodic` via
`advPMOn_le_advPM_of_injective`.  The matching `O(n)` upper bound is reading
every letter; the operational corollaries live in `Quantum/Applications.lean`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open scoped Classical

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The product of a two-letter word -/

/-- The alphabet `{1, g}`, named by a bit. -/
def gLetter (g : M) : Bool → M := fun b => if b then g else 1

@[simp] lemma gLetter_true (g : M) : gLetter g true = g := rfl

@[simp] lemma gLetter_false (g : M) : gLetter g false = 1 := rfl

lemma gLetter_injective {g : M} (hg : g ≠ 1) : Function.Injective (gLetter g) := by
  intro b b' hbb
  cases b <;> cases b'
  · rfl
  · exact absurd (show g = 1 from hbb.symm) hg
  · exact absurd (show g = 1 from hbb) hg
  · rfl

variable {n : ℕ}

/-- The prefix products of an indicator word: each marked position
contributes one factor `g`. -/
private lemma rangeProd_gLetter (g : M) (S : Finset (Fin n)) (m : ℕ) :
    rangeProd (fun i : Fin n => if i ∈ S then g else 1) 0 m
      = g ^ (S.filter fun i : Fin n => (i : ℕ) < m).card := by
  classical
  induction m with
  | zero =>
      rw [rangeProd_self, Finset.filter_false_of_mem (fun i _ => by omega),
        Finset.card_empty, pow_zero]
  | succ m ih =>
      rw [rangeProd_succ_right _ (Nat.zero_le m), ih]
      by_cases hm : m < n
      · rw [padAt_of_lt _ hm]
        by_cases hmem : (⟨m, hm⟩ : Fin n) ∈ S
        · rw [if_pos hmem]
          have hfil : (S.filter fun i : Fin n => (i : ℕ) < m + 1)
              = insert (⟨m, hm⟩ : Fin n) (S.filter fun i : Fin n => (i : ℕ) < m) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hiS, hlt⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
              · exact Or.inr ⟨hiS, h⟩
              · exact Or.inl (Fin.ext h)
            · rintro (rfl | ⟨hiS, hlt⟩)
              · exact ⟨hmem, Nat.lt_succ_self m⟩
              · exact ⟨hiS, Nat.lt_succ_of_lt hlt⟩
          rw [hfil, Finset.card_insert_of_notMem (by simp), pow_succ]
        · rw [if_neg hmem, mul_one]
          congr 2
          ext i
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hiS, hlt⟩
            exact ⟨hiS, Nat.lt_succ_of_lt hlt⟩
          · rintro ⟨hiS, hlt⟩
            refine ⟨hiS, ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
            · exact h
            · exact absurd ((Fin.ext h : i = (⟨m, hm⟩ : Fin n)) ▸ hiS) hmem
      · rw [padAt_of_le _ (by omega), mul_one]
        congr 2
        ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hiS, hlt⟩
          exact ⟨hiS, Nat.lt_succ_of_lt hlt⟩
        · rintro ⟨hiS, hlt⟩
          exact ⟨hiS, lt_of_lt_of_le i.isLt (not_lt.mp hm)⟩

/-- **The product of a `{1, g}`-word is `g` to the number of marked
positions.** -/
lemma orderedProd_gLetter (g : M) (S : Finset (Fin n)) :
    orderedProd (fun i : Fin n => if i ∈ S then g else 1) = g ^ S.card := by
  classical
  rw [orderedProd_eq_rangeProd, rangeProd_gLetter]
  congr 2
  exact Finset.filter_true_of_mem fun i _ => i.isLt

variable {r : ℕ}

/-- The promise product, read through the two-letter alphabet. -/
lemma wordProd_layerRead (g : M) (x : Layers n r) :
    wordProd (id : M → M) (layerRead (gLetter g) x)
      = g ^ (layerSet x).card := by
  rw [wordProd]
  have hfun : (fun i => id (layerRead (gLetter g) x i))
      = fun i : Fin n => if i ∈ layerSet x then g else 1 := by
    funext i
    simp only [id_eq, layerRead, gLetter, decide_eq_true_eq]
  rw [hfun, orderedProd_gLetter]

/-- **The Boolean postprocessing that recovers the layer from the product**:
the two promised products `g^r` and `g^{r+1}` are distinct, so testing the
product against `g^{r+1}` names the layer. -/
lemma decide_wordProd_eq_layerOut {g : M} (hne : g ^ r ≠ g ^ (r + 1)) :
    (fun x : Layers n r => decide
        (wordProd (id : M → M) (layerRead (gLetter g) x) = g ^ (r + 1)))
      = layerOut (n := n) (r := r) := by
  funext x
  rw [wordProd_layerRead]
  cases x with
  | inl S =>
      rw [layerSet_inl, S.2, layerOut_inl]
      exact decide_eq_false hne
  | inr T =>
      rw [layerSet_inr, T.2, layerOut_inr]
      exact decide_eq_true rfl

/-- Read-determinacy of the promise product. -/
lemma det_wordProd_layerRead (g : M) :
    ∀ x y : Layers n r,
      layerRead (gLetter g) x = layerRead (gLetter g) y →
      wordProd (id : M → M) (layerRead (gLetter g) x)
        = wordProd (id : M → M) (layerRead (gLetter g) y) :=
  fun x y h => by rw [h]

/-! ## The nonaperiodic lower bound -/

/-- Not being an aperiodic monoid means exactly: some element's powers never
stabilise. -/
lemma exists_nonaperiodic_elem (h : ¬ IsAperiodicMonoid M) :
    ∃ g : M, ∀ m, 0 < m → g ^ m ≠ g ^ (m + 1) := by
  by_contra hc
  push Not at hc
  exact h ⟨fun a => by
    obtain ⟨m, hm, hme⟩ := hc a
    exact ⟨m, hm, hme⟩⟩

/-- A non-stabilising element is not the identity. -/
lemma ne_one_of_nonaperiodic {g : M} (hg : ∀ m, 0 < m → g ^ m ≠ g ^ (m + 1)) :
    g ≠ 1 := by
  intro h1
  exact hg 1 one_pos (by rw [h1, one_pow, one_pow])

/-- **The nonaperiodic lower bound** (`monoid.tex`
Theorem `thm:fixed-monoid-trichotomy`, the `Θ(n)` regime): with `g` a
non-stabilising element, the product of `n` letters from `{1, g}` — on the
promise "Hamming weight `⌊n/2⌋` or `⌊n/2⌋+1`" — needs adversary value at
least `n/2`.  Linear, so *no* `√n` upper bound survives past aperiodicity.

The bound already holds for the Boolean postprocessing
`m ↦ decide (m = g^{⌊n/2⌋+1})` of the product. -/
theorem layerTheta_le_advPMOn_prodFun {g : M} (hg1 : g ≠ 1)
    (hne : g ^ r ≠ g ^ (r + 1)) (hr : r + 1 ≤ n) :
    layerTheta n r
      ≤ advPMOn (layerRead (n := n) (r := r) (gLetter g))
          (fun x => wordProd (id : M → M)
            (layerRead (n := n) (r := r) (gLetter g) x)) := by
  classical
  have hcomp := advPMOn_comp_le (f := fun x : Layers n r =>
      wordProd (id : M → M) (layerRead (gLetter g) x))
    (det_wordProd_layerRead g) (fun m => decide (m = g ^ (r + 1)))
  rw [decide_wordProd_eq_layerOut hne] at hcomp
  exact (sqrt_le_advPMOn_layerOut (gLetter_injective hg1) hr).trans hcomp

/-- The `Θ(n)` regime, at the balanced split `r = ⌊n/2⌋`. -/
theorem half_le_advPMOn_prodFun_of_nonaperiodic {g : M}
    (hg : ∀ m, 0 < m → g ^ m ≠ g ^ (m + 1)) (hn : 2 ≤ n) :
    ((n : ℝ)) / 2
      ≤ advPMOn (layerRead (n := n) (r := n / 2) (gLetter g))
          (fun x => wordProd (id : M → M)
            (layerRead (n := n) (r := n / 2) (gLetter g) x)) :=
  (half_le_layerTheta (by omega)).trans
    (layerTheta_le_advPMOn_prodFun (ne_one_of_nonaperiodic hg)
      (hg (n / 2) (by omega)) (by omega))

/-- The same bound from the structural hypothesis: `M` is **not** an
aperiodic monoid. -/
theorem half_le_advPMOn_prodFun_of_not_aperiodic (h : ¬ IsAperiodicMonoid M)
    (hn : 2 ≤ n) :
    ∃ g : M, ((n : ℝ)) / 2
      ≤ advPMOn (layerRead (n := n) (r := n / 2) (gLetter g))
          (fun x => wordProd (id : M → M)
            (layerRead (n := n) (r := n / 2) (gLetter g) x)) := by
  obtain ⟨g, hg⟩ := exists_nonaperiodic_elem h
  exact ⟨g, half_le_advPMOn_prodFun_of_nonaperiodic hg hn⟩

/-- **The total-function form**: the promise certificate transfers along the
injective encoding, so the honest product function `Prod_{M,n}` over the
two-letter alphabet is itself linear-hard. -/
theorem half_le_advPM_prodFun_of_nonaperiodic {g : M}
    (hg : ∀ m, 0 < m → g ^ m ≠ g ^ (m + 1)) (hn : 2 ≤ n) :
    ((n : ℝ)) / 2
      ≤ advPM (fun w : Fin n → M => wordProd (id : M → M) w) :=
  (half_le_advPMOn_prodFun_of_nonaperiodic hg hn).trans
    (advPMOn_le_advPM_of_injective
      (layerRead_injective (gLetter_injective (ne_one_of_nonaperiodic hg)))
      fun _ => rfl)

theorem half_le_advPM_prodFun_of_not_aperiodic (h : ¬ IsAperiodicMonoid M)
    (hn : 2 ≤ n) :
    ((n : ℝ)) / 2 ≤ advPM (fun w : Fin n → M => wordProd (id : M → M) w) := by
  obtain ⟨g, hg⟩ := exists_nonaperiodic_elem h
  exact half_le_advPM_prodFun_of_nonaperiodic hg hn

/-! ## The `Ω(√n)` regime: every nontrivial monoid

At `r = 0` the two layers are the empty set and the singletons — the
**promised Or** — and `layerTheta n 0 = √n`.  The two promised products are
then `g⁰ = 1` and `g¹ = g`, distinct for any `g ≠ 1`, so the same certificate
applies with no aperiodicity hypothesis at all. -/

lemma layerTheta_zero (n : ℕ) : layerTheta n 0 = Real.sqrt n := by
  rw [layerTheta]
  norm_num

/-- **Every nontrivial monoid needs `Ω(√n)`**: the promised `Or` embedded in
the alphabet `{1, g}`. -/
theorem sqrt_le_advPMOn_prodFun_of_ne_one {g : M} (hg1 : g ≠ 1) (hn : 1 ≤ n) :
    Real.sqrt n
      ≤ advPMOn (layerRead (n := n) (r := 0) (gLetter g))
          (fun x => wordProd (id : M → M)
            (layerRead (n := n) (r := 0) (gLetter g) x)) := by
  rw [← layerTheta_zero n]
  refine layerTheta_le_advPMOn_prodFun hg1 ?_ (by omega)
  rw [pow_zero, pow_one]
  exact fun h => hg1 h.symm

theorem sqrt_le_advPM_prodFun_of_ne_one {g : M} (hg1 : g ≠ 1) (hn : 1 ≤ n) :
    Real.sqrt n ≤ advPM (fun w : Fin n → M => wordProd (id : M → M) w) :=
  (sqrt_le_advPMOn_prodFun_of_ne_one hg1 hn).trans
    (advPMOn_le_advPM_of_injective
      (layerRead_injective (gLetter_injective hg1)) fun _ => rfl)

/-! ## The trivial regime -/

/-- **A trivial monoid costs nothing**: the product is constant. -/
theorem advPM_prodFun_of_subsingleton [Subsingleton M] :
    advPM (fun w : Fin n → M => wordProd (id : M → M) w) = 0 :=
  advPM_eq_zero_of_forall_eq fun x y => Subsingleton.elim _ _

/-! ## The trichotomy, at the `ADV±` level

The `O_M(√n · polylog)` upper bound of the middle regime is
`advPM_wordProd_le` (`Aperiodic/Induction.lean`, the AGS route); the `O(n)`
upper bound of the last is reading every letter
(`nonaperiodic_qQuery_upper`, `Quantum/Applications.lean`). -/

/-- **The fixed finite-monoid trichotomy, all three regimes**
(`monoid.tex` Theorem `thm:fixed-monoid-trichotomy`, lower bounds): a trivial
monoid costs nothing; every nontrivial one costs `Ω(√n)`; every
**nonaperiodic** one costs `Ω(n)`.

Scope, on the record: this is the *finite monoid* statement.  The paper's
opening clause — every finite nonaperiodic **semigroup** has `Θ_S(n)` — is in
`Trichotomy/Semigroup.lean`, with the operational bound
`qQuery_semigroupProd_lower_of_not_aperiodic` in `Quantum/Applications.lean`;
it uses a subgroup identity `e` in place of `1` as the neutral letter. -/
theorem trichotomy_lower_bounds (hn : 2 ≤ n) :
    (Subsingleton M →
        advPM (fun w : Fin n → M => wordProd (id : M → M) w) = 0)
      ∧ (∀ g : M, g ≠ 1 →
        Real.sqrt n ≤ advPM (fun w : Fin n → M => wordProd (id : M → M) w))
      ∧ (¬ IsAperiodicMonoid M →
        ((n : ℝ)) / 2
          ≤ advPM (fun w : Fin n → M => wordProd (id : M → M) w)) :=
  ⟨fun h => @advPM_prodFun_of_subsingleton M _ _ _ n h,
    fun g hg1 => sqrt_le_advPM_prodFun_of_ne_one hg1 (by omega),
    fun h => half_le_advPM_prodFun_of_not_aperiodic h hn⟩

end MonoidProduct
