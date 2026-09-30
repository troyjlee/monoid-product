import MonoidProduct.Trichotomy.Main
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# The aperiodicity index and its lower bound

The paper's aperiodicity index (defined just before
`thm:aperiodicity-index-lower`) and that theorem.

The **aperiodicity index** `ι(M)` of a finite aperiodic monoid is the least
`k ≥ 1` with `x^k = x^{k+1}` for every `x`; a uniform exponent exists because
the elementwise ones are finitely many (`exists_uniform_stab`), and `Nat.find`
picks the least.  Below the index some element still moves: for `r < ι(M)`
there is `g` with `g^r ≠ g^{r+1}` (`exists_pow_ne_of_lt_aperiodicIndex`; at
`r = 0` this is nontriviality).

The lower bound is the two-layer certificate of `Layer/Lower.lean` exactly as
the trichotomy uses it (`layerTheta_le_advPMOn_prodFun`): letters `{1, g}`,
weights `r` against `r + 1`, adversary value `√((n − r)(r + 1))`.  Choosing
`r = min{ι − 1, ⌊n/2⌋}` gives `(n − r)(r + 1) ≥ n·min{n, ι}/4`
(`index_layer_bound`), hence

`sqrt_index_le_advPM_prodFun : √(n·min{n, ι(M)}) / 2 ≤ ADV±(Prod_{M,n})`

for every nontrivial finite aperiodic monoid and `n ≥ 1`, over the two-letter
alphabet and after a Boolean postprocessing, as the paper states.  The
operational form is in `Quantum/Applications.lean` (`index_qQuery_lower`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

section Index

variable [IsAperiodicMonoid M]

/-- A uniform stabilization exponent exists: the maximum of the elementwise
ones (or `1`). -/
lemma exists_uniform_stab : ∃ k : ℕ, 1 ≤ k ∧ ∀ x : M, x ^ k = x ^ (k + 1) := by
  classical
  choose N hN using fun x : M => IsAperiodicMonoid.stabilizes x
  refine ⟨max 1 (Finset.univ.sup N), le_max_left _ _, fun x => ?_⟩
  exact pow_stab (hN x).2
    (le_trans (Finset.le_sup (f := N) (Finset.mem_univ x)) (le_max_right _ _))

/-- **The aperiodicity index** `ι(M)`: the least `k ≥ 1` with `x^k = x^{k+1}`
for every `x`. -/
noncomputable def aperiodicIndex (M : Type) [Monoid M] [Fintype M] [DecidableEq M]
    [IsAperiodicMonoid M] : ℕ :=
  Nat.find (exists_uniform_stab (M := M))

lemma aperiodicIndex_spec :
    1 ≤ aperiodicIndex M ∧ ∀ x : M, x ^ aperiodicIndex M = x ^ (aperiodicIndex M + 1) :=
  Nat.find_spec (exists_uniform_stab (M := M))

lemma one_le_aperiodicIndex : 1 ≤ aperiodicIndex M := aperiodicIndex_spec.1

lemma pow_aperiodicIndex (x : M) : x ^ aperiodicIndex M = x ^ (aperiodicIndex M + 1) :=
  aperiodicIndex_spec.2 x

lemma aperiodicIndex_le {k : ℕ} (hk : 1 ≤ k) (h : ∀ x : M, x ^ k = x ^ (k + 1)) :
    aperiodicIndex M ≤ k :=
  Nat.find_min' _ ⟨hk, h⟩

/-- **Below the index some element still moves**: for `r < ι(M)` there is `g`
with `g^r ≠ g^{r+1}`.  At `r = 0` this is nontriviality. -/
lemma exists_pow_ne_of_lt_aperiodicIndex [Nontrivial M] {r : ℕ}
    (hr : r < aperiodicIndex M) : ∃ g : M, g ^ r ≠ g ^ (r + 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · obtain ⟨g, hg⟩ := exists_ne (1 : M)
    exact ⟨g, by rw [pow_zero, pow_one]; exact fun h => hg h.symm⟩
  · by_contra h
    push Not at h
    exact absurd (aperiodicIndex_le hr0 h) (not_le.mpr hr)

end Index

/-! ## The layer parameter -/

/-- The arithmetic behind the choice `r = min{ι − 1, ⌊n/2⌋}`:
`4(n − r)(r + 1) ≥ n·min{n, ι}`. -/
lemma index_layer_bound {n ι r : ℕ} (hι : 1 ≤ ι) (hr : r = min (ι - 1) (n / 2)) :
    n * min n ι ≤ 4 * ((n - r) * (r + 1)) := by
  have h1 : n ≤ 2 * (n - r) := by omega
  have h2 : min n ι ≤ 2 * (r + 1) := by omega
  calc n * min n ι ≤ (2 * (n - r)) * (2 * (r + 1)) := Nat.mul_le_mul h1 h2
    _ = 4 * ((n - r) * (r + 1)) := by ring

/-- The layer value dominates `√(n·min{n, ι})/2` at `r = min{ι − 1, ⌊n/2⌋}`. -/
lemma sqrt_index_le_layerTheta {n ι r : ℕ} (hι : 1 ≤ ι) (hr : r = min (ι - 1) (n / 2)) :
    Real.sqrt ((n * min n ι : ℕ) : ℝ) / 2 ≤ layerTheta n r := by
  have h4 : ((n * min n ι : ℕ) : ℝ) ≤ 4 * (((n - r) * (r + 1) : ℕ) : ℝ) := by
    exact_mod_cast index_layer_bound hι hr
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [layerTheta, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc Real.sqrt ((n * min n ι : ℕ) : ℝ)
      ≤ Real.sqrt (4 * (((n - r) * (r + 1) : ℕ) : ℝ)) := Real.sqrt_le_sqrt h4
    _ = 2 * Real.sqrt (((n - r) * (r + 1) : ℕ) : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), hsqrt4]
    _ = Real.sqrt (((n - r) * (r + 1) : ℕ) : ℝ) * 2 := mul_comm _ _

/-! ## The lower bound -/

section Lower

variable [IsAperiodicMonoid M] [Nontrivial M] {n : ℕ}

/-- **Theorem `thm:aperiodicity-index-lower`, at the `ADV±` level**: for a
nontrivial finite aperiodic monoid and `n ≥ 1`,
`√(n·min{n, ι(M)}) / 2 ≤ ADV±(Prod_{M,n})`, already for the two-letter
alphabet `{1, g}` on the layer promise and a Boolean postprocessing. -/
theorem sqrt_index_le_advPMOn_prodFun (hn : 1 ≤ n) :
    ∃ g : M, g ≠ 1 ∧
      g ^ min (aperiodicIndex M - 1) (n / 2)
        ≠ g ^ (min (aperiodicIndex M - 1) (n / 2) + 1) ∧
      Real.sqrt ((n * min n (aperiodicIndex M) : ℕ) : ℝ) / 2
        ≤ advPMOn (layerRead (n := n) (r := min (aperiodicIndex M - 1) (n / 2)) (gLetter g))
            (fun x => wordProd (id : M → M)
              (layerRead (n := n) (r := min (aperiodicIndex M - 1) (n / 2))
                (gLetter g) x)) := by
  have hι := one_le_aperiodicIndex (M := M)
  have hrι : min (aperiodicIndex M - 1) (n / 2) < aperiodicIndex M := by omega
  obtain ⟨g, hg⟩ := exists_pow_ne_of_lt_aperiodicIndex hrι
  have hg1 : g ≠ 1 := fun h => hg (by rw [h, one_pow, one_pow])
  have hrn : min (aperiodicIndex M - 1) (n / 2) + 1 ≤ n := by omega
  refine ⟨g, hg1, hg, ?_⟩
  exact (sqrt_index_le_layerTheta hι rfl).trans (layerTheta_le_advPMOn_prodFun hg1 hg hrn)

/-- **Theorem `thm:aperiodicity-index-lower`** for the honest total product
over the full alphabet: `√(n·min{n, ι(M)}) / 2 ≤ ADV±(Prod_{M,n})`. -/
theorem sqrt_index_le_advPM_prodFun (hn : 1 ≤ n) :
    Real.sqrt ((n * min n (aperiodicIndex M) : ℕ) : ℝ) / 2
      ≤ advPM (fun w : Fin n → M => wordProd (id : M → M) w) := by
  obtain ⟨g, hg1, -, h⟩ := sqrt_index_le_advPMOn_prodFun (M := M) hn
  exact h.trans (advPMOn_le_advPM_of_injective
    (layerRead_injective (gLetter_injective hg1)) fun _ => rfl)

end Lower

end MonoidProduct
