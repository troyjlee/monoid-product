import QuantumQueryComplexity.Quantum.LowerBound.MainBool
import QuantumQueryComplexity.Quantum.FiniteOutput
import QuantumQueryComplexity.Quantum.ReadAll
import QuantumQueryComplexity.Quantum.UniformHasDual
import MonoidProduct.Capped.Theta
import MonoidProduct.Tropical.Lower
import MonoidProduct.UT.Main
import MonoidProduct.Simon.Main
import MonoidProduct.Quantum.Division
import MonoidProduct.Trichotomy.Main
import MonoidProduct.Trichotomy.Index
import MonoidProduct.Trichotomy.Semigroup
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Applications: operational lower bounds

The adversary lower bounds of this library, pushed through the
adversary-to-query bound (`mul_advPMOn_le_qQueryOn_of_error_sixteenth`:
`7/32 · ADV± ≤ Q_{1/16}`) into genuine quantum query complexity:

* **capped counters** — `7/128·√(n·min{n,kr}) ≤ Q_{1/16}(Prod_{M_{k,r},n})`
  (`capped_qQuery_lower`).

**The tropical product** (Section `sec:tropical`; the lower bound,
operational).  The postprocessing bridge
(`qQueryOn_postcomp_le`: classical postprocessing of the readout is free,
from `ComputesWithErrorOn.postcomp`) hands any algorithm for the
matrix-valued promise product to the Boolean parity of the marked blocks,
where the fixed-error lower bounds apply:
`7/32·√(nd/2) ≤ Q_{1/16}(Prod_{U_k(T),n})`
(`tropical_qQuery_lower_sixteenth`) and, by the sharp Boolean `1/3` bound,
`1/36·√(nd/2) ≤ Q_{1/3}(Prod_{U_k(T),n})`, `d = min{k−1, n}`
(`tropical_qQuery_lower`, `tropical_qQuery_lower_min`).  The bridge is
forced *by the current library*, on the **lower-bound** side, for one
reason: the product's output type `TMat k` is generally infinite, while
the finite-output lower bounds assume `Fintype O` — including the
conventional-error bound `(7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f)`
(`Quantum/Plurality.lean`), which closed the former plurality gap.  That is
a library gap, not a theorem that no other route exists.  (The
uniform extraction removed the cardinality factors of the **upper**
extraction — `√|σ|`, the output encoding — and does not touch this
lower-bound limitation.)

**The fixed finite-monoid trichotomy's lower bounds**
(`thm:fixed-monoid-trichotomy`), operationally: `nonaperiodic_qQuery_lower` and `nontrivial_qQuery_lower`
(with `_total` forms over the full alphabet `M`, and structural forms from
`¬ IsAperiodicMonoid` / `¬ Subsingleton`), and for **semigroups**
`nonaperiodic_semigroup_qQuery_lower_total` with its matching read-everything
upper bound `nonaperiodic_semigroup_qQuery_upper`, giving

    (1/36)·(n+1)/2 ≤ Q_{1/3}(semigroupProd n) ≤ n+1.

**The Boolean unitriangular product** (the paper's
Theorem `thm:boolean-unitriangular`, operational, both halves):
`1/36·√(n·min{n,⌊k²/4⌋}/2) ≤ Q_{1/3}(Prod_{UT_k(𝔹),n}) ≤ min{n,
8192(1 + 8√(n·min{n, C(k,2)}))}` — the upper bound through the
cardinality-free extraction on the bounded-change-scan dual,
the lower bound through the cross-edge disjoint search and the parity
postprocessing — i.e. `Θ(min{n, k√n})` (`ut_qQuery_sandwich`); and the
`k = 1` endpoint `ut_qQuery_eq_zero_dim_one`; and the **conditional
division theorem** `qQuery_le_of_but_division` (alias
`jtrivial_qQuery_le_of_division`): from a supplied division witness
`M ≺ UT_k(𝔹)`, `Q_{1/3}(Prod_{M,n}) ≤ 2·8192(1 + 8√(n·min{n, C(k,2)}))` by
the division compiler.  No 𝓙-triviality is assumed; Simon's theorem,
which supplies the witness, is not used by this statement.

Every `Q` here is the project's **native transposition-oracle** complexity.
Conventional-oracle equivalence is formalized for Boolean alphabets via the
XOR oracle (`Quantum/Simulation.lean`) and, for arbitrary finite alphabets,
via the canonical one-hot XOR model (`Quantum/OneHotSimulation.lean`, a
direct factor two each way); the tropical, unitriangular and 𝓙-trivial
headlines below are transported into that model in
`Quantum/OneHotApplications.lean`.

This file deliberately sits outside the generic `QuantumQueryComplexity.Quantum`
aggregate: it is an application layer importing both the quantum model and
the adversary constructions.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## Capped counters -/

section Capped

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ] [Nonempty ρ]

/-- **The capped-counter product needs `Ω(√(n·min{n,kr}))` quantum
queries.** -/
theorem capped_qQuery_lower {k : ℕ} (hk : 0 < k) :
    (7 / 128 : ℝ) * Real.sqrt ((Fintype.card ι : ℝ)
        * (min (Fintype.card ι) (k * Fintype.card ρ) : ℕ))
      ≤ (qQueryOn (id : (ι → (ρ → Capped k)) → ι → (ρ → Capped k))
          (fun x => ∏ i, x i) (1 / 16) : ℝ) := by
  have hdet : ∀ x y : ι → (ρ → Capped k),
      id x = id y → (∏ i, x i) = ∏ i, y i :=
    fun x y hxy => by rw [show x = y from hxy]
  have hA := mul_advPMOn_le_qQueryOn_of_error_sixteenth
    (read := (id : (ι → (ρ → Capped k)) → ι → (ρ → Capped k)))
    (f := fun x : ι → (ρ → Capped k) => ∏ i, x i) hdet
  replace hA : (7 / 32 : ℝ) * advPM (fun x : ι → ρ → Capped k => ∏ i, x i)
      ≤ (qQueryOn (id : (ι → (ρ → Capped k)) → ι → (ρ → Capped k))
          (fun x => ∏ i, x i) (1 / 16) : ℝ) := hA
  have hlow := (advPM_cappedProd_sandwich (ι := ι) (ρ := ρ) hk).1
  calc (7 / 128 : ℝ) * Real.sqrt ((Fintype.card ι : ℝ)
        * (min (Fintype.card ι) (k * Fintype.card ρ) : ℕ))
      = (7 / 32) * (Real.sqrt ((Fintype.card ι : ℝ)
          * (min (Fintype.card ι) (k * Fintype.card ρ) : ℕ)) / 4) := by
        ring
    _ ≤ (7 / 32) * advPM (fun x : ι → ρ → Capped k => ∏ i, x i) :=
        mul_le_mul_of_nonneg_left hlow (by norm_num)
    _ ≤ _ := hA

end Capped

/-! ## The tropical product -/

section Tropical

variable {k n d : ℕ}

/-- The parity of the marked blocks is a classical postprocessing of the
promise product, so its query complexity bounds the product's from below at
every error. -/
private lemma tropical_parity_bridge (hd : 0 < d) (hdk : d < k) {ε : ℝ}
    (hε : 0 ≤ ε) :
    qQueryOn (dsRead (modBlk n d hd)) (dsFun (modBlk n d hd)) ε
      ≤ qQueryOn (dsRead (modBlk n d hd))
          (fun x => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
            (dsRead (modBlk n d hd) x)) ε := by
  have hemb : ∀ c : Fin d, (c : ℕ) + 1 < k := fun c => by
    have := c.isLt
    omega
  have hdet : ∀ x y : DsMarks (modBlk n d hd),
      dsRead (modBlk n d hd) x = dsRead (modBlk n d hd) y →
      linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
          (dsRead (modBlk n d hd) x)
        = linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
            (dsRead (modBlk n d hd) y) :=
    fun x y h => by rw [h]
  have h := qQueryOn_postcomp_le
    (slotParity (fun c : Fin d => (c : ℕ)) hemb)
    (queryCounts_nonempty hdet hε)
  rwa [show (fun x => slotParity (fun c : Fin d => (c : ℕ)) hemb
        (linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
          (dsRead (modBlk n d hd) x)))
      = dsFun (modBlk n d hd) from
    funext fun x =>
      slotParity_linProd_dsRead Fin.val_injective hemb x] at h

/-- The disjoint-search certificate, restated for the parity. -/
private lemma tropical_sqrt_le_advPMOn_dsFun (hd : 0 < d) (hdn : d ≤ n) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPMOn (dsRead (modBlk n d hd)) (dsFun (modBlk n d hd)) :=
  (sqrt_le_dsTheta hd hdn).trans
    (dsTheta_le_advPMOn_dsFun (modBlk n d hd) (modBlk_surjective hd hdn))

/-- **The tropical product needs `Ω(√(nd))` quantum queries at error
`1/16`**: the adversary lower bound on the Boolean parity, carried to the
matrix-valued promise product by the free postprocessing bridge.  (The
bridge is unavoidable here: the product's output type `TMat k` is
infinite, outside the `Fintype`-output lower bounds.) -/
theorem tropical_qQuery_lower_sixteenth (hd : 0 < d) (hdn : d ≤ n)
    (hdk : d < k) :
    (7 / 32 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (qQueryOn (dsRead (modBlk n d hd))
          (fun x => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
            (dsRead (modBlk n d hd) x)) (1 / 16) : ℝ) := by
  have hpar := mul_advPMOn_le_qQueryOn_of_error_sixteenth
    (read := dsRead (modBlk n d hd)) (f := dsFun (modBlk n d hd))
    (separates_of_injective (dsRead_injective (modBlk n d hd)) _)
  have hbridge := tropical_parity_bridge (k := k) (n := n) hd hdk
    (by norm_num : (0 : ℝ) ≤ 1 / 16)
  calc (7 / 32 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (7 / 32) * advPMOn (dsRead (modBlk n d hd)) (dsFun (modBlk n d hd)) :=
        mul_le_mul_of_nonneg_left
          (tropical_sqrt_le_advPMOn_dsFun hd hdn) (by norm_num)
    _ ≤ (qQueryOn (dsRead (modBlk n d hd)) (dsFun (modBlk n d hd))
          (1 / 16) : ℝ) := hpar
    _ ≤ _ := by exact_mod_cast hbridge

/-- **The tropical product at the conventional error**: any `1/3`-error
algorithm for the promise product computes the parity of the marked blocks
by classical postprocessing of its readout at no query cost, and the parity
is Boolean, where the sharp `1/3` lower bound applies:
`1/36·√(nd/2) ≤ Q_{1/3}(Prod_{U_k(T),n})`. -/
theorem tropical_qQuery_lower (hd : 0 < d) (hdn : d ≤ n) (hdk : d < k) :
    (1 / 36 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (qQueryOn (dsRead (modBlk n d hd))
          (fun x => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
            (dsRead (modBlk n d hd) x)) (1 / 3) : ℝ) := by
  have hpar := mul_advPMOn_le_qQueryOn_of_error_third
    (read := dsRead (modBlk n d hd)) (f := dsFun (modBlk n d hd))
    (separates_of_injective (dsRead_injective (modBlk n d hd)) _)
  have hbridge := tropical_parity_bridge (k := k) (n := n) hd hdk
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc (1 / 36 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (1 / 36) * advPMOn (dsRead (modBlk n d hd)) (dsFun (modBlk n d hd)) :=
        mul_le_mul_of_nonneg_left
          (tropical_sqrt_le_advPMOn_dsFun hd hdn) (by norm_num)
    _ ≤ (qQueryOn (dsRead (modBlk n d hd)) (dsFun (modBlk n d hd))
          (1 / 3) : ℝ) := hpar
    _ ≤ _ := by exact_mod_cast hbridge

/-- **The tropical product lower bound, operational**: with `d = min{k−1, n}`,
`Q_{1/3}(Prod_{U_k(T),n}) = Ω(√(n·min{k−1, n}))` — the `√n` of the tropical
product theorem is optimal up to the polylogarithmic factor, as a statement
about quantum algorithms. -/
theorem tropical_qQuery_lower_min (hk : 2 ≤ k) (hn : 0 < n)
    (hd : d = min (k - 1) n) :
    (1 / 36 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (qQueryOn (dsRead (modBlk n d (by omega)))
          (fun x => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
            (dsRead (modBlk n d (by omega)) x)) (1 / 3) : ℝ) :=
  tropical_qQuery_lower (by omega) (by omega) (by omega)

/-- **The honest total product over the generator alphabet**: the promise
bound restricts (`qQueryOn_comp_read_le_qQuery` — a total algorithm run on
the promised observations), so the total function
`w ↦ x₁ ⊗ ⋯ ⊗ xₙ` on `Fin n → Option (Fin d)` is itself hard.

Scope, on the record: the alphabet is the `d+1` generator letters used by
the hard instance, **not** all of `U_k(𝕋)`.  A theorem about the literal
full tropical alphabet is not expressible here at all: `QBasis` and
`qQuery` require a **finite** answer alphabet, and `U_k(𝕋)` is infinite for
`k ≥ 2`.  What the division-monotonicity compiler buys is uniformity over
*finite allowed subalphabets*; the literal full-alphabet statement needs a
separate infinite-alphabet model or wrapper. -/
theorem tropical_qQuery_lower_total (hd : 0 < d) (hdn : d ≤ n) (hdk : d < k) :
    (1 / 36 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (qQuery (fun w : Fin n → Option (Fin d) =>
          linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n w)
          (1 / 3) : ℝ) := by
  refine (tropical_qQuery_lower hd hdn hdk).trans ?_
  have hne : (QueryCounts (X := Fin n → Option (Fin d)) id
      (fun w => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n w)
      (1 / 3 : ℝ)).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [show x = y from h])
      (by norm_num)
  exact_mod_cast qQueryOn_comp_read_le_qQuery (dsRead (modBlk n d hd)) _ hne

end Tropical

/-! ## The Boolean unitriangular product -/

section UT

variable {k n : ℕ}

/-- The promise reading of the cross-edge hard instance over the **full**
alphabet `UT_k(𝔹)`: block `c` is the identity except for at most one copy
of the `c`-th cross-edge letter. -/
def utRead (k n d : ℕ) (hd : 0 < d) (hdk : d ≤ k / 2 * (k - k / 2)) :
    DsMarks (modBlk n d hd) → Fin n → BUT k :=
  fun x i => optBLetter (crossEdge k d hdk) (crossEdge_cross k d hdk)
    (dsRead (modBlk n d hd) x i)

lemma utRead_injective (k n d : ℕ) (hd : 0 < d)
    (hdk : d ≤ k / 2 * (k - k / 2)) :
    Function.Injective (utRead k n d hd hdk) := fun x y h =>
  dsRead_injective _ (funext fun i =>
    optBLetter_injective _ _ (crossEdge_injective k d hdk) (congrFun h i))

/-- **The `UT_k(𝔹)` product needs `Ω(√(n·min{n, ⌊k²/4⌋}))` quantum
queries at error `1/3`**: the parity of the marked blocks is Boolean, so
the sharp `1/3` bound applies; it is a free postprocessing of the promise
product; and a total algorithm runs on the promised observations. -/
theorem ut_qQuery_lower (hk : 2 ≤ k) (hn : 0 < n) {d : ℕ}
    (hd : d = min n (k ^ 2 / 4)) :
    (1 / 36 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ) := by
  have hprod : 1 ≤ k / 2 * (k - k / 2) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [← half_mul_sub_half] at hd
  have hd0 : 0 < d := by omega
  have hdn : d ≤ n := by omega
  have hdk : d ≤ k / 2 * (k - k / 2) := by omega
  have hinj := utRead_injective k n d hd0 hdk
  have hpar := mul_advPMOn_le_qQueryOn_of_error_third
    (read := utRead k n d hd0 hdk) (f := dsFun (modBlk n d hd0))
    (separates_of_injective hinj _)
  have hadv : Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPMOn (utRead k n d hd0 hdk) (dsFun (modBlk n d hd0)) := by
    show Real.sqrt _ ≤ advPMOn (fun x i => optBLetter (crossEdge k d hdk)
      (crossEdge_cross k d hdk) (dsRead (modBlk n d hd0) x i)) _
    rw [advPMOn_comp_injective
      (optBLetter_injective _ _ (crossEdge_injective k d hdk))]
    exact (sqrt_le_dsTheta hd0 hdn).trans
      (dsTheta_le_advPMOn_dsFun _ (modBlk_surjective hd0 hdn))
  have hdet : ∀ x y : DsMarks (modBlk n d hd0),
      utRead k n d hd0 hdk x = utRead k n d hd0 hdk y →
        wordProd (id : BUT k → BUT k) (utRead k n d hd0 hdk x)
          = wordProd (id : BUT k → BUT k) (utRead k n d hd0 hdk y) :=
    fun x y h => by rw [h]
  have hbridge := qQueryOn_postcomp_le (bslotParity (crossEdge k d hdk))
    (queryCounts_nonempty hdet (by norm_num : (0 : ℝ) ≤ 1 / 3))
  have hfun : (fun x : DsMarks (modBlk n d hd0) =>
        bslotParity (crossEdge k d hdk)
          (wordProd (id : BUT k → BUT k) (utRead k n d hd0 hdk x)))
      = dsFun (modBlk n d hd0) :=
    funext fun x =>
      bslotParity_wordProd_dsRead (crossEdge k d hdk) (crossEdge_cross k d hdk)
        (crossEdge_injective k d hdk) x
  rw [hfun] at hbridge
  have hne : (QueryCounts (X := Fin n → BUT k) id
      (fun w => wordProd (id : BUT k → BUT k) w) (1 / 3 : ℝ)).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [show x = y from h])
      (by norm_num)
  have hres := qQueryOn_comp_read_le_qQuery (utRead k n d hd0 hdk)
    (fun w : Fin n → BUT k => wordProd (id : BUT k → BUT k) w) hne
  calc (1 / 36 : ℝ) * Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ (1 / 36) * advPMOn (utRead k n d hd0 hdk) (dsFun (modBlk n d hd0)) :=
        mul_le_mul_of_nonneg_left hadv (by norm_num)
    _ ≤ (qQueryOn (utRead k n d hd0 hdk) (dsFun (modBlk n d hd0))
          (1 / 3) : ℝ) := hpar
    _ ≤ (qQueryOn (utRead k n d hd0 hdk)
          (fun x => wordProd (id : BUT k → BUT k) (utRead k n d hd0 hdk x))
          (1 / 3) : ℝ) := by exact_mod_cast hbridge
    _ ≤ _ := by exact_mod_cast hres

/-- **The `UT_k(𝔹)` product via the cardinality-free extraction**:
`Q_{1/3}(Prod_{UT_k(𝔹),n}) ≤ 8192(1 + 8√(n·min{n, C(k,2)}))`. -/
theorem ut_qQuery_upper :
    (qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ))) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_wordProd_but (id : BUT k → BUT k)).hasDualOn (by positivity)

/-- **Reading every letter**: `Q_{1/3}(Prod_{UT_k(𝔹),n}) ≤ n`. -/
theorem ut_qQuery_upper_length :
    qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) ≤ n := by
  have h := qQueryOn_le_card
    (read := (id : (Fin n → BUT k) → Fin n → BUT k))
    (f := fun w => wordProd (id : BUT k → BUT k) w)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **Theorem `thm:boolean-unitriangular` of the paper, operational**:
for `k ≥ 2` and `n ≥ 1`,

    1/36·√(n·min{n,⌊k²/4⌋}/2) ≤ Q_{1/3}(Prod_{UT_k(𝔹),n})
      ≤ min{n, 8192(1 + 8√(n·min{n, C(k,2)}))},

i.e. `Θ(min{n, k√n})` with universal constants, in the native model. -/
theorem ut_qQuery_sandwich (hk : 2 ≤ k) (hn : 0 < n) :
    (1 / 36 : ℝ) * Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ)
        ≤ (qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
      ∧ (qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
        ≤ min (n : ℝ) (uniformExtractionConstant
            * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)))) :=
  ⟨ut_qQuery_lower hk hn rfl,
   le_min (by exact_mod_cast ut_qQuery_upper_length) ut_qQuery_upper⟩

/-- **`UT_1(𝔹)` costs no queries**: the `k = 1` endpoint of the theorem. -/
theorem ut_qQuery_eq_zero_dim_one (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun w : Fin n → BUT 1 => wordProd id w) ε = 0 :=
  qQueryOn_const_eq_zero _ (c := (1 : BUT 1)) (fun _ => Subsingleton.elim _ _) hε

/-- **Products in a divisor of `UT_k(𝔹)`** (the paper's Corollary
`cor:jtrivial-division`, from a **supplied** division witness; no
𝓙-triviality is assumed): if `M ≺ UT_k(𝔹)` — a subsemigroup `T ≤ UT_k(𝔹)`
with a hom `T → M` split by a section — then
`Q_{1/3}(Prod_{M,n}) ≤ 2·8192(1 + 8√(n·min{n, C(k,2)}))`, by the
division compiler.  Simon's theorem, which supplies such a witness for
every finite 𝓙-trivial monoid, is proved in `Simon/Chain.lean`
and discharged in `jtrivial_qQuery_le` below; it is **not**
assumed here. -/
theorem qQuery_le_of_but_division {M : Type} [Monoid M] [Fintype M]
    [DecidableEq M] (hn : 1 ≤ n) (T : Subsemigroup (BUT k)) (φ : T →ₙ* M)
    (ψ : M → T) (hsec : ∀ m, φ (ψ m) = m) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ 2 * (uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)))) := by
  have h := qQuery_prodFun_le_of_division hn T φ ψ hsec
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h' : (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ 2 * (qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ) := by
    exact_mod_cast h
  exact h'.trans (mul_le_mul_of_nonneg_left ut_qQuery_upper (by norm_num))

/-- **The division corollary in the exact algebraic interface**: from
`SemigroupDivides M (BUT k)` — a subsemigroup of `UT_k(𝔹)` mapping onto
`M` — the same bound; the section is extracted classically.  Simon's
theorem discharges this interface (`semigroupDivides_but_tau`), giving the
unconditional `jtrivial_qQuery_le` / `jtrivial_qQuery_le_min` below. -/
theorem qQuery_le_of_semigroupDivides_but {M : Type} [Monoid M] [Fintype M]
    [DecidableEq M] (hn : 1 ≤ n) (h : SemigroupDivides M (BUT k)) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ 2 * (uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)))) := by
  obtain ⟨T, φ, ψ, hsec⟩ := h.exists_section
  exact qQuery_le_of_but_division hn T φ ψ hsec

/-- **The unconditional 𝓙-trivial theorem** (the paper's Corollary
`cor:jtrivial-division`, with Simon's theorem discharged): every finite
𝓙-trivial monoid `M` satisfies
`Q_{1/3}(Prod_{M,n}) ≤ 2·8192(1 + 8√(n·min{n, C(τ(M),2)}))`, i.e.
`O(min{n, τ(M)√n})`, where `τ(M)` is the least unitriangular division
degree. -/
theorem jtrivial_qQuery_le {M : Type} [Monoid M] [Fintype M] [DecidableEq M]
    (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ 2 * (uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ)))) :=
  qQuery_le_of_semigroupDivides_but hn (semigroupDivides_but_tau hJ)

/-- A divisor of `UT_1(𝔹)` is a subsingleton: the divided-into monoid has
one element. -/
lemma subsingleton_of_semigroupDivides_but_one {M : Type} [Monoid M]
    (h : SemigroupDivides M (BUT 1)) : Subsingleton M := by
  obtain ⟨T, φ, hφ⟩ := h
  refine ⟨fun m m' => ?_⟩
  obtain ⟨t, rfl⟩ := hφ m
  obtain ⟨t', rfl⟩ := hφ m'
  congr 1
  exact Subtype.ext (Subsingleton.elim _ _)

/-- **The unconditional 𝓙-trivial theorem in the paper's shape**
(the paper's Corollary `cor:jtrivial-division`):
`Q_{1/3}(Prod_{M,n}) ≤ min{n, 147456·√(n·min{n, C(τ(M),2)})}` — at
`τ(M) = 1` the divisor of `UT_1(𝔹)` is a subsingleton and the product is
constant, so the bound is `0` as displayed; otherwise `√(n·min{…}) ≥ 1`
absorbs the additive `1` of the raw compiler bound into the constant
`2·8192·9 = 147456`, and reading every letter caps the count by `n`. -/
theorem jtrivial_qQuery_le_min {M : Type} [Monoid M] [Fintype M] [DecidableEq M]
    (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
        (147456 * Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))) := by
  have hcard : qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) ≤ n := by
    have h := qQueryOn_le_card (read := (id : (Fin n → M) → Fin n → M))
      (f := fun w => wordProd (id : M → M) w)
      (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [Fintype.card_fin] at h
  refine le_min (by exact_mod_cast hcard) ?_
  rcases Nat.lt_or_ge (tau M hJ) 2 with h1 | h2
  · -- `τ(M) = 1`: the product is constant, so zero queries suffice
    have hτ : tau M hJ = 1 := by have := one_le_tau hJ; omega
    have : Subsingleton M :=
      subsingleton_of_semigroupDivides_but_one (hτ ▸ semigroupDivides_but_tau hJ)
    have h0 : qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) = 0 :=
      qQueryOn_const_eq_zero _ (c := (1 : M)) (fun _ => Subsingleton.elim _ _)
        (by norm_num)
    rw [h0, Nat.cast_zero]
    positivity
  · -- `τ(M) ≥ 2`: `√(n·min{n, C(τ,2)}) ≥ 1` absorbs the additive term
    have hC : 1 ≤ (tau M hJ).choose 2 := Nat.choose_pos h2
    have hmin : (1 : ℝ) ≤ ((min n ((tau M hJ).choose 2) : ℕ) : ℝ) := by
      exact_mod_cast le_min hn hC
    have hs1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by nlinarith [(by exact_mod_cast hn : (1 : ℝ) ≤ n)])
    have hraw := jtrivial_qQuery_le hJ hn
    rw [uniformExtractionConstant] at hraw
    linarith

/-- Alias of `qQuery_le_of_but_division` under its original name. -/
theorem jtrivial_qQuery_le_of_division {M : Type} [Monoid M] [Fintype M]
    [DecidableEq M] (hn : 1 ≤ n) (T : Subsemigroup (BUT k)) (φ : T →ₙ* M)
    (ψ : M → T) (hsec : ∀ m, φ (ψ m) = m) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ 2 * (uniformExtractionConstant
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)))) :=
  qQuery_le_of_but_division hn T φ ψ hsec

end UT

/-! ## The fixed finite-monoid trichotomy: the nonaperiodic regime -/

section Trichotomy

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] {n : ℕ}

/-- Testing the product against `g^{⌊n/2⌋+1}` is a classical postprocessing
of the readout, so it costs no extra queries. -/
private lemma trichotomy_layer_bridge {g : M} {r : ℕ}
    (hne : g ^ r ≠ g ^ (r + 1)) {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn (layerRead (n := n) (r := r) (gLetter g))
        (layerOut (n := n) (r := r)) ε
      ≤ qQueryOn (layerRead (n := n) (r := r) (gLetter g))
          (fun x => wordProd (id : M → M)
            (layerRead (n := n) (r := r) (gLetter g) x)) ε := by
  haveI : Nonempty M := ⟨1⟩
  have h := qQueryOn_postcomp_le (fun m : M => decide (m = g ^ (r + 1)))
    (queryCounts_nonempty (det_wordProd_layerRead (n := n) (r := r) g) hε)
  rwa [decide_wordProd_eq_layerOut hne] at h

/-- **A nonaperiodic monoid needs `Ω(n)` quantum queries** (the paper's
Theorem `thm:fixed-monoid-trichotomy`, the `Θ(n)` regime) — already for a
Boolean postprocessing of the product, at fixed error `1/16`. -/
theorem nonaperiodic_qQuery_lower_sixteenth {g : M}
    (hg : ∀ m, 0 < m → g ^ m ≠ g ^ (m + 1)) (hn : 2 ≤ n) :
    (7 / 32 : ℝ) * ((n : ℝ) / 2)
      ≤ (qQueryOn (layerRead (n := n) (r := n / 2) (gLetter g))
          (fun x => wordProd (id : M → M)
            (layerRead (n := n) (r := n / 2) (gLetter g) x)) (1 / 16) : ℝ) := by
  have hpar := mul_advPMOn_le_qQueryOn_of_error_sixteenth
    (read := layerRead (n := n) (r := n / 2) (gLetter g))
    (f := layerOut (n := n) (r := n / 2))
    (separates_of_injective
      (layerRead_injective (gLetter_injective (ne_one_of_nonaperiodic hg))) _)
  have hbridge := trichotomy_layer_bridge (n := n)
    (hg (n / 2) (by omega)) (by norm_num : (0 : ℝ) ≤ 1 / 16)
  calc (7 / 32 : ℝ) * ((n : ℝ) / 2)
      ≤ (7 / 32) * advPMOn (layerRead (n := n) (r := n / 2) (gLetter g))
          (layerOut (n := n) (r := n / 2)) :=
        mul_le_mul_of_nonneg_left
          (half_le_advPMOn_layerOut
            (gLetter_injective (ne_one_of_nonaperiodic hg)) (by omega))
          (by norm_num)
    _ ≤ (qQueryOn (layerRead (n := n) (r := n / 2) (gLetter g))
          (layerOut (n := n) (r := n / 2)) (1 / 16) : ℝ) := hpar
    _ ≤ _ := by exact_mod_cast hbridge

/-- The same at the conventional error, with the sharp Boolean constant:
`(1/36)·(n/2) ≤ Q_{1/3}(Prod_{M,n})` for nonaperiodic `M`. -/
theorem nonaperiodic_qQuery_lower {g : M}
    (hg : ∀ m, 0 < m → g ^ m ≠ g ^ (m + 1)) (hn : 2 ≤ n) :
    (1 / 36 : ℝ) * ((n : ℝ) / 2)
      ≤ (qQueryOn (layerRead (n := n) (r := n / 2) (gLetter g))
          (fun x => wordProd (id : M → M)
            (layerRead (n := n) (r := n / 2) (gLetter g) x)) (1 / 3) : ℝ) := by
  have hpar := mul_advPMOn_le_qQueryOn_of_error_third
    (read := layerRead (n := n) (r := n / 2) (gLetter g))
    (f := layerOut (n := n) (r := n / 2))
    (separates_of_injective
      (layerRead_injective (gLetter_injective (ne_one_of_nonaperiodic hg))) _)
  have hbridge := trichotomy_layer_bridge (n := n)
    (hg (n / 2) (by omega)) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc (1 / 36 : ℝ) * ((n : ℝ) / 2)
      ≤ (1 / 36) * advPMOn (layerRead (n := n) (r := n / 2) (gLetter g))
          (layerOut (n := n) (r := n / 2)) :=
        mul_le_mul_of_nonneg_left
          (half_le_advPMOn_layerOut
            (gLetter_injective (ne_one_of_nonaperiodic hg)) (by omega))
          (by norm_num)
    _ ≤ (qQueryOn (layerRead (n := n) (r := n / 2) (gLetter g))
          (layerOut (n := n) (r := n / 2)) (1 / 3) : ℝ) := hpar
    _ ≤ _ := by exact_mod_cast hbridge

/-- **Reading every letter suffices**: the matching `O(n)` upper bound, so
the nonaperiodic regime is `Θ(n)`. -/
theorem nonaperiodic_qQuery_upper (g : M) {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn (layerRead (n := n) (r := n / 2) (gLetter g))
        (fun x => wordProd (id : M → M)
          (layerRead (n := n) (r := n / 2) (gLetter g) x)) ε ≤ n := by
  haveI : Nonempty M := ⟨1⟩
  have h := qQueryOn_le_card
    (read := layerRead (n := n) (r := n / 2) (gLetter g))
    (f := fun x => wordProd (id : M → M)
      (layerRead (n := n) (r := n / 2) (gLetter g) x))
    (det_wordProd_layerRead (n := n) (r := n / 2) g) hε
  rwa [Fintype.card_fin] at h

/-- **Every nontrivial monoid needs `Ω(√n)` quantum queries**: the promised
`Or` embedded in the alphabet `{1, g}` — the middle regime's lower half, with
no aperiodicity hypothesis. -/
theorem nontrivial_qQuery_lower {g : M} (hg1 : g ≠ 1) (hn : 1 ≤ n) :
    (1 / 36 : ℝ) * Real.sqrt n
      ≤ (qQueryOn (layerRead (n := n) (r := 0) (gLetter g))
          (fun x => wordProd (id : M → M)
            (layerRead (n := n) (r := 0) (gLetter g) x)) (1 / 3) : ℝ) := by
  have hne : g ^ (0 : ℕ) ≠ g ^ (0 + 1) := by
    rw [pow_zero, pow_one]
    exact fun h => hg1 h.symm
  have hpar := mul_advPMOn_le_qQueryOn_of_error_third
    (read := layerRead (n := n) (r := 0) (gLetter g))
    (f := layerOut (n := n) (r := 0))
    (separates_of_injective (layerRead_injective (gLetter_injective hg1)) _)
  have hbridge := trichotomy_layer_bridge (n := n) hne
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc (1 / 36 : ℝ) * Real.sqrt n
      ≤ (1 / 36) * advPMOn (layerRead (n := n) (r := 0) (gLetter g))
          (layerOut (n := n) (r := 0)) :=
        mul_le_mul_of_nonneg_left
          (by rw [← layerTheta_zero n]
              exact sqrt_le_advPMOn_layerOut (gLetter_injective hg1)
                (by omega))
          (by norm_num)
    _ ≤ (qQueryOn (layerRead (n := n) (r := 0) (gLetter g))
          (layerOut (n := n) (r := 0)) (1 / 3) : ℝ) := hpar
    _ ≤ _ := by exact_mod_cast hbridge

/-- The two-letter promise bound restricts to the **honest total product**
`Prod_{M,n}` over the full alphabet `M`. -/
private lemma trichotomy_restrict {g : M} {r : ℕ} {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn (layerRead (n := n) (r := r) (gLetter g))
        (fun x => wordProd (id : M → M)
          (layerRead (n := n) (r := r) (gLetter g) x)) ε
      ≤ qQuery (fun w : Fin n → M => wordProd (id : M → M) w) ε := by
  haveI : Nonempty M := ⟨1⟩
  exact qQueryOn_comp_read_le_qQuery _ _
    (queryCounts_nonempty (fun x y h => by rw [show x = y from h]) hε)

/-- **The nonaperiodic regime, for the honest total product**:
`(1/36)·(n/2) ≤ Q_{1/3}(Prod_{M,n})` over the full alphabet `M`. -/
theorem nonaperiodic_qQuery_lower_total {g : M}
    (hg : ∀ m, 0 < m → g ^ m ≠ g ^ (m + 1)) (hn : 2 ≤ n) :
    (1 / 36 : ℝ) * ((n : ℝ) / 2)
      ≤ (qQuery (fun w : Fin n → M => wordProd (id : M → M) w)
          (1 / 3) : ℝ) :=
  by
  refine (nonaperiodic_qQuery_lower hg hn).trans ?_
  have hres := trichotomy_restrict (n := n) (g := g) (r := n / 2)
    (ε := (1 / 3 : ℝ)) (by norm_num)
  exact_mod_cast hres

/-- **The nontrivial regime, for the honest total product**:
`(1/36)·√n ≤ Q_{1/3}(Prod_{M,n})` for any `g ≠ 1`. -/
theorem nontrivial_qQuery_lower_total {g : M} (hg1 : g ≠ 1) (hn : 1 ≤ n) :
    (1 / 36 : ℝ) * Real.sqrt n
      ≤ (qQuery (fun w : Fin n → M => wordProd (id : M → M) w)
          (1 / 3) : ℝ) :=
  by
  refine (nontrivial_qQuery_lower hg1 hn).trans ?_
  have hres := trichotomy_restrict (n := n) (g := g) (r := 0)
    (ε := (1 / 3 : ℝ)) (by norm_num)
  exact_mod_cast hres

/-- **Theorem `thm:aperiodicity-index-lower`, operational**: for a nontrivial
finite aperiodic monoid and `n ≥ 1`,
`(1/36)·√(n·min{n, ι(M)})/2 ≤ Q_{1/3}(Prod_{M,n})` over the full alphabet —
the two-layer certificate at `r = min{ι − 1, ⌊n/2⌋}` (`Trichotomy/Index.lean`),
through the sharp Boolean bound, the postprocessing bridge and the
restriction to the total product. -/
theorem index_qQuery_lower [IsAperiodicMonoid M] [Nontrivial M] (hn : 1 ≤ n) :
    (1 / 36 : ℝ) * (Real.sqrt ((n * min n (aperiodicIndex M) : ℕ) : ℝ) / 2)
      ≤ (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ) := by
  have hι := one_le_aperiodicIndex (M := M)
  set r := min (aperiodicIndex M - 1) (n / 2) with hr
  have hrι : r < aperiodicIndex M := by omega
  obtain ⟨g, hg⟩ := exists_pow_ne_of_lt_aperiodicIndex hrι
  have hg1 : g ≠ 1 := fun h => hg (by rw [h, one_pow, one_pow])
  have hrn : r + 1 ≤ n := by omega
  have hpar := mul_advPMOn_le_qQueryOn_of_error_third
    (read := layerRead (n := n) (r := r) (gLetter g))
    (f := layerOut (n := n) (r := r))
    (separates_of_injective (layerRead_injective (gLetter_injective hg1)) _)
  have hbridge := trichotomy_layer_bridge (n := n) hg (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hres := trichotomy_restrict (n := n) (g := g) (r := r)
    (ε := (1 / 3 : ℝ)) (by norm_num)
  calc (1 / 36 : ℝ) * (Real.sqrt ((n * min n (aperiodicIndex M) : ℕ) : ℝ) / 2)
      ≤ (1 / 36) * advPMOn (layerRead (n := n) (r := r) (gLetter g))
          (layerOut (n := n) (r := r)) :=
        mul_le_mul_of_nonneg_left
          ((sqrt_index_le_layerTheta hι hr).trans
            (sqrt_le_advPMOn_layerOut (gLetter_injective hg1) hrn))
          (by norm_num)
    _ ≤ (qQueryOn (layerRead (n := n) (r := r) (gLetter g))
          (layerOut (n := n) (r := r)) (1 / 3) : ℝ) := hpar
    _ ≤ (qQueryOn (layerRead (n := n) (r := r) (gLetter g))
          (fun x => wordProd (id : M → M)
            (layerRead (n := n) (r := r) (gLetter g) x)) (1 / 3) : ℝ) := by
        exact_mod_cast hbridge
    _ ≤ _ := by exact_mod_cast hres

/-! ### Structural forms

The same bounds with the hypothesis stated as a property of `M` rather than
as a supplied witness. -/

/-- **Nonaperiodic ⇒ `Ω(n)`**, structurally. -/
theorem qQuery_lower_of_not_aperiodic (h : ¬ IsAperiodicMonoid M)
    (hn : 2 ≤ n) :
    (1 / 36 : ℝ) * ((n : ℝ) / 2)
      ≤ (qQuery (fun w : Fin n → M => wordProd (id : M → M) w)
          (1 / 3) : ℝ) := by
  obtain ⟨g, hg⟩ := exists_nonaperiodic_elem h
  exact nonaperiodic_qQuery_lower_total hg hn

/-- **Nontrivial ⇒ `Ω(√n)`**, structurally. -/
theorem qQuery_lower_of_not_subsingleton (h : ¬ Subsingleton M)
    (hn : 1 ≤ n) :
    (1 / 36 : ℝ) * Real.sqrt n
      ≤ (qQuery (fun w : Fin n → M => wordProd (id : M → M) w)
          (1 / 3) : ℝ) := by
  haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp h
  obtain ⟨g, hg1⟩ := exists_ne (1 : M)
  exact nontrivial_qQuery_lower_total hg1 hn

end Trichotomy

/-! ## The trichotomy's opening clause: finite nonaperiodic semigroups -/

section TrichotomySemigroup

variable {S : Type} [Semigroup S] [Fintype S] [DecidableEq S] {n : ℕ}

/-- Testing the coerced product against `g^{L+r+1}` is classical
postprocessing of the readout, so it costs nothing. -/
private lemma semigroup_layer_bridge {s : S}
    (hs : ∀ m, 0 < m → (s : WithOne S) ^ m ≠ (s : WithOne S) ^ (m + 1))
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s))
        (layerOut (n := n + 1) (r := (n + 1) / 2)) ε
      ≤ qQueryOn (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s))
          (fun x => semigroupProd n
            (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s) x)) ε := by
  haveI : Nonempty S := ⟨s⟩
  have h := qQueryOn_postcomp_le
    (fun t : S => decide ((t : WithOne S)
      = (s : WithOne S) ^ ((n + 1) + (n + 1) / 2 + 1)))
    (queryCounts_nonempty
      (det_semigroupProd_layerRead s n ((n + 1) / 2)) hε)
  rwa [decide_coe_semigroupProd_eq_layerOut hs n] at h

/-- **A finite nonaperiodic semigroup needs `Ω(n)` quantum queries**, on the
displayed hard promise. -/
theorem nonaperiodic_semigroup_qQuery_lower {s : S}
    (hs : ∀ m, 0 < m → (s : WithOne S) ^ m ≠ (s : WithOne S) ^ (m + 1))
    (n : ℕ) :
    (1 / 36 : ℝ) * (((n + 1 : ℕ) : ℝ) / 2)
      ≤ (qQueryOn (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s))
          (fun x => semigroupProd n
            (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s) x))
          (1 / 3) : ℝ) := by
  have hpar := mul_advPMOn_le_qQueryOn_of_error_third
    (read := layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s))
    (f := layerOut (n := n + 1) (r := (n + 1) / 2))
    (separates_of_injective
      (layerRead_injective (sLetter_injective hs)) _)
  have hbridge := semigroup_layer_bridge hs n (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc (1 / 36 : ℝ) * (((n + 1 : ℕ) : ℝ) / 2)
      ≤ (1 / 36) * advPMOn
          (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s))
          (layerOut (n := n + 1) (r := (n + 1) / 2)) :=
        mul_le_mul_of_nonneg_left
          (half_le_advPMOn_layerOut (sLetter_injective hs) (by omega))
          (by norm_num)
    _ ≤ (qQueryOn (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s))
          (layerOut (n := n + 1) (r := (n + 1) / 2)) (1 / 3) : ℝ) := hpar
    _ ≤ _ := by exact_mod_cast hbridge

/-- **The honest total form**: `(1/36)·((n+1)/2) ≤ Q_{1/3}(semigroupProd n)`
over the full alphabet `S`. -/
theorem nonaperiodic_semigroup_qQuery_lower_total {s : S}
    (hs : ∀ m, 0 < m → (s : WithOne S) ^ m ≠ (s : WithOne S) ^ (m + 1))
    (n : ℕ) :
    (1 / 36 : ℝ) * (((n + 1 : ℕ) : ℝ) / 2)
      ≤ (qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ) := by
  haveI : Nonempty S := ⟨s⟩
  refine (nonaperiodic_semigroup_qQuery_lower hs n).trans ?_
  have hres := qQueryOn_comp_read_le_qQuery
    (layerRead (n := n + 1) (r := (n + 1) / 2) (sLetter s))
    (fun w : Fin (n + 1) → S => semigroupProd n w)
    (queryCounts_nonempty (fun x y h => by rw [show x = y from h])
      (by norm_num : (0 : ℝ) ≤ 1 / 3))
  exact_mod_cast hres

/-- **Reading every letter suffices**: the matching `O(n)` upper bound, so
the regime is `Θ(n)`. -/
theorem nonaperiodic_semigroup_qQuery_upper [Nonempty S] {ε : ℝ}
    (hε : 0 ≤ ε) (n : ℕ) :
    qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) ε ≤ n + 1 := by
  have h := qQueryOn_le_card
    (read := (id : (Fin (n + 1) → S) → Fin (n + 1) → S))
    (f := fun w : Fin (n + 1) → S => semigroupProd n w)
    (fun x y h => by rw [show x = y from h]) hε
  rwa [Fintype.card_fin] at h

/-- **The trichotomy's opening clause, from the structural hypothesis.** -/
theorem qQuery_semigroupProd_lower_of_not_aperiodic
    (h : ¬ IsAperiodicSemigroup S) (n : ℕ) :
    (1 / 36 : ℝ) * (((n + 1 : ℕ) : ℝ) / 2)
      ≤ (qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) (1 / 3) : ℝ) := by
  obtain ⟨s, hs⟩ := exists_nonaperiodic_semigroup_elem h
  exact nonaperiodic_semigroup_qQuery_lower_total hs n

end TrichotomySemigroup

end MonoidProduct
