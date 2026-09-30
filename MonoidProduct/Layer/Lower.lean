import MonoidProduct.Capped.Embed
import QuantumQueryComplexity.Promise.Post
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.openClassical false

/-!
# The two-layer (inclusion-matrix) adversary

The `Ω(n)` certificate behind `monoid.tex`'s fixed finite-monoid trichotomy:
on the promise "the marked set has size `r` or size `r+1`", telling the two
layers apart needs adversary value `√((n−r)(r+1))`, which at `r = ⌊n/2⌋` is
`Ω(n)` — linear, not `√n`.

The promise domain is the **structural** sum

  `Layers n r = {S : Finset (Fin n) // S.card = r} ⊕ {S // S.card = r+1}`,

so no promise predicate ever appears; a query at `i` returns
`letter (i ∈ S)` for an arbitrary injective two-letter alphabet, and the
output `layerOut` names the layer.

The certificate is the inclusion matrix `layerΓ`, supported on the pairs
`S ⊆ T` across the two layers — the paper's symmetric adversary with
off-diagonal blocks `A` and `Aᵀ`.  Its two-value vector (`√((n−r)(r+1))` on
the low layer, `r+1` on the high layer) is an **exact** eigenvector with
eigenvalue `√((n−r)(r+1))`, because the bipartite graph is
`(n−r, r+1)`-biregular: a low vertex has `n−r` supersets in the high layer
(`card_filter_superset`) and a high vertex has `r+1` subsets in the low
layer (`card_filter_subset`).  Filtering by one queried coordinate leaves
the graph of the flip-at-`i` involution (`layerFlip`), a partial matching of
norm at most one.

`le_advPMOn` then gives `√((n−r)(r+1)) ≤ advPMOn` (`sqrt_le_advPMOn_layerOut`),
and at `r = n/2` this is `n/2 ≤ advPMOn` (`half_le_advPMOn_layerOut`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open scoped Classical
open Matrix

variable {n r : ℕ}

/-! ## The promise domain -/

/-- The low layer: marked sets of size `r`. -/
abbrev LowLayer (n r : ℕ) : Type := {S : Finset (Fin n) // S.card = r}

/-- The high layer: marked sets of size `r + 1`. -/
abbrev HighLayer (n r : ℕ) : Type := {S : Finset (Fin n) // S.card = r + 1}

/-- The two-layer promise domain. -/
abbrev Layers (n r : ℕ) : Type := LowLayer n r ⊕ HighLayer n r

/-- The marked set of a promise input. -/
def layerSet : Layers n r → Finset (Fin n) :=
  Sum.elim (fun S => S.val) (fun T => T.val)

@[simp] lemma layerSet_inl (S : LowLayer n r) :
    layerSet (Sum.inl S : Layers n r) = S.val := rfl

@[simp] lemma layerSet_inr (T : HighLayer n r) :
    layerSet (Sum.inr T : Layers n r) = T.val := rfl

lemma card_layerSet_inl (S : LowLayer n r) :
    (layerSet (Sum.inl S : Layers n r)).card = r := S.2

lemma card_layerSet_inr (T : HighLayer n r) :
    (layerSet (Sum.inr T : Layers n r)).card = r + 1 := T.2

/-- The marked set determines the input: the two layers have different
sizes. -/
lemma layerSet_injective : Function.Injective (layerSet (n := n) (r := r)) := by
  intro x y hxy
  cases x with
  | inl S =>
      cases y with
      | inl S' => exact congrArg Sum.inl (Subtype.ext hxy)
      | inr T =>
          exfalso
          have h1 : S.val.card = r := S.2
          have h2 : T.val.card = r + 1 := T.2
          rw [layerSet_inl, layerSet_inr] at hxy
          rw [hxy, h2] at h1
          omega
  | inr T =>
      cases y with
      | inl S =>
          exfalso
          have h1 : S.val.card = r := S.2
          have h2 : T.val.card = r + 1 := T.2
          rw [layerSet_inr, layerSet_inl] at hxy
          rw [hxy, h1] at h2
          omega
      | inr T' => exact congrArg Sum.inr (Subtype.ext hxy)

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- A query at `i` returns the letter naming membership of `i` in the marked
set. -/
def layerRead (letter : Bool → σ) (x : Layers n r) (i : Fin n) : σ :=
  letter (decide (i ∈ layerSet x))

lemma layerRead_injective {letter : Bool → σ}
    (hletter : Function.Injective letter) :
    Function.Injective (layerRead (n := n) (r := r) letter) := by
  intro x y hxy
  refine layerSet_injective (Finset.ext fun i => ?_)
  have h := congrFun hxy i
  rw [layerRead, layerRead] at h
  have hd : decide (i ∈ layerSet x) = decide (i ∈ layerSet y) := hletter h
  constructor
  · intro hi
    exact of_decide_eq_true (by rw [← hd, decide_eq_true hi])
  · intro hi
    exact of_decide_eq_true (by rw [hd, decide_eq_true hi])

/-- The output: which layer the input lies in. -/
def layerOut : Layers n r → Bool := Sum.elim (fun _ => false) (fun _ => true)

@[simp] lemma layerOut_inl (S : LowLayer n r) :
    layerOut (Sum.inl S : Layers n r) = false := rfl

@[simp] lemma layerOut_inr (T : HighLayer n r) :
    layerOut (Sum.inr T : Layers n r) = true := rfl

/-! ## The inclusion matrix -/

/-- The inclusion matrix: `1` on the pairs `S ⊆ T` across the two layers,
`0` inside a layer.  This is the paper's symmetric adversary with
off-diagonal blocks `A` and `Aᵀ`. -/
noncomputable def layerΓ (n r : ℕ) : Matrix (Layers n r) (Layers n r) ℝ :=
  Matrix.of <| Sum.elim
    (fun S => Sum.elim (fun _ : LowLayer n r => (0 : ℝ))
      (fun T : HighLayer n r => if S.val ⊆ T.val then 1 else 0))
    (fun T => Sum.elim
      (fun S : LowLayer n r => if S.val ⊆ T.val then 1 else 0)
      (fun _ : HighLayer n r => (0 : ℝ)))

@[simp] lemma layerΓ_inl_inl (S S' : LowLayer n r) :
    layerΓ n r (Sum.inl S) (Sum.inl S') = 0 := rfl

@[simp] lemma layerΓ_inr_inr (T T' : HighLayer n r) :
    layerΓ n r (Sum.inr T) (Sum.inr T') = 0 := rfl

@[simp] lemma layerΓ_inl_inr (S : LowLayer n r) (T : HighLayer n r) :
    layerΓ n r (Sum.inl S) (Sum.inr T) = if S.val ⊆ T.val then 1 else 0 := rfl

@[simp] lemma layerΓ_inr_inl (T : HighLayer n r) (S : LowLayer n r) :
    layerΓ n r (Sum.inr T) (Sum.inl S) = if S.val ⊆ T.val then 1 else 0 := rfl

lemma layerΓ_symm (x y : Layers n r) : layerΓ n r x y = layerΓ n r y x := by
  cases x <;> cases y <;> rfl

lemma layerΓ_isHermitian : (layerΓ n r).IsHermitian :=
  Matrix.IsHermitian.ext fun x y => by rw [star_trivial, layerΓ_symm y x]

lemma abs_layerΓ_le_one (x y : Layers n r) : |layerΓ n r x y| ≤ 1 := by
  cases x <;> cases y <;>
    simp only [layerΓ_inl_inl, layerΓ_inr_inr, layerΓ_inl_inr, layerΓ_inr_inl] <;>
    [skip; split_ifs; split_ifs; skip] <;> norm_num

/-- Adversary validity: connected inputs lie in different layers. -/
lemma layerΓ_apply_eq_zero {x y : Layers n r}
    (hf : layerOut x = layerOut y) : layerΓ n r x y = 0 := by
  cases x with
  | inl S =>
      cases y with
      | inl S' => rfl
      | inr T => exact absurd hf (by simp)
  | inr T =>
      cases y with
      | inl S => exact absurd hf (by simp)
      | inr T' => rfl

/-! ## Biregularity -/

/-- **A low vertex has `n − r` supersets in the high layer.** -/
lemma card_filter_superset (hr : r + 1 ≤ n) (S : LowLayer n r) :
    (Finset.univ.filter fun T : HighLayer n r => S.val ⊆ T.val).card
      = n - r := by
  classical
  have hbij : (S.val)ᶜ.card
      = (Finset.univ.filter fun T : HighLayer n r => S.val ⊆ T.val).card := by
    refine Finset.card_bij
      (fun i hi => (⟨insert i S.val, by
        rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hi), S.2]⟩ :
          HighLayer n r)) ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_insert _ _⟩
    · intro i hi j hj hij
      have h : insert i S.val = insert j S.val := congrArg Subtype.val hij
      have hi' : i ∉ S.val := Finset.mem_compl.mp hi
      have himem : i ∈ insert j S.val := by
        rw [← h]
        exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp himem with h1 | h1
      · exact h1
      · exact absurd h1 hi'
    · intro T hT
      rw [Finset.mem_filter] at hT
      obtain ⟨a, ha, hins⟩ :=
        Finset.exists_eq_insert_iff.mpr ⟨hT.2, by rw [S.2, T.2]⟩
      exact ⟨a, Finset.mem_compl.mpr ha, Subtype.ext hins⟩
  rw [← hbij, Finset.card_compl, S.2, Fintype.card_fin]

/-- **A high vertex has `r + 1` subsets in the low layer.** -/
lemma card_filter_subset (T : HighLayer n r) :
    (Finset.univ.filter fun S : LowLayer n r => S.val ⊆ T.val).card
      = r + 1 := by
  classical
  have hbij : T.val.card
      = (Finset.univ.filter fun S : LowLayer n r => S.val ⊆ T.val).card := by
    refine Finset.card_bij
      (fun i hi => (⟨T.val.erase i, by
        rw [Finset.card_erase_of_mem hi, T.2]; omega⟩ : LowLayer n r)) ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.erase_subset _ _⟩
    · intro i hi j hj hij
      have h : T.val.erase i = T.val.erase j := congrArg Subtype.val hij
      by_contra hne
      have himem : i ∈ T.val.erase j := Finset.mem_erase.mpr ⟨hne, hi⟩
      rw [← h] at himem
      exact (Finset.notMem_erase i T.val) himem
    · intro S hS
      rw [Finset.mem_filter] at hS
      obtain ⟨a, ha, hins⟩ :=
        Finset.exists_eq_insert_iff.mpr ⟨hS.2, by rw [S.2, T.2]⟩
      refine ⟨a, by rw [← hins]; exact Finset.mem_insert_self _ _,
        Subtype.ext ?_⟩
      show T.val.erase a = S.val
      conv_lhs => rw [← hins]
      exact Finset.erase_insert ha
  rw [← hbij, T.2]

/-! ## The eigenvector -/

/-- The eigenvalue `√((n−r)(r+1))`. -/
noncomputable def layerTheta (n r : ℕ) : ℝ :=
  Real.sqrt (((n - r) * (r + 1) : ℕ) : ℝ)

lemma layerTheta_nonneg : 0 ≤ layerTheta n r := Real.sqrt_nonneg _

lemma layerTheta_mul_self :
    layerTheta n r * layerTheta n r = (((n - r) * (r + 1) : ℕ) : ℝ) :=
  Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- The two-value eigenvector. -/
noncomputable def layerVec (n r : ℕ) : Layers n r → ℝ :=
  Sum.elim (fun _ => layerTheta n r) (fun _ => ((r : ℝ) + 1))

@[simp] lemma layerVec_inl (S : LowLayer n r) :
    layerVec n r (Sum.inl S) = layerTheta n r := rfl

@[simp] lemma layerVec_inr (T : HighLayer n r) :
    layerVec n r (Sum.inr T) = (r : ℝ) + 1 := rfl

/-- **The exact eigen equation** `Γ v = θ v`, from biregularity. -/
lemma layerΓ_mulVec_layerVec (hr : r + 1 ≤ n) :
    layerΓ n r *ᵥ layerVec n r = layerTheta n r • layerVec n r := by
  classical
  funext x
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.smul_apply,
    smul_eq_mul]
  cases x with
  | inl S =>
      have h1 : (∑ S' : LowLayer n r,
          layerΓ n r (Sum.inl S) (Sum.inl S') * layerVec n r (Sum.inl S')) = 0 :=
        Finset.sum_eq_zero fun S' _ => by rw [layerΓ_inl_inl, zero_mul]
      have h2 : (∑ T : HighLayer n r,
            layerΓ n r (Sum.inl S) (Sum.inr T) * layerVec n r (Sum.inr T))
          = ((n - r : ℕ) : ℝ) * ((r : ℝ) + 1) := by
        rw [Finset.sum_congr rfl fun T _ => by
          rw [layerΓ_inl_inr, layerVec_inr, ite_mul, one_mul, zero_mul],
          ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          card_filter_superset hr S]
      rw [h1, h2, layerVec_inl, layerTheta_mul_self, zero_add]
      push_cast
      ring
  | inr T =>
      have h1 : (∑ S : LowLayer n r,
            layerΓ n r (Sum.inr T) (Sum.inl S) * layerVec n r (Sum.inl S))
          = ((r : ℝ) + 1) * layerTheta n r := by
        rw [Finset.sum_congr rfl fun S _ => by
          rw [layerΓ_inr_inl, layerVec_inl, ite_mul, one_mul, zero_mul],
          ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          card_filter_subset T]
        push_cast
        ring
      have h2 : (∑ T' : HighLayer n r,
          layerΓ n r (Sum.inr T) (Sum.inr T') * layerVec n r (Sum.inr T')) = 0 :=
        Finset.sum_eq_zero fun T' _ => by rw [layerΓ_inr_inr, zero_mul]
      rw [h1, h2, layerVec_inr, add_zero]
      ring

lemma layerVec_ne_zero (hr : r + 1 ≤ n) : layerVec n r ≠ 0 := by
  intro h0
  have hne : Nonempty (HighLayer n r) := by
    obtain ⟨T, hT⟩ := Finset.exists_subset_card_eq
      (show r + 1 ≤ (Finset.univ : Finset (Fin n)).card by
        rw [Finset.card_univ, Fintype.card_fin]; exact hr)
    exact ⟨⟨T, hT.2⟩⟩
  obtain ⟨T⟩ := hne
  have h := congrFun h0 (Sum.inr T)
  rw [layerVec_inr, Pi.zero_apply] at h
  have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  linarith

lemma layerTheta_le_norm (hr : r + 1 ≤ n) : layerTheta n r ≤ ‖layerΓ n r‖ :=
  (le_abs_self _).trans
    (abs_eigenvalue_le_norm (layerΓ_mulVec_layerVec hr) (layerVec_ne_zero hr))

/-! ## The query masks -/

/-- The flip at `i`: add `i` to a low set that misses it, remove `i` from a
high set that has it, and stand still otherwise — the unique incident edge,
when there is one. -/
def layerFlipFun (i : Fin n) : Layers n r → Layers n r
  | Sum.inl S =>
      if h : i ∈ S.val then Sum.inl S
      else Sum.inr ⟨insert i S.val, by
        rw [Finset.card_insert_of_notMem h, S.2]⟩
  | Sum.inr T =>
      if h : i ∈ T.val then Sum.inl ⟨T.val.erase i, by
        rw [Finset.card_erase_of_mem h, T.2]; omega⟩
      else Sum.inr T

lemma layerFlipFun_involutive (i : Fin n) :
    Function.Involutive (layerFlipFun (n := n) (r := r) i) := by
  intro x
  cases x with
  | inl S =>
      by_cases h : i ∈ S.val
      · simp only [layerFlipFun, dif_pos h]
      · simp only [layerFlipFun, dif_neg h,
          dif_pos (Finset.mem_insert_self i S.val)]
        exact congrArg Sum.inl (Subtype.ext (Finset.erase_insert h))
  | inr T =>
      by_cases h : i ∈ T.val
      · simp only [layerFlipFun, dif_pos h,
          dif_neg (Finset.notMem_erase i T.val)]
        exact congrArg Sum.inr (Subtype.ext (Finset.insert_erase h))
      · simp only [layerFlipFun, dif_neg h]

/-- The support of a masked entry: the unique incident flip. -/
lemma layerMask_support {letter : Bool → σ}
    (hletter : Function.Injective letter) {i : Fin n} {x y : Layers n r}
    (hΓ : layerΓ n r x y ≠ 0)
    (hmask : layerRead letter x i ≠ layerRead letter y i) :
    y = layerFlipFun i x := by
  have hmem : ¬ ((i ∈ layerSet x) ↔ (i ∈ layerSet y)) := by
    intro hiff
    exact hmask (by rw [layerRead, layerRead, decide_eq_decide.mpr hiff])
  cases x with
  | inl S =>
      cases y with
      | inl S' => exact absurd (layerΓ_inl_inl S S') hΓ
      | inr T =>
          have hsub : S.val ⊆ T.val := by
            by_contra hns
            rw [layerΓ_inl_inr, if_neg hns] at hΓ
            exact hΓ rfl
          have hiT : i ∈ T.val := by
            by_contra hiT
            exact hmem ⟨fun hiS => absurd (hsub hiS) hiT, fun h => absurd h hiT⟩
          have hiS : i ∉ S.val := fun hiS => hmem ⟨fun _ => hiT, fun _ => hiS⟩
          have hins : insert i S.val = T.val :=
            Finset.eq_of_subset_of_card_le (Finset.insert_subset hiT hsub)
              (le_of_eq (by rw [Finset.card_insert_of_notMem hiS, S.2, T.2]))
          simp only [layerFlipFun, dif_neg hiS]
          exact congrArg Sum.inr (Subtype.ext hins.symm)
  | inr T =>
      cases y with
      | inr T' => exact absurd (layerΓ_inr_inr T T') hΓ
      | inl S =>
          have hsub : S.val ⊆ T.val := by
            by_contra hns
            rw [layerΓ_inr_inl, if_neg hns] at hΓ
            exact hΓ rfl
          have hiT : i ∈ T.val := by
            by_contra hiT
            exact hmem ⟨fun h => absurd h hiT, fun hiS => absurd (hsub hiS) hiT⟩
          have hiS : i ∉ S.val := fun hiS => hmem ⟨fun _ => hiS, fun _ => hiT⟩
          have hcT : (T.val.erase i).card = r := by
            have hc := Finset.card_erase_of_mem hiT
            rw [T.2] at hc
            omega
          have hers : S.val = T.val.erase i :=
            Finset.eq_of_subset_of_card_le
              (fun a ha => Finset.mem_erase.mpr
                ⟨fun hai => hiS (hai ▸ ha), hsub ha⟩)
              (le_of_eq (by rw [hcT, S.2]))
          simp only [layerFlipFun, dif_pos hiT]
          exact congrArg Sum.inl (Subtype.ext hers)

/-- **The mask bound**: every query filter leaves norm at most one. -/
lemma layerΓ_hadamard_le_one {letter : Bool → σ}
    (hletter : Function.Injective letter) (i : Fin n) :
    ‖layerΓ n r ⊙ advDOn (layerRead (n := n) (r := r) letter) i‖ ≤ 1 := by
  refine l2_opNorm_le_one_of_equiv_support _
    ((layerFlipFun_involutive (n := n) (r := r) i).toPerm) ?_ ?_
  · intro x y hne
    rw [Matrix.hadamard_apply, advDOn_apply]
    by_cases hmask : layerRead letter x i = layerRead letter y i
    · rw [if_pos hmask, mul_zero]
    · rw [if_neg hmask]
      by_cases hΓ : layerΓ n r x y = 0
      · rw [hΓ, zero_mul]
      · exact absurd (layerMask_support hletter hΓ hmask) hne
  · intro x y
    rw [Matrix.hadamard_apply, advDOn_apply]
    split_ifs with hm
    · rw [mul_zero, abs_zero]
      norm_num
    · rw [mul_one]
      exact abs_layerΓ_le_one x y

/-! ## The certificate -/

/-- **The two-layer adversary bound**: telling a marked set of size `r` from
one of size `r+1` needs adversary value `√((n−r)(r+1))`. -/
theorem sqrt_le_advPMOn_layerOut {letter : Bool → σ}
    (hletter : Function.Injective letter) (hr : r + 1 ≤ n) :
    layerTheta n r
      ≤ advPMOn (layerRead (n := n) (r := r) letter) (layerOut (n := n) (r := r)) := by
  have hdet := separates_of_injective (layerRead_injective hletter)
    (layerOut (n := n) (r := r))
  have h1 : IsAdvMatrixOn (layerOut (n := n) (r := r)) (layerΓ n r) :=
    ⟨layerΓ_isHermitian, fun x y hf => layerΓ_apply_eq_zero hf⟩
  exact (layerTheta_le_norm hr).trans
    (le_advPMOn hdet h1 (layerΓ_hadamard_le_one hletter))

/-- At the balanced split `r = n/2` the certificate is **linear**:
`n/2 ≤ √((n−r)(r+1))`. -/
lemma half_le_layerTheta (hn : 0 < n) :
    ((n : ℝ)) / 2 ≤ layerTheta n (n / 2) := by
  have hprod : (n : ℝ) / 2 * ((n : ℝ) / 2)
      ≤ (((n - n / 2) * (n / 2 + 1) : ℕ) : ℝ) := by
    have hnat : n * n ≤ 4 * ((n - n / 2) * (n / 2 + 1)) := by
      have h1 : n / 2 + (n - n / 2) = n := by omega
      have h2 : n ≤ 2 * (n / 2) + 1 := by omega
      have h3 : 2 * (n - n / 2) ≥ n := by omega
      nlinarith [Nat.div_le_self n 2, Nat.zero_le (n / 2)]
    have hcast : ((n * n : ℕ) : ℝ) ≤ ((4 * ((n - n / 2) * (n / 2 + 1)) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast ⊢
    linarith
  rw [layerTheta]
  rw [show ((n : ℝ)) / 2 = Real.sqrt (((n : ℝ) / 2) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [pow_two]
  exact hprod

/-- **The linear two-layer bound**: at `r = ⌊n/2⌋`,
`n/2 ≤ advPMOn` for the layer test. -/
theorem half_le_advPMOn_layerOut {letter : Bool → σ}
    (hletter : Function.Injective letter) (hn : 0 < n) :
    ((n : ℝ)) / 2
      ≤ advPMOn (layerRead (n := n) (r := n / 2) letter)
          (layerOut (n := n) (r := n / 2)) :=
  (half_le_layerTheta hn).trans
    (sqrt_le_advPMOn_layerOut hletter (by omega))

end MonoidProduct
