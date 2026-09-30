import MonoidProduct.Width.Product
import MonoidProduct.Width.Numeric
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The index-two width bound: `κ ≤ 5·log₂|M|`  (`thm:index-two-width`)

For a finite commutative monoid in which every element satisfies `x³ = x²`,
the essential width of the subset product is below `5·log₂|M|`, and hence
`ADV±(∏) ≤ 16√(n·5·log₂|M|)`.

The combinatorial core is a collision count on the subset cube over the
essential positions, entirely in `ℕ` and `M`:

* **Every edge of the cube is strict** — that is `ctxProd_ne_erase`, proved in
  `MonoidProduct/Width/Product.lean`.
* **Collision lemma**: a collision `p(A) = p(C)` inside `R` makes every factor
  of the symmetric difference absorbed at `R`: `p(R)·aᵢ = p(R)`.  The identity
  `x³ = x²` enters exactly twice — once as `p(R) = qky²d ⇒ p(R)·y = p(R)` and
  once inside absorption.
* **Injectivity**: on subsets of `N_R = {i ∈ R : p(R)aᵢ ≠ p(R)}` the map
  `A ↦ p(A)` is injective, so `2^{|N_R|} ≤ |M|`.
* **The fiber injection**: `S ↦ (p(S), N_S)` is injective on the whole cube,
  because `S = N_S ∪ {i : p(S)aᵢ = p(S)}` and the second part depends only on
  `p(S)`.  Hence the **ball inequality**
  `2^B ≤ |M| · ∑_{j ≤ ⌊log₂|M|⌋} C(B, j)`.

The analytic endgame `lt_five_logb_of_ball` lives in
`MonoidProduct/Width/Numeric.lean`; the `x³ = x²` identity supplies aperiodicity
(`stabilizes` at exponent two), so all of `Product.lean`'s absorption machinery
applies.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {M : Type*} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- `x³ = x²` is aperiodicity with stabilisation exponent two. -/
lemma isAperiodicMonoid_of_cube_eq_sq (hx3 : ∀ z : M, z ^ 3 = z ^ 2) :
    IsAperiodicMonoid M :=
  ⟨fun a => ⟨2, by norm_num, (hx3 a).symm⟩⟩

section IndexTwo

variable (hx3 : ∀ z : M, z ^ 3 = z ^ 2)
variable (m : σ → M) (x : ι → σ) (T : Finset ι)

include hx3 in
/-- **The collision lemma**: a collision between two subsets of `R` absorbs
every factor of the symmetric difference at `R`.  Stated for `i ∈ C \ A`; the
other half follows by symmetry of the hypothesis. -/
lemma ctxProd_mul_eq_of_collision {A C R : Finset ι} (hA : A ⊆ R) (hC : C ⊆ R)
    (hR : R ⊆ prodEss m x T) (hpp : ctxProd m x T A = ctxProd m x T C)
    {i : ι} (hi : i ∈ C \ A) :
    ctxProd m x T R * m (x i) = ctxProd m x T R := by
  haveI : IsAperiodicMonoid M := isAperiodicMonoid_of_cube_eq_sq hx3
  set q : M := ∏ j ∈ T \ prodEss m x T, m (x j) with hq
  set k : M := ∏ j ∈ A ∩ C, m (x j) with hk
  set xx : M := ∏ j ∈ A \ C, m (x j) with hxx
  set y : M := ∏ j ∈ C \ A, m (x j) with hy
  set d : M := ∏ j ∈ R \ (A ∪ C), m (x j) with hd
  -- the four decompositions
  have hprodA : ∏ j ∈ A, m (x j) = xx * k := by
    rw [hxx, hk, ← Finset.prod_union (Finset.disjoint_sdiff_inter A C),
      Finset.sdiff_union_inter]
  have hprodC : ∏ j ∈ C, m (x j) = y * k := by
    rw [hy, hk, Finset.inter_comm,
      ← Finset.prod_union (Finset.disjoint_sdiff_inter C A),
      Finset.sdiff_union_inter]
  have hprodAC : ∏ j ∈ A ∪ C, m (x j) = xx * k * y := by
    rw [← Finset.union_sdiff_self_eq_union,
      Finset.prod_union Finset.disjoint_sdiff, hprodA, hy]
  have hprodR : ∏ j ∈ R, m (x j) = d * (xx * k * y) := by
    rw [hd, ← hprodAC, Finset.prod_sdiff (Finset.union_subset hA hC)]
  -- the collision, in product form
  have hcol : q * (xx * k) = q * (y * k) := by
    have h := hpp
    rw [ctxProd, ctxProd, hprodA, hprodC, ← hq] at h
    exact h
  -- `p(R) = q·k·y²·d`
  have hRy : ctxProd m x T R = q * k * y ^ 2 * d := by
    calc ctxProd m x T R = q * (d * (xx * k * y)) := by
          rw [ctxProd, hprodR, ← hq]
      _ = q * (xx * k) * (y * d) := by ac_rfl
      _ = q * (y * k) * (y * d) := by rw [hcol]
      _ = q * k * y ^ 2 * d := by rw [sq]; ac_rfl
  -- `p(R)·y = p(R)`
  have hRabs : ctxProd m x T R * y = ctxProd m x T R := by
    rw [hRy]
    calc q * k * y ^ 2 * d * y = q * k * (y ^ 2 * y) * d := by ac_rfl
      _ = q * k * y ^ 3 * d := by rw [← pow_succ]
      _ = q * k * y ^ 2 * d := by rw [hx3 y]
  -- peel `aᵢ` off `y` and absorb
  have hsplit : y = m (x i) * ∏ j ∈ (C \ A).erase i, m (x j) :=
    (Finset.mul_prod_erase _ _ hi).symm
  rw [hsplit] at hRabs
  exact mul_right_absorb hRabs

/-- The positions of `R` not absorbed by `p(R)`. -/
def nSet (R : Finset ι) : Finset ι :=
  R.filter fun i => ctxProd m x T R * m (x i) ≠ ctxProd m x T R

lemma nSet_subset (R : Finset ι) : nSet m x T R ⊆ R :=
  Finset.filter_subset _ _

include hx3 in
/-- **Injectivity on the unabsorbed positions**: `2^{|N_R|} ≤ |M|`. -/
lemma two_pow_card_nSet_le {R : Finset ι} (hR : R ⊆ prodEss m x T) :
    2 ^ (nSet m x T R).card ≤ Fintype.card M := by
  classical
  have hinj : Set.InjOn (fun S => ctxProd m x T S)
      ((nSet m x T R).powerset : Finset (Finset ι)) := by
    intro A hA C hC hpp
    rw [Finset.mem_coe, Finset.mem_powerset] at hA hC
    by_contra hne
    -- some position lies in exactly one of the two
    have hex : ∃ i, (i ∈ C ∧ i ∉ A) ∨ (i ∈ A ∧ i ∉ C) := by
      by_contra hall
      push_neg at hall
      exact hne (Finset.ext fun i =>
        ⟨fun hiA => (hall i).2 hiA, fun hiC => (hall i).1 hiC⟩)
    obtain ⟨i, hcase⟩ := hex
    have hAR : A ⊆ R := hA.trans (nSet_subset m x T R)
    have hCR : C ⊆ R := hC.trans (nSet_subset m x T R)
    rcases hcase with ⟨hiC, hiA⟩ | ⟨hiA, hiC⟩
    · have habs := ctxProd_mul_eq_of_collision hx3 m x T hAR hCR hR hpp
        (Finset.mem_sdiff.mpr ⟨hiC, hiA⟩)
      have hiN : i ∈ nSet m x T R := hC hiC
      exact (Finset.mem_filter.mp hiN).2 habs
    · have habs := ctxProd_mul_eq_of_collision hx3 m x T hCR hAR hR hpp.symm
        (Finset.mem_sdiff.mpr ⟨hiA, hiC⟩)
      have hiN : i ∈ nSet m x T R := hA hiA
      exact (Finset.mem_filter.mp hiN).2 habs
  calc 2 ^ (nSet m x T R).card = (nSet m x T R).powerset.card :=
        (Finset.card_powerset _).symm
    _ ≤ (Finset.univ : Finset M).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    _ = Fintype.card M := Finset.card_univ

include hx3 in
/-- The unabsorbed positions of a subset of the essential set number at most
`⌊log₂|M|⌋`. -/
lemma card_nSet_le_log {R : Finset ι}
    (hR : R ⊆ prodEss m x T) :
    (nSet m x T R).card ≤ Nat.log 2 (Fintype.card M) :=
  Nat.le_log_of_pow_le (by norm_num) (two_pow_card_nSet_le hx3 m x T hR)

/-- The absorbed essential positions of a state `z`. -/
def stabSet (z : M) : Finset ι :=
  (prodEss m x T).filter fun i => z * m (x i) = z

/-- **Absorbed positions are present**: a state cannot absorb an essential
position it does not contain, or the corresponding cube edge would collapse. -/
lemma stabSet_subset {S : Finset ι} (hS : S ⊆ prodEss m x T) :
    stabSet m x T (ctxProd m x T S) ⊆ S := by
  intro i hi
  obtain ⟨hiE, hiz⟩ := Finset.mem_filter.mp hi
  by_contra hiS
  refine ctxProd_ne_erase m x T (Finset.insert_subset hiE hS)
    (Finset.mem_insert_self i S) ?_
  rw [ctxProd_insert m x T hiS, hiz, Finset.erase_insert hiS]

/-- Every subset of the essential set is its unabsorbed part together with the
absorbed part of its state. -/
lemma eq_nSet_union_stabSet {S : Finset ι} (hS : S ⊆ prodEss m x T) :
    S = nSet m x T S ∪ stabSet m x T (ctxProd m x T S) := by
  have hstab : S.filter (fun i => ctxProd m x T S * m (x i) = ctxProd m x T S)
      = stabSet m x T (ctxProd m x T S) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro i hi
      obtain ⟨hiS, hiz⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hS hiS, hiz⟩
    · intro i hi
      exact Finset.mem_filter.mpr
        ⟨stabSet_subset m x T hS hi, (Finset.mem_filter.mp hi).2⟩
  calc S = S.filter (fun i => ctxProd m x T S * m (x i) ≠ ctxProd m x T S)
        ∪ S.filter (fun i => ¬ ctxProd m x T S * m (x i) ≠ ctxProd m x T S) :=
        (Finset.filter_union_filter_not_eq _ S).symm
    _ = nSet m x T S ∪ stabSet m x T (ctxProd m x T S) := by
        rw [← hstab, nSet]
        congr 1
        exact Finset.filter_congr fun i _ => not_not

include hx3 in
/-- **The ball inequality** (`eq:index-two-ball`):
`2^B ≤ |M| · ∑_{j ≤ ⌊log₂|M|⌋} C(B, j)` for `B` the essential width. -/
theorem two_pow_card_prodEss_le (hM : 2 ≤ Fintype.card M) :
    2 ^ (prodEss m x T).card
      ≤ Fintype.card M * ∑ j ∈ range (Nat.log 2 (Fintype.card M) + 1),
          (prodEss m x T).card.choose j := by
  classical
  set E := prodEss m x T with hE
  set ℓ := Nat.log 2 (Fintype.card M) with hℓ
  -- the target of the fiber injection
  set Y : Finset (M × Finset ι) :=
    Finset.univ ×ˢ (E.powerset.filter fun S => S.card ≤ ℓ) with hY
  -- the injection
  have hmaps : ∀ S ∈ E.powerset,
      (ctxProd m x T S, nSet m x T S) ∈ Y := by
    intro S hS
    have hSE : S ⊆ E := Finset.mem_powerset.mp hS
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      ((nSet_subset m x T S).trans hSE), ?_⟩
    exact card_nSet_le_log hx3 m x T hSE
  have hinj : Set.InjOn (fun S => (ctxProd m x T S, nSet m x T S))
      (E.powerset : Finset (Finset ι)) := by
    intro S₁ h₁ S₂ h₂ hpair
    rw [Finset.mem_coe, Finset.mem_powerset] at h₁ h₂
    have hz : ctxProd m x T S₁ = ctxProd m x T S₂ := congrArg Prod.fst hpair
    have hn : nSet m x T S₁ = nSet m x T S₂ := congrArg Prod.snd hpair
    rw [eq_nSet_union_stabSet m x T h₁, eq_nSet_union_stabSet m x T h₂, hz, hn]
  -- counting the target
  have hcount : (E.powerset.filter fun S => S.card ≤ ℓ).card
      = ∑ j ∈ range (ℓ + 1), E.card.choose j := by
    have hset : E.powerset.filter (fun S => S.card ≤ ℓ)
        = (range (ℓ + 1)).biUnion (fun j => E.powersetCard j) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard, Nat.lt_succ_iff]
      constructor
      · rintro ⟨hSE, hcard⟩
        exact ⟨S.card, hcard, hSE, rfl⟩
      · rintro ⟨j, hj, hSE, rfl⟩
        exact ⟨hSE, hj⟩
    rw [hset, Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun j _ => Finset.card_powersetCard j E
    · intro j₁ _ j₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      exact hne ((Finset.mem_powersetCard.mp hS₁).2.symm.trans
        (Finset.mem_powersetCard.mp hS₂).2)
  calc 2 ^ E.card = E.powerset.card := (Finset.card_powerset E).symm
    _ ≤ Y.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = Fintype.card M * ∑ j ∈ range (ℓ + 1), E.card.choose j := by
        rw [hY, Finset.card_product, Finset.card_univ, hcount]

include hx3 in
/-- **The index-two width bound** (`thm:index-two-width`): `x³ = x²` forces
the essential width of the subset product below `5·log₂|M|`. -/
theorem card_prodEss_lt_five_logb (hM : 2 ≤ Fintype.card M) :
    ((prodEss m x T).card : ℝ) < 5 * Real.logb 2 (Fintype.card M) :=
  lt_five_logb_of_ball hM (two_pow_card_prodEss_le hx3 m x T hM)

end IndexTwo

/-- **`ADV±(∏) ≤ 16√(n·5·log₂|M|)`** for a finite commutative monoid with
`x³ = x²` (`eq:index-two-adv`). -/
theorem advPM_prodFun_le_five_logb (hx3 : ∀ z : M, z ^ 3 = z ^ 2)
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * (5 * Real.logb 2 (Fintype.card M))) := by
  set L : ℝ := Real.logb 2 (Fintype.card M) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) (by positivity),
      Real.rpow_one]
    exact_mod_cast hM
  set B₀ : ℕ := Nat.floor (5 * L) with hB₀
  have hB₀pos : 0 < B₀ := by
    have h5 : (5 : ℕ) ≤ B₀ := Nat.le_floor (by push_cast; linarith)
    omega
  have hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ B₀ := by
    intro x T
    exact Nat.le_floor (le_of_lt (card_prodEss_lt_five_logb hx3 m x T hM))
  have h := advPM_prodFun_le_of_width (ι := ι) (σ := σ) m hB₀pos hw
  refine le_trans h ?_
  have hmono : (Fintype.card ι : ℝ) * B₀ ≤ (Fintype.card ι : ℝ) * (5 * L) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact Nat.floor_le (by linarith)
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)

end MonoidProduct
