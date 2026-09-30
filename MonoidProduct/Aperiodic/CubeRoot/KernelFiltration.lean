import MonoidProduct.Aperiodic.CubeRoot.ApexJoint
import MonoidProduct.Aperiodic.CubeRoot.MunnLayer
import Mathlib.Algebra.Algebra.Pi

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The cardinality filtration and the layer drop

The joint kernel's nilpotency runs over a **principal series** of two-sided
ideals of `ℚ[M]`.  Rather than choosing a linear extension of the `J`-order,
the series is the canonical **cardinality filtration**

    `filtration M s = {x : supp x ⊆ {m : |twoIdeal m| ≤ s}}`,

a two-sided ideal for every `s`, with `filtration M 0 = ⊥` and
`filtration M |M| = ⊤`.  Distinct `J`-classes of one ideal size are
incomparable, so their cross products drop, and the top of each layer is a
direct sum of principal factors — no order theory is needed anywhere.

**The layer calculus.**  For an apex `a`, `layerMat a` reads off the class's
coefficient matrix (rows `R`-classes, columns `L`-classes).  On the
filtration ideal at the class's own size it is multiplicative through the
sandwich (`layerMat_mul`), and the coordinate `AlgHom` is its compression
(`coordAlgHom_eq_layer`) — by the multiplication bridge, with the
annihilation-off-the-cone lemmas killing every other class of that size.

**The drop** (`mul_ker_mul_mem_filtration`): a triple product with *outer*
factors in `A_s` and a *middle* factor from the joint kernel inside `A_s`
falls to `A_{s-1}`.  On a regular class the kernel's layer matrix has
`D·X·C = 0` and `MunnLayer.layer_triple_eq_zero` applies; on a null class the
sandwich itself is zero (`sandwichMat_eq_zero_of_not_isRegularClass`).
`MunnLayer.lean`'s counterexample shows the middle position is essential — a
one-sided product does **not** drop.

Iterating the drop triples the exponent per layer and proves
`Ker^(3^|M|) = ⊥` (`ker_pow_exists_eq_bot`).  That exponent is far too big
for the package — but it only has to *exist*: `MunnPackage.lean` converts any
nilpotency into the quantitative `Ker^|M| = ⊥` by strict power descent.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace PrincipalFactor

open Matrix

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## Coefficient kill lemmas

A product's coefficient at `m` only sees factors whose principal ideal
contains `twoIdeal m` — so support bounds pass through multiplication by
anything, on either side. -/

lemma coeff_mul_eq_zero_of_right {s : ℕ} {x y : MonoidAlgebra ℚ M} {m : M}
    (hy : ∀ b : M, s < (twoIdeal b).card → y.coeff b = 0)
    (hm : s < (twoIdeal m).card) : (x * y).coeff m = 0 := by
  classical
  rw [MonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  refine Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₂ _ => ?_
  by_cases h : m₁ * m₂ = m
  · rw [if_pos h, hy m₂ (lt_of_lt_of_le hm (Finset.card_le_card
      (by rw [← h]; exact twoIdeal_mul_subset_right m₁ m₂))), mul_zero]
  · rw [if_neg h]

lemma coeff_mul_eq_zero_of_left {s : ℕ} {x y : MonoidAlgebra ℚ M} {m : M}
    (hx : ∀ b : M, s < (twoIdeal b).card → x.coeff b = 0)
    (hm : s < (twoIdeal m).card) : (x * y).coeff m = 0 := by
  classical
  rw [MonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  refine Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₂ _ => ?_
  by_cases h : m₁ * m₂ = m
  · rw [if_pos h, hx m₁ (lt_of_lt_of_le hm (Finset.card_le_card
      (by rw [← h]; exact twoIdeal_mul_subset_left m₁ m₂))), zero_mul]
  · rw [if_neg h]

/-! ## The cardinality filtration -/

variable (M) in
/-- **The cardinality filtration**: the elements supported on the monoid
elements whose principal two-sided ideal has at most `s` elements — a
two-sided ideal of the monoid algebra, since `twoIdeal (u·m·v) ⊆ twoIdeal m`. -/
def filtration (s : ℕ) : Ideal (MonoidAlgebra ℚ M) where
  carrier := {x | ∀ m : M, s < (twoIdeal m).card → x.coeff m = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hx hy m hm => by
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx m hm, hy m hm, add_zero]
  smul_mem' := fun c {x} hx m hm => by
    rw [smul_eq_mul]
    exact coeff_mul_eq_zero_of_right hx hm

lemma mem_filtration {s : ℕ} {x : MonoidAlgebra ℚ M} :
    x ∈ filtration M s ↔ ∀ m : M, s < (twoIdeal m).card → x.coeff m = 0 := Iff.rfl

instance (s : ℕ) : (filtration M s).IsTwoSided :=
  ⟨fun _b hx _m hm => coeff_mul_eq_zero_of_left hx hm⟩

/-- Everything lives at the carrier size. -/
lemma mem_filtration_card (x : MonoidAlgebra ℚ M) : x ∈ filtration M (Fintype.card M) := by
  intro m hm
  refine absurd hm ?_
  have h := Finset.card_le_univ (twoIdeal m)
  omega

/-- The filtration starts at `⊥`: every principal ideal is nonempty. -/
lemma eq_zero_of_mem_filtration_zero {x : MonoidAlgebra ℚ M}
    (hx : x ∈ filtration M 0) : x = 0 := by
  ext m
  rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  exact hx m (Finset.card_pos.2 ⟨m, self_mem_twoIdeal m⟩)

/-- The canonical decomposition into singles. -/
lemma repr_eq (x : MonoidAlgebra ℚ M) :
    x = ∑ m ∈ x.coeff.support, MonoidAlgebra.single m (x.coeff m) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
  rfl

lemma card_le_of_mem_support {s : ℕ} {x : MonoidAlgebra ℚ M}
    (hx : x ∈ filtration M s) {m : M} (hm : m ∈ x.coeff.support) :
    (twoIdeal m).card ≤ s := by
  by_contra h
  exact Finsupp.mem_support_iff.1 hm (hx m (by omega))

/-! ## The layer matrix -/

variable [IsAperiodicMonoid M]

lemma cellEquiv_apply {a : M} (z : JType M a) :
    cellEquiv M a z = (rIdx M z, lIdx M z) := rfl

/-- **The layer matrix at an apex `a`**: the class's coefficients of `x`,
arranged on the cells.  Linear in `x`; the filtration layer at size
`|twoIdeal a|` is read class by class through these. -/
noncomputable def layerMat (a : M) :
    MonoidAlgebra ℚ M →ₗ[ℚ] Matrix (RIdx M a) (LIdx M a) ℚ where
  toFun x := Matrix.of fun i l => x.coeff ((cellEquiv M a).symm (i, l)).1
  map_add' x y := by
    ext i l
    simp [MonoidAlgebra.coeff_add]
  map_smul' c x := by
    ext i l
    simp [MonoidAlgebra.coeff_smul]

lemma layerMat_apply {a : M} (x : MonoidAlgebra ℚ M) (i : RIdx M a) (l : LIdx M a) :
    layerMat a x i l = x.coeff ((cellEquiv M a).symm (i, l)).1 := rfl

/-- The layer matrix reads the coefficient at each cell. -/
lemma layerMat_apply_cell {a : M} (x : MonoidAlgebra ℚ M) (z : JType M a) :
    layerMat a x (rIdx M z) (lIdx M z) = x.coeff z.1 := by
  rw [layerMat_apply, ← cellEquiv_apply, Equiv.symm_apply_apply]

/-- On a class element, the layer matrix of a single is a matrix single. -/
lemma layerMat_single_of_mem {a : M} (z : JType M a) (c : ℚ) :
    layerMat a (MonoidAlgebra.single z.1 c) = Matrix.single (rIdx M z) (lIdx M z) c := by
  ext i l
  rw [layerMat_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, Matrix.single_apply]
  by_cases h : rIdx M z = i ∧ lIdx M z = l
  · obtain ⟨h1, h2⟩ := h
    have hw : (cellEquiv M a).symm (i, l) = z := by
      rw [Equiv.symm_apply_eq, cellEquiv_apply]
      exact Prod.ext h1.symm h2.symm
    rw [if_pos (congrArg Subtype.val hw).symm, if_pos ⟨h1, h2⟩]
  · rw [if_neg, if_neg h]
    intro hc
    refine h ?_
    have hw : (cellEquiv M a).symm (i, l) = z := Subtype.ext hc.symm
    have hp : (i, l) = cellEquiv M a z := by rw [← hw, Equiv.apply_symm_apply]
    rw [cellEquiv_apply] at hp
    exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩

/-- Off the class, the layer matrix of a single vanishes. -/
lemma layerMat_single_of_notMem {a m : M} (h : m ∉ jClass M a) (c : ℚ) :
    layerMat a (MonoidAlgebra.single m c) = 0 := by
  ext i l
  rw [layerMat_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    Matrix.zero_apply, if_neg]
  intro hc
  exact h (hc ▸ ((cellEquiv M a).symm (i, l)).2)

/-! ## The double-product formula

Uniform over the class — regular or null: the sandwich carries the survival
data and `rIdx_mul`/`lIdx_mul` carry the target cell. -/

/-- Same size and comparable is equal: an element of the filtration at the
class's size whose ideal contains the class's ideal is in the class. -/
lemma mem_jClass_of_card_le {a m : M} (hle : (twoIdeal m).card ≤ (twoIdeal a).card)
    (hsub : twoIdeal a ⊆ twoIdeal m) : m ∈ jClass M a :=
  mem_jClass.2 (Finset.eq_of_subset_of_card_le hsub hle).symm

/-- **The basis case**: singles at the layer size multiply through the
sandwich. -/
lemma layerMat_single_mul_single {a : M} {m' m : M}
    (hm' : (twoIdeal m').card ≤ (twoIdeal a).card)
    (hm : (twoIdeal m).card ≤ (twoIdeal a).card) (c' c : ℚ) :
    layerMat a (MonoidAlgebra.single m' c' * MonoidAlgebra.single m c)
      = layerMat a (MonoidAlgebra.single m' c') * sandwichMat M a
          * layerMat a (MonoidAlgebra.single m c) := by
  rw [MonoidAlgebra.single_mul_single]
  by_cases hm'J : m' ∈ jClass M a
  · by_cases hmJ : m ∈ jClass M a
    · rw [layerMat_single_of_mem (⟨m', hm'J⟩ : JType M a) c',
        layerMat_single_of_mem (⟨m, hmJ⟩ : JType M a) c,
        Matrix.single_mul_mul_single, sandwichMat_apply]
      by_cases hsurv : twoIdeal (m' * m) = twoIdeal a
      · rw [layerMat_single_of_mem (⟨m' * m, mem_jClass.2 hsurv⟩ : JType M a) (c' * c),
          rIdx_mul ⟨m', hm'J⟩ ⟨m, hmJ⟩ hsurv, lIdx_mul ⟨m', hm'J⟩ ⟨m, hmJ⟩ hsurv,
          if_pos ((sandwich_eq_true_iff ⟨m', hm'J⟩ ⟨m, hmJ⟩).2 hsurv), mul_one]
      · rw [layerMat_single_of_notMem (fun hc => hsurv (mem_jClass.1 hc)) (c' * c),
          if_neg (fun hc =>
            hsurv ((sandwich_eq_true_iff ⟨m', hm'J⟩ ⟨m, hmJ⟩).1 hc)),
          mul_zero, zero_mul, Matrix.single_zero]
    · rw [layerMat_single_of_notMem hmJ c, Matrix.mul_zero,
        layerMat_single_of_notMem _ (c' * c)]
      intro hc
      have hsub : twoIdeal a ⊆ twoIdeal m := by
        rw [← mem_jClass.1 hc]
        exact twoIdeal_mul_subset_right m' m
      exact hmJ (mem_jClass_of_card_le hm hsub)
  · rw [layerMat_single_of_notMem hm'J c', Matrix.zero_mul, Matrix.zero_mul,
      layerMat_single_of_notMem _ (c' * c)]
    intro hc
    have hsub : twoIdeal a ⊆ twoIdeal m' := by
      rw [← mem_jClass.1 hc]
      exact twoIdeal_mul_subset_left m' m
    exact hm'J (mem_jClass_of_card_le hm' hsub)

/-- **The double-product formula**: on the filtration ideal at the class's own
size, the layer matrix is multiplicative through the sandwich. -/
theorem layerMat_mul {a : M} {x y : MonoidAlgebra ℚ M}
    (hx : x ∈ filtration M ((twoIdeal a).card))
    (hy : y ∈ filtration M ((twoIdeal a).card)) :
    layerMat a (x * y) = layerMat a x * sandwichMat M a * layerMat a y := by
  calc layerMat a (x * y)
      = ∑ m' ∈ x.coeff.support, ∑ m ∈ y.coeff.support,
          layerMat a (MonoidAlgebra.single m' (x.coeff m')
            * MonoidAlgebra.single m (y.coeff m)) := by
        conv_lhs => rw [repr_eq x, repr_eq y]
        rw [Finset.sum_mul_sum, map_sum]
        exact Finset.sum_congr rfl fun m' _ => map_sum _ _ _
    _ = ∑ m' ∈ x.coeff.support, ∑ m ∈ y.coeff.support,
          layerMat a (MonoidAlgebra.single m' (x.coeff m')) * sandwichMat M a
            * layerMat a (MonoidAlgebra.single m (y.coeff m)) := by
        refine Finset.sum_congr rfl fun m' hm' => Finset.sum_congr rfl fun m hm => ?_
        exact layerMat_single_mul_single (card_le_of_mem_support hx hm')
          (card_le_of_mem_support hy hm) _ _
    _ = layerMat a x * sandwichMat M a * layerMat a y := by
        conv_rhs => rw [repr_eq x, repr_eq y]
        rw [map_sum, map_sum, Matrix.sum_mul, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun m' _ => ?_
        rw [Matrix.mul_sum]

/-! ## The coordinate is the compressed layer -/

/-- **The coordinate `AlgHom` on the filtration ideal at the class's size is
the compressed layer matrix.**  Off the class, both sides die: the coordinate
by annihilation off the cone, the layer matrix by definition. -/
theorem coordAlgHom_eq_layer {a : M} (F : RankFactorization (sandwichMat M a))
    {x : MonoidAlgebra ℚ M} (hx : x ∈ filtration M ((twoIdeal a).card)) :
    coordAlgHom F x = F.D * layerMat a x * F.C := by
  conv_lhs => rw [repr_eq x]
  conv_rhs => rw [repr_eq x]
  rw [map_sum, map_sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hcard := card_le_of_mem_support hx hm
  have hs : MonoidAlgebra.single m (x.coeff m)
      = x.coeff m • MonoidAlgebra.single m (1 : ℚ) := by
    rw [MonoidAlgebra.smul_single', mul_one]
  rw [hs, map_smul, map_smul, Matrix.mul_smul, Matrix.smul_mul]
  refine congrArg (x.coeff m • ·) ?_
  rw [coordAlgHom_single]
  by_cases hmJ : m ∈ jClass M a
  · rw [show compressedRep F (rowColAction M a) m
        = F.D * Matrix.single (rIdx M (⟨m, hmJ⟩ : JType M a))
            (lIdx M (⟨m, hmJ⟩ : JType M a)) (1 : ℚ) * F.C from
      compressedRep_cell_of_mem F ⟨m, hmJ⟩,
      layerMat_single_of_mem (⟨m, hmJ⟩ : JType M a) (1 : ℚ)]
  · rw [compressedRep_eq_zero_of_not_subset F m
        (fun hsub => hmJ (mem_jClass_of_card_le hcard hsub)),
      layerMat_single_of_notMem hmJ, Matrix.mul_zero, Matrix.zero_mul]

/-! ## The joint kernel meets the layer -/

/-- The joint map's `k`-th coordinate is the `k`-th coordinate `AlgHom`. -/
lemma jointAlgHom_apply_coord (x : MonoidAlgebra ℚ M) (k : Fin (idemIdeals M).card) :
    jointAlgHom M x k = coordAlgHom (jointFactor M k) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      rw [map_zero, map_zero, Pi.zero_apply]
      rfl
  | add f g hf hg =>
      rw [map_add, map_add, Pi.add_apply, hf, hg]
      rfl
  | single m c =>
      rw [jointAlgHom, MonoidAlgebra.lift_single, coordAlgHom, MonoidAlgebra.lift_single]
      rfl

/-- A kernel element's layer matrix is annihilated by the compression, at
every listed apex. -/
lemma compress_layerMat_eq_zero_of_ker {x : MonoidAlgebra ℚ M}
    (hker : x ∈ RingHom.ker (jointAlgHom M).toRingHom) (k : Fin (idemIdeals M).card)
    (hx : x ∈ filtration M ((twoIdeal (jointApex M k)).card)) :
    (jointFactor M k).D * layerMat (jointApex M k) x * (jointFactor M k).C = 0 := by
  rw [← coordAlgHom_eq_layer (jointFactor M k) hx, ← jointAlgHom_apply_coord]
  have h0 : jointAlgHom M x = 0 := RingHom.mem_ker.1 hker
  rw [h0, Pi.zero_apply]
  rfl

/-! ## The layer drop -/

/-- **The middle-kill drop.**  A triple product with outer factors in the
filtration ideal at `s` and a middle factor from the joint kernel inside it
falls to `s - 1`.  Regular classes: the middle's layer matrix is annihilated
by the compression and `MunnLayer.layer_triple_eq_zero` closes the sandwich;
null classes: the sandwich is zero outright.  The *middle* position is
essential — `MunnLayer.layer_kernel_mul_ne_zero` refutes the one-sided
version. -/
theorem mul_ker_mul_mem_filtration {s : ℕ} {w x y : MonoidAlgebra ℚ M}
    (hw : w ∈ filtration M s) (hx : x ∈ filtration M s) (hy : y ∈ filtration M s)
    (hker : x ∈ RingHom.ker (jointAlgHom M).toRingHom) :
    w * x * y ∈ filtration M (s - 1) := by
  intro m hm
  by_cases hcard : s < (twoIdeal m).card
  · have hwx : ∀ b : M, s < (twoIdeal b).card → (w * x).coeff b = 0 :=
      fun b hb => coeff_mul_eq_zero_of_left hw hb
    exact coeff_mul_eq_zero_of_left hwx hcard
  · -- the boundary: `m` sits at size exactly `s`
    have hpos : 0 < (twoIdeal m).card := Finset.card_pos.2 ⟨m, self_mem_twoIdeal m⟩
    have hcs : (twoIdeal m).card = s := by omega
    by_cases hreg : IsRegularClass m
    · -- regular: read the coefficient at the listed apex and kill the middle
      obtain ⟨k, hk⟩ := exists_index_of_isRegularClass hreg
      rw [jointCoord_apex] at hk
      have hmJ : m ∈ jClass M (jointApex M k) := mem_jClass.2 hk.symm
      have hca : (twoIdeal (jointApex M k)).card = s := by rw [hk, hcs]
      have hw' : w ∈ filtration M ((twoIdeal (jointApex M k)).card) := by rwa [hca]
      have hx' : x ∈ filtration M ((twoIdeal (jointApex M k)).card) := by rwa [hca]
      have hy' : y ∈ filtration M ((twoIdeal (jointApex M k)).card) := by rwa [hca]
      have hwx' : w * x ∈ filtration M ((twoIdeal (jointApex M k)).card) :=
        Ideal.mul_mem_right _ _ hw'
      have hlayer : layerMat (jointApex M k) (w * x * y) = 0 := by
        rw [layerMat_mul hwx' hy', layerMat_mul hw' hx',
          ← (jointFactor M k).factor]
        exact MunnLayer.layer_triple_eq_zero (jointFactor M k).C (jointFactor M k).D
          _ _ _ (compress_layerMat_eq_zero_of_ker hker k hx')
      have := layerMat_apply_cell (w * x * y) (⟨m, hmJ⟩ : JType M (jointApex M k))
      rw [hlayer, Matrix.zero_apply] at this
      exact this.symm
    · -- null: the sandwich is zero, one product formula suffices
      have hmJ : m ∈ jClass M m := self_mem_jClass m
      have hw' : w ∈ filtration M ((twoIdeal m).card) := by rwa [hcs]
      have hx' : x ∈ filtration M ((twoIdeal m).card) := by rwa [hcs]
      have hy' : y ∈ filtration M ((twoIdeal m).card) := by rwa [hcs]
      have hwx' : w * x ∈ filtration M ((twoIdeal m).card) :=
        Ideal.mul_mem_right _ _ hw'
      have hlayer : layerMat m (w * x * y) = 0 := by
        rw [layerMat_mul hwx' hy', sandwichMat_eq_zero_of_not_isRegularClass hreg,
          Matrix.mul_zero, Matrix.zero_mul]
      have := layerMat_apply_cell (w * x * y) (⟨m, hmJ⟩ : JType M m)
      rw [hlayer, Matrix.zero_apply] at this
      exact this.symm

/-! ## Existence of a nilpotency exponent

The drop triples the power per filtration level: from `Ker^n ⊆ A_s` and the
drop, `Ker^(3n) = Ker^n · Ker^n · Ker^n ⊆ A_s·(Ker ∩ A_s)·A_s ⊆ A_(s-1)`.
Starting at `A_(card M) = ⊤` and descending `card M` levels gives
`Ker^(3^(card M)) = ⊥` — an *existence* statement only; `MunnPackage.lean`
sharpens the exponent to `card M` by strict power descent. -/

/-- One level of the descent. -/
lemma ker_pow_three_mul_le {s n : ℕ} (hn : 0 < n)
    (h : ∀ z ∈ RingHom.ker (jointAlgHom M).toRingHom ^ n, z ∈ filtration M s) :
    ∀ z ∈ RingHom.ker (jointAlgHom M).toRingHom ^ (3 * n), z ∈ filtration M (s - 1) := by
  set K := RingHom.ker (jointAlgHom M).toRingHom with hK
  have hpow : K ^ (3 * n) = K ^ n * K ^ n * K ^ n := by
    rw [show 3 * n = n + n + n by ring, Ideal.IsTwoSided.pow_add,
      Ideal.IsTwoSided.pow_add]
  intro z hz
  rw [hpow] at hz
  have key : ∀ u ∈ K ^ n * K ^ n, ∀ y ∈ K ^ n, u * y ∈ filtration M (s - 1) := by
    intro u hu
    refine Submodule.mul_induction_on hu ?_ ?_
    · intro w hw x hx y hy
      exact mul_ker_mul_mem_filtration (h w hw) (h x hx) (h y hy)
        (Ideal.pow_le_self hn.ne' hx)
    · intro u₁ u₂ h₁ h₂ y hy
      rw [add_mul]
      exact Submodule.add_mem _ (h₁ y hy) (h₂ y hy)
  exact Submodule.mul_induction_on hz key fun z₁ z₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂

/-- The full descent: `card M` levels down from the top. -/
lemma ker_pow_le_filtration (k : ℕ) :
    ∀ z ∈ RingHom.ker (jointAlgHom M).toRingHom ^ (3 ^ k),
      z ∈ filtration M (Fintype.card M - k) := by
  induction k with
  | zero =>
      intro z _
      rw [Nat.sub_zero]
      exact mem_filtration_card z
  | succ k ih =>
      have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ, mul_comm]
      have hstep := ker_pow_three_mul_le (n := 3 ^ k) (s := Fintype.card M - k)
        (Nat.pow_pos (by omega)) ih
      rw [← h3] at hstep
      intro z hz
      have hz' := hstep z hz
      rwa [Nat.sub_sub] at hz'

/-- **A nilpotency exponent exists**: `Ker^(3^|M|) = ⊥`. -/
theorem ker_pow_exists_eq_bot :
    RingHom.ker (jointAlgHom M).toRingHom ^ (3 ^ Fintype.card M) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun z hz => ?_
  have hmem := ker_pow_le_filtration (Fintype.card M) z hz
  rw [Nat.sub_self] at hmem
  exact eq_zero_of_mem_filtration_zero hmem

end PrincipalFactor

end MonoidProduct
