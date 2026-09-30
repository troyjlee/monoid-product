import MonoidProduct.Dyck.Monoid.Peel
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
set_option linter.style.header false

/-!
# The contracted Dyck algebra is split semisimple (`monoid.tex`, `prop:dyck-munn-peel`,
item 3)

`eq:dyck-contracted-decomposition`:

  `ℚ₀[M_k] ≅ ⊕_{s=0}^{k} M_{s+1}(ℚ)`,   `Rad(ℚ₀[M_k]) = 0`.

**The contracted algebra** is the honest quotient `DyckContracted k =
ℚ[M_k] / dyckZeroIdeal k`, where `dyckZeroIdeal k` is the ideal spanned by the
zero of `M_k` (two-sided because that zero is central, `dyckZero_mul_comm`).

**The Munn map.**  Level `s` acts on its `s + 1` intervals `[p, p + k − s]`,
`0 ≤ p ≤ s` (the idempotents `[s; p, p]`): an element `x` sends `p` to `p + e`
exactly when the interval lies in the domain of `x`, i.e. `a ≤ p ∧ p + b ≤ s`
(`dyckMunnEntry`).  With the row convention this is multiplicative for the
sequential product (`dyckMunnEntry_mul`, pure `max` arithmetic), giving
`dyckMunnHom : M_k →* ⊕_s M_{s+1}(ℚ)` with `0 ↦ 0`, and its linear extension
`dyckMunnAlgHom`.  A level-`u` element vanishes in blocks `s < u`
(`dyckMunnEntry_live_of_lt`) and is the matrix unit `E_{ij}` in block `u`
(`dyckMunnEntry_live_self`): the map is unitriangular in the level.

**Surjectivity by Möbius inversion** (`dyckMunnAlgHom_surjective`): the strict
restrictions of `[s; p, q]` to a one-shorter interval are `[s+1; p+1, q+1]` and
`[s+1; p, q]`, and both meet in `[s+2; p+1, q+1]`, so
`[s;p,q] − [s+1;p+1,q+1] − [s+1;p,q] + [s+2;p+1,q+1]` (terms of level `> k`
omitted) maps to the single matrix unit `E_{pq}` of block `s`
(`dyckMunnAlgHom_unitPre`).  Then rank–nullity against
`dim ℚ[M_k] = |M_k| = Σ (s+1)² + 1` pins the kernel to the line `ℚ·0`
(`ker_dyckMunnAlgHom`), which is `dyckZeroIdeal k`.  This replaces the paper's
appeal to Munn's theorem plus the radical-dimension count by a direct
computation; the conclusion is the same.

Main results: `dyckContractedEquiv : ℚ₀[M_k] ≃ₐ[ℚ] Π s : Fin (k+1),
M_{s+1}(ℚ)`, `finrank_dyckContracted`, the `IsSemisimpleRing` instance, and
`jacobson_dyckContracted : Ring.jacobson ℚ₀[M_k] = ⊥`.
-/

namespace MonoidProduct

open DyckNF DyckTriple

variable {k : ℕ}

/-- A maximum of two nonnegative-dominated integers, as a natural number. -/
lemma dyckAlg_max_facts (x y : ℤ) (h : 0 ≤ x) :
    ∃ m : ℕ, max x y = m ∧ x ≤ m ∧ y ≤ m ∧ ((m : ℤ) = x ∨ (m : ℤ) = y) :=
  ⟨(max x y).toNat, by
    rw [Int.toNat_of_nonneg (le_trans h (le_max_left _ _))]
    exact ⟨rfl, le_max_left _ _, le_max_right _ _, max_choice _ _⟩⟩

/-- The Munn entry of `x` at level `s`, row `p`, column `q`. -/
def dyckMunnEntry : DyckNF k → ℕ → ℕ → ℕ → ℚ
  | .zero, _, _, _ => 0
  | .live t, s, p, q => if t.a ≤ p ∧ p + t.b ≤ s ∧ (q : ℤ) = p + t.e then 1 else 0

lemma dyckMunnEntry_mul (x y : DyckNF k) {s : ℕ} (hs : s ≤ k) (p r : Fin (s + 1)) :
    ∑ q : Fin (s + 1), dyckMunnEntry x s p q * dyckMunnEntry y s q r
      = dyckMunnEntry (x * y) s p r := by
  cases x with
  | zero => simp [dyckMunnEntry]
  | live t₁ =>
    cases y with
    | zero => simp [dyckMunnEntry]
    | live t₂ =>
      have hp := p.isLt; have hr := r.isLt
      have := t₁.lower; have := t₁.upper; have := t₂.lower; have := t₂.upper
      have := t₁.budget; have := t₂.budget
      let q₀ : Fin (s + 1) := ⟨min (((p : ℕ) : ℤ) + t₁.e).toNat s, by omega⟩
      rw [Finset.sum_eq_single q₀]
      · rw [live_mul_live]
        unfold DyckTriple.comp
        obtain ⟨A, hA, hA1, hA2, hA3⟩ :=
          dyckAlg_max_facts (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e) (by positivity)
        obtain ⟨B, hB, hB1, hB2, hB3⟩ :=
          dyckAlg_max_facts (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e) (by positivity)
        split_ifs with hk
        · simp only [dyckMunnEntry, compT_a, compT_b, compT_e, q₀, hA, hB, Int.toNat_natCast]
          split_ifs <;> simp only [mul_one, mul_zero] <;> first | rfl | (exfalso; omega)
        · simp only [dyckMunnEntry, q₀]
          rw [hA, hB] at hk
          split_ifs <;> simp only [mul_one, mul_zero]
          exfalso; omega
      · intro q _ hq
        simp only [dyckMunnEntry]
        split_ifs with h1 h2 <;> simp only [mul_one, mul_zero]
        exact absurd (Fin.ext (by simp only [q₀]; omega)) hq
      · intro h; exact absurd (Finset.mem_univ _) h

/-- The block algebra `⊕_{s=0}^{k} M_{s+1}(ℚ)`. -/
abbrev DyckBlocks (k : ℕ) : Type := Π s : Fin (k + 1), Matrix (Fin (s + 1)) (Fin (s + 1)) ℚ

/-- The Munn representation of `x`, one `(s+1) × (s+1)` block per level `s`. -/
def dyckMunnRep (x : DyckNF k) : DyckBlocks k := fun s p q => dyckMunnEntry x s p q

/-- The Munn representation is a monoid homomorphism (zero goes to zero). -/
def dyckMunnHom (k : ℕ) : DyckNF k →* DyckBlocks k where
  toFun := dyckMunnRep
  map_one' := by
    funext s; ext p q
    have := p.isLt; have := q.isLt; have := s.isLt
    change dyckMunnEntry (DyckNF.live (oneT k)) s p q = (1 : Matrix _ _ ℚ) p q
    rw [Matrix.one_apply]
    refine if_congr ?_ rfl rfl
    simp only [oneT, Fin.ext_iff]
    omega
  map_mul' x y := by
    funext s; ext p r
    simp only [dyckMunnRep, Pi.mul_apply, Matrix.mul_apply]
    exact (dyckMunnEntry_mul x y (Nat.lt_succ_iff.mp s.isLt) p r).symm

lemma dyckMunnHom_apply (x : DyckNF k) (s : Fin (k + 1)) (p q : Fin (s + 1)) :
    dyckMunnHom k x s p q = dyckMunnEntry x s p q := rfl

/-- **Level `u` is invisible below block `u`**: a level-`u` element acts as zero in
every block `s < u`. -/
theorem dyckMunnEntry_live_of_lt {t : DyckTriple k} {s p q : ℕ} (h : s < t.a + t.b) :
    dyckMunnEntry (DyckNF.live t) s p q = 0 :=
  if_neg (by omega)

/-- **In its own block, `[s; i, j]` is the matrix unit `E_{ij}`**, with
`i = t.a`, `j = t.a + t.e`. -/
theorem dyckMunnEntry_live_self {t : DyckTriple k} (p q : ℕ) :
    dyckMunnEntry (DyckNF.live t) (t.a + t.b) p q
      = if p = t.a ∧ (q : ℤ) = t.a + t.e then 1 else 0 :=
  if_congr (by constructor <;> intro h <;> constructor <;> omega) rfl rfl

@[simp] lemma dyckMunnHom_zero : dyckMunnHom k DyckNF.zero = 0 := by
  funext s; ext p q; rfl

/-- The linear extension `ℚ[M_k] → ⊕_s M_{s+1}(ℚ)`. -/
noncomputable def dyckMunnAlgHom (k : ℕ) : MonoidAlgebra ℚ (DyckNF k) →ₐ[ℚ] DyckBlocks k :=
  MonoidAlgebra.lift ℚ (DyckBlocks k) (DyckNF k) (dyckMunnHom k)

lemma dyckMunnAlgHom_single (x : DyckNF k) (c : ℚ) :
    dyckMunnAlgHom k (MonoidAlgebra.single x c) = c • dyckMunnHom k x :=
  MonoidAlgebra.lift_single _ _ _

/-! ## Möbius inversion: matrix units in the image -/

/-- The basis element `[u; i, i + e]`, or `0` when the level `u` exceeds `k`. -/
noncomputable def dyckAlgElt (k u i : ℕ) (e : ℤ) : MonoidAlgebra ℚ (DyckNF k) :=
  if h : u ≤ k ∧ i ≤ u ∧ -(i : ℤ) ≤ e ∧ e ≤ ((u - i : ℕ) : ℤ) then
    MonoidAlgebra.single (DyckNF.live ⟨i, u - i, e, by omega, by omega, by omega⟩) 1
  else 0

lemma dyckMunnAlgHom_elt {u i : ℕ} {e : ℤ} (hiu : i ≤ u) (he₁ : -(i : ℤ) ≤ e)
    (he₂ : e ≤ ((u - i : ℕ) : ℤ)) (s : Fin (k + 1)) (p q : Fin (s + 1)) :
    dyckMunnAlgHom k (dyckAlgElt k u i e) s p q
      = if i ≤ (p : ℕ) ∧ (p : ℕ) + u ≤ s + i ∧ ((q : ℕ) : ℤ) = p + e then 1 else 0 := by
  have hs := s.isLt
  unfold dyckAlgElt
  split_ifs with h h'
  · rw [dyckMunnAlgHom_single, one_smul]
    simp only [dyckMunnHom, MonoidHom.coe_mk, OneHom.coe_mk, dyckMunnRep, dyckMunnEntry]
    rw [if_pos (by omega)]
  · rw [dyckMunnAlgHom_single, one_smul]
    simp only [dyckMunnHom, MonoidHom.coe_mk, OneHom.coe_mk, dyckMunnRep, dyckMunnEntry]
    rw [if_neg (by omega)]
  · exfalso; omega
  · rfl

/-- The Möbius combination `[s;p,q] − [s+1;p+1,q+1] − [s+1;p,q] + [s+2;p+1,q+1]`:
`x` minus its strict restrictions, the preimage of a single matrix unit. -/
noncomputable def dyckAlgUnitPre (k s p q : ℕ) : MonoidAlgebra ℚ (DyckNF k) :=
  dyckAlgElt k s p ((q : ℤ) - p) - dyckAlgElt k (s + 1) (p + 1) ((q : ℤ) - p)
    - dyckAlgElt k (s + 1) p ((q : ℤ) - p) + dyckAlgElt k (s + 2) (p + 1) ((q : ℤ) - p)

/-- **The Möbius combination maps to the matrix unit `E_{pq}` in block `s`.** -/
theorem dyckMunnAlgHom_unitPre {s p q : ℕ} (hp : p ≤ s) (hq : q ≤ s)
    (s' : Fin (k + 1)) (p' q' : Fin (s' + 1)) :
    dyckMunnAlgHom k (dyckAlgUnitPre k s p q) s' p' q'
      = if (s' : ℕ) = s ∧ (p' : ℕ) = p ∧ (q' : ℕ) = q then 1 else 0 := by
  unfold dyckAlgUnitPre
  simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply, Matrix.add_apply, Matrix.sub_apply]
  rw [dyckMunnAlgHom_elt (by omega) (by omega) (by omega),
    dyckMunnAlgHom_elt (by omega) (by omega) (by omega),
    dyckMunnAlgHom_elt (by omega) (by omega) (by omega),
    dyckMunnAlgHom_elt (by omega) (by omega) (by omega)]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **The Munn map is onto `⊕_s M_{s+1}(ℚ)`**: every block entry is hit by a Möbius
combination. -/
theorem dyckMunnAlgHom_surjective (k : ℕ) : Function.Surjective (dyckMunnAlgHom k) := by
  intro A
  refine ⟨∑ s : Fin (k + 1), ∑ p : Fin (s + 1), ∑ q : Fin (s + 1),
    A s p q • dyckAlgUnitPre k s p q, ?_⟩
  funext s'; ext p' q'
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single s']
  · rw [Finset.sum_eq_single p']
    · rw [Finset.sum_eq_single q']
      · rw [dyckMunnAlgHom_unitPre (by omega) (by omega), if_pos ⟨rfl, rfl, rfl⟩,
          smul_eq_mul, mul_one]
      · intro q _ hq
        rw [dyckMunnAlgHom_unitPre (by omega) (by omega), if_neg, smul_zero]
        exact fun h => hq (Fin.ext h.2.2.symm)
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro p _ hp
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [dyckMunnAlgHom_unitPre (by omega) (by omega), if_neg, smul_zero]
      exact fun h => hp (Fin.ext h.2.1.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro s _ hs
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [dyckMunnAlgHom_unitPre (by omega) (by omega), if_neg, smul_zero]
    exact fun h => hs (Fin.ext h.1.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Dimensions -/

theorem finrank_dyckMonoidAlgebra (k : ℕ) :
    Module.finrank ℚ (MonoidAlgebra ℚ (DyckNF k))
      = (∑ s ∈ Finset.range (k + 1), (s + 1) ^ 2) + 1 := by
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (DyckNF k) ℚ), card_dyckNF_sum]

/-- `dim ⊕_{s=0}^{k} M_{s+1}(ℚ) = Σ (s+1)² = |M_k| − 1`. -/
theorem finrank_dyckBlocks (k : ℕ) :
    Module.finrank ℚ (DyckBlocks k) = ∑ s ∈ Finset.range (k + 1), (s + 1) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun s => (s + 1) * (s + 1)) (k + 1)]
  exact Finset.sum_congr rfl fun s _ => (pow_two _).symm

/-! ## The contracted algebra -/

/-- The zero of `M_k` spans a two-sided ideal: it is central. -/
lemma dyckZero_mul_comm (b : MonoidAlgebra ℚ (DyckNF k)) :
    MonoidAlgebra.single DyckNF.zero 1 * b = b * MonoidAlgebra.single DyckNF.zero 1 := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => rw [mul_zero, zero_mul]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]
  | single m r =>
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, DyckNF.zero_mul_eq,
        DyckNF.mul_zero_eq, one_mul, mul_one]

/-- The **contracting ideal** `ℚ·0` of `ℚ[M_k]`, spanned by the zero of the monoid. -/
noncomputable def dyckZeroIdeal (k : ℕ) : Ideal (MonoidAlgebra ℚ (DyckNF k)) :=
  Ideal.span {MonoidAlgebra.single DyckNF.zero 1}

instance (k : ℕ) : (dyckZeroIdeal k).IsTwoSided where
  mul_mem_of_left b h := by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp h
    rw [mul_assoc, dyckZero_mul_comm, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- The **contracted rational algebra** `ℚ₀[M_k] = ℚ[M_k] / ℚ·0`. -/
abbrev DyckContracted (k : ℕ) : Type := MonoidAlgebra ℚ (DyckNF k) ⧸ dyckZeroIdeal k

/-- The kernel of the Munn map is exactly the contracting ideal. -/
theorem ker_dyckMunnAlgHom (k : ℕ) : RingHom.ker (dyckMunnAlgHom k) = dyckZeroIdeal k := by
  set z : MonoidAlgebra ℚ (DyckNF k) := MonoidAlgebra.single DyckNF.zero 1 with hz
  have hfz : dyckMunnAlgHom k z = 0 := by
    rw [hz, dyckMunnAlgHom_single, dyckMunnHom_zero, smul_zero]
  refine le_antisymm ?_ ?_
  · -- rank–nullity: the kernel is one-dimensional
    set f := (dyckMunnAlgHom k).toLinearMap
    have hrange : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.mpr (dyckMunnAlgHom_surjective k)
    have hdim := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, finrank_top, finrank_dyckBlocks, finrank_dyckMonoidAlgebra] at hdim
    have hker : Module.finrank ℚ (LinearMap.ker f) = 1 := by omega
    have hzker : z ∈ LinearMap.ker f := hfz
    have hz0 : (⟨z, hzker⟩ : LinearMap.ker f) ≠ 0 := by
      intro h
      have := congrArg Subtype.val h
      exact (MonoidAlgebra.single_ne_zero.mpr one_ne_zero) this
    intro x hx
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hz0).mp hker ⟨x, hx⟩
    have hc' : c • z = x := congrArg Subtype.val hc
    rw [← hc', Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [dyckZeroIdeal, Ideal.span_le, Set.singleton_subset_iff]
    exact hfz

/-! ## Item 3 -/

/-- **`ℚ₀[M_k] ≅ ⊕_{s=0}^{k} M_{s+1}(ℚ)`** (`eq:dyck-contracted-decomposition`), induced
by the Munn representation. -/
noncomputable def dyckContractedEquiv (k : ℕ) : DyckContracted k ≃ₐ[ℚ] DyckBlocks k :=
  (Ideal.quotientEquivAlgOfEq ℚ (ker_dyckMunnAlgHom k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (dyckMunnAlgHom_surjective k))

@[simp] lemma dyckContractedEquiv_mk (x : MonoidAlgebra ℚ (DyckNF k)) :
    dyckContractedEquiv k (Ideal.Quotient.mk _ x) = dyckMunnAlgHom k x := rfl

/-- `dim_ℚ ℚ₀[M_k] = Σ_{s=0}^{k} (s+1)² = |M_k| − 1`. -/
theorem finrank_dyckContracted (k : ℕ) :
    Module.finrank ℚ (DyckContracted k) = Fintype.card (DyckNF k) - 1 := by
  rw [(dyckContractedEquiv k).toLinearEquiv.finrank_eq, finrank_dyckBlocks, card_dyckNF_sum,
    Nat.add_sub_cancel]

/-- `ℚ₀[M_k]` is semisimple. -/
instance (k : ℕ) : IsSemisimpleRing (DyckContracted k) :=
  RingHom.isSemisimpleRing_of_surjective ((dyckContractedEquiv k).symm : DyckBlocks k →+* _)
    (dyckContractedEquiv k).symm.surjective

/-- **`Rad(ℚ₀[M_k]) = 0`** (`eq:dyck-contracted-decomposition`). -/
theorem jacobson_dyckContracted (k : ℕ) : Ring.jacobson (DyckContracted k) = ⊥ :=
  IsSemisimpleRing.jacobson_eq_bot _

end MonoidProduct
