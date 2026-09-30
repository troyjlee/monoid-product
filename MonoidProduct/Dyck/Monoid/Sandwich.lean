import MonoidProduct.Dyck.Monoid.Peel
import MonoidProduct.Aperiodic.CubeRoot.PrincipalMatrix
set_option linter.style.header false

/-!
# The Dyck sandwich matrices in the cube-root library's language (`monoid.tex`,
`prop:dyck-munn-peel`, item 2, `eq:dyck-block-square`)

Item 2 says the level-`s` principal factor is the Brandt semigroup of
`(s+1) × (s+1)` matrix units, so its sandwich matrix is the identity and
`d_{J_s} = s + 1`, `|J_s| = d_{J_s}²`.  Here `d_J` is read in the cube-root
library's own terms: the rational rank of `PrincipalFactor.sandwichMat`, the
matrix the apex coordinates (`ApexBuild`, `ApexJoint`) are built from.

* `dyck_rEq_iff` / `dyck_lEq_iff`: inside a level, Green's `R` is "same domain
  start `i`" and `L` is "same range start `j`" — each proved by one inverse
  factor (`[s;i,j]·([s;i,j]⁻¹·[s;i,j']) = [s;i,j']`), and conversely by the
  composition formula (a one-sided multiple has a smaller domain or range, of
  the same length only if equal);
* `dyckRIdxEquiv` / `dyckLIdxEquiv`: the `R`- and `L`-classes of `J_s` are
  indexed by `Fin (s+1)`;
* `dyck_sandwichMat_eq`: under these indexings the sandwich matrix **is** the
  identity (the Brandt law `live_mul_live_of_eq` / `lt_dyckLevel_mul_of_ne`);
* `dyck_sandwichMat_rank : rank = s + 1` and
  `dyck_card_jClass : |J_s| = (s+1)² = rank²` — equality in the library's
  charge `rank_sq_le_card_jClass`.
-/

namespace MonoidProduct

open DyckNF DyckTriple PrincipalFactor

variable {k : ℕ}

/-! ## `J`-classes are levels -/

lemma dyck_twoIdeal_eq_iff (x y : DyckNF k) :
    twoIdeal x = twoIdeal y ↔ dyckLevel x = dyckLevel y := by
  constructor
  · intro h
    have h1 := (mem_twoIdeal_iff_dyckLevel x y).1 (h ▸ self_mem_twoIdeal y)
    have h2 := (mem_twoIdeal_iff_dyckLevel y x).1 (h.symm ▸ self_mem_twoIdeal x)
    omega
  · intro h
    ext z
    rw [mem_twoIdeal_iff_dyckLevel, mem_twoIdeal_iff_dyckLevel, h]

/-- An element of the `J`-class of `[s; ·, ·]` is a live triple of level `s`. -/
lemma dyck_mem_jClass_live {t₀ : DyckTriple k} {x : DyckNF k}
    (hx : x ∈ jClass (DyckNF k) (DyckNF.live t₀)) :
    ∃ u : DyckTriple k, x = DyckNF.live u ∧ u.a + u.b = t₀.a + t₀.b := by
  rw [mem_jClass, dyck_twoIdeal_eq_iff, dyckLevel_live] at hx
  cases x with
  | zero => rw [dyckLevel_zero] at hx; have := t₀.budget; omega
  | live u => exact ⟨u, rfl, hx⟩

lemma dyck_live_mem_jClass {t₀ u : DyckTriple k} (h : u.a + u.b = t₀.a + t₀.b) :
    DyckNF.live u ∈ jClass (DyckNF k) (DyckNF.live t₀) := by
  rw [mem_jClass, dyck_twoIdeal_eq_iff, dyckLevel_live, dyckLevel_live, h]

/-! ## Green's `R` and `L` inside a level -/

/-- The composition coordinates as natural numbers, with the `max` bounds. -/
private lemma dyck_of_mul_eq_live {x y : DyckNF k} {u : DyckTriple k}
    (h : x * y = DyckNF.live u) :
    ∃ t₁ t₂ : DyckTriple k, x = DyckNF.live t₁ ∧ y = DyckNF.live t₂ ∧
      (t₁.a : ℤ) ≤ u.a ∧ (t₂.a : ℤ) - t₁.e ≤ u.a ∧
      (t₁.b : ℤ) ≤ u.b ∧ (t₂.b : ℤ) + t₁.e ≤ u.b ∧ t₁.e + t₂.e = u.e := by
  obtain ⟨t₁, t₂, rfl, rfl, ha, hb, he⟩ := of_mul_eq_live h
  refine ⟨t₁, t₂, rfl, rfl, ?_, ?_, ?_, ?_, he⟩
  · have := le_max_left (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e)
    generalize max (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e) = A at *; omega
  · have := le_max_right (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e)
    generalize max (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e) = A at *; omega
  · have := le_max_left (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e)
    generalize max (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e) = B at *; omega
  · have := le_max_right (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e)
    generalize max (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e) = B at *; omega

private lemma dyck_rLe_of_a_eq {t u : DyckTriple k} (hs : t.a + t.b = u.a + u.b)
    (ha : t.a = u.a) : RLe (DyckNF.live t) (DyckNF.live u) := by
  refine rLe_iff_exists.2 ⟨DyckNF.live u.invT * DyckNF.live t, ?_⟩
  rw [← mul_assoc, live_mul_inv]
  have : u.domT = t.domT := DyckTriple.ext ha.symm (by simp [DyckTriple.domT]; omega) rfl
  rw [this, dom_mul_live]

private lemma dyck_lLe_of_ran_eq {t u : DyckTriple k} (hs : t.a + t.b = u.a + u.b)
    (hr : (t.a : ℤ) + t.e = u.a + u.e) : LLe (DyckNF.live t) (DyckNF.live u) := by
  refine lLe_iff_exists.2 ⟨DyckNF.live t * DyckNF.live u.invT, ?_⟩
  have hx := mul_inv_mul (DyckNF.live t)
  rw [inv_live, mul_assoc, inv_mul_live] at hx
  rw [mul_assoc, inv_mul_live]
  have : u.invT.domT = t.invT.domT := by
    have := t.lower; have := u.lower
    refine DyckTriple.ext ?_ ?_ rfl <;> simp [DyckTriple.domT] <;> omega
  rw [this, hx]

/-- **Green's `R` inside a level is "same domain"**: `[s;i,j] R [s;i',j'] ↔ i = i'`. -/
theorem dyck_rEq_iff {t u : DyckTriple k} (hs : t.a + t.b = u.a + u.b) :
    REq (DyckNF.live t) (DyckNF.live u) ↔ t.a = u.a := by
  refine ⟨fun h => ?_, fun h => rEq_iff.2 ⟨dyck_rLe_of_a_eq hs h, dyck_rLe_of_a_eq hs.symm h.symm⟩⟩
  obtain ⟨q, hq⟩ := rLe_iff_exists.1 (rEq_iff.1 h).1
  obtain ⟨t₁, t₂, h₁, -, h1, -, h3, -, -⟩ := dyck_of_mul_eq_live hq
  cases h₁
  omega

/-- **Green's `L` inside a level is "same range"**: `[s;i,j] L [s;i',j'] ↔ j = j'`. -/
theorem dyck_lEq_iff {t u : DyckTriple k} (hs : t.a + t.b = u.a + u.b) :
    LEq (DyckNF.live t) (DyckNF.live u) ↔ (t.a : ℤ) + t.e = u.a + u.e := by
  refine ⟨fun h => ?_,
    fun h => lEq_iff.2 ⟨dyck_lLe_of_ran_eq hs h, dyck_lLe_of_ran_eq hs.symm h.symm⟩⟩
  obtain ⟨p, hp⟩ := lLe_iff_exists.1 (lEq_iff.1 h).1
  obtain ⟨t₁, t₂, -, h₂, -, h2, -, h4, h5⟩ := dyck_of_mul_eq_live hp
  cases h₂
  omega

/-- **The Brandt law as the sandwich condition**: a product of two level-`s`
elements stays at level `s` iff the range of the first is the domain of the second. -/
theorem dyck_twoIdeal_mul_eq_iff {t u : DyckTriple k} (hs : t.a + t.b = u.a + u.b) :
    twoIdeal (DyckNF.live t * DyckNF.live u) = twoIdeal (DyckNF.live t)
      ↔ (t.a : ℤ) + t.e = u.a := by
  rw [dyck_twoIdeal_eq_iff, dyckLevel_live]
  constructor
  · intro h
    by_contra hne
    have := lt_dyckLevel_mul_of_ne hs hne
    omega
  · intro h
    rw [live_mul_live_of_eq hs h, dyckLevel_live]

/-! ## The `R`- and `L`-classes of a level, indexed by `Fin (s+1)` -/

/-- The domain start `i` of `[s; i, j]` (zero at `0`). -/
def dyckDom : DyckNF k → ℕ
  | .zero => 0
  | .live t => t.a

/-- The range start `j` of `[s; i, j]` (zero at `0`). -/
def dyckRan : DyckNF k → ℕ
  | .zero => 0
  | .live t => ((t.a : ℤ) + t.e).toNat

section Level

variable (t₀ : DyckTriple k)

local notation "Mk" => DyckNF k
local notation "a₀" => DyckNF.live t₀

/-- The coordinate of an `R`-class of `J_s`: its common domain start. -/
noncomputable def dyckRCoord (r : RIdx Mk a₀) : Fin (t₀.a + t₀.b + 1) :=
  ⟨dyckDom (rRep Mk r).1, by
    obtain ⟨u, hu, hs⟩ := dyck_mem_jClass_live (rRep Mk r).2
    rw [hu]; change u.a < _; omega⟩

/-- The coordinate of an `L`-class of `J_s`: its common range start. -/
noncomputable def dyckLCoord (l : LIdx Mk a₀) : Fin (t₀.a + t₀.b + 1) :=
  ⟨dyckRan (lRep Mk l).1, by
    obtain ⟨u, hu, hs⟩ := dyck_mem_jClass_live (lRep Mk l).2
    rw [hu]; change ((u.a : ℤ) + u.e).toNat < _; have := u.upper; omega⟩

lemma dyckRCoord_rIdx (z : JType Mk a₀) : (dyckRCoord t₀ (rIdx Mk z) : ℕ) = dyckDom z.1 := by
  have hR : REq (rRep Mk (rIdx Mk z)).1 z.1 := (rIdx_eq_iff _ _).1 (rIdx_rRep _)
  obtain ⟨u, hu, hus⟩ := dyck_mem_jClass_live (rRep Mk (rIdx Mk z)).2
  obtain ⟨v, hv, hvs⟩ := dyck_mem_jClass_live z.2
  change dyckDom (rRep Mk (rIdx Mk z)).1 = dyckDom z.1
  rw [hu, hv] at hR ⊢
  exact (dyck_rEq_iff (hus.trans hvs.symm)).1 hR

lemma dyckLCoord_lIdx (z : JType Mk a₀) : (dyckLCoord t₀ (lIdx Mk z) : ℕ) = dyckRan z.1 := by
  have hL : LEq (lRep Mk (lIdx Mk z)).1 z.1 := (lIdx_eq_iff _ _).1 (lIdx_lRep _)
  obtain ⟨u, hu, hus⟩ := dyck_mem_jClass_live (lRep Mk (lIdx Mk z)).2
  obtain ⟨v, hv, hvs⟩ := dyck_mem_jClass_live z.2
  change dyckRan (lRep Mk (lIdx Mk z)).1 = dyckRan z.1
  rw [hu, hv] at hL ⊢
  have := (dyck_lEq_iff (hus.trans hvs.symm)).1 hL
  change ((u.a : ℤ) + u.e).toNat = ((v.a : ℤ) + v.e).toNat
  rw [this]

/-- The element `[s; i, j]` of `J_s` as a member of the class. -/
def dyckCell (i j : Fin (t₀.a + t₀.b + 1)) : JType Mk a₀ :=
  ⟨DyckNF.live (levelTriple t₀.budget (i, j)).1,
    dyck_live_mem_jClass (levelTriple t₀.budget (i, j)).2⟩

lemma dyckDom_cell (i j : Fin (t₀.a + t₀.b + 1)) : dyckDom (dyckCell t₀ i j).1 = i := rfl

lemma dyckRan_cell (i j : Fin (t₀.a + t₀.b + 1)) : dyckRan (dyckCell t₀ i j).1 = j := by
  change (((i : ℕ) : ℤ) + (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))).toNat = j
  omega

theorem dyckRCoord_bijective : Function.Bijective (dyckRCoord t₀) := by
  refine ⟨fun r₁ r₂ h => ?_, fun i => ⟨rIdx Mk (dyckCell t₀ i i), ?_⟩⟩
  · rw [← rIdx_rRep r₁, ← rIdx_rRep r₂]
    refine (rIdx_eq_iff _ _).2 ?_
    obtain ⟨u, hu, hus⟩ := dyck_mem_jClass_live (rRep Mk r₁).2
    obtain ⟨v, hv, hvs⟩ := dyck_mem_jClass_live (rRep Mk r₂).2
    have h' : dyckDom (rRep Mk r₁).1 = dyckDom (rRep Mk r₂).1 := congrArg Fin.val h
    rw [hu, hv] at *
    exact (dyck_rEq_iff (hus.trans hvs.symm)).2 h'
  · exact Fin.ext ((dyckRCoord_rIdx t₀ _).trans (dyckDom_cell t₀ i i))

theorem dyckLCoord_bijective : Function.Bijective (dyckLCoord t₀) := by
  refine ⟨fun l₁ l₂ h => ?_, fun j => ⟨lIdx Mk (dyckCell t₀ j j), ?_⟩⟩
  · rw [← lIdx_lRep l₁, ← lIdx_lRep l₂]
    refine (lIdx_eq_iff _ _).2 ?_
    obtain ⟨u, hu, hus⟩ := dyck_mem_jClass_live (lRep Mk l₁).2
    obtain ⟨v, hv, hvs⟩ := dyck_mem_jClass_live (lRep Mk l₂).2
    have h' : dyckRan (lRep Mk l₁).1 = dyckRan (lRep Mk l₂).1 := congrArg Fin.val h
    rw [hu, hv] at *
    have := u.lower; have := v.lower
    change ((u.a : ℤ) + u.e).toNat = ((v.a : ℤ) + v.e).toNat at h'
    exact (dyck_lEq_iff (hus.trans hvs.symm)).2 (by omega)
  · exact Fin.ext ((dyckLCoord_lIdx t₀ _).trans (dyckRan_cell t₀ j j))

/-- **The `R`-classes of `J_s` are indexed by the domain start `i ∈ [0, s]`.** -/
noncomputable def dyckRIdxEquiv : RIdx Mk a₀ ≃ Fin (t₀.a + t₀.b + 1) :=
  Equiv.ofBijective _ (dyckRCoord_bijective t₀)

/-- **The `L`-classes of `J_s` are indexed by the range start `j ∈ [0, s]`.** -/
noncomputable def dyckLIdxEquiv : LIdx Mk a₀ ≃ Fin (t₀.a + t₀.b + 1) :=
  Equiv.ofBijective _ (dyckLCoord_bijective t₀)

/-- **The sandwich matrix of `J_s` is the identity** `I_{s+1}`, read through the
range/domain indexings. -/
theorem dyck_sandwichMat_eq :
    sandwichMat Mk a₀
      = (1 : Matrix (Fin (t₀.a + t₀.b + 1)) (Fin (t₀.a + t₀.b + 1)) ℚ).submatrix
          (dyckLIdxEquiv t₀) (dyckRIdxEquiv t₀) := by
  ext l r
  rw [sandwichMat_apply, Matrix.submatrix_apply, Matrix.one_apply]
  refine if_congr ?_ rfl rfl
  have hb : sandwichBool Mk l r = sandwichBool Mk (lIdx Mk (lRep Mk l)) (rIdx Mk (rRep Mk r)) := by
    rw [lIdx_lRep, rIdx_rRep]
  rw [hb, sandwich_eq_true_iff]
  change _ ↔ dyckLCoord t₀ l = dyckRCoord t₀ r
  rw [Fin.ext_iff]
  change _ ↔ dyckRan (lRep Mk l).1 = dyckDom (rRep Mk r).1
  obtain ⟨u, hu, hus⟩ := dyck_mem_jClass_live (lRep Mk l).2
  obtain ⟨v, hv, hvs⟩ := dyck_mem_jClass_live (rRep Mk r).2
  rw [hu, hv]
  have hJ : twoIdeal (DyckNF.live u) = twoIdeal a₀ := by
    rw [dyck_twoIdeal_eq_iff, dyckLevel_live, dyckLevel_live, hus]
  rw [← hJ, dyck_twoIdeal_mul_eq_iff (hus.trans hvs.symm)]
  have := u.lower
  change _ ↔ ((u.a : ℤ) + u.e).toNat = v.a
  omega

/-- **`d_{J_s} = s + 1`** (`eq:dyck-block-square`): the rational rank of the
level-`s` sandwich matrix, in the cube-root library's sense. -/
theorem dyck_sandwichMat_rank : (sandwichMat Mk a₀).rank = t₀.a + t₀.b + 1 := by
  rw [dyck_sandwichMat_eq, Matrix.rank_submatrix, Matrix.rank_one, Fintype.card_fin]

/-- **`|J_s| = (s+1)² = d_{J_s}²`**: equality in the library's apex charge
`rank_sq_le_card_jClass`. -/
theorem dyck_card_jClass :
    (jClass Mk a₀).card = (t₀.a + t₀.b + 1) ^ 2
      ∧ (jClass Mk a₀).card = (sandwichMat Mk a₀).rank ^ 2 := by
  have h : (jClass Mk a₀).card = (t₀.a + t₀.b + 1) ^ 2 := by
    rw [card_jClass_eq, Fintype.card_congr (dyckRIdxEquiv t₀),
      Fintype.card_congr (dyckLIdxEquiv t₀), Fintype.card_fin, sq]
  exact ⟨h, by rw [h, dyck_sandwichMat_rank]⟩

end Level

end MonoidProduct
