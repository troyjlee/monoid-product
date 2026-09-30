import MonoidProduct.Aperiodic.CubeRoot.LocallyThinCompiler
import MonoidProduct.Aperiodic.CubeRoot.RadicalStep
import MonoidProduct.Aperiodic.CubeRoot.ApexData
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The radical tower

For an `ApexPackage` — any faithful embedding of `M` into a ring with a
quantitatively nilpotent two-sided kernel — the word-product contract lifts
from the **coordinate image** (the image of `M` in `Alg ⧸ Ker`; the package
embeds this quotient into a product of matrix algebras but is not asked to
make that embedding onto, so no semisimplicity is claimed or used) all the
way back to `M`, at `Nat.clog 2 |M|` doublings:

    `Alg ⧸ Ker^(2r)  →  Alg ⧸ Ker^r`,   `r = 1, 2, 4, …`

Each transition restricts to the **layer monoids** (the images of `M`), its
algebra kernel is square-zero (`doublingMap_ker_mul`), so the locally-thin
compiler of `LocallyThinCompiler.lean` applies with no algebra section
anywhere: one `thinStep` per layer.
`Ker^(2^k) = ⊥` for `k = clog 2 |M|` by the package's quantitative exponent,
and at the top the layer embedding is faithful, so the contract transfers to
`M` itself for free (`HasWordProdDualPoly.of_injective_hom`).

Endpoints:

* `ApexPackage.radical_lift` — the tower, hypothesis at the `Ker^1` layer;
* `ApexPackage.radical_lift'` — the same with the hypothesis at the `Ker`
  layer (the bottom layer as `Assembly.lean` produces it);
* `iterate_thinStep_add_one_le` — the closed-form majorant
  `D_k + 1 ≤ (thinStep n₀ N 0 + 1)^k · (D + 1)`, through the vocabulary lemma
  `thinStep_eq_mul` so no body is unfolded here.

Everything is parametric in the per-layer coefficient: `thinStep` is quoted by
name, and the exponent multiplier `K` of `cubeRootFactor` is neither mentioned
nor chosen here — it is chosen in `Main.lean` (`K = 256`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

open LocallyThin

namespace ApexPackage

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]
variable (Pk : ApexPackage M)

/-! ## The layer monoids -/

/-- The monoid map into the layer at the ideal `I`. -/
noncomputable def layerEmbed (I : Ideal Pk.Alg) [I.IsTwoSided] : M →* Pk.Alg ⧸ I :=
  (Ideal.Quotient.mk I).toMonoidHom.comp Pk.embed

@[simp] lemma layerEmbed_apply (I : Ideal Pk.Alg) [I.IsTwoSided] (m : M) :
    Pk.layerEmbed I m = Ideal.Quotient.mk I (Pk.embed m) := rfl

/-- **The layer monoid**: the image of `M` in `Alg ⧸ I`.  Reducible, so that
the `Fintype`/`DecidableEq`/aperiodicity instances below key uniformly on the
`mrange` spelling. -/
noncomputable abbrev layerMonoid (I : Ideal Pk.Alg) [I.IsTwoSided] :
    Submonoid (Pk.Alg ⧸ I) :=
  MonoidHom.mrange (Pk.layerEmbed I)

instance (I : Ideal Pk.Alg) [I.IsTwoSided] : Finite ↥(Pk.layerMonoid I) :=
  Finite.of_surjective (MonoidHom.mrangeRestrict (Pk.layerEmbed I))
    (MonoidHom.mrangeRestrict_surjective _)

noncomputable instance (I : Ideal Pk.Alg) [I.IsTwoSided] :
    Fintype ↥(Pk.layerMonoid I) := Fintype.ofFinite _

noncomputable instance (I : Ideal Pk.Alg) [I.IsTwoSided] :
    DecidableEq ↥(Pk.layerMonoid I) := Classical.decEq _

instance [IsAperiodicMonoid M] (I : Ideal Pk.Alg) [I.IsTwoSided] :
    IsAperiodicMonoid ↥(Pk.layerMonoid I) :=
  inferInstanceAs (IsAperiodicMonoid ↥(MonoidHom.mrange (Pk.layerEmbed I)))

/-- A layer monoid is no larger than the monoid. -/
lemma card_layerMonoid_le (I : Ideal Pk.Alg) [I.IsTwoSided] :
    Fintype.card ↥(Pk.layerMonoid I) ≤ Fintype.card M :=
  Fintype.card_le_of_surjective (MonoidHom.mrangeRestrict (Pk.layerEmbed I))
    (MonoidHom.mrangeRestrict_surjective _)

/-! ## The doubling transition on the layer monoids -/

/-- **The tower map**: the doubling transition `Alg ⧸ Ker^(2r) → Alg ⧸ Ker^r`
restricted to the layer monoids. -/
noncomputable def towerHom (r : ℕ) :
    ↥(Pk.layerMonoid (Pk.kernel ^ (2 * r))) →* ↥(Pk.layerMonoid (Pk.kernel ^ r)) where
  toFun s := ⟨doublingMap Pk.kernel r s.1, by
    obtain ⟨m, hm⟩ := MonoidHom.mem_mrange.1 s.2
    refine MonoidHom.mem_mrange.2 ⟨m, ?_⟩
    rw [← hm, layerEmbed_apply, layerEmbed_apply, doublingMap_mk]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp)

@[simp] lemma towerHom_coe (r : ℕ) (s : ↥(Pk.layerMonoid (Pk.kernel ^ (2 * r)))) :
    (Pk.towerHom r s : Pk.Alg ⧸ Pk.kernel ^ r) = doublingMap Pk.kernel r s.1 := rfl

/-- **The tower map has a square-zero kernel** — the algebraic input of the
square-zero product lift (`lem:ags-square-zero-lift`), with the subtype inclusion as the faithful
representation and the doubling map's ring kernel as the ideal. -/
theorem squareZeroKernel_towerHom (r : ℕ) :
    SquareZeroKernel (Pk.towerHom r) (Pk.layerMonoid (Pk.kernel ^ (2 * r))).subtype
      (RingHom.ker (doublingMap Pk.kernel r)) where
  twoSided := inferInstance
  sq_zero := fun _ ha _ hb => doublingMap_ker_mul Pk.kernel r ha hb
  emb_inj := fun _ _ h => Subtype.ext h
  fibre := fun s s' h => by
    have hval : doublingMap Pk.kernel r s.1 = doublingMap Pk.kernel r s'.1 :=
      congrArg Subtype.val h
    change s.1 - s'.1 ∈ RingHom.ker (doublingMap Pk.kernel r)
    rw [RingHom.mem_ker, map_sub, hval, sub_self]

/-- **One layer of the tower**: the square-zero lift, applied to the doubling
transition. -/
theorem liftsWordProd_towerHom [IsAperiodicMonoid M] (r n₀ : ℕ) (D : ℝ) :
    LiftsWordProd ↥(Pk.layerMonoid (Pk.kernel ^ (2 * r)))
      ↥(Pk.layerMonoid (Pk.kernel ^ r)) n₀ D :=
  liftsWordProd_of_locallyThin
    (locallyThinKernel_of_squareZero (Pk.squareZeroKernel_towerHom r)) n₀ D

/-- The layer step, with the size bound normalized to `|M|`: one doubling
costs one `thinStep` at the carrier size. -/
theorem hasWordProdDualPoly_double [IsAperiodicMonoid M] (r n₀ : ℕ) {D : ℝ}
    (h : HasWordProdDualPoly ↥(Pk.layerMonoid (Pk.kernel ^ r)) n₀ D) :
    HasWordProdDualPoly ↥(Pk.layerMonoid (Pk.kernel ^ (2 * r))) n₀
      (thinStep n₀ (Fintype.card M) D) := by
  refine (Pk.liftsWordProd_towerHom r n₀ D h).mono_cost
    (thinStep_mono n₀ ?_ h.nonneg le_rfl)
  exact max_le (Pk.card_layerMonoid_le _) (Pk.card_layerMonoid_le _)

/-! ## The tower -/

/-- **The doubling tower**: `k` layers up from `Ker^1`, at one `thinStep` per
layer. -/
theorem hasWordProdDualPoly_tower [IsAperiodicMonoid M] (n₀ : ℕ) {D : ℝ}
    (h : HasWordProdDualPoly ↥(Pk.layerMonoid (Pk.kernel ^ 1)) n₀ D) (k : ℕ) :
    HasWordProdDualPoly ↥(Pk.layerMonoid (Pk.kernel ^ (2 ^ k))) n₀
      ((thinStep n₀ (Fintype.card M))^[k] D) := by
  induction k with
  | zero => exact h
  | succ k ih =>
      have hstep := Pk.hasWordProdDualPoly_double (2 ^ k) n₀ ih
      rw [show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k from by rw [pow_succ, Nat.mul_comm],
        Function.iterate_succ_apply']
      exact hstep

/-! ## Terminal recovery -/

/-- At an ideal that is `⊥`, the layer embedding is faithful. -/
lemma layerEmbed_injective_of_eq_bot {I : Ideal Pk.Alg} [I.IsTwoSided]
    (hI : I = ⊥) : Function.Injective (Pk.layerEmbed I) := by
  intro a b h
  simp only [layerEmbed_apply] at h
  refine Pk.embed_injective ?_
  have hmem := Ideal.Quotient.eq.1 h
  rw [hI] at hmem
  exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hmem)

/-- **The radical lift** (the paper's `sec:ags-radical-lift`).  From the word-product contract at
the bottom layer `Alg ⧸ Ker^1`, the tower of `Nat.clog 2 |M|` doublings
reaches an ideal that the package's quantitative nilpotency makes `⊥`; the
layer embedding is faithful there, and the contract transfers to `M` at no
further cost.  No intermediate quotient is assumed to split. -/
theorem radical_lift [IsAperiodicMonoid M] (n₀ : ℕ) {D : ℝ}
    (h : HasWordProdDualPoly ↥(Pk.layerMonoid (Pk.kernel ^ 1)) n₀ D) :
    HasWordProdDualPoly M n₀
      ((thinStep n₀ (Fintype.card M))^[Nat.clog 2 (Fintype.card M)] D) := by
  have htop := Pk.hasWordProdDualPoly_tower n₀ h (Nat.clog 2 (Fintype.card M))
  have hbot : Pk.kernel ^ (2 ^ Nat.clog 2 (Fintype.card M)) = ⊥ := by
    refine pow_eq_bot_of_le Pk.kernel Pk.kernel_pow_eq_bot ?_
    calc Pk.nilExponent ≤ Fintype.card M := Pk.nilExponent_le
      _ ≤ 2 ^ Nat.clog 2 (Fintype.card M) := Nat.le_pow_clog (by norm_num) _
  set I : Ideal Pk.Alg := Pk.kernel ^ (2 ^ Nat.clog 2 (Fintype.card M)) with hI
  have hψ : Function.Injective
      (MonoidHom.mrangeRestrict (Pk.layerEmbed I) :
        M →* ↥(Pk.layerMonoid I)) := by
    intro a b hab
    exact Pk.layerEmbed_injective_of_eq_bot hbot (congrArg Subtype.val hab)
  exact HasWordProdDualPoly.of_injective_hom
    (MonoidHom.mrangeRestrict (Pk.layerEmbed I) : M →* ↥(Pk.layerMonoid I)) hψ htop

/-! ## The bottom of the tower, at `Ker` itself

`Ker^1 = Ker` only propositionally, and the two quotients are different
types.  The factor map bridges them, injectively since the ideals are equal,
so the hypothesis can be taken at the image in `Alg ⧸ Ker` as `Assembly.lean`
produces it. -/

/-- The factor map from the `Ker^1` layer to the `Ker` layer. -/
noncomputable def bridgeHom :
    ↥(Pk.layerMonoid (Pk.kernel ^ 1)) →* ↥(Pk.layerMonoid Pk.kernel) where
  toFun s := ⟨Ideal.Quotient.factor (le_of_eq (Submodule.pow_one Pk.kernel)) s.1, by
    obtain ⟨m, hm⟩ := MonoidHom.mem_mrange.1 s.2
    refine MonoidHom.mem_mrange.2 ⟨m, ?_⟩
    rw [← hm, layerEmbed_apply, layerEmbed_apply, Ideal.Quotient.factor_mk]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp)

lemma bridgeHom_injective : Function.Injective Pk.bridgeHom := by
  intro s s' h
  have hval : Ideal.Quotient.factor (le_of_eq (Submodule.pow_one Pk.kernel)) s.1
      = Ideal.Quotient.factor (le_of_eq (Submodule.pow_one Pk.kernel)) s'.1 :=
    congrArg Subtype.val h
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective s.1
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective s'.1
  refine Subtype.ext ?_
  rw [← ha, ← hb]
  rw [← ha, ← hb, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk] at hval
  have hmem := Ideal.Quotient.eq.1 hval
  rw [← Submodule.pow_one Pk.kernel] at hmem
  exact Ideal.Quotient.eq.2 hmem

/-- **The radical lift, hypothesis at the coordinate image** in `Alg ⧸ Ker`. -/
theorem radical_lift' [IsAperiodicMonoid M] (n₀ : ℕ) {D : ℝ}
    (h : HasWordProdDualPoly ↥(Pk.layerMonoid Pk.kernel) n₀ D) :
    HasWordProdDualPoly M n₀
      ((thinStep n₀ (Fintype.card M))^[Nat.clog 2 (Fintype.card M)] D) :=
  Pk.radical_lift n₀
    (HasWordProdDualPoly.of_injective_hom Pk.bridgeHom Pk.bridgeHom_injective h)

end ApexPackage

/-! ## The closed-form majorant

The iterate is the primary statement; the majorant converts it into the
`(base)^layers · (D + 1)` shape the carrier recurrence consumes, through the
vocabulary lemma `thinStep_eq_mul` — no body is unfolded here. -/

lemma iterate_thinStep_nonneg (n₀ N : ℕ) {D : ℝ} (hD : 0 ≤ D) (k : ℕ) :
    0 ≤ (thinStep n₀ N)^[k] D := by
  induction k with
  | zero => exact hD
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact thinStep_nonneg n₀ N ih

/-- **The tower's cost in closed form**:
`D_k + 1 ≤ (thinStep n₀ N 0 + 1)^k · (D + 1)`. -/
theorem iterate_thinStep_add_one_le (n₀ N : ℕ) {D : ℝ} (hD : 0 ≤ D) (k : ℕ) :
    (thinStep n₀ N)^[k] D + 1
      ≤ (thinStep n₀ N 0 + 1) ^ k * (D + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hE : 0 ≤ (thinStep n₀ N)^[k] D := iterate_thinStep_nonneg n₀ N hD k
      have hc0 : 0 ≤ thinStep n₀ N 0 := thinStep_nonneg n₀ N le_rfl
      rw [Function.iterate_succ_apply', thinStep_eq_mul, pow_succ]
      calc thinStep n₀ N 0 * ((thinStep n₀ N)^[k] D + 1) + 1
          ≤ (thinStep n₀ N 0 + 1) * ((thinStep n₀ N)^[k] D + 1) := by nlinarith
        _ ≤ (thinStep n₀ N 0 + 1) * ((thinStep n₀ N 0 + 1) ^ k * (D + 1)) := by
            refine mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (thinStep n₀ N 0 + 1) ^ k * (thinStep n₀ N 0 + 1) * (D + 1) := by ring

end MonoidProduct
