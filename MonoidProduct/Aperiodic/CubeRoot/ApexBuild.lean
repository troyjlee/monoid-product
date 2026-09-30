import MonoidProduct.Aperiodic.CubeRoot.PrincipalMatrix
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The coordinate of a class, and the total charge

Everything the per-`J` construction produced, assembled into the frozen
`ApexCoordinate` interface, plus the counting that `ApexPackage.charge` asks
for.

**A coordinate is built at an idempotent**, not at an arbitrary class
representative: `ApexCoordinate` carries `apex` together with `apex_idem`, and a
regular class is exactly one containing an idempotent
(`isRegularClass_iff_exists_idem`).  Building at `e` from the start means every
field is already stated about the right class and nothing has to be transported
along `twoIdeal e = twoIdeal a`.

**What each field costs.**  `rep` is the compressed representation of
`rowColAction`; `annihilate` is the annihilation below `J` of `PrincipalMatrix.lean`, pure ideal descent; `degree_sq_le` is
`rank_sq_le_card_jClass`, which is the sandwich's rank bound composed with the
cell count.  Notably *none* of the three needs regularity — regularity's whole
contribution is the existence of the idempotent `apex` itself.

**The total charge** `∑_J d_J² ≤ |M|` is then pure counting: the classes of
distinct coordinates are disjoint, so their cardinalities sum to at most `|M|`,
and each `d_J²` is under its own class.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace PrincipalFactor

open Matrix

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The coordinate of an idempotent's class -/

/-- **The coordinate attached to an idempotent**, from a rank factorization of
its sandwich.  The factorization is a parameter rather than chosen inside, so
the degree is visibly the sandwich's rank. -/
noncomputable def apexCoordinateOf [IsAperiodicMonoid M] {e : M}
    (he : IsIdempotentElem e) (F : RankFactorization (sandwichMat M e))
    (hF : F.d = (sandwichMat M e).rank) : ApexCoordinate M where
  degree := F.d
  rep := compressedRep F (rowColAction M e)
  apex := e
  apex_idem := he.eq
  annihilate s hs := compressedRep_eq_zero_of_ssubset F s hs
  degree_sq_le := by
    rw [hF]
    exact rank_sq_le_card_jClass e

@[simp] lemma apexCoordinateOf_apex [IsAperiodicMonoid M] {e : M}
    (he : IsIdempotentElem e) (F : RankFactorization (sandwichMat M e))
    (hF : F.d = (sandwichMat M e).rank) : (apexCoordinateOf he F hF).apex = e := rfl

/-- **Every idempotent carries a coordinate.** -/
theorem exists_apexCoordinate [IsAperiodicMonoid M] {e : M} (he : IsIdempotentElem e) :
    ∃ c : ApexCoordinate M, c.apex = e := by
  obtain ⟨F, hF⟩ := exists_rankFactorization (sandwichMat M e)
  exact ⟨apexCoordinateOf he F hF, rfl⟩

/-- **Every regular class carries a coordinate.**  The apex is the class's
idempotent, which is what makes the class regular in the first place. -/
theorem exists_apexCoordinate_of_isRegularClass [IsAperiodicMonoid M] {a : M}
    (hreg : IsRegularClass a) :
    ∃ c : ApexCoordinate M, twoIdeal c.apex = twoIdeal a := by
  obtain ⟨e, hJ, hidem⟩ := isRegularClass_iff_exists_idem.1 hreg
  obtain ⟨c, hc⟩ := exists_apexCoordinate hidem
  exact ⟨c, by rw [hc, hJ]⟩

/-! ## The total charge

`ApexPackage.charge`, in the shape the package asks for.  Distinct coordinates
have distinct apex classes, distinct `J`-classes are disjoint, and each
coordinate's charge is under its own class. -/

/-- Distinct classes are disjoint. -/
lemma disjoint_jClass {x y : M} (h : twoIdeal x ≠ twoIdeal y) :
    Disjoint (jClass M x) (jClass M y) :=
  Finset.disjoint_left.2 fun b hbx hby =>
    h ((mem_jClass.1 hbx).symm.trans (mem_jClass.1 hby))

/-- **The total charge is at most the carrier.**  This is `ApexPackage.charge`,
and it is nothing but disjointness plus the per-coordinate charge. -/
theorem sum_degree_sq_le {n : ℕ} (c : Fin n → ApexCoordinate M)
    (hdisj : ∀ i j, twoIdeal (c i).apex = twoIdeal (c j).apex → i = j) :
    ∑ i, (c i).degree ^ 2 ≤ Fintype.card M := by
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ (Finset.univ : Finset (Fin n)),
      i ≠ j → Disjoint (jClass M (c i).apex) (jClass M (c j).apex) :=
    fun i _ j _ hij => disjoint_jClass fun hc => hij (hdisj i j hc)
  calc ∑ i, (c i).degree ^ 2 ≤ ∑ i, (jClass M (c i).apex).card :=
        Finset.sum_le_sum fun i _ => (c i).degree_sq_le
    _ = (Finset.univ.biUnion fun i => jClass M (c i).apex).card :=
        (Finset.card_biUnion hd).symm
    _ ≤ Fintype.card M := by
        rw [← Finset.card_univ]
        exact Finset.card_le_univ _

end PrincipalFactor

end MonoidProduct
