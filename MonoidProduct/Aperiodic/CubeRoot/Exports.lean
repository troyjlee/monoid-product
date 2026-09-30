import MonoidProduct.Aperiodic.CubeRoot.Main
import MonoidProduct.Aperiodic.Semigroup
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The exact `HasDual` and `advPM` exports

The cube-root theorem, read at a fixed length: for every finite aperiodic
monoid `M`, every alphabet, and every length `n`, the word product has an
explicit dual witness of cost `cubeRootDualCost 256 |M| n
= √n · (|M|·L(n))^(256·cubeExponent |M|)`, and hence
`advPM ≤ cubeRootDualCost 256 |M| n` by weak duality.

The `WithOne` semigroup forms transport by `HasDual.ofKer` at zero cost —
the coercion is injective, so the `S`-valued product and its unitised image
have the same level sets.  The conventions are visible in the statements:
**length `n + 1`** (a semigroup product needs a nonempty word) and **carrier
`|S| + 1`** (the adjoined unit).  These exact certificates are total and
carry no nonemptiness hypothesis; `[Nonempty S]` enters only on the
*operational* semigroup exports (`Quantum/CubeRootApplications.lean`), where
the answer alphabet must be inhabited.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Monoid

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **The cube-root dual, exactly**: every word product over a finite
aperiodic monoid has a dual witness of cost `cubeRootDualCost 256 |M| n`. -/
theorem hasDual_wordProd_cubeRoot (letter : σ → M) (n : ℕ) :
    HasDual (fun x : Fin n → σ => wordProd letter x)
      (cubeRootDualCost 256 (Fintype.card M) n) :=
  ((hasWordProdDualPoly_cubeRootFactor M n).toUpTo letter).hasDual_cubeRootDualCost

/-- **The cube-root adversary bound**, by weak duality. -/
theorem advPM_wordProd_cubeRoot (letter : σ → M) (n : ℕ) :
    advPM (fun x : Fin n → σ => wordProd letter x)
      ≤ cubeRootDualCost 256 (Fintype.card M) n :=
  advPM_le_of_hasDual (cubeRootDualCost_nonneg _ _ _)
    (hasDual_wordProd_cubeRoot letter n)

end Monoid

section Semigroup

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {S : Type} [Semigroup S] [Fintype S] [DecidableEq S]
  [IsAperiodicSemigroup S]

/-- **The cube-root dual for a finite aperiodic semigroup** — length `n + 1`,
carrier `|S| + 1`, and the adapter costs nothing (`HasDual.ofKer` through the
injective unitisation). -/
theorem hasDual_semigroupProd_cubeRoot (sletter : σ → S) (n : ℕ) :
    HasDual (fun x : Fin (n + 1) → σ => semigroupProd n fun i => sletter (x i))
      (cubeRootDualCost 256 (Fintype.card S + 1) (n + 1)) := by
  have hbase := hasDual_wordProd_cubeRoot (M := WithOne S)
    (fun c => ((sletter c : S) : WithOne S)) (n + 1)
  rw [card_withOne] at hbase
  refine hbase.ofKer fun u v => ?_
  rw [wordProd, wordProd, ← coe_semigroupProd, ← coe_semigroupProd]
  exact WithOne.coe_inj

/-- **The cube-root adversary bound for a finite aperiodic semigroup.** -/
theorem advPM_semigroupProd_cubeRoot (sletter : σ → S) (n : ℕ) :
    advPM (fun x : Fin (n + 1) → σ => semigroupProd n fun i => sletter (x i))
      ≤ cubeRootDualCost 256 (Fintype.card S + 1) (n + 1) :=
  advPM_le_of_hasDual (cubeRootDualCost_nonneg _ _ _)
    (hasDual_semigroupProd_cubeRoot sletter n)

end Semigroup

end MonoidProduct
