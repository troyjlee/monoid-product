import MonoidProduct.Aperiodic.CubeRoot.Basic
import MonoidProduct.Aperiodic.CubeRoot.Green
import MonoidProduct.Aperiodic.CubeRoot.GreenCalibration
import MonoidProduct.Aperiodic.CubeRoot.FiniteAction
import MonoidProduct.Aperiodic.CubeRoot.TargetAction
import MonoidProduct.Aperiodic.CubeRoot.ActionCost
import MonoidProduct.Aperiodic.CubeRoot.AxisPacket
import MonoidProduct.Aperiodic.CubeRoot.ActionCompiler
import MonoidProduct.Aperiodic.CubeRoot.ActionTarget
import MonoidProduct.Aperiodic.CubeRoot.AxisRecurrence
import MonoidProduct.Aperiodic.CubeRoot.MatrixRank
import MonoidProduct.Aperiodic.CubeRoot.MatrixWord
import MonoidProduct.Aperiodic.CubeRoot.Rees
import MonoidProduct.Aperiodic.CubeRoot.FirstEntry
import MonoidProduct.Aperiodic.CubeRoot.FixedApex
import MonoidProduct.Aperiodic.CubeRoot.ApexAdapter
import MonoidProduct.Aperiodic.CubeRoot.LocallyThin
import MonoidProduct.Aperiodic.CubeRoot.LocallyThinCalibration
import MonoidProduct.Aperiodic.CubeRoot.LocallyThinCompiler
import MonoidProduct.Aperiodic.CubeRoot.StrictParent
import MonoidProduct.Aperiodic.CubeRoot.AdaptiveCall
import MonoidProduct.Aperiodic.CubeRoot.ReesBlock
import MonoidProduct.Aperiodic.CubeRoot.Compression
import MonoidProduct.Aperiodic.CubeRoot.RadicalStep
import MonoidProduct.Aperiodic.CubeRoot.ApexData
import MonoidProduct.Aperiodic.CubeRoot.Recurrence
import MonoidProduct.Aperiodic.CubeRoot.PrincipalFactor
import MonoidProduct.Aperiodic.CubeRoot.PrincipalAction
import MonoidProduct.Aperiodic.CubeRoot.PrincipalMatrix
import MonoidProduct.Aperiodic.CubeRoot.ApexBuild
import MonoidProduct.Aperiodic.CubeRoot.ApexJoint
import MonoidProduct.Aperiodic.CubeRoot.MunnLayer
import MonoidProduct.Aperiodic.CubeRoot.KernelFiltration
import MonoidProduct.Aperiodic.CubeRoot.MunnPackage
import MonoidProduct.Aperiodic.CubeRoot.RadicalTower
import MonoidProduct.Aperiodic.CubeRoot.Assembly
import MonoidProduct.Aperiodic.CubeRoot.Main
import MonoidProduct.Aperiodic.CubeRoot.Exports
set_option linter.style.header false

/-!
# The cube-root AGS development: local aggregate

This aggregate is imported by `MonoidProduct.lean`, so the plain build covers
the cube-root development (Section `sec:ags-cuberoot-size` of the paper,
`thm:ags-cuberoot-size`); CI also keeps it as an explicit target.

| module | contents |
| --- | --- |
| `Basic` | the horizon-uniform dual contract, the cost vocabulary, hom images, the localized IH |
| `Green` | R/L relations, regularity, regular classes, stability (`lem:ags-green-stability`) |
| `GreenCalibration` | the Green layer checked on `U₂` and `N₂` |
| `FiniteAction` | right actions, killed `R`-axes, components, owner cover (`lem:ags-owner-cover`) |
| `TargetAction` | the target-reachability action and the regular-height drop (`lem:ags-target-action`) |
| `ActionCost` | axis packets — exact endpoint and first death |
| `AxisPacket` | the killed `R_e`-axis packet, and the identity base case |
| `ActionCompiler` | the action compiler — windows, the transcript, and `hasDual_actionPacket` (`lem:ags-action-compiler`) |
| `ActionTarget` | the target test through the compiler, and the `N₂` decoder regression |
| `AxisRecurrence` | the alphabet-polymorphic axis recurrence, exact and solved (`prop:ags-axis-recurrence`) |
| `MatrixRank` | rank, the equal-rank `J` theorem, strict rank growth, and `regHeight + mrank ≤ d` (`lem:ags-matrix-rank-ceiling`) |
| `MatrixWord` | the Cayley action, and `HasWordProdDualUpTo` for a represented monoid (Section `sec:ags-matrix-bound`) |
| `Rees` | the Rees quotient, nonzero lifts, quotient aperiodicity, the carrier drop |
| `FirstEntry` | the boundary search — trace at `4D√n`, crossing letter at `4D√n + 2` |
| `FixedApex` | the decoded first entry `h = p·a`, the below-apex/apex-class split, the axis feed (`lem:ags-fixed-apex-peel`) |
| `ApexAdapter` | the quotient-to-Boolean adapter, `apexStep`, the uniform coordinate contract |
| `LocallyThin` | the kernel category, local thinness, the cut path, the dyadic count (`lem:ags-square-zero-lift`) |
| `LocallyThinCalibration` | the local-thinness theorem checked on `{0,1,2} ⊆ ZMod 4` |
| `LocallyThinCompiler` | the sequential search, its padded transcript, and `LiftsWordProd` |
| `StrictParent` | the localized AGS step, and the fixed-left-context test (`lem:ags-local-step`) |
| `AdaptiveCall` | the adaptive killed-axis call; the prepend integration test |
| `ReesBlock` | the Rees 0-matrix block and its direct Munn map |
| `Compression` | rank factorizations, the degree-`rank P` compression, the globalization theorem |
| `RadicalStep` | the doubling transition with square-zero kernel; layer count |
| `ApexData` | the frozen `ApexCoordinate`/`ApexPackage` interface |
| `Recurrence` | the carrier recurrence, the two-sided threshold, and the cube-root exponent (`prop:ags-cuberoot-recurrence`) |
| `PrincipalFactor` | `H`-triviality, `J = D`, the cells, and the sandwich's two regularity facts |
| `PrincipalAction` | the monoid's partial row/column action on the cells — composition and absorbing death |
| `PrincipalMatrix` | the matrices, the `RowColAction`, the cell formulas, spanning, the algebra transfer, annihilation |
| `ApexBuild` | the coordinate of an idempotent's class, and the total charge |
| `ApexJoint` | the class enumeration, the ambient algebra, and the joint coordinate map |
| `MunnLayer` | the layer's cube-zero kernel, and the counterexample retracting the one-step drop |
| `KernelFiltration` | the cardinality filtration, the layer calculus, the middle-kill drop, `Ker^(3^\|M\|) = ⊥` |
| `MunnPackage` | strict power descent, `Ker^\|M\| = ⊥`, and the unconditional `munnPackage` (`lem:ags-munn-decomposition`) |
| `RadicalTower` | the layer monoids of the doubling tower, one `thinStep` per layer, `clog₂\|M\|` layers, faithful terminal recovery — `ApexPackage.radical_lift` |
| `Assembly` | the bottom layer through the injective coordinate map, the matrix-bound/apex-peel dichotomy, the per-monoid step |
| `Main` | the majorants, the strong induction over monoid types, `K = 256` — `hasWordProdDualPoly_cubeRootFactor` |
| `Exports` | the exact `HasDual`/`advPM` bounds, monoid and `WithOne` semigroup forms (length `n+1`, carrier `\|S\|+1`) |
-/
