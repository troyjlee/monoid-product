import MonoidProduct.Aperiodic.Induction
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The horizon-uniform dual contract, and the cube-root cost vocabulary

Every compiler of the cube-root development (Section
`sec:ags-cuberoot-size` of the paper) consumes and produces
**concrete dual witnesses at every horizon**, never a bare numeric `advPM`
inequality: the recursion asks for the certificate of every shorter word.
`HasWordProdDualUpTo letter n₀ D` is that contract — a dual of cost `D·√ℓ`
for the word product at every length `ℓ ≤ n₀`, length `0` included.

Also here:

* the cost vocabulary the compilers are stated in (`cubeLog`,
  `cubeThreshold`, `cubeExponent`, `cubeRootFactor`, `cubeRootDualCost`).
  `cubeThreshold` and `cubeExponent` — the *layer count* — have fixed
  bodies; `cubeRootFactor` and `cubeRootDualCost` carry a universal exponent
  multiplier `K`, kept parametric through the compilers and **fixed at
  `K = 256`** in `Main.lean`.  No compiler theorem depends on the numeric
  bodies; the convention is below;
* generic facts for images of finite aperiodic monoids;
* the **localized strict-parent induction hypothesis** `StrictParentIH`
  that the localized AGS step of `StrictParent.lean` consumes — certificates for every
  strict `twoIdeal`-parent of `m` — and the bridge showing that the existing
  numeric `jLevel` hypothesis is stronger (the converse fails: a smaller
  level does not mean a strictly larger ideal, which is exactly why the step
  is localized).
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## The contract -/

section Contract

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {H : Type} [Monoid H] [Fintype H] [DecidableEq H]

/-- **The horizon-uniform dual contract**: a dual of cost `D·√ℓ` for the word
product at every length `ℓ ≤ n₀`, with `D ≥ 0`. -/
def HasWordProdDualUpTo (letter : σ → H) (n₀ : ℕ) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ ℓ, ℓ ≤ n₀ →
    HasDual (fun x : Fin ℓ → σ => wordProd letter x) (D * Real.sqrt (ℓ : ℝ))

namespace HasWordProdDualUpTo

variable {letter : σ → H} {n₀ : ℕ} {D : ℝ}

lemma nonneg (h : HasWordProdDualUpTo letter n₀ D) : 0 ≤ D := h.1

lemma apply (h : HasWordProdDualUpTo letter n₀ D) {ℓ : ℕ} (hℓ : ℓ ≤ n₀) :
    HasDual (fun x : Fin ℓ → σ => wordProd letter x) (D * Real.sqrt (ℓ : ℝ)) :=
  h.2 ℓ hℓ

/-- The contract is monotone in the cost. -/
lemma mono_cost (h : HasWordProdDualUpTo letter n₀ D) {D' : ℝ} (hD : D ≤ D') :
    HasWordProdDualUpTo letter n₀ D' :=
  ⟨le_trans h.1 hD, fun ℓ hℓ =>
    (h.2 ℓ hℓ).mono (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg _))⟩

/-- The contract is antitone in the horizon. -/
lemma mono_horizon (h : HasWordProdDualUpTo letter n₀ D) {n₁ : ℕ} (hn : n₁ ≤ n₀) :
    HasWordProdDualUpTo letter n₁ D :=
  ⟨h.1, fun ℓ hℓ => h.2 ℓ (le_trans hℓ hn)⟩

end HasWordProdDualUpTo

/-- **Horizon `0`**: the empty word has a constant product, so the contract
holds at every nonnegative cost. -/
lemma hasWordProdDualUpTo_zero (letter : σ → H) {D : ℝ} (hD : 0 ≤ D) :
    HasWordProdDualUpTo letter 0 D := by
  refine ⟨hD, fun ℓ hℓ => ?_⟩
  obtain rfl : ℓ = 0 := Nat.le_zero.mp hℓ
  refine (hasDual_const fun x y => ?_).mono (by simp)
  rw [show x = y from funext fun i => i.elim0]

/-- The word product at a fixed length is the total function the contract
certifies; the contract at horizon `n` gives it at cost `D·√n`. -/
lemma HasWordProdDualUpTo.hasDual_self {letter : σ → H} {n : ℕ} {D : ℝ}
    (h : HasWordProdDualUpTo letter n D) :
    HasDual (fun x : Fin n → σ => wordProd letter x) (D * Real.sqrt (n : ℝ)) :=
  h.apply le_rfl

/-! ### The alphabet-uniform contract

`HasWordProdDualUpTo` fixes the alphabet.  A compiler that prepends a letter
asks for the same certificate over `Option σ`, and the `σ`-version does **not**
give it: the extra letter is genuinely new input, and no `alphaMap`/`pullback`
runs in that direction.  So the fixed-apex peel's recursion hypothesis has to
be uniform in the alphabet as well as the horizon.  Nothing is lost by asking:
the global AGS bound already is (`hasDual_eqProd'` is proved for every
alphabet), which is exactly why `strictParentIH_prependLetter` can be stated
with no hypotheses at all. -/

variable (H) in
/-- **The alphabet-uniform dual contract**: a dual of cost `D·√ℓ` for the word
product at every length `ℓ ≤ n₀` and over **every** finite alphabet. -/
def HasWordProdDualPoly (n₀ : ℕ) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (L : α → H) (ℓ : ℕ), ℓ ≤ n₀ →
    HasDual (fun x : Fin ℓ → α => wordProd L x) (D * Real.sqrt (ℓ : ℝ))

namespace HasWordProdDualPoly

variable {n₀ : ℕ} {D : ℝ}

lemma nonneg (h : HasWordProdDualPoly H n₀ D) : 0 ≤ D := h.1

/-- **Instantiating the alphabet.**  This is the whole point: the augmented
alphabet an axis runs over is just another instance. -/
lemma toUpTo (h : HasWordProdDualPoly H n₀ D) {α : Type} [Fintype α]
    [DecidableEq α] (L : α → H) : HasWordProdDualUpTo L n₀ D :=
  ⟨h.1, fun ℓ hℓ => h.2 α L ℓ hℓ⟩

lemma mono_horizon (h : HasWordProdDualPoly H n₀ D) {n₁ : ℕ} (hn : n₁ ≤ n₀) :
    HasWordProdDualPoly H n₁ D :=
  ⟨h.1, fun α _ _ L ℓ hℓ => h.2 α L ℓ (le_trans hℓ hn)⟩

lemma mono_cost (h : HasWordProdDualPoly H n₀ D) {D' : ℝ} (hD : D ≤ D') :
    HasWordProdDualPoly H n₀ D' :=
  ⟨le_trans h.1 hD, fun α _ _ L ℓ hℓ =>
    (h.2 α L ℓ hℓ).mono (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg _))⟩

end HasWordProdDualPoly

end Contract

/-! ## The cost vocabulary (layer count frozen; coefficient parameterized)

**Convention**: the compiler theorems downstream of this file, and the assembly, treat
`cubeThreshold`, `cubeExponent`, `cubeRootFactor` and `cubeRootDualCost`
as **opaque names**: they are stated against the names and may not unfold
the bodies.  The elementary vocabulary lemmas of this
file — the threshold specifications, nonnegativity, monotonicity, and the
normalization theorem — are exempt: they *are* the API through which the
names are used.

**Status**: the *exponent shape* is settled and its
arithmetic proved (`CubeRoot/Recurrence.lean`), so `cubeThreshold` and
`cubeExponent` keep the bodies below.  The **universal coefficient is not**
built in: `cubeRootFactor` carries an explicit multiplier `K` — carried
parametrically through the compilers and **chosen as `K = 256`** in the final
assembly (`Main.lean`'s majorants are the justification), for the reason recorded on its docstring.  Statements upstream
of the assembly stay parametric in `K`; the endpoints quote `256`.

**Normalization**: the final contract is stated with `cubeRootFactor` as
the coefficient, `HasWordProdDualUpTo letter n (cubeRootFactor K s n)`, whose
cost at length `ℓ` is `cubeRootFactor K s n · √ℓ`; `cubeRootDualCost K s n`
already includes the `√n` of the top horizon
(`HasWordProdDualUpTo.hasDual_cubeRootDualCost`). -/

/-- `L(n) = 2 + ⌈log₂(n + 2)⌉`, the manuscript's logarithmic factor in
`Nat.clog` form. -/
def cubeLog (n : ℕ) : ℕ := Nat.clog 2 (n + 2) + 2

lemma two_le_cubeLog (n : ℕ) : 2 ≤ cubeLog n := by
  unfold cubeLog
  omega

lemma cubeLog_mono {a b : ℕ} (h : a ≤ b) : cubeLog a ≤ cubeLog b := by
  unfold cubeLog
  have := Nat.clog_mono_right 2 (Nat.add_le_add_right h 2)
  omega

lemma exists_cubeThreshold (s : ℕ) : ∃ t : ℕ, 2 ≤ t ∧ s * cubeLog s ≤ t ^ 3 :=
  ⟨s * cubeLog s + 2, by omega,
    le_trans (Nat.le_add_right _ 2) (Nat.le_self_pow (by norm_num) _)⟩

/-- The balancing threshold: the least `t ≥ 2` with `s·L(s) ≤ t³`, within a
constant factor of `(s log(s+2))^{1/3}` — two-sidedly, by
`Recurrence.cubeThreshold_pow_le`.  The body is fixed. -/
noncomputable def cubeThreshold (s : ℕ) : ℕ := Nat.find (exists_cubeThreshold s)

lemma two_le_cubeThreshold (s : ℕ) : 2 ≤ cubeThreshold s :=
  (Nat.find_spec (exists_cubeThreshold s)).1

lemma cubeThreshold_spec (s : ℕ) : s * cubeLog s ≤ cubeThreshold s ^ 3 :=
  (Nat.find_spec (exists_cubeThreshold s)).2

/-- The exponent shape of the carrier recurrence,
`t + (⌈s/t²⌉ + 1)·⌈log₂(s + 2)⌉`.  The body is fixed: `Recurrence.lean` proves
the recurrence closes against exactly this shape, so the body stands.  It counts
*layers*, not cost — the cost of one layer is `K`'s job. -/
noncomputable def cubeExponent (s : ℕ) : ℕ :=
  cubeThreshold s
    + ((s + cubeThreshold s ^ 2 - 1) / cubeThreshold s ^ 2 + 1) * Nat.clog 2 (s + 2)

/-- The polynomial-logarithmic factor `(s·L(n))^{K · cubeExponent s}`.

**`K` is a parameter, not a constant, and that is deliberate.**  `cubeExponent`
counts *layers*; each layer costs a compiler constant, and those constants are
much larger than `s·L(n)` at small parameters, so a multiplier of one is simply
false.  Concretely: `thinStep 1 2 1 = 2592`, while at `s = 2`, `n = 1` the whole
per-layer budget `(s·L(n))^{⌈log₂(s+2)⌉}` is `8² = 64`; and `MatrixWord`'s
terminal coefficient carries `axisConst ^ (d+1)` with `axisBase ≥ 192`.

`K` is **carried through the compilers and chosen in the final assembly:
`K = 256`** — not fixed at the radical tower, whose own `thinStep` is merely one
of the constants `K` has to dominate.  The assembly is the first point at which
the terminal, peel, radical and assembly constants are all on the board, so it
is the first point at which a value can be justified rather than guessed.  The asymptotics do not depend on it —
`(K · cubeExponent s)³ ≤ 512·K³·(s·cubeLog s)`,
`Recurrence.cubeExponent_pow_le_mul` — which is exactly why leaving it open costs
nothing. -/
noncomputable def cubeRootFactor (K s n : ℕ) : ℝ :=
  ((s : ℝ) * cubeLog n) ^ (K * cubeExponent s)

/-- The dual cost `√n · cubeRootFactor K s n`. -/
noncomputable def cubeRootDualCost (K s n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * cubeRootFactor K s n

lemma cubeRootFactor_nonneg (K s n : ℕ) : 0 ≤ cubeRootFactor K s n := by
  unfold cubeRootFactor
  positivity

lemma cubeRootDualCost_nonneg (K s n : ℕ) : 0 ≤ cubeRootDualCost K s n := by
  unfold cubeRootDualCost
  exact mul_nonneg (Real.sqrt_nonneg _) (cubeRootFactor_nonneg K s n)

/-- The dual cost, spelled out — the vocabulary form the presentation
theorem reads. -/
lemma cubeRootDualCost_eq (K s n : ℕ) :
    cubeRootDualCost K s n
      = Real.sqrt (n : ℝ) * ((s : ℝ) * cubeLog n) ^ (K * cubeExponent s) := rfl

lemma cubeThreshold_le_cubeExponent (s : ℕ) :
    cubeThreshold s ≤ cubeExponent s := Nat.le_add_right _ _

lemma two_le_cubeExponent (s : ℕ) : 2 ≤ cubeExponent s :=
  le_trans (two_le_cubeThreshold s) (cubeThreshold_le_cubeExponent s)

/-- **The normalization of the contract**: with coefficient `cubeRootFactor K s n`,
the top-horizon dual has cost `cubeRootDualCost K s n`. -/
lemma HasWordProdDualUpTo.hasDual_cubeRootDualCost {σ H : Type} [Fintype σ] [DecidableEq σ]
    [Monoid H] [Fintype H] [DecidableEq H] {letter : σ → H} {K s n : ℕ}
    (h : HasWordProdDualUpTo letter n (cubeRootFactor K s n)) :
    HasDual (fun x : Fin n → σ => wordProd letter x) (cubeRootDualCost K s n) := by
  have := h.hasDual_self
  rwa [cubeRootDualCost, mul_comm]

/-! ## Images of finite aperiodic monoids -/

section Images

variable {M N : Type} [Monoid M] [Monoid N]

/-- A surjective image of an aperiodic monoid is aperiodic. -/
theorem IsAperiodicMonoid.of_surjective [IsAperiodicMonoid M] (φ : M →* N)
    (hφ : Function.Surjective φ) : IsAperiodicMonoid N := by
  refine ⟨fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hφ b
  obtain ⟨K, hK, ha⟩ := IsAperiodicMonoid.stabilizes a
  exact ⟨K, hK, by rw [← map_pow, ← map_pow, ha]⟩

/-- The range of a monoid homomorphism out of an aperiodic monoid is an
aperiodic monoid. -/
instance IsAperiodicMonoid.mrange [IsAperiodicMonoid M] (φ : M →* N) :
    IsAperiodicMonoid (MonoidHom.mrange φ) :=
  IsAperiodicMonoid.of_surjective (MonoidHom.mrangeRestrict φ)
    (MonoidHom.mrangeRestrict_surjective φ)

/-- A submonoid of an aperiodic monoid is aperiodic. -/
instance IsAperiodicMonoid.submonoid [IsAperiodicMonoid M] (S : Submonoid M) :
    IsAperiodicMonoid S :=
  ⟨fun a => by
    obtain ⟨K, hK, ha⟩ := IsAperiodicMonoid.stabilizes (a : M)
    exact ⟨K, hK, Subtype.ext (by simpa using ha)⟩⟩

/-- **Transport along an injective homomorphism**: the alphabet-uniform
contract descends from the target monoid to the source at the *same* cost —
the word product over the source is determined by its `ψ`-image, so
`HasDual.ofKer` recodes for free.  This is the terminal-recovery step of the
radical tower, and the reason a faithful image is as good as the monoid. -/
lemma HasWordProdDualPoly.of_injective_hom {H H' : Type}
    [Monoid H] [Fintype H] [DecidableEq H] [Monoid H'] [Fintype H'] [DecidableEq H']
    {n₀ : ℕ} {D : ℝ} (ψ : H →* H') (hψ : Function.Injective ψ)
    (h : HasWordProdDualPoly H' n₀ D) : HasWordProdDualPoly H n₀ D := by
  refine ⟨h.1, fun α _ _ L ℓ hℓ => ?_⟩
  refine (h.2 α (fun a => ψ (L a)) ℓ hℓ).ofKer fun x y => ?_
  rw [show wordProd (fun a => ψ (L a)) x = ψ (wordProd L x) from (map_wordProd ψ L x).symm,
    show wordProd (fun a => ψ (L a)) y = ψ (wordProd L y) from (map_wordProd ψ L y).symm]
  exact hψ.eq_iff

end Images

/-! ## The localized strict-parent induction hypothesis -/

section Localized

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- **The localized induction hypothesis** of the strict-parent AGS step:
dual certificates, at every horizon `ℓ ≤ n₀`, for the target test of every
`s` whose principal two-sided ideal *strictly contains* that of `m`. -/
def StrictParentIH (letter : σ → M) (m : M) (n₀ : ℕ) (D : ℝ) : Prop :=
  ∀ s : M, twoIdeal m ⊂ twoIdeal s → ∀ ℓ, ℓ ≤ n₀ →
    HasDual (eqProd (n := ℓ) letter s) (D * Real.sqrt (ℓ : ℝ))

/-- The existing numeric `jLevel` hypothesis of `hasDual_eqProd_step` implies
the localized one (strict containment lowers the level); the converse fails,
which is why the strict-parent step is localized. -/
lemma strictParentIH_of_jLevel {letter : σ → M} {m : M} {n₀ : ℕ} {D : ℝ}
    (h : ∀ s : M, jLevel s < jLevel m → ∀ ℓ, ℓ ≤ n₀ →
      HasDual (eqProd (n := ℓ) letter s) (D * Real.sqrt (ℓ : ℝ))) :
    StrictParentIH letter m n₀ D :=
  fun s hs => h s (jLevel_lt_of_ssubset hs)

lemma StrictParentIH.mono_horizon {letter : σ → M} {m : M} {n₀ : ℕ} {D : ℝ}
    (h : StrictParentIH letter m n₀ D) {n₁ : ℕ} (hn : n₁ ≤ n₀) :
    StrictParentIH letter m n₁ D :=
  fun s hs ℓ hℓ => h s hs ℓ (le_trans hℓ hn)

end Localized

end MonoidProduct
