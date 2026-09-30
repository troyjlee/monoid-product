import MonoidProduct.Aperiodic.CubeRoot.RadicalTower
import MonoidProduct.Aperiodic.CubeRoot.MatrixWord
import MonoidProduct.Aperiodic.CubeRoot.ApexAdapter
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The bottom layer through the injective coordinate map

The assembly's guardrail: the bottom layer — the image
of `M` in `Alg ⧸ Ker` — is **not** claimed to be semisimple, and no joint
surjectivity is assumed.  What the package does give is *injectivity*: the
joint coordinate map descends injectively to `Alg ⧸ Ker`, so a bottom-layer
element is determined by its tuple of coordinates
(`bottomCoord_injective`).  That is enough: a word product over the bottom
layer is an (arbitrary, classically defined) function of the per-coordinate
word products, so `HasDual.combine'` assembles per-coordinate certificates
into a bottom-layer certificate at twice the summed cost
(`hasWordProdDualPoly_bottom`).

Also here: the alphabet-uniform repackaging of the regular matrix-rank
ceiling (`lem:ags-matrix-rank-ceiling`, `MatrixRank.lean`)
(`hasWordProdDualPoly_mrange`), which is the **small-coordinate** route of
the assembly — each coordinate's image is a finite aperiodic matrix monoid,
and its subtype inclusion is the faithful representation the action ceiling
wants.  The large-coordinate route is the fixed-apex peel's
`hasWordProdDualPoly_apexCoord`;
combining the two per-coordinate routes, feeding the result here, and
climbing `RadicalTower` is the per-monoid step of the strong induction.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace ApexPackage

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]
variable (Pk : ApexPackage M)

/-! ## The coordinates of the bottom layer -/

/-- **The `k`-th coordinate of a bottom-layer element**, valued in the
coordinate's image monoid.  Reads through a chosen preimage; well defined by
`bottomCoord_eq` below, since `φ`-equal preimages differ by the kernel and
the kernel is annihilated by every coordinate. -/
noncomputable def bottomCoord (k : Fin Pk.count)
    (b : ↥(Pk.layerMonoid Pk.kernel)) : ↥(MonoidHom.mrange (Pk.coord k).rep) :=
  MonoidHom.mrangeRestrict (Pk.coord k).rep (MonoidHom.mem_mrange.1 b.2).choose

/-- Two preimages of one bottom-layer element have equal coordinates. -/
lemma coord_rep_eq_of_layerEmbed_eq {m m' : M}
    (h : Pk.layerEmbed Pk.kernel m = Pk.layerEmbed Pk.kernel m')
    (k : Fin Pk.count) : (Pk.coord k).rep m = (Pk.coord k).rep m' := by
  simp only [layerEmbed_apply] at h
  have hker : Pk.embed m - Pk.embed m' ∈ Pk.kernel := Ideal.Quotient.eq.1 h
  have h0 : Pk.toCoord (Pk.embed m - Pk.embed m') = 0 := RingHom.mem_ker.1 hker
  rw [map_sub, sub_eq_zero] at h0
  have := congrFun h0 k
  rwa [Pk.toCoord_embed, Pk.toCoord_embed] at this

/-- **Well-definedness**: the coordinate reads the same through any
preimage. -/
lemma bottomCoord_eq (k : Fin Pk.count) {b : ↥(Pk.layerMonoid Pk.kernel)}
    {m : M} (hm : Pk.layerEmbed Pk.kernel m = b.1) :
    Pk.bottomCoord k b = MonoidHom.mrangeRestrict (Pk.coord k).rep m := by
  have hspec := (MonoidHom.mem_mrange.1 b.2).choose_spec
  refine Subtype.ext ?_
  exact Pk.coord_rep_eq_of_layerEmbed_eq (hspec.trans hm.symm) k

/-- The coordinates of an embedded element are the coordinate values. -/
lemma bottomCoord_mrangeRestrict (k : Fin Pk.count) (m : M) :
    Pk.bottomCoord k (MonoidHom.mrangeRestrict (Pk.layerEmbed Pk.kernel) m)
      = MonoidHom.mrangeRestrict (Pk.coord k).rep m :=
  Pk.bottomCoord_eq k rfl

/-- **The guardrail fact: the coordinates are jointly injective on the bottom
layer.**  Two bottom-layer elements with equal coordinate tuples have
preimages whose embedded difference is annihilated by the joint map, hence
lies in the kernel, hence vanishes in `Alg ⧸ Ker`.  No surjectivity and no
semisimple decomposition anywhere. -/
theorem bottomCoord_injective {b b' : ↥(Pk.layerMonoid Pk.kernel)}
    (h : ∀ k, Pk.bottomCoord k b = Pk.bottomCoord k b') : b = b' := by
  obtain ⟨m, hm⟩ := MonoidHom.mem_mrange.1 b.2
  obtain ⟨m', hm'⟩ := MonoidHom.mem_mrange.1 b'.2
  have hco : ∀ k, (Pk.coord k).rep m = (Pk.coord k).rep m' := by
    intro k
    have hb := Pk.bottomCoord_eq k hm
    have hb' := Pk.bottomCoord_eq k hm'
    have := (hb.symm.trans ((h k).trans hb'))
    exact congrArg Subtype.val this
  have hcoord : Pk.toCoord (Pk.embed m) = Pk.toCoord (Pk.embed m') := by
    funext k
    rw [Pk.toCoord_embed, Pk.toCoord_embed]
    exact hco k
  have hker : Pk.embed m - Pk.embed m' ∈ Pk.kernel := by
    rw [kernel, RingHom.mem_ker]
    have : Pk.toCoord (Pk.embed m - Pk.embed m') = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hcoord
    exact this
  refine Subtype.ext ?_
  rw [← hm, ← hm']
  simp only [layerEmbed_apply]
  exact Ideal.Quotient.eq.2 hker

/-! ## The combination -/

/-- **The bottom layer from its coordinates.**  Per-coordinate alphabet-uniform
certificates assemble into a bottom-layer certificate at twice the summed
cost: the bottom-layer word product is a function of the per-coordinate word
products — by `bottomCoord_injective`, through a classically chosen decoder —
so `HasDual.combine'` applies. -/
theorem hasWordProdDualPoly_bottom {n₀ : ℕ} {c : Fin Pk.count → ℝ}
    (hcoord : ∀ k,
      HasWordProdDualPoly ↥(MonoidHom.mrange (Pk.coord k).rep) n₀ (c k)) :
    HasWordProdDualPoly ↥(Pk.layerMonoid Pk.kernel) n₀ (2 * ∑ k, c k) := by
  classical
  have hc0 : ∀ k, 0 ≤ c k := fun k => (hcoord k).nonneg
  have hsum0 : 0 ≤ ∑ k, c k := Finset.sum_nonneg fun k _ => hc0 k
  refine ⟨by linarith, ?_⟩
  intro α _ _ L ℓ hℓ
  -- choose a preimage letter for each bottom-layer letter
  have hex : ∀ a : α, ∃ m : M, Pk.layerEmbed Pk.kernel m = (L a).1 :=
    fun a => MonoidHom.mem_mrange.1 (L a).2
  choose letter hletter using hex
  have hL : L = fun a =>
      MonoidHom.mrangeRestrict (Pk.layerEmbed Pk.kernel) (letter a) :=
    funext fun a => Subtype.ext (hletter a).symm
  -- the coordinate word functions, encoded into a common value type
  set enc : (k : Fin Pk.count) → ↥(MonoidHom.mrange (Pk.coord k).rep) → ℕ :=
    fun k v => (Fintype.equivFin _ v).val with henc
  have henc_inj : ∀ k, Function.Injective (enc k) := fun k v v' hv =>
    (Fintype.equivFin _).injective (Fin.val_injective hv)
  set g : Fin Pk.count → (Fin ℓ → α) → ℕ := fun k x =>
    enc k (wordProd (fun a =>
      MonoidHom.mrangeRestrict (Pk.coord k).rep (letter a)) x) with hg
  have hgdual : ∀ k, HasDual (g k) (c k * Real.sqrt (ℓ : ℝ)) := by
    intro k
    refine ((hcoord k).2 α
      (fun a => MonoidHom.mrangeRestrict (Pk.coord k).rep (letter a)) ℓ hℓ).ofKer
      fun x y => ?_
    exact ⟨fun hxy => congrArg (enc k) hxy, fun hxy => henc_inj k hxy⟩
  -- the classical decoder
  set dec : (Fin Pk.count → ℕ) → ↥(Pk.layerMonoid Pk.kernel) := fun z =>
    if hz : ∃ b : ↥(Pk.layerMonoid Pk.kernel),
        ∀ k, enc k (Pk.bottomCoord k b) = z k
    then hz.choose else 1 with hdec
  -- the word product is the decoder applied to the coordinate words
  have hkey : ∀ x : Fin ℓ → α, wordProd L x = dec (fun k => g k x) := by
    intro x
    set W : M := wordProd letter x with hW
    set b₀ : ↥(Pk.layerMonoid Pk.kernel) :=
      MonoidHom.mrangeRestrict (Pk.layerEmbed Pk.kernel) W with hb₀
    have hwordL : wordProd L x = b₀ := by
      rw [hL, hb₀, hW,
        map_wordProd (MonoidHom.mrangeRestrict (Pk.layerEmbed Pk.kernel)) letter x]
    have hcoords : ∀ k, enc k (Pk.bottomCoord k b₀) = g k x := by
      intro k
      rw [hb₀, Pk.bottomCoord_mrangeRestrict k W, hg]
      refine congrArg (enc k) ?_
      rw [hW, map_wordProd (MonoidHom.mrangeRestrict (Pk.coord k).rep) letter x]
    have hzex : ∃ b : ↥(Pk.layerMonoid Pk.kernel),
        ∀ k, enc k (Pk.bottomCoord k b) = g k x := ⟨b₀, hcoords⟩
    have hdecval : dec (fun k => g k x) = hzex.choose := by
      rw [hdec]
      exact dif_pos hzex
    rw [hwordL, hdecval]
    have hchoose := hzex.choose_spec
    refine (Pk.bottomCoord_injective fun k => ?_).symm
    exact henc_inj k ((hchoose k).trans (hcoords k).symm)
  -- assemble
  have hcomb := HasDual.combine' dec
    (fun k => mul_nonneg (hc0 k) (Real.sqrt_nonneg _)) hgdual
  rw [show (fun x : Fin ℓ → α => dec fun k => g k x)
      = (fun x : Fin ℓ → α => wordProd L x) from funext fun x => (hkey x).symm]
    at hcomb
  refine hcomb.mono (le_of_eq ?_)
  rw [← Finset.sum_mul]
  ring

end ApexPackage

/-! ## The small-coordinate route: the matrix-rank ceiling, alphabet-uniformly -/

section SmallRoute

variable {T : Type} [Monoid T] [Fintype T] [DecidableEq T] [IsAperiodicMonoid T]
variable {d : ℕ} (ρ : T →* Matrix (Fin d) (Fin d) ℚ)

/-- **The matrix-rank ceiling in `HasWordProdDualPoly` form**: the image monoid of any finite
rational matrix representation carries the alphabet-uniform contract, at the
faithful-action ceiling of its inclusion.  An arbitrary letter map into the
image lifts to `T` by choice, and `map_wordProd` transports the product. -/
theorem hasWordProdDualPoly_mrange (n₀ : ℕ) :
    HasWordProdDualPoly ↥(MonoidHom.mrange ρ) n₀
      (2 * (Fintype.card (repImage ρ) : ℝ)
        * (axisConst (n₀ + d) (repImage ρ) ^ (d + 1) + 2)) := by
  classical
  have hC1 : 1 ≤ axisConst (n₀ + d) (repImage ρ) := one_le_axisConst _ _
  have hCp : (1 : ℝ) ≤ axisConst (n₀ + d) (repImage ρ) ^ (d + 1) := one_le_pow₀ hC1
  have hcard : (0 : ℝ) ≤ (Fintype.card (repImage ρ) : ℝ) := Nat.cast_nonneg _
  refine ⟨by nlinarith, ?_⟩
  intro α _ _ L ℓ hℓ
  have hex : ∀ a : α, ∃ t : T, MonoidHom.mrangeRestrict ρ t = L a := by
    intro a
    obtain ⟨t, ht⟩ := MonoidHom.mem_mrange.1 (L a).2
    exact ⟨t, Subtype.ext ht⟩
  choose letter hletter using hex
  have hL : L = fun a => MonoidHom.mrangeRestrict ρ (letter a) :=
    funext fun a => (hletter a).symm
  rw [hL]
  exact (hasWordProdDualUpTo_mrange ρ letter n₀).2 ℓ hℓ

end SmallRoute

/-! ## The per-monoid step -/

section Step

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **Above-threshold coordinates are automatically proper**: a coordinate of
degree at least two has at least four elements in its apex class, while the
identity class of an aperiodic monoid is the singleton `{1}` — so its apex is
not the identity and its principal ideal is proper.  This is why the assembly
never needs a properness side condition on the peel branch. -/
lemma ApexCoordinate.isProper_of_two_le_degree (c : ApexCoordinate M)
    (h : 2 ≤ c.degree) : c.IsProper := by
  have h4 : 4 ≤ c.degree ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ c.degree ^ 2 := Nat.pow_le_pow_left h 2
  have hsq : 4 ≤ (jClass M c.apex).card := le_trans h4 c.degree_sq_le
  have hone : (1 : M) ∉ twoIdeal c.apex := by
    intro h1
    have hax : c.apex = 1 := one_mem_twoIdeal_iff.1 h1
    have hsub : jClass M c.apex ⊆ {1} := by
      intro b hb
      rw [mem_jClass, hax] at hb
      have h1b : (1 : M) ∈ twoIdeal b := by
        rw [hb]
        exact self_mem_twoIdeal 1
      rw [Finset.mem_singleton]
      exact one_mem_twoIdeal_iff.1 h1b
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hle
    omega
  refine ⟨fun hax => hone ?_, hone⟩
  rw [hax]
  exact self_mem_twoIdeal 1

namespace ApexPackage

variable (Pk : ApexPackage M)

open LocallyThin ApexAdapter

/-- **The per-coordinate cost of the assembly's dichotomy**: the fixed-apex
peel above the threshold, the faithful-action ceiling of the matrix-rank bound below it. -/
noncomputable def coordCost (n₀ t : ℕ) (D : ℝ) (k : Fin Pk.count) : ℝ :=
  if t < (Pk.coord k).degree then apexStep n₀ M D
  else 2 * (Fintype.card (repImage (Pk.coord k).rep) : ℝ)
    * (axisConst (n₀ + (Pk.coord k).degree) (repImage (Pk.coord k).rep)
        ^ ((Pk.coord k).degree + 1) + 2)

/-- **The per-monoid step of the assembly** — the structural content of the
carrier recurrence, with every constant still explicit and `K` untouched.
Given quotient certificates for the Rees quotients of the above-threshold
coordinates (which the strong induction supplies, since each such quotient
drops the carrier by more than `t²`), the coordinates are certified by the
dichotomy, combined through the injective joint-coordinate map at the bottom
layer, and lifted through the radical tower. -/
theorem hasWordProdDualPoly_step (n₀ t : ℕ) (ht : 2 ≤ t) {D : ℝ} (hD : 1 ≤ D)
    (hquot : ∀ (k : Fin Pk.count) (hc : (Pk.coord k).IsProper),
      t < (Pk.coord k).degree →
      HasWordProdDualPoly (ReesQuot (ReesQuot.apexIdeal (Pk.coord k) hc)) n₀ D) :
    HasWordProdDualPoly M n₀
      ((thinStep n₀ (Fintype.card M))^[Nat.clog 2 (Fintype.card M)]
        (2 * ∑ k, Pk.coordCost n₀ t D k)) := by
  have hper : ∀ k : Fin Pk.count,
      HasWordProdDualPoly ↥(MonoidHom.mrange (Pk.coord k).rep) n₀
        (Pk.coordCost n₀ t D k) := by
    intro k
    by_cases hdeg : t < (Pk.coord k).degree
    · have hc : (Pk.coord k).IsProper :=
        (Pk.coord k).isProper_of_two_le_degree (by omega)
      rw [coordCost, if_pos hdeg]
      exact hasWordProdDualPoly_apexCoord (Pk.coord k) hc hD (hquot k hc hdeg)
    · rw [coordCost, if_neg hdeg]
      exact hasWordProdDualPoly_mrange (Pk.coord k).rep n₀
  exact Pk.radical_lift' n₀ (Pk.hasWordProdDualPoly_bottom hper)

end ApexPackage

end Step

end MonoidProduct
