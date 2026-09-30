import MonoidProduct.Width.Product
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Product fibers contain no large sunflower (`monoid.tex`, `lem:no-product-sunflower`)

For a finite commutative monoid with `x^{k+1} = x^k`, the full fibers of
the subset product over the essential positions contain no
`(k+1)`-sunflower. The `t`-uniform version follows as a corollary.

This is the monoid-specific half of the general-index width bound
(`thm:index-k-width`): combined with **any** bound `F(t)` on the size of a
`t`-uniform `(k+1)`-sunflower-free family, the fiber partition gives
`C(B, t) ≤ |M| · F(t)` (`choose_le_card_mul_of_fiber_card_le` below).  The
sunflower theorem supplying `F` is deliberately *not* imported here:

* the Bell–Chueluecha–Warnke bound `F(t) < (2⁶⁰·(k+1)·lg t)^t` is formalized
  in `tcs-formalizations-public` (`Sunflower.RaoBCW.rao_bcw_uniform`), which
  is built on Lean/Mathlib **v4.33.0** — consuming it awaits the gated
  toolchain migration of this repo;
* the sunflower definitions below (`IsSunflowerWith`, `IsSunflower`,
  `HasSunflower`) mirror `Sunflower/Defs.lean` of that repository **verbatim**,
  so that the post-migration bridge is definitional.

The proof of the sunflower-freeness is the paper's: a sunflower
`K ∪ P₀, …, K ∪ P_k` in a fiber gives `c·b₀ = ⋯ = c·b_k` for the petal
products, so the product over the whole union is `c·b₀^{k+1} = c·b₀^k` — the
petal `P₀` is deletable wholesale, absorption (`mul_right_absorb`) makes each
of its factors individually deletable, and edge strictness
(`ctxProd_ne_erase`) contradicts essentiality. Since the sunflower has at
least two distinct members, one differs from the core; choose it as the
distinguished member so that `P₀` is nonempty. The other petals may be
empty. Uniformity is needed only for the subsequent counting bound.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open Finset

/-! ## Sunflowers

Verbatim mirrors of `Sunflower/Defs.lean` from `tcs-formalizations-public`
(commit `58e94f3`), so that after the toolchain migration the bridge to
`Sunflower.IsSunflower` is `Iff.rfl`. -/

section SunflowerDefs

variable {α : Type*} [DecidableEq α]

/-- `IsSunflowerWith 𝒮 K` : any two distinct members of `𝒮` meet exactly in
`K`. -/
def IsSunflowerWith (𝒮 : Finset (Finset α)) (K : Finset α) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝒮 → ∀ ⦃T⦄, T ∈ 𝒮 → S ≠ T → S ∩ T = K

/-- `IsSunflower r 𝒮` : `𝒮` is a sunflower with `r` petals. -/
def IsSunflower (r : ℕ) (𝒮 : Finset (Finset α)) : Prop :=
  𝒮.card = r ∧ ∃ K, IsSunflowerWith 𝒮 K

/-- A family `𝓕` contains an `r`-sunflower. -/
def HasSunflower (r : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∃ 𝒮 ⊆ 𝓕, IsSunflower r 𝒮

end SunflowerDefs

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {M : Type*} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- A set with more than one element has a member different from any given
point. -/
lemma exists_mem_ne {α : Type*} [DecidableEq α] {s : Finset α} (h : 1 < s.card)
    (a : α) : ∃ b ∈ s, b ≠ a := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
  rcases eq_or_ne u a with rfl | hua
  · exact ⟨v, hv, huv.symm⟩
  · exact ⟨u, hu, hua⟩

variable (m : σ → M) (x : ι → σ) (T : Finset ι)

/-- The context product over a disjoint union splits. -/
lemma ctxProd_union {S₁ S₂ : Finset ι} (h : Disjoint S₁ S₂) :
    ctxProd m x T (S₁ ∪ S₂) = ctxProd m x T S₁ * ∏ j ∈ S₂, m (x j) := by
  rw [ctxProd, ctxProd, Finset.prod_union h, mul_assoc]

/-- **The full product fiber** over the essential positions. -/
def fullProdFiber (z : M) : Finset (Finset ι) :=
  (prodEss m x T).powerset.filter fun S => ctxProd m x T S = z

lemma mem_fullProdFiber {z : M} {S : Finset ι} :
    S ∈ fullProdFiber m x T z
      ↔ S ⊆ prodEss m x T ∧ ctxProd m x T S = z := by
  rw [fullProdFiber, Finset.mem_filter, Finset.mem_powerset]

/-- **The `t`-uniform product fiber** over the essential positions. -/
def prodFiber (z : M) (t : ℕ) : Finset (Finset ι) :=
  ((prodEss m x T).powersetCard t).filter fun S => ctxProd m x T S = z

lemma mem_prodFiber {z : M} {t : ℕ} {S : Finset ι} :
    S ∈ prodFiber m x T z t
      ↔ (S ⊆ prodEss m x T ∧ S.card = t) ∧ ctxProd m x T S = z := by
  rw [prodFiber, Finset.mem_filter, Finset.mem_powersetCard]

/-- **Full product fibers contain no `(k+1)`-sunflower**
(`monoid.tex`, `lem:no-product-sunflower`). No uniformity is required. -/
theorem not_isSunflower_of_subset_fullProdFiber
    {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k)
    {z : M} {𝒮 : Finset (Finset ι)}
    (h𝒮 : 𝒮 ⊆ fullProdFiber m x T z) : ¬ IsSunflower (k + 1) 𝒮 := by
  classical
  rintro ⟨hcard, K, hK⟩
  have : IsAperiodicMonoid M := ⟨fun a => ⟨k, hk, (hxk a).symm⟩⟩
  have hmem : ∀ S ∈ 𝒮, S ⊆ prodEss m x T ∧ ctxProd m x T S = z :=
    fun S hS => (mem_fullProdFiber m x T).mp (h𝒮 hS)
  have h2 : 1 < 𝒮.card := by omega
  -- the core lies inside every member
  have hKS : ∀ S ∈ 𝒮, K ⊆ S := by
    intro S hS
    obtain ⟨S', hS', hne⟩ := exists_mem_ne h2 S
    rw [← hK hS hS' hne.symm]
    exact Finset.inter_subset_left
  -- petals are pairwise disjoint
  have hpet : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → Disjoint (S \ K) (S' \ K) := by
    intro S hS S' hS' hne
    rw [Finset.disjoint_left]
    intro a haS haS'
    have haK : a ∈ K := by
      rw [← hK hS hS' hne]
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp haS).1,
        (Finset.mem_sdiff.mp haS').1⟩
    exact (Finset.mem_sdiff.mp haS).2 haK
  -- choose a member different from the core, so its petal is nonempty
  obtain ⟨S₀, hS₀, hS₀K⟩ := exists_mem_ne h2 K
  have hPne : (S₀ \ K).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hSK
    exact hS₀K (Finset.Subset.antisymm hSK (hKS S₀ hS₀))
  -- the core and petal products
  set c : M := ctxProd m x T K with hc
  set b : Finset ι → M := fun S => ∏ j ∈ S \ K, m (x j) with hb
  have hdecomp : ∀ S ∈ 𝒮, ctxProd m x T S = c * b S := by
    intro S hS
    have hu : K ∪ S \ K = S := Finset.union_sdiff_of_subset (hKS S hS)
    calc ctxProd m x T S = ctxProd m x T (K ∪ S \ K) := by rw [hu]
      _ = c * b S := ctxProd_union m x T Finset.disjoint_sdiff
  have hfib : ∀ S ∈ 𝒮, c * b S = c * b S₀ := by
    intro S hS
    rw [← hdecomp S hS, ← hdecomp S₀ hS₀, (hmem S hS).2, (hmem S₀ hS₀).2]
  -- the product over any subfamily collapses to a power of `b S₀`
  have hpow : ∀ 𝒯 : Finset (Finset ι), 𝒯 ⊆ 𝒮 →
      c * ∏ S ∈ 𝒯, b S = c * b S₀ ^ 𝒯.card := by
    intro 𝒯
    induction 𝒯 using Finset.induction_on with
    | empty => intro _; simp
    | insert S 𝒯 hS ih =>
        intro hsub
        have hS𝒮 : S ∈ 𝒮 := hsub (Finset.mem_insert_self S 𝒯)
        have h𝒯 : 𝒯 ⊆ 𝒮 := (Finset.subset_insert S 𝒯).trans hsub
        rw [Finset.prod_insert hS, Finset.card_insert_of_notMem hS]
        calc c * (b S * ∏ S' ∈ 𝒯, b S')
            = (c * b S) * ∏ S' ∈ 𝒯, b S' := by ac_rfl
          _ = (c * b S₀) * ∏ S' ∈ 𝒯, b S' := by rw [hfib S hS𝒮]
          _ = b S₀ * (c * ∏ S' ∈ 𝒯, b S') := by ac_rfl
          _ = b S₀ * (c * b S₀ ^ 𝒯.card) := by rw [ih h𝒯]
          _ = c * b S₀ ^ (𝒯.card + 1) := by rw [pow_succ]; ac_rfl
  -- the two unions
  set 𝒮' : Finset (Finset ι) := 𝒮.erase S₀ with h𝒮'
  set P₀ : Finset ι := S₀ \ K with hP₀
  set petals' : Finset ι := 𝒮'.biUnion (fun S => S \ K) with hpetals'
  set V' : Finset ι := K ∪ petals' with hV'def
  set V : Finset ι := V' ∪ P₀ with hVdef
  have h𝒮'card : 𝒮'.card = k := by
    rw [h𝒮', Finset.card_erase_of_mem hS₀, hcard]
    omega
  have hdisjKp : Disjoint K petals' := by
    rw [hpetals', Finset.disjoint_biUnion_right]
    exact fun S _ => Finset.disjoint_sdiff
  have hdisjV'P : Disjoint V' P₀ := by
    rw [hV'def, Finset.disjoint_union_left]
    constructor
    · exact Finset.disjoint_sdiff
    · rw [hpetals', Finset.disjoint_biUnion_left]
      intro S hS
      exact hpet S (Finset.mem_of_mem_erase hS) S₀ hS₀
        (Finset.ne_of_mem_erase hS)
  have hVsub : V ⊆ prodEss m x T := by
    rw [hVdef, hV'def]
    refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
    · exact (hKS S₀ hS₀).trans (hmem S₀ hS₀).1
    · rw [hpetals']
      refine Finset.biUnion_subset.mpr fun S hS => ?_
      exact (Finset.sdiff_subset).trans (hmem S (Finset.mem_of_mem_erase hS)).1
    · exact (Finset.sdiff_subset).trans (hmem S₀ hS₀).1
  -- the two context products
  have hprodpetals' : ∏ j ∈ petals', m (x j) = ∏ S ∈ 𝒮', b S := by
    rw [hpetals']
    refine Finset.prod_biUnion ?_
    intro S hS S' hS' hne
    show Disjoint (S \ K) (S' \ K)
    exact hpet S (Finset.mem_of_mem_erase (Finset.mem_coe.mp hS))
      S' (Finset.mem_of_mem_erase (Finset.mem_coe.mp hS')) hne
  have hprodV' : ctxProd m x T V' = c * b S₀ ^ k := by
    rw [hV'def, ctxProd_union m x T hdisjKp, hprodpetals', ← hc, ← h𝒮'card]
    exact hpow 𝒮' (Finset.erase_subset S₀ 𝒮)
  have hVsplit : ctxProd m x T V = ctxProd m x T V' * ∏ j ∈ P₀, m (x j) := by
    rw [hVdef]
    exact ctxProd_union m x T hdisjV'P
  have hprodV : ctxProd m x T V = ctxProd m x T V' := by
    rw [hVsplit, hprodV']
    have hbP : ∏ j ∈ P₀, m (x j) = b S₀ := by rw [hb, hP₀]
    rw [hbP, mul_assoc, ← pow_succ, hxk (b S₀)]
  -- the endgame: one factor of the deleted petal survives, absorption kills it
  obtain ⟨i, hi⟩ : P₀.Nonempty := hPne
  have hiV' : i ∉ V' := Finset.disjoint_right.mp hdisjV'P hi
  have hiV : i ∈ V := by
    rw [hVdef]
    exact Finset.mem_union_right V' hi
  have hverase : V.erase i = V' ∪ P₀.erase i := by
    rw [hVdef, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hiV']
  have hdisjV'Q : Disjoint V' (P₀.erase i) :=
    hdisjV'P.mono_right (Finset.erase_subset i P₀)
  have hw : ctxProd m x T (V.erase i)
      = ctxProd m x T V' * ∏ j ∈ P₀.erase i, m (x j) := by
    rw [hverase]
    exact ctxProd_union m x T hdisjV'Q
  -- absorption of the whole petal, then of the single factor
  have hpe : m (x i) * ∏ j ∈ P₀.erase i, m (x j) = ∏ j ∈ P₀, m (x j) :=
    Finset.mul_prod_erase P₀ (fun j => m (x j)) hi
  have habs0 : ctxProd m x T V'
      * (m (x i) * ∏ j ∈ P₀.erase i, m (x j)) = ctxProd m x T V' := by
    rw [hpe, ← hVsplit]
    exact hprodV
  have hV'a : ctxProd m x T V' * m (x i) = ctxProd m x T V' :=
    mul_right_absorb habs0
  have hwa : ctxProd m x T (V.erase i) * m (x i) = ctxProd m x T (V.erase i) := by
    rw [hw]
    calc (ctxProd m x T V' * ∏ j ∈ P₀.erase i, m (x j)) * m (x i)
        = (ctxProd m x T V' * m (x i)) * ∏ j ∈ P₀.erase i, m (x j) := by ac_rfl
      _ = ctxProd m x T V' * ∏ j ∈ P₀.erase i, m (x j) := by rw [hV'a]
  refine ctxProd_ne_erase m x T hVsub hiV ?_
  calc ctxProd m x T V
      = ctxProd m x T V' * ∏ j ∈ P₀, m (x j) := hVsplit
    _ = ctxProd m x T V' * (m (x i) * ∏ j ∈ P₀.erase i, m (x j)) := by
        rw [hpe]
    _ = (ctxProd m x T V' * ∏ j ∈ P₀.erase i, m (x j)) * m (x i) := by ac_rfl
    _ = ctxProd m x T (V.erase i) * m (x i) := by rw [← hw]
    _ = ctxProd m x T (V.erase i) := hwa

/-- **The full fiber contains no `(k+1)`-sunflower**, without fixing set sizes. -/
theorem not_hasSunflower_fullProdFiber
    {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (z : M) :
    ¬ HasSunflower (k + 1) (fullProdFiber m x T z) := by
  rintro ⟨𝒮, hsub, hsf⟩
  exact not_isSunflower_of_subset_fullProdFiber m x T hxk hk hsub hsf

/-- The `t`-uniform version follows by inclusion in the full fiber. -/
theorem not_isSunflower_of_subset_prodFiber
    {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k)
    {z : M} {t : ℕ} {𝒮 : Finset (Finset ι)}
    (h𝒮 : 𝒮 ⊆ prodFiber m x T z t) : ¬ IsSunflower (k + 1) 𝒮 := by
  apply not_isSunflower_of_subset_fullProdFiber m x T hxk hk (z := z)
  intro S hS
  obtain ⟨⟨hsub, _⟩, hprod⟩ := (mem_prodFiber m x T).mp (h𝒮 hS)
  exact (mem_fullProdFiber m x T).mpr ⟨hsub, hprod⟩

/-- **The uniform fiber contains no `(k+1)`-sunflower** — the `HasSunflower` form the
sunflower theorem's contrapositive consumes. -/
theorem not_hasSunflower_prodFiber
    {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k) (z : M) (t : ℕ) :
    ¬ HasSunflower (k + 1) (prodFiber m x T z t) := by
  rintro ⟨𝒮, hsub, hsf⟩
  exact not_isSunflower_of_subset_prodFiber m x T hxk hk hsub hsf

/-! ## The fiber partition

Any bound on a single fiber multiplies by `|M|` into a bound on all
`t`-subsets of the essential set — the counting half of
`thm:index-k-width`, independent of *which* sunflower theorem supplies the fiber
bound. -/

/-- **The fiber partition count**: `C(B, t) ≤ |M| · F` whenever every
`t`-uniform fiber has at most `F` members. -/
theorem choose_le_card_mul_of_fiber_card_le {t F : ℕ}
    (hF : ∀ z : M, (prodFiber m x T z t).card ≤ F) :
    (prodEss m x T).card.choose t ≤ Fintype.card M * F := by
  classical
  have hpart : (prodEss m x T).powersetCard t
      = (Finset.univ : Finset M).biUnion (fun z => prodFiber m x T z t) := by
    ext S
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hS
      exact ⟨ctxProd m x T S, (mem_prodFiber m x T).mpr
        ⟨Finset.mem_powersetCard.mp hS, rfl⟩⟩
    · rintro ⟨z, hS⟩
      exact Finset.mem_powersetCard.mpr ((mem_prodFiber m x T).mp hS).1
  calc (prodEss m x T).card.choose t
      = ((prodEss m x T).powersetCard t).card :=
        (Finset.card_powersetCard t _).symm
    _ = ∑ z : M, (prodFiber m x T z t).card := by
        rw [hpart, Finset.card_biUnion]
        intro z₁ _ z₂ _ hne
        show Disjoint (prodFiber m x T z₁ t) (prodFiber m x T z₂ t)
        rw [Finset.disjoint_left]
        intro S hS₁ hS₂
        exact hne (((mem_prodFiber m x T).mp hS₁).2.symm.trans
          ((mem_prodFiber m x T).mp hS₂).2)
    _ ≤ ∑ _z : M, F := Finset.sum_le_sum fun z _ => hF z
    _ = Fintype.card M * F := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end MonoidProduct
