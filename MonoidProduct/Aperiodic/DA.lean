import MonoidProduct.Aperiodic.CubeRoot.PrincipalFactor
import MonoidProduct.Trichotomy.Index
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The variety `DA`: regular elements are idempotent

`IsDA M`: every (von Neumann) regular element is idempotent.  This file is the
semigroup theory behind the query bound for `DA` monoids:

* `isDA_iff_identity` — the equational characterization: at a uniform stabilisation exponent
  `k ≥ 1`, `M ∈ DA ↔ (xy)^k·x·(xy)^k = (xy)^k`;
* `IsDA.idem_of_twoIdeal_eq_idem` / `IsDA.twoIdeal_mul_eq` — a regular class of
  a `DA` monoid consists of idempotents and is closed under multiplication
  (the class is a rectangular band);
* `IsDA.idem_mul_mul_idem` — local absorption: if `e ≤_J a` for every `a ∈ A`
  then `e·h·e = e` for all `h ∈ ⟨A⟩`;
* `IsDA.mul_mul_eq_of_complete` — absorption and discarding in one statement:
  if `P` and `Q` are products of `|M|` blocks from `⟨A⟩` each containing every
  letter of `A` (`IsComplete`), then `P·u·Q = P·Q` for every `u ∈ ⟨A⟩`.  The
  usual route is through the minimal ideal of `⟨A⟩`; here the idempotents
  produced by the right- and left-ideal chains (`exists_absorb_right`,
  `exists_absorb_left`) are shown to multiply as in a rectangular band
  directly (`IsDA.idem_mul_mul_idem_eq`).
-/

namespace MonoidProduct
open PrincipalFactor

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- **`DA`**: every regular element is idempotent. -/
def IsDA (M : Type) [Monoid M] : Prop :=
  ∀ a : M, IsVonNeumannRegular a → IsIdempotentElem a

/-- A right multiple of a member of `M a M` is in `M a M`. -/
lemma mul_mem_twoIdeal_of_mem {a x : M} (hx : x ∈ twoIdeal a) (y : M) :
    x * y ∈ twoIdeal a := by
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 hx
  exact mem_twoIdeal.2 ⟨p, q * y, by rw [← mul_assoc, hpq]⟩

/-- A left multiple of a member of `M a M` is in `M a M`. -/
lemma mem_twoIdeal_of_mul_left {a x : M} (hx : x ∈ twoIdeal a) (y : M) :
    y * x ∈ twoIdeal a := by
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 hx
  exact mem_twoIdeal.2 ⟨y * p, q, by simp only [mul_assoc] at hpq ⊢; rw [hpq]⟩

section Aperiodic

variable [IsAperiodicMonoid M]

/-- A uniform stabilisation exponent `k ≥ 1`, with every `z^k` idempotent. -/
lemma exists_idem_pow : ∃ k : ℕ, 1 ≤ k ∧ ∀ z : M, z ^ k = z ^ (k + 1) ∧
    IsIdempotentElem (z ^ k) := by
  obtain ⟨k, hk1, hk⟩ := exists_uniform_stab (M := M)
  refine ⟨k, hk1, fun z => ⟨hk z, ?_⟩⟩
  change z ^ k * z ^ k = z ^ k
  rw [← pow_add]
  exact pow_eq_pow_of_stab (hk z) (by omega)

/-! ## The identity -/

/-- **The `DA` identity**: `M ∈ DA ↔ (xy)^k·x·(xy)^k = (xy)^k` at a uniform
stabilisation exponent `k ≥ 1`. -/
theorem isDA_iff_identity {k : ℕ} (hk1 : 1 ≤ k) (hk : ∀ z : M, z ^ k = z ^ (k + 1)) :
    IsDA M ↔ ∀ x y : M, (x * y) ^ k * x * (x * y) ^ k = (x * y) ^ k := by
  have hidem : ∀ z : M, IsIdempotentElem (z ^ k) := fun z => by
    change z ^ k * z ^ k = z ^ k
    rw [← pow_add]
    exact pow_eq_pow_of_stab (hk z) (by omega)
  constructor
  · intro hDA x y
    have he_idem : IsIdempotentElem ((x * y) ^ k) := hidem _
    have hexy : (x * y) ^ k * (x * y) = (x * y) ^ k := by rw [← pow_succ, ← hk]
    -- `e·x` is in the regular class of `e`
    have hR : REq ((x * y) ^ k * x) ((x * y) ^ k) := by
      refine rEq_iff.2 ⟨rLe_iff_exists.2 ⟨x, rfl⟩, rLe_iff_exists.2 ⟨y, ?_⟩⟩
      rw [mul_assoc, hexy]
    have hex : IsIdempotentElem ((x * y) ^ k * x) :=
      hDA _ ((IsIdempotentElem.isVonNeumannRegular he_idem).of_rEq (rEq_symm hR))
    have h3 : (x * y) ^ k * x * (x * y) ^ k * (x * y) = (x * y) ^ k * (x * y) := by
      calc (x * y) ^ k * x * (x * y) ^ k * (x * y)
          = ((x * y) ^ k * x * ((x * y) ^ k * x)) * y := by simp only [mul_assoc]
        _ = ((x * y) ^ k * x) * y := by rw [hex.eq]
        _ = (x * y) ^ k * (x * y) := by simp only [mul_assoc]
    rw [mul_assoc ((x * y) ^ k * x) ((x * y) ^ k) (x * y), hexy] at h3
    exact h3
  · intro hid a ⟨b, hab⟩
    have hf : IsIdempotentElem (a * b) := IsVonNeumannRegular.idem_right hab
    have hfk : (a * b) ^ k = a * b := by
      obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
      exact hf.pow_succ_eq d
    have h := hid a b
    rw [hfk, hab] at h
    -- `h : a·(a·b) = a·b`; times `a` on the right
    have h2 : a * (a * b) * a = a * b * a := congrArg (· * a) h
    rw [mul_assoc a (a * b) a, hab] at h2
    exact h2

/-! ## Regular classes of a `DA` monoid -/

/-- Every element of a regular class is regular. -/
lemma isVonNeumannRegular_of_twoIdeal_eq_idem {e x : M} (he : IsIdempotentElem e)
    (hx : twoIdeal x = twoIdeal e) : IsVonNeumannRegular x := by
  obtain ⟨z, hz1, hz2⟩ := exists_rEq_lEq_of_twoIdeal_eq hx.symm
  exact ((IsIdempotentElem.isVonNeumannRegular he).of_rEq hz1).of_lEq hz2

/-- In a `DA` monoid every element of a regular class is idempotent. -/
lemma IsDA.idem_of_twoIdeal_eq_idem (hDA : IsDA M) {e x : M} (he : IsIdempotentElem e)
    (hx : twoIdeal x = twoIdeal e) : IsIdempotentElem x :=
  hDA x (isVonNeumannRegular_of_twoIdeal_eq_idem he hx)

/-- **A regular class of a `DA` monoid is closed under multiplication**
(the sandwich matrix is all ones). -/
theorem IsDA.twoIdeal_mul_eq (hDA : IsDA M) {e x y : M} (he : IsIdempotentElem e)
    (hx : twoIdeal x = twoIdeal e) (hy : twoIdeal y = twoIdeal e) :
    twoIdeal (x * y) = twoIdeal e := by
  -- a cell `z` in the row of `y` and the column of `x`
  obtain ⟨z, hzy, hzx⟩ := exists_rEq_lEq_of_twoIdeal_eq (hy.trans hx.symm)
  have hz : twoIdeal z = twoIdeal e := (twoIdeal_eq_of_rEq hzy).symm.trans hy
  have hzz : IsIdempotentElem z := hDA.idem_of_twoIdeal_eq_idem he hz
  let x' : JType M e := ⟨x, mem_jClass.2 hx⟩
  let y' : JType M e := ⟨y, mem_jClass.2 hy⟩
  let z' : JType M e := ⟨z, mem_jClass.2 hz⟩
  have hl : lIdx M x' = lIdx M z' := (lIdx_eq_iff _ _).2 (lEq_symm hzx)
  have hr : rIdx M y' = rIdx M z' := (rIdx_eq_iff _ _).2 hzy
  have hzz' : sandwichBool M (lIdx M z') (rIdx M z') = true := by
    rw [sandwich_eq_true_iff]
    change twoIdeal (z * z) = twoIdeal e
    rw [hzz.eq, hz]
  exact (sandwich_eq_true_iff x' y').1 (by rw [hl, hr]; exact hzz')

/-- Inside a regular class, an element below `e` on both sides is `e`. -/
lemma IsDA.eq_of_twoIdeal_eq_of_le (_hDA : IsDA M) {e x : M} (hx : twoIdeal x = twoIdeal e)
    (hR : RLe x e) (hL : LLe x e) : x = e :=
  eq_of_rEq_of_lEq (rEq_of_twoIdeal_eq_of_rLe hx hR) (lEq_of_twoIdeal_eq_of_lLe hx hL)

/-! ## Absorbing the available letters -/

/-- **Local absorption, one letter**: if `e = u·a·v` then `e·a·e = e`. -/
lemma IsDA.idem_mul_mul_idem_of_mem (hDA : IsDA M) {e a : M} (he : IsIdempotentElem e)
    (ha : e ∈ twoIdeal a) : e * a * e = e := by
  obtain ⟨u, v, huv⟩ := mem_twoIdeal.1 ha
  obtain ⟨k, hk1, hk⟩ := exists_idem_pow (M := M)
  obtain ⟨d, hd⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have hek : e ^ k = e := by rw [hd]; exact he.pow_succ_eq d
  obtain ⟨f, hf⟩ : ∃ f : M, f = (a * v * u) ^ k := ⟨_, rfl⟩
  have hf_idem : IsIdempotentElem f := hf ▸ (hk _).2
  -- the shift `(uav)^t·u = u·(avu)^t`
  have hshift : ∀ t : ℕ, (u * a * v) ^ t * u = u * (a * v * u) ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        calc (u * a * v) ^ (t + 1) * u = (u * a * v) ^ t * u * (a * v * u) := by
              rw [pow_succ]; simp only [mul_assoc]
          _ = u * (a * v * u) ^ t * (a * v * u) := by rw [ih]
          _ = u * (a * v * u) ^ (t + 1) := by rw [pow_succ, mul_assoc]
  have h1 : u * f = e * u := by rw [hf, ← hshift, huv, hek]
  -- `e = u·f·(a·v)` and `f = (a·v)·e·u`: the same `J`-class
  have h2 : e = u * f * (a * v) := by
    calc e = e * e := he.eq.symm
      _ = e * (u * a * v) := by rw [huv]
      _ = e ^ k * u * (a * v) := by rw [hek]; simp only [mul_assoc]
      _ = (u * a * v) ^ k * u * (a * v) := by rw [huv]
      _ = u * f * (a * v) := by rw [hshift, hf]
  have h3 : f = a * v * e * u := by
    calc f = (a * v * u) ^ (k + 1) := by rw [hf, (hk _).1]
      _ = a * v * (u * (a * v * u) ^ k) := by rw [pow_succ']; simp only [mul_assoc]
      _ = a * v * (e * u) := by rw [← hf, h1]
      _ = a * v * e * u := by simp only [mul_assoc]
  have hJ : twoIdeal f = twoIdeal e := by
    refine Finset.Subset.antisymm ?_ ?_
    · exact mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨a * v, u, h3.symm⟩)
    · exact mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨u, a * v, h2.symm⟩)
  -- `e·f ∈ J`, and `e·f ≤_R e·a ≤_R e` puts `e·a` in `J`
  have hef : twoIdeal (e * f) = twoIdeal e := hDA.twoIdeal_mul_eq he rfl hJ
  have hea : twoIdeal (e * a) = twoIdeal e := by
    refine Finset.Subset.antisymm ?_ ?_
    · exact mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨1, a, by rw [one_mul]⟩)
    · rw [← hef]
      refine mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨1, v * u * (a * v * u) ^ d, ?_⟩)
      rw [one_mul, hf, hd, pow_succ']
      simp only [mul_assoc]
  -- `e·a·e ∈ J` sits below `e` on both sides
  have h4 : twoIdeal (e * a * e) = twoIdeal e := hDA.twoIdeal_mul_eq he hea rfl
  exact hDA.eq_of_twoIdeal_eq_of_le h4
    (rLe_iff_exists.2 ⟨a * e, (mul_assoc _ _ _).symm⟩) (lLe_iff_exists.2 ⟨e * a, rfl⟩)

/-- **Local absorption**: if `e ≤_J a` for every `a ∈ A`, then `e·h·e = e` for
every `h` in the submonoid generated by `A`. -/
theorem IsDA.idem_mul_mul_idem (hDA : IsDA M) {e : M} (he : IsIdempotentElem e) {A : Set M}
    (hA : ∀ a ∈ A, e ∈ twoIdeal a) : ∀ h ∈ Submonoid.closure A, e * h * e = e := by
  intro h hh
  induction hh using Submonoid.closure_induction with
  | mem a ha => exact hDA.idem_mul_mul_idem_of_mem he (hA a ha)
  | one => rw [mul_one]; exact he.eq
  | mul s t _ _ hs ht =>
      have hes : twoIdeal (e * s) = twoIdeal e := by
        refine Finset.Subset.antisymm ?_ ?_
        · exact mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨1, s, by rw [one_mul]⟩)
        · exact mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨1, e, by rw [one_mul]; exact hs⟩)
      have hte : twoIdeal (t * e) = twoIdeal e := by
        refine Finset.Subset.antisymm ?_ ?_
        · exact mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨t, 1, by rw [mul_one]⟩)
        · exact mem_twoIdeal_iff_subset.1
            (mem_twoIdeal.2 ⟨e, 1, by rw [mul_one, ← mul_assoc]; exact ht⟩)
      have hprod : twoIdeal (e * s * (t * e)) = twoIdeal e := hDA.twoIdeal_mul_eq he hes hte
      have : e * (s * t) * e = e * s * (t * e) := by simp only [mul_assoc]
      rw [this]
      exact hDA.eq_of_twoIdeal_eq_of_le hprod
        (rLe_iff_exists.2 ⟨s * (t * e), by simp only [mul_assoc]⟩)
        (lLe_iff_exists.2 ⟨e * s * t, by simp only [mul_assoc]⟩)

/-! ## The rectangular-band product of two absorbing idempotents -/

/-- If `e` and `f` are idempotents of `H` absorbing `H` (`e·h·e = e`,
`f·h·f = f`), then `e·g·f = e·f` for every `g ∈ H` (in the
rectangular band, the product keeps the left factor's row and the right
factor's column). -/
theorem IsDA.idem_mul_mul_idem_eq (hDA : IsDA M) {e f : M} (he : IsIdempotentElem e)
    (_hf : IsIdempotentElem f) {H : Submonoid M} (heH : e ∈ H) (hfH : f ∈ H)
    (he' : ∀ h ∈ H, e * h * e = e) (hf' : ∀ h ∈ H, f * h * f = f) {g : M} (hg : g ∈ H) :
    e * g * f = e * f := by
  have hx1 : e * g * f * e = e := by
    have := he' _ (H.mul_mem hg hfH)
    simpa only [mul_assoc] using this
  have hx2 : f * (e * g * f) = f := by
    have := hf' _ (H.mul_mem heH hg)
    simpa only [mul_assoc] using this
  have hJe : twoIdeal (e * g * f) = twoIdeal e :=
    Finset.Subset.antisymm
      (mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨1, g * f, by simp only [one_mul, mul_assoc]⟩))
      (mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨1, e, by rw [one_mul]; exact hx1⟩))
  have hJf : twoIdeal (e * g * f) = twoIdeal f :=
    Finset.Subset.antisymm
      (mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨e * g, 1, by rw [mul_one]⟩))
      (mem_twoIdeal_iff_subset.1 (mem_twoIdeal.2 ⟨f, 1, by rw [mul_one]; exact hx2⟩))
  have hfe : twoIdeal f = twoIdeal e := hJf.symm.trans hJe
  have hef : twoIdeal (e * f) = twoIdeal e := hDA.twoIdeal_mul_eq he rfl hfe
  have hR1 : REq (e * g * f) e :=
    rEq_of_twoIdeal_eq_of_rLe hJe (rLe_iff_exists.2 ⟨g * f, by simp only [mul_assoc]⟩)
  have hR2 : REq (e * f) e := rEq_of_twoIdeal_eq_of_rLe hef (rLe_iff_exists.2 ⟨f, rfl⟩)
  have hL1 : LEq (e * g * f) f :=
    lEq_of_twoIdeal_eq_of_lLe hJf (lLe_iff_exists.2 ⟨e * g, rfl⟩)
  have hL2 : LEq (e * f) f :=
    lEq_of_twoIdeal_eq_of_lLe (hef.trans hfe.symm) (lLe_iff_exists.2 ⟨e, rfl⟩)
  exact eq_of_rEq_of_lEq (rEq_trans hR1 (rEq_symm hR2)) (lEq_trans hL1 (lEq_symm hL2))

/-! ## Complete blocks -/

/-- A block is **complete** for `A` if it lies in `⟨A⟩` and every letter of `A`
is one of its factors. -/
def IsComplete (A : Set M) (b : M) : Prop :=
  b ∈ Submonoid.closure A ∧ ∀ a ∈ A, b ∈ twoIdeal a

/-- A decreasing chain of nonempty subsets of `M` repeats within `|M|` steps. -/
lemma exists_chain_eq (S : ℕ → Finset M) (hanti : ∀ i, S (i + 1) ⊆ S i)
    (hne : ∀ i, (S i).Nonempty) : ∃ i < Fintype.card M, S i = S (i + 1) := by
  by_contra h
  push Not at h
  have hlt : ∀ i < Fintype.card M, (S (i + 1)).card + 1 ≤ (S i).card := fun i hi =>
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hanti i, fun e => h i hi e.symm⟩)
  have hj : ∀ j ≤ Fintype.card M, (S j).card + j ≤ (S 0).card := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have := hlt j (by omega)
        have := ih (by omega)
        omega
  have h1 := hj _ le_rfl
  have h2 := Finset.card_pos.2 (hne (Fintype.card M))
  have h3 := Finset.card_le_univ (S 0)
  omega

/-- The submonoid generated by `A`, as a finset. -/
noncomputable def closureFinset (A : Set M) : Finset M := by
  classical exact Finset.univ.filter fun h => h ∈ Submonoid.closure A

lemma mem_closureFinset {A : Set M} {h : M} : h ∈ closureFinset A ↔ h ∈ Submonoid.closure A := by
  simp only [closureFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A product of blocks of `⟨A⟩` is in `⟨A⟩`. -/
lemma list_prod_mem_closure {A : Set M} {l : List M} (hl : ∀ b ∈ l, IsComplete A b) :
    l.prod ∈ Submonoid.closure A :=
  Submonoid.list_prod_mem _ fun b hb => (hl b hb).1

/-- **Absorption from the right**: after `|M|` complete blocks the prefix
product `P = p·h'` carries an idempotent `e ∈ ⟨A⟩` with `p·e = p` that absorbs
`⟨A⟩`. -/
theorem IsDA.exists_absorb_right (hDA : IsDA M) {A : Set M} {bs : List M}
    (hlen : Fintype.card M ≤ bs.length) (hbs : ∀ b ∈ bs, IsComplete A b) :
    ∃ p h' e : M, h' ∈ Submonoid.closure A ∧ bs.prod = p * h' ∧ IsIdempotentElem e ∧
      e ∈ Submonoid.closure A ∧ p * e = p ∧ ∀ h ∈ Submonoid.closure A, e * h * e = e := by
  -- the chain of right multiples `p_i·⟨A⟩`
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Finset M,
      S = fun i => (closureFinset A).image ((bs.take i).prod * ·) := ⟨_, rfl⟩
  have hmemS : ∀ i x, x ∈ S i ↔ ∃ h ∈ Submonoid.closure A, (bs.take i).prod * h = x := by
    intro i x
    rw [hS, Finset.mem_image]
    simp only [mem_closureFinset]
  have hanti : ∀ i, S (i + 1) ⊆ S i := by
    intro i x hx
    obtain ⟨h, hh, rfl⟩ := (hmemS _ _).1 hx
    by_cases hi : i < bs.length
    · refine (hmemS _ _).2 ⟨bs[i] * h, (Submonoid.closure A).mul_mem ?_ hh, ?_⟩
      · exact (hbs _ (List.getElem_mem hi)).1
      · rw [List.prod_take_succ _ _ hi, mul_assoc]
    · refine (hmemS _ _).2 ⟨h, hh, ?_⟩
      rw [List.take_of_length_le (l := bs) (by omega), List.take_of_length_le (l := bs) (by omega)]
  have hne : ∀ i, (S i).Nonempty :=
    fun i => ⟨_, (hmemS _ _).2 ⟨1, (Submonoid.closure A).one_mem, rfl⟩⟩
  obtain ⟨i, hi, hSi⟩ := exists_chain_eq S hanti hne
  have hi' : i < bs.length := by omega
  -- `p_i = p_{i+1}·c` with `c ∈ ⟨A⟩`
  have hp : (bs.take i).prod ∈ S (i + 1) := by
    rw [← hSi]
    exact (hmemS _ _).2 ⟨1, (Submonoid.closure A).one_mem, mul_one _⟩
  obtain ⟨c, hc, hpc⟩ := (hmemS _ _).1 hp
  rw [List.prod_take_succ _ _ hi', mul_assoc] at hpc
  have hbH : bs[i] ∈ Submonoid.closure A := (hbs _ (List.getElem_mem hi')).1
  obtain ⟨k, hk1, hk⟩ := exists_idem_pow (M := M)
  obtain ⟨d, hd⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  refine ⟨(bs.take i).prod, (bs.drop i).prod, (bs[i] * c) ^ k,
    Submonoid.list_prod_mem _ fun x hx => (hbs x (List.mem_of_mem_drop hx)).1,
    (List.prod_take_mul_prod_drop bs i).symm, (hk _).2,
    (Submonoid.closure A).pow_mem ((Submonoid.closure A).mul_mem hbH hc) k, ?_, ?_⟩
  · -- `p·(bc)^t = p`
    have : ∀ t : ℕ, (bs.take i).prod * (bs[i] * c) ^ t = (bs.take i).prod := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ', ← mul_assoc, hpc, ih]
    exact this k
  · refine hDA.idem_mul_mul_idem (hk _).2 fun a ha => ?_
    rw [hd, pow_succ']
    exact mul_mem_twoIdeal_of_mem
      (mul_mem_twoIdeal_of_mem ((hbs _ (List.getElem_mem hi')).2 a ha) c) _

/-- **Absorption from the left**: after `|M|` complete blocks the suffix
product `Q = h''·q` carries an idempotent `f ∈ ⟨A⟩` with `f·q = q` that absorbs
`⟨A⟩`. -/
theorem IsDA.exists_absorb_left (hDA : IsDA M) {A : Set M} {cs : List M}
    (hlen : Fintype.card M ≤ cs.length) (hcs : ∀ c ∈ cs, IsComplete A c) :
    ∃ q h'' f : M, h'' ∈ Submonoid.closure A ∧ cs.prod = h'' * q ∧ IsIdempotentElem f ∧
      f ∈ Submonoid.closure A ∧ f * q = q ∧ ∀ h ∈ Submonoid.closure A, f * h * f = f := by
  -- the chain of left multiples `⟨A⟩·q_j`, `q_j = (cs.drop j).prod`, read backwards
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Finset M,
      S = fun i => (closureFinset A).image (· * (cs.drop (cs.length - i)).prod) := ⟨_, rfl⟩
  have hmemS : ∀ i x, x ∈ S i ↔
      ∃ h ∈ Submonoid.closure A, h * (cs.drop (cs.length - i)).prod = x := by
    intro i x
    rw [hS, Finset.mem_image]
    simp only [mem_closureFinset]
  have hdrop : ∀ j (hj : j < cs.length),
      (cs.drop j).prod = cs[j]'hj * (cs.drop (j + 1)).prod := by
    intro j hj
    rw [List.drop_eq_getElem_cons hj, List.prod_cons]
  have hanti : ∀ i, S (i + 1) ⊆ S i := by
    intro i x hx
    obtain ⟨h, hh, rfl⟩ := (hmemS _ _).1 hx
    by_cases hi : i < cs.length
    · have hj : cs.length - (i + 1) < cs.length := by omega
      refine (hmemS _ _).2 ⟨h * cs[cs.length - (i + 1)]'hj,
        (Submonoid.closure A).mul_mem hh (hcs _ (List.getElem_mem hj)).1, ?_⟩
      rw [show cs.length - i = cs.length - (i + 1) + 1 by omega, hdrop _ hj, mul_assoc]
    · refine (hmemS _ _).2 ⟨h, hh, ?_⟩
      rw [show cs.length - (i + 1) = 0 by omega, show cs.length - i = 0 by omega]
  have hne : ∀ i, (S i).Nonempty :=
    fun i => ⟨_, (hmemS _ _).2 ⟨1, (Submonoid.closure A).one_mem, rfl⟩⟩
  obtain ⟨i, hi, hSi⟩ := exists_chain_eq S hanti hne
  have hj : cs.length - (i + 1) < cs.length := by omega
  have hnj : cs.length - i = cs.length - (i + 1) + 1 := by omega
  -- `q_{j+1} = c·q_j = c·b·q_{j+1}` with `c ∈ ⟨A⟩`
  have hq : (cs.drop (cs.length - (i + 1) + 1)).prod ∈ S (i + 1) := by
    rw [← hSi]
    exact (hmemS _ _).2 ⟨1, (Submonoid.closure A).one_mem, by rw [one_mul, hnj]⟩
  obtain ⟨c, hc, hqc⟩ := (hmemS _ _).1 hq
  rw [hdrop _ hj, ← mul_assoc] at hqc
  have hbH : cs[cs.length - (i + 1)]'hj ∈ Submonoid.closure A := (hcs _ (List.getElem_mem hj)).1
  obtain ⟨k, hk1, hk⟩ := exists_idem_pow (M := M)
  obtain ⟨d, hd⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  refine ⟨(cs.drop (cs.length - (i + 1) + 1)).prod, (cs.take (cs.length - (i + 1) + 1)).prod,
    (c * cs[cs.length - (i + 1)]'hj) ^ k,
    Submonoid.list_prod_mem _ fun x hx => (hcs x (List.mem_of_mem_take hx)).1,
    (List.prod_take_mul_prod_drop cs _).symm, (hk _).2,
    (Submonoid.closure A).pow_mem ((Submonoid.closure A).mul_mem hc hbH) k, ?_, ?_⟩
  · have : ∀ t : ℕ, (c * cs[cs.length - (i + 1)]'hj) ^ t * (cs.drop (cs.length - (i + 1) + 1)).prod
        = (cs.drop (cs.length - (i + 1) + 1)).prod := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, mul_assoc, hqc, ih]
    exact this k
  · refine hDA.idem_mul_mul_idem (hk _).2 fun a ha => ?_
    rw [hd, pow_succ]
    exact mem_twoIdeal_of_mul_left
      (mem_twoIdeal_of_mul_left ((hcs _ (List.getElem_mem hj)).2 a ha) c) _

/-- **Absorption and discarding**: `|M|` complete blocks on each side make the
middle irrelevant, `P·u·Q = P·Q` for every `u ∈ ⟨A⟩`. -/
theorem IsDA.mul_mul_eq_of_complete (hDA : IsDA M) {A : Set M} {bs cs : List M}
    (hb : Fintype.card M ≤ bs.length) (hc : Fintype.card M ≤ cs.length)
    (hbs : ∀ b ∈ bs, IsComplete A b) (hcs : ∀ c ∈ cs, IsComplete A c)
    {u : M} (hu : u ∈ Submonoid.closure A) :
    bs.prod * u * cs.prod = bs.prod * cs.prod := by
  obtain ⟨p, h', e, hh', hP, he, heH, hpe, he'⟩ := hDA.exists_absorb_right hb hbs
  obtain ⟨q, h'', f, hh'', hQ, hf, hfH, hfq, hf'⟩ := hDA.exists_absorb_left hc hcs
  have key : ∀ g ∈ Submonoid.closure A, p * g * q = p * (e * f) * q := fun g hg => by
    calc p * g * q = p * e * g * (f * q) := by rw [hpe, hfq]
      _ = p * (e * g * f) * q := by simp only [mul_assoc]
      _ = p * (e * f) * q := by rw [hDA.idem_mul_mul_idem_eq he hf heH hfH he' hf' hg]
  rw [hP, hQ]
  calc p * h' * u * (h'' * q) = p * (h' * u * h'') * q := by simp only [mul_assoc]
    _ = p * (e * f) * q :=
        key _ ((Submonoid.closure A).mul_mem ((Submonoid.closure A).mul_mem hh' hu) hh'')
    _ = p * (h' * h'') * q := (key _ ((Submonoid.closure A).mul_mem hh' hh'')).symm
    _ = p * h' * (h'' * q) := by simp only [mul_assoc]

end Aperiodic

end MonoidProduct
