import MonoidProduct.Aperiodic.CubeRoot.Green
import MonoidProduct.Aperiodic.CubeRoot.ApexData
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The cells of a principal factor

The first step of the Munn decomposition, and the only one that touches no
matrices: what a `J`-class *looks like* as a Rees 0-matrix semigroup.  Three
facts, in the order they depend on each other.

* **`H`-triviality** (`eq_of_rEq_of_lEq`).  In an aperiodic monoid an element is
  determined by its `R`-class and its `L`-class.  Four lines, and no Green's
  lemma: from `a = v·b`, `b = a·u` one gets `a = vᵏ·a·uᵏ` for every `k`, and at
  the exponent where `u` stabilises that reads `a = a·u = b`.  This is the only
  **direct** appeal to the stabilisation exponent in the file — aperiodicity
  also enters, less visibly, through every use of stability, which this
  development proves from the aperiodic sandwich lemmas.  It is exactly what
  makes the sandwich group trivial — `ReesBlock`'s `M⁰(1; I, Λ; P)`;
* **`J = D`** (`exists_rEq_lEq_of_twoIdeal_eq`).  Two elements of one `J`-class
  are joined by a third that is `R`-equivalent to the first and `L`-equivalent
  to the second.  This needs no *regularity* — only stability, which is where
  its `IsAperiodicMonoid` hypothesis is spent — and it is what makes the cell
  map *onto*: every `(R, L)` pair of the class is occupied;
* **the cells** (`cellEquiv`).  Together: the `J`-class is in bijection with
  `RIdx × LIdx`, which is the second regularity fact the construction needs
  and gives the apex charge `d² ≤ |J|` immediately (`card_jClass_eq`).

**The index types are ideals, not quotients.**  `REq` is *defined* as equality
of right ideals, so indexing the `R`-classes by the right ideals they generate
makes `rIdx x = rIdx y ↔ REq x y` hold by `Subtype.ext_iff` and nothing else.
A `Quotient` would have needed a setoid, its `DecidableRel`, and a `Fintype`
instance transported through a `def`, for a relation that was already an
equality.

The sandwich and the regularity facts follow: `sandwichBool` records whether an
`L`-class times an `R`-class stays in the class, well-defined by the two
congruence lemmas, and a *regular* class has **no zero row and no zero column**
(`exists_sandwich_row`, `exists_sandwich_col`) — witnessed by the idempotents
that regularity supplies, not by a counting argument.

Finally the **multiplication bridge** (`rIdx_mul`, `lIdx_mul`,
`twoIdeal_mul_ssubset`), without which none of the above would yet say that the
principal factor *is* a Rees 0-matrix semigroup.  Cell data alone does not: it
is these three that read off `(i,λ)(j,μ) = (i,μ)` when `P λ j`, and `0`
otherwise.  They are stated as local laws rather than as a bundled semigroup
equivalence, which is all the row/column matrix action (`PrincipalMatrix`)
consumes.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace PrincipalFactor

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## `H`-triviality -/

/-- **An aperiodic monoid is `H`-trivial**: an element is determined by its
`R`-class together with its `L`-class.

The argument is a single stabilisation.  With `a = v·b` and `b = a·u`, one step
gives `v·a·u = a`, hence `vᵏ·a·uᵏ = a` for every `k`; at an exponent where `u`
stabilises, `uᴺ = uᴺ⁺¹` turns that into `a = a·u = b`.  No Green's lemma, and no
subgroup theory — which is the point, since the subgroup being trivial is what
`ReesBlock`'s trivial-group block assumes. -/
theorem eq_of_rEq_of_lEq [IsAperiodicMonoid M] {a b : M} (hR : REq a b)
    (hL : LEq a b) : a = b := by
  obtain ⟨u, hu⟩ := rLe_iff_exists.1 (rEq_iff.1 hR).2
  obtain ⟨v, hv⟩ := lLe_iff_exists.1 (lEq_iff.1 hL).1
  have h1 : v * a * u = a := by rw [mul_assoc, hu, hv]
  have key : ∀ k : ℕ, v ^ k * a * u ^ k = a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ' v k, pow_succ u k]
        calc v * v ^ k * a * (u ^ k * u) = v * (v ^ k * a * u ^ k) * u := by
              simp only [mul_assoc]
          _ = v * a * u := by rw [ih]
          _ = a := h1
  obtain ⟨N, -, hpow⟩ := IsAperiodicMonoid.stabilizes u
  calc a = v ^ N * a * u ^ N := (key N).symm
    _ = v ^ N * a * u ^ (N + 1) := by rw [hpow]
    _ = v ^ N * a * u ^ N * u := by rw [pow_succ]; simp only [mul_assoc]
    _ = a * u := by rw [key N]
    _ = b := hu

/-! ## `J = D` -/

/-- **Two elements of one `J`-class are joined by a corner.**  This is `J = D`
in the form the cell map needs, and it is pure stability — no regularity.  The
corner is `x · q` for any factorisation `y = p · x · q`: it is below `x` on the
right and above `y` on the left, and both containments are equalities because
the whole chain sits in one `J`-class. -/
theorem exists_rEq_lEq_of_twoIdeal_eq [IsAperiodicMonoid M] {x y : M}
    (h : twoIdeal x = twoIdeal y) : ∃ z : M, REq x z ∧ LEq z y := by
  have hy : y ∈ twoIdeal x := by rw [h]; exact self_mem_twoIdeal y
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 hy
  refine ⟨x * q, ?_, ?_⟩
  · have hRle : RLe (x * q) x := rLe_iff_exists.2 ⟨q, rfl⟩
    have hLle : LLe y (x * q) := lLe_iff_exists.2 ⟨p, by rw [← hpq, mul_assoc]⟩
    have h1 : twoIdeal (x * q) ⊆ twoIdeal x := twoIdeal_subset_of_rLe hRle
    have h2 : twoIdeal y ⊆ twoIdeal (x * q) := twoIdeal_subset_of_lLe hLle
    exact rEq_symm (rEq_of_twoIdeal_eq_of_rLe
      (Finset.Subset.antisymm h1 (h ▸ h2)) hRle)
  · have hLle : LLe y (x * q) := lLe_iff_exists.2 ⟨p, by rw [← hpq, mul_assoc]⟩
    have hRle : RLe (x * q) x := rLe_iff_exists.2 ⟨q, rfl⟩
    have h1 : twoIdeal (x * q) ⊆ twoIdeal x := twoIdeal_subset_of_rLe hRle
    have h2 : twoIdeal y ⊆ twoIdeal (x * q) := twoIdeal_subset_of_lLe hLle
    exact lEq_symm (lEq_of_twoIdeal_eq_of_lLe
      (Finset.Subset.antisymm h2 (h ▸ h1)) hLle)

/-! ## Moving inside a class does not move the product's class -/

/-- Replacing the left factor by an `L`-equivalent one leaves the product's
`J`-class alone. -/
lemma twoIdeal_mul_congr_left {u u' w : M} (h : LEq u u') :
    twoIdeal (u * w) = twoIdeal (u' * w) := by
  obtain ⟨p, hp⟩ := lLe_iff_exists.1 (lEq_iff.1 h).1
  obtain ⟨p', hp'⟩ := lLe_iff_exists.1 (lEq_iff.1 h).2
  refine Finset.Subset.antisymm (twoIdeal_subset_of_lLe (lLe_iff_exists.2 ⟨p, ?_⟩))
    (twoIdeal_subset_of_lLe (lLe_iff_exists.2 ⟨p', ?_⟩))
  · rw [← mul_assoc, hp]
  · rw [← mul_assoc, hp']

/-- Replacing the right factor by an `R`-equivalent one leaves the product's
`J`-class alone. -/
lemma twoIdeal_mul_congr_right {u w w' : M} (h : REq w w') :
    twoIdeal (u * w) = twoIdeal (u * w') := by
  obtain ⟨q, hq⟩ := rLe_iff_exists.1 (rEq_iff.1 h).1
  obtain ⟨q', hq'⟩ := rLe_iff_exists.1 (rEq_iff.1 h).2
  refine Finset.Subset.antisymm (twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨q, ?_⟩))
    (twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨q', ?_⟩))
  · rw [mul_assoc, hq]
  · rw [mul_assoc, hq']

/-! ## The class, and its two index types -/

variable (M) in
/-- The `J`-class of `a`, as a type. -/
abbrev JType (a : M) : Type := {b : M // b ∈ jClass M a}

variable (M) in
/-- **The `R`-classes of the `J`-class**, indexed by the right ideals they
generate.  `REq` *is* equality of right ideals, so this makes `rIdx x = rIdx y`
and `REq x y` the same statement by `Subtype.ext_iff`. -/
def RIdx (a : M) : Type := {s : Finset M // ∃ x, x ∈ jClass M a ∧ s = rightIdeal x}

variable (M) in
/-- **The `L`-classes of the `J`-class**, indexed by their left ideals. -/
def LIdx (a : M) : Type := {s : Finset M // ∃ x, x ∈ jClass M a ∧ s = leftIdeal x}

instance (a : M) : DecidableEq (RIdx M a) :=
  inferInstanceAs (DecidableEq {s : Finset M // ∃ x, x ∈ jClass M a ∧ s = rightIdeal x})

instance (a : M) : Fintype (RIdx M a) :=
  inferInstanceAs (Fintype {s : Finset M // ∃ x, x ∈ jClass M a ∧ s = rightIdeal x})

instance (a : M) : DecidableEq (LIdx M a) :=
  inferInstanceAs (DecidableEq {s : Finset M // ∃ x, x ∈ jClass M a ∧ s = leftIdeal x})

instance (a : M) : Fintype (LIdx M a) :=
  inferInstanceAs (Fintype {s : Finset M // ∃ x, x ∈ jClass M a ∧ s = leftIdeal x})

variable (M) in
/-- The `R`-class of an element of the class. -/
def rIdx {a : M} (x : JType M a) : RIdx M a := ⟨rightIdeal x.1, x.1, x.2, rfl⟩

variable (M) in
/-- The `L`-class of an element of the class. -/
def lIdx {a : M} (x : JType M a) : LIdx M a := ⟨leftIdeal x.1, x.1, x.2, rfl⟩

lemma rIdx_eq_iff {a : M} (x y : JType M a) : rIdx M x = rIdx M y ↔ REq x.1 y.1 :=
  Subtype.ext_iff

lemma lIdx_eq_iff {a : M} (x y : JType M a) : lIdx M x = lIdx M y ↔ LEq x.1 y.1 :=
  Subtype.ext_iff

variable (M) in
/-- A representative of an `R`-class. -/
noncomputable def rRep {a : M} (r : RIdx M a) : JType M a :=
  ⟨r.2.choose, r.2.choose_spec.1⟩

variable (M) in
/-- A representative of an `L`-class. -/
noncomputable def lRep {a : M} (l : LIdx M a) : JType M a :=
  ⟨l.2.choose, l.2.choose_spec.1⟩

@[simp] lemma rIdx_rRep {a : M} (r : RIdx M a) : rIdx M (rRep M r) = r :=
  Subtype.ext r.2.choose_spec.2.symm

@[simp] lemma lIdx_lRep {a : M} (l : LIdx M a) : lIdx M (lRep M l) = l :=
  Subtype.ext l.2.choose_spec.2.symm

/-! ## The cell map -/

variable (M) in
/-- **The cell coordinates** of an element of the class. -/
def cellMap {a : M} (x : JType M a) : RIdx M a × LIdx M a := (rIdx M x, lIdx M x)

/-- Injective by `H`-triviality. -/
theorem cellMap_injective [IsAperiodicMonoid M] (a : M) :
    Function.Injective (cellMap M (a := a)) := by
  intro x y h
  have hr : REq x.1 y.1 := (rIdx_eq_iff x y).1 (congrArg Prod.fst h)
  have hl : LEq x.1 y.1 := (lIdx_eq_iff x y).1 (congrArg Prod.snd h)
  exact Subtype.ext (eq_of_rEq_of_lEq hr hl)

/-- **Surjective by `J = D`**: every `(R, L)` pair of the class is occupied. -/
theorem cellMap_surjective [IsAperiodicMonoid M] (a : M) :
    Function.Surjective (cellMap M (a := a)) := by
  rintro ⟨r, l⟩
  have hx : twoIdeal (rRep M r).1 = twoIdeal a := mem_jClass.1 (rRep M r).2
  have hy : twoIdeal (lRep M l).1 = twoIdeal a := mem_jClass.1 (lRep M l).2
  obtain ⟨z, hzr, hzl⟩ :=
    exists_rEq_lEq_of_twoIdeal_eq (x := (rRep M r).1) (y := (lRep M l).1)
      (hx.trans hy.symm)
  have hz : z ∈ jClass M a := by
    rw [mem_jClass, ← hx]
    exact (twoIdeal_eq_of_rEq hzr).symm
  refine ⟨⟨z, hz⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · rw [← rIdx_rRep r]
    exact ((rIdx_eq_iff _ _).2 (rEq_symm hzr))
  · rw [← lIdx_lRep l]
    exact ((lIdx_eq_iff _ _).2 hzl)

variable (M) in
/-- **The cells identify the `J`-class with `R × L`** — the second
regularity fact the construction needs, and `ReesBlock`'s `I × Λ`. -/
noncomputable def cellEquiv [IsAperiodicMonoid M] (a : M) :
    JType M a ≃ RIdx M a × LIdx M a :=
  Equiv.ofBijective _ ⟨cellMap_injective a, cellMap_surjective a⟩

/-- **The apex charge's counting half**: `|J| = |I|·|Λ|`.  With
`ReesBlock.rank_sandwich_sq_le` this is `d² ≤ |J|`. -/
theorem card_jClass_eq [IsAperiodicMonoid M] (a : M) :
    (jClass M a).card = Fintype.card (RIdx M a) * Fintype.card (LIdx M a) := by
  rw [← Fintype.card_coe, Fintype.card_congr (cellEquiv M a), Fintype.card_prod]

/-! ## The sandwich, and the two regularity facts -/

variable (M) in
/-- **The sandwich entry**: whether an element of `L`-class `l` times an element
of `R`-class `i` stays in the class.  Read on representatives, and well defined
by `sandwich_eq_true_iff` below. -/
noncomputable def sandwichBool {a : M} (l : LIdx M a) (i : RIdx M a) : Bool :=
  decide (twoIdeal ((lRep M l).1 * (rRep M i).1) = twoIdeal a)

/-- **The sandwich is well defined**, and says what it should: the entry at the
`L`-class of `x` and the `R`-class of `y` records whether `x·y` stays in the
class, for *every* pair of representatives. -/
theorem sandwich_eq_true_iff {a : M} (x y : JType M a) :
    sandwichBool M (lIdx M x) (rIdx M y) = true
      ↔ twoIdeal (x.1 * y.1) = twoIdeal a := by
  have hl : LEq (lRep M (lIdx M x)).1 x.1 := (lIdx_eq_iff _ _).1 (lIdx_lRep _)
  have hr : REq (rRep M (rIdx M y)).1 y.1 := (rIdx_eq_iff _ _).1 (rIdx_rRep _)
  simp only [sandwichBool, decide_eq_true_eq]
  rw [twoIdeal_mul_congr_left hl, twoIdeal_mul_congr_right hr]

/-- **No zero row.**  Every `L`-class of a regular class has a partner: the
idempotent `z·x` that regularity supplies is in the class, and `x·(z·x) = x`
stays in it. -/
theorem exists_sandwich_row [IsAperiodicMonoid M] {a : M} (hreg : IsRegularClass a)
    (l : LIdx M a) : ∃ i : RIdx M a, sandwichBool M l i = true := by
  set x : JType M a := lRep M l with hx
  have hxJ : twoIdeal x.1 = twoIdeal a := mem_jClass.1 x.2
  obtain ⟨z, hz⟩ := isRegularClass_iff_forall.1 hreg x.1 hxJ
  have hfix : x.1 * (z * x.1) = x.1 := by rw [← mul_assoc]; exact hz
  have hmem : z * x.1 ∈ jClass M a := by
    rw [mem_jClass, ← hxJ]
    refine Finset.Subset.antisymm
      (twoIdeal_subset_of_lLe (lLe_iff_exists.2 ⟨z, rfl⟩))
      (twoIdeal_subset_of_lLe (lLe_iff_exists.2 ⟨x.1, hfix⟩))
  refine ⟨rIdx M ⟨z * x.1, hmem⟩, ?_⟩
  rw [← lIdx_lRep l, ← hx]
  exact (sandwich_eq_true_iff x ⟨z * x.1, hmem⟩).2 (by rw [hfix]; exact hxJ)

/-- **No zero column.**  Symmetrically, with the idempotent `y·w`. -/
theorem exists_sandwich_col [IsAperiodicMonoid M] {a : M} (hreg : IsRegularClass a)
    (i : RIdx M a) : ∃ l : LIdx M a, sandwichBool M l i = true := by
  set y : JType M a := rRep M i with hy
  have hyJ : twoIdeal y.1 = twoIdeal a := mem_jClass.1 y.2
  obtain ⟨w, hw⟩ := isRegularClass_iff_forall.1 hreg y.1 hyJ
  have hfix : (y.1 * w) * y.1 = y.1 := hw
  have hmem : y.1 * w ∈ jClass M a := by
    rw [mem_jClass, ← hyJ]
    refine Finset.Subset.antisymm
      (twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨w, rfl⟩))
      (twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨y.1, hfix⟩))
  refine ⟨lIdx M ⟨y.1 * w, hmem⟩, ?_⟩
  rw [← rIdx_rRep i, ← hy]
  exact (sandwich_eq_true_iff ⟨y.1 * w, hmem⟩ y).2 (by rw [hfix]; exact hyJ)

/-! ## The Rees multiplication law

Cell coordinates and a sandwich are not yet a Rees 0-matrix semigroup; what
makes the identification true is how the product behaves.  Both halves of
`(i,λ)(j,μ) = (i,μ) if P λ j, else 0`:

* a product that stays in the class keeps the **left** factor's `R`-class and
  the **right** factor's `L`-class — pure stability again, since the product is
  below each factor on the appropriate side and the class is the same;
* a product at a **false** sandwich entry drops *strictly* below the class.

These are the local laws the row/column matrix action consumes.  A bundled
semigroup equivalence with `ReesZero` would add nothing the global action needs. -/

/-- **A surviving product keeps the left factor's `R`-class.** -/
theorem rIdx_mul [IsAperiodicMonoid M] {a : M} (x y : JType M a)
    (h : twoIdeal (x.1 * y.1) = twoIdeal a) :
    rIdx M (⟨x.1 * y.1, mem_jClass.2 h⟩ : JType M a) = rIdx M x :=
  (rIdx_eq_iff _ _).2 (rEq_of_twoIdeal_eq_of_rLe
    (h.trans (mem_jClass.1 x.2).symm) (rLe_iff_exists.2 ⟨y.1, rfl⟩))

/-- **A surviving product keeps the right factor's `L`-class.** -/
theorem lIdx_mul [IsAperiodicMonoid M] {a : M} (x y : JType M a)
    (h : twoIdeal (x.1 * y.1) = twoIdeal a) :
    lIdx M (⟨x.1 * y.1, mem_jClass.2 h⟩ : JType M a) = lIdx M y :=
  (lIdx_eq_iff _ _).2 (lEq_of_twoIdeal_eq_of_lLe
    (h.trans (mem_jClass.1 y.2).symm) (lLe_iff_exists.2 ⟨x.1, rfl⟩))

/-- **A product always stays inside the class's ideal.** -/
lemma twoIdeal_mul_subset {a : M} (x y : JType M a) :
    twoIdeal (x.1 * y.1) ⊆ twoIdeal a := by
  rw [← mem_jClass.1 x.2]
  exact twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨y.1, rfl⟩)

/-- **A false sandwich entry is a strict drop.**  This is the `0` of the Rees
product, and it is what makes the block's zero the class's *boundary* rather
than an adjoined symbol. -/
theorem twoIdeal_mul_ssubset {a : M} (x y : JType M a)
    (h : sandwichBool M (lIdx M x) (rIdx M y) = false) :
    twoIdeal (x.1 * y.1) ⊂ twoIdeal a := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨twoIdeal_mul_subset x y, fun hc => ?_⟩
  rw [(sandwich_eq_true_iff x y).2 hc] at h
  exact Bool.noConfusion h

end PrincipalFactor

end MonoidProduct
