import MonoidProduct.Aperiodic.CubeRoot.Basic
import MonoidProduct.Aperiodic.CubeRoot.RadicalStep
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The two-sided kernel category, and local thinness

The paper's square-zero product lift (`lem:ags-square-zero-lift`), formalized
in this order: the endpoint first, then the category, then the one algebraic fact the
category needs, and only then the dyadic compiler that consumes them.

* **The endpoint, frozen** (`LiftsWordProd`).  Both sides are
  `HasWordProdDualPoly` — alphabet-uniform *and* horizon-uniform — so the lift
  composes with the fixed-apex peel (`FixedApex.lean`, `ApexAdapter.lean`)
  with no adapter in between;
* **The category** (`SameArrow`).  Objects are pairs `(p, q)` of context
  images; two segment products are the same arrow at `(p, q)` when they agree
  in *every* compatible surrounding context.  That is precisely the
  identification that licenses substituting one segment inside an arbitrary
  word, which is the only thing the compiler ever does with an arrow.  It is an
  equivalence, it whiskers on both sides, and it composes;
* **The interface** (`LocallyThinKernel`).  Loops are identities — and that is
  the *whole* of it.  Nothing about rings, ideals or characteristic survives
  past this line, and the identity fibre is not a second assumption: it is
  `LocallyThinKernel.fibre_one`, derived below;
* **The algebra** (`locallyThinKernel_of_squareZero`).  A square-zero kernel
  satisfies the interface.  The loop argument is
  `RadicalStep.mul_pow_mul_sub_eq_of_mem` — the defect is linear in the
  exponent — plus coincident powers.

**Characteristic zero is not needed for local thinness.**  The paper takes
two coincident powers `ℓ₁ < ℓ₂` out of finiteness and cancels `(ℓ₂-ℓ₁)·δ = 0`
in a rational algebra.  Aperiodicity of `S` gives *consecutive* coincident
powers, `s^N = s^(N+1)`, so the multiplier is `1` and no cancellation is
required.  `SquareZeroKernel` accordingly asks for no `ℚ`-algebra structure,
and the calibration in `LocallyThinCalibration.lean` runs in `ZMod 4`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace LocallyThin

/-! ## The endpoint, frozen -/

section Endpoint

/-- The square-zero lift's cost coefficient.  Signature frozen — horizon, a
common size bound for the two monoids, and the image monoid's constant — with
the body provisional in the sense `apexStep` and `cubeRootFactor` already are:
downstream statements quote the name, and the dyadic recursion below
fixes the exponents. -/
noncomputable def thinStep (n₀ N : ℕ) (D : ℝ) : ℝ :=
  ((N : ℝ) + 1) ^ 4 * ((Nat.clog 2 (n₀ + 2) : ℝ) + 2) ^ 2 * (D + 1)

lemma thinStep_nonneg (n₀ N : ℕ) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ thinStep n₀ N D := by
  have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (Nat.clog 2 (n₀ + 2) : ℝ) := Nat.cast_nonneg _
  simp only [thinStep]
  positivity

lemma one_le_thinStep (n₀ N : ℕ) {D : ℝ} (hD : 0 ≤ D) : 1 ≤ thinStep n₀ N D := by
  have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (Nat.clog 2 (n₀ + 2) : ℝ) := Nat.cast_nonneg _
  have h3 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
  have h4 : (1 : ℝ) ≤ ((Nat.clog 2 (n₀ + 2) : ℝ) + 2) ^ 2 := one_le_pow₀ (by linarith)
  have hab : (1 : ℝ) * 1
      ≤ ((N : ℝ) + 1) ^ 4 * ((Nat.clog 2 (n₀ + 2) : ℝ) + 2) ^ 2 :=
    mul_le_mul h3 h4 zero_le_one (by positivity)
  rw [mul_one] at hab
  have hc : (1 : ℝ) ≤ D + 1 := by linarith
  have hfin := mul_le_mul hab hc zero_le_one (by positivity)
  simp only [thinStep]
  simpa using hfin

/-- **The coefficient factors through its cost slot**:
`thinStep n₀ N D = thinStep n₀ N 0 · (D + 1)`.  This is the vocabulary form the
radical tower's closed-form majorant uses, so no consumer unfolds the body. -/
lemma thinStep_eq_mul (n₀ N : ℕ) (D : ℝ) :
    thinStep n₀ N D = thinStep n₀ N 0 * (D + 1) := by
  simp only [thinStep]
  ring

/-- Monotonicity in the size bound and the cost. -/
lemma thinStep_mono (n₀ : ℕ) {N N' : ℕ} (hN : N ≤ N') {D D' : ℝ} (hD0 : 0 ≤ D)
    (hD : D ≤ D') : thinStep n₀ N D ≤ thinStep n₀ N' D' := by
  have hN' : ((N : ℝ)) ≤ (N' : ℝ) := Nat.cast_le.2 hN
  have h2 : (0 : ℝ) ≤ (Nat.clog 2 (n₀ + 2) : ℝ) := Nat.cast_nonneg _
  simp only [thinStep]
  gcongr

/-- **The endpoint of this file.**  A quotient with square-zero
kernel lifts the word-product contract from the image monoid to the source
monoid — in `HasWordProdDualPoly` form on *both* sides, so alphabet uniformity
and horizon uniformity are preserved rather than re-derived. -/
def LiftsWordProd (S T : Type) [Monoid S] [Fintype S] [DecidableEq S]
    [Monoid T] [Fintype T] [DecidableEq T] (n₀ : ℕ) (D : ℝ) : Prop :=
  HasWordProdDualPoly T n₀ D →
    HasWordProdDualPoly S n₀
      (thinStep n₀ (max (Fintype.card S) (Fintype.card T)) D)

end Endpoint

/-! ## The two-sided kernel category -/

section Category

variable {S T : Type} [Monoid S] [Monoid T] (φ : S →* T)

/-- **The typed contextual congruence.**  Two segment products are the same
arrow at `(p, q)` when they agree in every compatible surrounding context.

Note what is deliberately *not* required: equal `φ`-images.  A loop at `(p, q)`
need not have `φ s = 1` — only `p · φ s = p` and `φ s · q = q` — and the whole
content of local thinness is that such an `s` is nevertheless the identity
arrow.  Building the image into the relation would make the statement true by
fiat and useless. -/
def SameArrow (p q : T) (s s' : S) : Prop :=
  ∀ x y : S, φ x = p → φ y = q → x * s * y = x * s' * y

/-- **A loop** at `(p, q)`: a segment whose arrow returns to its own object. -/
def IsLoop (p q : T) (s : S) : Prop := p * φ s = p ∧ φ s * q = q

variable {φ}

@[refl] theorem SameArrow.refl (p q : T) (s : S) : SameArrow φ p q s s :=
  fun _ _ _ _ => rfl

theorem SameArrow.symm {p q : T} {s s' : S} (h : SameArrow φ p q s s') :
    SameArrow φ p q s' s := fun x y hx hy => (h x y hx hy).symm

theorem SameArrow.trans {p q : T} {s s' s'' : S} (h : SameArrow φ p q s s')
    (h' : SameArrow φ p q s' s'') : SameArrow φ p q s s'' :=
  fun x y hx hy => (h x y hx hy).trans (h' x y hx hy)

/-- The congruence is an equivalence at each object. -/
theorem sameArrow_equivalence (p q : T) : Equivalence (SameArrow φ p q) :=
  ⟨fun s => SameArrow.refl p q s, SameArrow.symm, SameArrow.trans⟩

/-- **Substitution.**  `SameArrow` read as a rewriting rule: an identified
segment may be replaced inside any compatible surrounding word.  This is the
only use the compiler makes of an arrow. -/
theorem SameArrow.subst {p q : T} {s s' : S} (h : SameArrow φ p q s s')
    {x y : S} (hx : φ x = p) (hy : φ y = q) : x * s * y = x * s' * y :=
  h x y hx hy

/-- **Left whiskering**: absorbing a prefix into the context moves the object,
not the identification. -/
theorem SameArrow.whiskerLeft {p q : T} (a : S) {s s' : S}
    (h : SameArrow φ (p * φ a) q s s') : SameArrow φ p q (a * s) (a * s') := by
  intro x y hx hy
  have hxa : φ (x * a) = p * φ a := by rw [map_mul, hx]
  have hstep := h (x * a) y hxa hy
  simp only [mul_assoc] at hstep ⊢
  exact hstep

/-- **Right whiskering.** -/
theorem SameArrow.whiskerRight {p q : T} (b : S) {s s' : S}
    (h : SameArrow φ p (φ b * q) s s') : SameArrow φ p q (s * b) (s' * b) := by
  intro x y hx hy
  have hby : φ (b * y) = φ b * q := by rw [map_mul, hy]
  have hstep := h x (b * y) hx hby
  simp only [mul_assoc] at hstep ⊢
  exact hstep

/-- **Composition.**  Arrows compose, with the types threading through the
image of the *second* segment — which is where the two-sidedness of the
category is doing its work. -/
theorem SameArrow.comp {p q : T} {s₁ s₁' s₂ s₂' : S}
    (h₁ : SameArrow φ p (φ s₂' * q) s₁ s₁')
    (h₂ : SameArrow φ (p * φ s₁) q s₂ s₂') :
    SameArrow φ p q (s₁ * s₂) (s₁' * s₂') := by
  intro x y hx hy
  have hxs : φ (x * s₁) = p * φ s₁ := by rw [map_mul, hx]
  have hsy : φ (s₂' * y) = φ s₂' * q := by rw [map_mul, hy]
  have step₂ := h₂ (x * s₁) y hxs hy
  have step₁ := h₁ x (s₂' * y) hx hsy
  simp only [mul_assoc] at step₁ step₂ ⊢
  exact step₂.trans step₁

end Category

/-! ## The interface the compiler consumes -/

section Interface

variable {S T : Type} [Monoid S] [Monoid T]

/-- **Everything the dyadic compiler needs from the algebra**, and it is a single fact:
every local loop is the identity arrow, so a strongly connected component has
at most one arrow between a fixed pair of objects.  Nothing about rings, ideals
or characteristic survives past this structure.

The identity fibre is deliberately *not* a second field.  `φ s = 1` makes `s` a
loop at `(1, 1)`, so `loop_id` already gives `s = 1`
(`LocallyThinKernel.fibre_one`, proved once `eq_of_sameArrow_root` is
available).  Assuming it separately would have hidden that. -/
structure LocallyThinKernel (φ : S →* T) : Prop where
  /-- Every local loop is the identity arrow. -/
  loop_id : ∀ (p q : T) (s : S), IsLoop φ p q s → SameArrow φ p q s 1

end Interface

/-! ## Square-zero kernels are locally thin -/

section SquareZero

variable {A : Type} [Ring A]
variable {S T : Type} [Monoid S] [IsAperiodicMonoid S] [Monoid T]

/-- **The algebraic input.**  `S` sits faithfully in a ring and `φ`-equal
elements differ by an element of a square-zero two-sided ideal.

The fibre condition is deliberately one-directional — `φ`-equal *implies* the
difference is in the kernel — because that is the only direction the proofs
below use, and asking for the converse would exclude instances for no gain. -/
structure SquareZeroKernel (φ : S →* T) (emb : S →* A) (J : Ideal A) : Prop where
  /-- The kernel is a two-sided ideal. -/
  twoSided : J.IsTwoSided
  /-- And square-zero. -/
  sq_zero : ∀ a ∈ J, ∀ b ∈ J, a * b = 0
  /-- The representation is faithful. -/
  emb_inj : Function.Injective emb
  /-- `φ`-equal elements differ by an element of the kernel. -/
  fibre : ∀ s s' : S, φ s = φ s' → emb s - emb s' ∈ J

variable {φ : S →* T} {emb : S →* A} {J : Ideal A}

/-- **Every local loop is the identity** — the heart of this file.

Three steps.  The contextual loop formula makes the loop's defect linear in the
exponent; aperiodicity supplies *consecutive* coincident powers `s^N = s^(N+1)`;
subtracting the two instances leaves the defect itself, with multiplier `1`.
That last point is why no characteristic hypothesis appears. -/
theorem loop_id_of_squareZero (κ : SquareZeroKernel φ emb J)
    (p q : T) (s : S) (hs : IsLoop φ p q s) : SameArrow φ p q s 1 := by
  have := κ.twoSided
  intro x y hx hy
  refine κ.emb_inj ?_
  have hxs : emb x * (emb s - 1) ∈ J := by
    have himg : φ (x * s) = φ x := by rw [map_mul, hx, hs.1]
    have h := κ.fibre (x * s) x himg
    rw [map_mul] at h
    simpa [mul_sub, mul_one] using h
  have hsy : (emb s - 1) * emb y ∈ J := by
    have himg : φ (s * y) = φ y := by rw [map_mul, hy, hs.2]
    have h := κ.fibre (s * y) y himg
    rw [map_mul] at h
    simpa [sub_mul, one_mul] using h
  obtain ⟨N, hN, hstab⟩ := IsAperiodicMonoid.stabilizes s
  have hpow : emb s ^ N = emb s ^ (N + 1) := by
    rw [← map_pow, ← map_pow, hstab]
  have e1 := mul_pow_mul_sub_eq_of_mem κ.sq_zero hxs hsy N
  have e2 := mul_pow_mul_sub_eq_of_mem κ.sq_zero hxs hsy (N + 1)
  rw [← hpow] at e2
  have hEq : (N : ℤ) • (emb x * (emb s - 1) * emb y)
      = ((N + 1 : ℕ) : ℤ) • (emb x * (emb s - 1) * emb y) := e1.symm.trans e2
  have hsplit : ((N + 1 : ℕ) : ℤ) • (emb x * (emb s - 1) * emb y)
      = (N : ℤ) • (emb x * (emb s - 1) * emb y) + emb x * (emb s - 1) * emb y := by
    push_cast
    rw [add_smul, one_smul]
  rw [hsplit] at hEq
  have hcancel : (N : ℤ) • (emb x * (emb s - 1) * emb y)
      + emb x * (emb s - 1) * emb y
      = (N : ℤ) • (emb x * (emb s - 1) * emb y) + 0 := by
    rw [add_zero]
    exact hEq.symm
  have hδ : emb x * (emb s - 1) * emb y = 0 := add_left_cancel hcancel
  have hexp : emb x * (emb s - 1) * emb y
      = emb x * emb s * emb y - emb x * emb y := by noncomm_ring
  rw [hexp] at hδ
  have hgoal : emb x * emb s * emb y = emb x * emb y := sub_eq_zero.mp hδ
  simpa [map_mul] using hgoal

/-- **The identity fibre is a singleton — the paper's own argument.**
`φ s = 1` puts `emb s = 1 + k` with `k` square-zero, hence a unit with inverse
`1 - k`; aperiodicity stabilises a power, and multiplying the stability
identity by that inverse collapses `s` to `1`.

This is **not** load-bearing: `LocallyThinKernel.fibre_one` derives the same
conclusion from `loop_id` alone, with no algebra at all.  It is kept as the
comparison point — it is the step the paper performs by hand, and having
both makes the redundancy checkable rather than asserted. -/
theorem fibre_one_of_squareZero (κ : SquareZeroKernel φ emb J)
    (s : S) (h : φ s = 1) : s = 1 := by
  have := κ.twoSided
  refine κ.emb_inj ?_
  rw [map_one]
  set k : A := emb s - 1 with hkdef
  have hkJ : k ∈ J := by
    have hfib := κ.fibre s 1 (by rw [h, map_one])
    rwa [map_one] at hfib
  have hk2 : k * k = 0 := κ.sq_zero k hkJ k hkJ
  have hemb : emb s = 1 + k := by rw [hkdef]; noncomm_ring
  have hinv : (1 - k) * (1 + k) = 1 := by
    have hx : (1 - k) * (1 + k) = 1 - k * k := by noncomm_ring
    rw [hx, hk2, sub_zero]
  have hcomm : Commute (1 - k) (1 + k) := by
    change (1 - k) * (1 + k) = (1 + k) * (1 - k)
    noncomm_ring
  obtain ⟨N, hN, hstab⟩ := IsAperiodicMonoid.stabilizes s
  have hkey : (1 - k) ^ N * emb s ^ N = 1 := by
    rw [hemb, ← hcomm.mul_pow, hinv, one_pow]
  have hpow : emb s ^ N = emb s ^ N * emb s := by
    rw [← pow_succ, ← map_pow, ← map_pow, hstab]
  calc emb s = 1 * emb s := (one_mul _).symm
    _ = ((1 - k) ^ N * emb s ^ N) * emb s := by rw [hkey]
    _ = (1 - k) ^ N * (emb s ^ N * emb s) := by rw [mul_assoc]
    _ = (1 - k) ^ N * emb s ^ N := by rw [← hpow]
    _ = 1 := hkey

/-- **Square-zero kernels are locally thin.**  The dyadic compiler depends on
this and on nothing else about the algebra. -/
theorem locallyThinKernel_of_squareZero (κ : SquareZeroKernel φ emb J) :
    LocallyThinKernel φ :=
  ⟨loop_id_of_squareZero κ⟩

end SquareZero

/-! ## Arrows, reachability, and thinness

`SameArrow` says when two segments are the same arrow; this
section says what the arrows *are*, when a component forces two of them to
coincide, and why the arrow at the root is the product itself. -/

section Arrows

variable {S T : Type} [Monoid S] [Monoid T] (φ : S →* T)

/-- **A typed arrow** of the two-sided kernel category: `s` carries the object
`o` to the object `o'`.  The left context grows by the segment's image and the
right context shrinks by it — the two halves of the paper's
`(p, q) → (p φ(s), q')` with `φ(s) q' = q`. -/
structure IsArrow (o o' : T × T) (s : S) : Prop where
  /-- The left context grows. -/
  left : o.1 * φ s = o'.1
  /-- The right context shrinks. -/
  right : φ s * o'.2 = o.2

/-- **Reachability**: some segment carries `o` to `o'`. -/
def Reach (o o' : T × T) : Prop := ∃ s : S, IsArrow φ o o' s

/-- **Lying in one strongly connected component.** -/
def SameComp (o o' : T × T) : Prop := Reach φ o o' ∧ Reach φ o' o

variable {φ}

theorem isArrow_one (o : T × T) : IsArrow φ o o 1 :=
  ⟨by rw [map_one, mul_one], by rw [map_one, one_mul]⟩

theorem IsArrow.comp {o o' o'' : T × T} {u v : S}
    (hu : IsArrow φ o o' u) (hv : IsArrow φ o' o'' v) : IsArrow φ o o'' (u * v) :=
  ⟨by rw [map_mul, ← mul_assoc, hu.left, hv.left],
   by rw [map_mul, mul_assoc, hv.right, hu.right]⟩

/-- A loop is exactly an arrow from an object to itself. -/
theorem IsArrow.isLoop {o : T × T} {s : S} (h : IsArrow φ o o s) :
    IsLoop φ o.1 o.2 s := ⟨h.left, h.right⟩

@[refl] theorem Reach.refl (o : T × T) : Reach φ o o := ⟨1, isArrow_one o⟩

theorem Reach.trans {o o' o'' : T × T} (h : Reach φ o o') (h' : Reach φ o' o'') :
    Reach φ o o'' := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  exact ⟨u * v, hu.comp hv⟩

@[refl] theorem SameComp.refl (o : T × T) : SameComp φ o o :=
  ⟨Reach.refl o, Reach.refl o⟩

theorem SameComp.symm {o o' : T × T} (h : SameComp φ o o') : SameComp φ o' o :=
  ⟨h.2, h.1⟩

theorem SameComp.trans {o o' o'' : T × T} (h : SameComp φ o o')
    (h' : SameComp φ o' o'') : SameComp φ o o'' :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- **Thinness.**  Two arrows between the same pair of objects agree as soon as
*some* arrow returns — which is exactly what lying in one strongly connected
component provides.  This is the only consequence of `loop_id` the compiler
uses: inside a component an arrow is determined by its endpoints, so it can be
tabled and no query is needed to find it.

The argument is the categorical one, `u = u∘(w∘v) = (u∘w)∘v = v`, and it needs
the loop identity at **both** objects — which is why `LocallyThinKernel`
quantifies over all of them rather than over one. -/
theorem SameArrow.of_thin (h : LocallyThinKernel φ) {o o' : T × T} {u v w : S}
    (hu : IsArrow φ o o' u) (hv : IsArrow φ o o' v) (hw : IsArrow φ o' o w) :
    SameArrow φ o.1 o'.2 u v := by
  have hloop₁ : SameArrow φ o.1 o.2 (u * w) 1 :=
    h.loop_id o.1 o.2 (u * w) (hu.comp hw).isLoop
  have hloop₂ : SameArrow φ o'.1 o'.2 (w * v) 1 :=
    h.loop_id o'.1 o'.2 (w * v) (hw.comp hv).isLoop
  intro y z hy hz
  have hyu : φ (y * u) = o'.1 := by rw [map_mul, hy, hu.left]
  have hvz : φ (v * z) = o.2 := by rw [map_mul, hz, hv.right]
  have e2 := hloop₂ (y * u) z hyu hz
  have e1 := hloop₁ y (v * z) hy hvz
  simp only [mul_one, mul_assoc] at e1 e2 ⊢
  exact e2.symm.trans e1

/-- **At the root the arrow *is* the product.**  The root object is `(1, 1)` —
empty prefix, empty suffix — and `1` is a compatible lift of `1` on both sides,
so identified root arrows are equal elements of `S`.

With `SameArrow` quantified over **all** compatible lifts, the lift `1` is
always available — which is why this needs no hypothesis whatever, and why the
identity fibre is a *consequence* rather than an assumption
(`LocallyThinKernel.fibre_one`, immediately below). -/
theorem eq_of_sameArrow_root {u v : S} (h : SameArrow φ 1 1 u v) : u = v := by
  have h1 := h 1 1 (map_one φ) (map_one φ)
  simpa using h1

/-- **The identity fibre is a singleton — derived, not assumed.**  `φ s = 1`
makes `s` a loop at `(1, 1)`, so `loop_id` identifies it with the identity
arrow, and at the root an identified arrow *is* the element.

So the paper's separate square-zero argument for `φ⁻¹(1) = {1}` is not an
independent hypothesis of the compiler: local thinness already contains it.
`fibre_one_of_squareZero` is retained upstream only as the comparison. -/
theorem LocallyThinKernel.fibre_one (h : LocallyThinKernel φ) :
    ∀ s : S, φ s = 1 → s = 1 := by
  intro s hs
  exact eq_of_sameArrow_root
    (h.loop_id 1 1 s ⟨by rw [hs, mul_one], by rw [hs, mul_one]⟩)

end Arrows

/-! ## The cut path -/

section CutPath

variable {S T : Type} [Monoid S] [Monoid T] (φ : S →* T) {n : ℕ} (x : Fin n → S)

/-- The object at cut `i`: the image of the prefix and the image of the
suffix. -/
def cutObj (i : ℕ) : T × T := (φ (rangeProd x 0 i), φ (rangeProd x i n))

/-- The segment spanning two cuts. -/
def segment (i j : ℕ) : S := rangeProd x i j

@[simp] lemma cutObj_zero_fst : (cutObj φ x 0).1 = 1 := by
  simp [cutObj]

@[simp] lemma cutObj_last_snd : (cutObj φ x n).2 = 1 := by
  simp [cutObj]

/-- **The cuts form a path**: every segment is an arrow between the cuts it
spans.  Both halves are one application of `rangeProd_split`. -/
theorem isArrow_segment {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    IsArrow φ (cutObj φ x i) (cutObj φ x j) (segment x i j) := by
  constructor
  · simp only [cutObj, segment]
    rw [← map_mul, rangeProd_split x (Nat.zero_le i) hij]
  · simp only [cutObj, segment]
    rw [← map_mul, rangeProd_split x hij hjn]

theorem reach_cutObj {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    Reach φ (cutObj φ x i) (cutObj φ x j) :=
  ⟨segment x i j, isArrow_segment φ x hij hjn⟩

/-- **The condensation is acyclic**, in the form the recursion uses: the
components along the cut path are *intervals*.  If two cuts share a component
then so does everything between them, because the return arrow of the outer
pair composes with the forward arrow of the inner one. -/
theorem sameComp_of_between {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hkn : k ≤ n)
    (h : SameComp φ (cutObj φ x i) (cutObj φ x k)) :
    SameComp φ (cutObj φ x i) (cutObj φ x j) :=
  ⟨reach_cutObj φ x hij (le_trans hjk hkn),
   (reach_cutObj φ x hjk hkn).trans h.2⟩

/-- **The whole product is the tabled arrow**, when the two ends of the word
lie in one component: thinness pins the arrow, and at the root an identified
arrow is the element itself.  This is the base case of the dyadic recursion, and the case in
which the compiler asks no query at all. -/
theorem rangeProd_eq_of_sameComp (h : LocallyThinKernel φ)
    (hcomp : SameComp φ (cutObj φ x 0) (cutObj φ x n))
    {v : S} (hv : IsArrow φ (cutObj φ x 0) (cutObj φ x n) v) :
    rangeProd x 0 n = v := by
  obtain ⟨w, hw⟩ := hcomp.2
  have hthin :=
    SameArrow.of_thin h (isArrow_segment φ x (Nat.zero_le n) le_rfl) hv hw
  rw [cutObj_zero_fst, cutObj_last_snd] at hthin
  exact eq_of_sameArrow_root hthin

end CutPath

/-! ## Counting the component changes

The combinatorial core of the dyadic count.  Because components along the path are intervals,
distinct change points sit in distinct components — so there are fewer of them
than there are objects, and the last component is never one of theirs. -/

section Counting

variable {S T : Type} [Monoid S] [Monoid T] [Fintype T] [DecidableEq T]
  (φ : S →* T) {n : ℕ} (x : Fin n → S)

open Classical in
/-- The cuts at which the path leaves its component. -/
noncomputable def changeSet : Finset ℕ :=
  (Finset.range n).filter fun i => ¬ SameComp φ (cutObj φ x i) (cutObj φ x (i + 1))

lemma mem_changeSet {i : ℕ} :
    i ∈ changeSet φ x ↔ i < n ∧ ¬ SameComp φ (cutObj φ x i) (cutObj φ x (i + 1)) := by
  simp [changeSet]

/-- A change point is in a different component from every later cut it could be
compared with — in particular from the final one. -/
lemma not_sameComp_of_mem_changeSet {i j : ℕ} (hi : i ∈ changeSet φ x)
    (hij : i + 1 ≤ j) (hjn : j ≤ n) :
    ¬ SameComp φ (cutObj φ x i) (cutObj φ x j) := by
  intro hc
  exact ((mem_changeSet φ x).1 hi).2
    (sameComp_of_between φ x (Nat.le_succ i) hij hjn hc)

/-- **The component changes at most `|T|² - 1` times.**  The change points
inject into the objects, missing the final one. -/
theorem changeSet_card_le :
    (changeSet φ x).card ≤ Fintype.card (T × T) - 1 := by
  have hmaps : ∀ i ∈ changeSet φ x,
      cutObj φ x i ∈ (Finset.univ : Finset (T × T)).erase (cutObj φ x n) := by
    intro i hi
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    intro heq
    exact not_sameComp_of_mem_changeSet φ x hi
      (((mem_changeSet φ x).1 hi).1) le_rfl (heq ▸ SameComp.refl _)
  have hinj : Set.InjOn (cutObj φ x) (changeSet φ x) := by
    intro i hi j hj heq
    by_contra hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact not_sameComp_of_mem_changeSet φ x hi hlt
        (le_of_lt ((mem_changeSet φ x).1 hj).1) (heq ▸ SameComp.refl _)
    · have hlt' : j < i := lt_of_le_of_ne hge (Ne.symm hne)
      exact not_sameComp_of_mem_changeSet φ x hj hlt'
        (le_of_lt ((mem_changeSet φ x).1 hi).1) (heq ▸ SameComp.refl _)
  calc (changeSet φ x).card
      ≤ ((Finset.univ : Finset (T × T)).erase (cutObj φ x n)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = Fintype.card (T × T) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-! ### The dyadic active-node count

A dyadic node is *active* — the recursion must descend into it rather than read
a tabled arrow — exactly when its interval straddles a change point.  Each
change point lies in one node per level, so the active nodes at a level are the
images of the change points and there are at most `|T|² - 1` of them; over
`L + 1` levels that is the paper's `N^{O(1)} L(n)^{O(1)}`. -/

/-- **A node is tabled exactly when it straddles no change.**  The interval
property, read as the recursion's decision procedure. -/
theorem sameComp_iff_no_change {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    SameComp φ (cutObj φ x a) (cutObj φ x b)
      ↔ ∀ i ∈ changeSet φ x, ¬ (a ≤ i ∧ i < b) := by
  constructor
  · intro hc i hi ⟨hai, hib⟩
    have h1 : SameComp φ (cutObj φ x a) (cutObj φ x i) :=
      sameComp_of_between φ x hai (le_of_lt hib) hbn hc
    have h2 : SameComp φ (cutObj φ x a) (cutObj φ x (i + 1)) :=
      sameComp_of_between φ x (by omega) (by omega) hbn hc
    exact ((mem_changeSet φ x).1 hi).2 (h1.symm.trans h2)
  · intro hno
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction d with
    | zero => simpa using SameComp.refl (cutObj φ x a)
    | succ d ih =>
        have hstep : SameComp φ (cutObj φ x (a + d)) (cutObj φ x (a + d + 1)) := by
          by_contra hcon
          exact hno (a + d) ((mem_changeSet φ x).2 ⟨by omega, hcon⟩) ⟨by omega, by omega⟩
        have hprev : SameComp φ (cutObj φ x a) (cutObj φ x (a + d)) :=
          ih (by omega) (fun i hi hmem => hno i hi ⟨hmem.1, by omega⟩)
        exact (hprev.trans hstep).imp (fun h => h) (fun h => h) |>.imp
          (fun h => h) (fun h => h)

/-- Membership in a dyadic node is a division. -/
lemma mem_dyadic_iff {ℓ k i : ℕ} :
    (k * 2 ^ ℓ ≤ i ∧ i < (k + 1) * 2 ^ ℓ) ↔ i / 2 ^ ℓ = k := by
  have hp : 0 < 2 ^ ℓ := pow_pos (by norm_num) ℓ
  constructor
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 h2
  · rintro rfl
    refine ⟨Nat.div_mul_le_self i (2 ^ ℓ), ?_⟩
    have hdm := Nat.div_add_mod i (2 ^ ℓ)
    have hmod : i % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt i hp
    calc i = 2 ^ ℓ * (i / 2 ^ ℓ) + i % 2 ^ ℓ := hdm.symm
      _ < 2 ^ ℓ * (i / 2 ^ ℓ) + 2 ^ ℓ := by omega
      _ = (i / 2 ^ ℓ + 1) * 2 ^ ℓ := by ring

/-- The level-`ℓ` dyadic nodes the recursion must descend into. -/
noncomputable def activeNodes (ℓ : ℕ) : Finset ℕ :=
  (changeSet φ x).image (· / 2 ^ ℓ)

/-- **What `activeNodes` is**: a level-`ℓ` node is active exactly when it
contains a change point. -/
theorem mem_activeNodes_iff {ℓ k : ℕ} :
    k ∈ activeNodes φ x ℓ
      ↔ ∃ i ∈ changeSet φ x, k * 2 ^ ℓ ≤ i ∧ i < (k + 1) * 2 ^ ℓ := by
  simp only [activeNodes, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, mem_dyadic_iff.2 rfl⟩
  · rintro ⟨i, hi, hmem⟩
    exact ⟨i, hi, mem_dyadic_iff.1 hmem⟩

/-- **At most `|T|² - 1` active nodes per level**: each is the image of a change
point, and there are that few change points. -/
theorem activeNodes_card_le (ℓ : ℕ) :
    (activeNodes φ x ℓ).card ≤ Fintype.card (T × T) - 1 :=
  le_trans Finset.card_image_le (changeSet_card_le φ x)

/-- **The dyadic active-node count.**  Over `L + 1` levels the recursion
descends into at most `(L+1)(|T|² - 1)` nodes — the `N^{O(1)} L(n)^{O(1)}` of
the paper, with both exponents equal to one. -/
theorem sum_activeNodes_card_le (L : ℕ) :
    ∑ ℓ ∈ Finset.range (L + 1), (activeNodes φ x ℓ).card
      ≤ (L + 1) * (Fintype.card (T × T) - 1) := by
  calc ∑ ℓ ∈ Finset.range (L + 1), (activeNodes φ x ℓ).card
      ≤ ∑ _ℓ ∈ Finset.range (L + 1), (Fintype.card (T × T) - 1) :=
        Finset.sum_le_sum fun ℓ _ => activeNodes_card_le φ x ℓ
    _ = (L + 1) * (Fintype.card (T × T) - 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end Counting

end LocallyThin

end MonoidProduct
