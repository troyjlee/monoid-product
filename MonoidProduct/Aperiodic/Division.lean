import MonoidProduct.Aperiodic.EqProd
import QuantumQueryComplexity.HasDual
import MonoidProduct.UT.Upper
import MonoidProduct.Simon.Main
set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Division transports at the certificate level

`M ≺ S` — a subsemigroup `T ⊆ S` with a surjective homomorphism onto `M`,
split by a section — transports a product certificate for `S` to one for
`M` at a factor **two**: the letters lift through the section (free — the
section is a letter map, and the source certificate is uniform in the
letter alphabet), and the output projects through the extended
homomorphism (`HasDual.postcomp_of_determined`, the recorded factor-two
postcomposition).

This file holds the classical half of the division story:

* the extension lemmas hoisted from `Quantum/Division.lean`
  (they are pure monoid facts): `extendHom` and its
  action on ordered products, and the section identity
  `map_wordProd_section`;
* `hasDual_wordProd_of_section` — the generic certificate transport;
* `hasDual_wordProd_of_semigroupDivides_but` — instantiated at the
  `UT_k(𝔹)` certificate (`hasDual_wordProd_but`), `16·√(n·min{n,C(k,2)})`;
* `hasDual_wordProd_jtrivial` — with Simon's theorem discharged: every
  finite 𝓙-trivial monoid at `k = τ(M)`;
* `advPM_wordProd_le_of_jtrivial` — the previously missing classical
  `advPM` corollary.

The query-side division compilers (`Quantum/Division.lean`,
`Quantum/DivisionSemigroup.lean`) remain unchanged; the certificate route
feeds the single-extraction operational endpoints in
`Quantum/DivisionApplications.lean`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {M N : Type} [Monoid M] [Fintype M] [DecidableEq M]
  [Monoid N] [Fintype N] [DecidableEq N]

/-- The section identity at the level of whole words: lifting the letters and
projecting the product recovers the original product. -/
lemma map_wordProd_section (φ : N →* M) (ψ : M → N)
    (hsec : ∀ m, φ (ψ m) = m) {n : ℕ} (w : Fin n → M) :
    φ (wordProd (id : N → N) (fun j => ψ (w j))) = wordProd (id : M → M) w := by
  rw [wordProd, wordProd, map_orderedProd]
  exact congrArg orderedProd (funext fun j => hsec (w j))

section Subsemigroup

variable {S : Type} [Monoid S] [Fintype S] [DecidableEq S]

open scoped Classical in
/-- An arbitrary total extension of `φ` to `S`.  The junk value off `T` is
irrelevant: every *correct* product lies in `T`, and an outcome outside `T` is
one the algorithm already got wrong. -/
noncomputable def extendHom (T : Subsemigroup S) (φ : T →ₙ* M) : S → M :=
  fun s => if h : s ∈ T then φ ⟨s, h⟩ else 1

lemma extendHom_of_mem {T : Subsemigroup S} (φ : T →ₙ* M) {s : S}
    (h : s ∈ T) : extendHom T φ s = φ ⟨s, h⟩ := by
  classical
  rw [extendHom, dif_pos h]

/-- **A word of `T`-letters has its ordered product in `T`** — closure, on
nonempty prefixes.  (Nonemptiness is essential: the empty product is `1`,
which a subsemigroup need not contain.) -/
lemma rangeProd_mem_of_forall_mem (T : Subsemigroup S) {n : ℕ} (v : Fin n → S)
    (hv : ∀ i, v i ∈ T) :
    ∀ m : ℕ, 1 ≤ m → m ≤ n → rangeProd v 0 m ∈ T := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
      intro _ hmn
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [rangeProd_singleton _ (show 0 < n by omega)]
        exact hv _
      · rw [rangeProd_succ_right _ (Nat.zero_le m),
          padAt_of_lt _ (show m < n by omega)]
        exact mul_mem (ih hm0 (by omega)) (hv _)

/-- **On a word of `T`-letters the extension computes `φ` letterwise.** -/
lemma extendHom_rangeProd_of (T : Subsemigroup S) (φ : T →ₙ* M) {n : ℕ}
    (v : Fin n → S) (hv : ∀ i, v i ∈ T) (u : Fin n → M)
    (hu : ∀ i, φ ⟨v i, hv i⟩ = u i) :
    ∀ m : ℕ, 1 ≤ m → m ≤ n →
      extendHom T φ (rangeProd v 0 m) = rangeProd u 0 m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
      intro _ hmn
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [rangeProd_singleton _ (show 0 < n by omega),
          rangeProd_singleton _ (show 0 < n by omega),
          extendHom_of_mem φ (hv _)]
        exact hu _
      · have hA : rangeProd v 0 m ∈ T :=
          rangeProd_mem_of_forall_mem T v hv m hm0 (by omega)
        have hb : v ⟨m, by omega⟩ ∈ T := hv _
        rw [rangeProd_succ_right _ (Nat.zero_le m),
          padAt_of_lt _ (show m < n by omega),
          rangeProd_succ_right _ (Nat.zero_le m),
          padAt_of_lt _ (show m < n by omega),
          extendHom_of_mem φ (mul_mem hA hb),
          show (⟨rangeProd v 0 m * v ⟨m, by omega⟩, mul_mem hA hb⟩ : T)
            = (⟨_, hA⟩ : T) * ⟨_, hb⟩ from rfl, map_mul,
          ← extendHom_of_mem φ hA, ih hm0 (by omega)]
        congr 1
        exact hu _

/-- **The extension computes the `M`-product of a `T`-valued word.** -/
lemma extendHom_orderedProd (T : Subsemigroup S) (φ : T →ₙ* M) {n : ℕ}
    (hn : 1 ≤ n) (v : Fin n → S) (hv : ∀ i, v i ∈ T) (u : Fin n → M)
    (hu : ∀ i, φ ⟨v i, hv i⟩ = u i) :
    extendHom T φ (orderedProd v) = orderedProd u := by
  rw [orderedProd_eq_rangeProd, orderedProd_eq_rangeProd]
  exact extendHom_rangeProd_of T φ v hv u hu n hn (le_refl n)

/-- The word-level form, for a global section. -/
lemma extendHom_wordProd (T : Subsemigroup S) (φ : T →ₙ* M) (ψ : M → T)
    (hsec : ∀ m, φ (ψ m) = m) {n : ℕ} (hn : 1 ≤ n) (w : Fin n → M) :
    extendHom T φ (wordProd (id : S → S) (fun i => ((ψ (w i) : S))))
      = wordProd (id : M → M) w := by
  rw [wordProd, wordProd]
  exact extendHom_orderedProd T φ hn _ (fun i => (ψ (w i)).2) _
    fun i => hsec (w i)

/-! ## The certificate transport -/

/-- **Division transports a certificate at a factor two**: a dual for the
`S`-product read through the section's letters projects to a dual for the
`M`-product — `HasDual.postcomp_of_determined`, with the determination
supplied by `extendHom_wordProd`. -/
theorem hasDual_wordProd_of_section {n : ℕ} (hn : 1 ≤ n)
    (T : Subsemigroup S) (φ : T →ₙ* M) (ψ : M → T)
    (hsec : ∀ m, φ (ψ m) = m) {c : ℝ} (hc : 0 ≤ c)
    (h : HasDual (fun w : Fin n → M =>
      wordProd (fun m => ((ψ m : S))) w) c) :
    HasDual (fun w : Fin n → M => wordProd (id : M → M) w) (2 * c) := by
  refine HasDual.postcomp_of_determined hc h fun x y hxy => ?_
  have h1 := congrArg (extendHom T φ) hxy
  rwa [show wordProd (fun m : M => ((ψ m : S))) x
        = wordProd (id : S → S) (fun i => ((ψ (x i) : S))) from rfl,
    show wordProd (fun m : M => ((ψ m : S))) y
        = wordProd (id : S → S) (fun i => ((ψ (y i) : S))) from rfl,
    extendHom_wordProd T φ ψ hsec hn x,
    extendHom_wordProd T φ ψ hsec hn y] at h1

end Subsemigroup

/-! ## The `UT_k(𝔹)` instantiation and the 𝓙-trivial certificate -/

section But

variable {k n : ℕ}

/-- **The certificate for a divisor of `UT_k(𝔹)`, from a supplied
witness**: `HasDual (Prod_{M,n}) (16·√(n·min{n, C(k,2)}))` — the `UT`
scan dual lifted through the section's letters (free, since
`hasDual_wordProd_but` is uniform in the letter alphabet) and projected
at the factor two. -/
theorem hasDual_wordProd_of_but_division (hn : 1 ≤ n)
    (T : Subsemigroup (BUT k)) (φ : T →ₙ* M) (ψ : M → T)
    (hsec : ∀ m, φ (ψ m) = m) :
    HasDual (fun w : Fin n → M => wordProd (id : M → M) w)
      (16 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ))) := by
  have h := hasDual_wordProd_of_section hn T φ ψ hsec (by positivity)
    (hasDual_wordProd_but (letter := fun m : M => ((ψ m : BUT k))))
  rwa [show (16 : ℝ) * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ))
      = 2 * (8 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)))
    from by ring]

/-- **The certificate in the exact algebraic interface**: from
`SemigroupDivides M (BUT k)`, with the section extracted classically. -/
theorem hasDual_wordProd_of_semigroupDivides_but (hn : 1 ≤ n)
    (h : SemigroupDivides M (BUT k)) :
    HasDual (fun w : Fin n → M => wordProd (id : M → M) w)
      (16 * Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ))) := by
  obtain ⟨T, φ, ψ, hsec⟩ := h.exists_section
  exact hasDual_wordProd_of_but_division hn T φ ψ hsec

/-- **The unconditional 𝓙-trivial certificate** (Simon's theorem
discharged): every finite 𝓙-trivial monoid `M` has
`HasDual (Prod_{M,n}) (16·√(n·min{n, C(τ(M),2)}))`. -/
theorem hasDual_wordProd_jtrivial (hJ : IsJTrivialMonoid M) (hn : 1 ≤ n) :
    HasDual (fun w : Fin n → M => wordProd (id : M → M) w)
      (16 * Real.sqrt ((n : ℝ)
        * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))) :=
  hasDual_wordProd_of_semigroupDivides_but hn (semigroupDivides_but_tau hJ)

/-- **The 𝓙-trivial `advPM` bound** — the classical corollary the
query-side compiler never produced:
`ADV±(Prod_{M,n}) ≤ 16·√(n·min{n, C(τ(M),2)})`. -/
theorem advPM_wordProd_le_of_jtrivial (hJ : IsJTrivialMonoid M)
    (hn : 1 ≤ n) :
    advPM (fun w : Fin n → M => wordProd (id : M → M) w)
      ≤ 16 * Real.sqrt ((n : ℝ)
        * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ)) :=
  advPM_le_of_hasDual (by positivity) (hasDual_wordProd_jtrivial hJ hn)

end But

end MonoidProduct
