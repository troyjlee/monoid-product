import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Lattice.Nat
set_option linter.style.header false

/-!
# Equivalence under extensions and strong certificates

`monoid.tex`, section `sec:strong-certificates`: `def:extension-monoid` (the relation
`eq:certificate-equivalence`) and `def:strong-certificate` (the size
`eq:strong-certificate-size`).

Fix a function `f : Finset U → O` on the subsets of a universe `U`.

* `ExtensionEquiv f S T` is the paper's `S ∼_f T`: `f (S ∪ K) = f (T ∪ K)` for **every**
  extension `K ⊆ U`.  The extension may overlap `S` or `T`.  It is an equivalence relation
  (`extensionEquiv_equivalence`) and a congruence for union (`ExtensionEquiv.union`), and the
  empty extension shows `f S = f T` (`ExtensionEquiv.apply_eq`).  Equality `f S = f T` alone is
  weaker in general; it is equivalent when the value of a union is determined by the values of
  its parts (`extensionEquiv_iff_of_merge`).
* `IsStrongCertificate f C S`: `C ⊆ S` and `C ∼_f S`.  No monotonicity of `f` is assumed, and
  Boolean `f` are treated alike on yes- and no-instances.  Every set certifies itself
  (`isStrongCertificate_self`), a certificate certifies every set between it and `S` (the
  interval lemma `IsStrongCertificate.of_subset`), and a certificate for `f` is one for every
  function of the output of `f` (`IsStrongCertificate.postcomp`).
* `HasStrongCertificateBound f b`: every `S` has a strong certificate of at most `b` elements.
  `strongCertificateSize f` is the least such `b` (an `sInf` over `ℕ`, paralleling `breadth`).
  For finite `U` the defining set always contains `#U` (self-certification), so the infimum is
  attained (`hasStrongCertificateBound_strongCertificateSize`) and
  `strongCertificateSize_le_card` holds.
* `strongCertificateSize_eq_sup`: the least uniform bound is the paper's
  `b_f(U) = max_{S ⊆ U} min{|C| : C ⊆ S, C ∼_f S}`, with the inner minimum
  `minStrongCertificateSize f S`.
* `strongCertificateSize_eq_zero_iff`: size zero exactly for constant `f`.
-/

namespace MonoidProduct.Certificates

variable {U O O' : Type*} [DecidableEq U]

/-! ## Equivalence under extensions -/

/-- **Equivalence under extensions** (`eq:certificate-equivalence`): `S ∼_f T` when
`f (S ∪ K) = f (T ∪ K)` for every extension `K ⊆ U`.  The extension may overlap `S` or `T`. -/
def ExtensionEquiv (f : Finset U → O) (S T : Finset U) : Prop :=
  ∀ K : Finset U, f (S ∪ K) = f (T ∪ K)

namespace ExtensionEquiv

variable {f : Finset U → O} {S T R S' T' : Finset U}

protected theorem refl (f : Finset U → O) (S : Finset U) : ExtensionEquiv f S S :=
  fun _ => rfl

protected theorem symm (h : ExtensionEquiv f S T) : ExtensionEquiv f T S :=
  fun K => (h K).symm

protected theorem trans (h₁ : ExtensionEquiv f S T) (h₂ : ExtensionEquiv f T R) :
    ExtensionEquiv f S R :=
  fun K => (h₁ K).trans (h₂ K)

/-- The empty extension: equivalent sets have the same value. -/
theorem apply_eq (h : ExtensionEquiv f S T) : f S = f T := by
  simpa using h ∅

/-- **Congruence for union**, on the right: `S ∼_f T` implies `S ∪ D ∼_f T ∪ D`, by
applying the definition to the extension `D ∪ K`. -/
theorem union_right (h : ExtensionEquiv f S T) (D : Finset U) :
    ExtensionEquiv f (S ∪ D) (T ∪ D) := fun K => by
  rw [Finset.union_assoc, Finset.union_assoc]
  exact h (D ∪ K)

/-- **Congruence for union**, on the left. -/
theorem union_left (D : Finset U) (h : ExtensionEquiv f S T) :
    ExtensionEquiv f (D ∪ S) (D ∪ T) := by
  rw [Finset.union_comm D S, Finset.union_comm D T]
  exact h.union_right D

/-- **Congruence for union**: `∼_f` is a congruence of the union monoid. -/
theorem union (h₁ : ExtensionEquiv f S S') (h₂ : ExtensionEquiv f T T') :
    ExtensionEquiv f (S ∪ T) (S' ∪ T') :=
  (h₁.union_right T).trans (h₂.union_left S')

/-- Equivalence for `f` implies equivalence for every function of the output of `f`. -/
theorem postcomp (h : ExtensionEquiv f S T) (g : O → O') :
    ExtensionEquiv (fun A => g (f A)) S T :=
  fun K => congrArg g (h K)

end ExtensionEquiv

/-- `∼_f` is an equivalence relation on the subsets of `U`. -/
theorem extensionEquiv_equivalence (f : Finset U → O) : Equivalence (ExtensionEquiv f) :=
  ⟨ExtensionEquiv.refl f, ExtensionEquiv.symm, ExtensionEquiv.trans⟩

/-- **Mergeable outputs**: if the value of a union is determined by the values of its two
parts, then extension equivalence is equality of values. -/
theorem extensionEquiv_iff_of_merge {f : Finset U → O}
    (hmerge : ∀ S S' T T' : Finset U, f S = f S' → f T = f T' → f (S ∪ T) = f (S' ∪ T'))
    {S T : Finset U} : ExtensionEquiv f S T ↔ f S = f T :=
  ⟨ExtensionEquiv.apply_eq, fun h K => hmerge S T K K h rfl⟩

/-! ## Strong certificates -/

/-- **A strong certificate** (`def:strong-certificate`): `C` is a strong certificate for `S`
with respect to `f` when `C ⊆ S` and `C ∼_f S`, that is `f (C ∪ K) = f (S ∪ K)` for every
`K ⊆ U`. -/
def IsStrongCertificate (f : Finset U → O) (C S : Finset U) : Prop :=
  C ⊆ S ∧ ExtensionEquiv f C S

variable {f : Finset U → O} {C S T : Finset U} {b b' : ℕ}

/-- Every set is a strong certificate for itself. -/
theorem isStrongCertificate_self (f : Finset U → O) (S : Finset U) :
    IsStrongCertificate f S S :=
  ⟨subset_rfl, ExtensionEquiv.refl f S⟩

/-- **The interval lemma**: if `C ⊆ T ⊆ S` and `C` is a strong certificate for `S`, then so
is `T`. -/
theorem IsStrongCertificate.of_subset (h : IsStrongCertificate f C S) (hCT : C ⊆ T)
    (hTS : T ⊆ S) : IsStrongCertificate f T S := by
  refine ⟨hTS, fun K => ?_⟩
  calc f (T ∪ K) = f (C ∪ (T ∪ K)) := by
        rw [← Finset.union_assoc, Finset.union_eq_right.mpr hCT]
    _ = f (S ∪ (T ∪ K)) := h.2 (T ∪ K)
    _ = f (S ∪ K) := by rw [← Finset.union_assoc, Finset.union_eq_left.mpr hTS]

/-- A strong certificate for the output of `f` is one for every function of that output. -/
theorem IsStrongCertificate.postcomp (h : IsStrongCertificate f C S) (g : O → O') :
    IsStrongCertificate (fun A => g (f A)) C S :=
  ⟨h.1, h.2.postcomp g⟩

/-! ## Uniform bounds and the certificate size -/

/-- **A uniform certificate bound**: every `S ⊆ U` has a strong certificate with at most `b`
elements. -/
def HasStrongCertificateBound (f : Finset U → O) (b : ℕ) : Prop :=
  ∀ S : Finset U, ∃ C, IsStrongCertificate f C S ∧ C.card ≤ b

theorem HasStrongCertificateBound.mono (h : HasStrongCertificateBound f b) (hb : b ≤ b') :
    HasStrongCertificateBound f b' := fun S => by
  obtain ⟨C, hC, hcard⟩ := h S
  exact ⟨C, hC, hcard.trans hb⟩

theorem HasStrongCertificateBound.postcomp (h : HasStrongCertificateBound f b) (g : O → O') :
    HasStrongCertificateBound (fun A => g (f A)) b := fun S => by
  obtain ⟨C, hC, hcard⟩ := h S
  exact ⟨C, hC.postcomp g, hcard⟩

/-- **Self-certification**: over a finite universe, `#U` is a certificate bound. -/
theorem hasStrongCertificateBound_card [Fintype U] (f : Finset U → O) :
    HasStrongCertificateBound f (Fintype.card U) :=
  fun S => ⟨S, isStrongCertificate_self f S, Finset.card_le_univ S⟩

/-- **The strong-certificate size** `b_f(U)`: the least uniform certificate bound.  Over a
finite universe a bound always exists (`hasStrongCertificateBound_card`); otherwise the
infimum of the empty set is `0`, as for `breadth`. -/
noncomputable def strongCertificateSize (f : Finset U → O) : ℕ :=
  sInf {b | HasStrongCertificateBound f b}

theorem strongCertificateSize_le (h : HasStrongCertificateBound f b) :
    strongCertificateSize f ≤ b :=
  Nat.sInf_le h

/-- Over a finite universe the least bound is itself a bound: the infimum is attained. -/
theorem hasStrongCertificateBound_strongCertificateSize [Finite U] (f : Finset U → O) :
    HasStrongCertificateBound f (strongCertificateSize f) := by
  have := Fintype.ofFinite U
  exact Nat.sInf_mem (s := {b | HasStrongCertificateBound f b})
    ⟨_, hasStrongCertificateBound_card f⟩

theorem hasStrongCertificateBound_iff_size_le [Finite U] :
    HasStrongCertificateBound f b ↔ strongCertificateSize f ≤ b :=
  ⟨strongCertificateSize_le, fun h => (hasStrongCertificateBound_strongCertificateSize f).mono h⟩

/-- **An optimal certificate exists**: every set has a strong certificate of at most
`strongCertificateSize f` elements. -/
theorem exists_isStrongCertificate_card_le [Finite U] (f : Finset U → O) (S : Finset U) :
    ∃ C, IsStrongCertificate f C S ∧ C.card ≤ strongCertificateSize f :=
  hasStrongCertificateBound_strongCertificateSize f S

theorem strongCertificateSize_le_card [Fintype U] (f : Finset U → O) :
    strongCertificateSize f ≤ Fintype.card U :=
  strongCertificateSize_le (hasStrongCertificateBound_card f)

/-- A set all of whose strong certificates have at least `c` elements forces
`c ≤ strongCertificateSize f`. -/
theorem le_strongCertificateSize [Finite U] {c : ℕ} (S : Finset U)
    (h : ∀ C, IsStrongCertificate f C S → c ≤ C.card) : c ≤ strongCertificateSize f := by
  obtain ⟨C, hC, hcard⟩ := exists_isStrongCertificate_card_le f S
  exact (h C hC).trans hcard

/-- **Postprocessing**: certificates for an output certify every function of that output. -/
theorem strongCertificateSize_postcomp_le [Finite U] (f : Finset U → O) (g : O → O') :
    strongCertificateSize (fun A => g (f A)) ≤ strongCertificateSize f :=
  strongCertificateSize_le ((hasStrongCertificateBound_strongCertificateSize f).postcomp g)

/-- **An injective function has certificate size `#U`**: the empty extension forces a strong
certificate to equal the set it certifies, and the whole universe needs `#U` elements. -/
theorem strongCertificateSize_of_injective [Fintype U] (hf : Function.Injective f) :
    strongCertificateSize f = Fintype.card U := by
  refine (strongCertificateSize_le_card f).antisymm
    (le_strongCertificateSize Finset.univ fun C hC => ?_)
  rw [hf hC.2.apply_eq, Finset.card_univ]

/-- Bound `0` means `f` is constant: the empty set certifies every set. -/
theorem hasStrongCertificateBound_zero_iff :
    HasStrongCertificateBound f 0 ↔ ∀ S T, f S = f T := by
  constructor
  · intro h
    have hempty : ∀ S, f ∅ = f S := fun S => by
      obtain ⟨C, hC, hcard⟩ := h S
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at hC
      exact hC.2.apply_eq
    exact fun S T => (hempty S).symm.trans (hempty T)
  · intro h S
    exact ⟨∅, ⟨Finset.empty_subset S, fun K => h _ _⟩, le_rfl⟩

/-- **Size zero exactly for constant functions.** -/
theorem strongCertificateSize_eq_zero_iff [Finite U] :
    strongCertificateSize f = 0 ↔ ∀ S T, f S = f T := by
  rw [← hasStrongCertificateBound_zero_iff, hasStrongCertificateBound_iff_size_le,
    Nat.le_zero]

/-! ## The paper's maximum of minimum certificate sizes -/

/-- The minimum size of a strong certificate for `S`, the inner `min` of
`eq:strong-certificate-size`.  The set it minimizes over contains `#S` (self-certification). -/
noncomputable def minStrongCertificateSize (f : Finset U → O) (S : Finset U) : ℕ :=
  sInf {k | ∃ C, IsStrongCertificate f C S ∧ C.card = k}

/-- The minimum is attained. -/
theorem exists_isStrongCertificate_card_eq_min (f : Finset U → O) (S : Finset U) :
    ∃ C, IsStrongCertificate f C S ∧ C.card = minStrongCertificateSize f S :=
  Nat.sInf_mem (s := {k | ∃ C, IsStrongCertificate f C S ∧ C.card = k})
    ⟨S.card, S, isStrongCertificate_self f S, rfl⟩

theorem minStrongCertificateSize_le (h : IsStrongCertificate f C S) :
    minStrongCertificateSize f S ≤ C.card :=
  Nat.sInf_le ⟨C, h, rfl⟩

theorem minStrongCertificateSize_le_card (f : Finset U → O) (S : Finset U) :
    minStrongCertificateSize f S ≤ S.card :=
  minStrongCertificateSize_le (isStrongCertificate_self f S)

/-- A uniform bound is a bound on every minimum certificate size. -/
theorem hasStrongCertificateBound_iff_forall_min_le :
    HasStrongCertificateBound f b ↔ ∀ S, minStrongCertificateSize f S ≤ b := by
  constructor
  · intro h S
    obtain ⟨C, hC, hcard⟩ := h S
    exact (minStrongCertificateSize_le hC).trans hcard
  · intro h S
    obtain ⟨C, hC, hcard⟩ := exists_isStrongCertificate_card_eq_min f S
    exact ⟨C, hC, hcard ▸ h S⟩

/-- **`eq:strong-certificate-size`**: the least uniform certificate bound is the paper's
`b_f(U) = max_{S ⊆ U} min{|C| : C ⊆ S, C ∼_f S}`. -/
theorem strongCertificateSize_eq_sup [Fintype U] (f : Finset U → O) :
    strongCertificateSize f = Finset.univ.sup (minStrongCertificateSize f) := by
  refine le_antisymm (strongCertificateSize_le ?_) (Finset.sup_le_iff.mpr fun S _ => ?_)
  · exact hasStrongCertificateBound_iff_forall_min_le.mpr fun S =>
      Finset.le_sup (f := minStrongCertificateSize f) (Finset.mem_univ S)
  · exact hasStrongCertificateBound_iff_forall_min_le.mp
      (hasStrongCertificateBound_strongCertificateSize f) S

end MonoidProduct.Certificates
