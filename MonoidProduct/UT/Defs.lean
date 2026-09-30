import MonoidProduct.Tropical.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `UT_k(𝔹)`: reflexive upper-unitriangular Boolean matrices

The carrier of `thm:boolean-unitriangular`.  `𝔹 = ({0,1}, ∨, ∧)` is the Boolean semiring, a
Boolean `k × k` matrix is a `Fin k → Fin k → Bool`, and the product is

    (M N) s t = ⋁ᵥ (M s v ∧ N v t).

`UT_k(𝔹)` is the set of matrices with `true` on the diagonal and `false`
strictly below it, closed under the product and containing the identity —
a finite monoid of order `2^C(k,2)`.  It is bundled as a **`def`**, not an
`abbrev`, exactly as `Capped k` was: nothing of the underlying function
type's pointwise structure may leak into the monoid.

The **Boolean→tropical embedding** `true ↦ 0`, `false ↦ ⊥` sends the
Boolean product to the tropical product (`toTMat_bmul`) and the identity
to `tone` (`toTMat_bone`), is injective, and lands in the unitriangular
tropical matrices (`IsBUtri.toTMat`): `UT_k(𝔹)` embeds into the
`{0, ⊥}`-valued unitriangular submonoid of `U_k(𝕋)`.  This is **not** the
Simon transfer — Simon's theorem supplies a division `M ≺ UT_k(𝔹)`
directly; the embedding records how the Boolean and tropical products
relate.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-- A Boolean `k × k` matrix. -/
abbrev BMat (k : ℕ) := Fin k → Fin k → Bool

variable {k : ℕ}

/-- Boolean matrix multiplication: `(M N) s t = ⋁ᵥ (M s v ∧ N v t)`. -/
def bmul (M N : BMat k) : BMat k :=
  fun s t => decide (∃ v, M s v = true ∧ N v t = true)

/-- The identity matrix. -/
def bone (k : ℕ) : BMat k := fun s t => decide (s = t)

lemma bmul_apply (M N : BMat k) (s t : Fin k) :
    bmul M N s t = true ↔ ∃ v, M s v = true ∧ N v t = true := by
  simp [bmul]

lemma bmul_apply_false (M N : BMat k) (s t : Fin k) :
    bmul M N s t = false ↔ ¬ ∃ v, M s v = true ∧ N v t = true := by
  simp [bmul]

lemma bone_apply (s t : Fin k) : bone k s t = true ↔ s = t := by
  simp [bone]

theorem bmul_assoc (M N P : BMat k) :
    bmul (bmul M N) P = bmul M (bmul N P) := by
  funext s t
  simp only [bmul, decide_eq_true_eq]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨v, ⟨u, h1, h2⟩, h3⟩
    exact ⟨u, h1, v, h2, h3⟩
  · rintro ⟨u, h1, v, h2, h3⟩
    exact ⟨v, ⟨u, h1, h2⟩, h3⟩

theorem bone_bmul (M : BMat k) : bmul (bone k) M = M := by
  funext s t
  cases h : M s t <;> simp [bmul, bone, h]

theorem bmul_bone (M : BMat k) : bmul M (bone k) = M := by
  funext s t
  cases h : M s t <;> simp [bmul, bone, h]

/-! ## Unitriangularity -/

/-- **Reflexive upper-unitriangular**: `true` on the diagonal and `false`
strictly below it.  Entries above the diagonal are arbitrary. -/
structure IsBUtri (M : BMat k) : Prop where
  /-- The diagonal is `true`. -/
  diag : ∀ s, M s s = true
  /-- Nothing runs backwards. -/
  below : ∀ s t, t < s → M s t = false

lemma isBUtri_bone : IsBUtri (bone k) where
  diag s := by simp [bone]
  below s t h := by simp [bone, ne_of_gt h]

/-- `UT_k(𝔹)` is closed under the product: a walk from `s` to `t` must
climb `s ≤ v ≤ t`. -/
lemma IsBUtri.bmul {M N : BMat k} (hM : IsBUtri M) (hN : IsBUtri N) :
    IsBUtri (bmul M N) where
  diag s := (bmul_apply M N s s).mpr ⟨s, hM.diag s, hN.diag s⟩
  below s t hts := by
    rw [bmul_apply_false]
    rintro ⟨v, hMv, hNv⟩
    have hsv : ¬ v < s := fun h => by
      rw [hM.below s v h] at hMv
      exact Bool.false_ne_true hMv
    have hvt : ¬ t < v := fun h => by
      rw [hN.below v t h] at hNv
      exact Bool.false_ne_true hNv
    exact absurd hts (not_lt.mpr (le_trans (not_lt.mp hsv) (not_lt.mp hvt)))

instance : DecidablePred (IsBUtri (k := k)) := fun M =>
  decidable_of_iff ((∀ s, M s s = true) ∧ ∀ s t, t < s → M s t = false)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.diag, h.below⟩⟩

/-! ## The monoid -/

/-- **`UT_k(𝔹)`**, bundled.  A `def`, never an `abbrev`. -/
def BUT (k : ℕ) : Type := {M : BMat k // IsBUtri M}

namespace BUT

instance : DecidableEq (BUT k) := Subtype.instDecidableEq

instance : Fintype (BUT k) := Subtype.fintype _

/-- The underlying matrix. -/
def mat (M : BUT k) : BMat k := Subtype.val M

lemma isBUtri_mat (M : BUT k) : IsBUtri M.mat := Subtype.property M

@[ext] lemma ext {M N : BUT k} (h : M.mat = N.mat) : M = N := Subtype.ext h

instance : Monoid (BUT k) where
  mul M N := Subtype.mk (bmul (Subtype.val M) (Subtype.val N))
    ((Subtype.property M).bmul (Subtype.property N))
  one := Subtype.mk (bone k) isBUtri_bone
  mul_assoc M N P := Subtype.ext (bmul_assoc _ _ _)
  one_mul M := Subtype.ext (bone_bmul _)
  mul_one M := Subtype.ext (bmul_bone _)

@[simp] lemma mat_mul (M N : BUT k) : (M * N).mat = bmul M.mat N.mat := rfl

@[simp] lemma mat_one : (1 : BUT k).mat = bone k := rfl

/-- `UT_1(𝔹)` is trivial: the single entry is the diagonal `true`. -/
instance : Subsingleton (BUT 1) :=
  ⟨fun M N => BUT.ext (funext fun s => funext fun t => by
    have hst : s = t := Subsingleton.elim s t
    subst hst
    rw [M.isBUtri_mat.diag, N.isBUtri_mat.diag])⟩

end BUT

/-! ## The Boolean→tropical embedding -/

/-- `true ↦ 0`, `false ↦ ⊥`. -/
def bToTrop : Bool → Trop
  | true => 0
  | false => ⊥

@[simp] lemma bToTrop_true : bToTrop true = 0 := rfl

@[simp] lemma bToTrop_false : bToTrop false = ⊥ := rfl

lemma bToTrop_le_zero (b : Bool) : bToTrop b ≤ 0 := by
  cases b
  · exact bot_le
  · exact le_rfl

/-- The entrywise embedding of a Boolean matrix into the tropical matrices. -/
def toTMat (M : BMat k) : TMat k := fun s t => bToTrop (M s t)

theorem toTMat_bone : toTMat (bone k) = tone k := by
  funext s t
  by_cases h : s = t <;> simp [toTMat, bone, tone, h]

/-- **The embedding is multiplicative**: the Boolean product becomes the
tropical product — a sup of `{⊥, 0}`-valued terms is `0` exactly when some
term is `0 + 0`. -/
theorem toTMat_bmul (M N : BMat k) :
    toTMat (bmul M N) = tmul (toTMat M) (toTMat N) := by
  funext s t
  simp only [toTMat, tmul]
  by_cases h : ∃ v, M s v = true ∧ N v t = true
  · obtain ⟨v, hMv, hNv⟩ := h
    rw [(bmul_apply M N s t).mpr ⟨v, hMv, hNv⟩, bToTrop_true]
    apply le_antisymm
    · have h0 : (0 : Trop) ≤ bToTrop (M s v) + bToTrop (N v t) := by
        rw [hMv, hNv, bToTrop_true, add_zero]
      exact h0.trans (Finset.le_sup
        (f := fun v => bToTrop (M s v) + bToTrop (N v t)) (Finset.mem_univ v))
    · exact Finset.sup_le fun v _ => by
        simpa using add_le_add (bToTrop_le_zero (M s v)) (bToTrop_le_zero (N v t))
  · rw [(bmul_apply_false M N s t).mpr h, bToTrop_false]
    symm
    rw [Finset.sup_eq_bot_iff]
    intro v _
    cases hMv : M s v
    · rw [bToTrop_false, WithBot.bot_add]
    · cases hNv : N v t
      · rw [bToTrop_false, WithBot.add_bot]
      · exact absurd ⟨v, hMv, hNv⟩ h

theorem toTMat_injective : Function.Injective (toTMat (k := k)) := by
  intro M N h
  funext s t
  have hst := congrFun (congrFun h s) t
  simp only [toTMat] at hst
  cases hM : M s t <;> cases hN : N s t <;> rw [hM, hN] at hst <;>
    first
      | rfl
      | (rw [bToTrop_true, bToTrop_false] at hst; exact absurd hst WithBot.zero_ne_bot)
      | (rw [bToTrop_false, bToTrop_true] at hst; exact absurd hst.symm WithBot.zero_ne_bot)

/-- A unitriangular Boolean matrix embeds as a unitriangular tropical
matrix: `UT_k(𝔹) ⊆ U_k(𝕋)`. -/
theorem IsBUtri.toTMat {M : BMat k} (h : IsBUtri M) : IsUtri (MonoidProduct.toTMat M) where
  diag s := by simp [MonoidProduct.toTMat, h.diag s]
  below s t hts := by simp [MonoidProduct.toTMat, h.below s t hts]

end MonoidProduct
