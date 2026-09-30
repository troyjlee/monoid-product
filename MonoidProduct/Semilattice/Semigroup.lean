import MonoidProduct.Semilattice.Final
import MonoidProduct.Semilattice.Generated
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The product theorem for a commutative idempotent semigroup

A commutative idempotent semigroup **is** a join-semilattice:

  `a ≤ b ↔ a * b = b`,   `a ⊔ b = a * b`.

Reflexivity of `≤` is idempotence, transitivity is associativity, antisymmetry is
commutativity, and `a * b` is the least upper bound of `a` and `b`.  No identity
element is needed anywhere: the product of a *nonempty* family is a nonempty
join, which is why `MonoidProduct/Semilattice/*` never assumes a bottom and adjoins
one only inside `WithBot` while scanning.

The order is installed on a type synonym `AsJoin M` rather than on `M` itself.
`M` may already carry an unrelated order — a set of naturals under `max` carries
the arithmetic one — and installing a second `≤` globally would make instance
resolution incoherent.

Since `⊔` on `AsJoin M` is *definitionally* `*` (`AsJoin.sup_eq_mul` is `rfl`),
the join of the letters read at the query positions is literally their product,
folded over those positions; `prodMap_pair` confirms this on two positions.  So
the mathematical content is entirely `MonoidProduct/Semilattice/Final.lean` and this
file is only the translation.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-- A commutative semigroup in which every element is idempotent. -/
class IsIdemCommSemigroup (M : Type*) extends CommSemigroup M where
  /-- Every element is idempotent. -/
  mul_self : ∀ a : M, a * a = a

/-- A commutative idempotent semigroup, viewed as a join-semilattice.  The order
lives on this synonym so that no instance is installed on `M` itself. -/
def AsJoin (M : Type*) : Type _ := M

namespace AsJoin

variable {M : Type*}

instance [Fintype M] : Fintype (AsJoin M) := inferInstanceAs (Fintype M)
instance [DecidableEq M] : DecidableEq (AsJoin M) := inferInstanceAs (DecidableEq M)
instance [Nonempty M] : Nonempty (AsJoin M) := inferInstanceAs (Nonempty M)
instance [IsIdemCommSemigroup M] : CommSemigroup (AsJoin M) :=
  inferInstanceAs (CommSemigroup M)

/-- Viewing an element of `M` in the synonym.  This is the identity map, but
naming it keeps elaboration deterministic: a bare type ascription leaves Lean
looking for the order on `M` itself. -/
def mk (a : M) : AsJoin M := a

/-- Reading an element of the synonym back. -/
def val (a : AsJoin M) : M := a

@[simp] lemma val_mk (a : M) : (mk a).val = a := rfl

@[simp] lemma mk_val (a : AsJoin M) : mk a.val = a := rfl

lemma val_injective : Function.Injective (val : AsJoin M → M) := fun _ _ h => h

variable [IsIdemCommSemigroup M]

@[simp] lemma val_mul (a b : AsJoin M) : (a * b).val = a.val * b.val := rfl

lemma mul_self (a : AsJoin M) : a * a = a := IsIdemCommSemigroup.mul_self (M := M) a

/-- **The canonical order of a commutative idempotent semigroup.** -/
instance instSemilatticeSup : SemilatticeSup (AsJoin M) where
  le a b := a * b = b
  lt a b := a * b = b ∧ ¬ (b * a = a)
  le_refl a := mul_self a
  le_trans a b c hab hbc := by
    show a * c = c
    calc a * c = a * (b * c) := by rw [show b * c = c from hbc]
      _ = a * b * c := (mul_assoc a b c).symm
      _ = b * c := by rw [show a * b = b from hab]
      _ = c := hbc
  le_antisymm a b hab hba := by
    show a = b
    rw [← show a * b = b from hab, mul_comm]
    exact (show b * a = a from hba).symm
  sup a b := a * b
  le_sup_left a b := by
    show a * (a * b) = a * b
    rw [← mul_assoc, mul_self]
  le_sup_right a b := by
    show b * (a * b) = a * b
    rw [mul_comm a b, ← mul_assoc, mul_self]
  sup_le a b c hac hbc := by
    show a * b * c = c
    rw [mul_assoc, show b * c = c from hbc, show a * c = c from hac]

/-- The join *is* the product. -/
@[simp] lemma sup_eq_mul (a b : AsJoin M) : a ⊔ b = a * b := rfl

lemma le_iff (a b : AsJoin M) : a ≤ b ↔ a * b = b := Iff.rfl

end AsJoin

/-! ## The product of the letters read at the query positions -/

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M] [IsIdemCommSemigroup M]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The product of the letters read at the query positions, multiplied together
over those positions.  Because `⊔` on `AsJoin M` is `*`, this fold of the join is
the semigroup product. -/
noncomputable def prodMap (m : σ → M) (x : ι → σ) : M :=
  (joinMap (ι := ι) (A := AsJoin M) (fun s => AsJoin.mk (m s)) x).val

/-- Every letter's value absorbs into the product. -/
lemma mul_prodMap (m : σ → M) (x : ι → σ) (i : ι) :
    m (x i) * prodMap m x = prodMap m x :=
  le_joinMap (ι := ι) (A := AsJoin M) (fun s => AsJoin.mk (m s)) x i

/-- The product is least among the elements that every letter absorbs into. -/
lemma prodMap_mul (m : σ → M) (x : ι → σ) {b : M}
    (h : ∀ i, m (x i) * b = b) : prodMap m x * b = b :=
  joinMap_le (ι := ι) (A := AsJoin M) (m := fun s => AsJoin.mk (m s))
    (b := AsJoin.mk b) h

/-- **On two positions, the product really is a product.** -/
lemma prodMap_pair (m : σ → M) (x : Fin 2 → σ) :
    prodMap (ι := Fin 2) m x = m (x 0) * m (x 1) := by
  have h1 := le_joinMap (ι := Fin 2) (A := AsJoin M)
    (fun s => AsJoin.mk (m s)) x 0
  have h2 := le_joinMap (ι := Fin 2) (A := AsJoin M)
    (fun s => AsJoin.mk (m s)) x 1
  have h3 : joinMap (ι := Fin 2) (A := AsJoin M) (fun s => AsJoin.mk (m s)) x
      ≤ AsJoin.mk (m (x 0)) ⊔ AsJoin.mk (m (x 1)) := by
    refine joinMap_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  exact congrArg AsJoin.val (le_antisymm h3 (sup_le h1 h2))

/-! ## The theorem -/

/-- **The product theorem for a commutative idempotent semigroup.**

For `n` query positions and letters interpreted in a finite commutative
idempotent semigroup `M`,

  `ADV±(x ↦ ∏ᵢ m (xᵢ)) ≤ 16 √(n ⌊log₂(|M|+1)⌋)`.

Since the product of the letters is their join in the canonical order, this is
`advPM_joinMap_le` read through `AsJoin`.  The bound depends on `M` only through
its cardinality — not on the size of the letter type, and not on any structure of
`M` beyond the semigroup laws.  It is a direct adversary construction: no quantum
algorithm, no amplification, and no appeal to the characterisation of quantum
query complexity by the adversary bound. -/
theorem advPM_prodMap_le (m : σ → M) :
    advPM (prodMap m : (ι → σ) → M)
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * (joinBits M : ℝ)) := by
  obtain ⟨P, hP⟩ := exists_joinMap_dual_isCostLe (ι := ι) (A := AsJoin M) (σ := σ)
    (fun s => AsJoin.mk (m s))
  -- the dual sees only which inputs share a value, and `AsJoin.val` is injective
  have hcon : ∀ x y : ι → σ,
      (∑ i, if x i = y i then (0 : ℝ) else ∑ k, P.u x i k * P.v y i k)
        = if prodMap m x = prodMap m y then 0 else 1 := by
    intro x y
    rw [P.constraint x y]
    by_cases hxy : joinMap (ι := ι) (A := AsJoin M) (fun s => AsJoin.mk (m s)) x
        = joinMap (ι := ι) (A := AsJoin M) (fun s => AsJoin.mk (m s)) y
    · rw [if_pos hxy,
        if_pos (show prodMap m x = prodMap m y from congrArg AsJoin.val hxy)]
    · rw [if_neg hxy, if_neg (show ¬ prodMap m x = prodMap m y from
        fun hc => hxy (AsJoin.val_injective hc))]
  exact advPM_le_of_dualPair ⟨P.u, P.v, hcon⟩ (by positivity) ⟨hP.1, hP.2⟩

end Product

/-! ## An infinite ambient semigroup

The same statement with no finiteness assumption on `M`: the letters generate a
finite subsemigroup, and only its size enters. -/

section Ambient

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {M : Type*} [DecidableEq M] [IsIdemCommSemigroup M]
variable {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ]

/-- The subsemigroup generated by the letters' values.  It is finite because the
letter type is, however large `M` may be. -/
abbrev GeneratedSub (m : σ → M) : Type _ :=
  Generated (M := AsJoin M) (fun s => AsJoin.mk (m s))

/-- The product of the letters read at the query positions, in a possibly
infinite commutative idempotent semigroup. -/
noncomputable def prodMapAmb (m : σ → M) (x : ι → σ) : M :=
  (joinMap (ι := ι) (A := AsJoin M) (fun s => AsJoin.mk (m s)) x).val

/-- **The product theorem with no finiteness assumption on the semigroup.**

For `n` query positions and letters drawn from a finite type interpreted in *any*
commutative idempotent semigroup `M`,

  `ADV±(x ↦ ∏ᵢ m (xᵢ)) ≤ 16 √(n ⌊log₂(|L| + 1)⌋)`,

where `L` is the finite subsemigroup the letters generate.  Nothing about `M`
beyond `L` is counted. -/
theorem advPM_prodMapAmb_le (m : σ → M) :
    advPM (prodMapAmb m : (ι → σ) → M)
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * (joinBits (GeneratedSub m) : ℝ)) :=
  advPM_joinMap_ambient_le (ι := ι) (M := AsJoin M) (σ := σ)
    (fun s => AsJoin.mk (m s))

end Ambient

end MonoidProduct
