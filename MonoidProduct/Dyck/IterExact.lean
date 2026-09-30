import MonoidProduct.Dyck.ExactCount
import QuantumQueryComplexity.Promise.Compose
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Iterated exact count

The depth-`ℓ` iterated exact-count promise: a complete `2m`-ary tree of depth
`ℓ` whose every internal node sees a vector of `2m` child answers containing
either `m` or `m+1` zeros.  Composing `nat_le_advPMOn_exactCount` with itself
`ℓ` times gives

  `pow_le_advPMOn_iterExact : (m : ℝ) ^ ℓ ≤ ADV±(iterExact m ℓ)`.

## Inputs are words of leaf bits, not nested tuples

`Promise/Compose.lean` builds the composite domain as a subtype of *tuples of
inner inputs*, `{ys : α → Y // …}`.  Iterating that literally would need
`IterDom` and `iterOut` to be defined by mutual recursion — the domain at depth
`ℓ+1` mentions the answer function at depth `ℓ` — which Lean will not accept for
a type family.

So the iterated promise is instead carved out of a *fixed* cube: `iterVal` and
`IterOk` are defined by recursion on `ℓ` over all of `IterIdx m ℓ → Bool`, with
no dependency on each other's domains, and `IterDom m ℓ` is the subtype cut out
by `IterOk`.  Its `Fintype` and `DecidableEq` instances are then automatic, the
observation map is `Subtype.val` (injective for free), and the block encoder
(`Blocks.lean`) gets the leaf-bit view it wants.

The bridge is `iterEquiv`, a domain equivalence between the composite domain and
`IterDom m (ℓ+1)` that respects reads and answers, transported by
`advPMOn_le_of_equiv`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Relabelling a promise domain -/

section Congr

variable {ι σ O : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]
variable {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']

/-- An equivalence of promise domains respecting reads and answers transports
the adversary bound.  (Only one direction is stated; apply it twice for the
equality.) -/
theorem advPMOn_le_of_equiv {read : X → ι → σ} {f : X → O}
    {read' : X' → ι → σ} {f' : X' → O} (e : X ≃ X')
    (hdet' : ∀ a b : X', read' a = read' b → f' a = f' b)
    (hread : ∀ x, read' (e x) = read x) (hout : ∀ x, f' (e x) = f x) :
    advPMOn read f ≤ advPMOn read' f' := by
  refine advPMOn_le fun Γ hΓ hmask => ?_
  have hread' : ∀ a : X', read' a = read (e.symm a) := by
    intro a
    rw [← hread (e.symm a), e.apply_symm_apply]
  have hout' : ∀ a : X', f' a = f (e.symm a) := by
    intro a
    rw [← hout (e.symm a), e.apply_symm_apply]
  have hmaskEq : ∀ i, Γ.submatrix e.symm e.symm ⊙ advDOn read' i
      = (Γ ⊙ advDOn read i).submatrix e.symm e.symm := by
    intro i
    ext a b
    rw [Matrix.hadamard_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
      Matrix.hadamard_apply, advDOn_apply, advDOn_apply, hread' a, hread' b]
  have hadv : IsAdvMatrixOn f' (Γ.submatrix e.symm e.symm) := by
    refine ⟨hΓ.1.submatrix _, fun a b hab => ?_⟩
    rw [Matrix.submatrix_apply]
    exact hΓ.2 _ _ ((hout' a).symm.trans (hab.trans (hout' b)))
  have hmask' : ∀ i, ‖Γ.submatrix e.symm e.symm ⊙ advDOn read' i‖ ≤ 1 := by
    intro i
    rw [hmaskEq i, l2_opNorm_submatrix_equiv]
    exact hmask i
  rw [← l2_opNorm_submatrix_equiv Γ e.symm]
  exact le_advPMOn hdet' hadv hmask'

end Congr

/-! ## The depth-indexed promise -/

/-- Query indices: a leaf address in the complete `2m`-ary tree of depth `ℓ`. -/
def IterIdx (m : ℕ) : ℕ → Type
  | 0 => Unit
  | ℓ + 1 => Fin (2 * m) × IterIdx m ℓ

instance IterIdx.instFintype (m : ℕ) : (ℓ : ℕ) → Fintype (IterIdx m ℓ)
  | 0 => inferInstanceAs (Fintype Unit)
  | ℓ + 1 =>
      letI := IterIdx.instFintype m ℓ
      inferInstanceAs (Fintype (Fin (2 * m) × IterIdx m ℓ))

instance IterIdx.instDecidableEq (m : ℕ) : (ℓ : ℕ) → DecidableEq (IterIdx m ℓ)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | ℓ + 1 =>
      letI := IterIdx.instDecidableEq m ℓ
      inferInstanceAs (DecidableEq (Fin (2 * m) × IterIdx m ℓ))

/-- The word read by the `i`-th subtree. -/
def child {m ℓ : ℕ} (x : IterIdx m (ℓ + 1) → Bool) (i : Fin (2 * m)) :
    IterIdx m ℓ → Bool := fun j => x (i, j)

/-- The value the tree computes, defined on the whole cube. -/
def iterVal (m : ℕ) : (ℓ : ℕ) → (IterIdx m ℓ → Bool) → Bool
  | 0, x => x ()
  | ℓ + 1, x => decide (falseCount (fun i => iterVal m ℓ (child x i)) = m)

/-- The promise: every internal node sees an exact-count-promised vector. -/
def IterOk (m : ℕ) : (ℓ : ℕ) → (IterIdx m ℓ → Bool) → Prop
  | 0, _ => True
  | ℓ + 1, x =>
      (∀ i, IterOk m ℓ (child x i)) ∧
        (falseCount (fun i => iterVal m ℓ (child x i)) = m ∨
          falseCount (fun i => iterVal m ℓ (child x i)) = m + 1)

instance IterOk.decidablePred (m : ℕ) : (ℓ : ℕ) → DecidablePred (IterOk m ℓ)
  | 0 => fun _ => isTrue trivial
  | ℓ + 1 => fun x =>
      letI : DecidablePred (IterOk m ℓ) := IterOk.decidablePred m ℓ
      inferInstanceAs (Decidable ((∀ i, IterOk m ℓ (child x i)) ∧
        (falseCount (fun i => iterVal m ℓ (child x i)) = m ∨
          falseCount (fun i => iterVal m ℓ (child x i)) = m + 1)))

/-- The depth-`ℓ` iterated exact-count promise domain. -/
def IterDom (m ℓ : ℕ) : Type := {x : IterIdx m ℓ → Bool // IterOk m ℓ x}

instance IterDom.instFintype (m ℓ : ℕ) : Fintype (IterDom m ℓ) :=
  Subtype.fintype _

instance IterDom.instDecidableEq (m ℓ : ℕ) : DecidableEq (IterDom m ℓ) :=
  Subtype.instDecidableEq

/-- A query reads one leaf bit. -/
def iterRead {m ℓ : ℕ} (x : IterDom m ℓ) : IterIdx m ℓ → Bool := x.1

/-- The answer at the root. -/
def iterOut (m ℓ : ℕ) (x : IterDom m ℓ) : Bool := iterVal m ℓ x.1

lemma iterRead_injective {m ℓ : ℕ} :
    Function.Injective (iterRead (m := m) (ℓ := ℓ)) := fun _ _ h => Subtype.ext h

/-! ## Depth zero is the one-bit problem -/

lemma one_le_advPMOn_iter_zero (m : ℕ) :
    1 ≤ advPMOn (iterRead (m := m) (ℓ := 0)) (iterOut m 0) := by
  have hdet := separates_of_injective (iterRead_injective (m := m) (ℓ := 0))
    (iterOut m 0)
  have hbase : (1 : ℝ) ≤ advPM (fun x : Unit → Bool => x ()) :=
    one_le_advPM (x := fun _ => false) (y := fun _ => true) (by simp)
  refine hbase.trans ?_
  rw [← advPMOn_id (fun x : Unit → Bool => x ())]
  refine advPMOn_le_of_equiv
    (e := (Equiv.subtypeUnivEquiv (p := IterOk m 0) fun _ => trivial).symm)
    hdet (fun _ => rfl) (fun _ => rfl)

/-! ## The successor step -/

lemma child_flatten {m ℓ : ℕ} (ys : Fin (2 * m) → IterDom m ℓ)
    (i : Fin (2 * m)) :
    child (fun p : Fin (2 * m) × IterIdx m ℓ => (ys p.1).1 p.2) i
      = (ys i).1 := rfl

/-- The depth-`ℓ+1` promise **is** the exact-count composition of the depth-`ℓ`
promise. -/
def iterEquiv (m ℓ : ℕ) :
    ComposeDom (exactRead (m := m)) (iterOut m ℓ) ≃ IterDom m (ℓ + 1) where
  toFun ys := ⟨fun p => (ys.1 p.1).1 p.2, by
    obtain ⟨z, hz⟩ := ys.2
    refine ⟨fun i => (ys.1 i).2, ?_⟩
    have hval : (fun i => iterVal m ℓ
        (child (fun p : IterIdx m (ℓ + 1) => (ys.1 p.1).1 p.2) i))
        = exactRead z := by
      funext i
      exact (congrFun hz i).symm
    rw [hval]
    exact z.2⟩
  invFun x := ⟨fun i => ⟨child x.1 i, x.2.1 i⟩, by
    refine ⟨⟨fun i => iterVal m ℓ (child x.1 i), x.2.2⟩, rfl⟩⟩
  left_inv ys := Subtype.ext (funext fun _ => Subtype.ext rfl)
  right_inv x := Subtype.ext (funext fun _ => rfl)

lemma iterEquiv_read (m ℓ : ℕ)
    (ys : ComposeDom (exactRead (m := m)) (iterOut m ℓ)) :
    iterRead (iterEquiv m ℓ ys)
      = composeReadOn (exactRead (m := m)) (iterOut m ℓ)
          (iterRead (m := m) (ℓ := ℓ)) ys := rfl

lemma iterEquiv_out (m ℓ : ℕ)
    (ys : ComposeDom (exactRead (m := m)) (iterOut m ℓ)) :
    iterOut m (ℓ + 1) (iterEquiv m ℓ ys)
      = composeOutOn (exactRead (m := m)) (iterOut m ℓ) (exactOut m) ys := by
  obtain ⟨z, hz⟩ := ys.2
  have hR : composeOutOn (exactRead (m := m)) (iterOut m ℓ) (exactOut m) ys
      = exactOut m z := composeOutOn_eq exactRead_injective (exactOut m) ys hz
  have hL : iterOut m (ℓ + 1) (iterEquiv m ℓ ys)
      = decide (falseCount (fun i => iterOut m ℓ (ys.1 i)) = m) := rfl
  have hE : exactOut m z
      = decide (falseCount (fun i => iterOut m ℓ (ys.1 i)) = m) := by
    show decide (falseCount z.1 = m) = _
    rw [show (z.1 : Fin (2 * m) → Bool) = fun i => iterOut m ℓ (ys.1 i) from hz]
  rw [hL, hR, hE]

/-! ## The iterated lower bound -/

/-- **Iterated exact count.**  Iterating exact-count composition `ℓ` times. -/
theorem pow_le_advPMOn_iterExact (m : ℕ) (hm : 0 < m) (ℓ : ℕ) :
    (m : ℝ) ^ ℓ ≤ advPMOn (iterRead (m := m) (ℓ := ℓ)) (iterOut m ℓ) := by
  induction ℓ with
  | zero =>
      rw [pow_zero]
      exact one_le_advPMOn_iter_zero m
  | succ ℓ ih =>
      have hdet' := separates_of_injective
        (iterRead_injective (m := m) (ℓ := ℓ + 1)) (iterOut m (ℓ + 1))
      have hstep := advPMOn_mul_le_advPMOn_compose
        (outerRead := exactRead (m := m)) (innerRead := iterRead (m := m) (ℓ := ℓ))
        (f := exactOut m) (g := iterOut m ℓ)
        exactRead_injective iterRead_injective
      have htrans := advPMOn_le_of_equiv (iterEquiv m ℓ) hdet'
        (iterEquiv_read m ℓ) (iterEquiv_out m ℓ)
      calc (m : ℝ) ^ (ℓ + 1) = (m : ℝ) * (m : ℝ) ^ ℓ := by ring
        _ ≤ advPMOn (exactRead (m := m)) (exactOut m)
              * advPMOn (iterRead (m := m) (ℓ := ℓ)) (iterOut m ℓ) :=
            mul_le_mul (nat_le_advPMOn_exactCount m hm) ih (by positivity)
              (advPMOn_nonneg (separates_of_injective exactRead_injective _))
        _ ≤ advPMOn (composeReadOn (exactRead (m := m)) (iterOut m ℓ)
              (iterRead (m := m) (ℓ := ℓ)))
              (composeOutOn (exactRead (m := m)) (iterOut m ℓ) (exactOut m)) :=
            hstep
        _ ≤ advPMOn (iterRead (m := m) (ℓ := ℓ + 1)) (iterOut m (ℓ + 1)) := htrans

/-! ## Finite checks

At `m = 1` the bound `1 ^ ℓ ≤ …` is vacuous, so these check the *indexing*
rather than the strength: depth `ℓ` has `(2m)^ℓ` leaves, depth `0` is a single
free bit, and depth `1` reproduces the exact-count promise itself.  Note
`IterDom m ℓ` is cut out of a cube of size `2 ^ ((2m)^ℓ)`, so `decide` is only
affordable for very small `m` and `ℓ`. -/

example : Fintype.card (IterIdx 1 2) = 4 := by decide

example : Fintype.card (IterDom 1 0) = 2 := by decide
example : Fintype.card (IterDom 1 1) = 3 := by decide
example : Fintype.card (IterDom 1 2) = 5 := by decide

/-- Depth one *is* the exact-count problem: the domains have the same size. -/
example : Fintype.card (IterDom 2 1) = 10 := by decide
example : Fintype.card (ExactDom 2) = 10 := by decide

end MonoidProduct
