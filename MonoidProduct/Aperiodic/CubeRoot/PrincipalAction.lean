import MonoidProduct.Aperiodic.CubeRoot.PrincipalFactor
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The monoid's partial action on the cells

The action before the matrices.  `RowColAction` wants a monoid hom
`M →* Matrix I I ℚ` and a map `M → Matrix Λ Λ ℚ` intertwined by the sandwich;
what actually acts is coarser and easier to get right, so it is built first:

* **left** multiplication moves the `R`-class and fixes the `L`-class, so it is
  a partial map `RIdx → Option (RIdx)` — `rowMap`;
* **right** multiplication moves the `L`-class and fixes the `R`-class, so it is
  a partial map `LIdx → Option (LIdx)` — `colMap`.

"Partial" is not a convenience: a product can leave the class, and when it does
the block sees a genuine `0`.  `Option` carries that, and the two facts the
matrices will need are proved here where they are one line each — **composition**
(`rowMap_mul`, `colMap_mul`) and **absorbing death** (`rowMap_bind_none`,
`colMap_bind_none`), the latter being `twoIdeal_mul_left_ne` /
`twoIdeal_mul_right_ne`: once a product has dropped strictly below the class,
nothing brings it back.

Note the orders.  `rowMap` is a **left** action, so `rowMap (m*n) = rowMap m ∘
rowMap n`, written as `(rowMap n i).bind (rowMap m)`; `colMap` is a **right**
action and composes the other way.  That is exactly what makes `row` a monoid
homomorphism and `col` its opposite-handed partner in `PrincipalMatrix.lean`.

The plumbing that makes all of this well defined is `rEq_mul_left` /
`lEq_mul_right`: multiplying on the *far* side preserves the class, so the
partial maps do not depend on which representative is read.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace PrincipalFactor

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## Representative compatibility -/

/-- Left multiplication preserves `R`-equivalence. -/
lemma rEq_mul_left (m : M) {x y : M} (h : REq x y) : REq (m * x) (m * y) := by
  obtain ⟨q, hq⟩ := rLe_iff_exists.1 (rEq_iff.1 h).1
  obtain ⟨q', hq'⟩ := rLe_iff_exists.1 (rEq_iff.1 h).2
  exact rEq_iff.2 ⟨rLe_iff_exists.2 ⟨q, by rw [mul_assoc, hq]⟩,
    rLe_iff_exists.2 ⟨q', by rw [mul_assoc, hq']⟩⟩

/-- Right multiplication preserves `L`-equivalence. -/
lemma lEq_mul_right (m : M) {x y : M} (h : LEq x y) : LEq (x * m) (y * m) := by
  obtain ⟨p, hp⟩ := lLe_iff_exists.1 (lEq_iff.1 h).1
  obtain ⟨p', hp'⟩ := lLe_iff_exists.1 (lEq_iff.1 h).2
  exact lEq_iff.2 ⟨lLe_iff_exists.2 ⟨p, by rw [← mul_assoc, hp]⟩,
    lLe_iff_exists.2 ⟨p', by rw [← mul_assoc, hp']⟩⟩

/-! ## Death is absorbing

Once a product has left the class it has left the class's ideal *strictly*, and
no further multiplication returns: this is what makes the `0` of the block
absorbing, and it is the only thing the composition proofs need beyond
associativity. -/

/-- An element strictly below the class stays strictly below it on the left. -/
lemma twoIdeal_mul_left_ne {a z : M} (hsub : twoIdeal z ⊆ twoIdeal a)
    (h : twoIdeal z ≠ twoIdeal a) (m : M) : twoIdeal (m * z) ≠ twoIdeal a := by
  intro hc
  refine h (Finset.Subset.antisymm hsub ?_)
  rw [← hc]
  exact twoIdeal_subset_of_lLe (lLe_iff_exists.2 ⟨m, rfl⟩)

/-- An element strictly below the class stays strictly below it on the right. -/
lemma twoIdeal_mul_right_ne {a z : M} (hsub : twoIdeal z ⊆ twoIdeal a)
    (h : twoIdeal z ≠ twoIdeal a) (m : M) : twoIdeal (z * m) ≠ twoIdeal a := by
  intro hc
  refine h (Finset.Subset.antisymm hsub ?_)
  rw [← hc]
  exact twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨m, rfl⟩)

/-! ## The classes of a raw element -/

variable (M) in
/-- The `R`-class of `z`, if `z` lies in the class at all. -/
noncomputable def rClassOf (a z : M) : Option (RIdx M a) :=
  if h : twoIdeal z = twoIdeal a then some (rIdx M ⟨z, mem_jClass.2 h⟩) else none

variable (M) in
/-- The `L`-class of `z`, if `z` lies in the class at all. -/
noncomputable def lClassOf (a z : M) : Option (LIdx M a) :=
  if h : twoIdeal z = twoIdeal a then some (lIdx M ⟨z, mem_jClass.2 h⟩) else none

lemma rClassOf_eq_some {a z : M} (h : twoIdeal z = twoIdeal a) :
    rClassOf M a z = some (rIdx M ⟨z, mem_jClass.2 h⟩) := dif_pos h

lemma lClassOf_eq_some {a z : M} (h : twoIdeal z = twoIdeal a) :
    lClassOf M a z = some (lIdx M ⟨z, mem_jClass.2 h⟩) := dif_pos h

lemma rClassOf_eq_none {a z : M} (h : twoIdeal z ≠ twoIdeal a) :
    rClassOf M a z = none := dif_neg h

lemma lClassOf_eq_none {a z : M} (h : twoIdeal z ≠ twoIdeal a) :
    lClassOf M a z = none := dif_neg h

/-! ## The two partial actions -/

variable (M) in
/-- **The row action**: left multiplication, read on `R`-classes.  Partial,
because the product may leave the class. -/
noncomputable def rowMap {a : M} (m : M) (i : RIdx M a) : Option (RIdx M a) :=
  rClassOf M a (m * (rRep M i).1)

variable (M) in
/-- **The column action**: right multiplication, read on `L`-classes. -/
noncomputable def colMap {a : M} (m : M) (l : LIdx M a) : Option (LIdx M a) :=
  lClassOf M a ((lRep M l).1 * m)

/-- **Representative independence, row side.**  The action read at *any*
representative of the class is the action. -/
theorem rowMap_rIdx {a : M} (m : M) (x : JType M a) :
    rowMap M m (rIdx M x) = rClassOf M a (m * x.1) := by
  have hR : REq (m * (rRep M (rIdx M x)).1) (m * x.1) :=
    rEq_mul_left m ((rIdx_eq_iff _ _).1 (rIdx_rRep _))
  have hT : twoIdeal (m * (rRep M (rIdx M x)).1) = twoIdeal (m * x.1) :=
    twoIdeal_eq_of_rEq hR
  simp only [rowMap, rClassOf]
  by_cases hx : twoIdeal (m * x.1) = twoIdeal a
  · rw [dif_pos (hT.trans hx), dif_pos hx]
    exact congrArg some ((rIdx_eq_iff _ _).2 hR)
  · rw [dif_neg (fun hc => hx (hT.symm.trans hc)), dif_neg hx]

/-- **Representative independence, column side.** -/
theorem colMap_lIdx {a : M} (m : M) (x : JType M a) :
    colMap M m (lIdx M x) = lClassOf M a (x.1 * m) := by
  have hL : LEq ((lRep M (lIdx M x)).1 * m) (x.1 * m) :=
    lEq_mul_right m ((lIdx_eq_iff _ _).1 (lIdx_lRep _))
  have hT : twoIdeal ((lRep M (lIdx M x)).1 * m) = twoIdeal (x.1 * m) :=
    twoIdeal_eq_of_lEq hL
  simp only [colMap, lClassOf]
  by_cases hx : twoIdeal (x.1 * m) = twoIdeal a
  · rw [dif_pos (hT.trans hx), dif_pos hx]
    exact congrArg some ((lIdx_eq_iff _ _).2 hL)
  · rw [dif_neg (fun hc => hx (hT.symm.trans hc)), dif_neg hx]

/-! ## Identity and composition -/

@[simp] theorem rowMap_one {a : M} (i : RIdx M a) : rowMap M (1 : M) i = some i := by
  rw [rowMap, one_mul, rClassOf_eq_some (mem_jClass.1 (rRep M i).2), rIdx_rRep]

@[simp] theorem colMap_one {a : M} (l : LIdx M a) : colMap M (1 : M) l = some l := by
  rw [colMap, mul_one, lClassOf_eq_some (mem_jClass.1 (lRep M l).2), lIdx_lRep]

/-- **The row action composes as a left action**, with death absorbing. -/
theorem rowMap_mul {a : M} (m n : M) (i : RIdx M a) :
    rowMap M (m * n) i = (rowMap M n i).bind (rowMap M m) := by
  have hxJ : twoIdeal (rRep M i).1 = twoIdeal a := mem_jClass.1 (rRep M i).2
  have hL : rowMap M (m * n) i = rClassOf M a (m * (n * (rRep M i).1)) := by
    rw [rowMap, mul_assoc]
  have hR : rowMap M n i = rClassOf M a (n * (rRep M i).1) := rfl
  rw [hL, hR]
  by_cases h : twoIdeal (n * (rRep M i).1) = twoIdeal a
  · rw [rClassOf_eq_some h]
    exact (rowMap_rIdx m ⟨n * (rRep M i).1, mem_jClass.2 h⟩).symm
  · have hsub : twoIdeal (n * (rRep M i).1) ⊆ twoIdeal a := by
      rw [← hxJ]
      exact twoIdeal_subset_of_lLe (lLe_iff_exists.2 ⟨n, rfl⟩)
    rw [rClassOf_eq_none h]
    exact rClassOf_eq_none (twoIdeal_mul_left_ne hsub h m)

/-- **The column action composes as a right action**, with death absorbing. -/
theorem colMap_mul {a : M} (m n : M) (l : LIdx M a) :
    colMap M (m * n) l = (colMap M m l).bind (colMap M n) := by
  have hyJ : twoIdeal (lRep M l).1 = twoIdeal a := mem_jClass.1 (lRep M l).2
  have hL : colMap M (m * n) l = lClassOf M a ((lRep M l).1 * m * n) := by
    rw [colMap, ← mul_assoc]
  have hR : colMap M m l = lClassOf M a ((lRep M l).1 * m) := rfl
  rw [hL, hR]
  by_cases h : twoIdeal ((lRep M l).1 * m) = twoIdeal a
  · rw [lClassOf_eq_some h]
    exact (colMap_lIdx n ⟨(lRep M l).1 * m, mem_jClass.2 h⟩).symm
  · have hsub : twoIdeal ((lRep M l).1 * m) ⊆ twoIdeal a := by
      rw [← hyJ]
      exact twoIdeal_subset_of_rLe (rLe_iff_exists.2 ⟨m, rfl⟩)
    rw [lClassOf_eq_none h]
    exact lClassOf_eq_none (twoIdeal_mul_right_ne hsub h n)

/-- **Death is absorbing, row side** — the corollary the matrices consume. -/
theorem rowMap_bind_none {a : M} {m n : M} {i : RIdx M a} (h : rowMap M n i = none) :
    rowMap M (m * n) i = none := by
  rw [rowMap_mul, h]
  rfl

/-- **Death is absorbing, column side.** -/
theorem colMap_bind_none {a : M} {m n : M} {l : LIdx M a} (h : colMap M m l = none) :
    colMap M (m * n) l = none := by
  rw [colMap_mul, h]
  rfl

end PrincipalFactor

end MonoidProduct
