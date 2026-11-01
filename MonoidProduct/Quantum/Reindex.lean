import QuantumQueryComplexity.Quantum.Relabel
set_option linter.style.header false

/-!
# Renaming the query positions costs nothing

A bijection `e : ι ≃ ι'` of query positions renames the index register: the oracle answering
`a (e.symm i')` at position `i'` is the oracle for `a` with its positions renamed.  Transporting
an algorithm along the induced basis bijection `QBasis ι σ W ≃ QBasis ι' σ W`
(`indexRelabel`) costs no query.  Every step becomes a `submatrix` along the bijection, which
preserves unitarity, and the two oracles correspond (`oracleMap_indexRelabel`).

* `qQueryOn_reindex`: for every promise, output and error,

    `qQueryOn (fun x i' => read x (e.symm i')) f ε = qQueryOn read f ε`.

  It is an equality with no hypothesis: the two sets of achievable query counts coincide
  (`queryCounts_reindex`).  It is the position analogue of `qQueryOn_relabel` of
  QuantumQueryComplexity, which renames the answer alphabet.
* `qQueryOn_comp_eq_of_surjective`: pulling a problem back along a surjection of promise
  domains does not change its complexity.
* `qQuery_comp_reindex`: hence a total function, read through a bijection of positions, has
  the complexity of the original total function.
-/

namespace MonoidProduct

open QuantumQueryComplexity Matrix
open scoped Matrix

variable {ι ι' σ O W X : Type}

/-! ## The renamed basis and oracle -/

/-- A bijection of positions renames the index register. -/
def indexRelabel (e : ι ≃ ι') : QBasis ι σ W ≃ QBasis ι' σ W :=
  e.optionCongr.prodCongr (Equiv.refl _)

@[simp] theorem indexRelabel_apply (e : ι ≃ ι') (i : Option ι) (s : Option σ) (w : W) :
    indexRelabel (σ := σ) (W := W) e (i, s, w) = (i.map e, s, w) := rfl

section Oracle

variable [DecidableEq σ]

/-- **The renamed oracle is the oracle renamed.** -/
theorem oracleMap_indexRelabel (e : ι ≃ ι') (a : ι → σ) (p : QBasis ι σ W) :
    oracleMap (fun i' => a (e.symm i')) (indexRelabel e p) = indexRelabel e (oracleMap a p) := by
  obtain ⟨i, s, w⟩ := p
  cases i with
  | none => rfl
  | some i =>
      change (some (e i), Equiv.swap none (some (a (e.symm (e i)))) s, w)
        = (some (e i), Equiv.swap none (some (a i)) s, w)
      rw [Equiv.symm_apply_apply]

theorem oracleMap_indexRelabel_symm (e : ι ≃ ι') (a : ι → σ) (p : QBasis ι' σ W) :
    (indexRelabel e).symm (oracleMap (fun i' => a (e.symm i')) p)
      = oracleMap a ((indexRelabel e).symm p) := by
  conv_lhs => rw [show p = indexRelabel e ((indexRelabel e).symm p) from
    (Equiv.apply_symm_apply _ _).symm]
  rw [oracleMap_indexRelabel, Equiv.symm_apply_apply]

end Oracle

/-! ## The transported algorithm -/

variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- The algorithm `A`, run against the oracle with renamed positions. -/
def reindexAlg (e : ι ≃ ι') (A : QAlg ι σ O W) : QAlg ι' σ O W where
  init p := A.init ((indexRelabel e).symm p)
  init_isQState := by
    rw [IsQState, qNormSq_comp_equiv]
    exact A.init_isQState
  step t := (A.step t).submatrix (indexRelabel e).symm (indexRelabel e).symm
  step_unitary t := submatrix_mem_unitaryGroup _ (A.step_unitary t)
  readout p := A.readout ((indexRelabel e).symm p)

theorem reindexAlg_state (e : ι ≃ ι') (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    (reindexAlg e A).state (fun i' => a (e.symm i')) t
      = fun p => A.state a t ((indexRelabel e).symm p) := by
  induction t with
  | zero =>
      change (A.step 0).submatrix (indexRelabel e).symm (indexRelabel e).symm
          *ᵥ (fun p => A.init ((indexRelabel e).symm p)) = _
      rw [submatrix_mulVec_comp]
      rfl
  | succ t ih =>
      change (A.step (t + 1)).submatrix (indexRelabel e).symm (indexRelabel e).symm
          *ᵥ (oracleMat (fun i' => a (e.symm i'))
            *ᵥ (reindexAlg e A).state (fun i' => a (e.symm i')) t) = _
      rw [ih]
      have horacle : oracleMat (fun i' => a (e.symm i'))
            *ᵥ (fun p => A.state a t ((indexRelabel e).symm p))
          = fun p => (oracleMat a *ᵥ A.state a t) ((indexRelabel e).symm p) := by
        funext p
        rw [oracleMat_mulVec_apply, oracleMat_mulVec_apply, oracleMap_indexRelabel_symm]
      rw [horacle, submatrix_mulVec_comp]
      rfl

variable [DecidableEq O]

theorem computesWithErrorOn_reindex (e : ι ≃ ι') {A : QAlg ι σ O W} {q : ℕ}
    {read : X → ι → σ} {f : X → O} {ε : ℝ} (h : ComputesWithErrorOn A q read f ε) :
    ComputesWithErrorOn (reindexAlg e A) q (fun x i' => read x (e.symm i')) f ε := by
  intro x
  rw [QAlg.prob, reindexAlg_state]
  change 1 - ε ≤ qProb (fun p => A.readout ((indexRelabel e).symm p))
    (fun p => A.state (read x) q ((indexRelabel e).symm p)) (f x)
  rw [qProb_comp_equiv]
  exact h x

/-! ## Equal complexities -/

omit [Fintype W] [DecidableEq W] in
theorem queryCounts_subset_reindex (e : ι ≃ ι') (read : X → ι → σ) (f : X → O) (ε : ℝ) :
    QueryCounts read f ε ⊆ QueryCounts (fun x i' => read x (e.symm i')) f ε := by
  rintro q ⟨W', hW, hW', A, hA⟩
  exact ⟨W', hW, hW', reindexAlg e A, computesWithErrorOn_reindex e hA⟩

omit [Fintype W] [DecidableEq W] in
/-- Renaming the positions does not change the achievable query counts. -/
theorem queryCounts_reindex (e : ι ≃ ι') (read : X → ι → σ) (f : X → O) (ε : ℝ) :
    QueryCounts (fun x i' => read x (e.symm i')) f ε = QueryCounts read f ε := by
  refine Set.Subset.antisymm ?_ (queryCounts_subset_reindex e read f ε)
  have h := queryCounts_subset_reindex e.symm (fun x i' => read x (e.symm i')) f ε
  simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using h

omit [Fintype W] [DecidableEq W] in
/-- **Renaming the query positions is free**: for a bijection `e : ι ≃ ι'`, reading position
`i'` as position `e.symm i'` leaves the complexity unchanged, for every promise, output and
error. -/
theorem qQueryOn_reindex (e : ι ≃ ι') (read : X → ι → σ) (f : X → O) (ε : ℝ) :
    qQueryOn (fun x i' => read x (e.symm i')) f ε = qQueryOn read f ε := by
  rw [qQueryOn, qQueryOn, queryCounts_reindex]

omit [Fintype ι'] [DecidableEq ι'] [Fintype W] [DecidableEq W] in
/-- Pulling a problem back along a surjection of promise domains keeps the achievable query
counts: every promised input is the image of one. -/
theorem queryCounts_comp_eq_of_surjective {X' : Type} {E : X → X'}
    (hE : Function.Surjective E) (read' : X' → ι → σ) (g : X' → O) (ε : ℝ) :
    QueryCounts (fun x => read' (E x)) (fun x => g (E x)) ε = QueryCounts read' g ε := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro q ⟨W', hW, hW', A, hA⟩
    refine ⟨W', hW, hW', A, fun x' => ?_⟩
    obtain ⟨x, rfl⟩ := hE x'
    exact hA x
  · rintro q ⟨W', hW, hW', A, hA⟩
    exact ⟨W', hW, hW', A, fun x => hA (E x)⟩

omit [Fintype ι'] [DecidableEq ι'] [Fintype W] [DecidableEq W] in
/-- **A problem pulled back along a surjection** has the same complexity. -/
theorem qQueryOn_comp_eq_of_surjective {X' : Type} {E : X → X'}
    (hE : Function.Surjective E) (read' : X' → ι → σ) (g : X' → O) (ε : ℝ) :
    qQueryOn (fun x => read' (E x)) (fun x => g (E x)) ε = qQueryOn read' g ε := by
  rw [qQueryOn, qQueryOn, queryCounts_comp_eq_of_surjective hE]

omit [Fintype W] [DecidableEq W] in
/-- **Total functions read through a bijection of positions**: computing `g (y ∘ e.symm)` from
`y : ι → σ` costs exactly as much as computing `g` from its own input `ι' → σ`. -/
theorem qQuery_comp_reindex (e : ι ≃ ι') (g : (ι' → σ) → O) (ε : ℝ) :
    qQuery (fun y : ι → σ => g fun i' => y (e.symm i')) ε = qQuery g ε := by
  have hE : Function.Surjective fun (y : ι → σ) (i' : ι') => y (e.symm i') := fun z =>
    ⟨fun i => z (e i), funext fun i' => by simp⟩
  have h1 := qQueryOn_reindex e (id : (ι → σ) → ι → σ) (fun y => g fun i' => y (e.symm i')) ε
  have h2 := qQueryOn_comp_eq_of_surjective hE (id : (ι' → σ) → ι' → σ) g ε
  exact h1.symm.trans h2

end MonoidProduct
