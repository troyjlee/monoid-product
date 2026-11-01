import QuantumQueryComplexity.Quantum.AlphabetSimulation
set_option linter.style.header false

/-!
# Simulating a position-dependent alphabet map

Let `lift : ι → σ → τ` be any family of maps between finite alphabets, one for each query
position; none of them needs to be injective.  An algorithm for the `τ`-oracle, which answers
`lift i (read x i)` at position `i`, runs against the `σ`-oracle, which answers `read x i`, at
**two `σ`-queries per `τ`-query** (`qQueryOn_positionAlphabetMap_le`):

    query σ  →  write `lift i` of the answer into a τ-register  →  query σ again

The middle step (`posLiftSwapMat`) reads the index register and the `σ`-answer register,
both already set, so it is input-independent.  The second query is the uncompute that returns
the `σ`-answer register to blank.

This is `qQueryOn_alphabetMap_le` of QuantumQueryComplexity, whose lookup `lift : σ → τ` does
not see the position.  Only the middle step changes (`posLiftSwapMap`).  The embedding of the
simulated states (`embedAnswer`), the lifted steps (`kronLift basisEquiv`) and the readout
(`qProb_embedAnswer`) are reused from that file.
-/

namespace MonoidProduct

open QuantumQueryComplexity Matrix
open scoped Matrix

variable {ι σ τ W : Type}

/-! ## The middle step: writing `lift i` into the `τ`-register -/

/-- The transposition of the `τ`-register: `⊥ ↔ some (lift i s)` when the index register holds
`some i` and the `σ`-answer register holds `some s`, and the identity otherwise. -/
def posLiftSwap [DecidableEq τ] (lift : ι → σ → τ) : Option ι → Option σ → Equiv.Perm (Option τ)
  | some i, some s => Equiv.swap none (some (lift i s))
  | _, _ => Equiv.refl _

theorem posLiftSwap_self [DecidableEq τ] (lift : ι → σ → τ) (i : Option ι) (s : Option σ)
    (t : Option τ) : posLiftSwap lift i s (posLiftSwap lift i s t) = t := by
  cases i <;> cases s <;> simp [posLiftSwap]

/-- The middle step on basis states: `posLiftSwap` on the `τ`-register, controlled by the index
and `σ`-answer registers, which it leaves alone. -/
def posLiftSwapMap [DecidableEq τ] (lift : ι → σ → τ) (p : QBasis ι σ (Option τ × W)) :
    QBasis ι σ (Option τ × W) :=
  (p.1, p.2.1, posLiftSwap lift p.1 p.2.1 p.2.2.1, p.2.2.2)

theorem posLiftSwapMap_involutive [DecidableEq τ] (lift : ι → σ → τ) :
    Function.Involutive (posLiftSwapMap (W := W) lift) := by
  rintro ⟨i, s, t, w⟩
  simp only [posLiftSwapMap, posLiftSwap_self]

section Oracle

variable [DecidableEq σ] [DecidableEq τ]

/-- **The `σ`-answer register comes back blank**: the two oracle calls cancel on it, because the
middle step leaves it and the index register alone. -/
theorem posGadget_snd (lift : ι → σ → τ) (a : ι → σ) (p : QBasis ι σ (Option τ × W)) :
    (oracleMap a (posLiftSwapMap lift (oracleMap a p))).2.1 = p.2.1 := by
  obtain ⟨i, s, t, w⟩ := p
  cases i with
  | none => rfl
  | some i =>
      change Equiv.swap none (some (a i)) (Equiv.swap none (some (a i)) s) = s
      exact Equiv.swap_apply_self _ _ _

/-- **On a blank `σ`-answer register the gadget performs the simulated query**, with the lookup
`lift i` at the queried position `i`. -/
theorem posGadget_blank (lift : ι → σ → τ) (a : ι → σ) (i : Option ι) (t : Option τ) (w : W) :
    oracleMap a (posLiftSwapMap lift
        (oracleMap a ((i, none, t, w) : QBasis ι σ (Option τ × W))))
      = ((oracleMap (fun j => lift j (a j)) ((i, t, w) : QBasis ι τ W)).1, none,
          (oracleMap (fun j => lift j (a j)) ((i, t, w) : QBasis ι τ W)).2.1,
          (oracleMap (fun j => lift j (a j)) ((i, t, w) : QBasis ι τ W)).2.2) := by
  cases i with
  | none => rfl
  | some i =>
      change (some i, Equiv.swap none (some (a i)) (some (a i)),
          posLiftSwap lift (some i) (Equiv.swap none (some (a i)) none) t, w)
        = (some i, none, Equiv.swap none (some (lift i (a i))) t, w)
      rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
      rfl

end Oracle

section Gadget

variable [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  [Fintype W] [DecidableEq W]

/-- The middle step as a permutation matrix. -/
noncomputable def posLiftSwapMat (lift : ι → σ → τ) :
    Matrix (QBasis ι σ (Option τ × W)) (QBasis ι σ (Option τ × W)) ℂ :=
  qPerm (posLiftSwapMap_involutive (W := W) lift).toPerm

theorem posLiftSwapMat_mulVec_apply (lift : ι → σ → τ) (ψ : QBasis ι σ (Option τ × W) → ℂ)
    (p : QBasis ι σ (Option τ × W)) :
    (posLiftSwapMat lift *ᵥ ψ) p = ψ (posLiftSwapMap lift p) := by
  rw [posLiftSwapMat, qPerm_mulVec_apply]
  rfl

theorem posLiftSwapMat_mem_unitaryGroup (lift : ι → σ → τ) :
    posLiftSwapMat (W := W) lift ∈ Matrix.unitaryGroup (QBasis ι σ (Option τ × W)) ℂ :=
  qPerm_mem_unitaryGroup _

/-- **The gadget on embedded states**: two `σ`-queries with the position-dependent lookup in
between act as one `τ`-query. -/
theorem posGadget_mulVec (lift : ι → σ → τ) (a : ι → σ) (ψ : QBasis ι τ W → ℂ) :
    oracleMat a *ᵥ (posLiftSwapMat lift *ᵥ (oracleMat a *ᵥ embedAnswer (σ := σ) ψ))
      = embedAnswer (σ := σ) (oracleMat (fun j => lift j (a j)) *ᵥ ψ) := by
  funext p
  rw [oracleMat_mulVec_apply, posLiftSwapMat_mulVec_apply, oracleMat_mulVec_apply]
  obtain ⟨i, s, t, w⟩ := p
  cases s with
  | some s =>
      -- the `σ`-answer register is not blank on either side, so both sides vanish
      have hs : (oracleMap a (posLiftSwapMap lift
          (oracleMap a ((i, some s, t, w) : QBasis ι σ (Option τ × W))))).2.1 = some s :=
        posGadget_snd lift a _
      rw [embedAnswer_eq, embedAnswer_eq, hs, blankAnswer_some, mul_zero]
      exact (mul_zero _).symm
  | none =>
      rw [posGadget_blank, embedAnswer_apply, embedAnswer_apply, oracleMat_mulVec_apply]

/-! ## The compiled routine -/

/-- **The compiled routine**: each of `R`'s steps is carried over by `kronLift`, and each of its
queries becomes the two-query gadget. -/
noncomputable def posMapAlphabet (lift : ι → σ → τ) (R : QRoutine ι τ W) :
    QRoutine ι σ (Option τ × W) where
  len := 2 * R.len
  step t := if t % 2 = 1 then posLiftSwapMat lift else kronLift basisEquiv (R.step (t / 2))
  step_unitary t := by
    by_cases h : t % 2 = 1
    · rw [ite_eq_left h]
      exact posLiftSwapMat_mem_unitaryGroup lift
    · rw [ite_eq_right h]
      exact kronLift_mem_unitaryGroup _ (R.step_unitary _)

theorem posMapAlphabet_step_even (lift : ι → σ → τ) (R : QRoutine ι τ W) (j : ℕ) :
    (posMapAlphabet lift R).step (2 * j) = kronLift basisEquiv (R.step j) := by
  change (if (2 * j) % 2 = 1 then posLiftSwapMat lift
      else kronLift basisEquiv (R.step ((2 * j) / 2))) = _
  rw [ite_eq_right (by omega), show 2 * j / 2 = j by omega]

theorem posMapAlphabet_step_odd (lift : ι → σ → τ) (R : QRoutine ι τ W) (j : ℕ) :
    (posMapAlphabet lift R).step (2 * j + 1) = posLiftSwapMat lift := by
  change (if (2 * j + 1) % 2 = 1 then posLiftSwapMat lift
      else kronLift basisEquiv (R.step ((2 * j + 1) / 2))) = _
  rw [ite_eq_left (by omega)]

/-- **The compiled routine runs as the original**, on embedded states. -/
theorem posMapAlphabet_runUpto (lift : ι → σ → τ) (R : QRoutine ι τ W) (a : ι → σ)
    (ψ : QBasis ι τ W → ℂ) (t : ℕ) :
    (posMapAlphabet lift R).runUpto a (2 * t) *ᵥ embedAnswer (σ := σ) ψ
      = embedAnswer (σ := σ) (R.runUpto (fun j => lift j (a j)) t *ᵥ ψ) := by
  induction t with
  | zero =>
      rw [Nat.mul_zero, QRoutine.runUpto_zero, QRoutine.runUpto_zero,
        show (posMapAlphabet lift R).step 0 = kronLift basisEquiv (R.step 0) by
          simpa using posMapAlphabet_step_even lift R 0,
        embedAnswer, embedAnswer, kronLift_mulVec_splitVec]
  | succ t ih =>
      have hstep : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
      rw [hstep, QRoutine.runUpto_succ, QRoutine.runUpto_succ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        posMapAlphabet_step_odd lift R t, posGadget_mulVec,
        show (2 * t + 1) + 1 = 2 * (t + 1) by omega,
        posMapAlphabet_step_even lift R (t + 1),
        embedAnswer, embedAnswer, kronLift_mulVec_splitVec,
        QRoutine.runUpto_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end Gadget

/-! ## The algorithm level -/

variable [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  {O X : Type} [DecidableEq O]

/-- **The simulation at the algorithm level**: an algorithm for the `τ`-oracle
`fun i => lift i (read x i)` becomes an algorithm for the `σ`-oracle of twice the length, with
the same error and the same function. -/
theorem computesWithErrorOn_posMapAlphabet [Fintype W] [DecidableEq W] (lift : ι → σ → τ)
    {A : QAlg ι τ O W} {q : ℕ} {read : X → ι → σ} {f : X → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q (fun x i => lift i (read x i)) f ε) :
    ComputesWithErrorOn
      ((posMapAlphabet lift (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedAnswer (σ := σ) A.init) (isQState_embedAnswer A.init_isQState)
        (fun p => A.readout (basisEquiv p).1))
      (2 * q) read f ε := by
  intro x
  have hstate := QRoutine.toAlg_state
    (posMapAlphabet lift (QRoutine.mk q A.step A.step_unitary))
    (embedAnswer (σ := σ) A.init) (isQState_embedAnswer A.init_isQState)
    (fun p => A.readout (basisEquiv p).1) (read x) (2 * q)
  rw [QAlg.prob, hstate, posMapAlphabet_runUpto]
  change 1 - ε ≤ qProb (fun p : QBasis ι σ (Option τ × W) => A.readout (basisEquiv p).1)
    (embedAnswer (σ := σ) ((QRoutine.mk q A.step A.step_unitary).runUpto
      (fun j => lift j (read x j)) q *ᵥ A.init)) (f x)
  rw [qProb_embedAnswer, ← state_eq_runUpto2 A q]
  exact h x

/-- **The position-dependent alphabet-simulation bound**: for any maps `lift i : σ → τ`, one per
position and not necessarily injective, computing `f` against the `σ`-oracle costs at most twice
computing it against the `τ`-oracle that answers `lift i (read x i)` at position `i`. -/
theorem qQueryOn_positionAlphabetMap_le [Finite X] (lift : ι → σ → τ) (read : X → ι → σ)
    (f : X → O) {ε : ℝ} (hne : (QueryCounts (fun x i => lift i (read x i)) f ε).Nonempty) :
    qQueryOn read f ε ≤ 2 * qQueryOn (fun x i => lift i (read x i)) f ε := by
  have := Fintype.ofFinite X
  obtain ⟨W', hW1, hW2, A, hA⟩ := exists_computes_qQueryOn hne
  exact qQueryOn_le (computesWithErrorOn_posMapAlphabet lift hA)

end MonoidProduct
