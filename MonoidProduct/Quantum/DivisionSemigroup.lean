import QuantumQueryComplexity.Quantum.AlphabetSimulation
import QuantumQueryComplexity.Quantum.ReadAll
import QuantumQueryComplexity.Quantum.Relabel
import MonoidProduct.Aperiodic.Semigroup
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Division monotonicity for finite **semigroups**

`monoid.tex` states the division proposition for arbitrary semigroups:
`M ≺ S` when there are a subsemigroup `T ⊆ S` and a surjective homomorphism
`T ↠ M`.  `Quantum/Division.lean` proves the finite-**monoid** case; this
file is the semigroup version, on `semigroupProd n` — the ordered product of
a word of length `n + 1`.

Indexing by `Fin (n + 1)` is what makes the semigroup case *simpler* than the
monoid one rather than harder: every word is nonempty by construction, so the
positive-length hypothesis that the monoid theorems carry (`1 ≤ n`, there to
keep the empty product `1` out of `T`) disappears entirely.

The route is unchanged, and in particular the factor is still **two**, not
four: one section `ψ₀ : M → T`, included into `S`, gives a single map
`M → S`; that one map is compiled by the two-query section lookup
(`qQueryOn_alphabetMap_le`), and the answer is projected back by an arbitrary
total extension of `φ` (`extendHomS`), which is free
(`qQueryOn_postcomp_le`).  Correctness is closure: a nonempty word of
`T`-letters has its product in `T` (`semigroupProd_mem`), and there the
extension *is* `φ` (`extendHomS_semigroupProd`).

`[Nonempty M]` appears because extending `φ` off `T` needs a junk value and a
semigroup has no `1` to use.

**Model scope**: every `Q` here is the project's **native
transposition-oracle** complexity.  Conventional-oracle equivalence is
formalized for Boolean alphabets via the XOR oracle
(`Quantum/Simulation.lean`) and for arbitrary finite alphabets via the
canonical one-hot XOR model (`Quantum/OneHotSimulation.lean`, a direct
factor two each way; headlines transported in
`Quantum/OneHotApplications.lean`), so these native statements carry over
at a factor of two.

This file is a **cross-stream integration target** — it reaches both the
quantum layer and the classical `Aperiodic` cone — so it sits outside the
`QuantumQueryComplexity.Quantum` aggregate and CI builds it explicitly.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix
open scoped Classical

variable {M S : Type} [Semigroup M] [Fintype M] [DecidableEq M]
  [Semigroup S] [Fintype S] [DecidableEq S]

/-! ## Homomorphisms and the nonempty ordered product -/

/-- **A homomorphism commutes with the nonempty ordered product.** -/
theorem map_semigroupProd (φ : S →ₙ* M) :
    ∀ (n : ℕ) (x : Fin (n + 1) → S),
      φ (semigroupProd n x) = semigroupProd n fun i => φ (x i)
  | 0, x => rfl
  | n + 1, x => by
      show φ (semigroupProd n (fun i => x i.castSucc) * x (Fin.last (n + 1)))
        = semigroupProd n (fun i => φ (x i.castSucc)) * φ (x (Fin.last (n + 1)))
      rw [map_mul, map_semigroupProd φ n fun i => x i.castSucc]

/-- **Closure**: a nonempty word of `T`-letters has its product in `T`. -/
theorem semigroupProd_mem (T : Subsemigroup S) :
    ∀ (n : ℕ) (v : Fin (n + 1) → S), (∀ i, v i ∈ T) → semigroupProd n v ∈ T
  | 0, v, hv => hv 0
  | n + 1, v, hv => by
      show semigroupProd n (fun i => v i.castSucc) * v (Fin.last (n + 1)) ∈ T
      exact mul_mem (semigroupProd_mem T n _ fun i => hv _) (hv _)

/-! ## Extending the homomorphism off the subsemigroup -/

open Classical in
/-- An arbitrary total extension of `φ` to `S`.  A semigroup has no `1`, so
the junk value comes from `[Nonempty M]`.  Its value is irrelevant: every
*correct* product lies in `T`, and an outcome outside `T` is one the
algorithm already got wrong. -/
noncomputable def extendHomS [Nonempty M] (T : Subsemigroup S) (φ : T →ₙ* M) :
    S → M :=
  fun s => if h : s ∈ T then φ ⟨s, h⟩ else Classical.arbitrary M

lemma extendHomS_of_mem [Nonempty M] {T : Subsemigroup S} (φ : T →ₙ* M) {s : S}
    (h : s ∈ T) : extendHomS T φ s = φ ⟨s, h⟩ := by
  classical
  rw [extendHomS, dif_pos h]

/-- **On a word of `T`-letters the extension computes `φ` letterwise.** -/
theorem extendHomS_semigroupProd [Nonempty M] (T : Subsemigroup S)
    (φ : T →ₙ* M) :
    ∀ (n : ℕ) (v : Fin (n + 1) → S) (hv : ∀ i, v i ∈ T) (u : Fin (n + 1) → M),
      (∀ i, φ ⟨v i, hv i⟩ = u i) →
      extendHomS T φ (semigroupProd n v) = semigroupProd n u
  | 0, v, hv, u, hu => by
      show extendHomS T φ (v 0) = u 0
      rw [extendHomS_of_mem φ (hv 0)]
      exact hu 0
  | n + 1, v, hv, u, hu => by
      have hA : semigroupProd n (fun i => v i.castSucc) ∈ T :=
        semigroupProd_mem T n _ fun i => hv _
      have hb : v (Fin.last (n + 1)) ∈ T := hv _
      show extendHomS T φ (semigroupProd n (fun i => v i.castSucc)
          * v (Fin.last (n + 1)))
        = semigroupProd n (fun i => u i.castSucc) * u (Fin.last (n + 1))
      rw [extendHomS_of_mem φ (mul_mem hA hb),
        show (⟨semigroupProd n (fun i => v i.castSucc) * v (Fin.last (n + 1)),
            mul_mem hA hb⟩ : T) = (⟨_, hA⟩ : T) * ⟨_, hb⟩ from rfl, map_mul,
        ← extendHomS_of_mem φ hA,
        extendHomS_semigroupProd T φ n (fun i => v i.castSucc)
          (fun i => hv _) (fun i => u i.castSucc) (fun i => hu _)]
      congr 1
      exact hu _

/-! ## The division bound -/

variable {X : Type} [Fintype X]

/-- **Division monotonicity for semigroups**, the paper's `M ≺ S`: a
subsemigroup `T ⊆ S` with a section `ψ` of a homomorphism `φ : T →ₙ* M` makes
the `M`-product cost at most **twice** the `S`-product.  No positive-length
hypothesis: `semigroupProd n` is a product of `n + 1` letters. -/
theorem qQueryOn_semigroupProd_le_of_division [Nonempty M] {n : ℕ}
    (T : Subsemigroup S) (φ : T →ₙ* M) (ψ : M → T) (hsec : ∀ m, φ (ψ m) = m)
    (read : X → Fin (n + 1) → M) {ε : ℝ}
    (hne : (QueryCounts (fun x i => ((ψ (read x i) : S)))
      (fun x => semigroupProd n fun i => ((ψ (read x i) : S))) ε).Nonempty) :
    qQueryOn read (fun x => semigroupProd n (read x)) ε
      ≤ 2 * qQueryOn (fun x i => ((ψ (read x i) : S)))
          (fun x => semigroupProd n fun i => ((ψ (read x i) : S))) ε := by
  have hEq : (fun x => semigroupProd n (read x))
      = fun x => extendHomS T φ
        (semigroupProd n fun i => ((ψ (read x i) : S))) := by
    funext x
    rw [extendHomS_semigroupProd T φ n (fun i => ((ψ (read x i) : S)))
      (fun i => (ψ (read x i)).2) (read x) fun i => hsec (read x i)]
  rw [hEq]
  refine le_trans (qQueryOn_alphabetMap_le (fun m => ((ψ m : S))) read _
    (hne.mono (queryCounts_postcomp (extendHomS T φ) _ _ ε))) ?_
  exact Nat.mul_le_mul_left 2 (qQueryOn_postcomp_le (extendHomS T φ) hne)

/-- **The honest total form**: `Q_ε(Prod_M) ≤ 2·Q_ε(Prod_S)` for the
semigroup products of `n + 1` letters. -/
theorem qQuery_semigroupProd_le_of_division [Nonempty M] [Nonempty S] {n : ℕ}
    (T : Subsemigroup S) (φ : T →ₙ* M) (ψ : M → T) (hsec : ∀ m, φ (ψ m) = m)
    {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun w : Fin (n + 1) → M => semigroupProd n w) ε
      ≤ 2 * qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) ε := by
  have hStot : (QueryCounts (X := Fin (n + 1) → S) id
      (fun w => semigroupProd n w) ε).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [show x = y from h]) hε
  refine le_trans (qQueryOn_semigroupProd_le_of_division T φ ψ hsec
    (X := Fin (n + 1) → M) id
    (hStot.mono (queryCounts_subset_of_read _ _ ε))) ?_
  exact Nat.mul_le_mul_left 2
    (qQueryOn_comp_read_le_qQuery
      (fun w : Fin (n + 1) → M => fun i => ((ψ (w i) : S)))
      (fun v : Fin (n + 1) → S => semigroupProd n v) hStot)

/-- The surjectivity wrapper: the section is only used through `φ`. -/
theorem qQuery_semigroupProd_le_of_surjective [Nonempty M] [Nonempty S]
    {n : ℕ} (T : Subsemigroup S) (φ : T →ₙ* M) (hφ : Function.Surjective φ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun w : Fin (n + 1) → M => semigroupProd n w) ε
      ≤ 2 * qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) ε := by
  choose ψ hψ using hφ
  exact qQuery_semigroupProd_le_of_division T φ ψ hψ hε

/-! ### The allowed-alphabet form

As in the monoid case this costs **factor one**: both problems query the same
label oracle and only the interpretation of the labels differs, so nothing is
simulated.  Only a `T`-representative per allowed letter is needed — no
section on all of `M`. -/

theorem qQueryOn_semigroupProd_le_of_division_letters [Nonempty M]
    {σ : Type} [Fintype σ] [DecidableEq σ] {n : ℕ} (T : Subsemigroup S)
    (φ : T →ₙ* M) (letterS : σ → S) (letterM : σ → M)
    (hmem : ∀ a, letterS a ∈ T)
    (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a)
    (read : X → Fin (n + 1) → σ) {ε : ℝ}
    (hne : (QueryCounts read
      (fun x => semigroupProd n fun i => letterS (read x i)) ε).Nonempty) :
    qQueryOn read (fun x => semigroupProd n fun i => letterM (read x i)) ε
      ≤ qQueryOn read
          (fun x => semigroupProd n fun i => letterS (read x i)) ε := by
  have hEq : (fun x => semigroupProd n fun i => letterM (read x i))
      = fun x => extendHomS T φ
        (semigroupProd n fun i => letterS (read x i)) := by
    funext x
    rw [extendHomS_semigroupProd T φ n (fun i => letterS (read x i))
      (fun i => hmem (read x i)) (fun i => letterM (read x i))
      fun i => hφ (read x i)]
  rw [hEq]
  exact qQueryOn_postcomp_le (extendHomS T φ) hne

/-- **The clause with the two oracle alphabets named separately.**  The left
side queries the `σ` oracle, the right side the relabelled `σ'` oracle;
renaming costs zero queries (`qQueryOn_relabel`). -/
theorem qQueryOn_semigroupProd_le_of_division_relabel [Nonempty M] [Nonempty S]
    {σ σ' : Type} [Fintype σ] [DecidableEq σ] [Fintype σ'] [DecidableEq σ']
    {n : ℕ} (T : Subsemigroup S) (φ : T →ₙ* M) (e : σ ≃ σ')
    (letterS : σ → S) (letterM : σ → M) (hmem : ∀ a, letterS a ∈ T)
    (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a)
    (read : X → Fin (n + 1) → σ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn read (fun x => semigroupProd n fun i => letterM (read x i)) ε
      ≤ qQueryOn (fun x i => e (read x i))
          (fun x => semigroupProd n fun i => letterS (read x i)) ε := by
  have hneS : (QueryCounts read
      (fun x => semigroupProd n fun i => letterS (read x i)) ε).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [h]) hε
  rw [qQueryOn_relabel e read _ hneS]
  exact qQueryOn_semigroupProd_le_of_division_letters T φ letterS letterM hmem
    hφ read hneS

/-- Its total form: `Prod_M` over `σⁿ⁺¹` against `Prod_S` over `σ'ⁿ⁺¹`. -/
theorem qQuery_semigroupProd_le_of_division_relabel [Nonempty M] [Nonempty S]
    {σ σ' : Type} [Fintype σ] [DecidableEq σ] [Fintype σ'] [DecidableEq σ']
    {n : ℕ} (T : Subsemigroup S) (φ : T →ₙ* M) (e : σ ≃ σ')
    (letterS : σ → S) (letterM : σ → M) (hmem : ∀ a, letterS a ∈ T)
    (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin (n + 1) → σ =>
        semigroupProd n fun i => letterM (x i)) ε
      ≤ qQuery (fun y : Fin (n + 1) → σ' =>
          semigroupProd n fun i => letterS (e.symm (y i))) ε := by
  refine le_trans (qQueryOn_semigroupProd_le_of_division_relabel T φ e letterS
    letterM hmem hφ (X := Fin (n + 1) → σ) id hε) ?_
  simp only [id_eq]
  have hEq : (fun x : Fin (n + 1) → σ =>
        semigroupProd n fun i => letterS (x i))
      = fun x : Fin (n + 1) → σ =>
        semigroupProd n fun i => letterS (e.symm (e (x i))) := by
    funext x
    exact congrArg (semigroupProd n)
      (funext fun i => by rw [Equiv.symm_apply_apply])
  rw [hEq]
  exact qQueryOn_comp_read_le_qQuery
    (fun x : Fin (n + 1) → σ => fun i => e (x i))
    (fun y : Fin (n + 1) → σ' => semigroupProd n fun i => letterS (e.symm (y i)))
    (queryCounts_nonempty (X := Fin (n + 1) → σ')
      (fun x y h => by rw [show x = y from h]) hε)

/-- Its total form. -/
theorem qQuery_semigroupProd_le_of_division_letters [Nonempty M]
    {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ] {n : ℕ}
    (T : Subsemigroup S) (φ : T →ₙ* M) (letterS : σ → S) (letterM : σ → M)
    (hmem : ∀ a, letterS a ∈ T)
    (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin (n + 1) → σ =>
        semigroupProd n fun i => letterM (x i)) ε
      ≤ qQuery (fun x : Fin (n + 1) → σ =>
          semigroupProd n fun i => letterS (x i)) ε := by
  have : Nonempty S := ⟨letterS (Classical.arbitrary σ)⟩
  exact qQueryOn_semigroupProd_le_of_division_letters T φ letterS letterM hmem
    hφ (X := Fin (n + 1) → σ) id
    (queryCounts_nonempty (fun x y h => by rw [show x = y from h]) hε)

end MonoidProduct
