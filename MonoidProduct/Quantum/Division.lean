import QuantumQueryComplexity.Quantum.AlphabetSimulation
import QuantumQueryComplexity.Quantum.ReadAll
import QuantumQueryComplexity.Quantum.Relabel
import MonoidProduct.Aperiodic.EqProd
import MonoidProduct.Aperiodic.Division
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Division monotonicity for the product problem

**This file is a cross-stream integration target**: it imports both the
quantum layer and the classical `Aperiodic` cone, so it deliberately sits
*outside* the `QuantumQueryComplexity.Quantum` aggregate.  CI builds it explicitly:
`lake build QuantumQueryComplexity.Quantum.Division`.

The paper's division is `M ≺ S`: there is a **subsemigroup** `T ⊆ S` and a
surjective homomorphism `T ↠ M`.  On nonempty words this costs a factor
**two**, not four, and the reason is that only one alphabet map is ever
compiled:

1. choose a section `ψ₀ : M → T` of `φ` (nonempty words only — the empty
   product is `1`, which a subsemigroup need not contain);
2. include it into `S`, giving the single map `ψ : M → S`;
3. compile *that* map with the two-query section lookup
   (`qQueryOn_alphabetMap_le`) — this is the only simulation;
4. run the total `S`-product algorithm on the lifted word;
5. postprocess its output with an arbitrary total extension `S → M` of `φ`
   (`extendHom`), which is free (`qQueryOn_postcomp_le`).

Closure of `T` makes step 5 correct: the lifted letters lie in `T`, so their
ordered product does too (`rangeProd_mem_of_forall_mem`), and there
`extendHom` *is* `φ` (`extendHom_rangeProd_of`).  Compiling `M → T` and
`T → S` separately would cost four.

Headlines: `qQueryOn_prodFun_le_of_division` on any promise,
`qQuery_prodFun_le_of_division : Q_ε(Prod_M) ≤ 2·Q_ε(Prod_S)` for the honest
total products, and the monoid-quotient special case
`qQueryOn_prodFun_le_of_section`.

There is also an **allowed-alphabet** form
(`qQueryOn_wordProd_le_of_division_letters`), which costs **factor one**:
there both problems query the same label oracle and only the interpretation
of the labels differs, so nothing is simulated.  Labels may be renamed
freely — `qQueryOn_relabel` (`Quantum/Relabel.lean`) makes a bijective
relabelling of the answer alphabet cost **zero** queries — so presenting the
allowed letters through a common abstract label type is without loss of
generality; `qQueryOn_wordProd_le_of_division_relabel` and its total form
`qQuery_wordProd_le_of_division_relabel` state the clause with the `σ` oracle
on the left and the relabelled `σ'` oracle on the right.

Scope: finite alphabets and finite **monoids** `M`, `S`, with `n ≥ 1`.  The
arbitrary-**semigroup** proposition of the paper
(`prop:division-monotonicity`) is proved in
`Quantum/DivisionSemigroup.lean`, on `semigroupProd n`, where indexing by
`Fin (n + 1)` removes the positive-length hypothesis.

**Model scope**: every `Q` here is the project's **native
transposition-oracle** complexity.  Conventional-oracle equivalence is
formalized for Boolean alphabets via the XOR oracle
(`Quantum/Simulation.lean`) and for arbitrary finite alphabets via the
canonical one-hot XOR model (`Quantum/OneHotSimulation.lean`, a direct
factor two each way); the headline products are transported in
`Quantum/OneHotApplications.lean`.

The 𝓙-trivial corollary needs, besides this transfer, (i) the formal
`UT_k(𝔹)` construction with its sharp product bound (`UT/*`), (ii) an
output-uniform quantum upper bound — a general-output extraction would
contribute `√|σ|` = `2^Θ(k²)` for the Boolean-matrix alphabet, and the
cardinality-free extraction removes that factor
(`Quantum/UniformExtraction.lean`) — and (iii) Simon's theorem (`Simon/*`).
The unconditional corollary is `jtrivial_qQuery_le_min` in
`Quantum/Applications.lean`.
The transfer half proved here (`qQuery_prodFun_le_of_division`) is what
that corollary consumes.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix

variable {M N : Type} [Monoid M] [Fintype M] [DecidableEq M]
  [Monoid N] [Fintype N] [DecidableEq N]

/-! ## Homomorphisms and the ordered product

`map_padAt`, `map_rangeProd` and `map_orderedProd` live in
`Aperiodic/EqProd.lean`, and `map_wordProd_section`, the
`extendHom` block, and the certificate-level transports in
`Aperiodic/Division.lean`: all pure monoid facts the
classical side needs. -/

/-! ## The division bound -/

variable {X : Type} [Fintype X]

/-- **Division monotonicity**: with a homomorphism `φ : N →* M` admitting a
section `ψ`, the `M`-product on any promise costs at most **twice** the
`N`-product on the lifted promise.  `ψ` need not be injective, and `φ` need
not be surjective anywhere except on the image of `ψ`. -/
theorem qQueryOn_prodFun_le_of_section {n : ℕ} (φ : N →* M) (ψ : M → N)
    (hsec : ∀ m, φ (ψ m) = m) (read : X → Fin n → M) {ε : ℝ}
    (hne : (QueryCounts (fun x i => ψ (read x i))
      (fun x => wordProd (id : N → N) (fun j => ψ (read x j))) ε).Nonempty) :
    qQueryOn read (fun x => wordProd (id : M → M) (read x)) ε
      ≤ 2 * qQueryOn (fun x i => ψ (read x i))
          (fun x => wordProd (id : N → N) (fun j => ψ (read x j))) ε := by
  have hEq : (fun x => wordProd (id : M → M) (read x))
      = fun x => φ (wordProd (id : N → N) (fun j => ψ (read x j))) := by
    funext x
    rw [map_wordProd_section φ ψ hsec (read x)]
  rw [hEq]
  refine le_trans (qQueryOn_alphabetMap_le ψ read _
    (hne.mono (queryCounts_postcomp (fun m => φ m) _ _ ε))) ?_
  exact Nat.mul_le_mul_left 2 (qQueryOn_postcomp_le (fun m => φ m) hne)

/-! ## Division by a subsemigroup

`M ≺ S`: a subsemigroup `T ⊆ S` and a surjective homomorphism `φ : T ↠ M`. -/

section Subsemigroup

variable {S : Type} [Monoid S] [Fintype S] [DecidableEq S]

variable {X : Type} [Fintype X]

/-- **Division monotonicity, the paper's `M ≺ S`**: a subsemigroup `T ⊆ S`
with a section `ψ` of a surjective homomorphism `φ : T ↠ M` makes the
`M`-product cost at most **twice** the `S`-product, on any promise and for
nonempty words.  Only the single map `M → S` is ever simulated. -/
theorem qQueryOn_prodFun_le_of_division {n : ℕ} (hn : 1 ≤ n)
    (T : Subsemigroup S) (φ : T →ₙ* M) (ψ : M → T)
    (hsec : ∀ m, φ (ψ m) = m) (read : X → Fin n → M) {ε : ℝ}
    (hne : (QueryCounts (fun x i => ((ψ (read x i) : S)))
      (fun x => wordProd (id : S → S)
        (fun i => ((ψ (read x i) : S)))) ε).Nonempty) :
    qQueryOn read (fun x => wordProd (id : M → M) (read x)) ε
      ≤ 2 * qQueryOn (fun x i => ((ψ (read x i) : S)))
          (fun x => wordProd (id : S → S)
            (fun i => ((ψ (read x i) : S)))) ε := by
  have hEq : (fun x => wordProd (id : M → M) (read x))
      = fun x => extendHom T φ (wordProd (id : S → S)
          (fun i => ((ψ (read x i) : S)))) := by
    funext x
    rw [extendHom_wordProd T φ ψ hsec hn (read x)]
  rw [hEq]
  refine le_trans (qQueryOn_alphabetMap_le (fun m => ((ψ m : S))) read _
    (hne.mono (queryCounts_postcomp (extendHom T φ) _ _ ε))) ?_
  exact Nat.mul_le_mul_left 2 (qQueryOn_postcomp_le (extendHom T φ) hne)

/-- **The honest total form**: `Q_ε(Prod_M) ≤ 2·Q_ε(Prod_S)` whenever
`M ≺ S`, for nonempty words. -/
theorem qQuery_prodFun_le_of_division {n : ℕ} (hn : 1 ≤ n)
    (T : Subsemigroup S) (φ : T →ₙ* M) (ψ : M → T)
    (hsec : ∀ m, φ (ψ m) = m) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun w : Fin n → M => wordProd (id : M → M) w) ε
      ≤ 2 * qQuery (fun w : Fin n → S => wordProd (id : S → S) w) ε := by
  have : Nonempty S := ⟨1⟩
  have hStot : (QueryCounts (X := Fin n → S) id
      (fun w => wordProd (id : S → S) w) ε).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [show x = y from h]) hε
  have hrestrict := qQueryOn_comp_read_le_qQuery
    (fun w : Fin n → M => fun i => ((ψ (w i) : S)))
    (fun v : Fin n → S => wordProd (id : S → S) v) hStot
  refine le_trans (qQueryOn_prodFun_le_of_division hn T φ ψ hsec
    (X := Fin n → M) id (hStot.mono (queryCounts_subset_of_read _ _ ε))) ?_
  exact Nat.mul_le_mul_left 2 hrestrict

/-! ### The allowed-alphabet form

The paper's version that asks for a section only on the allowed letters.
Here the two problems share the **same** oracle — only the interpretation of
the letters differs — so no alphabet simulation happens at all and the factor
is **one**, not two.  A section on all of `M` is not needed: only that each
allowed letter has a `T`-representative mapping to it. -/

/-- **Division through a finite letter map**: if every allowed letter's
`S`-interpretation lies in `T` and `φ` sends it to the intended
`M`-interpretation, the `M`-product costs *no more* than the `S`-product on
the same alphabet. -/
theorem qQueryOn_wordProd_le_of_division_letters {σ : Type} [Fintype σ]
    [DecidableEq σ] {n : ℕ} (hn : 1 ≤ n) (T : Subsemigroup S) (φ : T →ₙ* M)
    (letterS : σ → S) (letterM : σ → M) (hmem : ∀ a, letterS a ∈ T)
    (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a)
    (read : X → Fin n → σ) {ε : ℝ}
    (hne : (QueryCounts read (fun x => wordProd letterS (read x)) ε).Nonempty) :
    qQueryOn read (fun x => wordProd letterM (read x)) ε
      ≤ qQueryOn read (fun x => wordProd letterS (read x)) ε := by
  have hEq : (fun x => wordProd letterM (read x))
      = fun x => extendHom T φ (wordProd letterS (read x)) := by
    funext x
    rw [wordProd, wordProd]
    exact (extendHom_orderedProd T φ hn _ (fun i => hmem (read x i)) _
      fun i => hφ (read x i)).symm
  rw [hEq]
  exact qQueryOn_postcomp_le (extendHom T φ) hne

/-- **The total form of the allowed-alphabet clause.** -/
theorem qQuery_wordProd_le_of_division_letters {σ : Type} [Fintype σ]
    [DecidableEq σ] {n : ℕ} (hn : 1 ≤ n) (T : Subsemigroup S) (φ : T →ₙ* M)
    (letterS : σ → S) (letterM : σ → M) (hmem : ∀ a, letterS a ∈ T)
    (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → σ => wordProd letterM x) ε
      ≤ qQuery (fun x : Fin n → σ => wordProd letterS x) ε := by
  have : Nonempty S := ⟨1⟩
  exact qQueryOn_wordProd_le_of_division_letters hn T φ letterS letterM hmem hφ
    (X := Fin n → σ) id
    (queryCounts_nonempty (fun x y h => by rw [show x = y from h]) hε)

/-- **The clause with the two oracle alphabets named separately.**  The left
side queries the `σ` oracle, the right side the relabelled `σ'` oracle; since
renaming costs zero queries (`qQueryOn_relabel`) the comparison is the
allowed-alphabet bound itself. -/
theorem qQueryOn_wordProd_le_of_division_relabel {σ σ' : Type} [Fintype σ]
    [DecidableEq σ] [Fintype σ'] [DecidableEq σ'] {n : ℕ} (hn : 1 ≤ n)
    (T : Subsemigroup S) (φ : T →ₙ* M) (e : σ ≃ σ')
    (letterS : σ → S) (letterM : σ → M) (hmem : ∀ a, letterS a ∈ T)
    (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a)
    (read : X → Fin n → σ) {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn read (fun x => wordProd letterM (read x)) ε
      ≤ qQueryOn (fun x i => e (read x i))
          (fun x => wordProd letterS (read x)) ε := by
  have : Nonempty S := ⟨1⟩
  have hneS :
      (QueryCounts read (fun x => wordProd letterS (read x)) ε).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [h]) hε
  rw [qQueryOn_relabel e read _ hneS]
  exact qQueryOn_wordProd_le_of_division_letters hn T φ letterS letterM hmem hφ
    read hneS

/-- **The total form with the two oracle alphabets named separately**:
`Prod_M` over `σⁿ` against `Prod_S` over `σ'ⁿ`, the letters of the latter
read through `e.symm`. -/
theorem qQuery_wordProd_le_of_division_relabel {σ σ' : Type} [Fintype σ]
    [DecidableEq σ] [Fintype σ'] [DecidableEq σ'] {n : ℕ} (hn : 1 ≤ n)
    (T : Subsemigroup S) (φ : T →ₙ* M) (e : σ ≃ σ')
    (letterS : σ → S) (letterM : σ → M) (hmem : ∀ a, letterS a ∈ T)
    (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin n → σ => wordProd letterM x) ε
      ≤ qQuery (fun y : Fin n → σ' =>
          wordProd (fun b => letterS (e.symm b)) y) ε := by
  have : Nonempty S := ⟨1⟩
  refine le_trans (qQueryOn_wordProd_le_of_division_relabel hn T φ e letterS
    letterM hmem hφ (X := Fin n → σ) id hε) ?_
  simp only [id_eq]
  have hEq : (fun x : Fin n → σ => wordProd letterS x)
      = fun x : Fin n → σ =>
        wordProd (fun b => letterS (e.symm b)) (fun i => e (x i)) := by
    funext x
    rw [wordProd, wordProd]
    exact congrArg orderedProd
      (funext fun i => by rw [Equiv.symm_apply_apply])
  rw [hEq]
  exact qQueryOn_comp_read_le_qQuery _ _
    (queryCounts_nonempty (fun x y h => by rw [show x = y from h]) hε)

/-! ### The surjectivity wrapper -/

/-- The section is only ever used through `φ`, so plain surjectivity
suffices. -/
theorem qQuery_prodFun_le_of_division_surjective {n : ℕ} (hn : 1 ≤ n)
    (T : Subsemigroup S) (φ : T →ₙ* M) (hφ : Function.Surjective φ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    qQuery (fun w : Fin n → M => wordProd (id : M → M) w) ε
      ≤ 2 * qQuery (fun w : Fin n → S => wordProd (id : S → S) w) ε := by
  choose ψ hψ using hφ
  exact qQuery_prodFun_le_of_division hn T φ ψ hψ hε

end Subsemigroup

/-- The surjective-homomorphism form: `M` a quotient of `N` costs at most
twice `N`. -/
theorem qQueryOn_prodFun_le_of_surjective {n : ℕ} (φ : N →* M)
    (hφ : Function.Surjective φ) (read : X → Fin n → M) {ε : ℝ}
    (hne : ∀ ψ : M → N, (∀ m, φ (ψ m) = m) →
      (QueryCounts (fun x i => ψ (read x i))
        (fun x => wordProd (id : N → N) (fun j => ψ (read x j))) ε).Nonempty) :
    ∃ ψ : M → N, (∀ m, φ (ψ m) = m) ∧
      qQueryOn read (fun x => wordProd (id : M → M) (read x)) ε
        ≤ 2 * qQueryOn (fun x i => ψ (read x i))
            (fun x => wordProd (id : N → N) (fun j => ψ (read x j))) ε := by
  classical
  refine ⟨fun m => (hφ m).choose, fun m => (hφ m).choose_spec, ?_⟩
  exact qQueryOn_prodFun_le_of_section φ _ (fun m => (hφ m).choose_spec) read
    (hne _ fun m => (hφ m).choose_spec)

end MonoidProduct
