import QuantumQueryComplexity.Quantum.AlphabetSimulation
import QuantumQueryComplexity.Quantum.ReadAll
import QuantumQueryComplexity.Quantum.Postcomp
import MonoidProduct.Aperiodic.Semigroup
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Division monotonicity for arbitrary (possibly infinite) semigroups

`monoid.tex`, `prop:division-monotonicity`: if `M ≺ S` — a subsemigroup `T ⊆ S` and a
surjective homomorphism `π : T ↠ M` — then `Q(Prod_{M,n}) ≤ 2·Q(Prod_{S,n})`, and more
generally, for `G ⊆ M` and a section `σ : G → T` of `π` over `G`,

  `Q(Prod_{M,G,n}) ≤ 2·Q(Prod_{S,σ(G),n})`.

`Quantum/Division.lean` and `Quantum/DivisionSemigroup.lean` prove this with `[Fintype M]`
and `[Fintype S]`.  This file removes both: `M`, `S` and `T` are arbitrary semigroups with
decidable equality, and only the **allowed input alphabets** are finite.

## What finiteness remains, and why

The query model (`QuantumQueryComplexity/Quantum/Algorithm.lean`) needs

* a **finite answer alphabet** `[Fintype σ]`: the oracle is a unitary on the finite basis
  `QBasis ι σ W`, so `qQueryOn read f ε` is only defined for `read : X → ι → σ` with
  `σ` finite (and a finite promise `X`);
* for the output type only `[DecidableEq O]` — *no* finiteness.

So the product problem `Prod_{S,G,n} : Gⁿ → S` is a problem of the model exactly when the
allowed alphabet `G` is finite; the ambient semigroups `S`, `M` (the output types) may be
infinite.  The paper's first assertion, with `G = M` and `G = S`, is a statement about
the infinite-alphabet problems `Mⁿ → M` and `Sⁿ → S` when `M` or `S` is infinite, which
have no meaning in a finite-oracle model; its content for finite `M` is
`qQuery_semigroupProd_le_of_division_cover` below (any finite alphabet of `S` that covers
`M` through `T`), and in general it is the section form, which is what the paper's own
proof reduces the first assertion to.  The section form is proved here verbatim
(`qQuery_semigroupProd_le_of_division_finset`) for every finite allowed alphabet
`G ⊆ M`, with `σ(G) ⊆ S` the image of the section.

The general engine is the **lift form** `qQueryOn_semigroupProd_le_of_division_lift`:
abstract finite letter types `α` (for `M`) and `β` (for `S`), interpretations
`letterM : α → M`, `letterS : β → S`, and a letter map `lift : α → β` landing in `T` with
`φ ∘ letterS ∘ lift = letterM`.  The factor two is the single compiled alphabet map
`lift` (`qQueryOn_alphabetMap_le`); postprocessing by an arbitrary extension of `φ` is free
(`qQueryOn_postcomp_le`); correctness is closure of `T` (`semigroupProd_mem_of_mem`).
When both problems read the same letters (`lift = id`) nothing is simulated and the factor
is **one** (`qQueryOn_semigroupProd_le_of_division_letters_inf`).

Words have length `n + 1` (`semigroupProd n`), as in `Quantum/DivisionSemigroup.lean`: a
semigroup has no empty product.  Every `Q` is the project's native transposition-oracle
complexity.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {M S : Type} [Semigroup M] [DecidableEq M] [Semigroup S] [DecidableEq S]

/-! ## Closure and the extension of `φ`, with no finiteness -/

/-- **Closure**: a nonempty word of `T`-letters has its product in `T` (no finiteness). -/
theorem semigroupProd_mem_of_mem (T : Subsemigroup S) :
    ∀ (n : ℕ) (v : Fin (n + 1) → S), (∀ i, v i ∈ T) → semigroupProd n v ∈ T
  | 0, v, hv => hv 0
  | n + 1, v, hv => by
      show semigroupProd n (fun i => v i.castSucc) * v (Fin.last (n + 1)) ∈ T
      exact mul_mem (semigroupProd_mem_of_mem T n _ fun i => hv _) (hv _)

open Classical in
/-- An arbitrary total extension of `φ : T →ₙ* M` to `S`, for arbitrary semigroups.  The
junk value off `T` comes from `[Nonempty M]` and is never used on a correct product. -/
noncomputable def extendHomInf [Nonempty M] (T : Subsemigroup S) (φ : T →ₙ* M) :
    S → M :=
  fun s => if h : s ∈ T then φ ⟨s, h⟩ else Classical.arbitrary M

lemma extendHomInf_of_mem [Nonempty M] {T : Subsemigroup S} (φ : T →ₙ* M) {s : S}
    (h : s ∈ T) : extendHomInf T φ s = φ ⟨s, h⟩ := by
  classical
  rw [extendHomInf, dif_pos h]

/-- **On a word of `T`-letters the extension computes `φ` letterwise.** -/
theorem extendHomInf_semigroupProd [Nonempty M] (T : Subsemigroup S) (φ : T →ₙ* M) :
    ∀ (n : ℕ) (v : Fin (n + 1) → S) (hv : ∀ i, v i ∈ T) (u : Fin (n + 1) → M),
      (∀ i, φ ⟨v i, hv i⟩ = u i) →
      extendHomInf T φ (semigroupProd n v) = semigroupProd n u
  | 0, v, hv, u, hu => by
      show extendHomInf T φ (v 0) = u 0
      rw [extendHomInf_of_mem φ (hv 0)]
      exact hu 0
  | n + 1, v, hv, u, hu => by
      have hA : semigroupProd n (fun i => v i.castSucc) ∈ T :=
        semigroupProd_mem_of_mem T n _ fun i => hv _
      have hb : v (Fin.last (n + 1)) ∈ T := hv _
      show extendHomInf T φ (semigroupProd n (fun i => v i.castSucc)
          * v (Fin.last (n + 1)))
        = semigroupProd n (fun i => u i.castSucc) * u (Fin.last (n + 1))
      rw [extendHomInf_of_mem φ (mul_mem hA hb),
        show (⟨semigroupProd n (fun i => v i.castSucc) * v (Fin.last (n + 1)),
            mul_mem hA hb⟩ : T) = (⟨_, hA⟩ : T) * ⟨_, hb⟩ from rfl, map_mul,
        ← extendHomInf_of_mem φ hA,
        extendHomInf_semigroupProd T φ n (fun i => v i.castSucc)
          (fun i => hv _) (fun i => u i.castSucc) (fun i => hu _)]
      congr 1
      exact hu _

/-! ## The lift form: factor two -/

variable {X : Type} [Fintype X]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **Division monotonicity, lift form, on any promise** (`prop:division-monotonicity`,
arbitrary semigroups).  `M`-letters `α` and `S`-letters `β` are finite; `lift : α → β`
sends every `M`-letter to an `S`-letter lying in `T` over it.  Then the `M`-product costs
at most **twice** the `S`-product on the lifted words. -/
theorem qQueryOn_semigroupProd_le_of_division_lift [Nonempty M] {n : ℕ}
    (T : Subsemigroup S) (φ : T →ₙ* M) (letterM : α → M) (letterS : β → S)
    (lift : α → β) (hmem : ∀ a, letterS (lift a) ∈ T)
    (hφ : ∀ a, φ ⟨letterS (lift a), hmem a⟩ = letterM a)
    (read : X → Fin (n + 1) → α) {ε : ℝ}
    (hne : (QueryCounts (fun x i => lift (read x i))
      (fun x => semigroupProd n fun i => letterS (lift (read x i))) ε).Nonempty) :
    qQueryOn read (fun x => semigroupProd n fun i => letterM (read x i)) ε
      ≤ 2 * qQueryOn (fun x i => lift (read x i))
          (fun x => semigroupProd n fun i => letterS (lift (read x i))) ε := by
  have hEq : (fun x => semigroupProd n fun i => letterM (read x i))
      = fun x => extendHomInf T φ
        (semigroupProd n fun i => letterS (lift (read x i))) := by
    funext x
    rw [extendHomInf_semigroupProd T φ n (fun i => letterS (lift (read x i)))
      (fun i => hmem (read x i)) (fun i => letterM (read x i))
      fun i => hφ (read x i)]
  rw [hEq]
  refine le_trans (qQueryOn_alphabetMap_le lift read _
    (hne.mono (queryCounts_postcomp (extendHomInf T φ) _ _ ε))) ?_
  exact Nat.mul_le_mul_left 2 (qQueryOn_postcomp_le (extendHomInf T φ) hne)

/-- **The total lift form**: `Q_ε(Prod over αⁿ⁺¹) ≤ 2·Q_ε(Prod over βⁿ⁺¹)`, for arbitrary
semigroups `M`, `S` and finite letter alphabets. -/
theorem qQuery_semigroupProd_le_of_division_lift [Nonempty α] {n : ℕ}
    (T : Subsemigroup S) (φ : T →ₙ* M) (letterM : α → M) (letterS : β → S)
    (lift : α → β) (hmem : ∀ a, letterS (lift a) ∈ T)
    (hφ : ∀ a, φ ⟨letterS (lift a), hmem a⟩ = letterM a) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin (n + 1) → α => semigroupProd n fun i => letterM (x i)) ε
      ≤ 2 * qQuery (fun y : Fin (n + 1) → β =>
          semigroupProd n fun i => letterS (y i)) ε := by
  have : Nonempty M := ⟨letterM (Classical.arbitrary α)⟩
  have : Nonempty S := ⟨letterS (lift (Classical.arbitrary α))⟩
  have hStot : (QueryCounts (X := Fin (n + 1) → β) id
      (fun y => semigroupProd n fun i => letterS (y i)) ε).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [show x = y from h]) hε
  refine le_trans (qQueryOn_semigroupProd_le_of_division_lift T φ letterM letterS lift
    hmem hφ (X := Fin (n + 1) → α) id
    (hStot.mono (queryCounts_subset_of_read (fun x : Fin (n + 1) → α => fun i => lift (x i))
      _ ε))) ?_
  exact Nat.mul_le_mul_left 2
    (qQueryOn_comp_read_le_qQuery (fun x : Fin (n + 1) → α => fun i => lift (x i))
      (fun y : Fin (n + 1) → β => semigroupProd n fun i => letterS (y i)) hStot)

/-! ## The paper's section form, verbatim -/

/-- The lifted allowed alphabet `σ(G) ⊆ S`: the image of a section `G → T`. -/
def divisionLiftAlphabet {T : Subsemigroup S} (G : Finset M) (sec : G → T) : Finset S :=
  G.attach.image fun g => ((sec g : T) : S)

lemma mem_divisionLiftAlphabet {T : Subsemigroup S} (G : Finset M) (sec : G → T)
    (g : G) : ((sec g : T) : S) ∈ divisionLiftAlphabet G sec :=
  Finset.mem_image.2 ⟨g, Finset.mem_attach _ _, rfl⟩

/-- **`prop:division-monotonicity`, the section form, for arbitrary semigroups**: for a
finite nonempty allowed alphabet `G ⊆ M` and a section `sec : G → T` of `φ` over `G`
(`φ (sec g) = g`; `sec` need not be multiplicative),

  `Q_ε(Prod_{M,G,n+1}) ≤ 2·Q_ε(Prod_{S,σ(G),n+1})`,

where `Prod_{M,G,·}` reads words over `G` and `Prod_{S,σ(G),·}` words over the image
`σ(G) = divisionLiftAlphabet G sec`.  `M`, `S`, `T` may be infinite. -/
theorem qQuery_semigroupProd_le_of_division_finset {n : ℕ} (T : Subsemigroup S)
    (φ : T →ₙ* M) (G : Finset M) (hG : G.Nonempty) (sec : G → T)
    (hsec : ∀ g, φ (sec g) = g) {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin (n + 1) → G => semigroupProd n fun i => ((x i : G) : M)) ε
      ≤ 2 * qQuery (fun y : Fin (n + 1) → divisionLiftAlphabet G sec =>
          semigroupProd n fun i => ((y i : divisionLiftAlphabet G sec) : S)) ε := by
  have : Nonempty G := hG.coe_sort
  exact qQuery_semigroupProd_le_of_division_lift T φ (fun g : G => (g : M))
    (fun b : divisionLiftAlphabet G sec => (b : S))
    (fun g => ⟨(sec g : S), mem_divisionLiftAlphabet G sec g⟩)
    (fun g => (sec g).2) (fun g => hsec g) hε

/-- **The first assertion for a finite `M` and an arbitrary `S`.**  `Prod_{M,n+1}` reads
all of `M`; on the `S` side any finite letter alphabet `β → S` whose letters inside `T`
cover `M` through `φ` will do (for finite `S`, `β = S` with `letterS = id` is the paper's
`Prod_{S,n+1}` whenever `φ` is surjective). -/
theorem qQuery_semigroupProd_le_of_division_cover [Fintype M] [Nonempty M] {n : ℕ}
    (T : Subsemigroup S) (φ : T →ₙ* M) (letterS : β → S)
    (hcov : ∀ m : M, ∃ b : β, ∃ h : letterS b ∈ T, φ ⟨letterS b, h⟩ = m)
    {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun w : Fin (n + 1) → M => semigroupProd n w) ε
      ≤ 2 * qQuery (fun y : Fin (n + 1) → β =>
          semigroupProd n fun i => letterS (y i)) ε := by
  choose lift hmem hφ using hcov
  exact qQuery_semigroupProd_le_of_division_lift T φ id letterS lift hmem hφ hε

/-- **The first assertion when `M` and `S` are both finite** — the only case in which
`Prod_{S,n+1}` over the full alphabet `S` is a problem of the finite-oracle model — as a
special case of the cover form: `Q(Prod_{M,n+1}) ≤ 2·Q(Prod_{S,n+1})` for a surjective
`φ : T ↠ M`.  (It restates `qQuery_semigroupProd_le_of_surjective`.) -/
theorem qQuery_semigroupProd_le_of_surjective_inf [Fintype M] [Nonempty M] [Fintype S]
    {n : ℕ} (T : Subsemigroup S) (φ : T →ₙ* M) (hφ : Function.Surjective φ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    qQuery (fun w : Fin (n + 1) → M => semigroupProd n w) ε
      ≤ 2 * qQuery (fun w : Fin (n + 1) → S => semigroupProd n w) ε := by
  refine qQuery_semigroupProd_le_of_division_cover T φ (id : S → S) (fun m => ?_) hε
  obtain ⟨t, rfl⟩ := hφ m
  exact ⟨t, t.2, rfl⟩

/-! ## The same-letters form: factor one -/

/-- **Division through a letter interpretation, on any promise, factor one**: if every
letter's `S`-interpretation lies in `T` and `φ` sends it to the `M`-interpretation, the
`M`-product costs no more than the `S`-product *on the same oracle*.  Arbitrary
semigroups. -/
theorem qQueryOn_semigroupProd_le_of_division_letters_inf [Nonempty M] {n : ℕ}
    (T : Subsemigroup S) (φ : T →ₙ* M) (letterS : α → S) (letterM : α → M)
    (hmem : ∀ a, letterS a ∈ T) (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a)
    (read : X → Fin (n + 1) → α) {ε : ℝ}
    (hne : (QueryCounts read
      (fun x => semigroupProd n fun i => letterS (read x i)) ε).Nonempty) :
    qQueryOn read (fun x => semigroupProd n fun i => letterM (read x i)) ε
      ≤ qQueryOn read (fun x => semigroupProd n fun i => letterS (read x i)) ε := by
  have hEq : (fun x => semigroupProd n fun i => letterM (read x i))
      = fun x => extendHomInf T φ (semigroupProd n fun i => letterS (read x i)) := by
    funext x
    rw [extendHomInf_semigroupProd T φ n (fun i => letterS (read x i))
      (fun i => hmem (read x i)) (fun i => letterM (read x i)) fun i => hφ (read x i)]
  rw [hEq]
  exact qQueryOn_postcomp_le (extendHomInf T φ) hne

/-- **The total same-letters form**, arbitrary semigroups, factor one. -/
theorem qQuery_semigroupProd_le_of_division_letters_inf [Nonempty α] {n : ℕ}
    (T : Subsemigroup S) (φ : T →ₙ* M) (letterS : α → S) (letterM : α → M)
    (hmem : ∀ a, letterS a ∈ T) (hφ : ∀ a, φ ⟨letterS a, hmem a⟩ = letterM a)
    {ε : ℝ} (hε : 0 ≤ ε) :
    qQuery (fun x : Fin (n + 1) → α => semigroupProd n fun i => letterM (x i)) ε
      ≤ qQuery (fun x : Fin (n + 1) → α => semigroupProd n fun i => letterS (x i)) ε := by
  have : Nonempty M := ⟨letterM (Classical.arbitrary α)⟩
  have : Nonempty S := ⟨letterS (Classical.arbitrary α)⟩
  exact qQueryOn_semigroupProd_le_of_division_letters_inf T φ letterS letterM hmem hφ
    (X := Fin (n + 1) → α) id
    (queryCounts_nonempty (fun x y h => by rw [show x = y from h]) hε)

end MonoidProduct
