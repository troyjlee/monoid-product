import MonoidProduct.Tropical.Support
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Product breadth of unitriangular tropical products

`monoid.tex` Corollary `cor:unitriangular-beta`, the breadth half: every word
over an alphabet of unitriangular max-plus matrices in `U_k(𝕋)` has a
**core** — a set of positions whose retained subword has the same full
product — of at most
`V_k = ∑_{s<t} (t − s) = k(k² − 1)/6 = C(k+1, 3)` positions.

This is the transition-support certificate of `Support.lean`
(`exists_certificate`) taken over *all* strict entries, promoted from
"the requested entries agree" to "the whole matrix agrees": the diagonal is
`0` and the lower triangle is `−∞` on both sides by unitriangularity.

The tropical matrices carry no `Monoid` instance in this development (their
products are `linProd`), so the statement is not literally an instance of
`IsBreadthBound` from `Width/Breadth.lean`; it is the same assertion, spelled
with `mask` (letters off the core replaced by the identity `none`) in place of
`subwordProd`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {k : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Two unitriangular matrices agreeing above the diagonal are equal. -/
lemma tmat_ext_of_isUtri {A B : TMat k} (hA : IsUtri A) (hB : IsUtri B)
    (h : ∀ s t : Fin k, s < t → A s t = B s t) : A = B := by
  funext s t
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact h s t hst
  · rw [hA.diag, hB.diag]
  · rw [hA.below s t hts, hB.below s t hts]

/-- **A core of at most `V_k` positions** for every word over a unitriangular
tropical alphabet: the retained word has the same product, all entries at
once. -/
theorem exists_core_linProd {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (n : ℕ) (w : Fin n → σ) :
    ∃ C : Finset (Fin n), C.card ≤ volume (strictPairs k) ∧
      linProd (optLetter letter) n (mask C w) = linProd letter n w := by
  obtain ⟨C, hC, hE, -⟩ := exists_certificate hL (enumOf (strictPairs k)) n w
  refine ⟨C, by rwa [nu_enumOf] at hC, ?_⟩
  refine tmat_ext_of_isUtri (isUtri_linProd (isUtri_optLetter hL) n _)
    (isUtri_linProd hL n w) fun s t hst => ?_
  have hmem : (s, t) ∈ strictPairs k := by
    simp [strictPairs, hst]
  set j := Fintype.equivFin (strictPairs k) ⟨(s, t), hmem⟩ with hjdef
  have hj : enumOf (strictPairs k) j = (s, t) := by
    simp [enumOf, hjdef]
  have h := congrArg (fun f : Lex (Fin _ → Trop) => ofLex f j) hE
  simp only [entries, ofLex_toLex, hj] at h
  exact h

/-- The breadth bound in closed form: `6·V_k = (k − 1)·k·(k + 1)`. -/
theorem exists_core_linProd_six_mul {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (n : ℕ) (w : Fin n → σ) :
    ∃ C : Finset (Fin n), 6 * C.card ≤ (k - 1) * k * (k + 1) ∧
      linProd (optLetter letter) n (mask C w) = linProd letter n w := by
  obtain ⟨C, hC, hprod⟩ := exists_core_linProd hL n w
  exact ⟨C, by rw [← six_mul_volume_strictPairs]; omega, hprod⟩

end MonoidProduct
