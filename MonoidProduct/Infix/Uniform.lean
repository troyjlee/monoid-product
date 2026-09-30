import MonoidProduct.Infix.TypedDual
import MonoidProduct.Infix.Monoids

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option synthInstance.maxSize 2048

/-!
# The uniform Rees bound

The product in `R(P)¹` is determined by the explicit-zero test, the typed clean-gap
test (`infZ` with the projection `reesProj`: identity ↦ neutral, zero ↦ blocking,
cells ↦ endpoints, and the relation `reesZ`: two cells are related when the sandwich
entry between them is zero) and the first and last non-identity letters.  The typed
dual `hasDual_infZ` costs `13·√n·λ(n)` whatever `P` is, so

`Q_{1/3}(Prod_{R(P)¹,n}) ≤ min{n, 8192·(1 + 2·(13√n·λ(n) + 24√n))}`

uniformly over all sandwich matrices (`rees_qQuery_le_min`); the Brandt monoids
`B_k¹ = R(I_k)¹` are the instance `brandt_qQuery_le_min`.
-/

namespace MonoidProduct.Infix

open Finset QuantumQueryComplexity MonoidProduct

variable {I Λ : Type} [Fintype I] [DecidableEq I] [Fintype Λ] [DecidableEq Λ]
variable (P : Λ → I → Bool)

/-- The projection of `R(P)¹`: identity ↦ `0`, zero ↦ `1`, cells ↦ `2`. -/
def reesProj (a : Rees1 P) : Fin 3 :=
  match (a : Option (ReesZero P)) with
  | none => 0
  | some ⟨none⟩ => 1
  | some ⟨some _⟩ => 2

/-- The forbidden endpoint relation: cells `(i, l)`, `(i', m)` with `P l i' = false`. -/
def reesZ (a b : Rees1 P) : Bool :=
  match (a : Option (ReesZero P)), (b : Option (ReesZero P)) with
  | some ⟨some (_, l)⟩, some ⟨some (i', _)⟩ => !P l i'
  | _, _ => false

variable {P}

@[simp] lemma reesProj_one : reesProj P 1 = 0 := rfl
@[simp] lemma reesProj_zero : reesProj P ↑(ReesZero.zero P) = 1 := rfl
@[simp] lemma reesProj_cell (i : I) (l : Λ) : reesProj P ↑(ReesZero.cell P i l) = 2 := rfl
@[simp] lemma reesZ_cell (i : I) (l : Λ) (i' : I) (m : Λ) :
    reesZ P ↑(ReesZero.cell P i l) ↑(ReesZero.cell P i' m) = !P l i' := rfl

lemma reesProj_eq_zero_iff {a : Rees1 P} : reesProj P a = 0 ↔ a = 1 := by
  rcases Rees1.cases P a with rfl | rfl | ⟨i, l, rfl⟩
  · simp
  · simp only [reesProj_zero]; exact ⟨fun h => absurd h (by decide), fun h => absurd h WithOne.coe_ne_one⟩
  · simp only [reesProj_cell]; exact ⟨fun h => absurd h (by decide), fun h => absurd h WithOne.coe_ne_one⟩

lemma reesProj_eq_two_iff {a : Rees1 P} : reesProj P a = 2 ↔ ∃ i l, a = ↑(ReesZero.cell P i l) := by
  rcases Rees1.cases P a with rfl | rfl | ⟨i, l, rfl⟩
  · simp only [reesProj_one]
    exact ⟨fun h => absurd h (by decide), fun ⟨_, _, h⟩ => absurd h.symm WithOne.coe_ne_one⟩
  · simp only [reesProj_zero]
    exact ⟨fun h => absurd h (by decide), fun ⟨i, l, h⟩ => absurd h.symm (Rees1.cell_ne_zero P i l)⟩
  · simp only [reesProj_cell, true_iff]; exact ⟨i, l, rfl⟩

/-- **`Bad` is the explicit-zero test or the typed clean-gap test.** -/
lemma bad_iff_typed {n : ℕ} (w : Fin n → Rees1 P) :
    Bad w n ↔ zeroTest n w = true ∨ infZ (reesProj P) (reesZ P) w = true := by
  simp only [zeroTest, decide_eq_true_eq, infZ_eq_true_iff]
  unfold Bad
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨s, s', hss', hs'n, hmid, i, l, i', m, hs, hs', hP⟩
    have hsn : s < n := hss'.trans hs'n
    rw [padAt_of_lt _ hsn] at hs
    rw [padAt_of_lt _ hs'n] at hs'
    refine ⟨⟨s, hsn⟩, ⟨s', hs'n⟩, hss', ?_, ?_, ?_, ?_⟩
    · rw [hs]; rfl
    · rw [hs']; rfl
    · rw [hs, hs', reesZ_cell, hP]; rfl
    · intro q h1 h2
      have := hmid q h1 h2
      rw [padAt_of_lt _ q.isLt] at this
      rw [this]; rfl
  · rintro ⟨l, r, hlr, hl, hr, hZ, hmid⟩
    obtain ⟨i, l₀, hl⟩ := reesProj_eq_two_iff.1 hl
    obtain ⟨i', m, hr⟩ := reesProj_eq_two_iff.1 hr
    refine ⟨l, r, hlr, r.isLt, fun q h1 h2 => ?_, i, l₀, i', m, ?_, ?_, ?_⟩
    · have hq : q < n := h2.trans r.isLt
      rw [padAt_of_lt _ hq]
      exact reesProj_eq_zero_iff.1 (hmid ⟨q, hq⟩ h1 h2)
    · rw [padAt_of_lt _ l.isLt]; exact hl
    · rw [padAt_of_lt _ r.isLt]; exact hr
    · rw [hl, hr, reesZ_cell] at hZ
      cases h : P l₀ i'
      · rfl
      · rw [h] at hZ; exact absurd hZ (by decide)

/-- The joint of the four tests, at cost `13√n·λ(n) + 24√n`. -/
theorem hasDual_joint_uniform (n : ℕ) :
    HasDual (fun w : Fin n → Rees1 P =>
        (((infZ (reesProj P) (reesZ P) w, zeroTest n w), firstNonId w), lastNonId w))
      (13 * Real.sqrt n * lam n + 8 * Real.sqrt n + 8 * Real.sqrt n + 8 * Real.sqrt n) :=
  (((hasDual_infZ (reesProj P) (reesZ P) n).adaptiveCall_const
    (hasDual_zeroTest n)).adaptiveCall_const
    (hasDual_firstNonId n)).adaptiveCall_const (hasDual_lastNonId n)

/-- **The uniform Rees bound, dual form**: the product in `R(P)¹` has a dual of
cost `2·(13√n·λ(n) + 24√n)`, independent of `P`. -/
theorem hasDual_wordProd_rees_uniform (n : ℕ) :
    HasDual (fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w)
      (2 * (13 * Real.sqrt n * lam n + 24 * Real.sqrt n)) := by
  have hl := two_le_lam n
  have hc : (0 : ℝ) ≤ 13 * Real.sqrt n * lam n + 8 * Real.sqrt n + 8 * Real.sqrt n
      + 8 * Real.sqrt n := by positivity
  have h := (hasDual_joint_uniform (P := P) n).postcomp_of_determined hc fun w w' hww' => by
    simp only [Prod.mk.injEq] at hww'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hww'
    refine wordProd_eq_of_data ?_ h3 h4
    rw [bad_iff_typed, bad_iff_typed, h1, h2]
  refine h.mono (le_of_eq ?_)
  ring

/-- **The uniform Rees bound**: `Q_{1/3}(Prod_{R(P)¹,n}) ≤ 8192·(1 + 2(13√n·λ(n) + 24√n))`
for every sandwich matrix `P`. -/
theorem rees_qQuery_upper_uniform (n : ℕ) :
    (qQuery (fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + 2 * (13 * Real.sqrt n * lam n + 24 * Real.sqrt n)) := by
  have : Nonempty (Rees1 P) := ⟨1⟩
  refine qQueryOn_third_le_of_hasDualOn_uniform (hasDual_wordProd_rees_uniform n).hasDualOn ?_
  have := two_le_lam n
  positivity

/-- The `min{n, √n·λ(n)}` form. -/
theorem rees_qQuery_le_min (n : ℕ) :
    (qQuery (fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
          (uniformExtractionConstant * (1 + 2 * (13 * Real.sqrt n * lam n + 24 * Real.sqrt n))) :=
  le_min (by
    have : Nonempty (Rees1 P) := ⟨1⟩
    have h := qQueryOn_le_card (read := (id : (Fin n → Rees1 P) → Fin n → Rees1 P))
      (f := fun w : Fin n → Rees1 P => wordProd (id : Rees1 P → Rees1 P) w)
      (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [Fintype.card_fin] at h
    exact_mod_cast h) (rees_qQuery_upper_uniform n)

/-! ## Brandt monoids -/

/-- The identity sandwich matrix of size `k`. -/
def PBk (k : ℕ) : Fin k → Fin k → Bool := fun l i => decide (l = i)

/-- **`B_k¹`**, the Brandt monoid with `k` idempotents adjoined an identity. -/
abbrev Bk (k : ℕ) := Rees1 (PBk k)

/-- **The uniform Brandt bound**: `Q_{1/3}(Prod_{B_k¹,n}) ≤ min{n, 8192·(1 + 2(13√n·λ(n) + 24√n))}`
for every `k`. -/
theorem brandt_qQuery_le_min (k n : ℕ) :
    (qQuery (fun w : Fin n → Bk k => wordProd (id : Bk k → Bk k) w) (1 / 3) : ℝ)
      ≤ min (n : ℝ)
          (uniformExtractionConstant * (1 + 2 * (13 * Real.sqrt n * lam n + 24 * Real.sqrt n))) :=
  rees_qQuery_le_min n

/-- `A₂¹`, uniform form. -/
theorem A2_qQuery_upper_uniform (n : ℕ) :
    (qQuery (fun w : Fin n → A2 => wordProd (id : A2 → A2) w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + 2 * (13 * Real.sqrt n * lam n + 24 * Real.sqrt n)) :=
  rees_qQuery_upper_uniform n

/-- `B₂¹`, uniform form. -/
theorem B2_qQuery_upper_uniform (n : ℕ) :
    (qQuery (fun w : Fin n → B2 => wordProd (id : B2 → B2) w) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + 2 * (13 * Real.sqrt n * lam n + 24 * Real.sqrt n)) :=
  rees_qQuery_upper_uniform n

end MonoidProduct.Infix
