import MonoidProduct.Infix.Uniform
import QuantumQueryComplexity.Quantum.PredictionTreeCompose
import QuantumQueryComplexity.Duality.FiniteOutputOn
import QuantumQueryComplexity.Quantum.Relabel
import QuantumQueryComplexity.Quantum.Postcomp
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option synthInstance.maxSize 2048

/-!
# Brandt products reduce to the two-state case (`monoid.tex` prop:brandt-two-colour)

With `q_k(n) = Q_{1/3}(Prod_{B_k¹,n})` (native model, `Bk k = Rees1 (PBk k)`):

* `brandt_two_colour` — for `k ≥ 2` and all `n`, `q_2(n) ≤ q_k(n) ≤ 10⁸·(q_2(n) + √n)`;
  the explicit form is `brandt_qQuery_le_two_explicit`,
  `q_k ≤ 8192·(1 + 32√n + 24√6·(1376/7)·q_2)`, valid for every `k`;
* `brandt_qQuery_theta` — `q_2 ≤ q_k ≤ 2·10¹⁰·q_2` uniformly in `k ≥ 2`;
* `brandt_qQuery_sqrt_log` — `(7/1376)√n ≤ q_k ≤ 2²¹·√n·log(n+2)` for `n ≥ 1`, all `k`
  (the display with `A = 1`, from `brandt_qQuery_le_min`).

**Upper half (the paper's random colourings).**  A colouring `h : [k] → [2]` recodes
letters locally (`bcCol`: `e_{il} ↦ e_{h(i)h(l)}`).  A recoded bad word comes from a bad
word (`bad_of_bad_bcCol`), and a bad word is caught by every colouring (explicit zero) or
by every colouring separating one fixed pair `l ≠ i'` (`bad_bcCol_of_bad`).  A seed is four
independent colourings (`BcSeed`); the seed output (`bcSeedOut`) is zero if one of the four
recoded `B_2¹` products is zero and the endpoint product (`bcEnd`) otherwise.  It is always
correct on nonzero products and correct on zero products for at least `15/16` of the
seeds (`bcSeedOut_prob`).  Each seed output has a dual (`hasDual_bcSeedOut`): the
`B_2¹` product's dual of cost `3·ADV±` (finite-output bridge), pulled back along the
non-injective letter map at cost `√|B_2¹| = √6` (`hasDual_letterCode`), four such calls
and the two endpoint scans joined by `adaptiveCall_const`, collapsed by `postcomp`.
The uniform extraction gives each seed error `1/16`, and the fixed-seed mixture
`qQueryOn_third_le_of_seeds` gives `Q_{1/3}`; finally `ADV± ≤ (1376/7)·q_2`.
The paper's coherent two-query simulation of encoded letters is replaced by the dual
pullback, so no quantum error reduction per call is needed.

**Lower half.**  `B_2¹` sits in `B_k¹` on two indices (`bcEmb`, a monoid homomorphism).
Restricting the oracle alphabet along an injection costs **nothing** in the native model
(`bc_qQueryOn_le_of_injective`, proved here by an explicit basis embedding intertwining
the transposition oracles), so `q_2 ≤ q_k` holds with factor one.
-/

namespace MonoidProduct.Infix

open Finset QuantumQueryComplexity MonoidProduct
open scoped Matrix

/-! ## The colouring letter map -/

/-- The colour-`h` recoding `B_k¹ → B_2¹`: `1 ↦ 1`, `0 ↦ 0`, `e_{il} ↦ e_{h(i) h(l)}`. -/
def bcCol {k : ℕ} (h : Fin k → Fin 2) (a : Bk k) : Bk 2 :=
  match (a : Option (ReesZero (PBk k))) with
  | none => 1
  | some ⟨none⟩ => ↑(ReesZero.zero (PBk 2))
  | some ⟨some (i, l)⟩ => ↑(ReesZero.cell (PBk 2) (h i) (h l))

variable {k : ℕ}

@[simp] lemma bcCol_one (h : Fin k → Fin 2) : bcCol h 1 = 1 := rfl
@[simp] lemma bcCol_zero (h : Fin k → Fin 2) :
    bcCol h ↑(ReesZero.zero (PBk k)) = ↑(ReesZero.zero (PBk 2)) := rfl
@[simp] lemma bcCol_cell (h : Fin k → Fin 2) (i l : Fin k) :
    bcCol h ↑(ReesZero.cell (PBk k) i l) = ↑(ReesZero.cell (PBk 2) (h i) (h l)) := rfl

lemma bcCol_eq_one {h : Fin k → Fin 2} {a : Bk k} (ha : bcCol h a = 1) : a = 1 := by
  rcases Rees1.cases (PBk k) a with rfl | rfl | ⟨i, l, rfl⟩
  · rfl
  · exact absurd ha WithOne.coe_ne_one
  · exact absurd ha WithOne.coe_ne_one

lemma bcCol_eq_zero {h : Fin k → Fin 2} {a : Bk k}
    (ha : bcCol h a = ↑(ReesZero.zero (PBk 2))) : a = ↑(ReesZero.zero (PBk k)) := by
  rcases Rees1.cases (PBk k) a with rfl | rfl | ⟨i, l, rfl⟩
  · exact absurd ha.symm WithOne.coe_ne_one
  · rfl
  · exact absurd ha (Rees1.cell_ne_zero _ _ _)

lemma bcCol_eq_cell {h : Fin k → Fin 2} {a : Bk k} {i l : Fin 2}
    (ha : bcCol h a = ↑(ReesZero.cell (PBk 2) i l)) :
    ∃ i' l', a = ↑(ReesZero.cell (PBk k) i' l') ∧ h i' = i ∧ h l' = l := by
  rcases Rees1.cases (PBk k) a with rfl | rfl | ⟨i', l', rfl⟩
  · exact absurd ha.symm WithOne.coe_ne_one
  · exact absurd ha.symm (Rees1.cell_ne_zero _ _ _)
  · obtain ⟨h1, h2⟩ := Rees1.cell_inj _ ha
    exact ⟨i', l', rfl, h1, h2⟩

lemma padAt_bcCol {n : ℕ} (h : Fin k → Fin 2) (w : Fin n → Bk k) (s : ℕ) :
    padAt (fun j => bcCol h (w j)) s = bcCol h (padAt w s) := by
  by_cases hs : s < n
  · rw [padAt_of_lt _ hs, padAt_of_lt _ hs]
  · rw [padAt_of_le _ (not_lt.1 hs), padAt_of_le _ (not_lt.1 hs), bcCol_one]

/-- **A recoded bad word comes from a bad word**: every colouring is one-sided. -/
lemma bad_of_bad_bcCol {n : ℕ} (h : Fin k → Fin 2) (w : Fin n → Bk k)
    (hb : Bad (fun j => bcCol h (w j)) n) : Bad w n := by
  rcases hb with ⟨s, hs, hz⟩ | ⟨s, s', hss, hs'n, hmid, i, l, i', m, h1, h2, hP⟩
  · rw [padAt_bcCol] at hz
    exact Or.inl ⟨s, hs, bcCol_eq_zero hz⟩
  · rw [padAt_bcCol] at h1 h2
    obtain ⟨a, b, ha, -, hb⟩ := bcCol_eq_cell h1
    obtain ⟨a', b', ha', ha'i, -⟩ := bcCol_eq_cell h2
    refine Or.inr ⟨s, s', hss, hs'n, fun q h1 h2 => ?_, a, b, a', b', ha, ha', ?_⟩
    · have := hmid q h1 h2
      rw [padAt_bcCol] at this
      exact bcCol_eq_one this
    · simp only [PBk, decide_eq_false_iff_not]
      rintro rfl
      simp only [PBk, decide_eq_false_iff_not] at hP
      exact hP (hb.symm.trans ha'i)

/-- **A bad word is caught by the colourings**: either by every colouring (an explicit
zero), or by every colouring separating one fixed pair of distinct indices. -/
lemma bad_bcCol_of_bad {n : ℕ} (w : Fin n → Bk k) (hb : Bad w n) :
    (∀ h : Fin k → Fin 2, Bad (fun j => bcCol h (w j)) n) ∨
      ∃ l i' : Fin k, l ≠ i' ∧
        ∀ h : Fin k → Fin 2, h l ≠ h i' → Bad (fun j => bcCol h (w j)) n := by
  rcases hb with ⟨s, hs, hz⟩ | ⟨s, s', hss, hs'n, hmid, i, l, i', m, h1, h2, hP⟩
  · refine Or.inl fun h => Or.inl ⟨s, hs, ?_⟩
    rw [padAt_bcCol, hz, bcCol_zero]
  · have hli : l ≠ i' := by simpa [PBk] using hP
    refine Or.inr ⟨l, i', hli, fun h hh => Or.inr ⟨s, s', hss, hs'n, fun q q1 q2 => ?_,
      h i, h l, h i', h m, ?_, ?_, ?_⟩⟩
    · rw [padAt_bcCol, hmid q q1 q2, bcCol_one]
    · rw [padAt_bcCol, h1, bcCol_cell]
    · rw [padAt_bcCol, h2, bcCol_cell]
    · simpa [PBk] using hh

/-! ## Counting colourings -/

/-- Half of all colourings identify two distinct indices. -/
lemma bc_two_mul_card_eq {l i' : Fin k} (hli : l ≠ i') :
    2 * (univ.filter (fun h : Fin k → Fin 2 => h l = h i')).card
      = Fintype.card (Fin k → Fin 2) := by
  classical
  have hrev : ∀ x : Fin 2, Fin.rev x ≠ x := by decide
  let φ : (Fin k → Fin 2) → (Fin k → Fin 2) := fun h => Function.update h l (Fin.rev (h l))
  have hφφ : ∀ h, φ (φ h) = h := by
    intro h
    funext j
    by_cases hj : j = l
    · subst hj; simp [φ]
    · simp [φ, hj]
  have hφl : ∀ h, φ h l = Fin.rev (h l) := fun h => by simp [φ]
  have hφi : ∀ h, φ h i' = h i' := fun h => by simp [φ, Ne.symm hli]
  have hcard : (univ.filter (fun h : Fin k → Fin 2 => h l = h i')).card
      = (univ.filter (fun h : Fin k → Fin 2 => ¬ h l = h i')).card := by
    refine Finset.card_nbij' φ φ ?_ ?_ (fun h _ => hφφ h) (fun h _ => hφφ h)
    · intro h hh
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hh ⊢
      rw [hφl, hφi, ← hh]
      exact hrev _
    · intro h hh
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hh ⊢
      rw [hφl, hφi]
      have h2 : ∀ x y : Fin 2, x ≠ y → Fin.rev x = y := by decide
      exact h2 _ _ hh
  rw [two_mul]
  conv_lhs => arg 2; rw [hcard]
  rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- The seeds: four independent colourings `[k] → [2]`. -/
abbrev BcSeed (k : ℕ) := Fin 4 → Fin k → Fin 2

/-- **Four colourings all identify two distinct indices with probability `1/16`.** -/
lemma bc_sixteen_mul_card_eq {l i' : Fin k} (hli : l ≠ i') :
    16 * (univ.filter (fun ω : BcSeed k => ∀ t, ω t l = ω t i')).card
      = Fintype.card (BcSeed k) := by
  classical
  set A := univ.filter (fun h : Fin k → Fin 2 => h l = h i') with hA
  have hpi : univ.filter (fun ω : BcSeed k => ∀ t, ω t l = ω t i')
      = Fintype.piFinset (fun _ : Fin 4 => A) := by
    ext ω
    simp [A, Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset, Fintype.card_pi]
  simp only [prod_const, card_univ, Fintype.card_fin]
  have h2 := bc_two_mul_card_eq hli
  rw [← hA] at h2
  rw [← h2]
  ring

/-- **The seeded success probability**: a property that holds whenever some colouring
separates `l ≠ i'` holds with probability at least `15/16`. -/
lemma bc_prob_ge {l i' : Fin k} (hli : l ≠ i') (G : BcSeed k → Prop) [DecidablePred G]
    (hG : ∀ ω, (∃ t, ω t l ≠ ω t i') → G ω) :
    (15 / 16 : ℝ) ≤ ∑ ω : BcSeed k, if G ω then 1 / (Fintype.card (BcSeed k) : ℝ) else 0 := by
  classical
  set N := Fintype.card (BcSeed k) with hN
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := Fintype.card_pos
    exact_mod_cast this
  set S := univ.filter (fun ω : BcSeed k => ∀ t, ω t l = ω t i') with hS
  have h16 : (16 : ℝ) * S.card = N := by exact_mod_cast bc_sixteen_mul_card_eq hli
  have hle : ∀ ω : BcSeed k, (if ω ∈ S then (0 : ℝ) else 1 / (N : ℝ))
      ≤ if G ω then 1 / (N : ℝ) else 0 := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [if_pos hω]; split_ifs <;> positivity
    · rw [if_neg hω, if_pos (hG ω ?_)]
      simp only [hS, mem_filter, mem_univ, true_and, not_forall] at hω
      exact hω
  refine le_trans ?_ (Finset.sum_le_sum fun ω _ => hle ω)
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  have hc : ((univ.filter (fun ω => ω ∉ S)).card : ℝ) = N - S.card := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (BcSeed k)))
      (fun ω => ω ∈ S)
    rw [card_univ] at this
    have hSS : (univ.filter (fun ω => ω ∈ S)) = S := by ext; simp
    rw [hSS] at this
    rw [← hN] at this
    rw [← this]; push_cast; ring
  rw [hc]
  field_simp
  nlinarith

/-! ## The endpoint formula for a nonzero product -/

section Endpoint

variable {I Λ : Type} [Fintype I] [DecidableEq I] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → I → Bool}

/-- The product read off the first and last non-identity letters: `e_{i m}` for
extremal cells `e_{i l}`, `e_{i' m}`, and `1` otherwise. -/
def bcEnd (a b : Option (ReesZero P)) : Rees1 P :=
  match a, b with
  | some ⟨some (i, _)⟩, some ⟨some (_, m)⟩ => ↑(ReesZero.cell P i m)
  | _, _ => 1

/-- **A word that is not bad has product `bcEnd first last`.** -/
lemma wordProd_eq_bcEnd {n : ℕ} (w : Fin n → Rees1 P) (hb : ¬ Bad w n) :
    wordProd (id : Rees1 P → Rees1 P) w = bcEnd (firstNonId w) (lastNonId w) := by
  have hN := (prefix_spec w n).2 hb
  rw [wordProd, orderedProd_eq_rangeProd]
  change rangeProd w 0 n = _
  rcases hN with ⟨h1, h2⟩ | ⟨s₁, s₂, i, l, i', m, h1, h2, h3, h4, h5, h6, h7⟩
  · rw [h2, (firstNonId_eq_none_iff w).2 h1]
    rfl
  · have hs₁ : s₁ < n := by
      by_contra hcon; rw [padAt_of_le _ (not_lt.1 hcon)] at h5; exact WithOne.one_ne_coe h5
    have hfirst : firstNonId w = some (ReesZero.cell P i l) := by
      rcases hfw : firstNonId w with _ | a
      · have := (firstNonId_eq_none_iff w).1 hfw s₁ hs₁
        rw [h5] at this; exact absurd this WithOne.coe_ne_one
      · obtain ⟨s, hs, hs1, hs2⟩ := firstNonId_eq_some w hfw
        obtain ⟨-, e⟩ := first_unique hs1 hs2 h5 h3
        rw [e]
    have hlast : lastNonId w = some (ReesZero.cell P i' m) := by
      rcases hlw : lastNonId w with _ | a
      · have := (lastNonId_eq_none_iff w).1 hlw s₂ h2
        rw [h6] at this; exact absurd this WithOne.coe_ne_one
      · obtain ⟨s, hs, hs1, hs2⟩ := lastNonId_eq_some w hlw
        obtain ⟨-, e⟩ := last_unique hs1 hs2 h6 h4 hs h2
        rw [e]
    rw [h7, hfirst, hlast]
    rfl

end Endpoint

/-! ## The seeded reduction -/

section Reduction

variable {n : ℕ}

/-- The two-state product. -/
abbrev bcProd2 (n : ℕ) : (Fin n → Bk 2) → Bk 2 := fun y => wordProd (id : Bk 2 → Bk 2) y

/-- The `B_k¹` product. -/
abbrev bcProdK (k n : ℕ) : (Fin n → Bk k) → Bk k := fun w => wordProd (id : Bk k → Bk k) w

/-- The seed-`ω` output: zero if one of the four recoded `B_2¹` products is zero, and
otherwise the endpoint product `e_{i m}` (or `1`). -/
def bcSeedOut (ω : BcSeed k) (w : Fin n → Bk k) : Bk k :=
  if ∃ t, bcProd2 n (fun j => bcCol (ω t) (w j)) = ↑(ReesZero.zero (PBk 2))
  then ↑(ReesZero.zero (PBk k)) else bcEnd (firstNonId w) (lastNonId w)

/-- The joint the seed-`ω` output is read from. -/
def bcJoint (ω : BcSeed k) (w : Fin n → Bk k) :=
  (((((bcProd2 n (fun j => bcCol (ω 0) (w j)), bcProd2 n (fun j => bcCol (ω 1) (w j))),
    bcProd2 n (fun j => bcCol (ω 2) (w j))), bcProd2 n (fun j => bcCol (ω 3) (w j))),
    firstNonId w), lastNonId w)

lemma bc_card_bk2 : Fintype.card (Bk 2) = 6 := by decide

/-- The two-state product has a dual of cost `3·ADV±`. -/
theorem hasDual_bcProd2 (n : ℕ) : HasDual (bcProd2 n) (3 * advPM (bcProd2 n)) := by
  have h := hasDualOn_three_mul_advPMOn (read := (fun y : Fin n → Bk 2 => y)) (f := bcProd2 n)
    (fun x y hxy => by rw [hxy])
  rw [advPMOn_id] at h
  exact HasDual.of_hasDualOn_id h

/-- **One recoded call**: the colour-`h` recoding of the `B_2¹` product costs `√6` times
its dual (the letter map is not injective; `hasDual_letterCode` with a trivial block). -/
theorem hasDual_bcProd2_col (h : Fin k → Fin 2) :
    HasDual (fun w : Fin n → Bk k => bcProd2 n (fun j => bcCol h (w j)))
      (Real.sqrt 6 * (3 * advPM (bcProd2 n))) := by
  have hc : (0 : ℝ) ≤ 3 * advPM (bcProd2 n) := by
    have := (hasDual_bcProd2 n).nonneg
    exact this
  have hpb := (hasDual_bcProd2 n).pullback (κ := Fin n) (ι := Fin n × Unit)
    (e := fun j => (j, ())) (fun a b hab => (Prod.mk.inj hab).1)
  have hl := hasDual_letterCode (ι := Fin n) (κ := Unit) (fun a (_ : Unit) => bcCol h a) hc hpb
  rw [bc_card_bk2] at hl
  exact hl.ofEq fun w => rfl

/-- The joint of the four recoded calls and the two endpoint scans. -/
theorem hasDual_bcJoint (ω : BcSeed k) :
    HasDual (bcJoint (n := n) ω)
      (4 * (Real.sqrt 6 * (3 * advPM (bcProd2 n))) + 16 * Real.sqrt n) := by
  have h := (((((hasDual_bcProd2_col (n := n) (ω 0)).adaptiveCall_const
    (hasDual_bcProd2_col (ω 1))).adaptiveCall_const (hasDual_bcProd2_col (ω 2))).adaptiveCall_const
    (hasDual_bcProd2_col (ω 3))).adaptiveCall_const
    (hasDual_firstNonId (P := PBk k) n)).adaptiveCall_const (hasDual_lastNonId (P := PBk k) n)
  exact h.mono (le_of_eq (by ring))

/-- **The seed-`ω` output has a dual** of cost `2·(12√6·ADV±(Prod_{B_2¹}) + 16√n)`. -/
theorem hasDual_bcSeedOut (ω : BcSeed k) :
    HasDual (bcSeedOut (n := n) ω)
      (2 * (4 * (Real.sqrt 6 * (3 * advPM (bcProd2 n))) + 16 * Real.sqrt n)) := by
  have hc : (0 : ℝ) ≤ 4 * (Real.sqrt 6 * (3 * advPM (bcProd2 n))) + 16 * Real.sqrt n := by
    have := (hasDual_bcProd2 n).nonneg
    positivity
  refine (hasDual_bcJoint ω).postcomp_of_determined hc fun w w' hww => ?_
  simp only [bcJoint, Prod.mk.injEq] at hww
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, hf⟩, hl⟩ := hww
  have hall : ∀ t : Fin 4, bcProd2 n (fun j => bcCol (ω t) (w j))
      = bcProd2 n (fun j => bcCol (ω t) (w' j)) := by
    intro t; fin_cases t
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  unfold bcSeedOut
  simp only [hall, hf, hl]

/-- **Every seed is one-sided and correct on nonzero products; a zero product is
detected by at least `15/16` of the seeds.** -/
theorem bcSeedOut_prob (w : Fin n → Bk k) :
    (9 / 10 : ℝ) ≤ ∑ ω : BcSeed k,
      if bcSeedOut ω w = bcProdK k n w then 1 / (Fintype.card (BcSeed k) : ℝ) else 0 := by
  classical
  have hNpos : (0 : ℝ) < Fintype.card (BcSeed k) := by
    have : 0 < Fintype.card (BcSeed k) := Fintype.card_pos
    exact_mod_cast this
  -- a certain event has probability one
  have hsure : (∀ ω : BcSeed k, bcSeedOut ω w = bcProdK k n w) →
      (9 / 10 : ℝ) ≤ ∑ ω : BcSeed k,
        if bcSeedOut ω w = bcProdK k n w then 1 / (Fintype.card (BcSeed k) : ℝ) else 0 := by
    intro hall
    simp only [hall, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    norm_num
  -- a flagged seed outputs zero, and a flag certifies a bad word
  have hflag : ∀ ω : BcSeed k, (∃ t, Bad (fun j => bcCol (ω t) (w j)) n) →
      bcSeedOut ω w = bcProdK k n w := by
    rintro ω ⟨t, ht⟩
    have hw : Bad w n := bad_of_bad_bcCol _ _ ht
    unfold bcSeedOut
    rw [if_pos ⟨t, (wordProd_eq_zero_iff _).2 ht⟩, bcProdK, (wordProd_eq_zero_iff w).2 hw]
  by_cases hb : Bad w n
  · rcases bad_bcCol_of_bad w hb with hall | ⟨l, i', hli, hsep⟩
    · exact hsure fun ω => hflag ω ⟨0, hall _⟩
    · refine le_trans (by norm_num) (bc_prob_ge hli (fun ω => bcSeedOut ω w = bcProdK k n w)
        fun ω ⟨t, ht⟩ => hflag ω ⟨t, hsep _ ht⟩)
  · refine hsure fun ω => ?_
    have hnf : ¬ ∃ t, bcProd2 n (fun j => bcCol (ω t) (w j)) = ↑(ReesZero.zero (PBk 2)) := by
      rintro ⟨t, ht⟩
      exact hb (bad_of_bad_bcCol _ _ ((wordProd_eq_zero_iff _).1 ht))
    unfold bcSeedOut
    rw [if_neg hnf, bcProdK, wordProd_eq_bcEnd w hb]

end Reduction

/-! ## Restricting the oracle alphabet along an injection costs nothing

An algorithm against the `τ`-oracle answering `e (a i)`, for an injective `e : σ → τ`,
runs against the `σ`-oracle answering `a i` at the **same** query count.  The `τ`-basis
embeds into a `σ`-basis with workspace `Option (Option ι × τ) × W`: a `τ`-answer in the
image of `e` (or blank) is stored as its `σ`-preimage, and a `τ`-answer `c` outside the
image is parked in the workspace together with the index, the index register being set
idle — such a state is fixed by every `τ`-oracle `e ∘ a`, and idle states are fixed by
every `σ`-oracle.  The embedding intertwines the two oracles (`bcEnc_oracle`); the steps
are extended by the identity off the image. -/

section Injective

variable {ι σ τ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype τ] [DecidableEq τ] [Fintype W] [DecidableEq W]

/-- The workspace of the simulating algorithm. -/
abbrev BcWork (ι τ W : Type) := Option (Option ι × τ) × W

open Classical in
/-- The basis embedding. -/
noncomputable def bcEnc (e : σ → τ) : QBasis ι τ W → QBasis ι σ (BcWork ι τ W)
  | (i, none, w) => (i, none, (none, w))
  | (i, some c, w) =>
      if h : ∃ b, e b = c then (i, some h.choose, (none, w)) else (none, none, (some (i, c), w))

/-- Its explicit left inverse. -/
def bcDec (e : σ → τ) : QBasis ι σ (BcWork ι τ W) → QBasis ι τ W
  | (i, s, (none, w)) => (i, s.map e, w)
  | (_, _, (some (i, c), w)) => (i, some c, w)

lemma bcDec_bcEnc (e : σ → τ) (p : QBasis ι τ W) : bcDec e (bcEnc e p) = p := by
  classical
  obtain ⟨i, _ | c, w⟩ := p
  · rfl
  · by_cases h : ∃ b, e b = c
    · simp only [bcEnc, dif_pos h, bcDec, Option.map_some, h.choose_spec]
    · simp only [bcEnc, dif_neg h, bcDec]

lemma bcEnc_injective (e : σ → τ) : Function.Injective (bcEnc (ι := ι) (W := W) e) :=
  Function.LeftInverse.injective (bcDec_bcEnc e)

/-- `Option.map` along an injection commutes with the transposition. -/
lemma bc_option_map_swap {e : σ → τ} (he : Function.Injective e) (c : σ) (s : Option σ) :
    Option.map e (Equiv.swap none (some c) s) = Equiv.swap none (some (e c)) (Option.map e s) := by
  rcases s with _ | x
  · simp
  · by_cases hx : x = c
    · subst hx; simp
    · have h1 : (some x : Option σ) ≠ some c := fun h => hx (Option.some_injective _ h)
      have h2 : (some (e x) : Option τ) ≠ some (e c) :=
        fun h => hx (he (Option.some_injective _ h))
      rw [Equiv.swap_apply_of_ne_of_ne (Option.some_ne_none x) h1, Option.map_some,
        Equiv.swap_apply_of_ne_of_ne (Option.some_ne_none _) h2]

/-- **The embedding intertwines the oracles.** -/
lemma bcEnc_oracle {e : σ → τ} (he : Function.Injective e) (a : ι → σ) (p : QBasis ι τ W) :
    oracleMap a (bcEnc e p) = bcEnc e (oracleMap (fun i => e (a i)) p) := by
  classical
  obtain ⟨_ | i, t, w⟩ := p
  · rcases t with _ | c
    · rfl
    · by_cases h : ∃ b, e b = c
      · simp only [bcEnc, dif_pos h, oracleMap_none]
      · simp only [bcEnc, dif_neg h, oracleMap_none]
  · -- first kind: a blank or an answer in the image
    have hfirst : ∀ s : Option σ,
        bcEnc (W := W) e (some i, s.map e, w) = (some i, s, (none, w)) := by
      intro s
      rcases s with _ | b
      · rfl
      · have h : ∃ b', e b' = e b := ⟨b, rfl⟩
        simp only [Option.map_some, bcEnc, dif_pos h, he h.choose_spec]
    rcases t with _ | c
    · have := hfirst (Equiv.swap none (some (a i)) none)
      rw [bc_option_map_swap he, Option.map_none] at this
      rw [oracleMap_some (a := fun i => e (a i)), this]
      rfl
    · by_cases h : ∃ b, e b = c
      · obtain ⟨b, rfl⟩ := h
        have h1 := hfirst (some b)
        have h2 := hfirst (Equiv.swap none (some (a i)) (some b))
        rw [bc_option_map_swap he] at h2
        rw [Option.map_some] at h1 h2
        rw [h1, oracleMap_some, oracleMap_some, h2]
      · have hne : (some c : Option τ) ≠ some (e (a i)) :=
          fun hc => h ⟨a i, (Option.some_injective _ hc).symm⟩
        simp only [bcEnc, dif_neg h, oracleMap_none, oracleMap_some,
          Equiv.swap_apply_of_ne_of_ne (Option.some_ne_none c) hne]

/-! ### Extension off the image -/

section Ext

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']

open Classical in
/-- `H' ≃ H ⊕ (complement of the image)`, for an injection `enc : H → H'`. -/
noncomputable def bcSplit {enc : H → H'} (henc : Function.Injective enc) :
    H' ≃ H ⊕ {q : H' // q ∉ Set.range enc} :=
  (Equiv.sumCompl (fun q : H' => q ∈ Set.range enc)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective enc henc).symm (Equiv.refl _))

lemma bcSplit_enc {enc : H → H'} (henc : Function.Injective enc) (p : H) :
    bcSplit henc (enc p) = Sum.inl p := by
  classical
  unfold bcSplit
  simp only [Equiv.trans_apply]
  rw [Equiv.sumCompl_symm_apply_of_pos (Set.mem_range_self p)]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.inl.injEq]
  exact (Equiv.ofInjective enc henc).symm_apply_apply p

lemma bcSplit_of_not_mem {enc : H → H'} (henc : Function.Injective enc) {q : H'}
    (hq : q ∉ Set.range enc) : bcSplit henc q = Sum.inr ⟨q, hq⟩ := by
  classical
  unfold bcSplit
  simp only [Equiv.trans_apply]
  rw [Equiv.sumCompl_symm_apply_of_neg hq]
  rfl

open Classical in
/-- The extension of a vector by zero. -/
noncomputable def bcExtVec {enc : H → H'} (henc : Function.Injective enc) (ψ : H → ℂ) :
    H' → ℂ :=
  fun q => Sum.elim ψ (fun _ => 0) (bcSplit henc q)

lemma bcExtVec_enc {enc : H → H'} (henc : Function.Injective enc) (ψ : H → ℂ) (p : H) :
    bcExtVec henc ψ (enc p) = ψ p := by
  simp [bcExtVec, bcSplit_enc]

lemma bcExtVec_of_not_mem {enc : H → H'} (henc : Function.Injective enc) (ψ : H → ℂ) {q : H'}
    (hq : q ∉ Set.range enc) : bcExtVec henc ψ q = 0 := by
  simp [bcExtVec, bcSplit_of_not_mem henc hq]

open Classical in
/-- The extension of a matrix by the identity. -/
noncomputable def bcExtMat {enc : H → H'} (henc : Function.Injective enc) (M : Matrix H H ℂ) :
    Matrix H' H' ℂ :=
  (Matrix.fromBlocks M 0 0 (1 : Matrix {q : H' // q ∉ Set.range enc}
    {q : H' // q ∉ Set.range enc} ℂ)).submatrix (bcSplit henc) (bcSplit henc)

lemma bcExtMat_unitary {enc : H → H'} (henc : Function.Injective enc) {M : Matrix H H ℂ}
    (hM : M ∈ Matrix.unitaryGroup H ℂ) : bcExtMat henc M ∈ Matrix.unitaryGroup H' ℂ := by
  classical
  unfold bcExtMat
  refine submatrix_mem_unitaryGroup (bcSplit henc) ?_
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  rw [conjTranspose_mul_self_of_unitary hM, Matrix.fromBlocks_one]

lemma bcExtMat_mulVec {enc : H → H'} (henc : Function.Injective enc) (M : Matrix H H ℂ)
    (ψ : H → ℂ) : bcExtMat henc M *ᵥ bcExtVec henc ψ = bcExtVec henc (M *ᵥ ψ) := by
  classical
  unfold bcExtMat bcExtVec
  rw [submatrix_mulVec_comp (bcSplit henc)]
  funext q
  rw [Matrix.fromBlocks_mulVec]
  congr 1
  · funext p
    simp only [Pi.add_apply, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    have h0 : (fun _ : {q : H' // q ∉ Set.range enc} => (0 : ℂ)) = 0 := rfl
    rw [h0, Matrix.mulVec_zero]
    simp
  · funext r
    simp only [Pi.add_apply, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    have h0 : (fun _ : {q : H' // q ∉ Set.range enc} => (0 : ℂ)) = 0 := rfl
    rw [h0, Matrix.mulVec_zero, Matrix.zero_mulVec]
    simp

/-- Sums of terms vanishing at `0` only see the image. -/
lemma bc_sum_extVec {enc : H → H'} (henc : Function.Injective enc) (ψ : H → ℂ)
    (G : H' → ℂ → ℝ) (hG : ∀ q, G q 0 = 0) :
    ∑ q, G q (bcExtVec henc ψ q) = ∑ p, G (enc p) (ψ p) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image enc)) (fun q _ hq => ?_),
    Finset.sum_image (fun p _ p' _ h => henc h)]
  · exact Finset.sum_congr rfl fun p _ => by rw [bcExtVec_enc]
  · have : q ∉ Set.range enc := by
      rintro ⟨p, rfl⟩; exact hq (Finset.mem_image_of_mem _ (Finset.mem_univ p))
    rw [bcExtVec_of_not_mem henc ψ this, hG]

end Ext

variable {O : Type} [DecidableEq O] {e : σ → τ}

/-- **The simulating algorithm.** -/
noncomputable def bcInjAlg (e : σ → τ) (A : QAlg ι τ O W) :
    QAlg ι σ O (BcWork ι τ W) where
  init := bcExtVec (bcEnc_injective e) A.init
  init_isQState := by
    have h := bc_sum_extVec (bcEnc_injective (ι := ι) (W := W) e) A.init
      (fun _ z => Complex.normSq z) (fun _ => by simp)
    rw [IsQState, qNormSq_def, h]
    exact A.init_isQState
  step t := bcExtMat (bcEnc_injective e) (A.step t)
  step_unitary t := bcExtMat_unitary _ (A.step_unitary t)
  readout q := A.readout (bcDec e q)

lemma bcInjAlg_state (he : Function.Injective e) (A : QAlg ι τ O W) (a : ι → σ) (t : ℕ) :
    (bcInjAlg e A).state a t
      = bcExtVec (bcEnc_injective e) (A.state (fun i => e (a i)) t) := by
  induction t with
  | zero => exact bcExtMat_mulVec _ _ _
  | succ t ih =>
      rw [QAlg.state_succ, QAlg.state_succ, ih]
      have hor : oracleMat a *ᵥ bcExtVec (bcEnc_injective (ι := ι) (W := W) e)
            (A.state (fun i => e (a i)) t)
          = bcExtVec (bcEnc_injective e)
              (oracleMat (fun i => e (a i)) *ᵥ A.state (fun i => e (a i)) t) := by
        funext q
        rw [oracleMat_mulVec_apply]
        by_cases hq : q ∈ Set.range (bcEnc (ι := ι) (W := W) e)
        · obtain ⟨p, rfl⟩ := hq
          rw [bcEnc_oracle he, bcExtVec_enc, bcExtVec_enc, oracleMat_mulVec_apply]
        · have hq' : oracleMap a q ∉ Set.range (bcEnc (ι := ι) (W := W) e) := by
            rintro ⟨p, hp⟩
            apply hq
            refine ⟨oracleMap (fun i => e (a i)) p, ?_⟩
            rw [← bcEnc_oracle he, hp, oracleMap_involutive]
          rw [bcExtVec_of_not_mem _ _ hq, bcExtVec_of_not_mem _ _ hq']
      rw [hor]
      exact bcExtMat_mulVec _ _ _

lemma bcInjAlg_prob (he : Function.Injective e) (A : QAlg ι τ O W) (a : ι → σ) (t : ℕ)
    (o : O) : (bcInjAlg e A).prob a t o = A.prob (fun i => e (a i)) t o := by
  rw [QAlg.prob, QAlg.prob, bcInjAlg_state he, qProb, qProb]
  have h := bc_sum_extVec (bcEnc_injective (ι := ι) (W := W) e)
    (A.state (fun i => e (a i)) t)
    (fun q z => if (bcInjAlg e A).readout q = o then Complex.normSq z else 0)
    (fun _ => by simp)
  rw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  show (if A.readout (bcDec e (bcEnc e p)) = o then _ else _) = _
  rw [bcDec_bcEnc]

variable {X : Type} [Fintype X]

/-- **Restricting the oracle alphabet along an injection**:
`Q_ε(f, read) ≤ Q_ε(f, e ∘ read)` for injective `e`, at factor one. -/
theorem bc_qQueryOn_le_of_injective (he : Function.Injective e) (read : X → ι → σ)
    (f : X → O) {ε : ℝ} (hne : (QueryCounts (fun x i => e (read x i)) f ε).Nonempty) :
    qQueryOn read f ε ≤ qQueryOn (fun x i => e (read x i)) f ε := by
  obtain ⟨W', hW1, hW2, A, hA⟩ := exists_computes_qQueryOn hne
  let _ := hW1
  let _ := hW2
  refine qQueryOn_le (A := bcInjAlg e A) fun x => ?_
  rw [bcInjAlg_prob he]
  exact hA x

end Injective

/-! ## The upper bound -/

section Upper

/-- **Adversary form of the reduction**:
`Q_{1/3}(Prod_{B_k¹,n}) ≤ 8192·(1 + 2·(12√6·ADV±(Prod_{B_2¹,n}) + 16√n))`. -/
theorem brandt_qQuery_le_advPM_two (k n : ℕ) :
    (qQuery (bcProdK k n) (1 / 3) : ℝ)
      ≤ 8192 * (1 + 2 * (4 * (Real.sqrt 6 * (3 * advPM (bcProd2 n))) + 16 * Real.sqrt n)) := by
  classical
  set X : ℝ := 8192 * (1 + 2 * (4 * (Real.sqrt 6 * (3 * advPM (bcProd2 n)))
    + 16 * Real.sqrt n)) with hX
  have hc : (0 : ℝ) ≤ 2 * (4 * (Real.sqrt 6 * (3 * advPM (bcProd2 n))) + 16 * Real.sqrt n) := by
    have := (hasDual_bcProd2 n).nonneg
    positivity
  have hseed : ∀ ω : BcSeed k,
      qQueryOn (fun w : Fin n → Bk k => w) (bcSeedOut ω) (1 / 16) ≤ ⌊X⌋₊ := by
    intro ω
    have h := qQueryOn_le_of_hasDualOn_uniform (hasDual_bcSeedOut (n := n) ω).hasDualOn hc
    rw [uniformExtractionConstant] at h
    exact Nat.le_floor h
  have hN : (0 : ℝ) < Fintype.card (BcSeed k) := by
    have : 0 < Fintype.card (BcSeed k) := Fintype.card_pos
    exact_mod_cast this
  have hmain := qQueryOn_third_le_of_seeds (read := fun w : Fin n → Bk k => w)
    (f := bcProdK k n) (fun _ => 1 / (Fintype.card (BcSeed k) : ℝ)) (fun _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun ω => bcSeedOut ω) (fun ω x y hxy => by rw [hxy]) hseed (bcSeedOut_prob (k := k))
  have hX0 : 0 ≤ X := by positivity
  calc (qQuery (bcProdK k n) (1 / 3) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hmain
    _ ≤ X := Nat.floor_le hX0

/-- For `n = 0` the product is constant and costs nothing. -/
lemma bc_qQuery_zero (k : ℕ) : qQuery (bcProdK k 0) (1 / 3) = 0 :=
  qQueryOn_eq_zero_of_forall_eq _ (fun x y => by rw [Subsingleton.elim x y]) (by norm_num)

/-- **The reduction with its constants**:
`q_k(n) ≤ 8192·(1 + 32√n + 24√6·(1376/7)·q_2(n))`. -/
theorem brandt_qQuery_le_two_explicit (k n : ℕ) :
    (qQuery (bcProdK k n) (1 / 3) : ℝ)
      ≤ 8192 * (1 + 32 * Real.sqrt n
          + 24 * Real.sqrt 6 * (1376 / 7) * (qQuery (bcProd2 n) (1 / 3) : ℝ)) := by
  have h := brandt_qQuery_le_advPM_two k n
  have hadv := mul_advPM_le_qQuery_third_finiteOutput (bcProd2 n)
  have h6 : (0 : ℝ) ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hA : advPM (bcProd2 n) ≤ (1376 / 7) * (qQuery (bcProd2 n) (1 / 3) : ℝ) := by linarith
  calc (qQuery (bcProdK k n) (1 / 3) : ℝ)
      ≤ 8192 * (1 + 2 * (4 * (Real.sqrt 6 * (3 * advPM (bcProd2 n))) + 16 * Real.sqrt n)) := h
    _ = 8192 * (1 + 32 * Real.sqrt n + 24 * Real.sqrt 6 * advPM (bcProd2 n)) := by ring
    _ ≤ 8192 * (1 + 32 * Real.sqrt n
          + 24 * Real.sqrt 6 * ((1376 / 7) * (qQuery (bcProd2 n) (1 / 3) : ℝ))) := by
        have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 24 * Real.sqrt 6)
        linarith
    _ = _ := by ring

/-- **`prop:brandt-two-colour`, upper half**: `q_k(n) ≤ 10⁸·(q_2(n) + √n)` for all `k, n`. -/
theorem brandt_qQuery_le_two (k n : ℕ) :
    (qQuery (bcProdK k n) (1 / 3) : ℝ)
      ≤ 10 ^ 8 * ((qQuery (bcProd2 n) (1 / 3) : ℝ) + Real.sqrt n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [bc_qQuery_zero]
    simp only [CharP.cast_eq_zero]
    positivity
  have h := brandt_qQuery_le_two_explicit k n
  have hsn : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  have h6 : Real.sqrt 6 ≤ 49 / 20 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hq : (0 : ℝ) ≤ (qQuery (bcProd2 n) (1 / 3) : ℝ) := Nat.cast_nonneg _
  have h6' : (0 : ℝ) ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  calc (qQuery (bcProdK k n) (1 / 3) : ℝ)
      ≤ 8192 * (1 + 32 * Real.sqrt n
          + 24 * Real.sqrt 6 * (1376 / 7) * (qQuery (bcProd2 n) (1 / 3) : ℝ)) := h
    _ ≤ 8192 * (Real.sqrt n + 32 * Real.sqrt n
          + 24 * (49 / 20) * (1376 / 7) * (qQuery (bcProd2 n) (1 / 3) : ℝ)) := by
        gcongr
    _ ≤ _ := by nlinarith

end Upper

/-! ## The lower half: `B_2¹` is a submonoid of `B_k¹` -/

section Lower

/-- The inclusion of letters `B_2¹ → B_k¹` (`k ≥ 2`), on the first two indices. -/
def bcEmbFun {k : ℕ} (hk : 2 ≤ k) (a : Bk 2) : Bk k :=
  match (a : Option (ReesZero (PBk 2))) with
  | none => 1
  | some ⟨none⟩ => ↑(ReesZero.zero (PBk k))
  | some ⟨some (i, l)⟩ => ↑(ReesZero.cell (PBk k) (Fin.castLE hk i) (Fin.castLE hk l))

variable {k : ℕ} (hk : 2 ≤ k)

@[simp] lemma bcEmbFun_one : bcEmbFun hk 1 = 1 := rfl
@[simp] lemma bcEmbFun_zero :
    bcEmbFun hk ↑(ReesZero.zero (PBk 2)) = ↑(ReesZero.zero (PBk k)) := rfl
@[simp] lemma bcEmbFun_cell (i l : Fin 2) :
    bcEmbFun hk ↑(ReesZero.cell (PBk 2) i l)
      = ↑(ReesZero.cell (PBk k) (Fin.castLE hk i) (Fin.castLE hk l)) := rfl

/-- **The inclusion is a monoid homomorphism.** -/
def bcEmb : Bk 2 →* Bk k where
  toFun := bcEmbFun hk
  map_one' := rfl
  map_mul' a b := by
    rcases Rees1.cases (PBk 2) a with rfl | rfl | ⟨i, l, rfl⟩ <;>
      rcases Rees1.cases (PBk 2) b with rfl | rfl | ⟨j, m, rfl⟩ <;>
      simp only [one_mul, mul_one, bcEmbFun_one, bcEmbFun_zero, bcEmbFun_cell,
        Rees1.mul_zero, Rees1.zero_mul]
    rw [Rees1.cell_mul_cell, Rees1.cell_mul_cell]
    have hP : PBk k (Fin.castLE hk l) (Fin.castLE hk j) = PBk 2 l j := by
      simp only [PBk, Fin.castLE_inj]
    rw [hP]
    split_ifs <;> rfl

lemma bcEmb_injective : Function.Injective (bcEmb hk) := by
  intro a b hab
  change bcEmbFun hk a = bcEmbFun hk b at hab
  rcases Rees1.cases (PBk 2) a with rfl | rfl | ⟨i, l, rfl⟩ <;>
    rcases Rees1.cases (PBk 2) b with rfl | rfl | ⟨j, m, rfl⟩ <;>
    simp only [bcEmbFun_one, bcEmbFun_zero, bcEmbFun_cell] at hab
  · rfl
  · exact absurd hab WithOne.one_ne_coe
  · exact absurd hab WithOne.one_ne_coe
  · exact absurd hab WithOne.coe_ne_one
  · rfl
  · exact absurd hab.symm (Rees1.cell_ne_zero _ _ _)
  · exact absurd hab WithOne.coe_ne_one
  · exact absurd hab (Rees1.cell_ne_zero _ _ _)
  · obtain ⟨h1, h2⟩ := Rees1.cell_inj _ hab
    rw [Fin.castLE_inj] at h1 h2
    rw [h1, h2]

include hk in
/-- **`prop:brandt-two-colour`, lower half**: `q_2(n) ≤ q_k(n)` for `k ≥ 2` — restrict the
input alphabet to the copy of `B_2¹` on two indices (factor one,
`bc_qQueryOn_le_of_injective`). -/
theorem brandt_two_le_qQuery (n : ℕ) :
    qQuery (bcProd2 n) (1 / 3) ≤ qQuery (bcProdK k n) (1 / 3) := by
  classical
  have hinj := bcEmb_injective hk
  let emb : (Fin n → Bk 2) → Fin n → Bk k := fun y i => bcEmb hk (y i)
  -- the retraction of the product
  let ret : Bk k → Bk 2 := Function.invFun (bcEmb hk)
  have hret : ∀ a, ret (bcEmb hk a) = a := Function.leftInverse_invFun hinj
  have hprod : ∀ y : Fin n → Bk 2, bcProd2 n y = ret (bcProdK k n (emb y)) := by
    intro y
    rw [bcProdK, show wordProd (id : Bk k → Bk k) (emb y)
      = bcEmb hk (wordProd (id : Bk 2 → Bk 2) y) from (map_wordProd (bcEmb hk) id y).symm, hret]
  have hdetK : ∀ x y : Fin n → Bk 2, emb x = emb y → bcProdK k n (emb x) = bcProdK k n (emb y) :=
    fun x y h => by rw [h]
  have hne1 : (QueryCounts emb (fun y => bcProdK k n (emb y)) (1 / 3)).Nonempty :=
    queryCounts_nonempty hdetK (by norm_num)
  have hneK : (QueryCounts (X := Fin n → Bk k) id (bcProdK k n) (1 / 3)).Nonempty :=
    queryCounts_nonempty (fun x y h => by rw [show x = y from h]) (by norm_num)
  have hne2 : (QueryCounts emb (bcProd2 n) (1 / 3)).Nonempty := by
    refine queryCounts_nonempty (fun x y h => ?_) (by norm_num)
    rw [hprod, hprod, h]
  calc qQuery (bcProd2 n) (1 / 3)
      ≤ qQueryOn emb (bcProd2 n) (1 / 3) :=
        bc_qQueryOn_le_of_injective hinj (fun y : Fin n → Bk 2 => y) (bcProd2 n) hne2
    _ = qQueryOn emb (fun y => ret (bcProdK k n (emb y))) (1 / 3) := by
        congr 1; funext y; exact hprod y
    _ ≤ qQueryOn emb (fun y => bcProdK k n (emb y)) (1 / 3) := qQueryOn_postcomp_le ret hne1
    _ ≤ qQuery (bcProdK k n) (1 / 3) := qQueryOn_comp_read_le_qQuery emb (bcProdK k n) hneK

end Lower

/-! ## Consequences -/

section Consequences

/-- **`q_k = Θ(q_2)` uniformly in `k`**: `q_2(n) ≤ q_k(n) ≤ 2·10¹⁰·q_2(n)` for all
`k ≥ 2` and all `n` (the additive `√n` is absorbed by `(7/1376)√n ≤ q_2(n)`). -/
theorem brandt_qQuery_theta {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (qQuery (bcProd2 n) (1 / 3) : ℝ) ≤ (qQuery (bcProdK k n) (1 / 3) : ℝ) ∧
      (qQuery (bcProdK k n) (1 / 3) : ℝ) ≤ 2 * 10 ^ 10 * (qQuery (bcProd2 n) (1 / 3) : ℝ) := by
  refine ⟨by exact_mod_cast brandt_two_le_qQuery hk n, ?_⟩
  have h := brandt_qQuery_le_two k n
  have hlow : (7 / 1376 : ℝ) * Real.sqrt n ≤ (qQuery (bcProd2 n) (1 / 3) : ℝ) :=
    rees_qQuery_lower (P := PBk 2) n
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

/-- **`prop:brandt-two-colour`**: for every `k ≥ 2` and every `n`,
`q_2(n) ≤ q_k(n) ≤ 10⁸·(q_2(n) + √n)`, with `q_k(n) = Q_{1/3}(Prod_{B_k¹,n})`. -/
theorem brandt_two_colour {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (qQuery (bcProd2 n) (1 / 3) : ℝ) ≤ (qQuery (bcProdK k n) (1 / 3) : ℝ) ∧
      (qQuery (bcProdK k n) (1 / 3) : ℝ)
        ≤ 10 ^ 8 * ((qQuery (bcProd2 n) (1 / 3) : ℝ) + Real.sqrt n) :=
  ⟨by exact_mod_cast brandt_two_le_qQuery hk n, brandt_qQuery_le_two k n⟩

/-- `B_2¹` of `Infix/Monoids.lean` is `Bk 2`. -/
lemma bc_B2_eq : (B2 : Type) = Bk 2 := rfl

/-- The same chain stated with `B₂¹ = Rees1 PB` of `Infix/Monoids.lean`. -/
theorem brandt_two_colour_B2 {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (qQuery (fun w : Fin n → B2 => wordProd (id : B2 → B2) w) (1 / 3) : ℝ)
        ≤ (qQuery (bcProdK k n) (1 / 3) : ℝ) ∧
      (qQuery (bcProdK k n) (1 / 3) : ℝ)
        ≤ 10 ^ 8 * ((qQuery (fun w : Fin n → B2 => wordProd (id : B2 → B2) w) (1 / 3) : ℝ)
          + Real.sqrt n) :=
  brandt_two_colour hk n

/-- `λ(n) ≤ 4·log(n + 2)`. -/
lemma bc_lam_le_log (n : ℕ) : lam n ≤ 4 * Real.log ((n : ℝ) + 2) := by
  have hl2 := Real.log_two_gt_d9
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL2 : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  -- `log(n+4) ≤ log 2 + log(n+2)`
  have h4 : Real.log ((n : ℝ) + 4) ≤ Real.log 2 + Real.log ((n : ℝ) + 2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  set y := Real.logb 2 ((n : ℝ) + 4) with hy
  have hypos : 0 < y := Real.logb_pos (by norm_num) (by linarith)
  have hyle : y ≤ 1 + Real.log ((n : ℝ) + 2) / Real.log 2 := by
    rw [hy, Real.logb, div_le_iff₀ (by linarith), add_mul, one_mul,
      div_mul_cancel₀ _ (by linarith)]
    linarith
  have hly : Real.logb 2 y ≤ (y - 1) / Real.log 2 := by
    rw [Real.logb]
    exact div_le_div_of_nonneg_right (Real.log_le_sub_one_of_pos hypos) (by linarith)
  unfold lam
  rw [← hy]
  have hq : Real.log ((n : ℝ) + 2) / Real.log 2 / Real.log 2
      ≤ Real.log ((n : ℝ) + 2) * (1 / (0.69 : ℝ) ^ 2) := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have : (0.69 : ℝ) ^ 2 ≤ Real.log 2 * Real.log 2 := by nlinarith
    have hLpos : 0 ≤ Real.log ((n : ℝ) + 2) := by linarith
    calc Real.log ((n : ℝ) + 2) = Real.log ((n : ℝ) + 2) * (1 / 0.69 ^ 2) * 0.69 ^ 2 := by
          field_simp
      _ ≤ _ := by gcongr
  have h1 : (y - 1) / Real.log 2 ≤ Real.log ((n : ℝ) + 2) / Real.log 2 / Real.log 2 :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hone : (1 : ℝ) ≤ Real.log ((n : ℝ) + 2) * (1 / 0.69) := by
    rw [mul_one_div, le_div_iff₀ (by norm_num)]; linarith
  nlinarith

/-- **The final display of `prop:brandt-two-colour`**, with `A = 1`: uniformly in `k`,
`(7/1376)·√n ≤ Q_{1/3}(Prod_{B_k¹,n}) ≤ 2²¹·√n·log(n + 2)` for `n ≥ 1`. -/
theorem brandt_qQuery_sqrt_log (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (7 / 1376 : ℝ) * Real.sqrt n ≤ (qQuery (bcProdK k n) (1 / 3) : ℝ) ∧
      (qQuery (bcProdK k n) (1 / 3) : ℝ) ≤ 2 ^ 21 * Real.sqrt n * Real.log ((n : ℝ) + 2) := by
  refine ⟨rees_qQuery_lower (P := PBk k) n, ?_⟩
  have h := (brandt_qQuery_le_min k n).trans (min_le_right _ _)
  rw [uniformExtractionConstant] at h
  have hlam := bc_lam_le_log n
  have hsn : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hl2 := Real.log_two_gt_d9
  have hL : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hL1 : 1 ≤ 2 * Real.log ((n : ℝ) + 2) := by linarith
  have hlam0 : 0 ≤ lam n := by have := two_le_lam n; linarith
  have e1 : Real.sqrt n * lam n ≤ Real.sqrt n * (4 * Real.log ((n : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left hlam (by linarith)
  have e2 : Real.sqrt n ≤ Real.sqrt n * (2 * Real.log ((n : ℝ) + 2)) := by nlinarith
  nlinarith

end Consequences


end MonoidProduct.Infix
