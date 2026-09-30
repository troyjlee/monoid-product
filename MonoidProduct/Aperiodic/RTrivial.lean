import MonoidProduct.Aperiodic.Ideals
import MonoidProduct.Aperiodic.EqProd
import QuantumQueryComplexity.Scan.Bounded
import QuantumQueryComplexity.HasDual
import QuantumQueryComplexity.Promise.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `R`-trivial monoids: the right-ideal depth and the log-free product bound

`monoid.tex` Theorem `thm:rtrivial`.

The **right-ideal depth** `d_R(M)` is the length of the longest strict chain
of principal right ideals `aM`; `rLevel` is the `rightIdeal` mirror of
`jLevel` (`Aperiodic/Ideals.lean`) — the level of `a` is the length of the
longest strictly ascending chain of right ideals starting at `aM`, larger
ideals having smaller level, and `rDepth M` is its maximum.  A monoid is
**`R`-trivial** when equal principal right ideals force equal elements.

The bound is the bounded-change scan (`hasDual_scan`) run on the prefix
products `p_t = x_1 ⋯ x_t`.  Always `p_{t+1}M ⊆ p_tM`; in an `R`-trivial
monoid a change of prefix therefore strictly descends the right ideal and
raises `rLevel`, so a trajectory has at most `rLevel(p_n) ≤ d_R(M)` changes
(`changeCount_le_rLevel`: the changed steps inject into `{1, …, rLevel(p_n)}`
by `i ↦ rLevel(p_{i+1})`, which is strictly increasing along them).  Hence

* `hasDual_wordProd_of_isRTrivial` : an explicit dual of cost
  `8√(n·min{n, d_R(M)})` for the total product, uniformly in the alphabet;
* `hasDualOn_wordProd_of_changeCount` : the promise form, at
  `8√(n·C)` for any bound `C` on the prefix changes over the promise (the
  paper's `C_𝒟`; no `R`-triviality is needed for this form).

Also here: every finite `R`-trivial monoid is aperiodic
(`isAperiodicMonoid_of_isRTrivial` — the levels of the powers of `a` would
otherwise increase forever).  The operational endpoints are in
`Quantum/RTrivialApplications.lean`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## The right-ideal depth -/

section Depth

variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]

/-- The elements whose principal right ideal strictly contains that of `a`. -/
def aboveR (a : M) : Finset M := Finset.univ.filter fun b => rightIdeal a ⊂ rightIdeal b

lemma mem_aboveR {a b : M} : b ∈ aboveR a ↔ rightIdeal a ⊂ rightIdeal b := by
  simp [aboveR]

/-- **The `R`-level**: the length of the longest strictly ascending chain of
principal right ideals beginning at `aM`.  Larger ideals have smaller level. -/
def rLevel (m : M) : ℕ :=
  (aboveR m).attach.sup fun b => rLevel b.1 + 1
termination_by Fintype.card M - (rightIdeal m).card
decreasing_by
  have h1 : (rightIdeal m).card < (rightIdeal b.1).card :=
    Finset.card_lt_card (mem_aboveR.1 b.2)
  have h2 : (rightIdeal b.1).card ≤ Fintype.card M := Finset.card_le_univ _
  omega

lemma rLevel_eq (m : M) : rLevel m = (aboveR m).sup fun b => rLevel b + 1 := by
  rw [rLevel]
  exact Finset.sup_attach (aboveR m) (fun b : M => rLevel b + 1)

lemma rLevel_congr {a b : M} (h : rightIdeal a = rightIdeal b) : rLevel a = rLevel b := by
  have haux : aboveR a = aboveR b := by
    ext c
    simp [mem_aboveR, h]
  rw [rLevel_eq, rLevel_eq, haux]

/-- **Strict right-ideal ascent lowers the level.** -/
theorem rLevel_lt_of_ssubset {a b : M} (h : rightIdeal a ⊂ rightIdeal b) :
    rLevel b < rLevel a := by
  have hmem : b ∈ aboveR a := mem_aboveR.2 h
  have := Finset.le_sup (f := fun c : M => rLevel c + 1) hmem
  rw [← rLevel_eq] at this
  omega

lemma rLevel_antitone {a b : M} (h : rightIdeal a ⊆ rightIdeal b) : rLevel b ≤ rLevel a := by
  rcases eq_or_ne (rightIdeal a) (rightIdeal b) with heq | hne
  · exact le_of_eq (rLevel_congr heq).symm
  · exact le_of_lt (rLevel_lt_of_ssubset (lt_of_le_of_ne h hne))

@[simp] lemma aboveR_one : aboveR (1 : M) = ∅ := by
  ext b
  simp only [mem_aboveR, Finset.notMem_empty, iff_false, rightIdeal_one]
  intro h
  exact absurd (Finset.Subset.antisymm h.1 (Finset.subset_univ _)) h.ne

@[simp] lemma rLevel_one : rLevel (1 : M) = 0 := by
  rw [rLevel_eq, aboveR_one, Finset.sup_empty]
  rfl

/-- **The right-ideal depth** `d_R(M)`: the maximum level. -/
def rDepth (M : Type*) [Monoid M] [Fintype M] [DecidableEq M] : ℕ :=
  Finset.univ.sup (rLevel : M → ℕ)

lemma rLevel_le_rDepth (m : M) : rLevel m ≤ rDepth M :=
  Finset.le_sup (f := (rLevel : M → ℕ)) (Finset.mem_univ m)

/-- A chain of principal right ideals is bounded by the size of the monoid. -/
lemma rLevel_add_card_le (m : M) : rLevel m + (rightIdeal m).card ≤ Fintype.card M := by
  induction hk : Fintype.card M - (rightIdeal m).card using Nat.strong_induction_on
    generalizing m with
  | _ k ih =>
      rcases Finset.eq_empty_or_nonempty (aboveR m) with hempty | ⟨b, hb⟩
      · rw [rLevel_eq, hempty, Finset.sup_empty]
        simpa using Finset.card_le_univ (rightIdeal m)
      · obtain ⟨c, hc, hcv⟩ := Finset.exists_mem_eq_sup (aboveR m) ⟨b, hb⟩
          (fun c : M => rLevel c + 1)
        have hlt : (rightIdeal m).card < (rightIdeal c).card :=
          Finset.card_lt_card (mem_aboveR.1 hc)
        have hub : (rightIdeal c).card ≤ Fintype.card M := Finset.card_le_univ _
        have hrec := ih (Fintype.card M - (rightIdeal c).card) (by omega) c rfl
        rw [rLevel_eq, hcv]
        omega

lemma rLevel_lt_card (m : M) : rLevel m < Fintype.card M := by
  have h := rLevel_add_card_le m
  have h1 : 1 ≤ (rightIdeal m).card :=
    Finset.card_pos.2 ⟨m, self_mem_rightIdeal m⟩
  omega

end Depth

/-! ## `R`-triviality -/

section RTrivial

variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]

/-- **`R`-trivial**: equal principal right ideals force equal elements. -/
def IsRTrivialMonoid (M : Type*) [Monoid M] [Fintype M] [DecidableEq M] : Prop :=
  ∀ a b : M, rightIdeal a = rightIdeal b → a = b

/-- In an `R`-trivial monoid a genuine right multiplication strictly shrinks
the right ideal. -/
lemma rightIdeal_mul_ssubset_of_ne (hR : IsRTrivialMonoid M) {a b : M} (h : a * b ≠ a) :
    rightIdeal (a * b) ⊂ rightIdeal a :=
  Finset.ssubset_iff_subset_ne.mpr ⟨rightIdeal_mul_subset a b, fun heq => h (hR _ _ heq)⟩

/-- **Every finite `R`-trivial monoid is aperiodic**: otherwise the levels of
the powers of some element would increase without bound. -/
theorem isAperiodicMonoid_of_isRTrivial (hR : IsRTrivialMonoid M) : IsAperiodicMonoid M := by
  refine ⟨fun a => ?_⟩
  by_contra hcon
  push Not at hcon
  have hstrict : ∀ k, 1 ≤ k → rLevel (a ^ k) < rLevel (a ^ (k + 1)) := by
    intro k hk
    have hne : a ^ k * a ≠ a ^ k := by
      rw [← pow_succ]
      exact (hcon k hk).symm
    have hss : rightIdeal (a ^ (k + 1)) ⊂ rightIdeal (a ^ k) := by
      rw [pow_succ]
      exact rightIdeal_mul_ssubset_of_ne hR hne
    exact rLevel_lt_of_ssubset hss
  have hgrow : ∀ j, j ≤ rLevel (a ^ (j + 1)) := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih => exact lt_of_le_of_lt ih (hstrict (j + 1) (by omega))
  exact absurd (hgrow (Fintype.card M)) (not_le.mpr (rLevel_lt_card _))

end RTrivial

/-! ## The prefix-product scan -/

section Scan

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] {n : ℕ}

/-- The summary step: multiply the next letter on the right. -/
def mulStep (letter : σ → M) : Fin n → M → σ → M := fun _ q a => q * letter a

variable (letter : σ → M)

/-- The prefix product after `t` letters. -/
def prefixWord (x : Fin n → σ) (t : ℕ) : M := scanState (1 : M) (mulStep letter) x t

lemma prefixWord_succ_of_lt (x : Fin n → σ) {t : ℕ} (h : t < n) :
    prefixWord letter x (t + 1) = prefixWord letter x t * letter (x ⟨t, h⟩) := by
  simp only [prefixWord, scanState, dif_pos h, mulStep]

lemma prefixWord_succ_of_not_lt (x : Fin n → σ) {t : ℕ} (h : ¬ t < n) :
    prefixWord letter x (t + 1) = prefixWord letter x t := by
  simp only [prefixWord, scanState, dif_neg h]

/-- The prefix products are the ordered range products. -/
lemma prefixWord_eq_rangeProd (x : Fin n → σ) (t : ℕ) :
    prefixWord letter x t = rangeProd (fun i => letter (x i)) 0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [rangeProd_succ_right _ (Nat.zero_le t)]
      by_cases h : t < n
      · rw [prefixWord_succ_of_lt letter x h, ih, padAt_of_lt _ h]
      · rw [prefixWord_succ_of_not_lt letter x h, ih, padAt_of_le _ (by omega), mul_one]

/-- The full prefix product is the word product. -/
lemma prefixWord_n (x : Fin n → σ) : prefixWord letter x n = wordProd letter x :=
  prefixWord_eq_rangeProd letter x n

/-- Right ideals of prefix products descend. -/
lemma rightIdeal_prefixWord_succ_subset (x : Fin n → σ) (t : ℕ) :
    rightIdeal (prefixWord letter x (t + 1)) ⊆ rightIdeal (prefixWord letter x t) := by
  by_cases h : t < n
  · rw [prefixWord_succ_of_lt letter x h]
    exact rightIdeal_mul_subset _ _
  · rw [prefixWord_succ_of_not_lt letter x h]

lemma rLevel_prefixWord_mono (x : Fin n → σ) :
    Monotone fun t => rLevel (prefixWord letter x t) :=
  monotone_nat_of_le_succ fun t =>
    rLevel_antitone (rightIdeal_prefixWord_succ_subset letter x t)

/-- **A prefix change raises the level** in an `R`-trivial monoid. -/
lemma rLevel_prefixWord_lt_of_change (hR : IsRTrivialMonoid M) (x : Fin n → σ) (t : ℕ)
    (hch : prefixWord letter x (t + 1) ≠ prefixWord letter x t) :
    rLevel (prefixWord letter x t) < rLevel (prefixWord letter x (t + 1)) :=
  rLevel_lt_of_ssubset (Finset.ssubset_iff_subset_ne.mpr
    ⟨rightIdeal_prefixWord_succ_subset letter x t, fun heq => hch (hR _ _ heq)⟩)

lemma scanCol_mulStep_eq_true_iff (x : Fin n → σ) (i : Fin n) :
    scanCol (1 : M) (mulStep letter) x i = true
      ↔ prefixWord letter x ((i : ℕ) + 1) ≠ prefixWord letter x (i : ℕ) := by
  simp [scanCol, prefixWord]

/-- **The change count is bounded by the final level**: the changed steps
inject into `{1, …, rLevel(p_n)}` by `i ↦ rLevel(p_{i+1})`. -/
theorem changeCount_le_rLevel (hR : IsRTrivialMonoid M) (x : Fin n → σ) :
    changeCount (1 : M) (mulStep letter) x ≤ rLevel (prefixWord letter x n) := by
  classical
  have hmaps : Set.MapsTo (fun i : Fin n => rLevel (prefixWord letter x ((i : ℕ) + 1)))
      ↑(Finset.univ.filter fun i => scanCol (1 : M) (mulStep letter) x i = true)
      ↑(Finset.Icc 1 (rLevel (prefixWord letter x n))) := by
    intro i hi
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    have hch := (scanCol_mulStep_eq_true_iff letter x i).mp hi.2
    have hlt := rLevel_prefixWord_lt_of_change letter hR x i hch
    have hle : rLevel (prefixWord letter x ((i : ℕ) + 1)) ≤ rLevel (prefixWord letter x n) :=
      rLevel_prefixWord_mono letter x (Nat.succ_le_of_lt i.isLt)
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨by omega, hle⟩
  have hinj : Set.InjOn (fun i : Fin n => rLevel (prefixWord letter x ((i : ℕ) + 1)))
      ↑(Finset.univ.filter fun i => scanCol (1 : M) (mulStep letter) x i = true) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_filter] at hi hj
    dsimp only at hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : rLevel (prefixWord letter x ((i : ℕ) + 1))
          ≤ rLevel (prefixWord letter x (j : ℕ)) :=
        rLevel_prefixWord_mono letter x (Nat.succ_le_of_lt (Fin.lt_def.mp hlt))
      have h2 := rLevel_prefixWord_lt_of_change letter hR x j
        ((scanCol_mulStep_eq_true_iff letter x j).mp hj.2)
      omega
    · have h1 : rLevel (prefixWord letter x ((j : ℕ) + 1))
          ≤ rLevel (prefixWord letter x (i : ℕ)) :=
        rLevel_prefixWord_mono letter x (Nat.succ_le_of_lt (Fin.lt_def.mp hlt))
      have h2 := rLevel_prefixWord_lt_of_change letter hR x i
        ((scanCol_mulStep_eq_true_iff letter x i).mp hi.2)
      omega
  calc changeCount (1 : M) (mulStep letter) x
      ≤ (Finset.Icc 1 (rLevel (prefixWord letter x n))).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = rLevel (prefixWord letter x n) := by simp

theorem changeCount_le_rDepth (hR : IsRTrivialMonoid M) (x : Fin n → σ) :
    changeCount (1 : M) (mulStep letter) x ≤ rDepth M :=
  (changeCount_le_rLevel letter hR x).trans (rLevel_le_rDepth _)

lemma changeCount_mulStep_le_length (x : Fin n → σ) :
    changeCount (1 : M) (mulStep letter) x ≤ n := by
  refine (Finset.card_filter_le _ _).trans_eq ?_
  simp

/-! ## The bounds -/

/-- **Theorem `thm:rtrivial`, certificate form**: the product in a finite
`R`-trivial monoid has an explicit dual of cost `8√(n·min{n, d_R(M)})`,
uniformly in the letter alphabet. -/
theorem hasDual_wordProd_of_isRTrivial (hR : IsRTrivialMonoid M) :
    HasDual (fun x : Fin n → σ => wordProd letter x)
      (8 * Real.sqrt ((n : ℝ) * ((min n (rDepth M) : ℕ) : ℝ))) := by
  have h := hasDual_scan (n := n) (1 : M) (mulStep letter) (id : M → M)
    (C := min n (rDepth M)) fun x =>
      le_min (changeCount_mulStep_le_length letter x) (changeCount_le_rDepth letter hR x)
  exact h.ofEq fun x => by
    show prefixWord letter x n = wordProd letter x
    exact prefixWord_n letter x

/-- **Theorem `thm:rtrivial`**: `ADV±(Prod_{M,n}) ≤ 8√(n·min{n, d_R(M)})`. -/
theorem advPM_wordProd_le_of_isRTrivial (hR : IsRTrivialMonoid M) :
    advPM (fun x : Fin n → σ => wordProd letter x)
      ≤ 8 * Real.sqrt ((n : ℝ) * ((min n (rDepth M) : ℕ) : ℝ)) :=
  advPM_le_of_hasDual (by positivity) (hasDual_wordProd_of_isRTrivial letter hR)

/-- **The promise form**: for any bound `C` on the number of prefix changes
over the promised inputs (the paper's `C_𝒟`), the product has a dual of cost
`8√(n·C)` on the promise.  No `R`-triviality is needed here. -/
theorem hasDualOn_wordProd_of_changeCount {X : Type} [Fintype X] [DecidableEq X]
    (read : X → Fin n → σ)
    {C : ℕ} (hC : ∀ x, changeCount (1 : M) (mulStep letter) (read x) ≤ C) :
    HasDualOn read (fun x => wordProd letter (read x))
      (8 * Real.sqrt ((n : ℝ) * (C : ℝ))) :=
  (hasDualOn_scan (n := n) (1 : M) (mulStep letter) read (id : M → M) hC).ofEq fun x => by
    show prefixWord letter (read x) n = wordProd letter (read x)
    exact prefixWord_n letter (read x)

theorem advPMOn_wordProd_le_of_changeCount {X : Type} [Fintype X] [DecidableEq X]
    (read : X → Fin n → σ)
    {C : ℕ} (hC : ∀ x, changeCount (1 : M) (mulStep letter) (read x) ≤ C) :
    advPMOn read (fun x => wordProd letter (read x))
      ≤ 8 * Real.sqrt ((n : ℝ) * (C : ℝ)) :=
  advPMOn_le_of_hasDualOn (by positivity) (hasDualOn_wordProd_of_changeCount letter read hC)

end Scan

end MonoidProduct
