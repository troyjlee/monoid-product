import MonoidProduct.Aperiodic.Prefix
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Suffix search

The mirror of `MonoidProduct/Aperiodic/Prefix.lean`: condition `(V)` of the
decomposition theorem (`thm:decomp` in the paper) asks for a position `j` at
which the letter is `a` and the *suffix* after it has product `r`, for some
`(a,r) ∈ F m`.

One could derive this by reversing the word and passing to `Mᵐᵒᵖ`.
That route needs the whole ideal/level layer transported across `MulOpposite`,
and the transport is longer than the mirror it saves.  So the search is built
directly, and the only change of substance is the parameter it searches over.

The right parameter is the **suffix length** `t`, not the cut position: as `t`
grows the suffix grows and its principal *left* ideal shrinks, so

  `K = { t | r ∈ M · (suffix of length t) }`

is again closed under shortening, and `QueryTree.stepUp_of_shorteningClosed`
applies verbatim.  A boundary at `t` names the position `n - t - 1`, which is
where the letter `a` must sit.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- `leftAbove r = { s | r ∈ Ms }`. -/
def leftAbove (r : M) : Finset M := Finset.univ.filter fun s => r ∈ leftIdeal s

@[simp] lemma mem_leftAbove {r s : M} : s ∈ leftAbove r ↔ r ∈ leftIdeal s := by
  simp [leftAbove]

lemma self_mem_leftAbove (r : M) : r ∈ leftAbove r :=
  mem_leftAbove.2 (self_mem_leftIdeal r)

/-- **The recursion does not ascend**, on this side either. -/
lemma twoIdeal_subset_of_mem_leftAbove {r s : M} (h : s ∈ leftAbove r) :
    twoIdeal r ⊆ twoIdeal s := by
  obtain ⟨p, hp⟩ := mem_leftIdeal.1 (mem_leftAbove.1 h)
  exact twoIdeal_subset_of_mem (mem_twoIdeal.2 ⟨p, 1, by rw [mul_one]; exact hp⟩)

lemma jLevel_le_of_mem_leftAbove [IsAperiodicMonoid M] {r s : M}
    (h : s ∈ leftAbove r) : jLevel s ≤ jLevel r :=
  jLevel_antitone (twoIdeal_subset_of_mem_leftAbove h)

end

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The test and the event -/

/-- The suffix of length `t` lies in `K`: `r` is a left multiple of its
product.  Lengths past `n` are excluded, so the search has a right endpoint to
bracket against. -/
def inKR (letter : σ → M) (r : M) {n : ℕ} (x : Fin n → σ) (t : ℕ) : Bool :=
  decide (t ≤ n ∧ r ∈ leftIdeal (winProd letter x (n - t) n))

lemma inKR_zero (letter : σ → M) (r : M) {n : ℕ} (x : Fin n → σ) :
    inKR letter r x 0 = true := by
  simp only [inKR, decide_eq_true_eq]
  refine ⟨Nat.zero_le n, ?_⟩
  rw [Nat.sub_zero, winProd, rangeProd_self, leftIdeal_one]
  exact Finset.mem_univ r

lemma inKR_of_gt (letter : σ → M) (r : M) {n : ℕ} (x : Fin n → σ) {t : ℕ}
    (h : n < t) : inKR letter r x t = false := by
  have ht : ¬ (t ≤ n) := by omega
  simp [inKR, ht]

/-- **`K` is closed under shortening**: the left ideals of the suffixes only
shrink as the suffix grows. -/
lemma inKR_mono (letter : σ → M) (r : M) {n : ℕ} (x : Fin n → σ) {t u : ℕ}
    (htu : t ≤ u) (h : inKR letter r x u = true) : inKR letter r x t = true := by
  simp only [inKR, decide_eq_true_eq] at h ⊢
  refine ⟨by omega, ?_⟩
  have hsplit : winProd letter x (n - u) (n - t) * winProd letter x (n - t) n
      = winProd letter x (n - u) n :=
    rangeProd_split _ (by omega) (by omega)
  have hsub : leftIdeal (winProd letter x (n - u) n)
      ⊆ leftIdeal (winProd letter x (n - t) n) := by
    rw [← hsplit]
    exact leftIdeal_mul_subset _ _
  exact hsub h.2

/-- **The suffix event** for one pair `(a, r) ∈ F m`. -/
def suffixEvent (letter : σ → M) (a r : M) {n : ℕ} (x : Fin n → σ) : Bool :=
  decide (∃ j : Fin n, letter (x j) = a ∧ winProd letter x ((j : ℕ) + 1) n = r)

lemma inKR_of_event {letter : σ → M} {r : M} {n : ℕ} {x : Fin n → σ} {t : ℕ}
    (ht : t ≤ n) (hprod : winProd letter x (n - t) n = r) :
    inKR letter r x t = true := by
  simp only [inKR, decide_eq_true_eq]
  exact ⟨ht, by rw [hprod]; exact self_mem_leftIdeal r⟩

/-- One letter earlier the suffix has left `K`: this is where the strict
inclusion `leftIdeal (a*r) ⊊ leftIdeal r` is used. -/
lemma not_inKR_succ_of_event {letter : σ → M} {a r : M}
    (hla : leftIdeal (a * r) ⊂ leftIdeal r) {n : ℕ} {x : Fin n → σ} {t : ℕ}
    (ht : t < n) (hprod : winProd letter x (n - t) n = r)
    (hlet : padAt (fun s => letter (x s)) (n - t - 1) = a) :
    inKR letter r x (t + 1) = false := by
  have hstep : winProd letter x (n - (t + 1)) n = a * r := by
    have hsplit : winProd letter x (n - (t + 1)) (n - t)
        * winProd letter x (n - t) n = winProd letter x (n - (t + 1)) n :=
      rangeProd_split _ (by omega) (by omega)
    have hone : winProd letter x (n - (t + 1)) (n - t)
        = padAt (fun s => letter (x s)) (n - t - 1) := by
      rw [show n - t - 1 = n - (t + 1) from by omega,
        show n - t = n - (t + 1) + 1 from by omega, winProd, rangeProd_eq_padAt]
    rw [← hsplit, hone, hlet, hprod]
  simp only [inKR, decide_eq_false_iff_not, not_and, hstep]
  intro _ hmem
  exact absurd (Finset.Subset.antisymm (leftIdeal_mul_subset a r)
    (leftIdeal_subset_of_mem hmem)) (ne_of_lt hla)

/-! ## The search tree -/

/-- The semantics of the three queries; `⟨0, t⟩` asks whether the suffix of
length `t` has left `K`, `⟨1, t⟩` whether its product is exactly `r`, and
`⟨2, t⟩` whether the letter just before it is `a`. -/
def suffixQuery (letter : σ → M) (a r : M) {n : ℕ}
    (p : Fin 3 × Fin (n + 2)) (x : Fin n → σ) : Bool :=
  if p.1 = 0 then !(inKR letter r x p.2)
  else if p.1 = 1 then
    decide ((p.2 : ℕ) ≤ n ∧ winProd letter x (n - (p.2 : ℕ)) n = r)
  else decide (padAt (fun s => letter (x s)) (n - (p.2 : ℕ) - 1) = a)

/-- The suffix-search tree.  Same shape as `prefixTree`; only the leaf's
position bookkeeping differs. -/
def suffixTree (n : ℕ) : QueryTree (Fin 3 × Fin (n + 2)) Bool :=
  (QueryTree.boundaryTree (fun t => (0, clampPos n t))
      (Nat.clog 2 (n + 1)) 0 (n + 1)).bind
    fun t => .query (1, clampPos n t) fun b1 =>
      .query (2, clampPos n t) fun b2 => .leaf (b1 && b2 && decide (t < n))

lemma depth_suffixTree (n : ℕ) :
    (suffixTree n).depth ≤ Nat.clog 2 (n + 1) + 2 := by
  refine le_trans (QueryTree.depth_bind_le _ _ (D := 2) fun t => ?_) ?_
  · simp [QueryTree.depth]
  · exact Nat.add_le_add_right (QueryTree.depth_boundaryTree _ _ 0 (n + 1)) 2

/-! ## Correctness -/

theorem suffixTree_eval (letter : σ → M) {a r : M}
    (hla : leftIdeal (a * r) ⊂ leftIdeal r) {n : ℕ} (x : Fin n → σ) :
    (suffixTree n).eval (fun p => suffixQuery letter a r p x)
      = suffixEvent letter a r x := by
  classical
  set z : Fin 3 × Fin (n + 2) → Bool := fun p => suffixQuery letter a r p x
    with hzdef
  have hzq : ∀ t : ℕ, z ((0 : Fin 3), clampPos n t)
      = !(inKR letter r x (min t (n + 1))) := by
    intro t
    rw [hzdef]
    simp only [suffixQuery, clampPos_val, ite_true]
  have h0 : z ((0 : Fin 3), clampPos n 0) = false := by
    rw [hzq 0, Nat.min_eq_left (Nat.zero_le _), inKR_zero]; rfl
  have h1 : z ((0 : Fin 3), clampPos n (n + 1)) = true := by
    rw [hzq (n + 1), Nat.min_self, inKR_of_gt letter r x (by omega)]; rfl
  have hstep : QueryTree.StepUp (fun t => ((0 : Fin 3), clampPos n t)) z 0 (n + 1) := by
    refine QueryTree.stepUp_of_shorteningClosed _ z (fun t u hut hj => ?_) 0 (n + 1)
    rw [hzq t] at hj
    rw [hzq u]
    have hK : inKR letter r x (min t (n + 1)) = true := by
      by_contra hcon
      rw [Bool.not_eq_true] at hcon
      rw [hcon] at hj
      exact absurd hj (by simp)
    rw [inKR_mono letter r x (min_le_min hut (le_refl _)) hK]
    rfl
  have hfuel : (n + 1) - 0 ≤ 2 ^ Nat.clog 2 (n + 1) := by
    simpa using Nat.le_pow_clog (b := 2) (by norm_num) (n + 1)
  simp only [suffixTree, QueryTree.eval_bind, QueryTree.eval_query,
    QueryTree.eval_leaf]
  obtain ⟨-, hhi, -, -⟩ := QueryTree.boundaryTree_spec
    (fun t => ((0 : Fin 3), clampPos n t)) z (Nat.clog 2 (n + 1)) 0 (n + 1)
    (by omega) hfuel h0 h1
  set t := (QueryTree.boundaryTree (fun t => ((0 : Fin 3), clampPos n t))
    (Nat.clog 2 (n + 1)) 0 (n + 1)).eval z with htdef
  have htle : t ≤ n := by omega
  have hct : ((clampPos n t : Fin (n + 2)) : ℕ) = t := clampPos_val_of_le (by omega)
  have hq1 : z ((1 : Fin 3), clampPos n t)
      = decide (t ≤ n ∧ winProd letter x (n - t) n = r) := by
    rw [hzdef]
    simp only [suffixQuery, hct, if_neg (by decide : ¬ ((1 : Fin 3) = 0)),
      if_pos rfl, ite_true]
  have hq2 : z ((2 : Fin 3), clampPos n t)
      = decide (padAt (fun s => letter (x s)) (n - t - 1) = a) := by
    rw [hzdef]
    simp only [suffixQuery, hct, if_neg (by decide : ¬ ((2 : Fin 3) = 0)),
      if_neg (by decide : ¬ ((2 : Fin 3) = 1))]
  have key : ∀ u : ℕ, u < n → winProd letter x (n - u) n = r →
      padAt (fun s => letter (x s)) (n - u - 1) = a → t = u := by
    intro u hu hprod hlet
    refine QueryTree.boundaryTree_eq_of_stepUp _ z hstep (by omega) hfuel h0 h1
      (Nat.zero_le u) (by omega) ?_ ?_
    · rw [hzq u, Nat.min_eq_left (by omega), inKR_of_event (by omega) hprod]; rfl
    · rw [hzq (u + 1), Nat.min_eq_left (by omega),
        not_inKR_succ_of_event hla hu hprod hlet]; rfl
  rw [hq1, hq2, suffixEvent, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨-, hprod⟩, hlet⟩, hlt⟩
    refine ⟨⟨n - t - 1, by omega⟩, ?_, ?_⟩
    · rwa [padAt_of_lt (fun s => letter (x s)) (show n - t - 1 < n by omega)] at hlet
    · simpa [show n - t - 1 + 1 = n - t from by omega] using hprod
  · rintro ⟨j, hlet, hprod⟩
    have hju := j.isLt
    have hprod' : winProd letter x (n - (n - (j : ℕ) - 1)) n = r := by
      rwa [show n - (n - (j : ℕ) - 1) = (j : ℕ) + 1 from by omega]
    have hlet' : padAt (fun s => letter (x s)) (n - (n - (j : ℕ) - 1) - 1) = a := by
      rw [show n - (n - (j : ℕ) - 1) - 1 = (j : ℕ) from by omega,
        padAt_of_lt _ hju]
      exact hlet
    have htt : t = n - (j : ℕ) - 1 := key _ (by omega) hprod' hlet'
    rw [htt]
    exact ⟨⟨⟨by omega, hprod'⟩, hlet'⟩, by omega⟩

/-! ## Cost -/

/-- One price for every query the suffix search can make.  As on the prefix
side, the membership query is a square-root search over `leftAbove r` only, so
no equality test is ever run at a value outside it. -/
theorem hasDual_suffixQuery (letter : σ → M) (a r : M) {n : ℕ} {Q : ℝ}
    (hQ : 0 ≤ Q)
    (hrec : ∀ s ∈ leftAbove r, ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q)
    (p : Fin 3 × Fin (n + 2)) :
    HasDual (fun x : Fin n → σ => suffixQuery letter a r p x)
      (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2) := by
  classical
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((Fintype.card M : ℝ) + 1) := by
    have hc : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((Fintype.card M : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at h1
  have hbig : (0 : ℝ) ≤ Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) := by
    nlinarith
  have hQle : Q ≤ Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) := by nlinarith
  have hmono : Q * (24 * Real.sqrt (((leftAbove r).card : ℝ) + 1))
      ≤ Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) := by
    have hc : ((leftAbove r).card : ℝ) ≤ (Fintype.card M : ℝ) := by
      exact_mod_cast Finset.card_le_univ (leftAbove r)
    have := Real.sqrt_le_sqrt (show ((leftAbove r).card : ℝ) + 1
      ≤ (Fintype.card M : ℝ) + 1 by linarith)
    nlinarith [Real.sqrt_nonneg (((leftAbove r).card : ℝ) + 1)]
  set t := ((p.2 : Fin (n + 2)) : ℕ) with htdef
  by_cases hp0 : p.1 = 0
  · refine (?_ : HasDual (fun x : Fin n → σ => !(inKR letter r x t)) _).ofEq
      fun x => by rw [suffixQuery, if_pos hp0]
    by_cases htn : t ≤ n
    · have hmem := hasDual_winMem letter (leftAbove r) (le_refl n)
        (show n - t ≤ n by omega) hQ
        fun s hs => hrec s hs (n - (n - t)) (by omega)
      have hneg : HasDual (fun x : Fin n → σ =>
          !(decide (winProd letter x (n - t) n ∈ leftAbove r)))
          (Q * (24 * Real.sqrt (((leftAbove r).card : ℝ) + 1))) :=
        hmem.ofKer fun u v => by simp
      exact ((hneg.mono hmono).ofEq
        fun x => by simp [inKR, htn, mem_leftAbove]).mono (by linarith)
    · refine ((hasDual_const (f := fun _ : Fin n → σ => (true : Bool))
        (fun _ _ => rfl)).mono (by linarith)).ofEq fun x => ?_
      rw [inKR_of_gt letter r x (by omega)]
      rfl
  · by_cases hp1 : p.1 = 1
    · refine (?_ : HasDual (fun x : Fin n → σ =>
        decide (t ≤ n ∧ winProd letter x (n - t) n = r)) _).ofEq
          fun x => by rw [suffixQuery, if_neg hp0, if_pos hp1]
      by_cases htn : t ≤ n
      · refine ((hasDual_winEq' letter r (le_refl n) (show n - t ≤ n by omega)
          (hrec r (self_mem_leftAbove r) (n - (n - t)) (by omega))).ofEq
            fun x => by simp [htn]).mono (by linarith)
      · refine ((hasDual_const (f := fun _ : Fin n → σ => (false : Bool))
          (fun _ _ => rfl)).mono (by linarith)).ofEq fun x => ?_
        simp [htn]
    · refine ((hasDual_letterTest letter a (n - t - 1)).mono (by linarith)).ofEq
        fun x => by rw [suffixQuery, if_neg hp0, if_neg hp1]

/-- **The prefix-search lemma (`lem:prefix`), suffix half.** -/
theorem hasDual_suffixEvent (letter : σ → M) {a r : M}
    (hla : leftIdeal (a * r) ⊂ leftIdeal r) {n : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s ∈ leftAbove r, ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => suffixEvent letter a r x)
      (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
        * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((Fintype.card M : ℝ) + 1) := by
    have hc : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((Fintype.card M : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at h1
  have hc₀ : (0 : ℝ)
      ≤ Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2 := by nlinarith
  have hbase := QueryTree.hasDual_shared_depth (ι := Fin n) (σ := σ) (suffixTree n)
    hc₀ (hasDual_suffixQuery letter a r hQ hrec)
  refine (hbase.ofEq fun x => suffixTree_eval letter hla x).mono ?_
  refine mul_le_mul_of_nonneg_right ?_ hc₀
  have hd : ((suffixTree n).depth : ℝ) ≤ (Nat.clog 2 (n + 1) : ℝ) + 2 := by
    exact_mod_cast depth_suffixTree n
  linarith

end

/-! ## The bridge to the decomposition theorem

`UEvent` and `VEvent` are stated in `MonoidProduct/Aperiodic/Decomposition.lean` for
a word of monoid elements; the searches above run on a word of letters.  These
two lemmas say the two readings agree, so the inductive step can put an
`E m`-indexed disjunction of `prefixEvent`s where `thm:decomp` asks for `(U)`. -/

section Bridge

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

lemma uEvent_iff (letter : σ → M) (m : M) {n : ℕ} (y : Fin n → σ) :
    UEvent m (fun i => letter (y i))
      ↔ ∃ p ∈ setE m, prefixEvent letter p.1 p.2 y = true := by
  constructor
  · rintro ⟨i, hi, r, a, hE, hprod, hlet⟩
    refine ⟨(r, a), hE, ?_⟩
    simp only [prefixEvent, decide_eq_true_eq]
    exact ⟨⟨i, hi⟩, hprod, by rwa [padAt_of_lt _ hi] at hlet⟩
  · rintro ⟨⟨r, a⟩, hE, hev⟩
    simp only [prefixEvent, decide_eq_true_eq] at hev
    obtain ⟨i, hprod, hlet⟩ := hev
    exact ⟨(i : ℕ), i.isLt, r, a, hE, hprod, by rw [padAt_of_lt _ i.isLt]; exact hlet⟩

lemma vEvent_iff (letter : σ → M) (m : M) {n : ℕ} (y : Fin n → σ) :
    VEvent m (fun i => letter (y i))
      ↔ ∃ p ∈ setF m, suffixEvent letter p.1 p.2 y = true := by
  constructor
  · rintro ⟨j, hj, a, r, hF, hlet, hprod⟩
    refine ⟨(a, r), hF, ?_⟩
    simp only [suffixEvent, decide_eq_true_eq]
    exact ⟨⟨j, hj⟩, by rwa [padAt_of_lt _ hj] at hlet, hprod⟩
  · rintro ⟨⟨a, r⟩, hF, hev⟩
    simp only [suffixEvent, decide_eq_true_eq] at hev
    obtain ⟨j, hlet, hprod⟩ := hev
    exact ⟨(j : ℕ), j.isLt, a, r, hF, by rw [padAt_of_lt _ j.isLt]; exact hlet, hprod⟩

end Bridge

end MonoidProduct
