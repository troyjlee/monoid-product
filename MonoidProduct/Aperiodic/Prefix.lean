import MonoidProduct.Aperiodic.EqProd
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Prefix search

The paper's prefix search (`lem:prefix`).  Condition `(U)` of the decomposition
theorem (`thm:decomp`) asks for a position `i` at which the prefix product is `r` and the next letter
is `a`, for some `(r,a) ∈ E m`.  Finding it by testing every position costs
`Θ(n)`; binary search costs `⌈log₂ n⌉`, and `QuantumQueryComplexity/DecisionTree.lean` prices
an adaptive search at its depth.

What makes the search legitimate is that the positions passing the test

  `K = { j | r ∈ (prefix j) · M }`

form an **initial segment**: right ideals only shrink as the prefix grows, so a
position passing implies every shorter one passes.  That is
`QueryTree.stepUp_of_shorteningClosed`, and it turns the sign change the search
returns into *the* boundary.  If the event happens at `i`, then `i ∈ K` because
`r ∈ rM`, and `i+1 ∉ K` because the prefix product there is `ra` and
`rightIdeal (r*a) ⊊ rightIdeal r`; so the boundary is exactly `i`, and two more
queries at the leaf confirm it.

Each `K`-membership query is a function of one window product, which
`hasDual_ofWinProd` prices at `2 |M|` recursive equality tests.  Every `s` those
tests are run at satisfies `MrM ⊆ MsM`, hence `jLevel s ≤ jLevel r` — the
recursion does not ascend.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The prefix-closed set

`rightAbove r` is the set of monoid elements a prefix may have without having
already left `K`. -/

/-- `rightAbove r = { s | r ∈ sM }`. -/
def rightAbove (r : M) : Finset M := Finset.univ.filter fun s => r ∈ rightIdeal s

@[simp] lemma mem_rightAbove {r s : M} : s ∈ rightAbove r ↔ r ∈ rightIdeal s := by
  simp [rightAbove]

lemma self_mem_rightAbove (r : M) : r ∈ rightAbove r :=
  mem_rightAbove.2 (self_mem_rightIdeal r)

/-- **The recursion does not ascend.**  Everything the prefix test is run at
generates an ideal containing the target's. -/
lemma twoIdeal_subset_of_mem_rightAbove {r s : M} (h : s ∈ rightAbove r) :
    twoIdeal r ⊆ twoIdeal s := by
  obtain ⟨q, hq⟩ := mem_rightIdeal.1 (mem_rightAbove.1 h)
  exact twoIdeal_subset_of_mem (mem_twoIdeal.2 ⟨1, q, by rw [one_mul]; exact hq⟩)

lemma jLevel_le_of_mem_rightAbove [IsAperiodicMonoid M] {r s : M}
    (h : s ∈ rightAbove r) : jLevel s ≤ jLevel r :=
  jLevel_antitone (twoIdeal_subset_of_mem_rightAbove h)

end

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The test and the event -/

/-- The prefix of length `j` lies in `K`.  Positions past `n` are excluded, so
the search always has a right endpoint outside `K` to bracket against. -/
def inK (letter : σ → M) (r : M) {n : ℕ} (x : Fin n → σ) (j : ℕ) : Bool :=
  decide (j ≤ n ∧ r ∈ rightIdeal (winProd letter x 0 j))

lemma inK_zero (letter : σ → M) (r : M) {n : ℕ} (x : Fin n → σ) :
    inK letter r x 0 = true := by
  simp only [inK, decide_eq_true_eq]
  refine ⟨Nat.zero_le n, ?_⟩
  rw [winProd, rangeProd_self, rightIdeal_one]
  exact Finset.mem_univ r

lemma inK_of_gt (letter : σ → M) (r : M) {n : ℕ} (x : Fin n → σ) {j : ℕ}
    (h : n < j) : inK letter r x j = false := by
  have hj : ¬ (j ≤ n) := by omega
  simp [inK, hj]

/-- **`K` is closed under shortening**: the right ideals of the prefixes only
shrink. -/
lemma inK_mono (letter : σ → M) (r : M) {n : ℕ} (x : Fin n → σ) {j k : ℕ}
    (hjk : j ≤ k) (h : inK letter r x k = true) : inK letter r x j = true := by
  simp only [inK, decide_eq_true_eq] at h ⊢
  refine ⟨by omega, ?_⟩
  have hsplit : winProd letter x 0 j * winProd letter x j k
      = winProd letter x 0 k := rangeProd_split _ (Nat.zero_le j) hjk
  have hsub : rightIdeal (winProd letter x 0 k)
      ⊆ rightIdeal (winProd letter x 0 j) := by
    rw [← hsplit]
    exact rightIdeal_mul_subset _ _
  exact hsub h.2

/-- **The prefix event** for one pair `(r, a) ∈ E m`. -/
def prefixEvent (letter : σ → M) (r a : M) {n : ℕ} (x : Fin n → σ) : Bool :=
  decide (∃ i : Fin n, winProd letter x 0 i = r ∧ letter (x i) = a)

lemma inK_of_event {letter : σ → M} {r : M} {n : ℕ} {x : Fin n → σ} {j : ℕ}
    (hj : j ≤ n) (hprod : winProd letter x 0 j = r) : inK letter r x j = true := by
  simp only [inK, decide_eq_true_eq]
  exact ⟨hj, by rw [hprod]; exact self_mem_rightIdeal r⟩

/-- Past the event the prefix has left `K`: this is where the strict inclusion
`rightIdeal (r*a) ⊊ rightIdeal r` is used. -/
lemma not_inK_succ_of_event {letter : σ → M} {r a : M}
    (hra : rightIdeal (r * a) ⊂ rightIdeal r) {n : ℕ} {x : Fin n → σ} {j : ℕ}
    (hj : j < n) (hprod : winProd letter x 0 j = r)
    (hlet : padAt (fun t => letter (x t)) j = a) :
    inK letter r x (j + 1) = false := by
  have hstep : winProd letter x 0 (j + 1) = r * a := by
    rw [winProd, rangeProd_succ_right _ (Nat.zero_le j), hlet]
    exact congrArg (· * a) hprod
  simp only [inK, decide_eq_false_iff_not, not_and, hstep]
  intro _ hmem
  exact absurd (Finset.Subset.antisymm (rightIdeal_mul_subset r a)
    (rightIdeal_subset_of_mem hmem)) (ne_of_lt hra)

/-! ## The search tree

Three kinds of query, all at a position in `[0, n+1]`: `⟨0, j⟩` asks whether the
prefix of length `j` has *left* `K`, `⟨1, j⟩` whether its product is exactly
`r`, and `⟨2, j⟩` whether the letter at `j` is `a`. -/

/-- Clamping a position into the label type. -/
def clampPos (n j : ℕ) : Fin (n + 2) := ⟨min j (n + 1), by omega⟩

lemma clampPos_val (n j : ℕ) : (clampPos n j : ℕ) = min j (n + 1) := rfl

lemma clampPos_val_of_le {n j : ℕ} (h : j ≤ n + 1) : (clampPos n j : ℕ) = j := by
  simp [clampPos, Nat.min_eq_left h]

/-- The semantics of the three queries. -/
def prefixQuery (letter : σ → M) (r a : M) {n : ℕ}
    (p : Fin 3 × Fin (n + 2)) (x : Fin n → σ) : Bool :=
  if p.1 = 0 then !(inK letter r x p.2)
  else if p.1 = 1 then decide ((p.2 : ℕ) ≤ n ∧ winProd letter x 0 p.2 = r)
  else decide (padAt (fun t => letter (x t)) p.2 = a)

/-- **The prefix-search tree.**  Binary search for the boundary of `K`, then two
confirming queries at the leaf.  The tree itself depends only on `n` — the
target `(r,a)` enters through the *semantics* of the labels. -/
def prefixTree (n : ℕ) : QueryTree (Fin 3 × Fin (n + 2)) Bool :=
  (QueryTree.boundaryTree (fun j => (0, clampPos n j))
      (Nat.clog 2 (n + 1)) 0 (n + 1)).bind
    fun i => .query (1, clampPos n i) fun b1 =>
      .query (2, clampPos n i) fun b2 => .leaf (b1 && b2 && decide (i < n))

lemma depth_prefixTree (n : ℕ) :
    (prefixTree n).depth ≤ Nat.clog 2 (n + 1) + 2 := by
  refine le_trans (QueryTree.depth_bind_le _ _ (D := 2) fun i => ?_) ?_
  · simp [QueryTree.depth]
  · exact Nat.add_le_add_right (QueryTree.depth_boundaryTree _ _ 0 (n + 1)) 2

/-! ## Correctness -/

theorem prefixTree_eval (letter : σ → M) {r a : M}
    (hra : rightIdeal (r * a) ⊂ rightIdeal r) {n : ℕ} (x : Fin n → σ) :
    (prefixTree n).eval (fun p => prefixQuery letter r a p x)
      = prefixEvent letter r a x := by
  classical
  set z : Fin 3 × Fin (n + 2) → Bool := fun p => prefixQuery letter r a p x
    with hzdef
  -- the search reads exactly the `K`-membership test
  have hzq : ∀ j : ℕ, z ((0 : Fin 3), clampPos n j)
      = !(inK letter r x (min j (n + 1))) := by
    intro j
    rw [hzdef]
    simp only [prefixQuery, clampPos_val, if_pos rfl, ite_true]
  have h0 : z ((0 : Fin 3), clampPos n 0) = false := by
    rw [hzq 0, Nat.min_eq_left (Nat.zero_le _), inK_zero]; rfl
  have h1 : z ((0 : Fin 3), clampPos n (n + 1)) = true := by
    rw [hzq (n + 1), Nat.min_self, inK_of_gt letter r x (by omega)]; rfl
  have hstep : QueryTree.StepUp (fun j => ((0 : Fin 3), clampPos n j)) z 0 (n + 1) := by
    refine QueryTree.stepUp_of_shorteningClosed _ z (fun j k hkj hj => ?_) 0 (n + 1)
    rw [hzq j] at hj
    rw [hzq k]
    have hK : inK letter r x (min j (n + 1)) = true := by
      by_contra hcon
      rw [Bool.not_eq_true] at hcon
      rw [hcon] at hj
      exact absurd hj (by simp)
    rw [inK_mono letter r x (min_le_min hkj (le_refl _)) hK]
    rfl
  have hfuel : (n + 1) - 0 ≤ 2 ^ Nat.clog 2 (n + 1) := by
    simpa using Nat.le_pow_clog (b := 2) (by norm_num) (n + 1)
  -- unfold the tree, then name the boundary the search returns
  simp only [prefixTree, QueryTree.eval_bind, QueryTree.eval_query,
    QueryTree.eval_leaf]
  obtain ⟨-, hhi, -, -⟩ := QueryTree.boundaryTree_spec
    (fun j => ((0 : Fin 3), clampPos n j)) z (Nat.clog 2 (n + 1)) 0 (n + 1)
    (by omega) hfuel h0 h1
  set i := (QueryTree.boundaryTree (fun j => ((0 : Fin 3), clampPos n j))
    (Nat.clog 2 (n + 1)) 0 (n + 1)).eval z with hidef
  have hile : i ≤ n := by omega
  have hci : ((clampPos n i : Fin (n + 2)) : ℕ) = i :=
    clampPos_val_of_le (by omega)
  have hq1 : z ((1 : Fin 3), clampPos n i)
      = decide (i ≤ n ∧ winProd letter x 0 i = r) := by
    rw [hzdef]
    simp only [prefixQuery, hci, if_neg (by decide : ¬ ((1 : Fin 3) = 0)),
      if_pos rfl, ite_true]
  have hq2 : z ((2 : Fin 3), clampPos n i)
      = decide (padAt (fun t => letter (x t)) i = a) := by
    rw [hzdef]
    simp only [prefixQuery, hci, if_neg (by decide : ¬ ((2 : Fin 3) = 0)),
      if_neg (by decide : ¬ ((2 : Fin 3) = 1))]
  -- the boundary is *the* event position
  have key : ∀ j : ℕ, j < n → winProd letter x 0 j = r →
      padAt (fun t => letter (x t)) j = a → i = j := by
    intro j hj hprod hlet
    refine QueryTree.boundaryTree_eq_of_stepUp _ z hstep (by omega) hfuel h0 h1
      (Nat.zero_le j) (by omega) ?_ ?_
    · rw [hzq j, Nat.min_eq_left (by omega), inK_of_event (by omega) hprod]; rfl
    · rw [hzq (j + 1), Nat.min_eq_left (by omega),
        not_inK_succ_of_event hra hj hprod hlet]; rfl
  rw [hq1, hq2, prefixEvent, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨-, hprod⟩, hlet⟩, hlt⟩
    refine ⟨⟨i, hlt⟩, hprod, ?_⟩
    rwa [padAt_of_lt (fun t => letter (x t)) hlt] at hlet
  · rintro ⟨i₀, hprod, hlet⟩
    have hlet' : padAt (fun t => letter (x t)) (i₀ : ℕ) = a := by
      rw [padAt_of_lt _ i₀.isLt]; exact hlet
    have hii : i = (i₀ : ℕ) := key _ i₀.isLt hprod hlet'
    rw [hii]
    exact ⟨⟨⟨le_of_lt i₀.isLt, hprod⟩, hlet'⟩, i₀.isLt⟩

end


/-! ## Cost

Each `K`-membership query is a function of one window product, so it costs
`2 |M|` recursive equality tests; the two confirming queries cost one test and
one letter read.  The search makes `⌈log₂(n+1)⌉ + 2` of them, and
`QueryTree.hasDual_shared_depth` charges only the path, not the `Θ(n)` positions
the search could have looked at. -/

section Cost

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- The `K`-membership query is membership of a window's product in
`rightAbove r`, so it is priced by a square-root search over that set — and
never by an equality test at a value outside it. -/
private lemma hasDual_memQuery (letter : σ → M) (r : M) {n : ℕ} (j : ℕ) {Q : ℝ}
    (hQ : 0 ≤ Q)
    (hrec : ∀ s ∈ rightAbove r, ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => !(inK letter r x j))
      (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1))) := by
  classical
  have hmono : Q * (24 * Real.sqrt (((rightAbove r).card : ℝ) + 1))
      ≤ Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) := by
    have hc : ((rightAbove r).card : ℝ) ≤ (Fintype.card M : ℝ) := by
      exact_mod_cast Finset.card_le_univ (rightAbove r)
    have := Real.sqrt_le_sqrt (show ((rightAbove r).card : ℝ) + 1
      ≤ (Fintype.card M : ℝ) + 1 by linarith)
    nlinarith [Real.sqrt_nonneg (((rightAbove r).card : ℝ) + 1)]
  have h0 : (0 : ℝ) ≤ Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) := by
    have := Real.sqrt_nonneg ((Fintype.card M : ℝ) + 1)
    positivity
  by_cases hjn : j ≤ n
  · have hmem := hasDual_winMem letter (rightAbove r) hjn (Nat.zero_le j) hQ
      fun s hs => hrec s hs j hjn
    have hneg : HasDual (fun x : Fin n → σ =>
        !(decide (winProd letter x 0 j ∈ rightAbove r)))
        (Q * (24 * Real.sqrt (((rightAbove r).card : ℝ) + 1))) :=
      hmem.ofKer fun u v => by simp
    exact (hneg.mono hmono).ofEq fun x => by simp [inK, hjn, mem_rightAbove]
  · refine ((hasDual_const (f := fun _ : Fin n → σ => (true : Bool))
      (fun _ _ => rfl)).mono h0).ofEq fun x => ?_
    rw [inK_of_gt letter r x (by omega)]
    rfl

private lemma hasDual_prodQuery (letter : σ → M) (r : M) {n : ℕ} (j : ℕ) {Q : ℝ}
    (hQ : 0 ≤ Q)
    (hrec : ∀ s ∈ rightAbove r, ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => decide (j ≤ n ∧ winProd letter x 0 j = r)) Q := by
  by_cases hjn : j ≤ n
  · refine (hasDual_winEq' letter r hjn (Nat.zero_le j)
      (hrec r (self_mem_rightAbove r) j hjn)).ofEq fun x => ?_
    simp [hjn]
  · refine ((hasDual_const (f := fun _ : Fin n → σ => (false : Bool))
      (fun _ _ => rfl)).mono hQ).ofEq fun x => ?_
    simp [hjn]

/-- One price for every query the prefix search can make. -/
theorem hasDual_prefixQuery (letter : σ → M) (r a : M) {n : ℕ} {Q : ℝ}
    (hQ : 0 ≤ Q)
    (hrec : ∀ s ∈ rightAbove r, ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q)
    (p : Fin 3 × Fin (n + 2)) :
    HasDual (fun x : Fin n → σ => prefixQuery letter r a p x)
      (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2) := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((Fintype.card M : ℝ) + 1) := by
    have hc : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((Fintype.card M : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at h1
  have hbig : (0 : ℝ) ≤ Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) := by
    nlinarith
  have hQle : Q ≤ Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) := by nlinarith
  by_cases hp0 : p.1 = 0
  · refine ((hasDual_memQuery letter r ((p.2 : Fin (n + 2)) : ℕ) hQ hrec).mono
      (by linarith)).ofEq fun x => ?_
    rw [prefixQuery, if_pos hp0]
  · by_cases hp1 : p.1 = 1
    · refine ((hasDual_prodQuery letter r ((p.2 : Fin (n + 2)) : ℕ) hQ hrec).mono
        (by linarith)).ofEq fun x => ?_
      rw [prefixQuery, if_neg hp0, if_pos hp1]
    · refine ((hasDual_letterTest letter a ((p.2 : Fin (n + 2)) : ℕ)).mono
        (by linarith)).ofEq fun x => ?_
      rw [prefixQuery, if_neg hp0, if_neg hp1]

/-- **Prefix search (`lem:prefix`).**  Locating the boundary of `(U)` for one pair
`(r,a) ∈ E m` costs `O(√|M| · log n)` recursive equality tests, and — this is
what makes the AGS induction (`thm:main-ags`) legitimate — it only ever tests at values
in `rightAbove r`, every one of which sits at or above `r` in the `J`-order. -/
theorem hasDual_prefixEvent (letter : σ → M) {r a : M}
    (hra : rightIdeal (r * a) ⊂ rightIdeal r) {n : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s ∈ rightAbove r, ∀ len ≤ n,
      HasDual (eqProd (n := len) letter s) Q) :
    HasDual (fun x : Fin n → σ => prefixEvent letter r a x)
      (2 * ((Nat.clog 2 (n + 1) : ℝ) + 2)
        * (Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2)) := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((Fintype.card M : ℝ) + 1) := by
    have hc : (0 : ℝ) ≤ (Fintype.card M : ℝ) := Nat.cast_nonneg _
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((Fintype.card M : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at h1
  have hc₀ : (0 : ℝ)
      ≤ Q * (24 * Real.sqrt ((Fintype.card M : ℝ) + 1)) + 2 := by nlinarith
  have hbase := QueryTree.hasDual_shared_depth (ι := Fin n) (σ := σ) (prefixTree n)
    hc₀ (hasDual_prefixQuery letter r a hQ hrec)
  refine (hbase.ofEq fun x => prefixTree_eval letter hra x).mono ?_
  refine mul_le_mul_of_nonneg_right ?_ hc₀
  have hd : ((prefixTree n).depth : ℝ) ≤ (Nat.clog 2 (n + 1) : ℝ) + 2 := by
    exact_mod_cast depth_prefixTree n
  linarith

end Cost

end MonoidProduct
