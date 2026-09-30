import MonoidProduct.UT.Upper
import MonoidProduct.UT.Lower
import MonoidProduct.Width.Breadth
import MonoidProduct.Quantum.Applications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The product breadth of `UT_k(𝔹)` is `C(k, 2)`

`monoid.tex` Theorem `thm:boolean-unitriangular`, breadth clause:
`β_{UT_k(𝔹)}(UT_k(𝔹)) = C(k, 2)`.

* **Upper bound** (`but_isBreadthBound`): retain the positions where the prefix
  product changes.  Off those positions the prefix product is stationary, so the
  retained subword has the same product (`isCore_of_prefix_stationary`, valid in
  any monoid), and by `changeCount_le_choose` (`UT/Upper.lean`: every change flips
  a distinct strict entry) there are at most `C(k, 2)` of them.  This holds for
  every alphabet `σ → UT_k(𝔹)`.
* **Lower bound** (`but_breadth_id`): one letter `F_{ij}` (identity plus the edge
  `(i, j)`) for each `i < j`, in order of nonincreasing row `i`.  No two edges
  compose in that order, so the product of any subword has exactly the strict
  entries of its letters (`mat_prod_butSetLetter`) and all `C(k, 2)` letters are
  needed.
* **The `Θ(min{n, k√n})` form** (`but_qQuery_theta`): the elementary conversion
  of `ut_qQuery_sandwich` (`Quantum/Applications.lean`),
  `min{n, k√n}/144 ≤ Q_{1/3}(Prod_{UT_k(𝔹),n}) ≤ 73728·min{n, k√n}` for `k ≥ 2`,
  `n ≥ 1`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open Finset

variable {k : ℕ}

/-! ## A stationary prefix product gives a core, in any monoid -/

/-- If the prefix product does not move at the positions off `u`, then `u` is a
core. -/
theorem isCore_of_prefix_stationary {σ M : Type} [Monoid M] (letter : σ → M) {n : ℕ}
    (x : Fin n → σ) (u : Finset (Fin n))
    (h : ∀ i : Fin n, i ∉ u →
      rangeProd (fun j => letter (x j)) 0 ((i : ℕ) + 1)
        = rangeProd (fun j => letter (x j)) 0 (i : ℕ)) :
    IsCore letter x u := by
  have key : ∀ t, t ≤ n →
      rangeProd (fun i => if i ∈ u then letter (x i) else 1) 0 t
        = rangeProd (fun j => letter (x j)) 0 t := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
        rw [rangeProd_succ_right _ (Nat.zero_le t), ih (by omega),
          padAt_of_lt _ (by omega : t < n)]
        by_cases hu : (⟨t, by omega⟩ : Fin n) ∈ u
        · rw [if_pos hu, rangeProd_succ_right _ (Nat.zero_le t), padAt_of_lt _ (by omega)]
        · rw [if_neg hu, mul_one]
          exact (h ⟨t, by omega⟩ hu).symm
  rw [IsCore, subwordProd, ← orderedProd_eq_prod_ofFn, orderedProd_eq_rangeProd, key n le_rfl,
    wordProd, orderedProd_eq_rangeProd]

/-! ## The upper bound `β ≤ C(k, 2)` -/

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- **`β(UT_k(𝔹)) ≤ C(k, 2)`**, for every alphabet: the positions where the prefix
product changes form a core, and there are at most `C(k, 2)` of them. -/
theorem but_isBreadthBound (letter : σ → BUT k) : IsBreadthBound letter (k.choose 2) := by
  intro n x
  refine ⟨univ.filter fun i => scanCol (1 : BUT k) (butStep letter) x i = true,
    changeCount_le_choose letter x, isCore_of_prefix_stationary letter x _ fun i hi => ?_⟩
  rw [mem_filter, not_and] at hi
  have hcol : ¬ scanCol (1 : BUT k) (butStep letter) x i = true := hi (mem_univ _)
  simp only [scanCol, ne_eq, decide_eq_true_eq, not_not] at hcol
  rw [← prefixProd_eq_rangeProd, ← prefixProd_eq_rangeProd]
  exact hcol

/-! ## Edge-set letters and orders in which no edges compose -/

/-- The identity plus the strict edges of `R`. -/
def butSetLetter (R : Finset (Fin k × Fin k)) : BUT k :=
  Subtype.mk (unionMat (R.filter fun e => e.1 < e.2))
    (isBUtri_unionMat fun _ he => (mem_filter.1 he).2)

lemma butSetLetter_empty : butSetLetter (∅ : Finset (Fin k × Fin k)) = 1 :=
  BUT.ext (by rw [BUT.mat_one, ← unionMat_empty]; rfl)

/-- **The product of edge-set letters in a non-composing order** has exactly the
strict edges of its letters. -/
theorem mat_prod_butSetLetter :
    ∀ (L : List (Finset (Fin k × Fin k))),
      L.Pairwise (fun R S => ∀ e ∈ R, ∀ e' ∈ S, e.2 ≠ e'.1) → ∀ s t : Fin k,
      ((L.map butSetLetter).prod.mat s t = true
        ↔ s = t ∨ ∃ R ∈ L, (s, t) ∈ R ∧ s < t)
  | [], _, s, t => by
      simp [BUT.mat_one, bone_apply]
  | R :: L, hL, s, t => by
      rw [List.pairwise_cons] at hL
      have ih := mat_prod_butSetLetter L hL.2
      rw [List.map_cons, List.prod_cons, BUT.mat_mul, bmul_apply]
      constructor
      · rintro ⟨v, hsv, hvt⟩
        change unionMat _ s v = true at hsv
        rw [unionMat_apply, mem_filter] at hsv
        rw [ih] at hvt
        rcases hsv with rfl | ⟨hsv, hlt⟩
        · rcases hvt with rfl | ⟨R', hR', hst, hlt⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨R', List.mem_cons_of_mem _ hR', hst, hlt⟩
        · rcases hvt with rfl | ⟨R', hR', hvt, -⟩
          · exact Or.inr ⟨R, List.mem_cons_self, hsv, hlt⟩
          · exact absurd rfl (hL.1 R' hR' _ hsv _ hvt)
      · rintro (rfl | ⟨R', hR', hst, hlt⟩)
        · exact ⟨s, (BUT.isBUtri_mat _).diag s, (BUT.isBUtri_mat _).diag s⟩
        · rcases List.mem_cons.1 hR' with rfl | hR'
          · refine ⟨t, ?_, (BUT.isBUtri_mat _).diag t⟩
            change unionMat _ s t = true
            rw [unionMat_apply, mem_filter]
            exact Or.inr ⟨hst, hlt⟩
          · refine ⟨s, (BUT.isBUtri_mat _).diag s, ?_⟩
            rw [ih]
            exact Or.inr ⟨R', hR', hst, hlt⟩

/-- A word of edge letters whose rows never increase: the subword on `u` has
exactly the strict edges at the positions of `u`. -/
theorem mat_subwordProd_edges {n : ℕ} (edge : Fin n → Fin k × Fin k)
    (hrow : ∀ i j : Fin n, i < j → (edge j).1 ≤ (edge i).1)
    (hlt : ∀ i, (edge i).1 < (edge i).2) (u : Finset (Fin n)) (s t : Fin k) :
    (subwordProd (fun i => butSetLetter {edge i}) id u).mat s t = true
      ↔ s = t ∨ ∃ i ∈ u, edge i = (s, t) := by
  let R : Fin n → Finset (Fin k × Fin k) := fun i => if i ∈ u then {edge i} else ∅
  have hfun : (fun i : Fin n => if i ∈ u then butSetLetter {edge (id i)} else 1)
      = fun i => butSetLetter (R i) := by
    funext i
    by_cases hi : i ∈ u
    · simp [R, hi]
    · simp [R, hi, butSetLetter_empty]
  have hpw : (List.ofFn R).Pairwise (fun R S => ∀ e ∈ R, ∀ e' ∈ S, e.2 ≠ e'.1) := by
    rw [List.pairwise_ofFn]
    intro i j hij e he e' he' heq
    simp only [R] at he he'
    split_ifs at he he' <;> simp only [mem_singleton, Finset.notMem_empty] at he he'
    subst he he'
    have h1 := hrow i j hij
    have h2 := hlt i
    rw [heq] at h2
    exact absurd h1 (not_le.2 h2)
  rw [subwordProd, hfun, show (List.ofFn fun i => butSetLetter (R i))
      = (List.ofFn R).map butSetLetter by rw [List.map_ofFn]; rfl,
    mat_prod_butSetLetter _ hpw]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨S, hS, hst, -⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hS
    simp only [R] at hst
    split_ifs at hst with hi
    · exact ⟨i, hi, (mem_singleton.1 hst).symm⟩
    · exact absurd hst (Finset.notMem_empty _)
  · rintro ⟨i, hi, he⟩
    refine ⟨R i, List.mem_ofFn.2 ⟨i, rfl⟩, ?_, ?_⟩
    · simp [R, hi, he]
    · have := hlt i
      rwa [he] at this

/-! ## The lower bound `β(UT_k(𝔹)) ≥ C(k, 2)` -/

/-- Sort key: row descending, then column ascending. -/
def butKey (p : Fin k × Fin k) : Lex ((Fin k)ᵒᵈ × Fin k) := toLex (OrderDual.toDual p.1, p.2)

lemma butKey_injective : Function.Injective (butKey (k := k)) := by
  intro p q h
  have h' := congrArg ofLex h
  simp only [butKey, ofLex_toLex, Prod.mk.injEq] at h'
  exact Prod.ext h'.1 h'.2

/-- The strict pairs, sorted by key. -/
def butKeys (k : ℕ) : Finset (Lex ((Fin k)ᵒᵈ × Fin k)) :=
  (univ.filter fun p : Fin k × Fin k => p.1 < p.2).map ⟨butKey, butKey_injective⟩

lemma card_butKeys (k : ℕ) : (butKeys k).card = k.choose 2 := by
  rw [butKeys, card_map, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- The `i`-th strict edge in order of nonincreasing row. -/
def butSortedEdge (k : ℕ) (i : Fin (k.choose 2)) : Fin k × Fin k :=
  (OrderDual.ofDual (ofLex ((butKeys k).orderEmbOfFin (card_butKeys k) i)).1,
    (ofLex ((butKeys k).orderEmbOfFin (card_butKeys k) i)).2)

lemma butSortedEdge_mem (i : Fin (k.choose 2)) :
    butKey (butSortedEdge k i) = (butKeys k).orderEmbOfFin (card_butKeys k) i ∧
      (butSortedEdge k i).1 < (butSortedEdge k i).2 := by
  have hmem := (butKeys k).orderEmbOfFin_mem (card_butKeys k) i
  obtain ⟨p, hp, hpk⟩ := Finset.mem_map.1 hmem
  have hp' : butSortedEdge k i = p := by
    simp only [butSortedEdge, ← hpk]
    rfl
  rw [hp']
  exact ⟨hpk, (mem_filter.1 hp).2⟩

lemma butSortedEdge_injective : Function.Injective (butSortedEdge k) := by
  intro i j h
  have := congrArg butKey h
  rw [(butSortedEdge_mem i).1, (butSortedEdge_mem j).1] at this
  exact ((butKeys k).orderEmbOfFin (card_butKeys k)).injective this

lemma butSortedEdge_row {i j : Fin (k.choose 2)} (hij : i < j) :
    (butSortedEdge k j).1 ≤ (butSortedEdge k i).1 := by
  have h := ((butKeys k).orderEmbOfFin (card_butKeys k)).strictMono hij
  rw [← (butSortedEdge_mem i).1, ← (butSortedEdge_mem j).1] at h
  rcases (Prod.Lex.toLex_lt_toLex).1 h with h1 | ⟨h1, -⟩
  · exact le_of_lt (OrderDual.toDual_lt_toDual.1 h1)
  · exact le_of_eq (OrderDual.toDual_inj.1 h1).symm

/-- **Every core of the sorted edge word is the whole word.** -/
theorem but_sorted_core_eq_univ (u : Finset (Fin (k.choose 2)))
    (hu : IsCore (fun i => butSetLetter {butSortedEdge k i}) id u) : u = univ := by
  refine eq_univ_of_forall fun i => ?_
  by_contra hi
  have hlt := (butSortedEdge_mem i).2
  have hfull : (subwordProd (fun i => butSetLetter {butSortedEdge k i}) id univ).mat
      (butSortedEdge k i).1 (butSortedEdge k i).2 = true :=
    (mat_subwordProd_edges _ (fun _ _ => butSortedEdge_row) (fun j => (butSortedEdge_mem j).2)
      _ _ _).2 (Or.inr ⟨i, mem_univ _, rfl⟩)
  rw [subwordProd_univ, ← hu,
    mat_subwordProd_edges _ (fun _ _ => butSortedEdge_row) (fun j => (butSortedEdge_mem j).2)]
    at hfull
  rcases hfull with h | ⟨j, hj, hji⟩
  · exact absurd h (ne_of_lt hlt)
  · rw [← butSortedEdge_injective (hji.trans (Prod.mk.eta))] at hi
    exact hi hj

/-- **`thm:boolean-unitriangular`, breadth clause**:
`β_{UT_k(𝔹)}(UT_k(𝔹)) = C(k, 2)`. -/
theorem but_breadth_id : breadth (id : BUT k → BUT k) = k.choose 2 := by
  refine le_antisymm (breadth_le (but_isBreadthBound id)) ?_
  have hex : ∃ b, IsBreadthBound (id : BUT k → BUT k) b := ⟨_, but_isBreadthBound id⟩
  refine le_breadth_of_forall_core hex (fun i => butSetLetter {butSortedEdge k i}) fun u hu => ?_
  have hu' : IsCore (fun i => butSetLetter {butSortedEdge k i}) id u := hu
  rw [but_sorted_core_eq_univ u hu', card_univ, Fintype.card_fin]

/-! ## `Θ(min{n, k√n})` with explicit constants -/

/-- `C(k, 2) ≤ k²`. -/
lemma but_choose_two_le_sq (k : ℕ) : k.choose 2 ≤ k ^ 2 := by
  rw [Nat.choose_two_right, sq]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- **`thm:boolean-unitriangular` in the paper's `Θ(min{n, k√n})` form**, with explicit
constants: for `k ≥ 2` and `n ≥ 1`,
`min{n, k√n}/144 ≤ Q_{1/3}(Prod_{UT_k(𝔹),n}) ≤ 73728·min{n, k√n}`. -/
theorem but_qQuery_theta {n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    (1 / 144 : ℝ) * min (n : ℝ) (k * Real.sqrt n)
        ≤ (qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
      ∧ (qQuery (fun w : Fin n → BUT k => wordProd id w) (1 / 3) : ℝ)
        ≤ 73728 * min (n : ℝ) (k * Real.sqrt n) := by
  obtain ⟨hlo, hup⟩ := ut_qQuery_sandwich hk hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsqn : (1 : ℝ) ≤ Real.sqrt n := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn1
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  set m := min (n : ℝ) (k * Real.sqrt n) with hm
  have hm0 : 0 ≤ m := le_min (by linarith) (by positivity)
  have hm1 : 1 ≤ m := le_min hn1 (by nlinarith)
  have hmn : m ≤ n := min_le_left _ _
  have hmk : m ≤ k * Real.sqrt n := min_le_right _ _
  have hm2n : m ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hm0 hmn 2
  have hm2k : m ^ 2 ≤ (k : ℝ) ^ 2 * n := by
    have := pow_le_pow_left₀ hm0 hmk 2
    rwa [mul_pow, hsq] at this
  constructor
  · -- lower bound
    refine le_trans ?_ hlo
    have hX : m / 4 ≤ Real.sqrt ((n * min n (k ^ 2 / 4) : ℕ) / 2 : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [Nat.cast_mul]
      rcases min_choice n (k ^ 2 / 4) with hd | hd
      · rw [hd]
        nlinarith
      · rw [hd]
        have hK : k ^ 2 ≤ 8 * (k ^ 2 / 4) := by
          have h4 : 4 ≤ k ^ 2 := by nlinarith
          omega
        have hK' : ((k : ℝ)) ^ 2 ≤ 8 * ((k ^ 2 / 4 : ℕ) : ℝ) := by exact_mod_cast hK
        nlinarith
    nlinarith
  · -- upper bound
    refine le_trans hup (le_trans (min_le_right _ _) ?_)
    have hc : Real.sqrt ((n : ℝ) * ((min n (k.choose 2) : ℕ) : ℝ)) ≤ m := by
      have hc1 : ((min n (k.choose 2) : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_left _ _
      have hc2 : ((min n (k.choose 2) : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
        exact_mod_cast (min_le_right _ _).trans (but_choose_two_le_sq k)
      refine le_min ?_ ?_
      · refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
        nlinarith
      · refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
        rw [mul_pow, hsq]
        nlinarith
    rw [show uniformExtractionConstant = 8192 from rfl]
    nlinarith

end MonoidProduct
