import MonoidProduct.Tropical.LinProd
import MonoidProduct.Capped.Embed
import QuantumQueryComplexity.Promise.Post
import QuantumQueryComplexity.Promise.Transport
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.openClassical false

/-!
# The disjoint-search lower bound for unitriangular tropical products

`Q(Prod_{U_k(T),n}) = Ω(√(n·min{k−1, n}))`, at the `ADV±` level and on a
finite promise: the dependence on `n` of the tropical product theorem
(`advPM_linProd_le`) is optimal up to the polylogarithmic factor, for every
fixed `k ≥ 2`.

The construction embeds `d = min{k−1, n}` disjoint promised **Or** instances
in the adjacent superdiagonal.  The positions are split into `d` balanced
blocks; in block `c` every letter is the tropical identity or the matrix
`J_c` enabling the single transition `c → c + 1`, with the promise that at
most one letter of each block is `J_c`.  A walk from state `c` to `c + 1`
takes exactly one transition, so the `(c, c+1)` entry of the product is `0`
exactly when block `c` is marked — and the parity of the marked blocks is a
Boolean postprocessing of the product.

The adversary certificate is the Kronecker sum of the `d` stars pairing the
all-identity block with its `|B_c|` singly-marked versions:

* the promise domain is the *product* `∀ c, Option B_c` (which block
  position is marked, if any), so the sum of stars has the product of their
  top eigenvectors as an **exact** eigenvector, with eigenvalue
  `θ = ∑_c √|B_c|`;
* every edge toggles one block and flips the parity, so the graph is a
  valid adversary matrix for the parity;
* a query mask `⊙ advDOn` leaves the graph of the toggle involution at that
  position — a partial matching, norm at most `1`
  (`l2_opNorm_le_one_of_equiv_support`).

`le_advPMOn` then gives `θ ≤ advPMOn` for the parity, and post-composition
monotonicity (`advPMOn_comp_le`) transfers the bound to the tropical product
itself.  With balanced blocks `θ ≥ √(nd/2)` (`tropical_lower_advPMOn`).

The superdiagonal entry of the product needs no path formula: for adjacent
states the interval `Ioo s t` is empty, so unitriangularity collapses the
tropical matrix product to the pointwise supremum of the letters
(`linProd_apply_adjacent`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open scoped Classical
open Matrix

variable {ι ρ : Type} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

/-! ## The promise domain -/

/-- The positions of block `c`. -/
abbrev dsFib (blk : ι → ρ) (c : ρ) : Type := {i : ι // blk i = c}

/-- A promise input: each block is unmarked, or carries exactly one marked
position. -/
abbrev DsMarks (blk : ι → ρ) : Type := ∀ c, Option (dsFib blk c)

variable (blk : ι → ρ)

/-- The letter read at position `i`: the name of its block if `i` is the
marked position, and the identity letter otherwise. -/
def dsRead (x : DsMarks blk) (i : ι) : Option ρ :=
  if x (blk i) = some ⟨i, rfl⟩ then some (blk i) else none

/-- Reading every position recovers the promise input. -/
lemma dsRead_injective : Function.Injective (dsRead blk) := by
  intro x y hxy
  have hpt : ∀ i : ι, x (blk i) = some ⟨i, rfl⟩ ↔ y (blk i) = some ⟨i, rfl⟩ := by
    intro i
    have h := congrFun hxy i
    rw [dsRead, dsRead] at h
    constructor
    · intro hx
      by_contra hy
      rw [if_pos hx, if_neg hy] at h
      exact Option.some_ne_none _ h
    · intro hy
      by_contra hx
      rw [if_neg hx, if_pos hy] at h
      exact Option.some_ne_none _ h.symm
  funext c
  cases hxc : x c with
  | some a =>
      obtain ⟨i, hi⟩ := a
      subst hi
      exact ((hpt i).1 hxc).symm
  | none =>
      cases hyc : y c with
      | none => rfl
      | some a =>
          obtain ⟨i, hi⟩ := a
          subst hi
          rw [(hpt i).2 hyc] at hxc
          exact absurd hxc (Option.some_ne_none _)

/-- The output: the parity of the number of marked blocks — the XOR of the
`d` promised **Or** instances. -/
def dsFun (x : DsMarks blk) : Bool :=
  decide ((Finset.univ.filter fun c => (x c).isSome).card % 2 = 1)

/-! ## The star edges -/

/-- One edge of the `c`-th star, oriented: `x` has block `c` unmarked, `y`
marks one of its positions, and every other block agrees. -/
def StarEdge (c : ρ) (x y : DsMarks blk) : Prop :=
  x c = none ∧ (y c).isSome ∧ ∀ c', c' ≠ c → x c' = y c'

lemma dsStarEdge_block_eq {c c' : ρ} {x y : DsMarks blk}
    (h : StarEdge blk c x y) (h' : StarEdge blk c' x y) : c = c' := by
  by_contra hne
  have hxy : x c = y c := h'.2.2 c hne
  have h21 := h.2.1
  rw [← hxy, h.1] at h21
  simp at h21

lemma dsStarEdge_asymm {c c' : ρ} {x y : DsMarks blk}
    (h : StarEdge blk c x y) (h' : StarEdge blk c' y x) : False := by
  by_cases hcc : c = c'
  · subst hcc
    have h21 := h.2.1
    rw [h'.1] at h21
    simp at h21
  · have hxy : y c = x c := h'.2.2 c hcc
    have h21 := h.2.1
    rw [hxy, h.1] at h21
    simp at h21

lemma dsEdge_block_unique {c c' : ρ} {x y : DsMarks blk}
    (h : StarEdge blk c x y ∨ StarEdge blk c y x)
    (h' : StarEdge blk c' x y ∨ StarEdge blk c' y x) : c = c' := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact dsStarEdge_block_eq blk h h'
  · exact (dsStarEdge_asymm blk h h').elim
  · exact (dsStarEdge_asymm blk h' h).elim
  · exact dsStarEdge_block_eq blk h h'

/-- The two characterizations of the incident edges: an unmarked block can
only gain a mark… -/
lemma starEdge_iff_of_none {c : ρ} {x y : DsMarks blk} (hx : x c = none) :
    (StarEdge blk c x y ∨ StarEdge blk c y x)
      ↔ ∃ a, y = Function.update x c (some a) := by
  constructor
  · rintro (⟨-, hy, hoff⟩ | ⟨-, hxs, -⟩)
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hy
      refine ⟨a, funext fun c' => ?_⟩
      by_cases hc : c' = c
      · subst hc
        rw [ha, Function.update_self]
      · rw [Function.update_of_ne hc, hoff c' hc]
    · rw [hx] at hxs
      simp at hxs
  · rintro ⟨a, rfl⟩
    refine Or.inl ⟨hx, ?_, fun c' hc => ?_⟩
    · rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hc]

/-- …and a marked block can only lose its mark. -/
lemma starEdge_iff_of_some {c : ρ} {x y : DsMarks blk} (hx : (x c).isSome) :
    (StarEdge blk c x y ∨ StarEdge blk c y x)
      ↔ y = Function.update x c none := by
  constructor
  · rintro (⟨hxc, -, -⟩ | ⟨hyc, -, hoff⟩)
    · rw [hxc] at hx
      simp at hx
    · refine funext fun c' => ?_
      by_cases hc : c' = c
      · subst hc
        rw [hyc, Function.update_self]
      · rw [Function.update_of_ne hc, hoff c' hc]
  · rintro rfl
    refine Or.inr ⟨Function.update_self c none x, hx, fun c' hc => ?_⟩
    rw [Function.update_of_ne hc]

/-! ## The adversary graph: the Kronecker sum of the stars -/

/-- The sum-of-stars graph on the promise: `x ∼ y` when they differ by
toggling one block. -/
noncomputable def dsΓ : Matrix (DsMarks blk) (DsMarks blk) ℝ :=
  Matrix.of fun x y =>
    if ∃ c, StarEdge blk c x y ∨ StarEdge blk c y x then 1 else 0

lemma dsΓ_apply (x y : DsMarks blk) :
    dsΓ blk x y
      = if ∃ c, StarEdge blk c x y ∨ StarEdge blk c y x then 1 else 0 := rfl

lemma dsΓ_symm (x y : DsMarks blk) : dsΓ blk x y = dsΓ blk y x := by
  rw [dsΓ_apply, dsΓ_apply]
  exact if_congr (exists_congr fun c => or_comm) rfl rfl

lemma dsΓ_isHermitian : (dsΓ blk).IsHermitian :=
  Matrix.IsHermitian.ext fun x y => by rw [star_trivial, dsΓ_symm blk y x]

/-- The blocks are disjoint: the graph entry is the sum of the per-block
edge indicators. -/
lemma dsΓ_apply_eq_sum (x y : DsMarks blk) :
    dsΓ blk x y
      = ∑ c, if StarEdge blk c x y ∨ StarEdge blk c y x then (1 : ℝ) else 0 := by
  rw [dsΓ_apply]
  by_cases hex : ∃ c, StarEdge blk c x y ∨ StarEdge blk c y x
  · obtain ⟨c₀, hc₀⟩ := hex
    rw [if_pos ⟨c₀, hc₀⟩, Finset.sum_eq_single c₀
      (fun c _ hne => if_neg fun hc => hne (dsEdge_block_unique blk hc hc₀))
      (fun h => absurd (Finset.mem_univ _) h), if_pos hc₀]
  · rw [if_neg hex]
    exact (Finset.sum_eq_zero fun c _ => if_neg fun hc => hex ⟨c, hc⟩).symm

/-! ## Adversary validity: every edge flips the parity -/

lemma card_marked_of_starEdge {c : ρ} {x y : DsMarks blk}
    (h : StarEdge blk c x y) :
    (Finset.univ.filter fun c' => (y c').isSome).card
      = (Finset.univ.filter fun c' => (x c').isSome).card + 1 := by
  have hset : (Finset.univ.filter fun c' => (y c').isSome)
      = insert c (Finset.univ.filter fun c' => (x c').isSome) := by
    ext c'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hc : c' = c
    · subst hc
      simp [h.2.1]
    · rw [← h.2.2 c' hc]
      simp [hc]
  rw [hset, Finset.card_insert_of_notMem (by simp [h.1])]

lemma dsFun_ne_of_starEdge {c : ρ} {x y : DsMarks blk}
    (h : StarEdge blk c x y) : dsFun blk x ≠ dsFun blk y := by
  rw [dsFun, dsFun, Ne, decide_eq_decide, card_marked_of_starEdge blk h]
  omega

lemma dsΓ_apply_eq_zero {x y : DsMarks blk}
    (hf : dsFun blk x = dsFun blk y) : dsΓ blk x y = 0 := by
  rw [dsΓ_apply, if_neg]
  rintro ⟨c, h | h⟩
  · exact dsFun_ne_of_starEdge blk h hf
  · exact dsFun_ne_of_starEdge blk h hf.symm

/-! ## The eigenvector: the product of the stars' top eigenvectors -/

/-- The per-block weight: `√|B_c|` on the unmarked state, `1` on the marked
ones. -/
noncomputable def dsWt (c : ρ) : Option (dsFib blk c) → ℝ
  | none => Real.sqrt (Fintype.card (dsFib blk c))
  | some _ => 1

/-- The product eigenvector. -/
noncomputable def dsVec (x : DsMarks blk) : ℝ := ∏ c, dsWt blk c (x c)

/-- The eigenvalue: `∑_c √|B_c|`. -/
noncomputable def dsTheta : ℝ := ∑ c, Real.sqrt (Fintype.card (dsFib blk c))

lemma dsVec_eq (x : DsMarks blk) (c : ρ) :
    dsVec blk x
      = dsWt blk c (x c) * ∏ c' ∈ Finset.univ.erase c, dsWt blk c' (x c') := by
  rw [dsVec]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ c)).symm

lemma dsVec_update (x : DsMarks blk) (c : ρ) (w : Option (dsFib blk c)) :
    dsVec blk (Function.update x c w)
      = dsWt blk c w * ∏ c' ∈ Finset.univ.erase c, dsWt blk c' (x c') := by
  rw [dsVec, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun c' hc' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hc')]

/-- **The row sum of one star against the eigenvector**: whether the block
is unmarked (`|B_c|` neighbors of relative weight `1/√|B_c|`) or marked (one
neighbor of relative weight `√|B_c|`), block `c` contributes exactly
`√|B_c| · v x`. -/
lemma dsΓ_row_sum (x : DsMarks blk) (c : ρ) :
    (∑ y, if StarEdge blk c x y ∨ StarEdge blk c y x
        then dsVec blk y else 0)
      = Real.sqrt (Fintype.card (dsFib blk c)) * dsVec blk x := by
  cases hx : x c with
  | none =>
      rw [Finset.sum_congr rfl fun y _ =>
        if_congr (starEdge_iff_of_none blk hx) rfl rfl, ← Finset.sum_filter]
      have himg : (Finset.univ.filter
            fun y => ∃ a, y = Function.update x c (some a))
          = Finset.univ.image
              fun a : dsFib blk c => Function.update x c (some a) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image]
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨a, rfl⟩
        · rintro ⟨a, rfl⟩
          exact ⟨a, rfl⟩
      have hinj : ∀ a ∈ Finset.univ, ∀ a' ∈ (Finset.univ : Finset (dsFib blk c)),
          Function.update x c (some a) = Function.update x c (some a') → a = a' := by
        intro a _ a' _ h
        have h' := congrFun h c
        rw [Function.update_self, Function.update_self] at h'
        exact Option.some_injective _ h'
      rw [himg, Finset.sum_image hinj,
        Finset.sum_congr rfl fun a _ => dsVec_update blk x c (some a),
        Finset.sum_congr rfl fun a _ => by
          rw [show dsWt blk c (some a) = 1 from rfl, one_mul],
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [dsVec_eq blk x c, hx,
        show dsWt blk c none = Real.sqrt (Fintype.card (dsFib blk c)) from rfl,
        ← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  | some a₀ =>
      have hs : (x c).isSome := by rw [hx]; rfl
      rw [Finset.sum_congr rfl fun y _ =>
        if_congr (starEdge_iff_of_some blk hs) rfl rfl,
        Finset.sum_ite_eq' Finset.univ (Function.update x c none)
          (dsVec blk), if_pos (Finset.mem_univ _)]
      rw [dsVec_update blk x c none, dsVec_eq blk x c, hx,
        show dsWt blk c (some a₀) = 1 from rfl, one_mul,
        show dsWt blk c none = Real.sqrt (Fintype.card (dsFib blk c)) from rfl]

/-- **The exact eigen equation** `Γ v = θ v`. -/
lemma dsΓ_mulVec_dsVec :
    dsΓ blk *ᵥ dsVec blk = dsTheta blk • dsVec blk := by
  funext x
  rw [Matrix.mulVec, dotProduct]
  have h1 : ∀ y, dsΓ blk x y * dsVec blk y
      = ∑ c, if StarEdge blk c x y ∨ StarEdge blk c y x
          then dsVec blk y else 0 := by
    intro y
    rw [dsΓ_apply_eq_sum blk x y, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_comm,
    Finset.sum_congr rfl fun c _ => dsΓ_row_sum blk x c, ← Finset.sum_mul]
  rw [Pi.smul_apply, smul_eq_mul, dsTheta]

lemma dsVec_ne_zero (hsurj : Function.Surjective blk) : dsVec blk ≠ 0 := by
  have hne : ∀ c, Nonempty (dsFib blk c) := fun c =>
    (hsurj c).elim fun i hi => ⟨⟨i, hi⟩⟩
  intro h0
  have hx := congrFun h0 fun c => some (Classical.arbitrary (dsFib blk c))
  rw [dsVec, Pi.zero_apply] at hx
  rw [Finset.prod_congr rfl fun c _ =>
      show dsWt blk c (some (Classical.arbitrary (dsFib blk c))) = 1 from rfl,
    Finset.prod_const_one] at hx
  norm_num at hx

lemma dsTheta_le_norm (hsurj : Function.Surjective blk) :
    dsTheta blk ≤ ‖dsΓ blk‖ :=
  (le_abs_self _).trans
    (abs_eigenvalue_le_norm (dsΓ_mulVec_dsVec blk) (dsVec_ne_zero blk hsurj))

/-! ## The query masks -/

/-- The toggle at position `i`: swap "block `blk i` unmarked" with "block
`blk i` marked at `i`". -/
def dsToggle (i : ι) (x : DsMarks blk) : DsMarks blk :=
  Function.update x (blk i)
    (Equiv.swap none (some ⟨i, rfl⟩) (x (blk i)))

lemma dsToggle_involutive (i : ι) : Function.Involutive (dsToggle blk i) := by
  intro x
  rw [dsToggle, dsToggle, Function.update_self, Function.update_idem,
    Equiv.swap_apply_self, Function.update_eq_self]

lemma dsRead_ne_imp {x y : DsMarks blk} {i : ι}
    (h : dsRead blk x i ≠ dsRead blk y i) : x (blk i) ≠ y (blk i) :=
  fun he => h (by rw [dsRead, dsRead, he])

/-- The support of a masked entry: the unique incident toggle. -/
lemma dsMask_support {i : ι} {x y : DsMarks blk}
    (hΓ : ∃ c, StarEdge blk c x y ∨ StarEdge blk c y x)
    (hmask : dsRead blk x i ≠ dsRead blk y i) : y = dsToggle blk i x := by
  obtain ⟨c, hc⟩ := hΓ
  have hbc : c = blk i := by
    by_contra hne
    refine dsRead_ne_imp blk hmask ?_
    rcases hc with h | h
    · exact h.2.2 (blk i) fun hh => hne hh.symm
    · exact (h.2.2 (blk i) fun hh => hne hh.symm).symm
  subst hbc
  rcases hc with h | h
  · have hymark : y (blk i) = some ⟨i, rfl⟩ := by
      by_contra hnm
      refine hmask ?_
      rw [dsRead, dsRead, if_neg (by rw [h.1]; simp), if_neg hnm]
    funext c'
    by_cases hcc : c' = blk i
    · subst hcc
      rw [hymark, dsToggle, Function.update_self, h.1, Equiv.swap_apply_left]
    · rw [dsToggle, Function.update_of_ne hcc, (h.2.2 c' hcc).symm]
  · have hxmark : x (blk i) = some ⟨i, rfl⟩ := by
      by_contra hnm
      refine hmask ?_
      rw [dsRead, dsRead, if_neg hnm, if_neg (by rw [h.1]; simp)]
    funext c'
    by_cases hcc : c' = blk i
    · subst hcc
      rw [h.1, dsToggle, Function.update_self, hxmark, Equiv.swap_apply_right]
    · rw [dsToggle, Function.update_of_ne hcc, h.2.2 c' hcc]

/-- **The mask bound**: every query filter leaves norm at most one. -/
lemma dsΓ_hadamard_le_one (i : ι) :
    ‖dsΓ blk ⊙ advDOn (dsRead blk) i‖ ≤ 1 := by
  refine l2_opNorm_le_one_of_equiv_support _
    ((dsToggle_involutive blk i).toPerm) ?_ ?_
  · intro x y hne
    rw [Matrix.hadamard_apply, advDOn_apply]
    by_cases hmask : dsRead blk x i = dsRead blk y i
    · rw [if_pos hmask, mul_zero]
    · rw [if_neg hmask]
      have hzero : dsΓ blk x y = 0 := by
        rw [dsΓ_apply, if_neg]
        intro hΓ
        exact hne (dsMask_support blk hΓ hmask)
      rw [hzero, zero_mul]
  · intro x y
    rw [Matrix.hadamard_apply, advDOn_apply]
    have h1 : |dsΓ blk x y| ≤ 1 := by
      rw [dsΓ_apply]
      split_ifs <;> norm_num
    split_ifs with hm
    · rw [mul_zero, abs_zero]
      norm_num
    · rw [mul_one]
      exact h1

/-! ## The abstract disjoint-search bound -/

/-- **The disjoint-search adversary bound**: on the promise "each block is
unmarked or singly marked", the parity of the marked blocks — the XOR of the
per-block **Or** instances — has `advPMOn ≥ ∑_c √|B_c|`. -/
theorem dsTheta_le_advPMOn_dsFun (hsurj : Function.Surjective blk) :
    dsTheta blk ≤ advPMOn (dsRead blk) (dsFun blk) := by
  have hdet := separates_of_injective (dsRead_injective blk) (dsFun blk)
  have h1 : IsAdvMatrixOn (dsFun blk) (dsΓ blk) :=
    ⟨dsΓ_isHermitian blk, fun x y hf => dsΓ_apply_eq_zero blk hf⟩
  exact (dsTheta_le_norm blk hsurj).trans
    (le_advPMOn hdet h1 (dsΓ_hadamard_le_one blk))

/-! ## The tropical letters -/

variable {k : ℕ}

/-- The block letter `J_j`: the tropical identity with the single extra
transition `j → j + 1` enabled at weight `0`. -/
noncomputable def jmat (k j : ℕ) : TMat k :=
  fun s t =>
    if (s : ℕ) = (t : ℕ) ∨ ((s : ℕ) = j ∧ (t : ℕ) = j + 1) then 0 else ⊥

lemma jmat_apply (k j : ℕ) (s t : Fin k) :
    jmat k j s t
      = if (s : ℕ) = (t : ℕ) ∨ ((s : ℕ) = j ∧ (t : ℕ) = j + 1) then 0 else ⊥ :=
  rfl

lemma isUtri_jmat (k j : ℕ) : IsUtri (jmat k j) where
  diag s := if_pos (Or.inl rfl)
  below s t h := by
    have hv : (t : ℕ) < (s : ℕ) := h
    exact if_neg (by rintro (h1 | ⟨h1, h2⟩) <;> omega)

lemma tone_apply (k : ℕ) (s t : Fin k) :
    tone k s t = if s = t then 0 else ⊥ := rfl

lemma optLetter_none {σ : Type} [Fintype σ] [DecidableEq σ]
    (letter : σ → TMat k) : optLetter letter none = tone k := rfl

lemma optLetter_some {σ : Type} [Fintype σ] [DecidableEq σ]
    (letter : σ → TMat k) (a : σ) : optLetter letter (some a) = letter a := rfl

/-! ## The adjacent superdiagonal of a product -/

lemma isUtri_linProd {σ : Type} [Fintype σ] [DecidableEq σ]
    {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a)) :
    ∀ (n : ℕ) (x : Fin n → σ), IsUtri (linProd letter n x)
  | 0, _ => isUtri_tone
  | n + 1, x => (isUtri_linProd hL n _).tmul (hL _)

/-- For **adjacent** states there is no strictly intermediate state, so
unitriangularity collapses the tropical matrix product to the supremum of
the factors' entries. -/
lemma tmul_apply_adjacent {M N : TMat k} (hM : IsUtri M) (hN : IsUtri N)
    {s t : Fin k} (hst : (t : ℕ) = (s : ℕ) + 1) :
    tmul M N s t = M s t ⊔ N s t := by
  refine le_antisymm (Finset.sup_le fun v _ => ?_) (sup_le ?_ ?_)
  · rcases lt_trichotomy v s with hv | hv | hv
    · rw [hM.below s v hv, WithBot.bot_add]
      exact bot_le
    · subst hv
      rw [hM.diag, zero_add]
      exact le_sup_right
    · have hsv : (s : ℕ) < (v : ℕ) := hv
      rcases eq_or_lt_of_le (show (t : ℕ) ≤ (v : ℕ) by omega) with hv' | hv'
      · have : v = t := Fin.ext hv'.symm
        subst this
        rw [hN.diag, add_zero]
        exact le_sup_left
      · rw [hN.below v t hv', WithBot.add_bot]
        exact bot_le
  · calc M s t = M s t + N t t := by rw [hN.diag, add_zero]
      _ ≤ _ := Finset.le_sup (f := fun v => M s v + N v t) (Finset.mem_univ t)
  · calc N s t = M s s + N s t := by rw [hM.diag, zero_add]
      _ ≤ _ := Finset.le_sup (f := fun v => M s v + N v t) (Finset.mem_univ s)

/-- **The adjacent superdiagonal of the product is the supremum of the
letters' entries**: a walk between adjacent states takes exactly one
transition. -/
lemma linProd_apply_adjacent {σ : Type} [Fintype σ] [DecidableEq σ]
    {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a)) {s t : Fin k}
    (hst : (t : ℕ) = (s : ℕ) + 1) :
    ∀ (n : ℕ) (x : Fin n → σ),
      linProd letter n x s t = Finset.univ.sup fun i => letter (x i) s t
  | 0, _ => by
      have hne : s ≠ t := fun h => by rw [h] at hst; omega
      rw [linProd_zero, tone_apply, if_neg hne, Finset.univ_eq_empty,
        Finset.sup_empty]
  | n + 1, x => by
      rw [show linProd letter (n + 1) x
          = tmul (linProd letter n fun i => x i.castSucc)
              (letter (x (Fin.last n))) from rfl,
        tmul_apply_adjacent (isUtri_linProd hL n _) (hL _) hst,
        linProd_apply_adjacent hL hst n fun i => x i.castSucc,
        Fin.univ_castSuccEmb, Finset.sup_cons, Finset.sup_map]
      exact sup_comm _ _

/-! ## The promise product -/

/-- The lower state of block `c`'s transition. -/
def slotS (emb : ρ → ℕ) (hemb : ∀ c, emb c + 1 < k) (c : ρ) : Fin k :=
  ⟨emb c, by have := hemb c; omega⟩

/-- The upper state of block `c`'s transition. -/
def slotT (emb : ρ → ℕ) (hemb : ∀ c, emb c + 1 < k) (c : ρ) : Fin k :=
  ⟨emb c + 1, hemb c⟩

lemma slotS_val (emb : ρ → ℕ) (hemb : ∀ c, emb c + 1 < k) (c : ρ) :
    ((slotS emb hemb c : Fin k) : ℕ) = emb c := rfl

lemma slotT_val (emb : ρ → ℕ) (hemb : ∀ c, emb c + 1 < k) (c : ρ) :
    ((slotT emb hemb c : Fin k) : ℕ) = emb c + 1 := rfl

/-- A letter's entry at block `c`'s slot: `0` exactly for the letter `J_c`
itself. -/
lemma optLetter_jmat_slot {emb : ρ → ℕ} (hinj : Function.Injective emb)
    (hemb : ∀ c, emb c + 1 < k) (c : ρ) (o : Option ρ) :
    optLetter (fun c' => jmat k (emb c')) o
        (slotS emb hemb c) (slotT emb hemb c)
      = if o = some c then (0 : Trop) else ⊥ := by
  cases o with
  | none =>
      have hne : slotS emb hemb c ≠ slotT emb hemb c := by
        intro h
        have := congrArg Fin.val h
        rw [slotS_val, slotT_val] at this
        omega
      rw [optLetter_none, tone_apply, if_neg hne,
        if_neg (fun h : (none : Option ρ) = some c => Option.some_ne_none _ h.symm)]
  | some c' =>
      rw [optLetter_some, jmat_apply, slotS_val, slotT_val]
      by_cases hc : c' = c
      · subst hc
        rw [if_pos (Or.inr ⟨rfl, rfl⟩), if_pos rfl]
      · rw [if_neg, if_neg (fun h => hc (Option.some_injective _ h))]
        rintro (h1 | ⟨h1, -⟩)
        · omega
        · exact hc (hinj h1).symm

variable {n : ℕ}

/-- **The slot entries of the promise product**: block `c`'s superdiagonal
entry of the product is `0` when the block is marked and `-∞` when it is
not. -/
lemma linProd_dsRead_slot {blk : Fin n → ρ} {emb : ρ → ℕ}
    (hinj : Function.Injective emb) (hemb : ∀ c, emb c + 1 < k)
    (x : DsMarks blk) (c : ρ) :
    linProd (optLetter fun c' => jmat k (emb c')) n (dsRead blk x)
        (slotS emb hemb c) (slotT emb hemb c)
      = if (x c).isSome then (0 : Trop) else ⊥ := by
  rw [linProd_apply_adjacent (isUtri_optLetter fun c' => isUtri_jmat k (emb c'))
      (by rw [slotT_val, slotS_val]) n (dsRead blk x),
    Finset.sup_congr rfl fun i _ => optLetter_jmat_slot hinj hemb c (dsRead blk x i)]
  by_cases hx : (x c).isSome
  · rw [if_pos hx]
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨i₀, hi₀⟩ := a
    subst hi₀
    have hread : dsRead blk x i₀ = some (blk i₀) := by
      rw [dsRead, if_pos ha]
    refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
    · split_ifs
      · exact le_refl _
      · exact bot_le
    · have h := Finset.le_sup
        (f := fun i => if dsRead blk x i = some (blk i₀) then (0 : Trop) else ⊥)
        (Finset.mem_univ i₀)
      rwa [if_pos hread] at h
  · rw [if_neg hx]
    have hall : ∀ i, dsRead blk x i ≠ some c := by
      intro i hread
      rw [dsRead] at hread
      by_cases hm : x (blk i) = some ⟨i, rfl⟩
      · rw [if_pos hm] at hread
        have hbc : blk i = c := Option.some_injective _ hread
        subst hbc
        rw [hm] at hx
        simp at hx
      · rw [if_neg hm] at hread
        exact Option.some_ne_none _ hread.symm
    refine le_bot_iff.mp (Finset.sup_le fun i _ => ?_)
    rw [if_neg (hall i)]

/-- The Boolean postprocessing: the parity of the number of `0` entries
among the designated superdiagonal slots. -/
noncomputable def slotParity (emb : ρ → ℕ) (hemb : ∀ c, emb c + 1 < k)
    (P : TMat k) : Bool :=
  decide ((Finset.univ.filter fun c : ρ =>
    P (slotS emb hemb c) (slotT emb hemb c) = 0).card % 2 = 1)

/-- The parity of the marked blocks is a Boolean postprocessing of the
promise product. -/
lemma slotParity_linProd_dsRead {blk : Fin n → ρ} {emb : ρ → ℕ}
    (hinj : Function.Injective emb) (hemb : ∀ c, emb c + 1 < k)
    (x : DsMarks blk) :
    slotParity emb hemb
        (linProd (optLetter fun c' => jmat k (emb c')) n (dsRead blk x))
      = dsFun blk x := by
  rw [slotParity, dsFun]
  have hset : (Finset.univ.filter fun c : ρ =>
        linProd (optLetter fun c' => jmat k (emb c')) n (dsRead blk x)
          (slotS emb hemb c) (slotT emb hemb c) = 0)
      = Finset.univ.filter fun c => (x c).isSome := by
    refine Finset.filter_congr fun c _ => ?_
    rw [linProd_dsRead_slot hinj hemb x c]
    by_cases hx : (x c).isSome
    · simp [hx]
    · simp [hx]
  rw [hset]

/-! ## The tropical lower bound -/

/-- **The abstract disjoint-search lower bound for the tropical product**:
on the promise "in block `c` every letter is the identity or `J_c`, at most
one letter marked per block", the promise product itself has
`advPMOn ≥ ∑_c √|B_c|` — the parity certificate transfers by postprocessing
monotonicity. -/
theorem dsTheta_le_advPMOn_linProd {blk : Fin n → ρ} {emb : ρ → ℕ}
    (hsurj : Function.Surjective blk) (hinj : Function.Injective emb)
    (hemb : ∀ c, emb c + 1 < k) :
    dsTheta blk ≤ advPMOn (dsRead blk)
      (fun x => linProd (optLetter fun c => jmat k (emb c)) n
        (dsRead blk x)) := by
  refine (dsTheta_le_advPMOn_dsFun blk hsurj).trans ?_
  have hdet : ∀ x y : DsMarks blk, dsRead blk x = dsRead blk y →
      linProd (optLetter fun c => jmat k (emb c)) n (dsRead blk x)
        = linProd (optLetter fun c => jmat k (emb c)) n (dsRead blk y) := by
    intro x y h
    rw [h]
  have hcomp := advPMOn_comp_le
    (f := fun x => linProd (optLetter fun c => jmat k (emb c)) n
      (dsRead blk x))
    hdet (slotParity emb hemb)
  rwa [show (fun x => slotParity emb hemb
        (linProd (optLetter fun c => jmat k (emb c)) n (dsRead blk x)))
      = dsFun blk from
    funext fun x => slotParity_linProd_dsRead hinj hemb x] at hcomp

/-! ## Balanced blocks -/

/-- The balanced block assignment: position `i` belongs to block `i % d`. -/
def modBlk (n d : ℕ) (hd : 0 < d) : Fin n → Fin d :=
  fun i => ⟨(i : ℕ) % d, Nat.mod_lt _ hd⟩

lemma modBlk_surjective {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    Function.Surjective (modBlk n d hd) := by
  intro c
  exact ⟨⟨(c : ℕ), lt_of_lt_of_le c.isLt hdn⟩,
    Fin.ext (Nat.mod_eq_of_lt c.isLt)⟩

/-- Every block holds at least `⌊n/d⌋` positions. -/
lemma div_le_card_dsFib {n d : ℕ} (hd : 0 < d) (c : Fin d) :
    n / d ≤ Fintype.card (dsFib (modBlk n d hd) c) := by
  have hlt : ∀ j : Fin (n / d), (j : ℕ) * d + (c : ℕ) < n := by
    intro j
    calc (j : ℕ) * d + (c : ℕ) < (j : ℕ) * d + d :=
        Nat.add_lt_add_left c.isLt _
      _ = ((j : ℕ) + 1) * d := by ring
      _ ≤ (n / d) * d := Nat.mul_le_mul_right d j.isLt
      _ ≤ n := Nat.div_mul_le_self n d
  have hmod : ∀ j : Fin (n / d),
      modBlk n d hd ⟨(j : ℕ) * d + (c : ℕ), hlt j⟩ = c := by
    intro j
    refine Fin.ext ?_
    change ((j : ℕ) * d + (c : ℕ)) % d = (c : ℕ)
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt c.isLt]
  have hinj : Function.Injective fun j : Fin (n / d) =>
      (⟨⟨(j : ℕ) * d + (c : ℕ), hlt j⟩, hmod j⟩ :
        dsFib (modBlk n d hd) c) := by
    intro j j' h
    have hv : (j : ℕ) * d + (c : ℕ) = (j' : ℕ) * d + (c : ℕ) :=
      congrArg Fin.val (congrArg Subtype.val h)
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd (by omega))
  calc n / d = Fintype.card (Fin (n / d)) := (Fintype.card_fin _).symm
    _ ≤ _ := Fintype.card_le_of_injective _ hinj

/-- With `d ≤ n` balanced blocks, `θ = ∑_c √|B_c| ≥ √(nd/2)`. -/
lemma sqrt_le_dsTheta {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ) ≤ dsTheta (modBlk n d hd) := by
  have h2 : (d : ℝ) * Real.sqrt ((n / d : ℕ) : ℝ) ≤ dsTheta (modBlk n d hd) := by
    rw [dsTheta]
    calc (d : ℝ) * Real.sqrt ((n / d : ℕ) : ℝ)
        = ∑ _c : Fin d, Real.sqrt ((n / d : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun c _ => Real.sqrt_le_sqrt
          (by exact_mod_cast div_le_card_dsFib hd c)
  refine le_trans ?_ h2
  have hmod := Nat.div_add_mod n d
  have hq1 : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) := by
    have := (Nat.one_le_div_iff hd).mpr hdn
    exact_mod_cast this
  have hrd : ((n % d : ℕ) : ℝ) + 1 ≤ (d : ℝ) := by
    have := Nat.mod_lt n hd
    exact_mod_cast this
  have hn : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) := by
    exact_mod_cast hmod.symm
  have hnum : ((n * d : ℕ) : ℝ) / 2 ≤ (d : ℝ) ^ 2 * ((n / d : ℕ) : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hr0 : (0 : ℝ) ≤ ((n % d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ ((n / d : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [hn, hq1, hrd, hd0, hr0, hq0, sq_nonneg ((d : ℝ))]
  calc Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ Real.sqrt ((d : ℝ) ^ 2 * ((n / d : ℕ) : ℝ)) := Real.sqrt_le_sqrt hnum
    _ = (d : ℝ) * Real.sqrt ((n / d : ℕ) : ℝ) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg d)]

/-- **The disjoint-search lower bound, parametric form**: for every
`0 < d ≤ n` with `d < k`, the product of `n` letters in `U_k(T)` — on the
promise "block `c` is the identity except for at most one letter `J_c`" —
has `advPMOn ≥ √(nd/2)`. -/
theorem sqrt_le_advPMOn_linProd {k n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hdk : d < k) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPMOn (dsRead (modBlk n d hd))
          (fun x => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
            (dsRead (modBlk n d hd) x)) :=
  (sqrt_le_dsTheta hd hdn).trans
    (dsTheta_le_advPMOn_linProd (modBlk_surjective hd hdn)
      Fin.val_injective (fun c => by have := c.isLt; omega))

/-- **The tropical disjoint-search lower bound at the `ADV±` level**:
for every `k ≥ 2` and `n ≥ 1`, with `d = min{k−1, n}` balanced blocks, the
tropical product of `n` letters in `U_k(T)` has, already on a finite
promise, `advPMOn ≥ √(n·d/2) = Ω(√(n·min{k−1, n}))` — matching
`advPM_linProd_le` in the dependence on `n` up to the polylogarithmic
factor.  The bound holds for a Boolean postprocessing of the adjacent
superdiagonal (`dsTheta_le_advPMOn_dsFun` + `slotParity_linProd_dsRead`),
which is what the operational quantum lower bound consumes. -/
theorem tropical_lower_advPMOn {k n d : ℕ} (hk : 2 ≤ k) (hn : 0 < n)
    (hd : d = min (k - 1) n) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPMOn (dsRead (modBlk n d (by omega)))
          (fun x => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
            (dsRead (modBlk n d (by omega)) x)) :=
  sqrt_le_advPMOn_linProd (by omega) (by omega) (by omega)

/-- The promise certificate transfers along the injective encoding
(`advPMOn_le_advPM_of_injective`): the **total** product function over the
letter alphabet `Option (Fin d)` — identity plus the `d` block letters — is
hard, in the form matched by `advPM_linProd_le`. -/
theorem sqrt_le_advPM_linProd {k n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hdk : d < k) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPM (fun w : Fin n → Option (Fin d) =>
          linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n w) :=
  (sqrt_le_advPMOn_linProd hd hdn hdk).trans
    (advPMOn_le_advPM_of_injective (dsRead_injective _) fun _ => rfl)

/-- **The tropical disjoint-search lower bound for the total product function**: with
`d = min{k−1, n}`, `ADV±(Prod_{U_k(T),n}) ≥ √(n·d/2)` over the alphabet of
the identity and the `d` block letters — so `advPM_linProd_le`'s `√n` is
tight up to the polylogarithmic factor for every fixed `k ≥ 2`. -/
theorem tropical_lower_advPM {k n d : ℕ} (hk : 2 ≤ k) (hn : 0 < n)
    (hd : d = min (k - 1) n) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPM (fun w : Fin n → Option (Fin d) =>
          linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n w) :=
  sqrt_le_advPM_linProd (by omega) (by omega) (by omega)

/-! ## Uniformity over finite allowed subalphabets

The hard instance uses `d + 1` specific letters.  Any *finite allowed
alphabet* that contains them — an injective `emb` whose letters are
interpreted as the hard instance's — inherits the bound verbatim, because
the adversary masks only ask whether two promise inputs are distinguished
(`advPMOn_comp_injective`).  This is the sense in which the tropical lower
bound is uniform in the alphabet; a *literally infinite* value oracle is
outside this model, whose answer registers are finite by construction. -/

lemma linProd_comp {σ σ' : Type} [Fintype σ] [DecidableEq σ] [Fintype σ']
    [DecidableEq σ'] (letter : σ' → TMat k) (emb : σ → σ') :
    ∀ (n : ℕ) (x : Fin n → σ),
      linProd letter n (fun i => emb (x i))
        = linProd (fun a => letter (emb a)) n x
  | 0, _ => rfl
  | n + 1, x => by
      show tmul (linProd letter n fun i => emb (x i.castSucc))
          (letter (emb (x (Fin.last n)))) = _
      rw [linProd_comp letter emb n fun i => x i.castSucc]
      rfl

/-- **The disjoint-search bound, uniformly over finite allowed
subalphabets**: any finite alphabet `σ'` whose letters include the `d + 1`
generators of the hard instance is at least as hard. -/
theorem sqrt_le_advPMOn_linProd_uniform {σ' : Type} [Fintype σ']
    [DecidableEq σ'] {k n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (hdk : d < k)
    (letter : σ' → TMat k) (emb : Option (Fin d) → σ')
    (hemb : Function.Injective emb)
    (hletter : ∀ a, letter (emb a)
      = optLetter (fun c : Fin d => jmat k (c : ℕ)) a) :
    Real.sqrt ((n * d : ℕ) / 2 : ℝ)
      ≤ advPMOn (fun x i => emb (dsRead (modBlk n d hd) x i))
          (fun x => linProd letter n
            fun i => emb (dsRead (modBlk n d hd) x i)) := by
  have hprod : (fun x => linProd letter n
        fun i => emb (dsRead (modBlk n d hd) x i))
      = fun x => linProd (optLetter fun c : Fin d => jmat k (c : ℕ)) n
          (dsRead (modBlk n d hd) x) := by
    funext x
    rw [linProd_comp letter emb n (dsRead (modBlk n d hd) x)]
    exact congrArg (fun L => linProd L n (dsRead (modBlk n d hd) x))
      (funext hletter)
  rw [hprod, advPMOn_comp_injective hemb]
  exact sqrt_le_advPMOn_linProd hd hdn hdk

/-! ## The vacuous dimension

`U_1(𝕋)` has a single element — the `1 × 1` matrix `(0)` — so the product
problem is constant and the lower bound is vacuously true there.  This is
the `k = 1` case the theorem statement excludes by `2 ≤ k`.  Stated at the
`ADV±` level only. -/

/-- **`U_1(𝕋)` is trivial**: every unitriangular `1 × 1` tropical matrix is
the identity, so the product of `n` letters is constant and its **adversary
bound is `0`**.  (This is an `ADV±` statement; the corresponding
`qQuery = 0` would come from `qQueryOn_const_eq_zero`.) -/
theorem advPM_linProd_eq_zero_of_dim_one {σ : Type} [Fintype σ]
    [DecidableEq σ] {letter : σ → TMat 1} (hL : ∀ a, IsUtri (letter a))
    (n : ℕ) : advPM (fun x : Fin n → σ => linProd letter n x) = 0 := by
  refine advPM_eq_zero_of_forall_eq fun x y => ?_
  have hconst : ∀ z : Fin n → σ, linProd letter n z = tone 1 := by
    intro z
    funext s t
    have hst : s = t := Subsingleton.elim s t
    subst hst
    rw [(isUtri_linProd hL n z).diag s, tone, if_pos rfl]
  rw [hconst x, hconst y]

end MonoidProduct
