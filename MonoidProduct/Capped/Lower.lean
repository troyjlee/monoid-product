import QuantumQueryComplexity.Basic
import MonoidProduct.Capped.Defs
import MonoidProduct.Capped.Embed
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Capped-counter products: the adversary lower bound (`thm:capped-counter-product`)

The lower half of `thm:capped-counter-product`, in parametric form: for any block assignment
`blk : ι → ρ` and any layer choice `s : ρ → ℕ` with
`1 ≤ s c ≤ min k (blkSize c)`,

  `∑_c √(s c · (blkSize c − s c + 1)) ≤ ADV±(Prod_{M_{k,r},n})`.

Everything happens on the Boolean cube `z : ι → Bool`, embedded into the
input space by `z ↦ (i ↦ if z i then e (blk i) else s0)` where the letters
`s0, e j` map to `1` and the `j`-th coordinate unit.  The adversary matrix
connects, per block `c`, the Hamming layers `s c − 1` and `s c` of that
block by inclusion (`Inc`), holding all other blocks fixed:

* the product vector `cubeVec z = ∏_c a_c(blkWt c z)` with
  `a_c = √(blkSize−s+1)` on the low layer and `√s` on the high layer is an
  exact eigenvector with eigenvalue `θ = ∑_c √(s(blkSize−s+1))` — the
  Kronecker-sum eigenvalues add, so no per-block norm computation is
  needed;
* a query mask `⊙ advD i` leaves a partial matching supported on the graph
  of the flip-at-`i` involution, so its norm is at most `1`;
* the certificate transfers to the ambient input space by
  `MonoidProduct.embMat` and finishes with `norm_div_le_advPM`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-! ## The cube and its embedding -/

/-- The coordinate unit of the capped power: `gen` in coordinate `j`. -/
def cappedUnit (k : ℕ) (j : ρ) : ρ → Capped k :=
  fun c => if c = j then Capped.gen else 1

/-- The sub-cube embedding: `z` chooses at each position between the
identity letter `s0` and the unit letter of the position's block. -/
def cubeEmb (blk : ι → ρ) (s0 : σ) (e : ρ → σ) : (ι → Bool) → ι → σ :=
  fun z i => if z i then e (blk i) else s0

/-- The explicit retraction of `cubeEmb` (no choice needed). -/
def cubeRetr (blk : ι → ρ) (e : ρ → σ) : (ι → σ) → ι → Bool :=
  fun x i => decide (x i = e (blk i))

/-- The size of block `c`. -/
def blkSize (blk : ι → ρ) (c : ρ) : ℕ :=
  (Finset.univ.filter fun i => blk i = c).card

/-- The Hamming weight of `z` inside block `c`. -/
def blkWt (blk : ι → ρ) (c : ρ) (z : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => blk i = c ∧ z i = true).card

/-- The inclusion relation of block `c` at layers `s c − 1 → s c`: equal
outside the block, one element added inside it. -/
def Inc (blk : ι → ρ) (s : ρ → ℕ) (c : ρ) (z w : ι → Bool) : Prop :=
  (∀ i, blk i ≠ c → z i = w i) ∧ (∀ i, z i = true → w i = true)
    ∧ blkWt blk c z = s c - 1 ∧ blkWt blk c w = s c

/-- The adversary matrix on the cube: per block, the symmetrized inclusion
between the two chosen layers. -/
noncomputable def cubeMat (blk : ι → ρ) (s : ρ → ℕ) :
    Matrix (ι → Bool) (ι → Bool) ℝ :=
  Matrix.of fun z w => ∑ c : ρ,
    ((if Inc blk s c z w then (1 : ℝ) else 0)
      + (if Inc blk s c w z then 1 else 0))

/-- The per-block eigenvector weight. -/
noncomputable def layerWeight (blk : ι → ρ) (s : ρ → ℕ) (c : ρ)
    (z : ι → Bool) : ℝ :=
  if blkWt blk c z = s c - 1 then Real.sqrt ((blkSize blk c - s c + 1 : ℕ) : ℝ)
  else if blkWt blk c z = s c then Real.sqrt (s c) else 0

/-- The product eigenvector. -/
noncomputable def cubeVec (blk : ι → ρ) (s : ρ → ℕ) : (ι → Bool) → ℝ :=
  fun z => ∏ c : ρ, layerWeight blk s c z

/-- The eigenvalue: the sum of the biregular block norms. -/
noncomputable def cubeTheta (blk : ι → ρ) (s : ρ → ℕ) : ℝ :=
  ∑ c : ρ, Real.sqrt ((s c : ℝ) * ((blkSize blk c - s c + 1 : ℕ) : ℝ))

/-- The flip-at-`i` involution of the cube. -/
def flipEquiv (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun z := Function.update z i (!z i)
  invFun z := Function.update z i (!z i)
  left_inv z := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp [Function.update_apply]
    · simp [Function.update_apply, hj]
  right_inv z := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp [Function.update_apply]
    · simp [Function.update_apply, hj]

section Cube

variable {blk : ι → ρ} {s : ρ → ℕ} {s0 : σ} {e : ρ → σ}

lemma cubeRetr_cubeEmb (hs0e : ∀ j, s0 ≠ e j) (z : ι → Bool) :
    cubeRetr blk e (cubeEmb blk s0 e z) = z := by
  funext i
  rw [cubeRetr, cubeEmb]
  cases hz : z i
  · simp [hs0e (blk i)]
  · simp

/-! ## Weight bookkeeping -/

lemma wt_update_of_blk_ne {i : ι} {c : ρ} (h : blk i ≠ c) (z : ι → Bool)
    (b : Bool) : blkWt blk c (Function.update z i b) = blkWt blk c z := by
  rw [blkWt, blkWt]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases eq_or_ne j i with rfl | hj
  · constructor
    · rintro ⟨hc, -⟩; exact absurd hc h
    · rintro ⟨hc, -⟩; exact absurd hc h
  · rw [Function.update_apply, if_neg hj]

lemma wt_update_true {i : ι} {c : ρ} (h : blk i = c) {z : ι → Bool}
    (hz : z i = false) :
    blkWt blk c (Function.update z i true) = blkWt blk c z + 1 := by
  have hins : (Finset.univ.filter fun j =>
        blk j = c ∧ Function.update z i true j = true)
      = insert i (Finset.univ.filter fun j => blk j = c ∧ z j = true) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    rcases eq_or_ne j i with rfl | hj
    · simp [Function.update_apply, h]
    · rw [Function.update_apply, if_neg hj]
      constructor
      · intro hh; exact Or.inr hh
      · rintro (rfl | hh)
        · exact absurd rfl hj
        · exact hh
  rw [blkWt, blkWt, hins, Finset.card_insert_of_notMem]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
  intro
  rw [hz]
  exact fun hh => Bool.false_ne_true hh

lemma wt_update_false {i : ι} {c : ρ} (h : blk i = c) {z : ι → Bool}
    (hz : z i = true) :
    blkWt blk c z = blkWt blk c (Function.update z i false) + 1 := by
  have h1 : Function.update (Function.update z i false) i true = z := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_apply, if_pos rfl, hz]
    · rw [Function.update_apply, if_neg hj, Function.update_apply,
        if_neg hj]
  have h2 : Function.update z i false i = false := by
    rw [Function.update_apply, if_pos rfl]
  calc blkWt blk c z
      = blkWt blk c (Function.update (Function.update z i false) i true) := by
        rw [h1]
    _ = blkWt blk c (Function.update z i false) + 1 := wt_update_true h h2

/-- Block weights add up to the block size. -/
lemma wt_add_card_le (c : ρ) (z : ι → Bool) :
    blkWt blk c z + (Finset.univ.filter fun i =>
      blk i = c ∧ z i = false).card = blkSize blk c := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i => blk i = c)
    (p := fun i => z i = true)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have hset : (Finset.univ.filter fun i => blk i = c ∧ z i = false)
      = Finset.univ.filter fun i => blk i = c ∧ ¬ (z i = true) := by
    ext j
    simp [Bool.not_eq_true]
  rw [blkWt, blkSize, hset, ← h]

/-! ## The structure of `Inc` -/

lemma inc_update {i : ι} {c : ρ} (hi : blk i = c) {z : ι → Bool}
    (hzi : z i = false) (hz : blkWt blk c z = s c - 1) (hs1 : 1 ≤ s c) :
    Inc blk s c z (Function.update z i true) := by
  refine ⟨?_, ?_, hz, ?_⟩
  · intro j hj
    rw [Function.update_apply, if_neg]
    rintro rfl
    exact hj hi
  · intro j hj
    rw [Function.update_apply]
    split_ifs with hij
    · rfl
    · exact hj
  · rw [wt_update_true hi hzi, hz]
    omega

/-- **Exactly one flip**: an `Inc`-pair is an update at a unique position of
its block. -/
lemma eq_update_of_inc {c : ρ} {z w : ι → Bool}
    (h : Inc blk s c z w) (hs1 : 1 ≤ s c) :
    ∃ i, blk i = c ∧ z i = false ∧ w = Function.update z i true := by
  classical
  obtain ⟨hout, hle, hz, hw⟩ := h
  set D : Finset ι := Finset.univ.filter fun j => ¬ z j = w j with hD
  have hDblk : ∀ j ∈ D, blk j = c := by
    intro j hj
    rw [hD, Finset.mem_filter] at hj
    by_contra hc
    exact hj.2 (hout j hc)
  have hDzw : ∀ j ∈ D, z j = false ∧ w j = true := by
    intro j hj
    rw [hD, Finset.mem_filter] at hj
    cases hzj : z j
    · cases hwj : w j
      · exact absurd (hzj.trans hwj.symm) hj.2
      · exact ⟨rfl, rfl⟩
    · exact absurd (hzj.trans (hle j hzj).symm) hj.2
  have hunion : (Finset.univ.filter fun j => blk j = c ∧ w j = true)
      = (Finset.univ.filter fun j => blk j = c ∧ z j = true) ∪ D := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, hD]
    constructor
    · rintro ⟨hc, hwj⟩
      by_cases hzj : z j = w j
      · exact Or.inl ⟨hc, hzj.trans hwj⟩
      · exact Or.inr hzj
    · rintro (⟨hc, hzj⟩ | hj)
      · exact ⟨hc, hle j hzj⟩
      · have hjD : j ∈ D := by
          rw [hD, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hj⟩
        exact ⟨hDblk j hjD, (hDzw j hjD).2⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun j => blk j = c ∧ z j = true) D := by
    rw [Finset.disjoint_left]
    intro j hj hjD
    rw [Finset.mem_filter] at hj
    have := (hDzw j hjD).1
    rw [hj.2.2] at this
    exact Bool.noConfusion this
  have hcard : s c = (s c - 1) + D.card := by
    have h1 : blkWt blk c w = blkWt blk c z + D.card := by
      rw [blkWt, blkWt, hunion, Finset.card_union_of_disjoint hdisj]
    rw [hw, hz] at h1
    exact h1
  have hD1 : D.card = 1 := by omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hD1
  have hiD : i ∈ D := by rw [hi]; exact Finset.mem_singleton_self i
  refine ⟨i, hDblk i hiD, (hDzw i hiD).1, ?_⟩
  funext j
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_apply, if_pos rfl, (hDzw j hiD).2]
  · rw [Function.update_apply, if_neg hj]
    by_contra hne
    have : j ∈ D := by
      rw [hD, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun hh => hne hh.symm⟩
    rw [hi, Finset.mem_singleton] at this
    exact hj this

/-- `Inc` cannot hold in both orientations. -/
lemma not_inc_symm {c c' : ρ} {z w : ι → Bool}
    (h : Inc blk s c z w) (h' : Inc blk s c' w z) (hs1 : 1 ≤ s c) : False := by
  have hzw : z = w := by
    funext j
    cases hzj : z j
    · cases hwj : w j
      · rfl
      · have := h'.2.1 j hwj
        rw [hzj] at this
        exact absurd this Bool.false_ne_true
    · rw [h.2.1 j hzj]
  rw [hzw] at h
  have h1 := h.2.2.1
  have h2 := h.2.2.2
  omega

/-- Two `Inc`-witnessing blocks for the same ordered pair agree. -/
lemma inc_block_eq {c c' : ρ} {z w : ι → Bool}
    (h : Inc blk s c z w) (h' : Inc blk s c' z w)
    (hs1 : 1 ≤ s c) (hs1' : 1 ≤ s c') : c = c' := by
  obtain ⟨i, hic, hzi, rfl⟩ := eq_update_of_inc h hs1
  obtain ⟨i', hic', hzi', hupd⟩ := eq_update_of_inc h' hs1'
  have : i' = i := by
    by_contra hne
    have h1 := congrFun hupd i'
    rw [Function.update_apply, if_neg hne, Function.update_apply,
      if_pos rfl] at h1
    rw [hzi'] at h1
    exact Bool.false_ne_true h1
  rw [← hic, ← hic', this]

end Cube

/-! ## The certificate -/

section Certificate

variable {k : ℕ} {blk : ι → ρ} {s : ρ → ℕ}
variable {m : σ → ρ → Capped k} {s0 : σ} {e : ρ → σ}

/-- The value of the product on an embedded cube point: coordinate `c` reads
the capped block weight. -/
lemma val_prod_cubeEmb (hk : 0 < k) (hm0 : m s0 = 1)
    (hme : ∀ j, m (e j) = cappedUnit k j) (z : ι → Bool) (c : ρ) :
    ((∏ i, m (cubeEmb blk s0 e z i)) c).val = min (blkWt blk c z) k := by
  classical
  have happly : (∏ i, m (cubeEmb blk s0 e z i)) c
      = ∏ i, m (cubeEmb blk s0 e z i) c :=
    map_prod (Pi.evalMonoidHom (fun _ : ρ => Capped k) c) _ Finset.univ
  rw [happly, Capped.val_prod]
  congr 1
  have hterm : ∀ i, (m (cubeEmb blk s0 e z i) c).val
      = if blk i = c ∧ z i = true then 1 else 0 := by
    intro i
    show (m (if z i then e (blk i) else s0) c).val
      = if blk i = c ∧ z i = true then 1 else 0
    cases hz : z i
    · rw [if_neg Bool.false_ne_true, hm0,
        if_neg (fun hh => Bool.false_ne_true hh.2)]
      rfl
    · rw [if_pos rfl, hme (blk i)]
      show (if c = blk i then Capped.gen else (1 : Capped k)).val
        = if blk i = c ∧ true = true then 1 else 0
      by_cases hbc : blk i = c
      · rw [if_pos hbc.symm, if_pos ⟨hbc, rfl⟩]
        show min 1 k = 1
        omega
      · rw [if_neg (fun hh => hbc hh.symm), if_neg (fun hh => hbc hh.1)]
        rfl

  calc ∑ i, (m (cubeEmb blk s0 e z i) c).val
      = ∑ i, if blk i = c ∧ z i = true then 1 else 0 :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = blkWt blk c z := by
        rw [blkWt, Finset.card_filter]

/-- `Inc`-pairs have different products. -/
lemma prod_ne_of_inc (hk : 0 < k) (hm0 : m s0 = 1)
    (hme : ∀ j, m (e j) = cappedUnit k j)
    {c : ρ} {z w : ι → Bool} (h : Inc blk s c z w)
    (hs1 : 1 ≤ s c) (hsk : s c ≤ k) :
    (∏ i, m (cubeEmb blk s0 e z i)) ≠ ∏ i, m (cubeEmb blk s0 e w i) := by
  intro heq
  have h1 := congrArg (fun g => (g c).val) heq
  rw [val_prod_cubeEmb hk hm0 hme z c, val_prod_cubeEmb hk hm0 hme w c,
    h.2.2.1, h.2.2.2] at h1
  omega

/-- The cube matrix is a valid adversary matrix for the product, transported
along the embedding. -/
lemma isAdvMatrix_embMat_cubeMat (hk : 0 < k) (hm0 : m s0 = 1)
    (hme : ∀ j, m (e j) = cappedUnit k j) (hs0e : ∀ j, s0 ≠ e j)
    (hs1 : ∀ c, 1 ≤ s c) (hsk : ∀ c, s c ≤ k) :
    IsAdvMatrix (fun x : ι → σ => ∏ i, m (x i))
      (embMat (cubeEmb blk s0 e) (cubeRetr blk e) (cubeMat blk s)) := by
  classical
  constructor
  · refine embMat_isHermitian ?_
    refine Matrix.IsHermitian.ext fun z w => ?_
    simp only [Matrix.conjTranspose_apply, star_trivial, cubeMat,
      Matrix.of_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · intro x y hf
    rw [embMat_apply]
    rcases eq_or_ne (cubeMat blk s (cubeRetr blk e x) (cubeRetr blk e y)) 0
      with h0 | h0
    · rw [h0, mul_zero]
    · by_cases hx : cubeEmb blk s0 e (cubeRetr blk e x) = x
      · by_cases hy : cubeEmb blk s0 e (cubeRetr blk e y) = y
        · exfalso
          set z := cubeRetr blk e x
          set w := cubeRetr blk e y
          have hsum : ∑ c : ρ,
              ((if Inc blk s c z w then (1 : ℝ) else 0)
                + (if Inc blk s c w z then 1 else 0)) ≠ 0 := h0
          have hex : ∃ c, Inc blk s c z w ∨ Inc blk s c w z := by
            by_contra hall
            push_neg at hall
            refine hsum (Finset.sum_eq_zero fun c _ => ?_)
            rw [if_neg (hall c).1, if_neg (hall c).2]
            norm_num
          obtain ⟨c, hc⟩ := hex
          have hne : (∏ i, m (cubeEmb blk s0 e z i))
              ≠ ∏ i, m (cubeEmb blk s0 e w i) := by
            rcases hc with hc | hc
            · exact prod_ne_of_inc hk hm0 hme hc (hs1 c) (hsk c)
            · exact (prod_ne_of_inc hk hm0 hme hc (hs1 c) (hsk c)).symm
          refine hne ?_
          calc ∏ i, m (cubeEmb blk s0 e z i)
              = ∏ i, m (x i) := by rw [hx]
            _ = ∏ i, m (y i) := hf
            _ = ∏ i, m (cubeEmb blk s0 e w i) := by rw [hy]
        · have h0y : embInd (cubeEmb blk s0 e) (cubeRetr blk e) y = 0 := by
            rw [embInd, if_neg hy]
          rw [h0y, mul_zero, zero_mul]
      · have h0x : embInd (cubeEmb blk s0 e) (cubeRetr blk e) x = 0 := by
          rw [embInd, if_neg hx]
        rw [h0x, zero_mul, zero_mul]

end Certificate

/-! ## The eigenvector -/

section Eigen

variable {blk : ι → ρ} {s : ρ → ℕ}

lemma layerWeight_update {i : ι} {c' : ρ} (h : blk i ≠ c') (z : ι → Bool)
    (b : Bool) :
    layerWeight blk s c' (Function.update z i b) = layerWeight blk s c' z := by
  rw [layerWeight, layerWeight, wt_update_of_blk_ne h]

/-- **The per-block eigen identity**: summing the symmetrized inclusion of
block `c` against the product vector reproduces the biregular norm
`√(s(m−s+1))`. -/
lemma block_eigen (hs1 : ∀ c, 1 ≤ s c) (hsm : ∀ c, s c ≤ blkSize blk c)
    (c : ρ) (z : ι → Bool) :
    ∑ w, ((if Inc blk s c z w then (1 : ℝ) else 0)
        + (if Inc blk s c w z then 1 else 0)) * cubeVec blk s w
    = Real.sqrt ((s c : ℝ) * ((blkSize blk c - s c + 1 : ℕ) : ℝ))
        * cubeVec blk s z := by
  classical
  have key : ∀ x y P : ℝ, 0 ≤ x → 0 ≤ y →
      y * (Real.sqrt x * P) = Real.sqrt (x * y) * (Real.sqrt y * P) := by
    intro x y P hx hy
    rw [Real.sqrt_mul hx]
    have hy2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy
    linear_combination (- (Real.sqrt x * P)) * hy2
  have hsplit : ∑ w, ((if Inc blk s c z w then (1 : ℝ) else 0)
        + (if Inc blk s c w z then 1 else 0)) * cubeVec blk s w
      = (∑ w, (if Inc blk s c z w then (1 : ℝ) else 0) * cubeVec blk s w)
        + ∑ w, (if Inc blk s c w z then (1 : ℝ) else 0) * cubeVec blk s w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [hsplit]
  by_cases hlow : blkWt blk c z = s c - 1
  · -- low layer: only up-flips contribute
    have hzero2 : ∑ w, (if Inc blk s c w z then (1 : ℝ) else 0)
        * cubeVec blk s w = 0 := by
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [if_neg, zero_mul]
      intro h
      have h1 := h.2.2.2
      have h2 := hs1 c
      omega
    have himg : Finset.univ.filter (fun w => Inc blk s c z w)
        = (Finset.univ.filter fun i => blk i = c ∧ z i = false).image
            (fun i => Function.update z i true) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · intro h
        obtain ⟨i, hic, hzi, rfl⟩ := eq_update_of_inc h (hs1 c)
        exact ⟨i, ⟨hic, hzi⟩, rfl⟩
      · rintro ⟨i, ⟨hic, hzi⟩, rfl⟩
        exact inc_update hic hzi hlow (hs1 c)
    have hinj : ∀ i ∈ Finset.univ.filter
          (fun i => blk i = c ∧ z i = false),
        ∀ i' ∈ Finset.univ.filter (fun i => blk i = c ∧ z i = false),
        Function.update z i true = Function.update z i' true → i = i' := by
      intro i hi i' hi' hupd
      by_contra hne
      have h1 := congrFun hupd i
      rw [Function.update_apply, if_pos rfl, Function.update_apply,
        if_neg (fun hh => hne hh)] at h1
      rw [Finset.mem_filter] at hi
      rw [hi.2.2] at h1
      exact Bool.noConfusion h1
    have hvw : ∀ i ∈ Finset.univ.filter
          (fun i => blk i = c ∧ z i = false),
        cubeVec blk s (Function.update z i true)
          = Real.sqrt (s c)
            * ∏ c' ∈ Finset.univ.erase c, layerWeight blk s c' z := by
      intro i hi
      obtain ⟨-, hic, hzi⟩ :
          i ∈ Finset.univ ∧ blk i = c ∧ z i = false :=
        Finset.mem_filter.mp hi
      have hpe := Finset.mul_prod_erase Finset.univ
        (fun c' => layerWeight blk s c' (Function.update z i true))
        (Finset.mem_univ c)
      rw [cubeVec, ← hpe]
      have hc1 : layerWeight blk s c (Function.update z i true)
          = Real.sqrt (s c) := by
        rw [layerWeight, wt_update_true hic hzi, hlow]
        have h1 := hs1 c
        rw [if_neg (by omega), if_pos (by omega)]
      rw [hc1]
      congr 1
      refine Finset.prod_congr rfl fun c' hc' => ?_
      have hcc' := (Finset.mem_erase.mp hc').1
      exact layerWeight_update
        (fun hh => hcc' (hic.symm.trans hh).symm) z true
    have hcard : (Finset.univ.filter
        fun i => blk i = c ∧ z i = false).card
        = blkSize blk c - s c + 1 := by
      have h := wt_add_card_le (blk := blk) c z
      have h1 := hs1 c
      have h2 := hsm c
      omega
    have hvz : layerWeight blk s c z
        = Real.sqrt ((blkSize blk c - s c + 1 : ℕ) : ℝ) := by
      rw [layerWeight, if_pos hlow]
    calc (∑ w, (if Inc blk s c z w then (1 : ℝ) else 0) * cubeVec blk s w)
          + ∑ w, (if Inc blk s c w z then (1 : ℝ) else 0) * cubeVec blk s w
        = ∑ w ∈ Finset.univ.filter (fun w => Inc blk s c z w),
            cubeVec blk s w := by
          rw [hzero2, add_zero, Finset.sum_filter]
          exact Finset.sum_congr rfl fun w _ => by split_ifs <;> ring
      _ = ∑ i ∈ Finset.univ.filter (fun i => blk i = c ∧ z i = false),
            cubeVec blk s (Function.update z i true) := by
          rw [himg, Finset.sum_image hinj]
      _ = ∑ i ∈ Finset.univ.filter (fun i => blk i = c ∧ z i = false),
            (Real.sqrt (s c)
              * ∏ c' ∈ Finset.univ.erase c, layerWeight blk s c' z) :=
          Finset.sum_congr rfl hvw
      _ = ((blkSize blk c - s c + 1 : ℕ) : ℝ) * (Real.sqrt (s c)
            * ∏ c' ∈ Finset.univ.erase c, layerWeight blk s c' z) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ = Real.sqrt ((s c : ℝ) * ((blkSize blk c - s c + 1 : ℕ) : ℝ))
            * cubeVec blk s z := by
          have hpe := Finset.mul_prod_erase Finset.univ
            (fun c' => layerWeight blk s c' z) (Finset.mem_univ c)
          rw [cubeVec, ← hpe, hvz]
          exact key (s c : ℝ) ((blkSize blk c - s c + 1 : ℕ) : ℝ) _
            (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · by_cases hhigh : blkWt blk c z = s c
    · -- high layer: only down-flips contribute
      have hzero1 : ∑ w, (if Inc blk s c z w then (1 : ℝ) else 0)
          * cubeVec blk s w = 0 := by
        refine Finset.sum_eq_zero fun w _ => ?_
        rw [if_neg, zero_mul]
        intro h
        exact hlow h.2.2.1
      have himg : Finset.univ.filter (fun w => Inc blk s c w z)
          = (Finset.univ.filter fun i => blk i = c ∧ z i = true).image
              (fun i => Function.update z i false) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image]
        constructor
        · intro h
          obtain ⟨i, hic, hwi, hz⟩ := eq_update_of_inc h (hs1 c)
          have hzi : z i = true := by
            have := congrFun hz i
            rwa [Function.update_apply, if_pos rfl] at this
          refine ⟨i, ⟨hic, hzi⟩, ?_⟩
          funext j
          rcases eq_or_ne j i with rfl | hj
          · rw [Function.update_apply, if_pos rfl, hwi]
          · have := congrFun hz j
            rw [Function.update_apply, if_neg hj] at this
            rw [Function.update_apply, if_neg hj, ← this]
        · rintro ⟨i, ⟨hic, hzi⟩, rfl⟩
          have hwi : Function.update z i false i = false := by
            rw [Function.update_apply, if_pos rfl]
          have hwwt : blkWt blk c (Function.update z i false) = s c - 1 := by
            have := wt_update_false hic hzi
            rw [hhigh] at this
            omega
          have hupd : Function.update (Function.update z i false) i true
              = z := by
            funext j
            rcases eq_or_ne j i with rfl | hj
            · rw [Function.update_apply, if_pos rfl, hzi]
            · rw [Function.update_apply, if_neg hj,
                Function.update_apply, if_neg hj]
          have := inc_update hic hwi hwwt (hs1 c)
          rwa [hupd] at this
      have hinj : ∀ i ∈ Finset.univ.filter
            (fun i => blk i = c ∧ z i = true),
          ∀ i' ∈ Finset.univ.filter (fun i => blk i = c ∧ z i = true),
          Function.update z i false = Function.update z i' false
            → i = i' := by
        intro i hi i' hi' hupd
        by_contra hne
        have h1 := congrFun hupd i
        rw [Function.update_apply, if_pos rfl, Function.update_apply,
          if_neg (fun hh => hne hh)] at h1
        rw [Finset.mem_filter] at hi
        rw [hi.2.2] at h1
        exact Bool.noConfusion h1.symm
      have hvw : ∀ i ∈ Finset.univ.filter
            (fun i => blk i = c ∧ z i = true),
          cubeVec blk s (Function.update z i false)
            = Real.sqrt ((blkSize blk c - s c + 1 : ℕ) : ℝ)
              * ∏ c' ∈ Finset.univ.erase c, layerWeight blk s c' z := by
        intro i hi
        obtain ⟨-, hic, hzi⟩ :
            i ∈ Finset.univ ∧ blk i = c ∧ z i = true :=
          Finset.mem_filter.mp hi
        have hpe := Finset.mul_prod_erase Finset.univ
          (fun c' => layerWeight blk s c' (Function.update z i false))
          (Finset.mem_univ c)
        rw [cubeVec, ← hpe]
        have hwwt : blkWt blk c (Function.update z i false) = s c - 1 := by
          have := wt_update_false hic hzi
          rw [hhigh] at this
          omega
        have hc1 : layerWeight blk s c (Function.update z i false)
            = Real.sqrt ((blkSize blk c - s c + 1 : ℕ) : ℝ) := by
          rw [layerWeight, if_pos hwwt]
        rw [hc1]
        congr 1
        refine Finset.prod_congr rfl fun c' hc' => ?_
        have hcc' := (Finset.mem_erase.mp hc').1
        exact layerWeight_update
          (fun hh => hcc' (hic.symm.trans hh).symm) z false
      have hcard : (Finset.univ.filter
          fun i => blk i = c ∧ z i = true).card = s c := by
        rw [← hhigh, blkWt]
      have hvz : layerWeight blk s c z = Real.sqrt (s c) := by
        rw [layerWeight, if_neg hlow, if_pos hhigh]
      calc (∑ w, (if Inc blk s c z w then (1 : ℝ) else 0)
              * cubeVec blk s w)
            + ∑ w, (if Inc blk s c w z then (1 : ℝ) else 0)
              * cubeVec blk s w
          = ∑ w ∈ Finset.univ.filter (fun w => Inc blk s c w z),
              cubeVec blk s w := by
            rw [hzero1, zero_add, Finset.sum_filter]
            exact Finset.sum_congr rfl fun w _ => by split_ifs <;> ring
        _ = ∑ i ∈ Finset.univ.filter (fun i => blk i = c ∧ z i = true),
              cubeVec blk s (Function.update z i false) := by
            rw [himg, Finset.sum_image hinj]
        _ = ∑ i ∈ Finset.univ.filter (fun i => blk i = c ∧ z i = true),
              (Real.sqrt ((blkSize blk c - s c + 1 : ℕ) : ℝ)
                * ∏ c' ∈ Finset.univ.erase c, layerWeight blk s c' z) :=
            Finset.sum_congr rfl hvw
        _ = (s c : ℝ) * (Real.sqrt ((blkSize blk c - s c + 1 : ℕ) : ℝ)
              * ∏ c' ∈ Finset.univ.erase c, layerWeight blk s c' z) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ = Real.sqrt ((s c : ℝ) * ((blkSize blk c - s c + 1 : ℕ) : ℝ))
              * cubeVec blk s z := by
            have hpe := Finset.mul_prod_erase Finset.univ
              (fun c' => layerWeight blk s c' z) (Finset.mem_univ c)
            rw [cubeVec, ← hpe, hvz,
              mul_comm ((s c : ℕ) : ℝ)
                ((blkSize blk c - s c + 1 : ℕ) : ℝ)]
            exact key ((blkSize blk c - s c + 1 : ℕ) : ℝ) ((s c : ℕ) : ℝ) _
              (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · -- off both layers: everything vanishes
      have hz0 : cubeVec blk s z = 0 := by
        rw [cubeVec]
        refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
        rw [layerWeight, if_neg hlow, if_neg hhigh]
      have hzero1 : ∑ w, (if Inc blk s c z w then (1 : ℝ) else 0)
          * cubeVec blk s w = 0 := by
        refine Finset.sum_eq_zero fun w _ => ?_
        rw [if_neg, zero_mul]
        intro h
        exact hlow h.2.2.1
      have hzero2 : ∑ w, (if Inc blk s c w z then (1 : ℝ) else 0)
          * cubeVec blk s w = 0 := by
        refine Finset.sum_eq_zero fun w _ => ?_
        rw [if_neg, zero_mul]
        intro h
        exact hhigh h.2.2.2
      rw [hzero1, hzero2, hz0, mul_zero, add_zero]

/-- **The exact eigenvalue equation.** -/
lemma cubeMat_mulVec_cubeVec (hs1 : ∀ c, 1 ≤ s c)
    (hsm : ∀ c, s c ≤ blkSize blk c) :
    cubeMat blk s *ᵥ cubeVec blk s
      = cubeTheta blk s • cubeVec blk s := by
  funext z
  calc (cubeMat blk s *ᵥ cubeVec blk s) z
      = ∑ w, (∑ c : ρ, ((if Inc blk s c z w then (1 : ℝ) else 0)
          + (if Inc blk s c w z then 1 else 0))) * cubeVec blk s w := rfl
    _ = ∑ w, ∑ c : ρ, ((if Inc blk s c z w then (1 : ℝ) else 0)
          + (if Inc blk s c w z then 1 else 0)) * cubeVec blk s w :=
        Finset.sum_congr rfl fun w _ => Finset.sum_mul _ _ _
    _ = ∑ c : ρ, ∑ w, ((if Inc blk s c z w then (1 : ℝ) else 0)
          + (if Inc blk s c w z then 1 else 0)) * cubeVec blk s w :=
        Finset.sum_comm
    _ = ∑ c : ρ, Real.sqrt ((s c : ℝ)
          * ((blkSize blk c - s c + 1 : ℕ) : ℝ)) * cubeVec blk s z :=
        Finset.sum_congr rfl fun c _ => block_eigen hs1 hsm c z
    _ = (cubeTheta blk s • cubeVec blk s) z := by
        rw [Pi.smul_apply, smul_eq_mul, cubeTheta, Finset.sum_mul]

/-- The eigenvector is nonzero. -/
lemma cubeVec_ne_zero (hs1 : ∀ c, 1 ≤ s c)
    (hsm : ∀ c, s c ≤ blkSize blk c) : cubeVec blk s ≠ 0 := by
  classical
  choose S hS hcard using fun c : ρ =>
    Finset.exists_subset_card_eq (n := s c)
      (s := Finset.univ.filter fun i => blk i = c) (hsm c)
  set z0 : ι → Bool := fun i => decide (i ∈ S (blk i)) with hz0
  have hwt : ∀ c, blkWt blk c z0 = s c := by
    intro c
    rw [blkWt, ← hcard c]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hz0,
      decide_eq_true_eq]
    constructor
    · rintro ⟨hc, hj⟩
      rwa [hc] at hj
    · intro hj
      have hjc : blk j = c := by
        have := hS c hj
        rw [Finset.mem_filter] at this
        exact this.2
      rw [hjc]
      exact ⟨rfl, hj⟩
  refine Function.ne_iff.mpr ⟨z0, ?_⟩
  rw [cubeVec, Pi.zero_apply]
  refine ne_of_gt (Finset.prod_pos fun c _ => ?_)
  rw [layerWeight, hwt c]
  have h1 := hs1 c
  rw [if_neg (by omega), if_pos rfl]
  exact Real.sqrt_pos.mpr (by exact_mod_cast h1)

end Eigen

/-! ## The matching bound -/

section Matching

variable {blk : ι → ρ} {s : ρ → ℕ}

lemma cubeMat_nonneg (z w : ι → Bool) : 0 ≤ cubeMat blk s z w := by
  refine Finset.sum_nonneg fun c _ => ?_
  have h1 : (0 : ℝ) ≤ if Inc blk s c z w then (1 : ℝ) else 0 := by
    split_ifs <;> norm_num
  have h2 : (0 : ℝ) ≤ if Inc blk s c w z then (1 : ℝ) else 0 := by
    split_ifs <;> norm_num
  linarith

lemma cubeMat_le_one (hs1 : ∀ c, 1 ≤ s c) (z w : ι → Bool) :
    cubeMat blk s z w ≤ 1 := by
  classical
  by_cases hex : ∃ c, Inc blk s c z w ∨ Inc blk s c w z
  · obtain ⟨c₀, hc₀⟩ := hex
    have hsingle : cubeMat blk s z w
        = (if Inc blk s c₀ z w then (1 : ℝ) else 0)
          + (if Inc blk s c₀ w z then 1 else 0) := by
      refine Finset.sum_eq_single c₀ (fun c' _ hne => ?_)
        (fun h => absurd (Finset.mem_univ _) h)
      rw [if_neg, if_neg]
      · norm_num
      · intro h'
        rcases hc₀ with hc | hc
        · exact not_inc_symm hc h' (hs1 c₀)
        · exact hne (inc_block_eq hc h' (hs1 c₀) (hs1 c')).symm
      · intro h'
        rcases hc₀ with hc | hc
        · exact hne (inc_block_eq hc h' (hs1 c₀) (hs1 c')).symm
        · exact not_inc_symm h' hc (hs1 c')
    rw [hsingle]
    split_ifs with h1 h2
    · exact (not_inc_symm h1 h2 (hs1 c₀)).elim
    · norm_num
    · norm_num
    · norm_num
  · push_neg at hex
    have h0 : cubeMat blk s z w = 0 :=
      Finset.sum_eq_zero fun c _ => by
        rw [if_neg (hex c).1, if_neg (hex c).2, add_zero]
    rw [h0]
    norm_num

/-- A flip mask on the cube is a partial matching: entries survive only on
the graph of the flip-at-`i` involution. -/
lemma cubeMat_hadamard_advD_norm_le (hs1 : ∀ c, 1 ≤ s c) (i : ι) :
    ‖cubeMat blk s ⊙ advD (σ := Bool) i‖ ≤ 1 := by
  classical
  refine l2_opNorm_le_one_of_equiv_support _ (flipEquiv i) ?_ ?_
  · intro z w hw
    rw [Matrix.hadamard_apply, advD_apply]
    by_cases hzw : z i = w i
    · rw [if_pos hzw, mul_zero]
    · rw [if_neg hzw]
      have hcube : cubeMat blk s z w = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        have hup : ¬ Inc blk s c z w := by
          intro h
          obtain ⟨j, hjc, hzj, rfl⟩ := eq_update_of_inc h (hs1 c)
          have hij : i = j := by
            by_contra hij
            exact hzw (by rw [Function.update_apply, if_neg hij])
          subst hij
          refine hw ?_
          show Function.update z i true = Function.update z i (!z i)
          rw [hzj]
          rfl
        have hdown : ¬ Inc blk s c w z := by
          intro h
          obtain ⟨j, hjc, hwj, hz⟩ := eq_update_of_inc h (hs1 c)
          have hij : i = j := by
            by_contra hij
            refine hzw ?_
            have h1 := congrFun hz i
            rw [Function.update_apply, if_neg hij] at h1
            exact h1
          subst hij
          have hzi : z i = true := by
            have h1 := congrFun hz i
            rwa [Function.update_apply, if_pos rfl] at h1
          refine hw ?_
          show w = Function.update z i (!z i)
          rw [hzi]
          funext j'
          rcases eq_or_ne j' i with rfl | hj'
          · rw [Function.update_apply, if_pos rfl, hwj]
            rfl
          · rw [Function.update_apply, if_neg hj']
            have h1 := congrFun hz j'
            rw [Function.update_apply, if_neg hj'] at h1
            exact h1.symm
        rw [if_neg hup, if_neg hdown, add_zero]
      rw [hcube, zero_mul]
  · intro z w
    rw [Matrix.hadamard_apply, advD_apply]
    by_cases hzw : z i = w i
    · rw [if_pos hzw, mul_zero, abs_zero]
      norm_num
    · rw [if_neg hzw, mul_one, abs_of_nonneg (cubeMat_nonneg z w)]
      exact cubeMat_le_one hs1 z w

end Matching

/-! ## Assembly -/

section Assembly

variable {k : ℕ} {blk : ι → ρ} {s : ρ → ℕ}
variable {m : σ → ρ → Capped k} {s0 : σ} {e : ρ → σ}

lemma advD_submatrix_cubeEmb (hs0e : ∀ j, s0 ≠ e j) (i : ι) :
    (advD (σ := σ) i).submatrix (cubeEmb blk s0 e) (cubeEmb blk s0 e)
      = advD (σ := Bool) i := by
  ext z w
  rw [Matrix.submatrix_apply, advD_apply, advD_apply]
  have hiff : (cubeEmb blk s0 e z i = cubeEmb blk s0 e w i)
      ↔ (z i = w i) := by
    show ((if z i then e (blk i) else s0) = if w i then e (blk i) else s0)
      ↔ (z i = w i)
    cases hzz : z i <;> cases hww : w i <;>
      simp [hs0e (blk i), Ne.symm (hs0e (blk i))]
  exact if_congr hiff rfl rfl

/-- **The parametric capped-counter lower bound** (`thm:capped-counter-product`,
lower half): for any block assignment and any in-range layer choice,
`∑_c √(s c · (blkSize c − s c + 1)) ≤ ADV±(Prod)`. -/
theorem cubeTheta_le_advPM_prodFun (hk : 0 < k) (hm0 : m s0 = 1)
    (hme : ∀ j, m (e j) = cappedUnit k j) (hs0e : ∀ j, s0 ≠ e j)
    (hs1 : ∀ c, 1 ≤ s c) (hsk : ∀ c, s c ≤ k)
    (hsm : ∀ c, s c ≤ blkSize blk c) :
    cubeTheta blk s ≤ advPM (fun x : ι → σ => ∏ i, m (x i)) := by
  have hre : ∀ z, cubeRetr blk e (cubeEmb blk s0 e z) = z :=
    cubeRetr_cubeEmb hs0e
  have h1 : IsAdvMatrix (fun x : ι → σ => ∏ i, m (x i))
      (embMat (cubeEmb blk s0 e) (cubeRetr blk e) (cubeMat blk s)) :=
    isAdvMatrix_embMat_cubeMat hk hm0 hme hs0e hs1 hsk
  have h2 : ∀ i, ‖embMat (cubeEmb blk s0 e) (cubeRetr blk e)
      (cubeMat blk s) ⊙ advD i‖ ≤ 1 := by
    intro i
    rw [embMat_hadamard, advD_submatrix_cubeEmb hs0e i]
    exact le_trans (l2_opNorm_embMat_le hre _)
      (cubeMat_hadamard_advD_norm_le hs1 i)
  have heig : embMat (cubeEmb blk s0 e) (cubeRetr blk e) (cubeMat blk s)
      *ᵥ embVec (cubeEmb blk s0 e) (cubeRetr blk e) (cubeVec blk s)
      = cubeTheta blk s
        • embVec (cubeEmb blk s0 e) (cubeRetr blk e) (cubeVec blk s) := by
    rw [embMat_mulVec_embVec hre, cubeMat_mulVec_cubeVec hs1 hsm]
    funext x
    rw [embVec, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      embVec]
    ring
  have h3 : cubeTheta blk s
      ≤ ‖embMat (cubeEmb blk s0 e) (cubeRetr blk e) (cubeMat blk s)‖ := by
    have habs := abs_eigenvalue_le_norm heig
      (embVec_ne_zero hre (cubeVec_ne_zero hs1 hsm))
    exact (le_abs_self _).trans habs
  have h4 := norm_div_le_advPM h1 h2 one_pos
  rw [div_one] at h4
  exact h3.trans h4

end Assembly

end MonoidProduct
