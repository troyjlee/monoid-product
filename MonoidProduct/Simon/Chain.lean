import MonoidProduct.Simon.Kernel
import MonoidProduct.UT.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Chain matrices, block sums, and the division into `UT_K(𝔹)`

The last step of the Simon formalization: realize each short pattern by a Boolean
**chain matrix**, combine the chains block-diagonally, and factor
`List.prod` through the range of the resulting word-to-matrix
homomorphism.  No quotient monoid is constructed.  The matrix-division
statement itself is Pin–Straubing's Theorem 1 (*Monoids of upper
triangular matrices*, Semigroups, Szeged 1981, Colloq. Math. Soc. János
Bolyai 39, 1985): a finite monoid is 𝓙-trivial iff it divides a monoid of
reflexive upper-triangular Boolean matrices — of which only the forward
direction is formalized here.

* `chainMat p w` — the `(|p|+1) × (|p|+1)` matrix whose `(i, j)` entry says
  "the segment `p[i..j)` is a subword of `w`".  It is reflexive
  unitriangular, `chainMat p [] = 1`, and it is a **homomorphism** on
  words: a subword of `w₁ ++ w₂` splits at some point
  (`List.sublist_append_iff`).  Its `(0, |p|)` entry is `[p <+ w]`.
* `blockDiag A B` — the block sum in `BUT (k₁ + k₂)`, a homomorphism in
  both arguments.
* `chainWord ps w` — the block sum of the chain matrices of a list of
  patterns; a homomorphism, with every pattern's readout entry.
* `exists_divides_but_of_isJTrivial` — with `ps` all patterns of length
  `≤ 2|M| − 2`, the kernel says `chainWord ps u = chainWord ps v →
  u.prod = v.prod`, so `List.prod` factors through the range of
  `chainWord ps`: a subsemigroup of `BUT K` mapping onto `M`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open List

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## Chain matrices -/

/-- The segment `p[i..j)` of a pattern. -/
def seg (p : List M) (i j : ℕ) : List M := (p.drop i).take (j - i)

lemma seg_self (p : List M) (i : ℕ) : seg p i i = [] := by simp [seg]

lemma seg_append (p : List M) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    seg p i k = seg p i j ++ seg p j k := by
  simp only [seg]
  rw [show k - i = (j - i) + (k - j) from by omega, List.take_add, List.drop_drop,
    show i + (j - i) = j from by omega]

lemma length_seg (p : List M) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    (seg p i j).length = j - i := by
  simp only [seg, List.length_take, List.length_drop]
  omega

/-- **The chain matrix** of a pattern on a word: `(i, j)` says that the
segment `p[i..j)` occurs in `w`. -/
def chainMat (p : List M) (w : List M) : BMat (p.length + 1) :=
  fun i j => decide ((i : ℕ) ≤ (j : ℕ) ∧ List.Sublist (seg p i j) w)

lemma chainMat_apply (p w : List M) (i j : Fin (p.length + 1)) :
    chainMat p w i j = true ↔ (i : ℕ) ≤ (j : ℕ) ∧ List.Sublist (seg p i j) w := by
  simp [chainMat]

lemma isBUtri_chainMat (p w : List M) : IsBUtri (chainMat p w) where
  diag i := (chainMat_apply p w i i).mpr ⟨le_rfl, by rw [seg_self]; exact List.nil_sublist _⟩
  below s t hts := by
    have : ¬ ((s : ℕ) ≤ (t : ℕ)) := not_le.mpr hts
    simp [chainMat, this]

/-- The chain matrix of the empty word is the identity. -/
lemma chainMat_nil (p : List M) : chainMat p [] = bone (p.length + 1) := by
  funext i j
  rw [chainMat, bone]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨hij, hsub⟩
    rw [List.sublist_nil] at hsub
    have := congrArg List.length hsub
    rw [length_seg p hij (by omega), List.length_nil] at this
    exact Fin.ext (by omega)
  · rintro rfl
    exact ⟨le_rfl, by rw [seg_self]⟩

/-- **The chain matrix is a homomorphism on words**: a subword of a
concatenation splits at some intermediate state. -/
lemma chainMat_append (p w₁ w₂ : List M) :
    chainMat p (w₁ ++ w₂) = bmul (chainMat p w₁) (chainMat p w₂) := by
  funext i k
  rw [Bool.eq_iff_iff, chainMat_apply, bmul_apply]
  constructor
  · rintro ⟨hik, hsub⟩
    obtain ⟨l₁, l₂, hl, h₁, h₂⟩ := List.sublist_append_iff.mp hsub
    have hlen : l₁.length ≤ (k : ℕ) - (i : ℕ) := by
      have := congrArg List.length hl
      rw [length_seg p hik (by omega), List.length_append] at this
      omega
    have hsplit := seg_append p (show (i : ℕ) ≤ (i : ℕ) + l₁.length by omega)
      (show (i : ℕ) + l₁.length ≤ (k : ℕ) by omega)
    rw [hl] at hsplit
    have hl₁ : l₁.length = (seg p i ((i : ℕ) + l₁.length)).length := by
      rw [length_seg p (by omega) (by omega)]; omega
    refine ⟨⟨(i : ℕ) + l₁.length, by omega⟩, ?_, ?_⟩
    · rw [chainMat_apply]
      refine ⟨by simp, ?_⟩
      show List.Sublist (seg p (i : ℕ) ((i : ℕ) + l₁.length)) w₁
      rw [← List.append_inj_left hsplit hl₁]
      exact h₁
    · rw [chainMat_apply]
      refine ⟨by simp; omega, ?_⟩
      show List.Sublist (seg p ((i : ℕ) + l₁.length) (k : ℕ)) w₂
      rw [← List.append_inj_right hsplit hl₁]
      exact h₂
  · rintro ⟨j, hij, hjk⟩
    rw [chainMat_apply] at hij hjk
    refine ⟨le_trans hij.1 hjk.1, ?_⟩
    rw [seg_append p hij.1 hjk.1]
    exact hij.2.append hjk.2

/-- The readout: the `(0, |p|)` entry is `[p <+ w]`. -/
lemma chainMat_zero_last (p w : List M) :
    chainMat p w ⟨0, by omega⟩ ⟨p.length, by omega⟩ = decide (List.Sublist p w) := by
  rw [chainMat]
  apply decide_eq_decide.mpr
  simp [seg]

/-- The chain matrix, as an element of `UT_{|p|+1}(𝔹)`. -/
def chain (p w : List M) : BUT (p.length + 1) :=
  Subtype.mk (chainMat p w) (isBUtri_chainMat p w)

@[simp] lemma mat_chain (p w : List M) : (chain p w).mat = chainMat p w := rfl

lemma chain_nil (p : List M) : chain p [] = 1 :=
  BUT.ext (by rw [mat_chain, chainMat_nil, BUT.mat_one])

lemma chain_append (p w₁ w₂ : List M) : chain p (w₁ ++ w₂) = chain p w₁ * chain p w₂ :=
  BUT.ext (by rw [mat_chain, BUT.mat_mul, mat_chain, mat_chain, chainMat_append])

/-! ## Block sums -/

variable {k₁ k₂ : ℕ}

/-- The block sum of two Boolean matrices. -/
def blockMat (A : BMat k₁) (B : BMat k₂) : BMat (k₁ + k₂) := fun x y =>
  if hx : (x : ℕ) < k₁ then
    (if hy : (y : ℕ) < k₁ then A ⟨x, hx⟩ ⟨y, hy⟩ else false)
  else
    (if hy : (y : ℕ) < k₁ then false
      else B ⟨(x : ℕ) - k₁, by omega⟩ ⟨(y : ℕ) - k₁, by omega⟩)

lemma blockMat_lt_lt (A : BMat k₁) (B : BMat k₂) {x y : Fin (k₁ + k₂)}
    (hx : (x : ℕ) < k₁) (hy : (y : ℕ) < k₁) :
    blockMat A B x y = A ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [blockMat, hx, hy]

lemma blockMat_ge_ge (A : BMat k₁) (B : BMat k₂) {x y : Fin (k₁ + k₂)}
    (hx : k₁ ≤ (x : ℕ)) (hy : k₁ ≤ (y : ℕ)) :
    blockMat A B x y = B ⟨(x : ℕ) - k₁, by omega⟩ ⟨(y : ℕ) - k₁, by omega⟩ := by
  simp [blockMat, not_lt.mpr hx, not_lt.mpr hy]

lemma blockMat_mixed (A : BMat k₁) (B : BMat k₂) {x y : Fin (k₁ + k₂)}
    (h : ((x : ℕ) < k₁ ∧ k₁ ≤ (y : ℕ)) ∨ (k₁ ≤ (x : ℕ) ∧ (y : ℕ) < k₁)) :
    blockMat A B x y = false := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · simp [blockMat, hx, not_lt.mpr hy]
  · simp [blockMat, not_lt.mpr hx, hy]

lemma blockMat_bone : blockMat (bone k₁) (bone k₂) = bone (k₁ + k₂) := by
  funext x y
  by_cases hx : (x : ℕ) < k₁ <;> by_cases hy : (y : ℕ) < k₁
  · rw [blockMat_lt_lt _ _ hx hy, bone, bone]
    apply decide_eq_decide.mpr
    simp [Fin.ext_iff]
  · rw [blockMat_mixed _ _ (Or.inl ⟨hx, not_lt.mp hy⟩), bone]
    symm
    rw [decide_eq_false_iff_not, Fin.ext_iff]
    omega
  · rw [blockMat_mixed _ _ (Or.inr ⟨not_lt.mp hx, hy⟩), bone]
    symm
    rw [decide_eq_false_iff_not, Fin.ext_iff]
    omega
  · rw [blockMat_ge_ge _ _ (not_lt.mp hx) (not_lt.mp hy), bone, bone]
    apply decide_eq_decide.mpr
    simp only [Fin.ext_iff]
    omega

/-- **The block sum is multiplicative.** -/
lemma blockMat_bmul (A A' : BMat k₁) (B B' : BMat k₂) :
    blockMat (bmul A A') (bmul B B') = bmul (blockMat A B) (blockMat A' B') := by
  funext x z
  by_cases hx : (x : ℕ) < k₁ <;> by_cases hz : (z : ℕ) < k₁
  · rw [blockMat_lt_lt _ _ hx hz, bmul, bmul]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨y, h1, h2⟩
      refine ⟨⟨(y : ℕ), by omega⟩, ?_, ?_⟩
      · rw [blockMat_lt_lt _ _ hx (by simp)]; exact h1
      · rw [blockMat_lt_lt _ _ (by simp) hz]; exact h2
    · rintro ⟨y, h1, h2⟩
      by_cases hy : (y : ℕ) < k₁
      · refine ⟨⟨y, hy⟩, ?_, ?_⟩
        · rw [blockMat_lt_lt _ _ hx hy] at h1; exact h1
        · rw [blockMat_lt_lt _ _ hy hz] at h2; exact h2
      · rw [blockMat_mixed _ _ (Or.inl ⟨hx, not_lt.mp hy⟩)] at h1
        exact absurd h1 Bool.false_ne_true
  · rw [blockMat_mixed _ _ (Or.inl ⟨hx, not_lt.mp hz⟩), bmul]
    symm
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro y h1 h2
    by_cases hy : (y : ℕ) < k₁
    · rw [blockMat_mixed _ _ (Or.inl ⟨hy, not_lt.mp hz⟩)] at h2
      exact absurd h2 Bool.false_ne_true
    · rw [blockMat_mixed _ _ (Or.inl ⟨hx, not_lt.mp hy⟩)] at h1
      exact absurd h1 Bool.false_ne_true
  · rw [blockMat_mixed _ _ (Or.inr ⟨not_lt.mp hx, hz⟩), bmul]
    symm
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro y h1 h2
    by_cases hy : (y : ℕ) < k₁
    · rw [blockMat_mixed _ _ (Or.inr ⟨not_lt.mp hx, hy⟩)] at h1
      exact absurd h1 Bool.false_ne_true
    · rw [blockMat_mixed _ _ (Or.inr ⟨not_lt.mp hy, hz⟩)] at h2
      exact absurd h2 Bool.false_ne_true
  · rw [blockMat_ge_ge _ _ (not_lt.mp hx) (not_lt.mp hz), bmul, bmul]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨y, h1, h2⟩
      refine ⟨⟨(y : ℕ) + k₁, by omega⟩, ?_, ?_⟩
      · rw [blockMat_ge_ge _ _ (not_lt.mp hx) (by simp)]
        convert h1 using 2
        exact Fin.ext (by simp)
      · rw [blockMat_ge_ge _ _ (by simp) (not_lt.mp hz)]
        convert h2 using 2
        exact Fin.ext (by simp)
    · rintro ⟨y, h1, h2⟩
      by_cases hy : (y : ℕ) < k₁
      · rw [blockMat_mixed _ _ (Or.inr ⟨not_lt.mp hx, hy⟩)] at h1
        exact absurd h1 Bool.false_ne_true
      · refine ⟨⟨(y : ℕ) - k₁, by omega⟩, ?_, ?_⟩
        · rw [blockMat_ge_ge _ _ (not_lt.mp hx) (not_lt.mp hy)] at h1; exact h1
        · rw [blockMat_ge_ge _ _ (not_lt.mp hy) (not_lt.mp hz)] at h2; exact h2

lemma isBUtri_blockMat {A : BMat k₁} {B : BMat k₂} (hA : IsBUtri A) (hB : IsBUtri B) :
    IsBUtri (blockMat A B) where
  diag x := by
    by_cases hx : (x : ℕ) < k₁
    · rw [blockMat_lt_lt _ _ hx hx]; exact hA.diag _
    · rw [blockMat_ge_ge _ _ (not_lt.mp hx) (not_lt.mp hx)]; exact hB.diag _
  below s t hts := by
    have hts' : (t : ℕ) < (s : ℕ) := hts
    by_cases hs : (s : ℕ) < k₁ <;> by_cases ht : (t : ℕ) < k₁
    · rw [blockMat_lt_lt _ _ hs ht]
      exact hA.below _ _ (by simpa using hts')
    · omega
    · rw [blockMat_mixed _ _ (Or.inr ⟨not_lt.mp hs, ht⟩)]
    · rw [blockMat_ge_ge _ _ (not_lt.mp hs) (not_lt.mp ht)]
      exact hB.below _ _ (by simp; omega)

/-- The block sum in `UT`. -/
def blockDiag (A : BUT k₁) (B : BUT k₂) : BUT (k₁ + k₂) :=
  Subtype.mk (blockMat A.mat B.mat) (isBUtri_blockMat A.isBUtri_mat B.isBUtri_mat)

@[simp] lemma mat_blockDiag (A : BUT k₁) (B : BUT k₂) :
    (blockDiag A B).mat = blockMat A.mat B.mat := rfl

lemma blockDiag_one : blockDiag (1 : BUT k₁) (1 : BUT k₂) = 1 :=
  BUT.ext (by rw [mat_blockDiag, BUT.mat_one, BUT.mat_one, blockMat_bone, BUT.mat_one])

lemma blockDiag_mul (A A' : BUT k₁) (B B' : BUT k₂) :
    blockDiag (A * A') (B * B') = blockDiag A B * blockDiag A' B' :=
  BUT.ext (by
    rw [mat_blockDiag, BUT.mat_mul, BUT.mat_mul, BUT.mat_mul, blockMat_bmul,
      mat_blockDiag, mat_blockDiag])

/-! ## The word-to-matrix homomorphism over a list of patterns -/

/-- The total chain size of a list of patterns. -/
def chainSize : List (List M) → ℕ
  | [] => 0
  | p :: ps => (p.length + 1) + chainSize ps

/-- The block sum of the chain matrices of the patterns in `ps`. -/
def chainWord : (ps : List (List M)) → List M → BUT (chainSize ps)
  | [], _ => 1
  | p :: ps, w => blockDiag (chain p w) (chainWord ps w)

lemma chainWord_nil (ps : List (List M)) : chainWord ps [] = 1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      show blockDiag (chain p []) (chainWord ps []) = 1
      rw [chain_nil, ih, blockDiag_one]

lemma chainWord_append (ps : List (List M)) (w₁ w₂ : List M) :
    chainWord ps (w₁ ++ w₂) = chainWord ps w₁ * chainWord ps w₂ := by
  induction ps with
  | nil => show (1 : BUT 0) = 1 * 1; rw [mul_one]
  | cons p ps ih =>
      show blockDiag (chain p (w₁ ++ w₂)) (chainWord ps (w₁ ++ w₂))
        = blockDiag (chain p w₁) (chainWord ps w₁) * blockDiag (chain p w₂) (chainWord ps w₂)
      rw [chain_append, ih, blockDiag_mul]

/-- **Every pattern has a readout entry**: some fixed entry of
`chainWord ps w` is `[p <+ w]`, for every word `w`. -/
lemma exists_readout (ps : List (List M)) {p : List M} (hp : p ∈ ps) :
    ∃ x y : Fin (chainSize ps), ∀ w : List M,
      (chainWord ps w).mat x y = decide (List.Sublist p w) := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
      rw [List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine ⟨⟨0, by simp only [chainSize]; omega⟩,
          ⟨p.length, by simp only [chainSize]; omega⟩, fun w => ?_⟩
        change (blockDiag (chain p w) (chainWord ps w)).mat
          (⟨0, by omega⟩ : Fin (p.length + 1 + chainSize ps))
          (⟨p.length, by omega⟩ : Fin (p.length + 1 + chainSize ps))
          = decide (List.Sublist p w)
        rw [mat_blockDiag, blockMat_lt_lt _ _ (show 0 < p.length + 1 by omega)
          (show p.length < p.length + 1 by omega), mat_chain]
        exact chainMat_zero_last p w
      · obtain ⟨x, y, hxy⟩ := ih hp
        refine ⟨⟨q.length + 1 + (x : ℕ), by simp only [chainSize]; omega⟩,
          ⟨q.length + 1 + (y : ℕ), by simp only [chainSize]; omega⟩, fun w => ?_⟩
        change (blockDiag (chain q w) (chainWord ps w)).mat
          (⟨q.length + 1 + (x : ℕ), by omega⟩ : Fin (q.length + 1 + chainSize ps))
          (⟨q.length + 1 + (y : ℕ), by omega⟩ : Fin (q.length + 1 + chainSize ps))
          = decide (List.Sublist p w)
        rw [mat_blockDiag, blockMat_ge_ge _ _ (show q.length + 1 ≤ q.length + 1 + (x : ℕ) by omega)
          (show q.length + 1 ≤ q.length + 1 + (y : ℕ) by omega)]
        convert hxy w using 2 <;> exact Fin.ext (by simp)

/-! ## All short patterns -/

/-- All words over `M` of length exactly `ℓ`. -/
noncomputable def wordsOfLength (ℓ : ℕ) : List (List M) :=
  (Finset.univ : Finset (Fin ℓ → M)).toList.map List.ofFn

lemma mem_wordsOfLength {ℓ : ℕ} {p : List M} (hp : p.length = ℓ) : p ∈ wordsOfLength ℓ := by
  rw [wordsOfLength, List.mem_map]
  subst hp
  exact ⟨fun i => p[i], Finset.mem_toList.mpr (Finset.mem_univ _), List.ofFn_getElem⟩

/-- All words over `M` of length at most `k`. -/
noncomputable def shortPatterns (k : ℕ) : List (List M) :=
  (List.range (k + 1)).flatMap wordsOfLength

lemma mem_shortPatterns {k : ℕ} {p : List M} (hp : p.length ≤ k) : p ∈ shortPatterns k := by
  rw [shortPatterns, List.mem_flatMap]
  exact ⟨p.length, List.mem_range.mpr (by omega), mem_wordsOfLength rfl⟩

/-! ## The division -/

/-- **A finite 𝓙-trivial monoid divides a `UT_K(𝔹)`**: the forward direction
of Simon's theorem, with `K` the total chain size of all patterns of
length `≤ 2|M| − 2`.  `List.prod` factors through the range of
`chainWord` by the kernel; no quotient monoid is constructed. -/
theorem exists_divides_but_of_isJTrivial (hJ : IsJTrivialMonoid M) :
    ∃ K, 1 ≤ K ∧ SemigroupDivides M (BUT K) := by
  classical
  set ps : List (List M) := shortPatterns (2 * Fintype.card M - 2) with hps
  -- the kernel, through the readouts
  have hker : ∀ u v : List M, chainWord ps u = chainWord ps v → u.prod = v.prod := by
    intro u v huv
    refine prod_eq_of_sublist_iff hJ u v fun p hp => ?_
    obtain ⟨x, y, hxy⟩ := exists_readout ps (mem_shortPatterns (k := 2 * Fintype.card M - 2) hp)
    have := hxy u
    rw [huv, hxy v] at this
    simpa using this.symm
  -- the range of `chainWord ps`, as a subsemigroup
  let T : Subsemigroup (BUT (chainSize ps)) :=
    { carrier := Set.range (chainWord ps)
      mul_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u ++ v, chainWord_append ps u v⟩ }
  -- the homomorphism onto `M`
  have hT : ∀ x : T, ∃ w : List M, chainWord ps w = x := fun x => x.2
  choose wit hwit using hT
  let φ : T →ₙ* M :=
    { toFun := fun x => (wit x).prod
      map_mul' := by
        intro x y
        have h1 : chainWord ps (wit (x * y)) = chainWord ps (wit x ++ wit y) := by
          rw [hwit, chainWord_append, hwit, hwit]
          rfl
        rw [hker _ _ h1, List.prod_append] }
  refine ⟨chainSize ps, ?_, T, φ, fun m => ?_⟩
  · -- the empty pattern contributes a `1 × 1` block
    have : [] ∈ ps := mem_shortPatterns (by simp)
    obtain ⟨x, -, -⟩ := exists_readout ps this
    exact Nat.one_le_iff_ne_zero.mpr fun h => by rw [h] at x; exact x.elim0
  · refine ⟨⟨chainWord ps [m], ⟨[m], rfl⟩⟩, ?_⟩
    show (wit _).prod = m
    have := hker _ _ (hwit ⟨chainWord ps [m], ⟨[m], rfl⟩⟩)
    rw [this]
    simp

end MonoidProduct
