import MonoidProduct.Tropical.Unitriangular
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The path formula for products in `U_k(𝕋)`: `lem:path`

The paper's `lem:path` (Section `sec:tropical`): for `A₁, …, Aₙ ∈ U_k(𝕋)` the
entry `(A₁ ⋯ Aₙ)_{st}` is the maximum weight of a path
`s = h₀ ≤ h₁ ≤ ⋯ ≤ hₙ = t` with nondecreasing state indices, of weight
`∑ᵢ (Aᵢ)_{h_{i-1} h_i}`; a repeated state contributes a diagonal entry `0`, so
the weight is carried by the *strict transitions* (at increasing input
positions), and there are at most `t − s` of them.

The existing library proves only the consequence used by the algorithm
(`exists_transitionSupport`, `Tropical/Support.lean`) by an induction with no
paths.  Here the paths themselves are formalized.  A path of length `n` is a
map `h : Fin (n + 1) → Fin k` (the states `h₀, …, hₙ`; letter `i` is read on
the step `h i.castSucc → h i.succ`).

* `tpathWeight`, `tpathAll`, `tpathMono`, `tpathStrict`: the weight, the paths
  with given endpoints, the nondecreasing ones, and the strict-transition
  positions of a path.
* `linProd_eq_sup_tpathAll`: for **any** tropical matrices the `(s,t)` entry of
  the product is the maximum over all paths `s → t` (the matrix product
  expanded).
* `linProd_eq_sup_tpathMono`: for unitriangular letters, only nondecreasing
  paths are needed (`lem:path`, the path formula); `tpathMono_monotone_iff`
  identifies the stepwise condition with `Monotone`.
* `tpathWeight_eq_sum_strict`: the weight of a nondecreasing path is the sum
  over its strict transitions only.
* `card_tpathStrict_le`: a nondecreasing path `s → t` has at most `t − s`
  strict transitions (`lem:path`, second sentence).
* `exists_optimal_tpath`: an optimal nondecreasing path exists, and retaining
  exactly its strict-transition positions preserves the entry — the paper's
  path-defined certificate, verbatim.
* `UTrop.wordProd_val_apply_eq_sup_tpath`: the path formula for the bundled
  monoid `UTrop k`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {k : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## Paths and their weights -/

/-- The **weight** of the path `h₀, …, hₙ` through the word `x`:
`∑ᵢ (letter xᵢ)_{h_i h_{i+1}}` (tropical multiplication is `+`). -/
def tpathWeight (letter : σ → TMat k) {n : ℕ} (x : Fin n → σ)
    (h : Fin (n + 1) → Fin k) : Trop :=
  ∑ i : Fin n, letter (x i) (h i.castSucc) (h i.succ)

/-- All paths of length `n` from `s` to `t`. -/
def tpathAll (n : ℕ) (s t : Fin k) : Finset (Fin (n + 1) → Fin k) :=
  Finset.univ.filter fun h => h 0 = s ∧ h (Fin.last n) = t

/-- The **nondecreasing** paths of length `n` from `s` to `t`:
`s = h₀ ≤ h₁ ≤ ⋯ ≤ hₙ = t`. -/
def tpathMono (n : ℕ) (s t : Fin k) : Finset (Fin (n + 1) → Fin k) :=
  Finset.univ.filter fun h =>
    h 0 = s ∧ h (Fin.last n) = t ∧ ∀ i : Fin n, h i.castSucc ≤ h i.succ

/-- The positions at which the path makes a **strict transition**
`h_i < h_{i+1}`. -/
def tpathStrict {n : ℕ} (h : Fin (n + 1) → Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun i => h i.castSucc < h i.succ

lemma mem_tpathAll {n : ℕ} {s t : Fin k} {h : Fin (n + 1) → Fin k} :
    h ∈ tpathAll n s t ↔ h 0 = s ∧ h (Fin.last n) = t := by
  simp [tpathAll]

lemma mem_tpathMono {n : ℕ} {s t : Fin k} {h : Fin (n + 1) → Fin k} :
    h ∈ tpathMono n s t ↔
      h 0 = s ∧ h (Fin.last n) = t ∧ ∀ i : Fin n, h i.castSucc ≤ h i.succ := by
  simp [tpathMono]

/-- The stepwise condition of `tpathMono` is `Monotone`. -/
lemma tpathMono_monotone_iff {n : ℕ} {s t : Fin k} {h : Fin (n + 1) → Fin k} :
    h ∈ tpathMono n s t ↔ h 0 = s ∧ h (Fin.last n) = t ∧ Monotone h := by
  rw [mem_tpathMono, Fin.monotone_iff_le_succ]

lemma tpathMono_subset_tpathAll (n : ℕ) (s t : Fin k) :
    tpathMono n s t ⊆ tpathAll n s t := fun h hh => by
  rw [mem_tpathMono] at hh
  exact mem_tpathAll.2 ⟨hh.1, hh.2.1⟩

/-- Extending a path by one last state adds the last step's entry. -/
lemma tpathWeight_snoc (letter : σ → TMat k) {n : ℕ} (x : Fin (n + 1) → σ)
    (h : Fin (n + 1) → Fin k) (t : Fin k) :
    tpathWeight letter x (Fin.snoc (α := fun _ => Fin k) h t)
      = tpathWeight letter (fun i => x i.castSucc) h
          + letter (x (Fin.last n)) (h (Fin.last n)) t := by
  rw [tpathWeight, Fin.sum_univ_castSucc, tpathWeight]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc]
    simp only [Fin.snoc_castSucc]
  · rw [Fin.succ_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Splitting off the last step of a path. -/
lemma tpathWeight_init (letter : σ → TMat k) {n : ℕ} (x : Fin (n + 1) → σ)
    (h : Fin (n + 2) → Fin k) :
    tpathWeight letter x h
      = tpathWeight letter (fun i => x i.castSucc) (fun j => h j.castSucc)
          + letter (x (Fin.last n)) (h (Fin.last n).castSucc) (h (Fin.last (n + 1))) := by
  rw [tpathWeight, Fin.sum_univ_castSucc, tpathWeight, Fin.succ_last]
  rfl

private lemma tpath_finsetSup_add {α : Type*} (S : Finset α) (f : α → Trop) (b : Trop) :
    S.sup f + b = S.sup fun a => f a + b := by
  classical
  refine Finset.induction_on S (by simp) fun a S _ ih => ?_
  rw [Finset.sup_insert, Finset.sup_insert, ← ih]
  rcases le_total (f a) (S.sup f) with h | h
  · rw [sup_eq_right.2 h, sup_eq_right.2 (add_le_add h le_rfl)]
  · rw [sup_eq_left.2 h, sup_eq_left.2 (add_le_add h le_rfl)]

/-! ## The path formula -/

/-- **The matrix product expanded over paths.**  For arbitrary tropical
matrices, `(x₀ ⊗ ⋯ ⊗ x_{n-1})_{st}` is the maximum weight of a path of length
`n` from `s` to `t`. -/
theorem linProd_eq_sup_tpathAll (letter : σ → TMat k) :
    ∀ (n : ℕ) (x : Fin n → σ) (s t : Fin k),
      linProd letter n x s t = (tpathAll n s t).sup (tpathWeight letter x) := by
  intro n
  induction n with
  | zero =>
      intro x s t
      refine le_antisymm ?_ (Finset.sup_le fun h hh => ?_)
      · rw [linProd_zero, tone_apply]
        split_ifs with hst
        · subst hst
          refine le_trans (le_of_eq ?_) (Finset.le_sup (f := tpathWeight letter x)
            (mem_tpathAll.2 ⟨rfl, rfl⟩ : (fun _ => s) ∈ tpathAll 0 s s))
          simp [tpathWeight]
        · exact bot_le
      · obtain ⟨h0, ht⟩ := mem_tpathAll.1 hh
        have hst : s = t := by rw [← h0, ← ht]; rfl
        rw [linProd_zero, tone_apply, if_pos hst]
        simp [tpathWeight]
  | succ n ih =>
      intro x s t
      rw [linProd_succ]
      refine le_antisymm (Finset.sup_le fun v _ => ?_) (Finset.sup_le fun h hh => ?_)
      · rw [ih, tpath_finsetSup_add]
        refine Finset.sup_le fun h hh => ?_
        obtain ⟨h0, hv⟩ := mem_tpathAll.1 hh
        have hmem : Fin.snoc (α := fun _ => Fin k) h t ∈ tpathAll (n + 1) s t := by
          refine mem_tpathAll.2 ⟨?_, by simp⟩
          rw [← h0, ← Fin.castSucc_zero, Fin.snoc_castSucc]
        refine le_trans (le_of_eq ?_) (Finset.le_sup hmem)
        rw [tpathWeight_snoc, hv]
      · obtain ⟨h0, ht⟩ := mem_tpathAll.1 hh
        set v := h (Fin.last n).castSucc
        have hmem : (fun j : Fin (n + 1) => h j.castSucc) ∈ tpathAll n s v :=
          mem_tpathAll.2 ⟨by rw [Fin.castSucc_zero, h0], rfl⟩
        rw [tpathWeight_init, ht]
        refine le_trans ?_ (Finset.le_sup (f := fun v =>
          linProd letter n (fun i => x i.castSucc) s v + letter (x (Fin.last n)) v t)
          (Finset.mem_univ v))
        refine add_le_add ?_ le_rfl
        rw [ih]
        exact Finset.le_sup (f := tpathWeight letter fun i => x i.castSucc) hmem

/-- A path with a backward step has weight `−∞` through a unitriangular
alphabet. -/
lemma tpathWeight_eq_bot_of_step {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    {n : ℕ} (x : Fin n → σ) {h : Fin (n + 1) → Fin k} {i : Fin n}
    (hi : h i.succ < h i.castSucc) : tpathWeight letter x h = ⊥ := by
  rw [tpathWeight, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    (hL (x i)).below _ _ hi, WithBot.bot_add]

/-- **`lem:path`, the path formula.**  For a unitriangular alphabet the
`(s,t)` entry of `x₀ ⊗ ⋯ ⊗ x_{n-1}` is the maximum, over nondecreasing paths
`s = h₀ ≤ ⋯ ≤ hₙ = t`, of `∑ᵢ (xᵢ)_{hᵢ h_{i+1}}`. -/
theorem linProd_eq_sup_tpathMono {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (n : ℕ) (x : Fin n → σ) (s t : Fin k) :
    linProd letter n x s t = (tpathMono n s t).sup (tpathWeight letter x) := by
  rw [linProd_eq_sup_tpathAll]
  refine le_antisymm (Finset.sup_le fun h hh => ?_)
    (Finset.sup_mono (tpathMono_subset_tpathAll n s t))
  obtain ⟨h0, ht⟩ := mem_tpathAll.1 hh
  by_cases hmono : ∀ i : Fin n, h i.castSucc ≤ h i.succ
  · exact Finset.le_sup (mem_tpathMono.2 ⟨h0, ht, hmono⟩)
  · simp only [not_forall, not_le] at hmono
    obtain ⟨i, hi⟩ := hmono
    rw [tpathWeight_eq_bot_of_step hL x hi]
    exact bot_le

/-! ## Strict transitions -/

/-- **Stays weigh nothing**: the weight of a nondecreasing path through a
unitriangular alphabet is the sum over its strict transitions alone. -/
theorem tpathWeight_eq_sum_strict {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    {n : ℕ} (x : Fin n → σ) {h : Fin (n + 1) → Fin k}
    (hmono : ∀ i : Fin n, h i.castSucc ≤ h i.succ) :
    tpathWeight letter x h
      = ∑ i ∈ tpathStrict h, letter (x i) (h i.castSucc) (h i.succ) := by
  rw [tpathStrict, Finset.sum_filter, tpathWeight]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hlt
  · rfl
  · have heq : h i.castSucc = h i.succ := le_antisymm (hmono i) (not_lt.1 hlt)
    rw [heq, (hL _).diag]

/-- The strict transitions of a nondecreasing path, counted against its
climb: `#strict + h₀ ≤ hₙ`. -/
lemma card_tpathStrict_add_le :
    ∀ {n : ℕ} (h : Fin (n + 1) → Fin k), (∀ i : Fin n, h i.castSucc ≤ h i.succ) →
      (tpathStrict h).card + (h 0 : ℕ) ≤ h (Fin.last n)
  | 0, h, _ => by simp [tpathStrict]
  | n + 1, h, hmono => by
      have ih := card_tpathStrict_add_le (fun j : Fin (n + 1) => h j.castSucc)
        fun i => by rw [← Fin.succ_castSucc]; exact hmono i.castSucc
      have hcard : (tpathStrict h).card
          = (tpathStrict fun j : Fin (n + 1) => h j.castSucc).card
            + if h (Fin.last n).castSucc < h (Fin.last (n + 1)) then 1 else 0 := by
        rw [tpathStrict, tpathStrict, Finset.card_filter, Finset.card_filter,
          Fin.sum_univ_castSucc, Fin.succ_last]
        simp only [Fin.succ_castSucc]
      have hstep := hmono (Fin.last n)
      rw [Fin.succ_last] at hstep
      simp only [Fin.castSucc_zero] at ih
      rw [hcard]
      split_ifs with hlt
      · have : ((h (Fin.last n).castSucc : ℕ)) < h (Fin.last (n + 1)) := hlt
        omega
      · have : ((h (Fin.last n).castSucc : ℕ)) ≤ h (Fin.last (n + 1)) := hstep
        omega

/-- **`lem:path`, second sentence**: a nondecreasing path from `s` to `t`
makes at most `t − s` strict transitions. -/
theorem card_tpathStrict_le {n : ℕ} {s t : Fin k} {h : Fin (n + 1) → Fin k}
    (hh : h ∈ tpathMono n s t) : (tpathStrict h).card ≤ (t : ℕ) - s := by
  obtain ⟨h0, ht, hmono⟩ := mem_tpathMono.1 hh
  have := card_tpathStrict_add_le h hmono
  rw [h0, ht] at this
  omega

/-- **An optimal path, and its strict transitions as a certificate.**  If the
entry is finite, some nondecreasing path `s → t` attains it; it has at most
`t − s` strict transitions, and retaining exactly the letters at those
positions (all others replaced by the identity) preserves the entry.  This is
the paper's path-defined certificate; `exists_transitionSupport` is the
path-free consequence. -/
theorem exists_optimal_tpath {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (n : ℕ) (x : Fin n → σ) {s t : Fin k} (hne : linProd letter n x s t ≠ ⊥) :
    ∃ h ∈ tpathMono n s t,
      linProd letter n x s t = tpathWeight letter x h ∧
      (tpathStrict h).card ≤ (t : ℕ) - s ∧
      linProd (optLetter letter) n (mask (tpathStrict h) x) s t
        = linProd letter n x s t := by
  have hS : (tpathMono n s t).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hS
    rw [linProd_eq_sup_tpathMono hL, hS, Finset.sup_empty] at hne
    exact hne rfl
  obtain ⟨h, hh, hopt⟩ := Finset.exists_mem_eq_sup _ hS (tpathWeight letter x)
  rw [← linProd_eq_sup_tpathMono hL] at hopt
  refine ⟨h, hh, hopt, card_tpathStrict_le hh,
    le_antisymm (linProd_mask_le hL _ x s t) ?_⟩
  obtain ⟨h0, ht, hmono⟩ := mem_tpathMono.1 hh
  have hw : tpathWeight (optLetter letter) (mask (tpathStrict h) x) h
      = tpathWeight letter x h := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ tpathStrict h
    · rw [mask_apply, if_pos hi, optLetter_some]
    · have hlt : ¬ h i.castSucc < h i.succ := by simpa [tpathStrict] using hi
      have heq : h i.castSucc = h i.succ := le_antisymm (hmono i) (not_lt.1 hlt)
      rw [mask_apply, if_neg hi, optLetter_none, heq, (hL _).diag, tone_apply, if_pos rfl]
  rw [hopt, linProd_eq_sup_tpathAll, ← hw]
  exact Finset.le_sup (mem_tpathAll.2 ⟨h0, ht⟩)

/-! ## The bundled monoid -/

/-- **`lem:path` in `U_k(𝕋)`**: the `(s,t)` entry of the monoid product
`x₁ ⋯ xₙ` is the maximum weight of a nondecreasing path from `s` to `t`. -/
theorem UTrop.wordProd_val_apply_eq_sup_tpath (letter : σ → UTrop k) {n : ℕ}
    (x : Fin n → σ) (s t : Fin k) :
    (wordProd letter x).val s t
      = (tpathMono n s t).sup (tpathWeight (fun a => (letter a).val) x) := by
  rw [UTrop.wordProd_val]
  exact linProd_eq_sup_tpathMono (fun a => (letter a).isUtri) n x s t

end MonoidProduct
