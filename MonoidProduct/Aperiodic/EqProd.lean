import MonoidProduct.Aperiodic.Decomposition
import QuantumQueryComplexity.DecisionTree
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The recursive equality-test interface

The AGS induction (Section `sec:ags` of the paper) proves one statement,

  "testing `orderedProd x = m` on a word of length `n` costs at most `Q n`",

and consumes it on **windows** of a longer word.  So the interface has to be
uniform in the length: an assertion only at the ambient length `N` would give a
window of length `ℓ` the cost `Q N` instead of the `Q ℓ` that the induction
needs.

Everything here is bookkeeping for that.  `winProd letter x lo hi` is the
product of the letters of `x` in `[lo, hi)`, `eqProd letter m` is the target
test, and `hasDual_winEq` says that a dual for the test *on a word of the
window's length* is a dual for the window test on the long word, at unchanged
cost — one application of `HasDual.pullback`, whose whole point is that an
injective inclusion of coordinates costs nothing.

`agsLog` is the single logarithmic budget every search depth and scale count is
charged to.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## Shifting an interval product to the front -/

section
variable {M : Type} [Monoid M]

/-- The product of `[lo, lo+len)` in `y` is the product of `[0, len)` in any
word `w` that reproduces those letters.  Note the two words may have different
lengths — that is exactly what reading a window of a long word needs. -/
lemma rangeProd_of_shift {n m : ℕ} (y : Fin n → M) (w : Fin m → M) (lo len : ℕ)
    (h : ∀ k, k < len → padAt y (lo + k) = padAt w k) :
    rangeProd y lo (lo + len) = rangeProd w 0 len := by
  induction len with
  | zero => simp
  | succ len ih =>
      rw [show lo + (len + 1) = lo + len + 1 from by ring,
        rangeProd_succ_right y (by omega),
        rangeProd_succ_right w (Nat.zero_le len),
        ih fun k hk => h k (by omega), h len (by omega)]

end

/-! ## Words, windows and the target test -/

section
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- The monoid value of a word, read through an interpretation of letters. -/
def wordProd (letter : σ → M) {n : ℕ} (x : Fin n → σ) : M :=
  orderedProd fun i => letter (x i)

/-- The product of the letters of `x` in the half-open window `[lo, hi)`. -/
def winProd (letter : σ → M) {n : ℕ} (x : Fin n → σ) (lo hi : ℕ) : M :=
  rangeProd (fun i => letter (x i)) lo hi

/-- **The target test.**  This is the function the whole AGS induction bounds. -/
def eqProd (letter : σ → M) (m : M) {n : ℕ} (x : Fin n → σ) : Bool :=
  decide (wordProd letter x = m)

@[simp] lemma eqProd_eq_true {letter : σ → M} {m : M} {n : ℕ} {x : Fin n → σ} :
    eqProd letter m x = true ↔ wordProd letter x = m := by simp [eqProd]

lemma wordProd_eq_winProd (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    wordProd letter x = winProd letter x 0 n :=
  orderedProd_eq_rangeProd _

/-- The inclusion of a window into the ambient word. -/
def winEmb {n : ℕ} (lo len : ℕ) (h : lo + len ≤ n) (j : Fin len) : Fin n :=
  ⟨lo + j, by have := j.isLt; omega⟩

lemma winEmb_injective {n lo len : ℕ} (h : lo + len ≤ n) :
    Function.Injective (winEmb (n := n) lo len h) := by
  intro j k hjk
  have : lo + (j : ℕ) = lo + (k : ℕ) := congrArg Fin.val hjk
  exact Fin.ext (by omega)

/-- **Reading a window of a long word is reading a short word.** -/
lemma wordProd_winEmb (letter : σ → M) {n : ℕ} (x : Fin n → σ) {lo len : ℕ}
    (h : lo + len ≤ n) :
    wordProd letter (fun j => x (winEmb lo len h j))
      = winProd letter x lo (lo + len) := by
  rw [wordProd, orderedProd_eq_rangeProd, winProd]
  refine (rangeProd_of_shift (fun i => letter (x i))
    (fun j : Fin len => letter (x (winEmb lo len h j))) lo len ?_).symm
  intro k hk
  rw [padAt_of_lt _ (by omega : lo + k < n), padAt_of_lt _ hk]
  rfl

/-- A *sub*-window of a window, in the coordinates of the short word.  This is
`rangeProd_of_shift` with an offset, and it is what identifies the searches run
inside a window with the searches of `MonoidProduct/Aperiodic/Prefix.lean` and
`Suffix.lean` run on a word of the window's length. -/
lemma rangeProd_of_shift' {n' m : ℕ} (y : Fin n' → M) (w : Fin m → M)
    (lo s d : ℕ) (h : ∀ k, k < s + d → padAt y (lo + k) = padAt w k) :
    rangeProd y (lo + s) (lo + (s + d)) = rangeProd w s (s + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show lo + (s + (d + 1)) = lo + (s + d) + 1 from by ring,
        rangeProd_succ_right y (show lo + s ≤ lo + (s + d) by omega),
        show s + (d + 1) = s + d + 1 from by ring,
        rangeProd_succ_right w (show s ≤ s + d by omega),
        ih fun k hk => h k (by omega), h (s + d) (by omega)]

/-- **Reading a sub-window of a window.** -/
lemma winProd_winEmb (letter : σ → M) {n : ℕ} (x : Fin n → σ) {lo len : ℕ}
    (h : lo + len ≤ n) {s e : ℕ} (hse : s ≤ e) (hel : e ≤ len) :
    winProd letter (fun t => x (winEmb lo len h t)) s e
      = winProd letter x (lo + s) (lo + e) := by
  simp only [winProd]
  rw [show e = s + (e - s) from by omega]
  refine (rangeProd_of_shift' (fun i => letter (x i))
    (fun t : Fin len => letter (x (winEmb lo len h t))) lo s (e - s)
    fun k hk => ?_).symm
  rw [padAt_of_lt _ (show lo + k < n by omega),
    padAt_of_lt _ (show k < len by omega)]
  rfl

/-- **The window test costs what the test on a word of the window's length
costs.**  `HasDual.pullback` is doing all the work: freezing the coordinates
outside an injective window changes nothing. -/
theorem hasDual_winEq (letter : σ → M) (s : M) {n lo len : ℕ}
    (h : lo + len ≤ n) {c : ℝ}
    (hrec : HasDual (eqProd (n := len) letter s) c) :
    HasDual (fun x : Fin n → σ => decide (winProd letter x lo (lo + len) = s))
      c := by
  refine (hrec.pullback (winEmb_injective h)).ofEq fun x => ?_
  rw [pullbackFun_apply]
  simp only [eqProd, wordProd_winEmb letter x h]

/-- The same, stated with an explicit right endpoint. -/
theorem hasDual_winEq' (letter : σ → M) (s : M) {n lo hi : ℕ} (h : hi ≤ n)
    (hlo : lo ≤ hi) {c : ℝ}
    (hrec : HasDual (eqProd (n := hi - lo) letter s) c) :
    HasDual (fun x : Fin n → σ => decide (winProd letter x lo hi = s)) c := by
  have hsum : lo + (hi - lo) = hi := by omega
  have := hasDual_winEq letter s (n := n) (lo := lo) (len := hi - lo)
    (by omega) hrec
  rwa [hsum] at this

/-! ### Any function of a window's product

The family of equality tests pins the value down, so `HasDual.combine'` — whose
outer function is arbitrary — turns "I can test a window's product" into "I can
compute any function of it", at `2 |M|` times the cost of one test. -/

/-- Recovering a value from its family of equality tests. -/
noncomputable def valueOf (f : M → Bool) : M :=
  if h : ∃ s : M, f s = true then h.choose else 1

lemma valueOf_spec {f : M → Bool} {v : M} (h : ∀ s, f s = true ↔ s = v) :
    valueOf f = v := by
  have hex : ∃ s : M, f s = true := ⟨v, (h v).2 rfl⟩
  rw [valueOf, dif_pos hex]
  exact (h _).1 hex.choose_spec

/-- **Any function of a window's product.** -/
theorem hasDual_ofWinProd {O' : Type} [DecidableEq O'] (letter : σ → M)
    (F : M → O') {n lo hi : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s : M,
      HasDual (fun x : Fin n → σ => decide (winProd letter x lo hi = s)) Q) :
    HasDual (fun x : Fin n → σ => F (winProd letter x lo hi))
      (2 * (Fintype.card M : ℝ) * Q) := by
  classical
  have h := HasDual.combine' (ι := Fin n) (σ := σ) (Pi := M) (V := Bool)
    (O' := O') (fun f => F (valueOf f))
    (g := fun s x => decide (winProd letter x lo hi = s))
    (c := fun _ => Q) (fun _ => hQ) hrec
  refine (h.ofEq fun x => ?_).mono (le_of_eq ?_)
  · exact congrArg F (valueOf_spec fun s => by simp [eq_comm])
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring

/-! ### Base cases -/

/-- The empty word has product `1`, so its test is constant. -/
lemma hasDual_eqProd_zero (letter : σ → M) (m : M) :
    HasDual (eqProd (n := 0) letter m) 0 :=
  hasDual_const fun x y => by
    simp only [eqProd, wordProd, orderedProd_eq_rangeProd, rangeProd_self]

lemma wordProd_one (letter : σ → M) (x : Fin 1 → σ) :
    wordProd letter x = letter (x 0) := by
  have h : rangeProd (fun i => letter (x i)) 0 1
      = padAt (fun i => letter (x i)) 0 := rangeProd_eq_padAt _ 0
  rw [wordProd, orderedProd_eq_rangeProd, h, padAt_of_lt _ Nat.one_pos]
  rfl

/-- A one-letter word is a function of one coordinate. -/
lemma hasDual_eqProd_one (letter : σ → M) (m : M) :
    HasDual (eqProd (n := 1) letter m) 2 := by
  refine (hasDual_ofCoord (ι := Fin 1) (σ := σ) 0
    (fun a => decide (letter a = m))).ofEq fun x => ?_
  rw [eqProd, wordProd_one]

/-- **Any function of a window's product**, priced directly in the recursive
equality tests on words of the window's length. -/
theorem hasDual_winFn {O' : Type} [DecidableEq O'] (letter : σ → M) (F : M → O')
    {n lo hi : ℕ} (hhi : hi ≤ n) (hlo : lo ≤ hi) {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s : M, HasDual (eqProd (n := hi - lo) letter s) Q) :
    HasDual (fun x : Fin n → σ => F (winProd letter x lo hi))
      (2 * (Fintype.card M : ℝ) * Q) :=
  hasDual_ofWinProd letter F hQ fun s => hasDual_winEq' letter s hhi hlo (hrec s)

/-- A `Bool`-valued `Finset.sup` is the disjunction. -/
lemma sup_bool_eq_true {α : Type} [DecidableEq α] (S : Finset α) (f : α → Bool) :
    S.sup f = true ↔ ∃ i ∈ S, f i = true := by
  refine Finset.induction_on S (by simp) fun a t ha ih => ?_
  simp [Finset.sup_insert, ih]

/-- **Membership of a window's product in a finite set.**

Priced by a square-root search over that set *only*.  Unlike `hasDual_winFn`
this never runs an equality test at a value outside `S`, which is exactly what
keeps the AGS recursion from having to test its own target: the sets it is used
at, `rightAbove r` and `leftAbove r`, sit at or above `r` in the `J`-order and
so strictly below the target. -/
theorem hasDual_winMem (letter : σ → M) (S : Finset M) {n lo hi : ℕ}
    (hhi : hi ≤ n) (hlo : lo ≤ hi) {Q : ℝ} (hQ : 0 ≤ Q)
    (hrec : ∀ s ∈ S, HasDual (eqProd (n := hi - lo) letter s) Q) :
    HasDual (fun x : Fin n → σ => decide (winProd letter x lo hi ∈ S))
      (Q * (24 * Real.sqrt ((S.card : ℝ) + 1))) := by
  classical
  refine (HasDual.finsetSup (ι := Fin n) (σ := σ) (A := Bool) S
    (g := fun s x => decide (winProd letter x lo hi = s)) hQ
    (fun s hs => hasDual_winEq' letter s hhi hlo (hrec s hs))).ofEq fun x => ?_
  rw [Bool.eq_iff_iff, sup_bool_eq_true]
  simp [eq_comm]

/-- **Reading one letter costs `2`**, whatever is asked of it.  Positions past
the end of the word read `1`, so the test is constant there. -/
theorem hasDual_letterTest (letter : σ → M) (a : M) {n : ℕ} (j : ℕ) :
    HasDual (fun x : Fin n → σ =>
      decide (padAt (fun t => letter (x t)) j = a)) 2 := by
  by_cases hjn : j < n
  · refine (hasDual_ofCoord (ι := Fin n) (σ := σ) ⟨j, hjn⟩
      (fun c => decide (letter c = a))).ofEq fun x => ?_
    rw [padAt_of_lt _ hjn]
  · refine ((hasDual_const (f := fun _ : Fin n → σ => decide ((1 : M) = a))
      (fun _ _ => rfl)).mono (by norm_num)).ofEq fun x => ?_
    rw [padAt_of_le _ (by omega)]

/-! ## The logarithmic budget

One quantity, `⌈log₂ (2 + N |M|)⌉`, absorbs every binary-search depth, scale
count and degenerate case in the development. -/

/-- The single logarithmic budget of the AGS induction. -/
def agsLog (N : ℕ) (M : Type) [Fintype M] : ℕ := Nat.clog 2 (2 + N * Fintype.card M)

lemma agsLog_pos (N : ℕ) : 0 < agsLog N M := by
  refine Nat.clog_pos (by norm_num) ?_
  omega

lemma clog_le_agsLog [Nonempty M] {n N : ℕ} (h : n ≤ N) :
    Nat.clog 2 n ≤ agsLog N M := by
  refine Nat.clog_mono_right _ ?_
  have hM : 1 ≤ Fintype.card M := Fintype.card_pos
  calc n ≤ N := h
    _ = N * 1 := (mul_one N).symm
    _ ≤ N * Fintype.card M := Nat.mul_le_mul_left N hM
    _ ≤ 2 + N * Fintype.card M := by omega

end

/-! ## Word products through a homomorphism

These are pure monoid facts, kept here rather than in `Quantum/Division.lean`
because the radical tower needs them on the classical side, where the quantum
layer is not imported. -/

section MapWordProd

variable {H H' : Type} [Monoid H] [Monoid H']

/-- A homomorphism commutes with the padding letter. -/
lemma map_padAt (φ : H →* H') {n : ℕ} (x : Fin n → H) (i : ℕ) :
    φ (padAt x i) = padAt (fun j => φ (x j)) i := by
  by_cases h : i < n
  · rw [padAt_of_lt _ h, padAt_of_lt _ h]
  · rw [padAt_of_le _ (by omega), padAt_of_le _ (by omega), map_one]

lemma map_rangeProd (φ : H →* H') {n : ℕ} (x : Fin n → H) (m : ℕ) :
    φ (rangeProd x 0 m) = rangeProd (fun j => φ (x j)) 0 m := by
  induction m with
  | zero => rw [rangeProd_self, rangeProd_self, map_one]
  | succ m ih =>
      rw [rangeProd_succ_right _ (Nat.zero_le m),
        rangeProd_succ_right _ (Nat.zero_le m), map_mul, ih, map_padAt]

/-- **A homomorphism commutes with the ordered product.** -/
theorem map_orderedProd (φ : H →* H') {n : ℕ} (x : Fin n → H) :
    φ (orderedProd x) = orderedProd (fun j => φ (x j)) := by
  rw [orderedProd_eq_rangeProd, orderedProd_eq_rangeProd, map_rangeProd]

/-- **A homomorphism commutes with the word product** — reading the letters
through `φ` first gives the `φ`-image of the product. -/
lemma map_wordProd {σ : Type} [Fintype σ] [DecidableEq σ] (φ : H →* H')
    (letter : σ → H) {n : ℕ} (x : Fin n → σ) :
    φ (wordProd letter x) = wordProd (fun a => φ (letter a)) x := by
  rw [wordProd, wordProd, map_orderedProd]

end MapWordProd

end MonoidProduct
