import MonoidProduct.Tropical.Breadth
import MonoidProduct.Width.StableOrder
import MonoidProduct.Quantum.OrderedApplications
import MonoidProduct.Quantum.OrderedLogApplications
import MonoidProduct.Stock.Strict
import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Group.WithOne.Basic
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `U_k(𝕋)` as a monoid: `cor:unitriangular-beta` and the tropical encodings

Section `sec:tropical` of the paper.

* `UTrop k` bundles the unitriangular max-plus matrices of `Tropical/Defs.lean`
  (`IsUtri`, product `tmul`, identity `tone`) as a `Monoid`, with the entrywise
  order; `utrop_isStableOrder` is the paper's "entrywise order is stable, and
  this identity is the minimum element".
* `UTrop.wordProd_val` / `UTrop.subwordProd_val` identify the library's
  `wordProd` / `subwordProd` with the tropical `linProd` / masked `linProd`, so
  the transition-support core of `Tropical/Breadth.lean`
  (`exists_core_linProd`, i.e. `lem:path` plus the choice of maximising paths)
  becomes the breadth bound `utrop_isBreadthBound`:
  `β ≤ V_k = ∑_{s<t} (t − s) = C(k+1, 3)` (`utropV_eq_choose`).
* `utrop_closure_finite`: a finite alphabet generates a finite submonoid (every
  strict entry of a product is `⊥` or a sum of at most `t − s ≤ k − 1` letter
  entries).
* `utrop_qQuery_third_le_five_halves`: the linear-exponent ordered product
  bound at `b = V_k`, with logarithmic power `5V_k/2`.
* `utrop_qQuery_third_le_paper`: the logarithmic-exponent ordered product
  bound at `b = V_k`, matching `cor:unitriangular-beta`; `utrop_qQuery_eq_zero`
  handles `k ≤ 1`.
* Encodings: the strict stock summary embeds at `k = 3` as a monoid hom
  (`utropStockHom`, `utropStockHom_injective`, `utropStock_mul`); and the
  signed chain of `t + 1` states computes
  `max_{i₁<⋯<i_t} ∑ⱼ εⱼ x_{iⱼ}` (`utropSignedChain_wordProd`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {k : ℕ}

/-! ## The monoid -/

/-- **`U_k(𝕋)`**, bundled: unitriangular `k × k` max-plus matrices. -/
def UTrop (k : ℕ) : Type := {M : TMat k // IsUtri M}

namespace UTrop

/-- The underlying matrix. -/
def val (M : UTrop k) : TMat k := Subtype.val M

lemma isUtri (M : UTrop k) : IsUtri M.val := Subtype.property M

@[ext] lemma ext {M N : UTrop k} (h : M.val = N.val) : M = N := Subtype.ext h

/-- Build an element from a unitriangular matrix. -/
def mk (M : TMat k) (h : IsUtri M) : UTrop k := Subtype.mk M h

@[simp] lemma val_mk (M : TMat k) (h : IsUtri M) : (mk M h).val = M := rfl

noncomputable instance : Monoid (UTrop k) where
  mul M N := Subtype.mk (tmul (Subtype.val M) (Subtype.val N))
    ((Subtype.property M).tmul (Subtype.property N))
  one := Subtype.mk (tone k) isUtri_tone
  mul_assoc M N P := Subtype.ext (tmul_assoc _ _ _)
  one_mul M := Subtype.ext (tone_tmul _)
  mul_one M := Subtype.ext (tmul_tone _)

@[simp] lemma val_mul (M N : UTrop k) : (M * N).val = tmul M.val N.val := rfl

@[simp] lemma val_one : (1 : UTrop k).val = tone k := rfl

/-- The entrywise order. -/
instance : PartialOrder (UTrop k) := Subtype.partialOrder _

lemma le_iff {M N : UTrop k} : M ≤ N ↔ M.val ≤ N.val := Iff.rfl

noncomputable instance : DecidableEq (UTrop k) := Classical.decEq _

end UTrop

/-- **The entrywise order on `U_k(𝕋)` is stable with least identity.** -/
theorem utrop_isStableOrder : IsStableOrder (UTrop k) where
  mul_le_mul_left _ h := UTrop.le_iff.2 (tmul_mono le_rfl (UTrop.le_iff.1 h))
  mul_le_mul_right _ h := UTrop.le_iff.2 (tmul_mono (UTrop.le_iff.1 h) le_rfl)
  one_le a := UTrop.le_iff.2 (tone_le_of_isUtri a.isUtri)

/-! ## Library products are tropical products -/

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The ordered product of a list of letters, read as a matrix. -/
lemma UTrop.val_prod_ofFn {τ : Type} [Fintype τ] [DecidableEq τ] (L : τ → TMat k) :
    ∀ {n : ℕ} (F : Fin n → UTrop k) (x : Fin n → τ), (∀ i, (F i).val = L (x i)) →
      (List.ofFn F).prod.val = linProd L n x
  | 0, _, _, _ => rfl
  | m + 1, F, x, hFx => by
      rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton, UTrop.val_mul,
        UTrop.val_prod_ofFn L (fun i => F i.castSucc) (fun i => x i.castSucc)
          (fun i => hFx _), linProd_succ, hFx]

/-- `wordProd` in `U_k(𝕋)` is the tropical ordered product `linProd`. -/
theorem UTrop.wordProd_val (letter : σ → UTrop k) {n : ℕ} (x : Fin n → σ) :
    (wordProd letter x).val = linProd (fun a => (letter a).val) n x := by
  rw [wordProd, orderedProd_eq_prod_ofFn]
  exact UTrop.val_prod_ofFn _ _ x fun _ => rfl

/-- The masked subword product in `U_k(𝕋)` is the tropical product of the masked
word (`mask`, letters off the core replaced by the identity `none`). -/
theorem UTrop.subwordProd_val (letter : σ → UTrop k) {n : ℕ} (x : Fin n → σ)
    (u : Finset (Fin n)) :
    (subwordProd letter x u).val
      = linProd (optLetter fun a => (letter a).val) n (mask u x) := by
  rw [subwordProd]
  exact UTrop.val_prod_ofFn _ _ (mask u x) fun i => by
    by_cases h : i ∈ u <;> simp [mask, h, optLetter]

/-! ## The breadth bound `V_k = C(k+1, 3)` -/

/-- `2·C(m, 2) = m(m − 1)`. -/
lemma utrop_two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Nat.choose_succ_succ', mul_add, ih, Nat.choose_one_right]
      cases m with
      | zero => rfl
      | succ m => simp only [Nat.add_sub_cancel]; ring

/-- `6·C(k+1, 3) = (k − 1)·k·(k + 1)`. -/
lemma utrop_six_mul_choose_three (k : ℕ) : 6 * (k + 1).choose 3 = (k - 1) * k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.choose_succ_succ', mul_add, ih,
        show 6 * (k + 1).choose 2 = 3 * (2 * (k + 1).choose 2) by ring,
        utrop_two_mul_choose_two]
      cases k with
      | zero => rfl
      | succ k => simp only [Nat.add_sub_cancel]; ring

/-- **`V_k = ∑_{s<t} (t − s) = C(k+1, 3)`.** -/
theorem utropV_eq_choose (k : ℕ) : volume (strictPairs k) = (k + 1).choose 3 := by
  have h1 := six_mul_volume_strictPairs k
  have h2 := utrop_six_mul_choose_three k
  omega

/-- **`cor:unitriangular-beta`, breadth clause**: every word over an alphabet in
`U_k(𝕋)` has a core of at most `V_k = ∑_{s<t} (t − s)` positions. -/
theorem utrop_isBreadthBound (letter : σ → UTrop k) :
    IsBreadthBound letter (volume (strictPairs k)) := fun n x => by
  obtain ⟨C, hC, hprod⟩ :=
    exists_core_linProd (letter := fun a => (letter a).val) (fun a => (letter a).isUtri) n x
  exact ⟨C, hC, UTrop.ext (by rw [UTrop.subwordProd_val, UTrop.wordProd_val, hprod])⟩

/-- The breadth bound as a binomial coefficient: `β ≤ C(k+1, 3)`. -/
theorem utrop_isBreadthBound_choose (letter : σ → UTrop k) :
    IsBreadthBound letter ((k + 1).choose 3) :=
  utropV_eq_choose k ▸ utrop_isBreadthBound letter

/-- `β_G(H) ≤ C(k+1, 3)` for the product breadth `breadth`. -/
theorem utrop_breadth_le (letter : σ → UTrop k) : breadth letter ≤ (k + 1).choose 3 :=
  breadth_le (utrop_isBreadthBound_choose letter)

/-- `V_k = 0` for `k ≤ 1`. -/
lemma utropV_eq_zero {k : ℕ} (hk : k ≤ 1) : volume (strictPairs k) = 0 := by
  have h := six_mul_volume_strictPairs k
  have : (k - 1) * k * (k + 1) = 0 := by
    rw [show k - 1 = 0 by omega, Nat.zero_mul, Nat.zero_mul]
  omega

/-! ## A finite alphabet generates a finite monoid -/

/-- `⊥` together with the sums of at most `d` entries of letters. -/
def utropEntrySums (letter : σ → UTrop k) (d : ℕ) : Set Trop :=
  insert ⊥ ((fun l : List (σ × Fin k × Fin k) =>
    (l.map fun e => (letter e.1).val e.2.1 e.2.2).sum) '' {l | l.length ≤ d})

lemma utropEntrySums_finite (letter : σ → UTrop k) (d : ℕ) :
    (utropEntrySums letter d).Finite :=
  ((List.finite_length_le _ d).image _).insert ⊥

lemma utropEntrySums_mono (letter : σ → UTrop k) {d d' : ℕ} (h : d ≤ d') :
    utropEntrySums letter d ⊆ utropEntrySums letter d' := by
  rintro a (rfl | ⟨l, hl, rfl⟩)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨l, le_trans hl h, rfl⟩

lemma utropEntrySums_add (letter : σ → UTrop k) {d d' : ℕ} {a b : Trop}
    (ha : a ∈ utropEntrySums letter d) (hb : b ∈ utropEntrySums letter d') :
    a + b ∈ utropEntrySums letter (d + d') := by
  rcases ha with rfl | ⟨l, hl, rfl⟩
  · rw [WithBot.bot_add]; exact Set.mem_insert _ _
  rcases hb with rfl | ⟨l', hl', rfl⟩
  · rw [WithBot.add_bot]; exact Set.mem_insert _ _
  refine Set.mem_insert_of_mem _ ⟨l ++ l', ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, List.length_append] at hl hl' ⊢
    omega
  · simp only [List.map_append, List.sum_append]

lemma zero_mem_utropEntrySums (letter : σ → UTrop k) (d : ℕ) :
    (0 : Trop) ∈ utropEntrySums letter d :=
  Set.mem_insert_of_mem _ ⟨[], by simp, by simp⟩

lemma bot_mem_utropEntrySums (letter : σ → UTrop k) (d : ℕ) :
    (⊥ : Trop) ∈ utropEntrySums letter d :=
  Set.mem_insert _ _

/-- The graded entry invariant: the `(s, t)` entry is a sum of at most `t − s`
letter entries (or `⊥`). -/
def UTrop.EntryInv (letter : σ → UTrop k) (M : UTrop k) : Prop :=
  ∀ s t : Fin k, s ≤ t → M.val s t ∈ utropEntrySums letter ((t : ℕ) - s)

lemma UTrop.entryInv_mul (letter : σ → UTrop k) {P Q : UTrop k}
    (hP : UTrop.EntryInv letter P) (hQ : UTrop.EntryInv letter Q) :
    UTrop.EntryInv letter (P * Q) := by
  intro s t hst
  rw [UTrop.val_mul, tmul]
  refine (LinearOrder.supClosed _).finsetSup_mem ⟨s, Finset.mem_univ _⟩ fun v _ => ?_
  rcases lt_or_ge v s with hvs | hsv
  · rw [P.isUtri.below s v hvs, WithBot.bot_add]
    exact bot_mem_utropEntrySums _ _
  rcases lt_or_ge t v with htv | hvt
  · rw [Q.isUtri.below v t htv, WithBot.add_bot]
    exact bot_mem_utropEntrySums _ _
  have h := utropEntrySums_add letter (hP s v hsv) (hQ v t hvt)
  have e : (v : ℕ) - s + ((t : ℕ) - v) = (t : ℕ) - s := by
    have := Fin.le_def.1 hsv
    have := Fin.le_def.1 hvt
    omega
  rwa [e] at h

/-- **A finite alphabet generates a finite submonoid of `U_k(𝕋)`**
(`cor:unitriangular-beta`): the entries of every product lie in the finite set of
sums of at most `k − 1` letter entries, together with `−∞`. -/
theorem utrop_closure_finite (letter : σ → UTrop k) :
    (Submonoid.closure (Set.range letter) : Set (UTrop k)).Finite := by
  classical
  have hinv : ∀ M ∈ Submonoid.closure (Set.range letter), UTrop.EntryInv letter M := by
    intro M hM
    induction hM using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        intro s t hst
        rcases hst.lt_or_eq with hlt | rfl
        · refine utropEntrySums_mono letter (d := 1) ?_
            (Set.mem_insert_of_mem _ ⟨[(a, s, t)], by simp, by simp⟩)
          have := Fin.lt_def.1 hlt
          omega
        · rw [(letter a).isUtri.diag]
          exact zero_mem_utropEntrySums _ _
    | one =>
        intro s t _
        by_cases h : s = t
        · subst h; simp only [UTrop.val_one, tone, if_true]
          exact zero_mem_utropEntrySums _ _
        · simp only [UTrop.val_one, tone, if_neg h]
          exact bot_mem_utropEntrySums _ _
    | mul x y _ _ hx hy => exact UTrop.entryInv_mul letter hx hy
  let F := utropEntrySums letter (k - 1)
  have hF : F.Finite := utropEntrySums_finite letter (k - 1)
  have hS : (Set.univ.pi fun _ : Fin k => Set.univ.pi fun _ : Fin k => F).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hF
  refine (hS.preimage (f := UTrop.val) fun M _ N _ h => UTrop.ext h).subset ?_
  intro M hM
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  intro s t
  rcases lt_or_ge t s with hts | hst
  · rw [M.isUtri.below s t hts]
    exact bot_mem_utropEntrySums _ _
  · refine utropEntrySums_mono letter ?_ (hinv M hM s t hst)
    have := t.isLt
    omega

/-! ## Query bounds from the ordered product theorems -/

/-- **The linear-exponent bound**, with `V_k = C(k+1, 3)` and
`L_n = ⌈log₂(n+1)⌉`:
`Q_{1/3}(Prod) ≤ min{n, (2^27·V_k)^{V_k}·√n·L_n^{5V_k/2}}`.
The logarithmic factor is written `orderedLogFactor L_n ^ V_k`. -/
theorem utrop_qQuery_third_le_five_halves (letter : σ → UTrop k) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) ((2 ^ 27 * (((k + 1).choose 3 : ℕ) : ℝ)) ^ (k + 1).choose 3
          * Real.sqrt n * orderedLogFactor (logLen n) ^ (k + 1).choose 3) :=
  ordered_qQuery_third_le_five_halves letter utrop_isStableOrder
    (utrop_isBreadthBound_choose letter) n

/-- **`cor:unitriangular-beta`, the logarithmic-exponent bound**, with
`V_k = C(k+1, 3)` and `C = 2^17`:
`Q_{1/3}(Prod) ≤ min{n, √(n+1)·(C(V_k+2)·log(n+2))^{C·log(V_k+2)}}`.
The logarithms in `quasipolyBound` are natural. -/
theorem utrop_qQuery_third_le_paper (letter : σ → UTrop k) (n : ℕ) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (quasipolyBound ((k + 1).choose 3) n) :=
  ordered_qQuery_third_le_quasipoly letter utrop_isStableOrder
    (utrop_isBreadthBound_choose letter) n

/-- **The case `k ≤ 1` is query-free**: `V_k = 0`, so the product is constant. -/
theorem utrop_qQuery_eq_zero (hk : k ≤ 1) (letter : σ → UTrop k) (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) : qQuery (fun x : Fin n → σ => wordProd letter x) ε = 0 :=
  qQuery_wordProd_zero_breadth letter
    (utropV_eq_zero hk ▸ utrop_isBreadthBound letter) n hε

/-! ## Encoding (i): the strict stock summary at `k = 3` -/

/-- `WithBot ℤ ↪ WithBot ℝ`, for the profit coordinate. -/
def utropStockTrop (c : WithBot ℤ) : Trop := WithBot.map (fun z : ℤ => (z : ℝ)) c

@[simp] lemma utropStockTrop_bot : utropStockTrop ⊥ = ⊥ := rfl

@[simp] lemma utropStockTrop_coe (z : ℤ) :
    utropStockTrop (z : WithBot ℤ) = ((z : ℝ) : Trop) :=
  rfl

lemma utropStockTrop_max (a b : WithBot ℤ) :
    utropStockTrop (max a b) = max (utropStockTrop a) (utropStockTrop b) := by
  induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe
  · rfl
  · simp
  · simp
  · rw [← WithBot.coe_max, utropStockTrop_coe, utropStockTrop_coe, utropStockTrop_coe,
      ← WithBot.coe_max, Int.cast_max]

/-- The embedding `(a, b, c) ↦ [[0, −a, c], [−∞, 0, b], [−∞, −∞, 0]]`. -/
def utropStockMat (s : StrictStock.SSumm) : TMat 3 :=
  ![![0, ((-(s.lo : ℝ) : ℝ) : Trop), utropStockTrop s.profit],
    ![⊥, 0, ((s.hi : ℝ) : Trop)],
    ![⊥, ⊥, 0]]

lemma isUtri_utropStockMat (s : StrictStock.SSumm) : IsUtri (utropStockMat s) where
  diag i := by fin_cases i <;> rfl
  below i j h := by
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- The stock summary as an element of `U_3(𝕋)`. -/
def utropStock (s : StrictStock.SSumm) : UTrop 3 :=
  UTrop.mk (utropStockMat s) (isUtri_utropStockMat s)

lemma utrop_sup_fin_three (f : Fin 3 → Trop) : Finset.univ.sup f = f 0 ⊔ f 1 ⊔ f 2 := by
  have h : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [h, Finset.sup_insert, Finset.sup_insert, Finset.sup_singleton, sup_assoc]

/-- **Multiplication reproduces the stock combination rule**:
`(a,b,c)·(d,e,f) = (min a d, max b e, max(c, f, e − a))`. -/
theorem utropStock_mul (s t : StrictStock.SSumm) :
    utropStock (s * t) = utropStock s * utropStock t := by
  refine UTrop.ext (tmat_ext_of_isUtri (isUtri_utropStockMat _)
    ((isUtri_utropStockMat s).tmul (isUtri_utropStockMat t)) fun i j hij => ?_)
  simp only [utropStock, UTrop.val_mul, UTrop.val_mk, tmul, utrop_sup_fin_three]
  fin_cases i <;> fin_cases j <;> try exact absurd hij (by decide)
  · simp only [utropStockMat, StrictStock.mul_lo]
    simp
    rw [← WithBot.coe_max, max_neg_neg, min_comm]
  · simp only [utropStockMat, StrictStock.mul_profit, StrictStock.mul_hi, StrictStock.mul_lo]
    simp
    rw [utropStockTrop_max, utropStockTrop_max, utropStockTrop_coe,
      max_comm (utropStockTrop s.profit)]
    congr 2
    rw [← WithBot.coe_add]
    congr 1
    push_cast
    ring
  · simp only [utropStockMat]
    simp [max_comm]

/-- The embedding as a multiplicative map of nonempty summaries. -/
def utropStockMulHom : StrictStock.SSumm →ₙ* UTrop 3 where
  toFun := utropStock
  map_mul' := utropStock_mul

/-- **The strict stock monoid embeds in `U_3(𝕋)`**: the empty summary goes to the
identity. -/
noncomputable def utropStockHom : StrictStock.Summaries →* UTrop 3 :=
  WithOne.lift utropStockMulHom

@[simp] lemma utropStockHom_coe (s : StrictStock.SSumm) :
    utropStockHom (s : StrictStock.Summaries) = utropStock s :=
  WithOne.lift_coe _ _

lemma utropStockHom_one : utropStockHom 1 = 1 := map_one _

/-- The embedding is injective: `−a`, `b` and `c` are read off the three strict
entries, and the identity has `−∞` where every summary has `b`. -/
theorem utropStockHom_injective : Function.Injective utropStockHom := by
  have h12 : ∀ s : StrictStock.SSumm, (utropStock s).val 1 2 = ((s.hi : ℝ) : Trop) :=
    fun _ => rfl
  have hne : ∀ s : StrictStock.SSumm, utropStock s ≠ 1 := fun s h => by
    have := congrArg (fun M : UTrop 3 => M.val 1 2) h
    simp only [h12, UTrop.val_one, tone] at this
    exact WithBot.coe_ne_bot this
  have hsplit : ∀ z : StrictStock.Summaries, z = 1 ∨ ∃ s : StrictStock.SSumm, z = ↑s := by
    intro z
    cases z with
    | none => exact Or.inl rfl
    | some s => exact Or.inr ⟨s, rfl⟩
  intro x y h
  rcases hsplit x with rfl | ⟨s, rfl⟩ <;> rcases hsplit y with rfl | ⟨t, rfl⟩
  · rfl
  · rw [utropStockHom_one, utropStockHom_coe] at h
    exact absurd h.symm (hne _)
  · rw [utropStockHom_one, utropStockHom_coe] at h
    exact absurd h (hne _)
  · rw [utropStockHom_coe, utropStockHom_coe] at h
    have e01 := congrArg (fun M : UTrop 3 => M.val 0 1) h
    have e12 := congrArg (fun M : UTrop 3 => M.val 1 2) h
    have e02 := congrArg (fun M : UTrop 3 => M.val 0 2) h
    simp only [utropStock, UTrop.val_mk, utropStockMat] at e01 e12 e02
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at e01 e12 e02
    have hlo : s.lo = t.lo := by exact_mod_cast neg_inj.1 (WithBot.coe_injective e01)
    have hhi : s.hi = t.hi := by exact_mod_cast WithBot.coe_injective e12
    have hpr : s.profit = t.profit :=
      WithBot.map_injective (f := fun z : ℤ => (z : ℝ)) Int.cast_injective e02
    exact congrArg _ (StrictStock.SSumm.ext hlo hhi hpr)

/-- The image of a single price `p`: `[[0, −p, −∞], [−∞, 0, p], [−∞, −∞, 0]]`. -/
lemma utropStockHom_price (p : ℤ) :
    (utropStockHom (StrictStock.price p : StrictStock.Summaries)).val
      = ![![0, ((-(p : ℝ) : ℝ) : Trop), ⊥], ![⊥, 0, ((p : ℝ) : Trop)],
          ![⊥, ⊥, 0]] := by
  rw [utropStockHom_coe]
  rfl

/-- **The stock product is computed in `U_3(𝕋)`**: the embedding carries the
stock word product to the tropical word product of the embedded letters. -/
theorem utropStockHom_wordProd {τ : Type} (letter : τ → StrictStock.Summaries) {n : ℕ}
    (x : Fin n → τ) :
    utropStockHom (wordProd letter x) = wordProd (fun a => utropStockHom (letter a)) x := by
  rw [wordProd, wordProd, orderedProd_eq_prod_ofFn, orderedProd_eq_prod_ofFn,
    map_list_prod, List.map_ofFn]
  rfl

/-! ## Encoding (ii): signed chains -/

/-- The chain matrix on `t + 1` states: the only strict transitions are
`j → j + 1`, of weight `c j`. -/
noncomputable def utropChainMat {t : ℕ} (c : Fin t → ℝ) : TMat (t + 1) := fun a b =>
  if a = b then 0
  else if h : (b : ℕ) = a + 1 ∧ (a : ℕ) < t then ((c ⟨a, h.2⟩ : ℝ) : Trop)
  else ⊥

lemma isUtri_utropChainMat {t : ℕ} (c : Fin t → ℝ) : IsUtri (utropChainMat c) where
  diag a := if_pos rfl
  below a b h := by
    have h' := Fin.lt_def.1 h
    rw [utropChainMat, if_neg (fun e => by subst e; omega), dif_neg (by omega)]

/-- The chain letter as an element of `U_{t+1}(𝕋)`. -/
noncomputable def utropChain {t : ℕ} (c : Fin t → ℝ) : UTrop (t + 1) :=
  UTrop.mk (utropChainMat c) (isUtri_utropChainMat c)

/-- **The signed-chain letter** of an input `r ∈ ℝ`: edge `j → j + 1` carries
`εⱼ · r`. -/
noncomputable def utropSignedLetter {t : ℕ} (ε : Fin t → ℝ) (r : ℝ) : UTrop (t + 1) :=
  utropChain fun j => ε j * r

/-- The best value of a chain of `j` transitions at strictly increasing positions,
coefficients `c`. -/
noncomputable def utropChainBest (c : ℕ → ℝ) {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : Trop :=
  (Finset.univ.filter fun f : Fin j → Fin n => StrictMono f).sup
    fun f => ((∑ l : Fin j, c l * x (f l) : ℝ) : Trop)

lemma utrop_finsetSup_add {α : Type*} (S : Finset α) (f : α → Trop) (b : Trop) :
    S.sup f + b = S.sup fun a => f a + b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S _ ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ← ih]
      rcases le_total (f a) (S.sup f) with h | h
      · rw [sup_eq_right.2 h, sup_eq_right.2 (add_le_add h le_rfl)]
      · rw [sup_eq_left.2 h, sup_eq_left.2 (add_le_add h le_rfl)]

lemma utropChainBest_zero (c : ℕ → ℝ) {n : ℕ} (x : Fin n → ℝ) :
    utropChainBest c x 0 = 0 := by
  have h : (Finset.univ.filter fun f : Fin 0 → Fin n => StrictMono f)
      = {fun i => i.elim0} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun _ => funext fun i => i.elim0, fun _ a => a.elim0⟩
  rw [utropChainBest, h, Finset.sup_singleton]
  simp

lemma utropChainBest_empty (c : ℕ → ℝ) (x : Fin 0 → ℝ) (j : ℕ) :
    utropChainBest c x (j + 1) = ⊥ := by
  have h : (Finset.univ.filter fun f : Fin (j + 1) → Fin 0 => StrictMono f) = ∅ := by
    ext f
    exact (f 0).elim0
  rw [utropChainBest, h, Finset.sup_empty]

/-- **The chain recursion**: a chain of `j + 1` transitions in a word of length
`n + 1` either avoids the last position or takes its last transition there. -/
theorem utropChainBest_succ (c : ℕ → ℝ) {n : ℕ} (x : Fin (n + 1) → ℝ) (j : ℕ) :
    utropChainBest c x (j + 1)
      = utropChainBest c (fun i => x i.castSucc) (j + 1)
        ⊔ (utropChainBest c (fun i => x i.castSucc) j
            + ((c j * x (Fin.last n) : ℝ) : Trop)) := by
  rw [utropChainBest, utropChainBest, utropChainBest, utrop_finsetSup_add]
  refine le_antisymm (Finset.sup_le fun f hf => ?_) (sup_le (Finset.sup_le fun f hf => ?_)
    (Finset.sup_le fun g hg => ?_))
  · have hmono : StrictMono f := (Finset.mem_filter.1 hf).2
    by_cases hl : f (Fin.last j) = Fin.last n
    · -- the last transition is at the last position
      have hlt : ∀ l : Fin j, (f l.castSucc : ℕ) < n := by
        intro l
        have := Fin.lt_def.1 (hmono (Fin.castSucc_lt_last l))
        rw [hl, Fin.val_last] at this
        exact this
      let g : Fin j → Fin n := fun l => ⟨f l.castSucc, hlt l⟩
      have hg : StrictMono g := fun a b hab =>
        Fin.lt_def.2 (Fin.lt_def.1 (hmono (Fin.castSucc_lt_castSucc_iff.2 hab)))
      refine le_sup_of_le_right (le_trans (le_of_eq ?_) (Finset.le_sup
        (f := fun g : Fin j → Fin n =>
          ((∑ l : Fin j, c l * x (g l).castSucc : ℝ) : Trop)
            + ((c j * x (Fin.last n) : ℝ) : Trop))
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩)))
      rw [← WithBot.coe_add, Fin.sum_univ_castSucc, hl]
      rfl
    · -- the last position is avoided
      have hlt : ∀ l : Fin (j + 1), (f l : ℕ) < n := by
        intro l
        have h1 := Fin.lt_def.1 (lt_of_le_of_ne (Fin.le_last _) hl)
        have h2 := Fin.le_def.1 (hmono.monotone (Fin.le_last l))
        rw [Fin.val_last] at h1
        omega
      let g : Fin (j + 1) → Fin n := fun l => ⟨f l, hlt l⟩
      have hg : StrictMono g := fun a b hab => Fin.lt_def.2 (Fin.lt_def.1 (hmono hab))
      refine le_sup_of_le_left (le_trans (le_of_eq rfl) (Finset.le_sup
        (f := fun g : Fin (j + 1) → Fin n =>
          ((∑ l : Fin (j + 1), c l * x (g l).castSucc : ℝ) : Trop))
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩)))
  · have hmono : StrictMono f := (Finset.mem_filter.1 hf).2
    exact Finset.le_sup (f := fun f : Fin (j + 1) → Fin (n + 1) =>
        ((∑ l : Fin (j + 1), c l * x (f l) : ℝ) : Trop))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun a b hab =>
        Fin.castSucc_lt_castSucc_iff.2 (hmono hab)⟩)
  · have hmono : StrictMono g := (Finset.mem_filter.1 hg).2
    let f : Fin (j + 1) → Fin (n + 1) := fun l =>
      if h : (l : ℕ) < j then (g ⟨l, h⟩).castSucc else Fin.last n
    have hf : StrictMono f := by
      intro a b hab
      have hab' := Fin.lt_def.1 hab
      have hb := b.isLt
      by_cases hbj : (b : ℕ) < j
      · simp only [f, dif_pos hbj, dif_pos (show (a : ℕ) < j by omega)]
        exact Fin.castSucc_lt_castSucc_iff.2 (hmono (Fin.lt_def.2 hab'))
      · simp only [f, dif_neg hbj, dif_pos (show (a : ℕ) < j by omega)]
        exact Fin.castSucc_lt_last _
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun f : Fin (j + 1) → Fin (n + 1) =>
        ((∑ l : Fin (j + 1), c l * x (f l) : ℝ) : Trop))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hf⟩))
    rw [← WithBot.coe_add, Fin.sum_univ_castSucc]
    simp only [f, Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg,
      not_false_eq_true, Fin.eta]

/-- A word of one more letter is the shorter word times the last letter. -/
lemma utrop_wordProd_succ {τ M : Type} [Monoid M] (letter : τ → M) {n : ℕ}
    (x : Fin (n + 1) → τ) :
    wordProd letter x = wordProd letter (fun i => x i.castSucc) * letter (x (Fin.last n)) := by
  rw [wordProd, wordProd, orderedProd_eq_prod_ofFn, orderedProd_eq_prod_ofFn,
    List.ofFn_succ_last, List.prod_append, List.prod_singleton]

/-- A supremum over `Fin m` concentrated on two distinct indices. -/
lemma utrop_sup_two {m : ℕ} (F : Fin m → Trop) {a b : Fin m}
    (h : ∀ v, v ≠ a → v ≠ b → F v = ⊥) : Finset.univ.sup F = F a ⊔ F b := by
  refine le_antisymm (Finset.sup_le fun v _ => ?_)
    (sup_le (Finset.le_sup (Finset.mem_univ a)) (Finset.le_sup (Finset.mem_univ b)))
  by_cases hva : v = a
  · subst hva; exact le_sup_left
  by_cases hvb : v = b
  · subst hvb; exact le_sup_right
  rw [h v hva hvb]
  exact bot_le

/-- The `(0, j)` entries of a signed-chain product, for every `j ≤ t`. -/
theorem utropSignedChain_entry {t : ℕ} (ε : Fin t → ℝ) :
    ∀ {n : ℕ} (x : Fin n → ℝ) (j : ℕ) (hj : j < t + 1),
      (wordProd (utropSignedLetter ε) x).val 0 ⟨j, hj⟩
        = utropChainBest (fun l => if h : l < t then ε ⟨l, h⟩ else 0) x j
  | 0, x, j, hj => by
      rw [wordProd, orderedProd_eq_prod_ofFn, List.ofFn_zero, List.prod_nil, UTrop.val_one]
      cases j with
      | zero => rw [utropChainBest_zero]; exact if_pos rfl
      | succ j =>
          rw [utropChainBest_empty, tone, if_neg]
          intro h
          have := congrArg Fin.val h
          simp at this
  | n + 1, x, j, hj => by
      rw [utrop_wordProd_succ, UTrop.val_mul]
      cases j with
      | zero =>
          rw [utropChainBest_zero]
          exact ((wordProd (utropSignedLetter ε) (fun i => x i.castSucc) *
            utropSignedLetter ε (x (Fin.last n))).isUtri.diag 0)
      | succ j =>
          have hjt : j < t := by omega
          rw [tmul, utrop_sup_two _ (a := ⟨j + 1, hj⟩) (b := ⟨j, by omega⟩),
            utropChainBest_succ,
            utropSignedChain_entry ε _ (j + 1) hj, utropSignedChain_entry ε _ j (by omega)]
          · congr 1
            · rw [(utropSignedLetter ε (x (Fin.last n))).isUtri.diag, add_zero]
            · congr 1
              simp only [utropSignedLetter, utropChain, UTrop.val_mk, utropChainMat, dif_pos hjt]
              rw [if_neg (fun h => by have := congrArg Fin.val h; simp at this),
                dif_pos ⟨trivial, hjt⟩]
          · intro v hva hvb
            simp only [utropSignedLetter, utropChain, UTrop.val_mk, utropChainMat]
            rw [if_neg (fun h => hva (h.trans rfl)), dif_neg, WithBot.add_bot]
            rintro ⟨h1, -⟩
            exact hvb (Fin.ext (by simp at h1 ⊢; omega))

/-- **The signed chain computes `max_{i₁<⋯<i_t} ∑ⱼ εⱼ x_{iⱼ}`**: the
first-to-last entry of the product of the chain letters of `x₁, …, xₙ` is the
best sum over strictly increasing position tuples — `⊥ = −∞` when `n < t`, where
there are none. -/
theorem utropSignedChain_wordProd {t : ℕ} (ε : Fin t → ℝ) {n : ℕ} (x : Fin n → ℝ) :
    (wordProd (utropSignedLetter ε) x).val 0 (Fin.last t)
      = (Finset.univ.filter fun f : Fin t → Fin n => StrictMono f).sup
          fun f => ((∑ j : Fin t, ε j * x (f j) : ℝ) : Trop) := by
  rw [show Fin.last t = ⟨t, Nat.lt_succ_self t⟩ from rfl, utropSignedChain_entry ε x t,
    utropChainBest]
  refine Finset.sup_congr rfl fun f _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]

/-- When the word is shorter than the chain, the entry is `−∞`. -/
theorem utropSignedChain_wordProd_of_lt {t : ℕ} (ε : Fin t → ℝ) {n : ℕ} (hn : n < t)
    (x : Fin n → ℝ) : (wordProd (utropSignedLetter ε) x).val 0 (Fin.last t) = ⊥ := by
  rw [utropSignedChain_wordProd]
  refine (Finset.sup_eq_bot_iff _ _).2 fun f hf => absurd ?_ (not_le.2 hn)
  have := Fintype.card_le_of_injective f (Finset.mem_filter.1 hf).2.injective
  simpa using this

end MonoidProduct
