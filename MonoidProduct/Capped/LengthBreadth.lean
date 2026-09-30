import MonoidProduct.Capped.Breadth
import MonoidProduct.Capped.RTrivial
import MonoidProduct.Quantum.CommutativeLower
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Capped counters at a fixed length: shortest cores of length `min{n, k·r}`

`monoid.tex` Theorem `thm:capped-counter-product`, the length-`n` clause and the
`Θ` statement `eq:capped-counter-theta`.  For `M_{k,r} = Capped k ^ ρ` (`r = |ρ|`):

* `cappedLen_exists_core_le`: every word of length `n` (over any alphabet mapped into
  `M_{k,r}`) has a core — a product-preserving scattered subword — of at most
  `min{n, k·r}` positions;
* `cappedLen_exists_word`: some length-`n` word over the full alphabet has no core of
  fewer than `min{n, k·r}` positions (the paper's `min{n, k·r}` unit vectors, at most
  `k` copies per coordinate, padded with the zero vector);
* `cappedLen_isGreatest`: together, `min{n, k·r}` is the largest length of a shortest
  core among words of length `n`.

The quantum clause: `M_{k,r}` is commutative, aperiodic and nontrivial, so the
commutative lower bound `commutative_qQuery_lower_total` with `breadth_capped_eq` gives
`√(n·min{n, k·r})/72 ≤ Q_{1/3}`, and with `capped_qQuery_le_min` the full sandwich
`cappedLen_qQuery_theta`, i.e. `Q_{1/3}(Prod_{M_{k,r},n}) = Θ(√(n·min{n, k·r}))`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ] {k : ℕ}

/-! ## The upper bound: a core of at most `min{n, k·r}` positions -/

/-- **Every length-`n` word has a core of at most `min{n, k·r}` positions.** -/
theorem cappedLen_exists_core_le {σ : Type} [Fintype σ] [DecidableEq σ]
    (m : σ → ρ → Capped k) {n : ℕ} (x : Fin n → σ) :
    ∃ u : Finset (Fin n), u.card ≤ min n (Fintype.card ρ * k) ∧ IsCore m x u := by
  obtain ⟨u, hu, hc⟩ :=
    isBreadthBound_of_width (fun _ x T => card_prodEss_le_capped' m x T) n x
  refine ⟨u, le_min ?_ hu, hc⟩
  simpa using Finset.card_le_univ u

/-! ## The lower bound: a labelled unit word -/

/-- The labelled unit word: a position `i ∈ S` carries the unit vector `e_{lab i}`,
every other position the identity. -/
noncomputable def cappedLenWord {n : ℕ} (S : Finset (Fin n)) (lab : Fin n → ρ) :
    Fin n → (ρ → Capped k) :=
  fun i => if i ∈ S then cappedUnit k (lab i) else 1

lemma cappedLenWord_val (hk : 0 < k) {n : ℕ} (S : Finset (Fin n)) (lab : Fin n → ρ)
    (i : Fin n) (c : ρ) :
    (cappedLenWord (k := k) S lab i c).val = if i ∈ S ∧ c = lab i then 1 else 0 := by
  unfold cappedLenWord cappedUnit
  by_cases hi : i ∈ S <;> by_cases hc : c = lab i <;> simp [hi, hc, gen_val_of_pos hk]

lemma cappedLenWord_val_prod (hk : 0 < k) {n : ℕ} (S : Finset (Fin n)) (lab : Fin n → ρ)
    (u : Finset (Fin n)) (c : ρ) :
    ((∏ i ∈ u, cappedLenWord (k := k) S lab i) c).val
      = min (u.filter fun i => i ∈ S ∧ c = lab i).card k := by
  rw [Finset.prod_apply, Capped.val_prod, Finset.card_filter]
  congr 1
  exact Finset.sum_congr rfl fun i _ => cappedLenWord_val hk S lab i c

/-- If every label is used at most `k` times on `S`, every core contains `S`: dropping a
position of `S` labelled `c` leaves fewer than `k` copies of `e_c`. -/
theorem cappedLenWord_subset_core (hk : 0 < k) {n : ℕ} (S : Finset (Fin n))
    (lab : Fin n → ρ) (hfib : ∀ c, (S.filter fun i => c = lab i).card ≤ k)
    (u : Finset (Fin n)) (hu : IsCore id (cappedLenWord (k := k) S lab) u) : S ⊆ u := by
  rw [isCore_iff] at hu
  simp only [id] at hu
  intro j hj
  by_contra hju
  have h1 := congrArg (fun f => (f (lab j)).val) hu
  rw [cappedLenWord_val_prod hk, cappedLenWord_val_prod hk] at h1
  have hsub : (u.filter fun i => i ∈ S ∧ lab j = lab i)
      ⊂ Finset.univ.filter fun i => i ∈ S ∧ lab j = lab i := by
    refine (Finset.ssubset_iff_of_subset
      (Finset.filter_subset_filter _ (Finset.subset_univ u))).mpr ⟨j, ?_, ?_⟩
    · simp [hj]
    · simp [hju]
  have hlt := Finset.card_lt_card hsub
  have hle : (Finset.univ.filter fun i => i ∈ S ∧ lab j = lab i).card ≤ k := by
    rw [show (Finset.univ.filter fun i => i ∈ S ∧ lab j = lab i)
        = S.filter fun i => lab j = lab i by ext i; simp]
    exact hfib (lab j)
  omega

/-- The first `m` positions of `Fin n`, `m ≤ n`, number `m`. -/
lemma cappedLen_card_filter_lt {n m : ℕ} (hm : m ≤ n) :
    (Finset.univ.filter fun i : Fin n => i.val < m).card = m := by
  have h : (Finset.univ.filter fun i : Fin n => i.val < m)
      = (Finset.univ : Finset (Fin m)).map (Fin.castLEEmb hm) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castLEEmb_apply]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- **Some length-`n` word needs `min{n, k·r}` positions**: every core of it has at least
`min{n, k·r}` positions. -/
theorem cappedLen_exists_word (hk : 0 < k) (n : ℕ) :
    ∃ x : Fin n → (ρ → Capped k), ∀ u : Finset (Fin n),
      IsCore id x u → min n (Fintype.card ρ * k) ≤ u.card := by
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · refine ⟨fun _ => 1, fun u _ => ?_⟩
    simp [Fintype.card_eq_zero]
  have hcard : Fintype.card (ρ × Fin k) = Fintype.card ρ * k := by
    rw [Fintype.card_prod, Fintype.card_fin]
  let d : ρ × Fin k := (Classical.arbitrary ρ, ⟨0, hk⟩)
  let g : Fin n → ρ × Fin k := fun i =>
    if h : i.val < Fintype.card (ρ × Fin k) then unitEquiv ρ k ⟨i.val, h⟩ else d
  let S : Finset (Fin n) := Finset.univ.filter fun i => i.val < min n (Fintype.card ρ * k)
  have hS : ∀ i ∈ S, i.val < Fintype.card (ρ × Fin k) := by
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    rw [hcard]
    omega
  have hfib : ∀ c, (S.filter fun i => c = (g i).1).card ≤ k := by
    intro c
    have h := Finset.card_le_card_of_injOn (fun i => (g i).2)
      (s := S.filter fun i => c = (g i).1) (t := (Finset.univ : Finset (Fin k)))
      (fun _ _ => Finset.mem_univ _) ?_
    · simpa using h
    intro i hi i' hi' heq
    have hi2 := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    have hi2' := Finset.mem_filter.mp (Finset.mem_coe.mp hi')
    have hg : g i = g i' := Prod.ext (hi2.2.symm.trans hi2'.2) heq
    simp only [g, dif_pos (hS i hi2.1), dif_pos (hS i' hi2'.1)] at hg
    exact Fin.ext (by simpa using (unitEquiv ρ k).injective hg)
  refine ⟨cappedLenWord S fun i => (g i).1, fun u hu => ?_⟩
  have hsub := cappedLenWord_subset_core hk S _ hfib u hu
  have := Finset.card_le_card hsub
  rwa [cappedLen_card_filter_lt (min_le_left _ _)] at this

/-- **The length-`n` clause of `thm:capped-counter-product`**: among words of length
`n` over `M_{k,r}`, the largest length of a shortest core is exactly `min{n, k·r}`. -/
theorem cappedLen_isGreatest (hk : 0 < k) (n : ℕ) :
    IsGreatest {c : ℕ | ∃ x : Fin n → (ρ → Capped k),
        ∀ u : Finset (Fin n), IsCore id x u → c ≤ u.card}
      (min n (Fintype.card ρ * k)) := by
  refine ⟨cappedLen_exists_word hk n, ?_⟩
  rintro c ⟨x, hx⟩
  obtain ⟨u, hu, hc⟩ := cappedLen_exists_core_le id x
  exact (hx u hc).trans hu

/-! ## The quantum clause: `Q_{1/3} = Θ(√(n·min{n, k·r}))` -/

/-- `M_{k,r}` is aperiodic, coordinatewise: `a^{k+1} = a^{k+2}`. -/
instance cappedLen_isAperiodicMonoid : IsAperiodicMonoid (ρ → Capped k) :=
  ⟨fun a => ⟨k + 1, Nat.succ_pos k, funext fun c => by
    simp only [Pi.pow_apply]
    rw [pow_succ (a c) (k + 1), Capped.pow_index, ← pow_succ, Capped.pow_index]⟩⟩

lemma cappedLen_nontrivial (hk : 0 < k) : Nontrivial (Capped k) :=
  ⟨⟨1, Capped.gen, fun h => by
    have := congrArg Capped.val h
    rw [gen_val_of_pos hk, Capped.one_val] at this
    omega⟩⟩

/-- **The capped-counter lower bound at error `1/3`**:
`√(n·min{n, k·r})/72 ≤ Q_{1/3}(Prod_{M_{k,r},n})`. -/
theorem cappedLen_qQuery_lower (hk : 0 < k) [Nonempty ρ] {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt ((n * min n (Fintype.card ρ * k) : ℕ) : ℝ) / 72
      ≤ (qQuery (fun x : Fin n → (ρ → Capped k) => ∏ i, x i) (1 / 3) : ℝ) := by
  have := cappedLen_nontrivial hk
  have h := commutative_qQuery_lower_total (M := ρ → Capped k) hn
  rwa [breadth_capped_eq hk] at h

/-- **`eq:capped-counter-theta`**: for `n ≥ 1`, `√(n·min{n,k·r})/72` is at most
`Q_{1/3}(Prod_{M_{k,r},n})`, which is at most `min{n, 8192·(1 + 16·√(n·min{n,k·r}))}`. -/
theorem cappedLen_qQuery_theta (hk : 0 < k) [Nonempty ρ] {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt ((n * min n (Fintype.card ρ * k) : ℕ) : ℝ) / 72
        ≤ (qQuery (fun x : Fin n → (ρ → Capped k) => ∏ i, x i) (1 / 3) : ℝ)
      ∧ (qQuery (fun x : Fin n → (ρ → Capped k) => ∏ i, x i) (1 / 3) : ℝ)
        ≤ min (n : ℝ) (uniformExtractionConstant
            * (1 + 16 * Real.sqrt ((n : ℝ) * (min n (Fintype.card ρ * k) : ℕ)))) := by
  refine ⟨cappedLen_qQuery_lower hk hn, ?_⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := capped_qQuery_le_min (ι := Fin n) hk (id : (ρ → Capped k) → ρ → Capped k)
  simpa only [Fintype.card_fin, id] using h

end MonoidProduct
