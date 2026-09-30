import MonoidProduct.Width.Product
import MonoidProduct.Aperiodic.EqProd
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Product breadth `β`, and `κ = β` for commutative products

`monoid.tex` `eq:monoid-beta` (product breadth) and
`lem:comm-beta-width`.

A **core** of a word is a scattered subword with the same product; the
**product breadth** `β_G(M)` of an alphabet is the least uniform bound on the
size of a shortest core.  The definition is for an arbitrary monoid and is
*ordered*: the subword on a position set `u` is the word with the letters off
`u` replaced by `1`, multiplied in reading order (`subwordProd`), so no
commutativity is assumed in the definition.

`IsBreadthBound letter b` says every word (of every length) has a core of at
most `b` positions; `breadth letter` is the least such `b`, as an `sInf` over
`ℕ` (so `0` when no bound exists — which never happens for the alphabets the
paper uses, see `exists_isBreadthBound`).  Stating the bounds as a predicate
and taking the infimum afterwards keeps every theorem free of the sup-over-all-
lengths bookkeeping.

For a **commutative aperiodic** monoid the paper's lemma identifies breadth
with the essential width of the subset-product summary of
`Width/Product.lean`.  Both directions are here:

* `prodEss_subset_of_prod_eq` — every essential position of a revealed set
  lies in every core of it (the "more precisely" clause).  Proof: if a core
  `S` omitted the essential `i`, then `p(S) = p(T) = p(S)·(c·xᵢ)` and
  absorption (`mul_right_absorb`, the aperiodic device of `Product.lean`)
  gives `p(S)·c = p(S)`, i.e. `p(T∖{i}) = p(T)`.  Hence
  `card_prodEss_le_of_isBreadthBound`: κ ≤ β.
* `isBreadthBound_of_width` — a shortest core is all-essential (deleting a
  non-essential position would shorten it), so β ≤ κ.  No aperiodicity is
  needed for this direction.

`isWidthBound_iff_isBreadthBound` is the lemma as stated.  Two further forms
are what the corollaries consume: `breadth_le_of_width` (a width bound is a
breadth bound) and `exists_card_prodEss_eq_breadth` (some word is its own
shortest core of size exactly `β`), through which real-valued width bounds
transfer to `β` verbatim.  Theorem `thm:commutative-beta` is
`advPM_prodFun_le_breadth`: `ADV±(Prod_{M,G,n}) ≤ 16√(n·min{n, β})`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## Breadth, for an arbitrary monoid -/

section General

variable {σ : Type} {M : Type} [Monoid M]

/-- The product of the scattered subword of `x` on the positions `u`, in
reading order: letters off `u` are replaced by `1`. -/
def subwordProd (letter : σ → M) {n : ℕ} (x : Fin n → σ) (u : Finset (Fin n)) : M :=
  (List.ofFn fun i => if i ∈ u then letter (x i) else 1).prod

lemma subwordProd_univ (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    subwordProd letter x Finset.univ = wordProd letter x := by
  simp only [subwordProd, Finset.mem_univ, if_true]
  rw [wordProd, orderedProd_eq_prod_ofFn]

lemma subwordProd_empty (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    subwordProd letter x ∅ = 1 := by
  simp [subwordProd, List.ofFn_const]

/-- `u` is a **core** of the word `x`: its scattered subword has the same
product. -/
def IsCore (letter : σ → M) {n : ℕ} (x : Fin n → σ) (u : Finset (Fin n)) : Prop :=
  subwordProd letter x u = wordProd letter x

lemma isCore_univ (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    IsCore letter x Finset.univ :=
  subwordProd_univ letter x

/-- **A breadth bound**: every word has a core of at most `b` positions. -/
def IsBreadthBound (letter : σ → M) (b : ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → σ), ∃ u : Finset (Fin n), u.card ≤ b ∧ IsCore letter x u

lemma IsBreadthBound.mono {letter : σ → M} {b b' : ℕ}
    (h : IsBreadthBound letter b) (hbb : b ≤ b') : IsBreadthBound letter b' := by
  intro n x
  obtain ⟨u, hu, hc⟩ := h n x
  exact ⟨u, hu.trans hbb, hc⟩

/-- **Product breadth** `β`: the least breadth bound (`0` if none exists). -/
noncomputable def breadth (letter : σ → M) : ℕ := sInf {b | IsBreadthBound letter b}

lemma breadth_le {letter : σ → M} {b : ℕ} (h : IsBreadthBound letter b) :
    breadth letter ≤ b :=
  Nat.sInf_le h

lemma isBreadthBound_breadth {letter : σ → M} (h : ∃ b, IsBreadthBound letter b) :
    IsBreadthBound letter (breadth letter) :=
  Nat.sInf_mem h

lemma isBreadthBound_iff_breadth_le {letter : σ → M} (h : ∃ b, IsBreadthBound letter b)
    {b : ℕ} : IsBreadthBound letter b ↔ breadth letter ≤ b :=
  ⟨breadth_le, fun hb => (isBreadthBound_breadth h).mono hb⟩

/-- A word every core of which has at least `c` positions forces `c ≤ β`. -/
lemma le_breadth_of_forall_core {letter : σ → M} (h : ∃ b, IsBreadthBound letter b)
    {n : ℕ} (x : Fin n → σ) {c : ℕ} (hx : ∀ u, IsCore letter x u → c ≤ u.card) :
    c ≤ breadth letter := by
  obtain ⟨u, hu, hc⟩ := isBreadthBound_breadth h n x
  exact (hx u hc).trans hu

/-- Breadth bound `0`: every word's product is the identity. -/
lemma wordProd_eq_one_of_isBreadthBound_zero {letter : σ → M}
    (h : IsBreadthBound letter 0) {n : ℕ} (x : Fin n → σ) : wordProd letter x = 1 := by
  obtain ⟨u, hu, hc⟩ := h n x
  have hu0 : u = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hu)
  rw [← hc, hu0, subwordProd_empty]

end General

/-! ## The commutative case: subwords are subsets -/

section Commutative

variable {σ : Type} {M : Type} [CommMonoid M]

lemma subwordProd_eq_prod (m : σ → M) {n : ℕ} (x : Fin n → σ) (u : Finset (Fin n)) :
    subwordProd m x u = ∏ i ∈ u, m (x i) := by
  rw [subwordProd, List.prod_ofFn, ← Finset.prod_filter]
  congr 1
  ext i
  simp

lemma wordProd_eq_prod (m : σ → M) {n : ℕ} (x : Fin n → σ) :
    wordProd m x = ∏ i, m (x i) := by
  rw [← subwordProd_univ, subwordProd_eq_prod]

lemma isCore_iff (m : σ → M) {n : ℕ} (x : Fin n → σ) (u : Finset (Fin n)) :
    IsCore m x u ↔ ∏ i ∈ u, m (x i) = ∏ i, m (x i) := by
  rw [IsCore, subwordProd_eq_prod, wordProd_eq_prod]

variable [DecidableEq M]

/-! The two `prodEss` lemmas of `Product.lean` carry that file's section
instances (`Nonempty ι`, `Fintype σ`); the summary-level originals do not, and
words of length `0` occur below. -/

lemma mem_prodEss' {ι : Type*} [Fintype ι] [DecidableEq ι] {m : σ → M} {x : ι → σ}
    {T : Finset ι} {i : ι} :
    i ∈ prodEss m x T ↔ i ∈ T ∧ ∏ j ∈ T, m (x j) ≠ ∏ j ∈ T.erase i, m (x j) := by
  unfold prodEss IncrementalSummary.essentialSet
  exact Finset.mem_filter

lemma prodEss_subset' {ι : Type*} [Fintype ι] [DecidableEq ι] (m : σ → M) (x : ι → σ)
    (T : Finset ι) : prodEss m x T ⊆ T :=
  Finset.filter_subset _ _

/-- **Every core contains every essential position** (`lem:comm-beta-width`,
the "more precisely" clause).  If a core `S ⊆ T` omitted an essential `i`,
absorption would make `i` inessential. -/
theorem prodEss_subset_of_prod_eq [Fintype M] [IsAperiodicMonoid M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : σ → M) (x : ι → σ) {T S : Finset ι}
    (hS : S ⊆ T) (hprod : ∏ i ∈ S, m (x i) = ∏ i ∈ T, m (x i)) :
    prodEss m x T ⊆ S := by
  intro i hi
  obtain ⟨hiT, hne⟩ := mem_prodEss'.mp hi
  by_contra hiS
  apply hne
  have hiR : i ∈ T \ S := Finset.mem_sdiff.mpr ⟨hiT, hiS⟩
  have hR : ∏ j ∈ T \ S, m (x j) = m (x i) * ∏ j ∈ (T \ S).erase i, m (x j) :=
    (Finset.mul_prod_erase (T \ S) (fun j => m (x j)) hiR).symm
  have hT : ∏ j ∈ T, m (x j)
      = (∏ j ∈ S, m (x j)) * (m (x i) * ∏ j ∈ (T \ S).erase i, m (x j)) := by
    rw [← hR, mul_comm, Finset.prod_sdiff hS]
  have habs : (∏ j ∈ S, m (x j))
      * ((∏ j ∈ (T \ S).erase i, m (x j)) * m (x i)) = ∏ j ∈ S, m (x j) := by
    rw [mul_comm (∏ j ∈ (T \ S).erase i, m (x j)), ← hT]
    exact hprod.symm
  have hc : (∏ j ∈ S, m (x j)) * ∏ j ∈ (T \ S).erase i, m (x j) = ∏ j ∈ S, m (x j) :=
    mul_right_absorb habs
  have hS' : S ⊆ T.erase i := fun j hj =>
    Finset.mem_erase.mpr ⟨fun h => hiS (h ▸ hj), hS hj⟩
  calc ∏ j ∈ T, m (x j) = ∏ j ∈ S, m (x j) := hprod.symm
    _ = (∏ j ∈ S, m (x j)) * ∏ j ∈ (T \ S).erase i, m (x j) := hc.symm
    _ = (∏ j ∈ S, m (x j)) * ∏ j ∈ T.erase i \ S, m (x j) := by
        rw [Finset.erase_sdiff_comm]
    _ = ∏ j ∈ T.erase i, m (x j) := by rw [mul_comm, Finset.prod_sdiff hS']

/-! ### Restricting a word to a revealed set

`prodEss` lives on an arbitrary finite index type while breadth is defined on
`Fin n` words; the two meet through the enumeration `T.equivFin`. -/

section Restrict

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : σ → M) (x : ι → σ) (T : Finset ι)

/-- The word `x` restricted to `T`, enumerated. -/
noncomputable def restrictWord : Fin T.card → σ := fun j => x (T.equivFin.symm j)

/-- The enumeration, as an embedding into `ι`. -/
noncomputable def restrictEmb : Fin T.card ↪ ι :=
  ⟨fun j => ((T.equivFin.symm j : T) : ι),
    fun _ _ h => T.equivFin.symm.injective (Subtype.ext h)⟩

lemma restrictEmb_mem (j : Fin T.card) : restrictEmb T j ∈ T :=
  (T.equivFin.symm j).2

lemma restrictEmb_equivFin {i : ι} (hi : i ∈ T) :
    restrictEmb T (T.equivFin ⟨i, hi⟩) = i := by
  show ((T.equivFin.symm (T.equivFin ⟨i, hi⟩) : T) : ι) = i
  rw [Equiv.symm_apply_apply]

lemma map_subset_of_restrictEmb (u : Finset (Fin T.card)) :
    u.map (restrictEmb T) ⊆ T := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
  exact restrictEmb_mem T j

lemma map_univ_restrictEmb : Finset.univ.map (restrictEmb T) = T := by
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact restrictEmb_mem T j
  · intro hi
    exact ⟨T.equivFin ⟨i, hi⟩, restrictEmb_equivFin T hi⟩

lemma prod_restrictWord (u : Finset (Fin T.card)) :
    ∏ j ∈ u, m (restrictWord x T j) = ∏ i ∈ u.map (restrictEmb T), m (x i) := by
  rw [Finset.prod_map]
  rfl

lemma prod_restrictWord_univ :
    ∏ j, m (restrictWord x T j) = ∏ i ∈ T, m (x i) := by
  rw [prod_restrictWord, map_univ_restrictEmb]

/-- Essential positions of the restricted word are the essential positions of
`T`, transported. -/
lemma prodEss_restrictWord :
    (prodEss m (restrictWord x T) Finset.univ).map (restrictEmb T) = prodEss m x T := by
  ext i
  simp only [Finset.mem_map, mem_prodEss', Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨restrictEmb_mem T j, fun h => hj ?_⟩
    rw [prod_restrictWord_univ, prod_restrictWord, Finset.map_erase,
      map_univ_restrictEmb]
    exact h
  · rintro ⟨hi, hne⟩
    refine ⟨T.equivFin ⟨i, hi⟩, fun h => hne ?_, restrictEmb_equivFin T hi⟩
    rw [prod_restrictWord_univ, prod_restrictWord, Finset.map_erase,
      map_univ_restrictEmb, restrictEmb_equivFin T hi] at h
    exact h

lemma card_prodEss_restrictWord :
    (prodEss m (restrictWord x T) Finset.univ).card = (prodEss m x T).card := by
  rw [← prodEss_restrictWord m x T, Finset.card_map]

end Restrict

/-- **κ ≤ β**: a breadth bound bounds the essential width of every revealed
set of every word. -/
theorem card_prodEss_le_of_isBreadthBound [Fintype M] [IsAperiodicMonoid M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : σ → M} {b : ℕ}
    (hb : IsBreadthBound m b) (x : ι → σ) (T : Finset ι) :
    (prodEss m x T).card ≤ b := by
  obtain ⟨u, hu, hc⟩ := hb T.card (restrictWord x T)
  rw [isCore_iff, prod_restrictWord, prod_restrictWord_univ] at hc
  have hsub := prodEss_subset_of_prod_eq m x (map_subset_of_restrictEmb T u) hc
  calc (prodEss m x T).card ≤ (u.map (restrictEmb T)).card := Finset.card_le_card hsub
    _ = u.card := Finset.card_map _
    _ ≤ b := hu

/-- **A shortest core is all-essential**: among the cores of `x` (nonempty:
the whole word), one of least cardinality has every position essential. -/
lemma exists_minimal_core (m : σ → M) {n : ℕ} (x : Fin n → σ) :
    ∃ u : Finset (Fin n), IsCore m x u ∧ prodEss m x u = u
      ∧ ∀ v, IsCore m x v → u.card ≤ v.card := by
  classical
  let P : Finset (Finset (Fin n)) := Finset.univ.filter fun u => IsCore m x u
  have hP : P.Nonempty := ⟨Finset.univ, by simp [P, isCore_univ]⟩
  obtain ⟨u, huP, hmin⟩ := Finset.exists_min_image P Finset.card hP
  have hu : IsCore m x u := (Finset.mem_filter.mp huP).2
  refine ⟨u, hu, ?_, fun v hv => hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)⟩
  refine Finset.Subset.antisymm (prodEss_subset' m x u) fun i hi => ?_
  refine mem_prodEss'.mpr ⟨hi, fun heq => ?_⟩
  have hcore : IsCore m x (u.erase i) := by
    rw [isCore_iff] at hu ⊢
    rw [← heq, hu]
  have hle := hmin _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcore⟩)
  have hlt := Finset.card_erase_lt_of_mem hi
  omega

/-- **β ≤ κ**: a width bound is a breadth bound.  No aperiodicity is needed. -/
theorem isBreadthBound_of_width {m : σ → M} {b : ℕ}
    (hw : ∀ (n : ℕ) (x : Fin n → σ) (T : Finset (Fin n)), (prodEss m x T).card ≤ b) :
    IsBreadthBound m b := by
  intro n x
  obtain ⟨u, hu, hall, -⟩ := exists_minimal_core m x
  refine ⟨u, ?_, hu⟩
  calc u.card = (prodEss m x u).card := by rw [hall]
    _ ≤ b := hw n x u

end Commutative

/-! ## Commutative aperiodic monoids: `κ = β` -/

section Aperiodic

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M] [IsAperiodicMonoid M]
variable (m : σ → M)

/-- The width fallback `|M| - 1`, for words of every length (the `n = 0` case
is vacuous). -/
lemma card_prodEss_le_card_monoid' {n : ℕ} (x : Fin n → σ) (T : Finset (Fin n)) :
    (prodEss m x T).card ≤ Fintype.card M - 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h : (prodEss m x T).card ≤ Fintype.card (Fin 0) :=
      (Finset.card_le_card (prodEss_subset' m x T)).trans (Finset.card_le_univ T)
    rw [Fintype.card_fin] at h
    omega
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact card_prodEss_le_card_monoid m x T

/-- A breadth bound always exists: `|M| - 1`. -/
theorem exists_isBreadthBound : ∃ b, IsBreadthBound m b :=
  ⟨Fintype.card M - 1, isBreadthBound_of_width fun _ x T => card_prodEss_le_card_monoid' m x T⟩

/-- **`κ = β`** (`monoid.tex` Lemma `lem:comm-beta-width`): the width bounds of
the subset-product summary are exactly the breadth bounds of the alphabet. -/
theorem isWidthBound_iff_isBreadthBound {b : ℕ} :
    (∀ (n : ℕ) (x : Fin n → σ) (T : Finset (Fin n)), (prodEss m x T).card ≤ b)
      ↔ IsBreadthBound m b :=
  ⟨isBreadthBound_of_width, fun h _ x T => card_prodEss_le_of_isBreadthBound h x T⟩

/-- Every revealed set of every word has at most `β` essential positions. -/
theorem card_prodEss_le_breadth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → σ) (T : Finset ι) : (prodEss m x T).card ≤ breadth m :=
  card_prodEss_le_of_isBreadthBound (isBreadthBound_breadth (exists_isBreadthBound m)) x T

/-- A width bound is a breadth bound. -/
theorem breadth_le_of_width {b : ℕ}
    (hw : ∀ (n : ℕ) (x : Fin n → σ) (T : Finset (Fin n)), (prodEss m x T).card ≤ b) :
    breadth m ≤ b :=
  breadth_le (isBreadthBound_of_width hw)

theorem breadth_le_card_monoid : breadth m ≤ Fintype.card M - 1 :=
  breadth_le_of_width m fun _ x T => card_prodEss_le_card_monoid' m x T

/-- **β is attained**: some word, revealed in full, has exactly `β` essential
positions.  (Take a word with no core of size `< β`; its shortest core,
restricted to itself, is all-essential of size `β`.)  Through this lemma every
real-valued width bound transfers to `β`. -/
theorem exists_card_prodEss_eq_breadth :
    ∃ (n : ℕ) (x : Fin n → σ), (prodEss m x Finset.univ).card = breadth m := by
  rcases Nat.eq_zero_or_pos (breadth m) with h0 | hpos
  · refine ⟨0, Fin.elim0, ?_⟩
    rw [h0]
    have h : (prodEss m Fin.elim0 Finset.univ).card ≤ Fintype.card (Fin 0) :=
      (Finset.card_le_card (prodEss_subset' m Fin.elim0 Finset.univ)).trans
        (Finset.card_le_univ _)
    rw [Fintype.card_fin] at h
    omega
  · obtain ⟨c, hc⟩ : ∃ c, breadth m = c + 1 := ⟨breadth m - 1, by omega⟩
    have hnot : ¬ IsBreadthBound m c := fun h => by
      have := breadth_le h
      omega
    simp only [IsBreadthBound, not_forall, not_exists, not_and] at hnot
    obtain ⟨n, x, hx⟩ := hnot
    obtain ⟨u, hu, hall, hmin⟩ := exists_minimal_core m x
    have hlo : c + 1 ≤ u.card := by
      by_contra hlt
      exact hx u (by omega) hu
    have hhi : u.card ≤ breadth m := by
      obtain ⟨v, hv, hvc⟩ := isBreadthBound_breadth (exists_isBreadthBound m) n x
      exact (hmin v hvc).trans hv
    refine ⟨u.card, restrictWord x u, ?_⟩
    rw [card_prodEss_restrictWord, hall]
    omega

/-- **Theorem `thm:commutative-beta`**: for a finite commutative aperiodic
monoid and any alphabet, `ADV±(Prod_{M,G,n}) ≤ 16√(n·min{n, β_G(M)})`. -/
theorem advPM_prodFun_le_breadth {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * (min (Fintype.card ι) (breadth m) : ℕ)) := by
  rcases Nat.eq_zero_or_pos (breadth m) with h0 | hpos
  · have hb : IsBreadthBound m 0 := h0 ▸ isBreadthBound_breadth (exists_isBreadthBound m)
    have hone : ∀ x : ι → σ, ∏ i, m (x i) = 1 := by
      intro x
      have h := wordProd_eq_one_of_isBreadthBound_zero hb
        (fun j => x ((Fintype.equivFin ι).symm j))
      rw [wordProd_eq_prod] at h
      rw [← h]
      exact Fintype.prod_equiv (Fintype.equivFin ι) _ _ fun i => by simp
    rw [advPM_eq_zero_of_forall_eq fun x y => by rw [hone x, hone y]]
    positivity
  · refine advPM_prodFun_le_of_width m (lt_min_iff.mpr ⟨Fintype.card_pos, hpos⟩)
      fun x T => le_min ?_ (card_prodEss_le_breadth m x T)
    exact (Finset.card_le_card (prodEss_subset' m x T)).trans (Finset.card_le_univ T)

end Aperiodic

end MonoidProduct
