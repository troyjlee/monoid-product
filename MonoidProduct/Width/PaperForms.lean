import MonoidProduct.Width.BreadthBounds
import MonoidProduct.Quantum.WidthApplications
import MonoidProduct.Quantum.Applications
import MonoidProduct.Aperiodic.CommJTrivial
import MonoidProduct.Aperiodic.RTrivial
import MonoidProduct.Promise.Semilattice
import MonoidProduct.Semilattice.Semigroup
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The commutative theorems of the paper in their displayed forms

The breadth, adversary and query statements of Section `sec:lattice` of the paper exactly as
displayed, assembled from the library's bounds.

* `thm:semilattice-product`:
  * `eq:semilattice-beta`, `β_G ≤ ⌊log₂(|L_G|+1)⌋`: `breadth_le_log_joinClosure`;
  * `eq:semilattice-adv`, with the `min{n,·}` branch: `advPM_prodFun_le_joinClosure`;
  * the `Q_{1/3}` clause: `qQuery_prodFun_le_joinClosure`;
  * the promise remark after it (`≤ K` generated joins): `advPMOn_joinMap_le_of_joinCount`.
* `thm:index-two-width`:
  * `eq:index-two-width` for every `|M|` (trivial `M` included): `breadth_le_five_logb`;
  * `eq:index-two-adv` and the `Q_{1/3}` clause: `advPM_prodFun_le_indexTwo_min`,
    `qQuery_prodFun_le_indexTwo_min`.
* `thm:index-k-width`:
  * `eq:index-k-width` with `C = 2⁶⁴` (natural log): `breadth_le_indexK_paper`;
  * `eq:index-k-adv` and the `Q_{1/3}` clause: `advPM_prodFun_le_indexK_min`,
    `qQuery_prodFun_le_indexK_min`.
* `prop:comm-jtrivial`, "hence `R`- and `L`-trivial": `isRTrivialMonoid_of_comm`,
  `leftIdeal_injective_of_comm`.
* `cor:jtrivial-division`, second form `O(min{n, τ(M)√n})`: `jtrivial_qQuery_le_min_tau`.

**The join closure.**  The paper's `L_G` is the *nonempty* join closure of the allowed
letters; in a commutative idempotent monoid the join is the product, so `L_G` is the set of
products of nonempty sets of letters (`joinClosureFin`).  The identity is not adjoined: it
enters the count only as the value of the empty subset, whence the `+1`, exactly as in the
paper's proof ("all in `L_G ∪ {1}`").  `card_generatedSub_eq_joinClosureFin` identifies
`|L_G|` with the library's `GeneratedSub` (mathlib's `supClosure` of the letters, in the
`AsJoin` order), the object counted by `advPM_prodMapAmb_le` and `hasDual_prodMapAmb`.

**The promise remark** is stated for the join of the letters in a finite semilattice
(`joinMap`, the setting of the library's promise certificate `advPMOn_joinMap_le_of_bound`);
"generates at most `K` nonempty joins" is `(supClosure (range of the input's values)).ncard
≤ K`.

**Two generic transfers** turn any real bound `β_G ≤ b` into the paper's displays:
`advPM_prodFun_le_of_breadth_le` (`ADV± ≤ 16√(n·min{n,b})`, from
`advPM_prodFun_le_breadth`, i.e. `thm:commutative-beta`) and
`qQuery_prodFun_le_min_of_breadth_le` (`Q_{1/3} ≤ min{n, 2¹⁸√(n·min{n,b})}`, through the
essential-width certificate and the uniform extraction, `width_qQuery_upper`).  The query
clause is proved as the paper proves it — "from `thm:commutative-beta`" — rather than from
the separate semilattice certificate, which would give the same shape.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## Generic transfers from a breadth bound -/

section Transfer

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **`thm:commutative-beta` against any real breadth bound**: if `β_G ≤ b` then
`ADV±(Prod_{M,G,n}) ≤ 16√(n·min{n, b})`. -/
theorem advPM_prodFun_le_of_breadth_le [IsAperiodicMonoid M] (m : σ → M) {b : ℝ}
    (hb : (breadth m : ℝ) ≤ b) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * min (Fintype.card ι : ℝ) b) := by
  refine (advPM_prodFun_le_breadth m).trans ?_
  gcongr
  push_cast
  exact min_le_min_left _ hb

/-- **The query clause of `thm:commutative-beta` against any real breadth bound**:
if `β_G ≤ b` then `Q_{1/3}(Prod_{M,G,n}) ≤ min{n, 2¹⁸·√(n·min{n, b})}`. -/
theorem qQuery_prodFun_le_min_of_breadth_le [IsAperiodicMonoid M] (m : σ → M) {b : ℝ}
    (hb : (breadth m : ℝ) ≤ b) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ) * min (Fintype.card ι : ℝ) b)) := by
  refine le_min (by exact_mod_cast prodFun_qQuery_upper_length m) ?_
  rcases Nat.eq_zero_or_pos (breadth m) with h0 | hpos
  · -- `β = 0`: the product is constant and zero queries suffice
    have hb0 : IsBreadthBound m 0 := h0 ▸ isBreadthBound_breadth (exists_isBreadthBound m)
    have hone : ∀ x : ι → σ, ∏ i, m (x i) = 1 := by
      intro x
      have h := wordProd_eq_one_of_isBreadthBound_zero hb0
        (fun j => x ((Fintype.equivFin ι).symm j))
      rw [wordProd_eq_prod] at h
      rw [← h]
      exact Fintype.prod_equiv (Fintype.equivFin ι) _ _ fun i => by simp
    have hq : qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) = 0 :=
      qQueryOn_const_eq_zero _ (c := (1 : M)) hone (by norm_num)
    rw [hq, Nat.cast_zero]
    positivity
  · set n : ℕ := Fintype.card ι with hn
    have hn1 : 1 ≤ n := Fintype.card_pos
    have hB : 0 < min n (breadth m) := lt_min hn1 hpos
    have hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ min n (breadth m) :=
      fun x T => le_min ((Finset.card_le_card (prodEss_subset' m x T)).trans
        (Finset.card_le_univ T)) (card_prodEss_le_breadth m x T)
    have h := width_qQuery_upper m hB hw
    have hB1 : (1 : ℝ) ≤ ((min n (breadth m) : ℕ) : ℝ) := by exact_mod_cast hB
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hs1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * ((min n (breadth m) : ℕ) : ℝ)) :=
      Real.one_le_sqrt.2 (by nlinarith)
    have hsb : Real.sqrt ((n : ℝ) * ((min n (breadth m) : ℕ) : ℝ))
        ≤ Real.sqrt ((n : ℝ) * min (n : ℝ) b) := by
      gcongr
      push_cast
      exact min_le_min_left _ hb
    refine h.trans ?_
    rw [uniformExtractionConstant]
    nlinarith

end Transfer

/-! ## `thm:semilattice-product`: the join closure `L_G` -/

section Semilattice

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- **The nonempty join closure `L_G`** of the letters `m : σ → M`: the products of the
nonempty sets of letters.  In a commutative idempotent monoid the join is the product, so
this is the paper's `L_G`; the identity is not adjoined (it lies in `L_G` only if some
nonempty product equals it). -/
def joinClosureFin (m : σ → M) : Finset M :=
  ((Finset.univ : Finset (Finset σ)).filter Finset.Nonempty).image fun S => ∏ s ∈ S, m s

lemma mem_joinClosureFin {m : σ → M} {a : M} :
    a ∈ joinClosureFin m ↔ ∃ S : Finset σ, S.Nonempty ∧ ∏ s ∈ S, m s = a := by
  simp [joinClosureFin]

variable (hidem : ∀ a : M, a * a = a)
include hidem

/-- Under idempotence a product over positions is the product over the letters that occur. -/
lemma prod_comp_eq_prod_image_of_idem {α β : Type*} [DecidableEq β] (f : β → M)
    (g : α → β) (s : Finset α) : ∏ a ∈ s, f (g a) = ∏ b ∈ s.image g, f b := by
  rw [Finset.prod_comp]
  refine Finset.prod_congr rfl fun b hb => ?_
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
  have hpos : 0 < (s.filter fun a' => g a' = g a).card :=
    Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [hk]
  exact IsIdempotentElem.pow_succ_eq k (hidem (f (g a)))

/-- Every subword product lies in `L_G ∪ {1}`. -/
lemma prod_mem_insert_one_joinClosureFin (m : σ → M) {ι : Type*} (x : ι → σ)
    (U : Finset ι) : ∏ j ∈ U, m (x j) ∈ insert 1 (joinClosureFin m) := by
  rcases U.eq_empty_or_nonempty with rfl | hU
  · simp
  · rw [prod_comp_eq_prod_image_of_idem hidem m x U]
    exact Finset.mem_insert_of_mem (mem_joinClosureFin.2 ⟨U.image x, hU.image x, rfl⟩)

/-- **`lem:critical` against the join closure**: the `2^{|E|}` context products of the
subsets of an essential set are distinct and lie in `L_G ∪ {1}`, so
`2^{|E|} ≤ |L_G| + 1`. -/
theorem two_pow_card_prodEss_le_joinClosure (m : σ → M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x : ι → σ) (T : Finset ι) :
    2 ^ (prodEss m x T).card ≤ (joinClosureFin m).card + 1 := by
  have hinj : Set.InjOn (fun S => ctxProd m x T S)
      ((prodEss m x T).powerset : Set (Finset ι)) := by
    intro S hS S' hS' heq
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hS hS'
    by_contra hne
    by_cases hsub : S ⊆ S'
    · obtain ⟨i, hiS', hiS⟩ :=
        Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      exact ctxProd_ne_of_mem_of_notMem hidem m x T hS' hS hiS' hiS heq.symm
    · obtain ⟨i, hiS, hiS'⟩ := Finset.not_subset.mp hsub
      exact ctxProd_ne_of_mem_of_notMem hidem m x T hS hS' hiS hiS' heq
  have hmaps : ∀ S ∈ (prodEss m x T).powerset,
      ctxProd m x T S ∈ insert 1 (joinClosureFin m) := by
    intro S _
    rw [ctxProd, ← prod_union_of_idem hidem]
    exact prod_mem_insert_one_joinClosureFin hidem m x _
  calc 2 ^ (prodEss m x T).card = (prodEss m x T).powerset.card :=
        (Finset.card_powerset _).symm
    _ ≤ (insert 1 (joinClosureFin m)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ (joinClosureFin m).card + 1 := Finset.card_insert_le _ _

/-- **Theorem `thm:semilattice-product`, `eq:semilattice-beta`**: for a finite commutative
idempotent monoid, `β_G(M) ≤ ⌊log₂(|L_G|+1)⌋` with `L_G` the nonempty join closure of the
allowed letters. -/
theorem breadth_le_log_joinClosure (m : σ → M) :
    breadth m ≤ Nat.log 2 ((joinClosureFin m).card + 1) := by
  have : IsAperiodicMonoid M := isAperiodicMonoid_of_idem hidem
  exact breadth_le_of_width m fun _ x T =>
    Nat.le_log_of_pow_le one_lt_two (two_pow_card_prodEss_le_joinClosure hidem m x T)

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Theorem `thm:semilattice-product`, `eq:semilattice-adv`**:
`ADV±(Prod_{M,G,n}) ≤ 16√(n·min{n, ⌊log₂(|L_G|+1)⌋})`. -/
theorem advPM_prodFun_le_joinClosure (m : σ → M) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * ((min (Fintype.card ι) (Nat.log 2 ((joinClosureFin m).card + 1)) : ℕ) : ℝ)) := by
  have : IsAperiodicMonoid M := isAperiodicMonoid_of_idem hidem
  have h := advPM_prodFun_le_of_breadth_le (ι := ι) m
    (b := (Nat.log 2 ((joinClosureFin m).card + 1) : ℝ))
    (by exact_mod_cast breadth_le_log_joinClosure hidem m)
  push_cast
  exact h

/-- **Theorem `thm:semilattice-product`, the query clause**, with its constant:
`Q_{1/3}(Prod_{M,G,n}) ≤ min{n, 2¹⁸·√(n·min{n, ⌊log₂(|L_G|+1)⌋})}`. -/
theorem qQuery_prodFun_le_joinClosure (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ)
          * ((min (Fintype.card ι) (Nat.log 2 ((joinClosureFin m).card + 1)) : ℕ) : ℝ))) := by
  have : IsAperiodicMonoid M := isAperiodicMonoid_of_idem hidem
  have h := qQuery_prodFun_le_min_of_breadth_le (ι := ι) m
    (b := (Nat.log 2 ((joinClosureFin m).card + 1) : ℝ))
    (by exact_mod_cast breadth_le_log_joinClosure hidem m)
  push_cast
  exact h

end Semilattice

/-! ## `L_G` is the library's generated subsemigroup -/

section Bridge

variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- A commutative idempotent monoid as an `IsIdemCommSemigroup` (same multiplication). -/
abbrev idemCommSemigroupOfMonoid (hidem : ∀ a : M, a * a = a) : IsIdemCommSemigroup M :=
  { (inferInstance : CommMonoid M) with mul_self := hidem }

/-- **`|L_G|` is the size of the library's `GeneratedSub`**: the nonempty join closure
`joinClosureFin m` has exactly as many elements as mathlib's `supClosure` of the letters in
the `AsJoin` order — the object counted by `advPM_prodMapAmb_le` and
`hasDual_prodMapAmb`. -/
theorem card_generatedSub_eq_joinClosureFin (hidem : ∀ a : M, a * a = a) (m : σ → M) :
    letI := idemCommSemigroupOfMonoid hidem
    Fintype.card (GeneratedSub m) = (joinClosureFin m).card := by
  let _ := idemCommSemigroupOfMonoid hidem
  have hmem : ∀ a : AsJoin M, a ∈ supClosure (Set.range fun s => AsJoin.mk (m s))
      ↔ a.val ∈ joinClosureFin m := by
    intro a
    constructor
    · intro ha
      have hsub : supClosure (Set.range fun s => AsJoin.mk (m s))
          ⊆ {b : AsJoin M | b.val ∈ joinClosureFin m} := by
        refine supClosure_min ?_ ?_
        · rintro _ ⟨s, rfl⟩
          exact (mem_joinClosureFin (M := M)).2
            ⟨{s}, Finset.singleton_nonempty s, Finset.prod_singleton _ _⟩
        · intro b hb c hc
          obtain ⟨S, hS, hSb⟩ := (mem_joinClosureFin (M := M) (a := b.val)).1 hb
          obtain ⟨S', -, hSc⟩ := (mem_joinClosureFin (M := M) (a := c.val)).1 hc
          refine (mem_joinClosureFin (M := M) (a := (b ⊔ c).val)).2
            ⟨S ∪ S', hS.mono Finset.subset_union_left, ?_⟩
          rw [prod_union_of_idem hidem, hSb, hSc]
          rfl
      exact hsub ha
    · intro ha
      have key : ∀ S : Finset σ, S.Nonempty →
          AsJoin.mk (∏ s ∈ S, m s) ∈ supClosure (Set.range fun s => AsJoin.mk (m s)) := by
        intro S hS
        induction hS using Finset.Nonempty.cons_induction with
        | singleton s =>
          rw [Finset.prod_singleton]
          exact subset_supClosure (Set.mem_range_self s)
        | cons s S hs hS ih =>
          rw [Finset.prod_cons]
          exact supClosed_supClosure (subset_supClosure (Set.mem_range_self s)) ih
      obtain ⟨S, hS, hSa⟩ := (mem_joinClosureFin (M := M) (a := a.val)).1 ha
      rw [← AsJoin.mk_val a, ← hSa]
      exact key S hS
  calc Fintype.card (GeneratedSub m) = Fintype.card {a : M // a ∈ joinClosureFin m} :=
        Fintype.card_congr
          { toFun := fun a => ⟨a.1.val, (hmem _).1 a.2⟩
            invFun := fun a => ⟨AsJoin.mk a.1, (hmem _).2 a.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    _ = (joinClosureFin m).card := Fintype.card_coe _

end Bridge

/-! ## The promise remark after `thm:semilattice-product` -/

section Promise

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [SemilatticeSup A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The criticality bound against the joins one input generates**: the positions of `T`
critical for `y` number at most `log₂` of one plus the size of the nonempty join closure of
`y`'s values. -/
theorem two_pow_card_criticalSet_le_ncard (y : ι → A) (T : Finset ι) :
    2 ^ (criticalSet y T).card ≤ (supClosure (Set.range y)).ncard + 1 := by
  classical
  set L := supClosure (Set.range y) with hL
  have hfin : L.Finite := (Set.finite_range y).supClosure
  let tgt : Finset (WithBot A) :=
    insert ⊥ (hfin.toFinset.map ⟨((↑) : A → WithBot A), WithBot.coe_injective⟩)
  have hmaps : ∀ U ∈ (criticalSet y T).powerset, joinOn y U ∈ tgt := by
    intro U _
    rcases U.eq_empty_or_nonempty with rfl | hU
    · simp [joinOn, tgt]
    · refine Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨U.sup' hU y, ?_, ?_⟩)
      · exact hfin.mem_toFinset.2 (supClosed_supClosure.finsetSup'_mem hU
          fun i _ => subset_supClosure (Set.mem_range_self i))
      · exact Finset.coe_sup' hU y
  calc 2 ^ (criticalSet y T).card = ((criticalSet y T).powerset).card :=
        (Finset.card_powerset _).symm
    _ ≤ tgt.card := Finset.card_le_card_of_injOn (fun U => joinOn y U) hmaps
        (joinOn_injOn y T)
    _ ≤ hfin.toFinset.card + 1 := by
        refine (Finset.card_insert_le _ _).trans ?_
        rw [Finset.card_map]
    _ = L.ncard + 1 := by rw [Set.ncard_eq_toFinset_card L hfin]

open scoped Matrix.Norms.L2Operator in
/-- **The promise remark after `thm:semilattice-product`**: if every promise input
generates at most `K` nonempty joins, then
`ADV± ≤ 16√(n·min{n, ⌊log₂(K+1)⌋})` for the join of the letters read. -/
theorem advPMOn_joinMap_le_of_joinCount {K : ℕ} (m : σ → A) (read : X → ι → σ)
    (hK : ∀ x, (supClosure (Set.range fun i => m (read x i))).ncard ≤ K) :
    advPMOn read (fun x => joinMap m (read x))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * ((min (Fintype.card ι) (Nat.log 2 (K + 1)) : ℕ) : ℝ)) := by
  set B := min (Fintype.card ι) (Nat.log 2 (K + 1)) with hBdef
  have hcrit : ∀ (x : X) (T : Finset ι),
      (criticalSet (fun i => m (read x i)) T).card ≤ B := by
    intro x T
    refine le_min ((Finset.card_le_card (criticalSet_subset _ T)).trans
      (Finset.card_le_univ T)) (Nat.le_log_of_pow_le one_lt_two ?_)
    exact (two_pow_card_criticalSet_le_ncard _ T).trans (by have := hK x; omega)
  rcases Nat.eq_zero_or_pos B with hB0 | hB
  · -- `B = 0` forces `K = 0`, which no input meets: the promise is empty
    have hX : IsEmpty X := by
      refine ⟨fun x => ?_⟩
      have hlog : Nat.log 2 (K + 1) = 0 := by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega
      have hK0 : K = 0 := by
        by_contra hK0
        have : 1 ≤ Nat.log 2 (K + 1) := Nat.le_log_of_pow_le one_lt_two (by omega)
        omega
      have hne : (supClosure (Set.range fun i => m (read x i))).Nonempty :=
        ⟨_, subset_supClosure (Set.mem_range_self (Classical.arbitrary ι))⟩
      have hpos := (Set.ncard_pos ((Set.finite_range _).supClosure)).2 hne
      have := hK x
      omega
    refine (advPMOn_le fun Γ _ _ => ?_).trans (by positivity)
    rw [Subsingleton.elim Γ 0, norm_zero]
  · have h := advPMOn_joinMap_le_of_bound m hB read hcrit
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)] at h
    exact h

end Promise

/-! ## Index two and index `k` in the paper's shapes -/

section Index

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **`thm:index-two-width`, `eq:index-two-width`, for every finite `M`**:
`β_G(M) ≤ 5·log₂|M|` under `x³ = x²` (the trivial monoid included). -/
theorem breadth_le_five_logb (hx3 : ∀ z : M, z ^ 3 = z ^ 2) (m : σ → M) :
    (breadth m : ℝ) ≤ 5 * Real.logb 2 (Fintype.card M) := by
  rcases Nat.lt_or_ge (Fintype.card M) 2 with h1 | h2
  · have : IsAperiodicMonoid M := isAperiodicMonoid_of_cube_eq_sq hx3
    have hb : breadth m = 0 := by
      have := breadth_le_card_monoid m
      omega
    have hc : (1 : ℝ) ≤ Fintype.card M := by exact_mod_cast Fintype.card_pos
    rw [hb, Nat.cast_zero]
    have := Real.logb_nonneg one_lt_two hc
    positivity
  · exact (breadth_lt_five_logb hx3 h2 m).le

/-- **`thm:index-two-width`, `eq:index-two-adv`**:
`ADV±(Prod_{M,G,n}) ≤ 16√(n·min{n, 5·log₂|M|})` under `x³ = x²`. -/
theorem advPM_prodFun_le_indexTwo_min (hx3 : ∀ z : M, z ^ 3 = z ^ 2) (m : σ → M) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * min (Fintype.card ι : ℝ) (5 * Real.logb 2 (Fintype.card M))) := by
  have : IsAperiodicMonoid M := isAperiodicMonoid_of_cube_eq_sq hx3
  exact advPM_prodFun_le_of_breadth_le m (breadth_le_five_logb hx3 m)

/-- **`thm:index-two-width`, the query clause**, with its constant:
`Q_{1/3}(Prod_{M,G,n}) ≤ min{n, 2¹⁸·√(n·min{n, 5·log₂|M|})}` under `x³ = x²`. -/
theorem qQuery_prodFun_le_indexTwo_min (hx3 : ∀ z : M, z ^ 3 = z ^ 2) (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ)
          * min (Fintype.card ι : ℝ) (5 * Real.logb 2 (Fintype.card M)))) := by
  have : IsAperiodicMonoid M := isAperiodicMonoid_of_cube_eq_sq hx3
  exact qQuery_prodFun_le_min_of_breadth_le m (breadth_le_five_logb hx3 m)

/-- The BCW scale is at most `log₂|M| + 2`. -/
lemma bcwT_le_logb_add_two : (bcwT M : ℝ) ≤ Real.logb 2 (Fintype.card M) + 2 := by
  have hc : (1 : ℝ) ≤ Fintype.card M := by exact_mod_cast Fintype.card_pos
  have hL : 0 ≤ Real.logb 2 (Fintype.card M) := Real.logb_nonneg one_lt_two hc
  have hclog : (Nat.clog 2 (Fintype.card M) : ℝ) ≤ Real.logb 2 (Fintype.card M) + 1 := by
    rcases Nat.lt_or_ge (Fintype.card M) 2 with h1 | h2
    · rw [Nat.clog_of_right_le_one (by omega)]
      push_cast
      linarith
    · have hlt := Nat.pow_pred_clog_lt_self one_lt_two h2
      have hlt' : ((2 : ℝ) ^ (Nat.clog 2 (Fintype.card M) - 1)) < Fintype.card M := by
        exact_mod_cast hlt
      have hpos : 0 < Nat.clog 2 (Fintype.card M) := Nat.clog_pos one_lt_two h2
      have hlog : ((Nat.clog 2 (Fintype.card M) - 1 : ℕ) : ℝ)
          < Real.logb 2 (Fintype.card M) := by
        rw [Real.lt_logb_iff_rpow_lt one_lt_two (by positivity), Real.rpow_natCast]
        exact hlt'
      have : ((Nat.clog 2 (Fintype.card M) - 1 : ℕ) : ℝ)
          = (Nat.clog 2 (Fintype.card M) : ℝ) - 1 := by
        rw [Nat.cast_sub hpos, Nat.cast_one]
      linarith
  rw [bcwT, Nat.cast_max]
  push_cast
  exact max_le (by linarith) (by linarith)

/-- **`thm:index-k-width`, `eq:index-k-width`, in the paper's shape**: under
`x^{k+1} = x^k` with `k ≥ 1`,
`β_G(M) ≤ C·(k+1)·(log₂|M| + 1)·log(log₂|M| + 2)` with `C = 2⁶⁴` and `log` natural. -/
theorem breadth_le_indexK_paper {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k)
    (m : σ → M) :
    (breadth m : ℝ) ≤ 2 ^ 64 * ((k : ℝ) + 1) * (Real.logb 2 (Fintype.card M) + 1)
      * Real.log (Real.logb 2 (Fintype.card M) + 2) := by
  refine (breadth_le_bcw hxk hk m).trans ?_
  set L := Real.logb 2 (Fintype.card M) with hLdef
  have hc : (1 : ℝ) ≤ Fintype.card M := by exact_mod_cast Fintype.card_pos
  have hL : 0 ≤ L := Real.logb_nonneg one_lt_two hc
  set t : ℝ := (bcwT M : ℝ) with htdef
  have ht2 : (2 : ℝ) ≤ t := by
    rw [htdef]
    exact_mod_cast two_le_bcwT M
  have htL : t ≤ L + 2 := bcwT_le_logb_add_two
  -- `log₂ t ≤ 2·log(L+2)` since `log 2 > 1/2`
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogt : Real.logb 2 t ≤ 2 * Real.log (L + 2) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have h1 : Real.log t ≤ Real.log (L + 2) := Real.log_le_log (by linarith) htL
    have h0 : 0 ≤ Real.log (L + 2) := Real.log_nonneg (by linarith)
    nlinarith
  have hlt0 : 0 ≤ Real.logb 2 t := Real.logb_nonneg one_lt_two (by linarith)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have htt : t * Real.logb 2 t ≤ (2 * (L + 1)) * (2 * Real.log (L + 2)) :=
    mul_le_mul (by linarith) hlogt hlt0 (by linarith)
  calc 2 ^ 62 * ((k : ℝ) + 1) * t * Real.logb 2 t
      = 2 ^ 62 * ((k : ℝ) + 1) * (t * Real.logb 2 t) := by ring
    _ ≤ 2 ^ 62 * ((k : ℝ) + 1) * ((2 * (L + 1)) * (2 * Real.log (L + 2))) :=
        mul_le_mul_of_nonneg_left htt (by positivity)
    _ = 2 ^ 64 * ((k : ℝ) + 1) * (L + 1) * Real.log (L + 2) := by ring

/-- **`thm:index-k-width`, `eq:index-k-adv`, with its constant**: under `x^{k+1} = x^k`,
`ADV±(Prod_{M,G,n}) ≤ 16√(n·min{n, C(k+1)(log₂|M|+1)·log(log₂|M|+2)})`, `C = 2⁶⁴`. -/
theorem advPM_prodFun_le_indexK_min {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k)
    (hk : 0 < k) (m : σ → M) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * min (Fintype.card ι : ℝ)
          (2 ^ 64 * ((k : ℝ) + 1) * (Real.logb 2 (Fintype.card M) + 1)
            * Real.log (Real.logb 2 (Fintype.card M) + 2))) := by
  have : IsAperiodicMonoid M := ⟨fun a => ⟨k, hk, (hxk a).symm⟩⟩
  exact advPM_prodFun_le_of_breadth_le m (breadth_le_indexK_paper hxk hk m)

/-- **`thm:index-k-width`, the query clause**, with its constants:
`Q_{1/3}(Prod_{M,G,n}) ≤ min{n, 2¹⁸·√(n·min{n, b})}` with
`b = 2⁶⁴(k+1)(log₂|M|+1)·log(log₂|M|+2)`. -/
theorem qQuery_prodFun_le_indexK_min {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k)
    (hk : 0 < k) (m : σ → M) :
    (qQuery (fun x : ι → σ => ∏ i, m (x i)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (2 ^ 18 * Real.sqrt ((Fintype.card ι : ℝ)
          * min (Fintype.card ι : ℝ)
            (2 ^ 64 * ((k : ℝ) + 1) * (Real.logb 2 (Fintype.card M) + 1)
              * Real.log (Real.logb 2 (Fintype.card M) + 2)))) := by
  have : IsAperiodicMonoid M := ⟨fun a => ⟨k, hk, (hxk a).symm⟩⟩
  exact qQuery_prodFun_le_min_of_breadth_le m (breadth_le_indexK_paper hxk hk m)

end Index

/-! ## `prop:comm-jtrivial`: hence `R`- and `L`-trivial -/

section Trivial

variable {M : Type} [CommMonoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **`prop:comm-jtrivial`, `R`-clause**: a finite commutative aperiodic monoid is
`R`-trivial. -/
theorem isRTrivialMonoid_of_comm : IsRTrivialMonoid M := by
  intro a b h
  obtain ⟨q, hq⟩ := mem_rightIdeal.1 (h ▸ self_mem_rightIdeal a : a ∈ rightIdeal b)
  obtain ⟨q', hq'⟩ := mem_rightIdeal.1 (h.symm ▸ self_mem_rightIdeal b : b ∈ rightIdeal a)
  have h3 : a * (q' * q) = a := by rw [← mul_assoc, hq', hq]
  rw [← hq', mul_right_absorb h3]

/-- **`prop:comm-jtrivial`, `L`-clause**: in a finite commutative aperiodic monoid equal
principal left ideals force equal elements (`L`-triviality, stated concretely as in
`not_isLTrivial_dyckNF`; the library has no `L`-trivial predicate). -/
theorem leftIdeal_injective_of_comm : ∀ a b : M, leftIdeal a = leftIdeal b → a = b := by
  intro a b h
  refine isRTrivialMonoid_of_comm a b ?_
  ext z
  simp only [mem_rightIdeal]
  have hz := congrArg (z ∈ ·) h
  simp only [mem_leftIdeal, eq_iff_iff] at hz
  simpa only [mul_comm] using hz

end Trivial

/-! ## `cor:jtrivial-division`, second form -/

section JTrivial

/-- **`cor:jtrivial-division`, second form**:
`Q_{1/3}(Prod_{M,n}) ≤ min{n, 147456·τ(M)·√n}` for every finite `𝓙`-trivial monoid, from
the first form (`jtrivial_qQuery_le_min`) and `C(τ,2) ≤ τ²`. -/
theorem jtrivial_qQuery_le_min_tau {M : Type} [Monoid M] [Fintype M] [DecidableEq M]
    (hJ : IsJTrivialMonoid M) {n : ℕ} (hn : 1 ≤ n) :
    (qQuery (fun w : Fin n → M => wordProd id w) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (147456 * (tau M hJ : ℝ) * Real.sqrt n) := by
  refine (jtrivial_qQuery_le_min hJ hn).trans (min_le_min_left _ ?_)
  have hc : ((min n ((tau M hJ).choose 2) : ℕ) : ℝ) ≤ (tau M hJ : ℝ) ^ 2 := by
    have : min n ((tau M hJ).choose 2) ≤ tau M hJ ^ 2 :=
      (min_le_right _ _).trans (Nat.choose_le_pow _ _)
    exact_mod_cast this
  have hs : Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))
      ≤ (tau M hJ : ℝ) * Real.sqrt n := by
    calc Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))
        ≤ Real.sqrt ((n : ℝ) * (tau M hJ : ℝ) ^ 2) := by gcongr
      _ = (tau M hJ : ℝ) * Real.sqrt n := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _), mul_comm]
  calc 147456 * Real.sqrt ((n : ℝ) * ((min n ((tau M hJ).choose 2) : ℕ) : ℝ))
      ≤ 147456 * ((tau M hJ : ℝ) * Real.sqrt n) := by gcongr
    _ = 147456 * (tau M hJ : ℝ) * Real.sqrt n := by ring

end JTrivial

end MonoidProduct
