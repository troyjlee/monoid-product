import MonoidProduct.Width.BreadthBounds
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The elementary index-`k` breadth bound (`monoid.tex`, `eq:elementary-index-k`)

The comparison estimate stated after `thm:index-k-width` in `monoid.tex`: the
classical Erdős–Rado sunflower lemma, in place of the Bell–Chueluecha–Warnke
bound, gives for a finite commutative monoid with `x^{k+1} = x^k`
`β_G(M) < 2k(log₂|M| + 1)²`.

* `erdosRado_card_le` — the **Erdős–Rado sunflower lemma** for the library's
  sunflower notions (`HasSunflower`, `Width/ProductSunflower.lean`): a
  `t`-uniform family with no `(k+1)`-sunflower has at most `t!·k^t` members.
  Proof by induction on `t`: a maximum pairwise-disjoint subfamily has at most
  `k` members (else it is a sunflower with empty kernel), so its union `U` has
  at most `k·t` points; every member meets `U`, and the link of each point is
  a `(t-1)`-uniform sunflower-free family.
* `erdosRado_choose_le` — the fiber partition (`choose_le_card_mul_of_fiber_card_le`)
  with the Erdős–Rado fiber bound: `C(B, t) ≤ |M|·t!·k^t`.
* `erdosRado_card_prodEss_lt` — at `t = ⌊log₂|M|⌋ + 1` (`erdosRadoT`), the
  paper's arithmetic `B^t ≤ t^t·C(B,t) ≤ t^t·|M|·t!·k^t < (2kt²)^t`, all in `ℕ`
  (using `|M| < 2^t` and `t! ≤ t^t`), hence `κ < 2kt²`.
* Breadth forms: `erdosRado_isBreadthBound` (every word has a core of fewer than
  `2kt²` positions), `erdosRado_card_lt_of_shortest_core` (every *shortest*
  core has length `< 2kt²`, the paper's phrasing), and the headline
  `erdosRado_breadth_lt : β < 2k(log₂|M| + 1)²` (`eq:elementary-index-k`).

Comparison with the library's index-`k` bound `breadth_le_bcw`
(`β ≤ 2⁶²(k+1)·t·log₂ t`, `t = max 2 ⌈log₂|M|⌉`): the Erdős–Rado estimate has
an extra factor `t` in place of `log₂ t` (from `(t!)^{1/t} ≤ t`) but constant
`2` instead of `2⁶²`; the constant needed no adjustment from the paper.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open Finset
open scoped Nat

/-! ## The Erdős–Rado sunflower lemma -/

section ErdosRado

variable {α : Type*} [DecidableEq α]

/-- `k + 1` pairwise disjoint sets form a sunflower with empty kernel. -/
lemma erdosRado_hasSunflower_of_pairwiseDisjoint {k : ℕ} {𝒟 : Finset (Finset α)}
    (hD : ∀ S ∈ 𝒟, ∀ T ∈ 𝒟, S ≠ T → Disjoint S T) (hk : k + 1 ≤ 𝒟.card) :
    HasSunflower (k + 1) 𝒟 := by
  obtain ⟨𝒮, hsub, hcard⟩ := Finset.exists_subset_card_eq hk
  refine ⟨𝒮, hsub, hcard, ∅, ?_⟩
  intro S hS T hT hST
  exact Finset.disjoint_iff_inter_eq_empty.mp (hD S (hsub hS) T (hsub hT) hST)

/-- A sunflower in the link of `a` lifts (by re-inserting `a`) to a sunflower of the
same size in the family. -/
lemma erdosRado_hasSunflower_of_link {k : ℕ} {𝓕 : Finset (Finset α)} (a : α)
    (h : HasSunflower (k + 1) ((𝓕.filter (a ∈ ·)).image (·.erase a))) :
    HasSunflower (k + 1) 𝓕 := by
  obtain ⟨𝒮, hsub, hcard, K, hK⟩ := h
  have hmem : ∀ S ∈ 𝒮, insert a S ∈ 𝓕 ∧ a ∉ S := by
    intro S hS
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp (hsub hS)
    obtain ⟨hF𝓕, haF⟩ := Finset.mem_filter.mp hF
    exact ⟨by rw [Finset.insert_erase haF]; exact hF𝓕, Finset.notMem_erase a F⟩
  have hinj : Set.InjOn (insert a) (𝒮 : Set (Finset α)) := by
    intro S hS T hT hST
    have h' := congrArg (·.erase a) hST
    simpa only [Finset.erase_insert (hmem S hS).2, Finset.erase_insert (hmem T hT).2]
      using h'
  refine ⟨𝒮.image (insert a), ?_, ?_, insert a K, ?_⟩
  · intro F hF
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hF
    exact (hmem S hS).1
  · rw [Finset.card_image_of_injOn hinj, hcard]
  · intro F hF G hG hFG
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hG
    have hST : S ≠ T := fun h => hFG (h ▸ rfl)
    rw [← Finset.insert_inter_distrib, hK hS hT hST]

/-- **The Erdős–Rado sunflower lemma**: a `t`-uniform family with no
`(k+1)`-sunflower has at most `t!·k^t` members. -/
theorem erdosRado_card_le (k : ℕ) : ∀ (t : ℕ) (𝓕 : Finset (Finset α)),
    (∀ S ∈ 𝓕, S.card = t) → ¬ HasSunflower (k + 1) 𝓕 → 𝓕.card ≤ t ! * k ^ t := by
  intro t
  induction t with
  | zero =>
    intro 𝓕 hu _
    have hsub : 𝓕 ⊆ {∅} := fun S hS =>
      Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (hu S hS))
    simpa using Finset.card_le_card hsub
  | succ t ih =>
    intro 𝓕 hu hsf
    -- a pairwise-disjoint subfamily of maximum size
    set 𝒬 := 𝓕.powerset.filter fun 𝒟 => ∀ S ∈ 𝒟, ∀ T ∈ 𝒟, S ≠ T → Disjoint S T
      with h𝒬def
    have h𝒬 : 𝒬.Nonempty := ⟨∅, by simp [𝒬]⟩
    obtain ⟨𝒟, h𝒟, hmax⟩ := Finset.exists_max_image 𝒬 Finset.card h𝒬
    obtain ⟨h𝒟F, h𝒟d⟩ := Finset.mem_filter.mp h𝒟
    rw [Finset.mem_powerset] at h𝒟F
    have hDk : 𝒟.card ≤ k := by
      by_contra hlt
      obtain ⟨𝒮, hs, h⟩ :=
        erdosRado_hasSunflower_of_pairwiseDisjoint h𝒟d (k := k) (by omega)
      exact hsf ⟨𝒮, hs.trans h𝒟F, h⟩
    set U := 𝒟.biUnion id with hUdef
    have hU : U.card ≤ k * (t + 1) := by
      calc U.card ≤ ∑ D ∈ 𝒟, (id D).card := Finset.card_biUnion_le
        _ = ∑ _D ∈ 𝒟, (t + 1) := Finset.sum_congr rfl fun D hD => hu D (h𝒟F hD)
        _ = 𝒟.card * (t + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ k * (t + 1) := Nat.mul_le_mul_right _ hDk
    -- every member meets `U`, by maximality
    have hmeet : ∀ S ∈ 𝓕, ∃ a ∈ U, a ∈ S := by
      intro S hS
      by_cases hSD : S ∈ 𝒟
      · obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by rw [hu S hS]; omega)
        exact ⟨a, Finset.mem_biUnion.mpr ⟨S, hSD, ha⟩, ha⟩
      · by_contra hno
        push Not at hno
        have hdisj : ∀ D ∈ 𝒟, Disjoint S D := by
          intro D hD
          rw [Finset.disjoint_left]
          intro a haS haD
          exact hno a (Finset.mem_biUnion.mpr ⟨D, hD, haD⟩) haS
        have hins : insert S 𝒟 ∈ 𝒬 := by
          refine Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (Finset.insert_subset hS h𝒟F), ?_⟩
          intro A hA B hB hAB
          rw [Finset.mem_insert] at hA hB
          rcases hA with rfl | hA <;> rcases hB with rfl | hB
          · exact absurd rfl hAB
          · exact hdisj B hB
          · exact (hdisj A hA).symm
          · exact h𝒟d A hA B hB hAB
        have h' := hmax _ hins
        rw [Finset.card_insert_of_notMem hSD] at h'
        omega
    -- each link is `t`-uniform and sunflower-free
    have hlink : ∀ a, (𝓕.filter (a ∈ ·)).card ≤ t ! * k ^ t := by
      intro a
      have hinj : Set.InjOn (·.erase a) ((𝓕.filter (a ∈ ·)) : Set (Finset α)) := by
        intro S hS T hT hST
        have hS' := (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).2
        have hT' := (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).2
        rw [← Finset.insert_erase hS', ← Finset.insert_erase hT']
        exact congrArg (insert a) hST
      rw [← Finset.card_image_of_injOn hinj]
      apply ih
      · intro S hS
        obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hS
        obtain ⟨hF𝓕, haF⟩ := Finset.mem_filter.mp hF
        rw [Finset.card_erase_of_mem haF, hu F hF𝓕]
        rfl
      · exact fun h => hsf (erdosRado_hasSunflower_of_link a h)
    have hcover : 𝓕 ⊆ U.biUnion fun a => 𝓕.filter (a ∈ ·) := by
      intro S hS
      obtain ⟨a, haU, haS⟩ := hmeet S hS
      exact Finset.mem_biUnion.mpr ⟨a, haU, Finset.mem_filter.mpr ⟨hS, haS⟩⟩
    calc 𝓕.card ≤ (U.biUnion fun a => 𝓕.filter (a ∈ ·)).card := Finset.card_le_card hcover
      _ ≤ ∑ a ∈ U, (𝓕.filter (a ∈ ·)).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ U, t ! * k ^ t := Finset.sum_le_sum fun a _ => hlink a
      _ = U.card * (t ! * k ^ t) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (k * (t + 1)) * (t ! * k ^ t) := Nat.mul_le_mul_right _ hU
      _ = (t + 1)! * k ^ (t + 1) := by rw [Nat.factorial_succ, pow_succ]; ring

end ErdosRado

/-! ## The evaluation scale `t = ⌊log₂|M|⌋ + 1` -/

/-- The scale of the elementary bound: `⌊log₂|M|⌋ + 1`, so that `|M| < 2^t`. -/
def erdosRadoT (M : Type*) [Fintype M] : ℕ := Nat.log 2 (Fintype.card M) + 1

lemma one_le_erdosRadoT (M : Type*) [Fintype M] : 1 ≤ erdosRadoT M :=
  Nat.le_add_left _ _

lemma card_lt_two_pow_erdosRadoT (M : Type*) [Fintype M] :
    Fintype.card M < 2 ^ erdosRadoT M :=
  Nat.lt_pow_succ_log_self (by norm_num) _

lemma erdosRadoT_le_logb (M : Type*) [Fintype M] :
    (erdosRadoT M : ℝ) ≤ Real.logb 2 (Fintype.card M) + 1 := by
  have h := Real.natLog_le_logb (Fintype.card M) 2
  push_cast at h
  unfold erdosRadoT
  push_cast
  linarith

/-! ## The width bound -/

section Width

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {M : Type*} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- **The Erdős–Rado fiber partition**: `C(B, t) ≤ |M|·t!·k^t` for the essential
set of size `B`, at every `t`. -/
theorem erdosRado_choose_le {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k)
    (m : σ → M) (x : ι → σ) (T : Finset ι) (t : ℕ) :
    (prodEss m x T).card.choose t ≤ Fintype.card M * (t ! * k ^ t) :=
  choose_le_card_mul_of_fiber_card_le m x T fun z =>
    erdosRado_card_le k t _ (fun _ hS => ((mem_prodFiber m x T).mp hS).1.2)
      (not_hasSunflower_prodFiber m x T hxk hk z t)

/-- **`κ < 2kt²`** at `t = ⌊log₂|M|⌋ + 1`: the essential set of the subset product
has fewer than `2k(⌊log₂|M|⌋ + 1)²` positions. -/
theorem erdosRado_card_prodEss_lt {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k)
    (hk : 0 < k) (m : σ → M) (x : ι → σ) (T : Finset ι) :
    (prodEss m x T).card < 2 * k * erdosRadoT M ^ 2 := by
  set t := erdosRadoT M with htdef
  set B := (prodEss m x T).card with hBdef
  have ht : 1 ≤ t := one_le_erdosRadoT M
  rcases lt_or_ge B t with hBt | htB
  · calc B < t := hBt
      _ ≤ 2 * k * t ^ 2 := by nlinarith
  · have h1 : B ^ t ≤ t ^ t * B.choose t := pow_le_pow_mul_choose htB
    have h2 := erdosRado_choose_le hxk hk m x T t
    have h3 : t ! ≤ t ^ t := Nat.factorial_le_pow t
    have hM : Fintype.card M < 2 ^ t := card_lt_two_pow_erdosRadoT M
    have hX : 0 < t ! * k ^ t := Nat.mul_pos (Nat.factorial_pos t) (Nat.pow_pos hk)
    have htt : 0 < t ^ t := Nat.pow_pos (by omega)
    have hlt : B ^ t < (2 * k * t ^ 2) ^ t := by
      calc B ^ t ≤ t ^ t * (Fintype.card M * (t ! * k ^ t)) :=
            h1.trans (Nat.mul_le_mul_left _ h2)
        _ < t ^ t * (2 ^ t * (t ! * k ^ t)) :=
            Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hM hX) htt
        _ ≤ t ^ t * (2 ^ t * (t ^ t * k ^ t)) := by gcongr
        _ = (2 * k * t ^ 2) ^ t := by rw [mul_pow, mul_pow, sq, mul_pow]; ring
    exact lt_of_pow_lt_pow_left₀ t (Nat.zero_le _) hlt

/-- The real form: `κ < 2k(log₂|M| + 1)²`. -/
theorem erdosRado_card_prodEss_lt_logb {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k)
    (hk : 0 < k) (m : σ → M) (x : ι → σ) (T : Finset ι) :
    ((prodEss m x T).card : ℝ) < 2 * k * (Real.logb 2 (Fintype.card M) + 1) ^ 2 := by
  have h := erdosRado_card_prodEss_lt hxk hk m x T
  have hlog := erdosRadoT_le_logb M
  have ht0 : (0 : ℝ) ≤ erdosRadoT M := Nat.cast_nonneg _
  calc ((prodEss m x T).card : ℝ) < ((2 * k * erdosRadoT M ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast h
    _ = 2 * k * (erdosRadoT M : ℝ) ^ 2 := by push_cast; ring
    _ ≤ 2 * k * (Real.logb 2 (Fintype.card M) + 1) ^ 2 := by gcongr

end Width

/-! ## Breadth forms (`eq:elementary-index-k`) -/

section Breadth

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- Every word has a core of fewer than `2kt²` positions, `t = ⌊log₂|M|⌋ + 1`. -/
theorem erdosRado_isBreadthBound {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k)
    (hk : 0 < k) (m : σ → M) :
    IsBreadthBound m (2 * k * erdosRadoT M ^ 2 - 1) := by
  apply isBreadthBound_of_width
  intro n x T
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [card_prodEss_fin_zero]
    exact Nat.zero_le _
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have := erdosRado_card_prodEss_lt hxk hk m x T
    omega

/-- **Every shortest core has length `B < 2kt²`** — the paper's phrasing of
`eq:elementary-index-k`, with `t = ⌊log₂|M|⌋ + 1`.  (Only minimality is used:
the bound holds for any `v` no longer than every core.) -/
theorem erdosRado_card_lt_of_shortest_core {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k)
    (hk : 0 < k) (m : σ → M) {n : ℕ} (x : Fin n → σ) {v : Finset (Fin n)}
    (_hv : IsCore m x v) (hmin : ∀ w, IsCore m x w → v.card ≤ w.card) :
    v.card < 2 * k * erdosRadoT M ^ 2 := by
  obtain ⟨u, hu, huc⟩ := erdosRado_isBreadthBound hxk hk m n x
  have hpos : 0 < 2 * k * erdosRadoT M ^ 2 :=
    Nat.mul_pos (by omega) (Nat.pow_pos (one_le_erdosRadoT M))
  have := hmin u huc
  omega

/-- **`β < 2k(log₂|M| + 1)²`** under `x^{k+1} = x^k` (`monoid.tex`,
`eq:elementary-index-k`): the Erdős–Rado comparison to `breadth_le_bcw`. -/
theorem erdosRado_breadth_lt {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k)
    (m : σ → M) :
    (breadth m : ℝ) < 2 * k * (Real.logb 2 (Fintype.card M) + 1) ^ 2 := by
  have hpos : 0 < 2 * k * erdosRadoT M ^ 2 :=
    Nat.mul_pos (by omega) (Nat.pow_pos (one_le_erdosRadoT M))
  have hb : breadth m < 2 * k * erdosRadoT M ^ 2 := by
    have := breadth_le (erdosRado_isBreadthBound hxk hk m)
    omega
  have hlog := erdosRadoT_le_logb M
  have ht0 : (0 : ℝ) ≤ erdosRadoT M := Nat.cast_nonneg _
  calc (breadth m : ℝ) < ((2 * k * erdosRadoT M ^ 2 : ℕ) : ℝ) := by exact_mod_cast hb
    _ = 2 * k * (erdosRadoT M : ℝ) ^ 2 := by push_cast; ring
    _ ≤ 2 * k * (Real.logb 2 (Fintype.card M) + 1) ^ 2 := by gcongr

end Breadth


end MonoidProduct
