import MonoidProduct.Width.Main
import MonoidProduct.Aperiodic.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The subset-product summary, and the `|M| - 1` width fallback

The commutative section of `monoid.tex` (`sec:lattice`) instantiates the essential-width theorem with the
**subset product**: for a finite commutative monoid `M` and a value map
`m : σ → M`, the state of a revealed set is the product of its values.
Commutativity makes the `Finset`-indexed product a well-defined summary with no
work; the essential positions of `T` are those whose deletion changes the
product (`eq:product-essential`).

The general transfer is `advPM_prodFun_le_of_width` (the paper's `eq:comm-width`):
any bound `B` on the essential width gives `ADV± ≤ 16√(nB)`.  All the algebra
of the section then goes into bounding the width.

This file proves an elementary **fallback** bound: in a finite commutative
*aperiodic* monoid the width is at most `|M| - 1`.  The proof is an ideal
chain: adding an essential factor **strictly** shrinks the principal ideal of
the running product.  Strictness rests on two facts.

* **Absorption** (`mul_right_absorb`): `r·(ab) = r` forces `r·a = r`.  Iterate
  to `r·aᴺbᴺ = r` at a stabilisation exponent of `a`; then
  `r·a = r·aᴺ⁺¹bᴺ = r·aᴺbᴺ = r`.  This replaces both the Sandwich lemma and
  `J`-triviality in the paper's development — equal principal ideals give
  `z = z·a·w`, and absorption alone yields `z·a = z`.
* **Edge lifting** (`ctxProd_ne_erase`): an absorption at a *sub*product lifts
  to the full set by multiplying in the remaining factors, contradicting
  essentiality at the top.

A strictly decreasing chain of `|E| + 1` nonempty subsets of `M` then forces
`|E| ≤ |M| - 1`.

The product breadth `β` (`eq:monoid-beta`) is formalized separately in
`Width/Breadth.lean`, which proves `κ = β` (`lem:comm-beta-width`); the width
bound here is what the corollaries consume.
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {M : Type*} [Fintype M] [DecidableEq M] [CommMonoid M]

/-! ## The summary -/

/-- **The subset-product summary**: the state of a revealed set is the product
of its values.  Order-independence is the `Finset` product. -/
def prodSummary (m : σ → M) : IncrementalSummary ι σ M M where
  state x T := ∏ j ∈ T, m (x j)
  out x := ∏ j, m (x j)
  state_empty x y := by simp
  state_insert x y T i hi hstate hxy := by
    rw [Finset.prod_insert hi, Finset.prod_insert hi, hxy, hstate]
  out_congr _ _ h := h

/-- **The essential positions of the subset product**, spelled out. -/
def prodEss (m : σ → M) (x : ι → σ) (T : Finset ι) : Finset ι :=
  (prodSummary (ι := ι) m).essentialSet x T

lemma mem_prodEss {m : σ → M} {x : ι → σ} {T : Finset ι} {i : ι} :
    i ∈ prodEss m x T
      ↔ i ∈ T ∧ ∏ j ∈ T, m (x j) ≠ ∏ j ∈ T.erase i, m (x j) :=
  IncrementalSummary.mem_essentialSet

lemma prodEss_subset (m : σ → M) (x : ι → σ) (T : Finset ι) :
    prodEss m x T ⊆ T :=
  (prodSummary (ι := ι) m).essentialSet_subset x T

/-- **The general width transfer** (`eq:comm-width`): a width bound gives
`ADV±(∏) ≤ 16√(nB)`. -/
theorem advPM_prodFun_le_of_width (m : σ → M) {B : ℕ} (hB : 0 < B)
    (hw : ∀ (x : ι → σ) (T : Finset ι), (prodEss m x T).card ≤ B) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * B) :=
  advPM_le_of_summary (prodSummary (ι := ι) (σ := σ) m) hB hw

/-! ## The context product

For `S` inside the essential set, `ctxProd S` is the product with all
*non-essential* positions of `T` present and only the essential positions of
`S` added.  Every subset-cube computation of the paper is about these. -/

/-- The product with the non-essential context and the essential positions of
`S`. -/
def ctxProd (m : σ → M) (x : ι → σ) (T S : Finset ι) : M :=
  (∏ j ∈ T \ prodEss m x T, m (x j)) * ∏ j ∈ S, m (x j)

section Ctx

variable (m : σ → M) (x : ι → σ) (T : Finset ι)

lemma ctxProd_insert {S : Finset ι} {i : ι} (hi : i ∉ S) :
    ctxProd m x T (insert i S) = ctxProd m x T S * m (x i) := by
  rw [ctxProd, ctxProd, Finset.prod_insert hi]
  ac_rfl

/-- Multiplying in the missing essential factors recovers the full product. -/
lemma ctxProd_mul_sdiff {S : Finset ι} (hS : S ⊆ prodEss m x T) :
    ctxProd m x T S * ∏ j ∈ prodEss m x T \ S, m (x j) = ∏ j ∈ T, m (x j) := by
  rw [ctxProd, mul_assoc, mul_comm (∏ j ∈ S, m (x j)),
    Finset.prod_sdiff hS, Finset.prod_sdiff (prodEss_subset m x T)]

lemma erase_sdiff_erase_of_mem {E T : Finset ι} {i : ι} (hE : E ⊆ T) (hi : i ∈ E) :
    T.erase i \ E.erase i = T \ E := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_erase, not_and]
  constructor
  · rintro ⟨⟨hji, hjT⟩, hj⟩
    exact ⟨hjT, hj hji⟩
  · rintro ⟨hjT, hjE⟩
    have hji : j ≠ i := fun h => hjE (h ▸ hi)
    exact ⟨⟨hji, hjT⟩, fun _ => hjE⟩

/-- The full product with `i` erased, through the context. -/
lemma ctxProd_erase_mul_sdiff {S : Finset ι} {i : ι} (hS : S ⊆ prodEss m x T)
    (hi : i ∈ S) :
    ctxProd m x T (S.erase i) * ∏ j ∈ prodEss m x T \ S, m (x j)
      = ∏ j ∈ T.erase i, m (x j) := by
  have hiE : i ∈ prodEss m x T := hS hi
  have h1 : prodEss m x T \ S = (prodEss m x T).erase i \ S.erase i := by
    rw [erase_sdiff_erase_of_mem hS hi]
  have h2 : T.erase i \ (prodEss m x T).erase i = T \ prodEss m x T :=
    erase_sdiff_erase_of_mem (prodEss_subset m x T) hiE
  rw [ctxProd, h1, mul_assoc, mul_comm (∏ j ∈ S.erase i, m (x j)),
    Finset.prod_sdiff (Finset.erase_subset_erase i hS), ← h2,
    Finset.prod_sdiff (Finset.erase_subset_erase i (prodEss_subset m x T))]

/-- **Edge strictness**: deleting an essential position from any subset of the
essential set changes the context product — an equality would lift to the full
set. -/
lemma ctxProd_ne_erase {S : Finset ι} {i : ι} (hS : S ⊆ prodEss m x T)
    (hi : i ∈ S) : ctxProd m x T S ≠ ctxProd m x T (S.erase i) := by
  intro h
  have hiE : i ∈ prodEss m x T := hS hi
  refine (mem_prodEss.mp hiE).2 ?_
  rw [← ctxProd_mul_sdiff m x T hS, h, ctxProd_erase_mul_sdiff m x T hS hi]

end Ctx

/-! ## Absorption -/

/-- **Absorption**: in a commutative aperiodic monoid, `r·(ab) = r` forces
`r·a = r`.  Iterate to a stabilisation exponent of `a` and absorb one more
copy. -/
lemma mul_right_absorb [IsAperiodicMonoid M] {r a b : M}
    (h : r * (a * b) = r) : r * a = r := by
  obtain ⟨N, -, hN⟩ := IsAperiodicMonoid.stabilizes a
  have hk : ∀ k : ℕ, r * (a * b) ^ k = r := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, h]
  have hNN : r * (a ^ N * b ^ N) = r := by
    rw [← mul_pow]
    exact hk N
  have hswap : a ^ N * b ^ N * a = a ^ (N + 1) * b ^ N := by
    rw [pow_succ]
    ac_rfl
  calc r * a = r * (a ^ N * b ^ N) * a := by rw [hNN]
    _ = r * (a ^ N * b ^ N * a) := by rw [mul_assoc]
    _ = r * (a ^ (N + 1) * b ^ N) := by rw [hswap]
    _ = r * (a ^ N * b ^ N) := by rw [← hN]
    _ = r := hNN

/-! ## Principal ideals, as finsets -/

/-- The principal ideal of `z`, as a finset. -/
def mulIdeal (z : M) : Finset M := Finset.univ.image (fun w => z * w)

lemma mem_mulIdeal {z u : M} : u ∈ mulIdeal z ↔ ∃ w, z * w = u := by
  simp [mulIdeal]

lemma self_mem_mulIdeal (z : M) : z ∈ mulIdeal z :=
  mem_mulIdeal.mpr ⟨1, mul_one z⟩

lemma mulIdeal_mul_subset (z a : M) : mulIdeal (z * a) ⊆ mulIdeal z := by
  intro u hu
  obtain ⟨w, hw⟩ := mem_mulIdeal.mp hu
  exact mem_mulIdeal.mpr ⟨a * w, by rw [← mul_assoc]; exact hw⟩

/-- **Equal principal ideals give absorption.**  This is where the paper's
`J`-triviality (`prop:comm-jtrivial`) is used, in exactly the instance needed. -/
lemma mul_eq_of_mulIdeal_eq [IsAperiodicMonoid M] {z a : M}
    (h : mulIdeal (z * a) = mulIdeal z) : z * a = z := by
  have hz : z ∈ mulIdeal (z * a) := h ▸ self_mem_mulIdeal z
  obtain ⟨w, hw⟩ := mem_mulIdeal.mp hz
  rw [mul_assoc] at hw
  exact mul_right_absorb hw

/-! ## The ideal chain -/

section Chain

variable [IsAperiodicMonoid M] (m : σ → M) (x : ι → σ) (T : Finset ι)

/-- **Adding an essential factor strictly shrinks the ideal**, and the drops
accumulate: `|S|` essential factors cost `|S|` elements of the ideal. -/
lemma card_add_card_mulIdeal_le :
    ∀ S : Finset ι, S ⊆ prodEss m x T →
      S.card + (mulIdeal (ctxProd m x T S)).card
        ≤ (mulIdeal (ctxProd m x T ∅)).card := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert e S he ih =>
      intro hSE
      have hS : S ⊆ prodEss m x T :=
        (Finset.subset_insert e S).trans hSE
      have heq : ctxProd m x T (insert e S) = ctxProd m x T S * m (x e) :=
        ctxProd_insert m x T he
      have hstep : mulIdeal (ctxProd m x T (insert e S))
          ⊂ mulIdeal (ctxProd m x T S) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨heq ▸ mulIdeal_mul_subset _ _, fun habs => ?_⟩
        have habsorb : ctxProd m x T S * m (x e) = ctxProd m x T S :=
          mul_eq_of_mulIdeal_eq (by rw [← heq]; exact habs)
        refine ctxProd_ne_erase m x T hSE (Finset.mem_insert_self e S) ?_
        rw [heq, habsorb, Finset.erase_insert he]
      have hcard := Finset.card_lt_card hstep
      have hih := ih hS
      rw [Finset.card_insert_of_notMem he]
      omega

/-- **The width fallback** (elementary ideal-chain bound): in a finite
commutative aperiodic monoid the essential width is at most `|M| - 1`. -/
theorem card_prodEss_le_card_monoid :
    (prodEss m x T).card ≤ Fintype.card M - 1 := by
  have h := card_add_card_mulIdeal_le m x T (prodEss m x T) subset_rfl
  have h1 : 0 < (mulIdeal (ctxProd m x T (prodEss m x T))).card :=
    Finset.card_pos.mpr ⟨_, self_mem_mulIdeal _⟩
  have h2 : (mulIdeal (ctxProd m x T ∅)).card ≤ Fintype.card M :=
    Finset.card_le_univ _
  omega

end Chain

/-- **`ADV±(∏) ≤ 16√(n(|M|-1))`** for a finite commutative aperiodic monoid —
the fallback instantiation of the essential-width theorem. -/
theorem advPM_prodFun_le_card_monoid [IsAperiodicMonoid M]
    (hM : 2 ≤ Fintype.card M) (m : σ → M) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ) * ((Fintype.card M : ℝ) - 1)) := by
  have h := advPM_prodFun_le_of_width (ι := ι) (σ := σ) m
    (B := Fintype.card M - 1) (by omega)
    (fun x T => card_prodEss_le_card_monoid m x T)
  have hcast : ((Fintype.card M - 1 : ℕ) : ℝ) = (Fintype.card M : ℝ) - 1 := by
    have : 1 ≤ Fintype.card M := by omega
    push_cast [Nat.cast_sub this]
    ring
  rwa [hcast] at h

end MonoidProduct
