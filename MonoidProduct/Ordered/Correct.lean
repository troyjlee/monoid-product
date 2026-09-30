import MonoidProduct.Ordered.Summary
import MonoidProduct.Ordered.PiProb

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# Correctness of rank summaries

The rank-`(r+1)` summary of `(j+1, q)` is an `(r+1)`-summary whenever, at every
depth `d ≤ j`, the merger output dominates all but a `1/(2·2^d)` mass of the
depth-`d` candidates (`isSummary_of_smallMass`).  The argument is deterministic
once the children's failure masses are at most `1/100`:

* the empty subword is least;
* a singleton is covered at depth `j`, where both children are exact letters, so
  every candidate at its node dominates it (mass `1/2^j`);
* a subword with at least two positions is split at the least common ancestor of
  its extreme positions (`exists_lca`); each side has at most `r` positions, so the
  candidates at that node whose two child summaries are correct dominate it, and
  they have mass at least `(98/100)/2^d > 1/(2·2^d)` (`sum_unifW_and_ge`).

The failure mass of a rank-`r` summary is then at most `1/100` for every rank and
every interval (`summary_correct`): the seeded merger's small-mass bound
(`seeded_small_mass`) gives `1/(100N)` per depth under the parameter hypothesis
`GoodParams`, and a union bound over the at most `N` depths finishes.
-/

namespace MonoidProduct

open Finset FiniteProb QuantumQueryComplexity Seeded

section Correct

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [PartialOrder M] [DecidableEq M]
variable [DecidableLE M] (letter : σ → M) {N : ℕ}

/-- `Fin (2^d)` is nonempty; stated as an instance so that seed spaces are found nonempty
without evaluating `2^d`. -/
instance instNonemptyFinTwoPow (d : ℕ) : Nonempty (Fin (2 ^ d)) := ⟨⟨0, Nat.two_pow_pos d⟩⟩

/-! ## Node arithmetic -/

lemma div_eq_iff_aux {m n k : ℕ} (hn : 0 < n) : m / n = k ↔ k * n ≤ m ∧ m < (k + 1) * n := by
  constructor
  · rintro rfl
    exact ⟨(Nat.le_div_iff_mul_le hn).1 le_rfl, (Nat.div_lt_iff_lt_mul hn).1 (Nat.lt_succ_self _)⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hn).2 h2))
      ((Nat.le_div_iff_mul_le hn).2 h1)

/-- The index of the depth-`d` node of `(j+1, q)` containing position `i`. -/
def nodeAt (j q d i : ℕ) : ℕ := (i - q * 2 ^ (j + 1)) / 2 ^ (j + 1 - d)

lemma nodeAt_zero {j q : ℕ} {i : Fin N} (hi : i ∈ ivl (j + 1) q) : nodeAt j q 0 (i : ℕ) = 0 := by
  rw [mem_ivl] at hi
  unfold nodeAt
  rw [Nat.sub_zero]
  apply Nat.div_eq_of_lt
  have e : (q + 1) * 2 ^ (j + 1) = q * 2 ^ (j + 1) + 2 ^ (j + 1) := by ring
  omega

lemma nodeAt_lt {j q d : ℕ} (hd : d ≤ j + 1) {i : Fin N} (hi : i ∈ ivl (j + 1) q) :
    nodeAt j q d (i : ℕ) < 2 ^ d := by
  rw [mem_ivl] at hi
  unfold nodeAt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  have e : d + (j + 1 - d) = j + 1 := by omega
  rw [e]
  have e2 : (q + 1) * 2 ^ (j + 1) = q * 2 ^ (j + 1) + 2 ^ (j + 1) := by ring
  omega

lemma nodeAt_succ_div {j q d : ℕ} (hd : d ≤ j) (i : ℕ) :
    nodeAt j q (d + 1) i / 2 = nodeAt j q d i := by
  unfold nodeAt
  rw [Nat.div_div_eq_div_mul, ← pow_succ]
  congr 2
  omega

lemma nodeAt_mono {j q d : ℕ} {i i' : ℕ} (h : i ≤ i') : nodeAt j q d i ≤ nodeAt j q d i' :=
  Nat.div_le_div_right (Nat.sub_le_sub_right h _)

lemma nodeAt_last {j q : ℕ} (i : ℕ) : nodeAt j q (j + 1) i = i - q * 2 ^ (j + 1) := by
  unfold nodeAt
  rw [Nat.sub_self, pow_zero, Nat.div_one]

/-- Membership in child `c` of the depth-`d` node `ν`, through the depth-`(d+1)` index. -/
lemma mem_ivl_child_iff {j q d : ℕ} (hd : d ≤ j) {i : Fin N} (hi : i ∈ ivl (j + 1) q) (ν c : ℕ) :
    i ∈ ivl (j - d) (2 * (q * 2 ^ d + ν) + c) ↔ nodeAt j q (d + 1) (i : ℕ) = 2 * ν + c := by
  rw [mem_ivl] at hi
  rw [mem_ivl]
  unfold nodeAt
  have e0 : j + 1 - (d + 1) = j - d := by omega
  rw [e0, div_eq_iff_aux (by positivity)]
  have h2 : 2 ^ (j + 1) = 2 * 2 ^ d * 2 ^ (j - d) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have e1 : (2 * (q * 2 ^ d + ν) + c) * 2 ^ (j - d)
      = q * 2 ^ (j + 1) + (2 * ν + c) * 2 ^ (j - d) := by
    rw [h2]; ring
  have e2 : (2 * (q * 2 ^ d + ν) + c + 1) * 2 ^ (j - d)
      = q * 2 ^ (j + 1) + (2 * ν + c + 1) * 2 ^ (j - d) := by
    rw [h2]; ring
  rw [e1, e2]
  omega

lemma mem_ivl_child0_iff {j q d : ℕ} (hd : d ≤ j) {i : Fin N} (hi : i ∈ ivl (j + 1) q) (ν : ℕ) :
    i ∈ ivl (j - d) (2 * (q * 2 ^ d + ν)) ↔ nodeAt j q (d + 1) (i : ℕ) = 2 * ν := by
  simpa using mem_ivl_child_iff hd hi ν 0

/-- **The least common ancestor** of a subword with at least two positions: a depth `d ≤ j`
and a node `ν` whose two children cover the subword and both meet it. -/
lemma exists_lca {j q : ℕ} {U : Finset (Fin N)} (hU : U ⊆ ivl (j + 1) q) (h2 : 2 ≤ U.card) :
    ∃ d ≤ j, ∃ ν < 2 ^ d,
      (∀ i ∈ U, i ∈ ivl (j - d) (2 * (q * 2 ^ d + ν)) ∨ i ∈ ivl (j - d) (2 * (q * 2 ^ d + ν) + 1))
      ∧ (∃ i ∈ U, i ∈ ivl (j - d) (2 * (q * 2 ^ d + ν)))
      ∧ (∃ i ∈ U, i ∈ ivl (j - d) (2 * (q * 2 ^ d + ν) + 1)) := by
  classical
  have hne : U.Nonempty := Finset.card_pos.1 (by omega)
  have hlt : U.min' hne < U.max' hne := Finset.min'_lt_max'_of_card U (by omega)
  have hloU : U.min' hne ∈ U := Finset.min'_mem U hne
  have hhiU : U.max' hne ∈ U := Finset.max'_mem U hne
  have hloI := hU hloU
  have hhiI := hU hhiU
  have hlt' : ((U.min' hne : Fin N) : ℕ) < U.max' hne := hlt
  obtain ⟨lo, hlo⟩ : ∃ lo : Fin N, U.min' hne = lo := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi : Fin N, U.max' hne = hi := ⟨_, rfl⟩
  rw [hlo] at hlt' hloU hloI
  rw [hhi] at hlt' hhiU hhiI
  have hP0 : nodeAt j q 0 (lo : ℕ) = nodeAt j q 0 (hi : ℕ) := by
    rw [nodeAt_zero hloI, nodeAt_zero hhiI]
  obtain ⟨d, hd⟩ : ∃ d, Nat.findGreatest (fun d => nodeAt j q d (lo : ℕ) = nodeAt j q d (hi : ℕ)) j = d :=
    ⟨_, rfl⟩
  have hdj : d ≤ j := hd ▸ Nat.findGreatest_le j
  have hPd : nodeAt j q d (lo : ℕ) = nodeAt j q d (hi : ℕ) :=
    hd ▸ Nat.findGreatest_spec (P := fun d => nodeAt j q d (lo : ℕ) = nodeAt j q d (hi : ℕ))
      (Nat.zero_le j) hP0
  have hnot : nodeAt j q (d + 1) (lo : ℕ) ≠ nodeAt j q (d + 1) (hi : ℕ) := by
    rcases Nat.lt_or_ge d j with h | h
    · exact Nat.findGreatest_is_greatest
        (P := fun d => nodeAt j q d (lo : ℕ) = nodeAt j q d (hi : ℕ)) (k := d + 1)
        (by rw [hd]; exact Nat.lt_succ_self d) (by omega)
    · have hdj' : d = j := le_antisymm hdj h
      intro hc
      rw [hdj', nodeAt_last, nodeAt_last] at hc
      rw [mem_ivl] at hloI hhiI
      omega
  have hlo2 := nodeAt_succ_div (q := q) hdj (lo : ℕ)
  have hhi2 := nodeAt_succ_div (q := q) hdj (hi : ℕ)
  have hle : nodeAt j q (d + 1) (lo : ℕ) ≤ nodeAt j q (d + 1) (hi : ℕ) := nodeAt_mono hlt'.le
  have hlo3 : nodeAt j q (d + 1) (lo : ℕ) = 2 * nodeAt j q d (lo : ℕ) := by omega
  have hhi3 : nodeAt j q (d + 1) (hi : ℕ) = 2 * nodeAt j q d (lo : ℕ) + 1 := by omega
  refine ⟨d, hdj, nodeAt j q d (lo : ℕ), nodeAt_lt (by omega) hloI, ?_, ?_, ?_⟩
  · intro i hiU
    have hiI := hU hiU
    have h1 : nodeAt j q (d + 1) (lo : ℕ) ≤ nodeAt j q (d + 1) (i : ℕ) :=
      nodeAt_mono (hlo ▸ Finset.min'_le U i hiU)
    have h2' : nodeAt j q (d + 1) (i : ℕ) ≤ nodeAt j q (d + 1) (hi : ℕ) :=
      nodeAt_mono (hhi ▸ Finset.le_max' U i hiU)
    rw [mem_ivl_child0_iff hdj hiI, mem_ivl_child_iff hdj hiI]
    omega
  · exact ⟨lo, hloU, (mem_ivl_child0_iff hdj hloI _).2 hlo3⟩
  · exact ⟨hi, hhiU, (mem_ivl_child_iff hdj hhiI _ _).2 hhi3⟩

/-! ## Summaries of the base cases -/

lemma isSummary_letterRec (hst : IsStableOrder M) (x : Fin N → σ) {b : ℕ} (hb1 : 1 ≤ b)
    (r q : ℕ) (hq : q < N) : IsSummary letter x b r 0 q (letterRec x ⟨q, hq⟩) where
  truthful := letterRec_truthful x _
  supp_subset := by rw [supp_letterRec, ivl_zero q hq]
  card_le := by rw [supp_letterRec, Finset.card_singleton]; exact hb1
  dom := fun U hU _ => by
    rw [Record.prod_of_truthful letter (letterRec_truthful x _), supp_letterRec]
    rw [ivl_zero q hq] at hU
    exact hst.subwordProd_mono letter x hU

lemma isSummary_emptyRec (hst : IsStableOrder M) (x : Fin N → σ) (b j q : ℕ) :
    IsSummary letter x b 0 j q emptyRec where
  truthful := truthful_emptyRec x
  supp_subset := by rw [supp_emptyRec]; exact Finset.empty_subset _
  card_le := by rw [supp_emptyRec, Finset.card_empty]; exact Nat.zero_le _
  dom := fun U _ hU => by
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hU), subwordProd_empty]
    exact hst.one_le _

lemma summary_of_eq_zero {b : ℕ} {P : MParams} {r j' : ℕ} (h : j' = 0) (q : ℕ) (ω : Ω b P r j')
    (x : Fin N → σ) : summary letter b P r j' q ω x = letterRecN x q := by
  subst h
  cases r <;> rfl

/-! ## Depth candidates and depth outputs -/

/-- The candidate of depth `d` at node `s.1`: compress the union of the two rank-`r` child
summaries with seeds `s.2.1`, `s.2.2`. -/
noncomputable def candF (b : ℕ) (P : MParams) (r j q d : ℕ)
    (s : Fin (2 ^ d) × Ω b P r (j - d) × Ω b P r (j - d)) (x : Fin N → σ) : Record N σ :=
  Record.compress letter b
    ((summary letter b P r (j - d) (2 * (q * 2 ^ d + (s.1 : ℕ))) s.2.1 x).union
      (summary letter b P r (j - d) (2 * (q * 2 ^ d + (s.1 : ℕ)) + 1) s.2.2 x))

/-- The seed table of the depth-`d` merger. -/
abbrev Tbl (b : ℕ) (P : MParams) (r j d : ℕ) : Type :=
  Fin (P (2 ^ d)).1 → Fin (2 * b) → Fin (P (2 ^ d)).2 → (Fin (2 ^ d) × Ω b P r (j - d) × Ω b P r (j - d))

/-- The depth-`d` merger output inside the rank-`(r+1)` summary with seed `ω`. -/
noncomputable def depthK (b : ℕ) (P : MParams) (r j q : ℕ) (ω : Ω b P (r + 1) (j + 1))
    (d : ℕ) (hd : d ≤ j) (x : Fin N → σ) : Record N σ :=
  mergeK letter b (P (2 ^ d)).1
    (fun ρ i t => candF letter b P r j q d (ω ⟨d, Nat.lt_succ_of_le hd⟩ ρ i t) x)

lemma summary_succ_succ (b : ℕ) (P : MParams) (r j q : ℕ) (ω : Ω b P (r + 1) (j + 1))
    (x : Fin N → σ) :
    summary letter b P (r + 1) (j + 1) q ω x
      = Record.compress letter b (unionList (List.ofFn fun d : Fin (j + 1) =>
          depthK letter b P r j q ω (d : ℕ) (Nat.lt_succ_iff.1 d.2) x)) :=
  rfl

/-- **Depth failure**: a `1/(2·2^d)` mass of depth-`d` candidates is undominated by the
merger output of the table `t`. -/
abbrev badDepth (b : ℕ) (P : MParams) (r j q d : ℕ) (t : Tbl b P r j d) (x : Fin N → σ) : Prop :=
  1 / (2 * (2 : ℝ) ^ d) ≤ ∑ U, pushW (unifW (Fin (2 ^ d) × Ω b P r (j - d) × Ω b P r (j - d)))
      (fun s => candF letter b P r j q d s x) U
    * (if U.prod letter ≤ (mergeK letter b (P (2 ^ d)).1
          (fun ρ i t' => candF letter b P r j q d (t ρ i t') x)).prod letter then 0 else 1)

open Classical in
/-- The failure mass of the rank-`r` summary of `(j, q)` under uniform seeds. -/
noncomputable def failMass (b : ℕ) (P : MParams) (r j q : ℕ) (x : Fin N → σ) : ℝ :=
  ∑ ω : Ω b P r j, unifW (Ω b P r j) ω
    * (if IsSummary letter x b r j q (summary letter b P r j q ω x) then 0 else 1)

/-- **Domination from small mass**: if a set of candidates of mass at least `a` all dominate
`m`, and the undominated mass is less than `a`, then `K` dominates `m`. -/
lemma dominated_of_smallMass {Ω' : Type} [Fintype Ω'] [DecidableEq Ω'] {ν : Ω' → ℝ}
    (hν : IsWeight ν) (cand : Ω' → Record N σ) (K : Record N σ) (G : Ω' → Prop) [DecidablePred G]
    {a : ℝ} {m : M} (hG : a ≤ ∑ s, ν s * (if G s then 1 else 0))
    (hdom : ∀ s, G s → m ≤ (cand s).prod letter)
    (hsmall : ¬ a ≤ ∑ U, pushW ν cand U * (if U.prod letter ≤ K.prod letter then 0 else 1)) :
    m ≤ K.prod letter := by
  by_contra hmK
  apply hsmall
  rw [sum_pushW]
  refine hG.trans (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hν.nonneg s))
  by_cases hGs : G s
  · rw [if_pos hGs, if_neg]
    exact fun hle => hmK ((hdom s hGs).trans hle)
  · rw [if_neg hGs]
    split_ifs <;> norm_num

lemma unifW_pi3 (E : Type) [Fintype E] [DecidableEq E] (R m k : ℕ) :
    unifW (Fin R → Fin m → Fin k → E) = tupleW (tupleW (tupleW (unifW E))) := by
  funext t
  simp only [unifW_pi, tupleW]

/-! ## The deterministic rank step -/

section Step

variable (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) (P : MParams)
include hst hb hb1

/-- At depth `j` both children are exact letters. -/
lemma prod_candF_of_last (x : Fin N → σ) {r j q : ℕ} (hq : (q + 1) * 2 ^ (j + 1) ≤ N)
    (s : Fin (2 ^ j) × Ω b P r (j - j) × Ω b P r (j - j)) :
    ∃ (h0 : 2 * (q * 2 ^ j + (s.1 : ℕ)) < N) (h1 : 2 * (q * 2 ^ j + (s.1 : ℕ)) + 1 < N),
      (candF letter b P r j q j s x).prod letter
        = subwordProd letter x
            {⟨2 * (q * 2 ^ j + (s.1 : ℕ)), h0⟩, ⟨2 * (q * 2 ^ j + (s.1 : ℕ)) + 1, h1⟩} := by
  have hs := s.1.isLt
  have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have e : (q + 1) * 2 ^ (j + 1) = 2 * (q * 2 ^ j) + 2 * 2 ^ j := by rw [pow_succ]; ring
  have h1 : 2 * (q * 2 ^ j + (s.1 : ℕ)) + 1 < N := by omega
  refine ⟨by omega, h1, ?_⟩
  rw [candF, (Record.compress_spec letter hb _).2.2, summary_of_eq_zero letter (Nat.sub_self j),
    summary_of_eq_zero letter (Nat.sub_self j), letterRecN, letterRecN, dif_pos h1,
    dif_pos (by omega : 2 * (q * 2 ^ j + (s.1 : ℕ)) < N),
    prod_union_truthful letter x (letterRec_truthful x _) (letterRec_truthful x _),
    supp_letterRec, supp_letterRec, Finset.insert_eq]

open Classical in
/-- **The rank step.**  With every child failure mass at most `1/100` and no depth failure,
the rank-`(r+1)` summary is an `(r+1)`-summary. -/
theorem isSummary_of_smallMass (x : Fin N → σ) {r j q : ℕ} (hq : (q + 1) * 2 ^ (j + 1) ≤ N)
    (ω : Ω b P (r + 1) (j + 1))
    (hchild : ∀ d ≤ j, ∀ ν < 2 ^ d, ∀ c < 2,
      failMass letter b P r (j - d) (2 * (q * 2 ^ d + ν) + c) x ≤ 1 / 100)
    (hgood : ∀ d (hd : d ≤ j),
      ¬ badDepth letter b P r j q d (ω ⟨d, Nat.lt_succ_of_le hd⟩) x) :
    IsSummary letter x b (r + 1) (j + 1) q (summary letter b P (r + 1) (j + 1) q ω x) where
  truthful := summary_truthful letter hb hb1 P _ _ _ ω x
  supp_subset := summary_supp_subset letter hb hb1 P _ _ _ ω x
  card_le := summary_card_le letter hb hb1 P _ _ _ ω x
  dom := by
    intro U hU hcard
    have hKtr : ∀ d (hd : d ≤ j), (depthK letter b P r j q ω d hd x).Truthful x := fun d hd =>
      (mergeK_spec letter hb hb1 x _ _ fun ρ i t => Record.truthful_compress letter
        (Record.truthful_union (summary_truthful letter hb hb1 P _ _ _ _ x)
          (summary_truthful letter hb hb1 P _ _ _ _ x)) b).1
    have hred : ∀ d (hd : d ≤ j), (depthK letter b P r j q ω d hd x).prod letter
        ≤ (summary letter b P (r + 1) (j + 1) q ω x).prod letter := by
      intro d hd
      have hmem : depthK letter b P r j q ω d hd x ∈ List.ofFn fun d : Fin (j + 1) =>
          depthK letter b P r j q ω (d : ℕ) (Nat.lt_succ_iff.1 d.2) x := by
        rw [List.mem_ofFn]; exact ⟨⟨d, Nat.lt_succ_of_le hd⟩, rfl⟩
      rw [summary_succ_succ, (Record.compress_spec letter hb _).2.2,
        Record.prod_of_truthful letter (truthful_unionList x fun A hA => ?_),
        Record.prod_of_truthful letter (hKtr d hd)]
      · exact hst.subwordProd_mono letter x (supp_subset_unionList hmem)
      · rw [List.mem_ofFn] at hA
        obtain ⟨d', rfl⟩ := hA
        exact hKtr _ _
    rcases Nat.lt_or_ge U.card 2 with hlt | hge
    · rcases Nat.lt_or_ge U.card 1 with h0 | h1
      · rw [Finset.card_eq_zero.1 (by omega : U.card = 0), subwordProd_empty]
        exact hst.one_le _
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (by omega : U.card = 1)
        have hiI : i ∈ ivl (j + 1) q := hU (Finset.mem_singleton_self i)
        have hνlt : nodeAt j q j (i : ℕ) < 2 ^ j := nodeAt_lt (by omega) hiI
        have hdiv := nodeAt_succ_div (q := q) (le_refl j) (i : ℕ)
        have hmem : i ∈ ivl (j - j)
            (2 * (q * 2 ^ j + nodeAt j q j (i : ℕ)) + nodeAt j q (j + 1) (i : ℕ) % 2) := by
          rw [mem_ivl_child_iff (le_refl j) hiI]; omega
        rw [mem_ivl, Nat.sub_self, pow_zero, mul_one, mul_one] at hmem
        refine le_trans ?_ (hred j le_rfl)
        refine dominated_of_smallMass letter (isWeight_unifW _) (fun s => candF letter b P r j q j s x)
          (depthK letter b P r j q ω j le_rfl x) (fun s => s.1 = ⟨_, hνlt⟩)
          (a := 1 / (2 * (2 : ℝ) ^ j)) ?_ ?_ (hgood j le_rfl)
        · have h1 := sum_unifW_prod_fst_eq (Fin (2 ^ j)) (Ω b P r (j - j) × Ω b P r (j - j))
            ⟨_, hνlt⟩ (fun _ => (1 : ℝ))
          beta_reduce at h1
          simp only [mul_one] at h1
          rw [(isWeight_unifW _).sum_one, mul_one, Fintype.card_fin] at h1
          refine le_of_le_of_eq ?_ h1.symm
          push_cast
          exact one_div_le_one_div_of_le (by positivity) (by linarith [pow_pos (two_pos (α := ℝ)) j])
        · intro s hs
          have hs1 : (s.1 : ℕ) = nodeAt j q j (i : ℕ) := by rw [hs]
          obtain ⟨h0, h1, hprod⟩ := prod_candF_of_last letter hst hb hb1 P x hq s
          rw [hprod]
          refine hst.subwordProd_mono letter x (Finset.singleton_subset_iff.2 ?_)
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          rw [hs1]
          clear hs
          omega
    · obtain ⟨d, hdj, ν, hν, hall, ⟨lo, hloU, hlo⟩, ⟨hi, hhiU, hhi⟩⟩ := exists_lca hU hge
      have hsep : ∀ i ∈ ivl (N := N) (j - d) (2 * (q * 2 ^ d + ν)),
          ∀ i' ∈ ivl (N := N) (j - d) (2 * (q * 2 ^ d + ν) + 1), i < i' := by
        intro i hi i' hi'
        rw [mem_ivl] at hi hi'
        rw [Fin.lt_def]
        omega
      obtain ⟨U₀, hU₀def⟩ : ∃ U₀, U.filter (· ∈ ivl (N := N) (j - d) (2 * (q * 2 ^ d + ν))) = U₀ :=
        ⟨_, rfl⟩
      obtain ⟨U₁, hU₁def⟩ :
          ∃ U₁, U.filter (· ∈ ivl (N := N) (j - d) (2 * (q * 2 ^ d + ν) + 1)) = U₁ := ⟨_, rfl⟩
      have hU₀ : U₀ ⊆ ivl (j - d) (2 * (q * 2 ^ d + ν)) := fun i hi => by
        rw [← hU₀def] at hi; exact (Finset.mem_filter.1 hi).2
      have hU₁ : U₁ ⊆ ivl (j - d) (2 * (q * 2 ^ d + ν) + 1) := fun i hi => by
        rw [← hU₁def] at hi; exact (Finset.mem_filter.1 hi).2
      have hdisj : Disjoint U₀ U₁ :=
        Finset.disjoint_left.2 fun i h0 h1 => lt_irrefl i (hsep i (hU₀ h0) i (hU₁ h1))
      have hunion : U = U₀ ∪ U₁ := by
        ext i
        rw [← hU₀def, ← hU₁def, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        constructor
        · intro h
          rcases hall i h with h' | h'
          · exact Or.inl ⟨h, h'⟩
          · exact Or.inr ⟨h, h'⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hcard : U₀.card + U₁.card = U.card := by
        rw [hunion, Finset.card_union_of_disjoint hdisj]
      have h0pos : 0 < U₀.card :=
        Finset.card_pos.2 ⟨lo, by rw [← hU₀def]; exact Finset.mem_filter.2 ⟨hloU, hlo⟩⟩
      have h1pos : 0 < U₁.card :=
        Finset.card_pos.2 ⟨hi, by rw [← hU₁def]; exact Finset.mem_filter.2 ⟨hhiU, hhi⟩⟩
      have hr0 : U₀.card ≤ r := by omega
      have hr1 : U₁.card ≤ r := by omega
      have hsplit : subwordProd letter x U = subwordProd letter x U₀ * subwordProd letter x U₁ := by
        rw [hunion]
        exact subwordProd_union_of_sep letter x fun i hi i' hi' => hsep i (hU₀ hi) i' (hU₁ hi')
      refine le_trans ?_ (hred d hdj)
      rw [hsplit]
      refine dominated_of_smallMass letter (isWeight_unifW _) (fun s => candF letter b P r j q d s x)
        (depthK letter b P r j q ω d hdj x)
        (fun s => s.1 = ⟨ν, hν⟩
          ∧ IsSummary letter x b r (j - d) (2 * (q * 2 ^ d + ν))
              (summary letter b P r (j - d) (2 * (q * 2 ^ d + ν)) s.2.1 x)
          ∧ IsSummary letter x b r (j - d) (2 * (q * 2 ^ d + ν) + 1)
              (summary letter b P r (j - d) (2 * (q * 2 ^ d + ν) + 1) s.2.2 x))
        (a := 1 / (2 * (2 : ℝ) ^ d)) ?_ ?_ (hgood d hdj)
      · have hf0 := hchild d hdj ν hν 0 (by norm_num)
        have hf1 := hchild d hdj ν hν 1 (by norm_num)
        rw [add_zero] at hf0
        unfold failMass at hf0 hf1
        have hand := sum_unifW_and_ge (Ω b P r (j - d)) (Ω b P r (j - d))
          (fun ω' => IsSummary letter x b r (j - d) (2 * (q * 2 ^ d + ν))
            (summary letter b P r (j - d) (2 * (q * 2 ^ d + ν)) ω' x))
          (fun ω' => IsSummary letter x b r (j - d) (2 * (q * 2 ^ d + ν) + 1)
            (summary letter b P r (j - d) (2 * (q * 2 ^ d + ν) + 1) ω' x))
        beta_reduce at hand
        have h1 := sum_unifW_prod_fst_eq (Fin (2 ^ d)) (Ω b P r (j - d) × Ω b P r (j - d)) ⟨ν, hν⟩
          (fun p => if IsSummary letter x b r (j - d) (2 * (q * 2 ^ d + ν))
              (summary letter b P r (j - d) (2 * (q * 2 ^ d + ν)) p.1 x)
            ∧ IsSummary letter x b r (j - d) (2 * (q * 2 ^ d + ν) + 1)
              (summary letter b P r (j - d) (2 * (q * 2 ^ d + ν) + 1) p.2 x) then (1 : ℝ) else 0)
        beta_reduce at h1
        rw [Fintype.card_fin] at h1
        push_cast at h1
        refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left (a := 1 / (2 : ℝ) ^ d) hand
          (by positivity)) (le_of_eq ?_))
        · rw [show (1 : ℝ) / (2 * 2 ^ d) = 1 / 2 ^ d * (1 / 2) by
            rw [one_div_mul_one_div, mul_comm]]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        · rw [← h1]
          refine Finset.sum_congr rfl fun s _ => ?_
          congr 1
          by_cases e1 : s.1 = ⟨ν, hν⟩ <;> by_cases e2 :
            (IsSummary letter x b r (j - d) (2 * (q * 2 ^ d + ν))
              (summary letter b P r (j - d) (2 * (q * 2 ^ d + ν)) s.2.1 x)
            ∧ IsSummary letter x b r (j - d) (2 * (q * 2 ^ d + ν) + 1)
              (summary letter b P r (j - d) (2 * (q * 2 ^ d + ν) + 1) s.2.2 x)) <;>
            simp [e1, e2]
      · rintro s ⟨hs1, hK₁, hK₂⟩
        have hs1' : (s.1 : ℕ) = ν := by rw [hs1]
        have hd1 := hK₁.dom U₀ hU₀ hr0
        have hd2 := hK₂.dom U₁ hU₁ hr1
        rw [Record.prod_of_truthful letter hK₁.truthful] at hd1
        rw [Record.prod_of_truthful letter hK₂.truthful] at hd2
        rw [candF, (Record.compress_spec letter hb _).2.2, hs1',
          prod_union_truthful letter x hK₁.truthful hK₂.truthful,
          subwordProd_union_of_sep letter x fun i hi i' hi' =>
            hsep i (hK₁.supp_subset hi) i' (hK₂.supp_subset hi')]
        exact hst.mul_le_mul hd1 hd2

end Step

/-! ## The probabilistic bound -/

/-- **The parameter hypothesis** `(C)` in abstract form: at every node count `h`, the merger
with `R = (P h).1` rounds and `k = (P h).2` proposals per draw fails with mass at most
`1/(100N)` at threshold `a = 1/(2h)`. -/
def GoodParams (b N : ℕ) (P : MParams) : Prop :=
  ∀ h : ℕ, 1 ≤ h → h ≤ N →
    (1 / 2 : ℝ) ^ (P h).1 / (1 / (2 * (h : ℝ)))
        + ((P h).1 : ℝ) * (2 * (b : ℝ)) * (1 - 1 / (2 * (h : ℝ))) ^ (P h).2
      ≤ 1 / (100 * (N : ℝ))

section Prob

variable (hst : IsStableOrder M) {b : ℕ} (hb : IsBreadthBound letter b) (hb1 : 1 ≤ b) (P : MParams)
include hst hb hb1

/-- Every depth fails with mass at most `1/(100N)`. -/
theorem depth_fail_le (hP : GoodParams b N P) (x : Fin N → σ) (r j q d : ℕ) (hdN : 2 ^ d ≤ N) :
    ∑ t : Tbl b P r j d, unifW (Tbl b P r j d) t
        * (if badDepth letter b P r j q d t x then 1 else 0)
      ≤ 1 / (100 * (N : ℝ)) := by
  have hcT : ∀ (s : Fin (2 ^ d) × Ω b P r (j - d) × Ω b P r (j - d)) (x : Fin N → σ),
      (candF letter b P r j q d s x).Truthful x := fun s x =>
    Record.truthful_compress letter (Record.truthful_union
      (summary_truthful letter hb hb1 P _ _ _ _ x) (summary_truthful letter hb hb1 P _ _ _ _ x)) b
  have ha : (0 : ℝ) < 1 / (2 * 2 ^ d) := by positivity
  have ha1 : (1 : ℝ) / (2 * 2 ^ d) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    linarith
  have h := seeded_small_mass letter hst hb hb1
    (isWeight_unifW (Fin (2 ^ d) × Ω b P r (j - d) × Ω b P r (j - d)))
    (candF letter b P r j q d) hcT x ha ha1 (k := (P (2 ^ d)).2) (P (2 ^ d)).1
  rw [unifW_pi3]
  refine le_trans h ?_
  have := hP (2 ^ d) Nat.one_le_two_pow hdN
  push_cast at this
  exact this

open Classical in
/-- **Every rank-`r` summary is correct with probability at least `99/100`.** -/
theorem summary_correct (hP : GoodParams b N P) :
    ∀ (r j q : ℕ), (q + 1) * 2 ^ j ≤ N → ∀ x : Fin N → σ, failMass letter b P r j q x ≤ 1 / 100
  | r, 0, q, hq, x => by
    have hqN : q < N := by simp at hq; omega
    unfold failMass
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun ω _ => ?_)) (by norm_num)
    rw [summary_of_eq_zero letter rfl, letterRecN, dif_pos hqN,
      if_pos (isSummary_letterRec letter hst x hb1 r q hqN), mul_zero]
  | 0, j + 1, q, hq, x => by
    unfold failMass
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun ω _ => ?_)) (by norm_num)
    rw [show summary letter b P 0 (j + 1) q ω x = emptyRec from rfl,
      if_pos (isSummary_emptyRec letter hst x b _ q), mul_zero]
  | r + 1, j + 1, q, hq, x => by
    have hchild : ∀ d ≤ j, ∀ ν < 2 ^ d, ∀ c < 2,
        failMass letter b P r (j - d) (2 * (q * 2 ^ d + ν) + c) x ≤ 1 / 100 := by
      intro d hd ν hν c hc
      refine summary_correct hP r (j - d) _ ?_ x
      have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have h2 : 2 ^ (j + 1) = 2 * 2 ^ d * 2 ^ (j - d) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have e1 : 2 * (q * 2 ^ d + ν) + c + 1 ≤ (q + 1) * (2 * 2 ^ d) := by
        have : (q + 1) * (2 * 2 ^ d) = 2 * (q * 2 ^ d) + 2 * 2 ^ d := by ring
        omega
      calc (2 * (q * 2 ^ d + ν) + c + 1) * 2 ^ (j - d)
          ≤ (q + 1) * (2 * 2 ^ d) * 2 ^ (j - d) := Nat.mul_le_mul_right _ e1
        _ = (q + 1) * 2 ^ (j + 1) := by rw [h2]; ring
        _ ≤ N := hq
    have hjN : (j + 1 : ℝ) ≤ N := by
      have h1 : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (j + 1) ≤ N := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hq
      exact_mod_cast (by omega : j + 1 ≤ N)
    have hN : (0 : ℝ) < N := by linarith [(by positivity : (0 : ℝ) ≤ j)]
    calc failMass letter b P (r + 1) (j + 1) q x
        ≤ ∑ ω : Ω b P (r + 1) (j + 1), unifW (Ω b P (r + 1) (j + 1)) ω
            * (if ∃ d : Fin (j + 1), badDepth letter b P r j q (d : ℕ) (ω d) x then 1 else 0) := by
          unfold failMass
          refine Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left ?_ ((isWeight_unifW _).nonneg ω)
          by_cases h1 : IsSummary letter x b (r + 1) (j + 1) q
            (summary letter b P (r + 1) (j + 1) q ω x)
          · rw [if_pos h1]; split_ifs <;> norm_num
          · rw [if_neg h1]
            split_ifs with h2
            · exact le_rfl
            · exfalso
              exact h1 (isSummary_of_smallMass letter hst hb hb1 P x hq ω hchild
                fun d hd hbad => h2 ⟨⟨d, Nat.lt_succ_of_le hd⟩, hbad⟩)
      _ = ∑ ω : (d : Fin (j + 1)) → Tbl b P r j d, piW (fun d : Fin (j + 1) => unifW (Tbl b P r j d)) ω
            * (if ∃ d : Fin (j + 1), badDepth letter b P r j q (d : ℕ) (ω d) x then 1 else 0) := by
          show ∑ ω : (d : Fin (j + 1)) → Tbl b P r j d,
            unifW ((d : Fin (j + 1)) → Tbl b P r j d) ω * _ = _
          simp only [unifW_dpi]
      _ ≤ ∑ d : Fin (j + 1), ∑ t : Tbl b P r j d, unifW (Tbl b P r j d) t
            * (if badDepth letter b P r j q (d : ℕ) t x then 1 else 0) :=
          sum_piW_exists_le (fun d => isWeight_unifW _)
            (fun (d : Fin (j + 1)) t => badDepth letter b P r j q (d : ℕ) t x)
      _ ≤ ∑ _d : Fin (j + 1), (1 : ℝ) / (100 * (N : ℝ)) :=
          Finset.sum_le_sum fun d _ => depth_fail_le letter hst hb hb1 P hP x r j q d
            (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : (d : ℕ) ≤ j + 1))
              (le_trans (by rw [add_mul, one_mul]; exact Nat.le_add_left _ _) hq))
      _ = (j + 1 : ℝ) * (1 / (100 * (N : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 1 / 100 := by
          rw [show (j + 1 : ℝ) * (1 / (100 * (N : ℝ))) = ((j + 1 : ℝ) / N) * (1 / 100) by
            field_simp]
          exact mul_le_of_le_one_left (by norm_num) ((div_le_one hN).2 hjN)

end Prob

end Correct

end MonoidProduct
