import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
set_option linter.style.header false

/-!
# Greedy bases of a matroid on a linearly ordered ground type

This file develops the greedy basis `B(S)` of `monoid.tex`, section `sec:matroid-bases`,
for a matroid `M` whose ground set is all of a linearly ordered type `E`.

We define `greedy M S` to keep exactly those `e ∈ S` that do not lie in the closure of
the elements of `S` strictly below `e`:

  `greedy M S = {e ∈ S | e ∉ cl {x ∈ S | x < e}}`.

The scan description of `monoid.tex` — run through `S` in increasing order and keep an
element exactly when it preserves independence — is `greedyScan`, and
`greedy_eq_greedyScan` proves that the two agree.

The central invariant is the prefix property `eq:matroid-prefix-closure`: for every
lower set `P` of the order, `greedy M S ∩ P` is a basis of `S ∩ P`
(`isBasis_greedy_inter`), hence has the same closure and rank.  Membership in the greedy
basis is decided by the closures of the prefixes `S ∩ Iio e` and `S ∩ Iic e`
(`mem_greedy_iff_closure`), so two sets whose prefix closures agree have the same greedy
basis (`greedy_eq_greedy_of_closure_inter_eq`).  This yields:

* the merge law of `lem:matroid-greedy-merge`,
  `greedy M (S ∪ T) = greedy M (greedy M S ∪ greedy M T)`;
* the insertion form `greedy M (insert e S) = greedy M (insert e (greedy M S))`;
* the facts `greedy M ∅ = ∅` and `greedy M S = S` for independent `S`, which make `∅`
  an identity and the product idempotent in `prop:matroid-greedy-monoid`;
* the sandwich property (`greedy M S ⊆ T ⊆ S` implies `greedy M T = greedy M S`) and
  its consequence, stability under deleting an unselected element.

Equality of whole-set closures alone would not suffice for these statements: the
arguments use the closure invariant on every order prefix.

No finiteness of `E` is needed: all sets here are `Finset`s.  Decidability of closure
membership is classical; the development concerns which elements are selected, not how
they are computed.
-/

namespace MonoidProduct.Matroid

open Set

variable {E : Type*} [LinearOrder E]

open scoped Classical in
/-- The greedy basis of `S`: the elements of `S` that are not spanned by the elements
of `S` strictly below them. -/
noncomputable def greedy (M : _root_.Matroid E) (S : Finset E) : Finset E :=
  S.filter fun e => e ∉ M.closure ↑(S.filter (· < e))

variable {M : _root_.Matroid E} {S T : Finset E} {P : Set E} {e : E}

lemma coe_filter_lt_eq_inter_Iio (S : Finset E) (e : E) :
    (↑(S.filter (· < e)) : Set E) = ↑S ∩ Iio e := by
  ext x; simp

lemma coe_filter_le_eq_inter_Iic (S : Finset E) (e : E) :
    (↑(S.filter (· ≤ e)) : Set E) = ↑S ∩ Iic e := by
  ext x; simp

lemma mem_greedy : e ∈ greedy M S ↔ e ∈ S ∧ e ∉ M.closure (↑S ∩ Iio e) := by
  classical
  unfold greedy
  rw [Finset.mem_filter, coe_filter_lt_eq_inter_Iio]

lemma greedy_subset (M : _root_.Matroid E) (S : Finset E) : greedy M S ⊆ S :=
  fun _ h => (mem_greedy.1 h).1

@[simp] lemma greedy_empty (M : _root_.Matroid E) : greedy M ∅ = ∅ := by
  ext e; simp [mem_greedy]

/-- Restricting to a lower set commutes with taking greedy bases. -/
lemma greedy_filter_of_isLowerSet [DecidablePred (· ∈ P)] (hP : IsLowerSet P) :
    greedy M (S.filter (· ∈ P)) = (greedy M S).filter (· ∈ P) := by
  ext e
  have key : e ∈ P → (↑(S.filter (· ∈ P)) : Set E) ∩ Iio e = ↑S ∩ Iio e := by
    intro heP
    ext x
    simp only [Finset.coe_filter, mem_inter_iff, Finset.mem_coe, mem_Iio]
    change (x ∈ S ∧ x ∈ P) ∧ x < e ↔ x ∈ S ∧ x < e
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hP (le_of_lt h.2) heP⟩, h.2⟩⟩
  simp only [mem_greedy, Finset.mem_filter]
  constructor
  · rintro ⟨⟨heS, heP⟩, hcl⟩
    exact ⟨⟨heS, by rwa [← key heP]⟩, heP⟩
  · rintro ⟨⟨heS, hcl⟩, heP⟩
    exact ⟨⟨heS, heP⟩, by rwa [key heP]⟩

open scoped Classical in
/-- Adding a new maximum element `a` to `S`: the greedy basis gains `a` exactly when `a`
is not spanned by `S`. -/
lemma greedy_insert_of_forall_lt {a : E} (ha : ∀ x ∈ S, x < a) :
    greedy M (insert a S) =
      if a ∈ M.closure ↑S then greedy M S else insert a (greedy M S) := by
  classical
  have hpre_a : (↑(insert a S) : Set E) ∩ Iio a = ↑S := by
    ext x
    simp only [Finset.coe_insert, mem_inter_iff, mem_insert_iff, Finset.mem_coe, mem_Iio]
    constructor
    · rintro ⟨rfl | h, hx⟩
      · exact absurd hx (lt_irrefl _)
      · exact h
    · intro h; exact ⟨Or.inr h, ha x h⟩
  have hpre : ∀ x ∈ S, (↑(insert a S) : Set E) ∩ Iio x = ↑S ∩ Iio x := by
    intro x hx
    ext y
    simp only [Finset.coe_insert, mem_inter_iff, mem_insert_iff, Finset.mem_coe, mem_Iio]
    constructor
    · rintro ⟨rfl | h, hy⟩
      · exact absurd (hy.trans (ha x hx)) (lt_irrefl _)
      · exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩; exact ⟨Or.inr h, hy⟩
  ext e
  by_cases hea : e = a
  · subst hea
    have heS : e ∉ S := fun h => lt_irrefl e (ha e h)
    have heg : e ∉ greedy M S := fun h => heS (greedy_subset M S h)
    rw [mem_greedy, hpre_a]
    split_ifs with h <;> simp [h, heg]
  · rw [mem_greedy]
    simp only [Finset.mem_insert, hea, false_or]
    constructor
    · rintro ⟨heS, hcl⟩
      have : e ∈ greedy M S := mem_greedy.2 ⟨heS, by rwa [← hpre e heS]⟩
      split_ifs <;> simp [this]
    · intro h
      have h' : e ∈ greedy M S := by split_ifs at h <;> simpa [hea] using h
      obtain ⟨heS, hcl⟩ := mem_greedy.1 h'
      exact ⟨heS, by rwa [hpre e heS]⟩

/-! ### The prefix invariant -/

/-- The greedy basis of `S` is a basis of `S`. -/
theorem isBasis_greedy (hM : M.E = univ) (S : Finset E) :
    M.IsBasis ↑(greedy M S) ↑S := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    rw [greedy_insert_of_forall_lt ha]
    split_ifs with hcl
    · refine ih.indep.isBasis_of_subset_of_subset_closure
        (ih.subset.trans (by simp)) ?_
      rw [ih.closure_eq_closure, Finset.coe_insert]
      exact insert_subset hcl (M.subset_closure _ (by simp [hM]))
    · have hag : a ∉ (↑(greedy M S) : Set E) := fun h => haS (greedy_subset M S h)
      have hind : M.Indep (insert a (↑(greedy M S) : Set E)) := by
        rw [ih.indep.insert_indep_iff_of_notMem hag, ih.closure_eq_closure]
        exact ⟨by simp [hM], hcl⟩
      simp only [Finset.coe_insert]
      refine hind.isBasis_of_subset_of_subset_closure
        (insert_subset_insert ih.subset) (insert_subset ?_ ?_)
      · exact M.mem_closure_of_mem (mem_insert _ _) (by simp [hM])
      · exact ih.subset_closure.trans (M.closure_subset_closure (subset_insert _ _))

lemma indep_greedy (hM : M.E = univ) (S : Finset E) : M.Indep ↑(greedy M S) :=
  (isBasis_greedy hM S).indep

lemma closure_greedy (hM : M.E = univ) (S : Finset E) :
    M.closure ↑(greedy M S) = M.closure ↑S :=
  (isBasis_greedy hM S).closure_eq_closure

lemma eRk_greedy (hM : M.E = univ) (S : Finset E) : M.eRk ↑(greedy M S) = M.eRk ↑S :=
  (isBasis_greedy hM S).eRk_eq_eRk

/-- **Prefix invariant** (`eq:matroid-prefix-closure`): on every lower set `P` of the
order, the greedy basis of `S` restricts to a basis of `S ∩ P`. -/
theorem isBasis_greedy_inter (hM : M.E = univ) (S : Finset E) (hP : IsLowerSet P) :
    M.IsBasis (↑(greedy M S) ∩ P) (↑S ∩ P) := by
  classical
  have h := isBasis_greedy hM (M := M) (S.filter (· ∈ P))
  rw [greedy_filter_of_isLowerSet hP] at h
  convert h using 1 <;> ext x <;> simp

lemma closure_greedy_inter (hM : M.E = univ) (S : Finset E) (hP : IsLowerSet P) :
    M.closure (↑(greedy M S) ∩ P) = M.closure (↑S ∩ P) :=
  (isBasis_greedy_inter hM S hP).closure_eq_closure

lemma eRk_greedy_inter (hM : M.E = univ) (S : Finset E) (hP : IsLowerSet P) :
    M.eRk (↑(greedy M S) ∩ P) = M.eRk (↑S ∩ P) :=
  (isBasis_greedy_inter hM S hP).eRk_eq_eRk

/-! ### The scan description -/

open scoped Classical in
/-- One step of the greedy scan: keep `e` exactly when it preserves independence. -/
noncomputable def greedyScanStep (M : _root_.Matroid E) (I : Finset E) (e : E) :
    Finset E :=
  if M.Indep (insert e (I : Set E)) then insert e I else I

/-- The greedy scan: run through `S` in increasing order, keeping an element exactly when
it preserves the independence of the elements kept so far. -/
noncomputable def greedyScan (M : _root_.Matroid E) (S : Finset E) : Finset E :=
  (S.sort (· ≤ ·)).foldl (greedyScanStep M) ∅

/-- Adding a new maximum element is one step of the scan. -/
lemma greedy_insert_eq_greedyScanStep (hM : M.E = univ) {a : E} (ha : ∀ x ∈ S, x < a) :
    greedy M (insert a S) = greedyScanStep M (greedy M S) a := by
  classical
  have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
  have hag : a ∉ (↑(greedy M S) : Set E) := fun h => haS (greedy_subset M S h)
  have hB := isBasis_greedy hM (M := M) S
  have hiff : M.Indep (insert a (↑(greedy M S) : Set E)) ↔ a ∉ M.closure ↑S := by
    rw [hB.indep.insert_indep_iff_of_notMem hag, hB.closure_eq_closure]
    simp [hM]
  rw [greedy_insert_of_forall_lt ha, greedyScanStep]
  by_cases h : a ∈ M.closure ↑S
  · rw [if_pos h, if_neg (by rwa [hiff, not_not])]
  · rw [if_neg h, if_pos (hiff.2 h)]

lemma foldl_greedyScanStep_eq_greedy (hM : M.E = univ) (l : List E)
    (hl : l.Pairwise (· < ·)) : l.foldl (greedyScanStep M) ∅ = greedy M l.toFinset := by
  classical
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.pairwise_append] at hl
    have ha : ∀ x ∈ l.toFinset, x < a := fun x hx =>
      hl.2.2 x (List.mem_toFinset.1 hx) a (by simp)
    have hl' : (l ++ [a]).toFinset = insert a l.toFinset := by ext; simp
    rw [List.foldl_append, ih hl.1, hl', greedy_insert_eq_greedyScanStep hM ha]
    simp

/-- The closure definition of the greedy basis agrees with the increasing scan that keeps
exactly the insertions preserving independence. -/
theorem greedy_eq_greedyScan (hM : M.E = univ) (S : Finset E) :
    greedy M S = greedyScan M S := by
  classical
  rw [greedyScan, foldl_greedyScanStep_eq_greedy hM _ (Finset.sortedLT_sort S).pairwise,
    Finset.sort_toFinset]

/-! ### Membership is decided by prefix closures -/

/-- `e` is selected exactly when the closure grows between the prefix of `S` strictly
below `e` and the prefix ending at `e` (the rank-increase characterization of
`monoid.tex`, section `sec:matroid-bases`). -/
lemma mem_greedy_iff_closure (hM : M.E = univ) :
    e ∈ greedy M S ↔ e ∈ M.closure (↑S ∩ Iic e) ∧ e ∉ M.closure (↑S ∩ Iio e) := by
  rw [mem_greedy]
  constructor
  · rintro ⟨heS, hcl⟩
    exact ⟨M.mem_closure_of_mem' ⟨heS, le_rfl⟩ (by simp [hM]), hcl⟩
  · rintro ⟨hcl, hncl⟩
    refine ⟨?_, hncl⟩
    by_contra heS
    refine hncl ?_
    convert hcl using 2
    ext x
    simp only [mem_inter_iff, Finset.mem_coe, mem_Iio, mem_Iic]
    exact ⟨fun h => ⟨h.1, h.2.le⟩,
      fun h => ⟨h.1, lt_of_le_of_ne h.2 (fun hx => heS (hx ▸ h.1))⟩⟩

/-- Two sets whose prefixes have equal closures have the same greedy basis. -/
theorem greedy_eq_greedy_of_closure_inter_eq (hM : M.E = univ)
    (h : ∀ P : Set E, IsLowerSet P → M.closure (↑S ∩ P) = M.closure (↑T ∩ P)) :
    greedy M S = greedy M T := by
  ext e
  rw [mem_greedy_iff_closure hM, mem_greedy_iff_closure hM, h _ (isLowerSet_Iic e),
    h _ (isLowerSet_Iio e)]

/-- Two sets with equal prefix closures keep equal prefix closures after adjoining
the same set, and unions of such pairs have equal prefix closures. -/
lemma closure_union_inter_congr {S' T' : Finset E}
    (hS : ∀ P : Set E, IsLowerSet P → M.closure (↑S ∩ P) = M.closure (↑S' ∩ P))
    (hT : ∀ P : Set E, IsLowerSet P → M.closure (↑T ∩ P) = M.closure (↑T' ∩ P))
    (P : Set E) (hP : IsLowerSet P) :
    M.closure (↑(S ∪ T) ∩ P) = M.closure (↑(S' ∪ T') ∩ P) := by
  classical
  simp only [Finset.coe_union, union_inter_distrib_right]
  rw [M.closure_union_congr_left (hS P hP), M.closure_union_congr_right (hT P hP)]

/-- **Merge law** (`lem:matroid-greedy-merge`). -/
theorem greedy_union_eq_greedy_union_greedy (hM : M.E = univ) (S T : Finset E) :
    greedy M (S ∪ T) = greedy M (greedy M S ∪ greedy M T) := by
  classical
  refine greedy_eq_greedy_of_closure_inter_eq hM
    (closure_union_inter_congr (fun P hP => ?_) (fun P hP => ?_))
  · exact (closure_greedy_inter hM S hP).symm
  · exact (closure_greedy_inter hM T hP).symm

/-- Greedy leaves every independent set unchanged. -/
theorem greedy_eq_self_of_indep (hS : M.Indep ↑S) : greedy M S = S := by
  ext e
  rw [mem_greedy]
  refine ⟨fun h => h.1, fun he => ⟨he, fun hcl => hS.notMem_closure_sdiff_of_mem he ?_⟩⟩
  refine M.closure_subset_closure (fun x hx => ?_) hcl
  refine ⟨hx.1, fun hxe => ?_⟩
  rw [mem_singleton_iff.1 hxe] at hx
  exact lt_irrefl e hx.2

/-- Greedy is idempotent. -/
@[simp] lemma greedy_greedy (hM : M.E = univ) (S : Finset E) :
    greedy M (greedy M S) = greedy M S :=
  greedy_eq_self_of_indep (indep_greedy hM S)

/-- **Insertion form** of the merge law. -/
theorem greedy_insert_eq_greedy_insert_greedy (hM : M.E = univ) (e : E) (S : Finset E) :
    greedy M (insert e S) = greedy M (insert e (greedy M S)) := by
  classical
  rw [Finset.insert_eq, Finset.insert_eq, greedy_union_eq_greedy_union_greedy hM,
    greedy_union_eq_greedy_union_greedy hM {e} (greedy M S), greedy_greedy hM]

/-- **Sandwich property**: every set between the greedy basis of `S` and `S` has the
same greedy basis. -/
theorem greedy_eq_greedy_of_greedy_subset_of_subset (hM : M.E = univ)
    (h₁ : greedy M S ⊆ T) (h₂ : T ⊆ S) : greedy M T = greedy M S := by
  refine greedy_eq_greedy_of_closure_inter_eq hM fun P hP => ?_
  refine (M.closure_subset_closure (inter_subset_inter_left _ h₂)).antisymm ?_
  rw [← closure_greedy_inter hM S hP]
  exact M.closure_subset_closure (inter_subset_inter_left _ h₁)

/-- **Deletion stability**: deleting an element that greedy does not select leaves the
greedy basis unchanged. -/
theorem greedy_erase_of_notMem_greedy (hM : M.E = univ) (he : e ∉ greedy M S) :
    greedy M (S.erase e) = greedy M S := by
  classical
  refine greedy_eq_greedy_of_greedy_subset_of_subset hM (fun x hx => ?_)
    (Finset.erase_subset _ _)
  exact Finset.mem_erase.2 ⟨fun hxe => he (hxe ▸ hx), greedy_subset M S hx⟩

end MonoidProduct.Matroid
