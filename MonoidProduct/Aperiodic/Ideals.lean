import MonoidProduct.Aperiodic.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Lattice

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Principal ideals and the `J`-depth

Principal right, left and two-sided ideals of a finite monoid, and the depth
parameter the AGS recursion descends on.

The key algebraic output is Schützenberger's lemma (`lem:singleton` of the
paper):

  `y = m  ↔  y ∈ mM  ∧  y ∈ Mm  ∧  m ∈ MyM`,

an element of an aperiodic monoid is determined by its three principal ideals.
Both nontrivial implications are the sandwich lemma.

For the recursion the descent measure is **not** the cardinal rank
`|M| - |MmM|`, but the *ideal-chain depth*

  `jLevel m = ` the length of the longest strictly increasing chain of principal
  two-sided ideals starting at `MmM`,

so that a strict inclusion `MmM ⊊ MrM` gives `jLevel r < jLevel m` directly.
That is what makes the final exponent `D_J(M)` rather than `|M|`, and `D_J` can
be exponentially smaller — a free semilattice on `k` atoms has `|M| = 2^k` but
depth `k`.  `jLevel` is defined by strong recursion on the (finite) set of
strictly larger principal ideals, which avoids `Order.coheight` and its `ℕ∞`
coercions.
-/

namespace MonoidProduct

section
variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## Principal ideals -/

/-- The principal right ideal `aM`. -/
def rightIdeal (a : M) : Finset M := Finset.univ.filter fun x => ∃ q, a * q = x

/-- The principal left ideal `Ma`. -/
def leftIdeal (a : M) : Finset M := Finset.univ.filter fun x => ∃ p, p * a = x

/-- The principal two-sided ideal `MaM`. -/
def twoIdeal (a : M) : Finset M :=
  Finset.univ.filter fun x => ∃ p q, p * a * q = x

@[simp] lemma mem_rightIdeal {a x : M} : x ∈ rightIdeal a ↔ ∃ q, a * q = x := by
  simp [rightIdeal]

@[simp] lemma mem_leftIdeal {a x : M} : x ∈ leftIdeal a ↔ ∃ p, p * a = x := by
  simp [leftIdeal]

@[simp] lemma mem_twoIdeal {a x : M} : x ∈ twoIdeal a ↔ ∃ p q, p * a * q = x := by
  simp [twoIdeal]

lemma self_mem_rightIdeal (a : M) : a ∈ rightIdeal a :=
  mem_rightIdeal.2 ⟨1, mul_one a⟩

lemma self_mem_leftIdeal (a : M) : a ∈ leftIdeal a :=
  mem_leftIdeal.2 ⟨1, one_mul a⟩

lemma self_mem_twoIdeal (a : M) : a ∈ twoIdeal a :=
  mem_twoIdeal.2 ⟨1, 1, by simp⟩

/-! ### Products generate smaller ideals -/

lemma rightIdeal_mul_subset (a b : M) : rightIdeal (a * b) ⊆ rightIdeal a := by
  intro x hx
  obtain ⟨q, rfl⟩ := mem_rightIdeal.1 hx
  exact mem_rightIdeal.2 ⟨b * q, by rw [← mul_assoc]⟩

lemma leftIdeal_mul_subset (a b : M) : leftIdeal (a * b) ⊆ leftIdeal b := by
  intro x hx
  obtain ⟨p, rfl⟩ := mem_leftIdeal.1 hx
  exact mem_leftIdeal.2 ⟨p * a, by rw [mul_assoc]⟩

lemma twoIdeal_mul_subset_left (a b : M) : twoIdeal (a * b) ⊆ twoIdeal a := by
  intro x hx
  obtain ⟨p, q, rfl⟩ := mem_twoIdeal.1 hx
  exact mem_twoIdeal.2 ⟨p, b * q, by simp [mul_assoc]⟩

lemma twoIdeal_mul_subset_right (a b : M) : twoIdeal (a * b) ⊆ twoIdeal b := by
  intro x hx
  obtain ⟨p, q, rfl⟩ := mem_twoIdeal.1 hx
  exact mem_twoIdeal.2 ⟨p * a, q, by simp [mul_assoc]⟩

lemma rightIdeal_subset_of_mem {a b : M} (h : a ∈ rightIdeal b) :
    rightIdeal a ⊆ rightIdeal b := by
  obtain ⟨q, rfl⟩ := mem_rightIdeal.1 h
  exact rightIdeal_mul_subset _ _

lemma leftIdeal_subset_of_mem {a b : M} (h : a ∈ leftIdeal b) :
    leftIdeal a ⊆ leftIdeal b := by
  obtain ⟨p, rfl⟩ := mem_leftIdeal.1 h
  exact leftIdeal_mul_subset _ _

@[simp] lemma rightIdeal_one : rightIdeal (1 : M) = Finset.univ := by
  ext x
  simp only [mem_rightIdeal, Finset.mem_univ, iff_true]
  exact ⟨x, one_mul x⟩

@[simp] lemma leftIdeal_one : leftIdeal (1 : M) = Finset.univ := by
  ext x
  simp only [mem_leftIdeal, Finset.mem_univ, iff_true]
  exact ⟨x, mul_one x⟩

/-- Membership in a two-sided ideal is transitive along generators. -/
lemma twoIdeal_subset_of_mem {a b : M} (h : a ∈ twoIdeal b) :
    twoIdeal a ⊆ twoIdeal b := by
  obtain ⟨p, q, rfl⟩ := mem_twoIdeal.1 h
  exact (twoIdeal_mul_subset_left _ _).trans (twoIdeal_mul_subset_right _ _)

lemma mem_twoIdeal_iff_subset {a b : M} : a ∈ twoIdeal b ↔ twoIdeal a ⊆ twoIdeal b :=
  ⟨twoIdeal_subset_of_mem, fun h => h (self_mem_twoIdeal a)⟩

end

/-! ## Schützenberger's lemma -/

section
variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **Schützenberger's lemma** (`lem:singleton`): in an aperiodic monoid an
element is determined by its right
ideal, its left ideal, and its two-sided ideal.  Both nontrivial steps are the
sandwich lemma. -/
theorem eq_iff_mem_ideals (m y : M) :
    y = m ↔ y ∈ rightIdeal m ∧ y ∈ leftIdeal m ∧ m ∈ twoIdeal y := by
  constructor
  · rintro rfl
    exact ⟨self_mem_rightIdeal y, self_mem_leftIdeal y, self_mem_twoIdeal y⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨q, hq⟩ := mem_rightIdeal.1 h1
    obtain ⟨p, hp⟩ := mem_leftIdeal.1 h2
    obtain ⟨r, s, hrs⟩ := mem_twoIdeal.1 h3
    -- `y = m q = (r y s) q = r · y · (s q)`, so `y = r y`
    have hry : r * y = y := by
      refine sandwich_left (r := s * q) ?_
      calc r * y * (s * q) = (r * y * s) * q := by simp only [mul_assoc]
        _ = m * q := by rw [hrs]
        _ = y := hq
    -- `y = p m = p (r y s) = (p r) · y · s`, so `y = y s`
    have hys : y * s = y := by
      refine sandwich_right (p := p * r) ?_
      calc p * r * y * s = p * (r * y * s) := by simp only [mul_assoc]
        _ = p * m := by rw [hrs]
        _ = y := hp
    calc y = r * y * s := by rw [hry, hys]
      _ = m := hrs

/-- If the `J`-class of `j` is a single `R`-class, a left coordinate can be
deleted from a sandwich that remains `J`-equivalent to `j`. -/
theorem delete_left_of_jClass_one_rightIdeal {j s t : M}
    (hR : ∀ x : M, twoIdeal x = twoIdeal j → rightIdeal x = rightIdeal j)
    (hst : twoIdeal (s * j * t) = twoIdeal j) :
    twoIdeal (j * t) = twoIdeal j ∧ s * j * t = j * t := by
  have hshort_le : twoIdeal (j * t) ⊆ twoIdeal j :=
    twoIdeal_mul_subset_left j t
  have hlong_le : twoIdeal (s * j * t) ⊆ twoIdeal (j * t) := by
    simpa only [mul_assoc] using twoIdeal_mul_subset_right s (j * t)
  have hjt : twoIdeal (j * t) = twoIdeal j := by
    apply Finset.Subset.antisymm hshort_le
    rw [← hst]
    exact hlong_le
  refine ⟨hjt, ?_⟩
  have hright : s * j * t ∈ rightIdeal (j * t) := by
    have hself := self_mem_rightIdeal (s * j * t)
    rw [(hR (s * j * t) hst).trans (hR (j * t) hjt).symm] at hself
    exact hself
  have hleft : s * j * t ∈ leftIdeal (j * t) :=
    mem_leftIdeal.2 ⟨s, by simp only [mul_assoc]⟩
  have htwo : j * t ∈ twoIdeal (s * j * t) := by
    rw [hst, ← hjt]
    exact self_mem_twoIdeal (j * t)
  exact (eq_iff_mem_ideals (j * t) (s * j * t)).2 ⟨hright, hleft, htwo⟩

/-- In a `J`-class that is a single `R`-class, any left multiplier that stays
in the class fixes the element. -/
theorem left_mul_eq_of_jClass_one_rightIdeal {j s : M}
    (hR : ∀ x : M, twoIdeal x = twoIdeal j → rightIdeal x = rightIdeal j)
    (hsj : twoIdeal (s * j) = twoIdeal j) : s * j = j := by
  have hst : twoIdeal (s * j * 1) = twoIdeal j := by simpa using hsj
  simpa using (delete_left_of_jClass_one_rightIdeal hR hst).2

/-- If the `J`-class of `j` is a single `L`-class, a right coordinate can be
deleted from a sandwich that remains `J`-equivalent to `j`. -/
theorem delete_right_of_jClass_one_leftIdeal {j s t : M}
    (hL : ∀ x : M, twoIdeal x = twoIdeal j → leftIdeal x = leftIdeal j)
    (hst : twoIdeal (s * j * t) = twoIdeal j) :
    twoIdeal (s * j) = twoIdeal j ∧ s * j * t = s * j := by
  have hshort_le : twoIdeal (s * j) ⊆ twoIdeal j :=
    twoIdeal_mul_subset_right s j
  have hlong_le : twoIdeal (s * j * t) ⊆ twoIdeal (s * j) :=
    twoIdeal_mul_subset_left (s * j) t
  have hsj : twoIdeal (s * j) = twoIdeal j := by
    apply Finset.Subset.antisymm hshort_le
    rw [← hst]
    exact hlong_le
  refine ⟨hsj, ?_⟩
  have hright : s * j * t ∈ rightIdeal (s * j) :=
    mem_rightIdeal.2 ⟨t, rfl⟩
  have hleft : s * j * t ∈ leftIdeal (s * j) := by
    have hself := self_mem_leftIdeal (s * j * t)
    rw [(hL (s * j * t) hst).trans (hL (s * j) hsj).symm] at hself
    exact hself
  have htwo : s * j ∈ twoIdeal (s * j * t) := by
    rw [hst, ← hsj]
    exact self_mem_twoIdeal (s * j)
  exact (eq_iff_mem_ideals (s * j) (s * j * t)).2 ⟨hright, hleft, htwo⟩

/-- **Word form of one-coordinate deletion.**  If the `J`-class of `j` is one
`R`-class, a product of letters fixes `j` exactly when every letter fixes `j`.
The forward implication uses one-coordinate deletion on each suffix. -/
theorem list_prod_mul_eq_iff_forall_mem_mul_eq_of_jClass_one_rightIdeal {j : M}
    (hR : ∀ x : M, twoIdeal x = twoIdeal j → rightIdeal x = rightIdeal j)
    (w : List M) :
    w.prod * j = j ↔ ∀ a ∈ w, a * j = j := by
  induction w with
  | nil => simp
  | cons a w ih =>
      constructor
      · intro hprod b hb
        have hprod' : a * (w.prod * j) = j := by
          simpa only [List.prod_cons, mul_assoc] using hprod
        have hj_mem : j ∈ twoIdeal (w.prod * j) :=
          mem_twoIdeal.2 ⟨a, 1, by simpa only [mul_one] using hprod'⟩
        have htailJ : twoIdeal (w.prod * j) = twoIdeal j :=
          Finset.Subset.antisymm (twoIdeal_mul_subset_right w.prod j)
            (twoIdeal_subset_of_mem hj_mem)
        have htail : w.prod * j = j :=
          left_mul_eq_of_jClass_one_rightIdeal hR htailJ
        have hhead : a * j = j := by
          calc a * j = a * (w.prod * j) := congrArg (fun x => a * x) htail.symm
            _ = j := hprod'
        rcases List.mem_cons.1 hb with rfl | hb
        · exact hhead
        · exact (ih.1 htail) b hb
      · intro hall
        have hhead : a * j = j := hall a (List.mem_cons_self)
        have htail : w.prod * j = j := ih.2 fun b hb =>
          hall b (List.mem_cons_of_mem a hb)
        calc
          (a :: w).prod * j = a * (w.prod * j) := by
            simp only [List.prod_cons, mul_assoc]
          _ = a * j := by rw [htail]
          _ = j := hhead

/-- For a one-`R` `J`-class, a word remains `J`-equivalent to `j` exactly when
each of its letters does. -/
theorem list_prod_mul_twoIdeal_eq_iff_forall_mem_twoIdeal_eq_of_jClass_one_rightIdeal
    {j : M}
    (hR : ∀ x : M, twoIdeal x = twoIdeal j → rightIdeal x = rightIdeal j)
    (w : List M) :
    twoIdeal (w.prod * j) = twoIdeal j ↔
      ∀ a ∈ w, twoIdeal (a * j) = twoIdeal j := by
  constructor
  · intro hword
    have hword_eq : w.prod * j = j :=
      left_mul_eq_of_jClass_one_rightIdeal hR hword
    have hletters :=
      (list_prod_mul_eq_iff_forall_mem_mul_eq_of_jClass_one_rightIdeal hR w).1 hword_eq
    intro a ha
    rw [hletters a ha]
  · intro hletters
    have hletters_eq : ∀ a ∈ w, a * j = j := fun a ha =>
      left_mul_eq_of_jClass_one_rightIdeal hR (hletters a ha)
    have hword_eq :=
      (list_prod_mul_eq_iff_forall_mem_mul_eq_of_jClass_one_rightIdeal hR w).2 hletters_eq
    rw [hword_eq]

/-- Mixed exact form: the whole word fixes `j` exactly when each letter remains
in its one-`R` `J`-class. -/
theorem list_prod_mul_eq_iff_forall_mem_twoIdeal_eq_of_jClass_one_rightIdeal
    {j : M}
    (hR : ∀ x : M, twoIdeal x = twoIdeal j → rightIdeal x = rightIdeal j)
    (w : List M) :
    w.prod * j = j ↔ ∀ a ∈ w, twoIdeal (a * j) = twoIdeal j := by
  rw [← list_prod_mul_twoIdeal_eq_iff_forall_mem_twoIdeal_eq_of_jClass_one_rightIdeal
    hR w]
  exact ⟨fun h => by rw [h], left_mul_eq_of_jClass_one_rightIdeal hR⟩

/-- In particular, if the product of a word remains in the one-`R`
`J`-class of `j`, then it fixes `j`. -/
theorem list_prod_mul_eq_of_twoIdeal_eq_of_jClass_one_rightIdeal {j : M}
    (hR : ∀ x : M, twoIdeal x = twoIdeal j → rightIdeal x = rightIdeal j)
    {w : List M} (hw : twoIdeal (w.prod * j) = twoIdeal j) :
    w.prod * j = j :=
  left_mul_eq_of_jClass_one_rightIdeal hR hw

/-- Only the identity generates the whole monoid as a right ideal. -/
lemma eq_one_of_rightIdeal_eq_univ {m : M} (h : rightIdeal m = Finset.univ) :
    m = 1 := by
  have h1 : (1 : M) ∈ rightIdeal m := by rw [h]; exact Finset.mem_univ _
  obtain ⟨q, hq⟩ := mem_rightIdeal.1 h1
  exact (mul_eq_one_iff'.1 hq).1

lemma eq_one_of_leftIdeal_eq_univ {m : M} (h : leftIdeal m = Finset.univ) :
    m = 1 := by
  have h1 : (1 : M) ∈ leftIdeal m := by rw [h]; exact Finset.mem_univ _
  obtain ⟨p, hp⟩ := mem_leftIdeal.1 h1
  exact (mul_eq_one_iff'.1 hp).2

lemma rightIdeal_ne_univ {m : M} (h : m ≠ 1) : rightIdeal m ≠ Finset.univ :=
  fun hc => h (eq_one_of_rightIdeal_eq_univ hc)

lemma leftIdeal_ne_univ {m : M} (h : m ≠ 1) : leftIdeal m ≠ Finset.univ :=
  fun hc => h (eq_one_of_leftIdeal_eq_univ hc)

end

/-! ## The `J`-depth -/

section
variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]

/-- The elements whose two-sided ideal strictly contains that of `a`. -/
def aboveJ (a : M) : Finset M := Finset.univ.filter fun b => twoIdeal a ⊂ twoIdeal b

lemma mem_aboveJ {a b : M} : b ∈ aboveJ a ↔ twoIdeal a ⊂ twoIdeal b := by
  simp [aboveJ]

/-- If `MaM ⊊ MbM` then `MbM` has strictly more elements, which is the measure
the recursion below decreases. -/
lemma card_twoIdeal_lt {a b : M} (h : twoIdeal a ⊂ twoIdeal b) :
    (twoIdeal a).card < (twoIdeal b).card := Finset.card_lt_card h

/-- **The `J`-level**: the length of the longest strictly increasing chain of
principal two-sided ideals beginning at `MmM`.  Larger ideals have *smaller*
level, which is the orientation the induction of `thm:main-ags` needs.

The recursion is well founded on the size of the ideal, which strictly increases
at every step.  Using `attach` is what lets `decreasing_by` see the membership
proof of the element the recursive call is made at. -/
def jLevel (m : M) : ℕ :=
  (aboveJ m).attach.sup fun b => jLevel b.1 + 1
termination_by Fintype.card M - (twoIdeal m).card
decreasing_by
  have h1 : (twoIdeal m).card < (twoIdeal b.1).card :=
    Finset.card_lt_card (mem_aboveJ.1 b.2)
  have h2 : (twoIdeal b.1).card ≤ Fintype.card M := Finset.card_le_univ _
  omega

lemma jLevel_eq (m : M) : jLevel m = (aboveJ m).sup fun b => jLevel b + 1 := by
  rw [jLevel]
  exact Finset.sup_attach (aboveJ m) (fun b : M => jLevel b + 1)

/-- The level depends only on the ideal. -/
lemma jLevel_congr {a b : M} (h : twoIdeal a = twoIdeal b) : jLevel a = jLevel b := by
  have haux : aboveJ a = aboveJ b := by
    ext c
    simp [mem_aboveJ, h]
  rw [jLevel_eq, jLevel_eq, haux]

/-- **Strict ideal ascent lowers the level.**  This is the inequality every
recursive call in the AGS induction is justified by. -/
theorem jLevel_lt_of_ssubset {a b : M} (h : twoIdeal a ⊂ twoIdeal b) :
    jLevel b < jLevel a := by
  have hmem : b ∈ aboveJ a := mem_aboveJ.2 h
  have := Finset.le_sup (f := fun c : M => jLevel c + 1) hmem
  rw [← jLevel_eq] at this
  omega

lemma jLevel_antitone {a b : M} (h : twoIdeal a ⊆ twoIdeal b) :
    jLevel b ≤ jLevel a := by
  rcases eq_or_ne (twoIdeal a) (twoIdeal b) with heq | hne
  · exact le_of_eq (jLevel_congr heq).symm
  · exact le_of_lt (jLevel_lt_of_ssubset (lt_of_le_of_ne h hne))

lemma jLevel_le_of_mem_twoIdeal {a b : M} (h : a ∈ twoIdeal b) :
    jLevel b ≤ jLevel a := jLevel_antitone (twoIdeal_subset_of_mem h)

/-- Everything lies in the two-sided ideal of `1`. -/
@[simp] lemma twoIdeal_one : twoIdeal (1 : M) = Finset.univ := by
  ext x
  simp only [mem_twoIdeal, Finset.mem_univ, iff_true]
  exact ⟨x, 1, by simp⟩

@[simp] lemma aboveJ_one : aboveJ (1 : M) = ∅ := by
  ext b
  simp only [mem_aboveJ, Finset.notMem_empty, iff_false, twoIdeal_one]
  intro h
  exact absurd (Finset.Subset.antisymm h.1 (Finset.subset_univ _)) h.ne

@[simp] lemma jLevel_one : jLevel (1 : M) = 0 := by
  rw [jLevel_eq, aboveJ_one, Finset.sup_empty]
  rfl

lemma aboveJ_eq_empty_of_jLevel_eq_zero {m : M} (h : jLevel m = 0) :
    aboveJ m = ∅ := by
  by_contra hne
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have := Finset.le_sup (f := fun c : M => jLevel c + 1) hb
  rw [← jLevel_eq, h] at this
  omega

/-- The maximum level over the monoid: the paper's `D_J(M)`. -/
def jDepth (M : Type*) [Monoid M] [Fintype M] [DecidableEq M] : ℕ :=
  Finset.univ.sup (jLevel : M → ℕ)

lemma jLevel_le_jDepth (m : M) : jLevel m ≤ jDepth M :=
  Finset.le_sup (f := (jLevel : M → ℕ)) (Finset.mem_univ m)

/-- A chain of principal ideals is bounded by the size of the monoid. -/
lemma jLevel_add_card_le (m : M) : jLevel m + (twoIdeal m).card ≤ Fintype.card M := by
  induction hk : Fintype.card M - (twoIdeal m).card using Nat.strong_induction_on
    generalizing m with
  | _ k ih =>
      rcases Finset.eq_empty_or_nonempty (aboveJ m) with hempty | ⟨b, hb⟩
      · rw [jLevel_eq, hempty, Finset.sup_empty]
        simpa using Finset.card_le_univ (twoIdeal m)
      · obtain ⟨c, hc, hcv⟩ := Finset.exists_mem_eq_sup (aboveJ m) ⟨b, hb⟩
          (fun c : M => jLevel c + 1)
        have hlt : (twoIdeal m).card < (twoIdeal c).card :=
          Finset.card_lt_card (mem_aboveJ.1 hc)
        have hub : (twoIdeal c).card ≤ Fintype.card M := Finset.card_le_univ _
        have hrec := ih (Fintype.card M - (twoIdeal c).card) (by omega) c rfl
        rw [jLevel_eq, hcv]
        omega

lemma jLevel_lt_card (m : M) : jLevel m < Fintype.card M := by
  have h := jLevel_add_card_le m
  have h1 : 1 ≤ (twoIdeal m).card :=
    Finset.card_pos.2 ⟨m, self_mem_twoIdeal m⟩
  omega

end

/-! ## Level zero means the identity -/

section
variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- The base case of the AGS recursion: only the identity has level `0`. -/
theorem jLevel_eq_zero_iff {m : M} : jLevel m = 0 ↔ m = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, jLevel_one]⟩
  have hempty := aboveJ_eq_empty_of_jLevel_eq_zero h
  -- otherwise `MmM ⊊ M = M1M` would put `1` above `m`
  have hfull : twoIdeal m = Finset.univ := by
    by_contra hne
    have hss : twoIdeal m ⊂ twoIdeal (1 : M) := by
      rw [twoIdeal_one]
      exact lt_of_le_of_ne (Finset.subset_univ _) hne
    have : (1 : M) ∈ aboveJ m := mem_aboveJ.2 hss
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty _)
  have hone : (1 : M) ∈ twoIdeal m := by rw [hfull]; exact Finset.mem_univ _
  obtain ⟨p, q, hpq⟩ := mem_twoIdeal.1 hone
  have h1 := (mul_eq_one_iff'.1 hpq).1
  exact (mul_eq_one_iff'.1 h1).2

end

end MonoidProduct
