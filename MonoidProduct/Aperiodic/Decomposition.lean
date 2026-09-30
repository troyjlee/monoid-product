import MonoidProduct.Aperiodic.Ideals
import Mathlib.Data.Fintype.Prod

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The Schützenberger decomposition

The decomposition theorem (`thm:decomp` of the paper; Schützenberger;
Aaronson–Grier–Schaeffer [AGS19]): for a target `m ≠ 1` in a finite
aperiodic monoid, the ordered product of a word equals `m` exactly when four
conditions hold, each of which mentions only *infix products* of the word:

* `(U)` some prefix has product `r` and is followed by the letter `a`, for some
  `(r,a) ∈ E m` — the right ideal drops to `mM` exactly here;
* `(V)` symmetrically on the left;
* `(C)` no letter `a` has `m ∉ MaM`;
* `(W)` no infix `a · r · b` has `m ∈ MarM ∩ MrbM` but `m ∉ MarbM`.

The critical output of this file is **not** the equivalence but the three ideal
ascent lemmas `twoIdeal_lt_of_mem_setE/setF/setG`: every `r` occurring in `E`,
`F` or `G` satisfies `MmM ⊊ MrM`, hence `jLevel r < jLevel m`.  That is what
makes the recursion behind `thm:main-ags` descend, and it is proved
from the sandwich lemma alone — no cardinal rank is used.

Indices are half-open throughout.  A prefix of length `i` is `[0,i)` and is
followed by the letter at position `i`; a suffix starting after position `j` is
`[j+1,n)`; a bad infix has endpoint positions `i < j` and middle `[i+1,j)`,
which is empty — product `1` — when `j = i+1`, matching the paper's remark.
-/

namespace MonoidProduct

/-! ## Two arithmetic conveniences for interval products -/

section
variable {M : Type*} [Monoid M] {n : ℕ}

/-- A one-letter interval product is the padded letter, with no side condition:
past the end both sides are `1`. -/
lemma rangeProd_eq_padAt (x : Fin n → M) (i : ℕ) :
    rangeProd x i (i + 1) = padAt x i := by
  rw [rangeProd_succ_right x (le_refl i), rangeProd_self, one_mul]

/-- Peeling the first letter off an interval product. -/
lemma padAt_mul_rangeProd (x : Fin n → M) {j k : ℕ} (h : j + 1 ≤ k) :
    padAt x j * rangeProd x (j + 1) k = rangeProd x j k := by
  rw [← rangeProd_eq_padAt x j, rangeProd_split x (Nat.le_succ j) h]

end

section
variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]

/-! ## The index sets -/

/-- `E m`: pairs `(r,a)` at which the prefix right ideal drops to `mM`. -/
def setE (m : M) : Finset (M × M) :=
  Finset.univ.filter fun ra =>
    rightIdeal (ra.1 * ra.2) = rightIdeal m ∧ rightIdeal ra.1 ≠ rightIdeal m

/-- `F m`: pairs `(a,r)` at which the suffix left ideal drops to `Mm`. -/
def setF (m : M) : Finset (M × M) :=
  Finset.univ.filter fun ar =>
    leftIdeal (ar.1 * ar.2) = leftIdeal m ∧ leftIdeal ar.2 ≠ leftIdeal m

/-- `C m`: the letters that cannot occur at all. -/
def setC (m : M) : Finset M := Finset.univ.filter fun a => m ∉ twoIdeal a

/-- `G m`: the forbidden marked infixes. -/
def setG (m : M) : Finset (M × M × M) :=
  Finset.univ.filter fun arb =>
    m ∈ twoIdeal (arb.1 * arb.2.1) ∧ m ∈ twoIdeal (arb.2.1 * arb.2.2)
      ∧ m ∉ twoIdeal (arb.1 * arb.2.1 * arb.2.2)

@[simp] lemma mem_setE {m r a : M} :
    (r, a) ∈ setE m
      ↔ rightIdeal (r * a) = rightIdeal m ∧ rightIdeal r ≠ rightIdeal m := by
  simp [setE]

@[simp] lemma mem_setF {m a r : M} :
    (a, r) ∈ setF m
      ↔ leftIdeal (a * r) = leftIdeal m ∧ leftIdeal r ≠ leftIdeal m := by
  simp [setF]

@[simp] lemma mem_setC {m a : M} : a ∈ setC m ↔ m ∉ twoIdeal a := by simp [setC]

@[simp] lemma mem_setG {m a r b : M} :
    (a, r, b) ∈ setG m
      ↔ m ∈ twoIdeal (a * r) ∧ m ∈ twoIdeal (r * b)
        ∧ m ∉ twoIdeal (a * r * b) := by
  simp [setG]

/-! ### Loop bounds

The recursion behind `thm:main-ags` iterates over these sets, so all it needs of them
is that they are polynomially many in `|M|`. -/

lemma card_setE_le (m : M) : (setE m).card ≤ Fintype.card M ^ 2 :=
  le_trans (Finset.card_le_univ _) (le_of_eq (by rw [Fintype.card_prod]; ring))

lemma card_setF_le (m : M) : (setF m).card ≤ Fintype.card M ^ 2 :=
  le_trans (Finset.card_le_univ _) (le_of_eq (by rw [Fintype.card_prod]; ring))

lemma card_setC_le (m : M) : (setC m).card ≤ Fintype.card M :=
  Finset.card_le_univ _

lemma card_setG_le (m : M) : (setG m).card ≤ Fintype.card M ^ 3 :=
  le_trans (Finset.card_le_univ _)
    (le_of_eq (by rw [Fintype.card_prod, Fintype.card_prod]; ring))

end

/-! ## Ideal ascent

Every `r` occurring in `E`, `F` or `G` generates a strictly larger two-sided
ideal than the target.  These are the lemmas the recursion descends on. -/

section
variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

theorem twoIdeal_lt_of_mem_setE {m r a : M} (h : (r, a) ∈ setE m) :
    twoIdeal m ⊂ twoIdeal r := by
  obtain ⟨heq, hne⟩ := mem_setE.1 h
  -- `m ∈ (ra)M = mM`, so `m = r a q` and hence `m ∈ MrM`
  have hmem : m ∈ rightIdeal (r * a) := by rw [heq]; exact self_mem_rightIdeal m
  obtain ⟨q, hq⟩ := mem_rightIdeal.1 hmem
  have hmr : m ∈ twoIdeal r :=
    mem_twoIdeal.2 ⟨1, a * q, by rw [one_mul, ← mul_assoc]; exact hq⟩
  refine lt_of_le_of_ne (twoIdeal_subset_of_mem hmr) fun hcon => ?_
  -- were the ideals equal, `r = u m v` would sandwich `m`, forcing `u m = m`
  have hrm : r ∈ twoIdeal m := by rw [hcon]; exact self_mem_twoIdeal r
  obtain ⟨u, v, huv⟩ := mem_twoIdeal.1 hrm
  have hsand : u * m * (v * a * q) = m := by
    calc u * m * (v * a * q) = u * m * v * (a * q) := by simp only [mul_assoc]
      _ = r * (a * q) := by rw [huv]
      _ = r * a * q := by rw [mul_assoc]
      _ = m := hq
  have hum : u * m = m := sandwich_left hsand
  have hrmem : r ∈ rightIdeal m := by
    refine mem_rightIdeal.2 ⟨v, ?_⟩
    calc m * v = u * m * v := by rw [hum]
      _ = r := huv
  exact hne (Finset.Subset.antisymm (rightIdeal_subset_of_mem hrmem)
    ((by rw [← heq]; exact rightIdeal_mul_subset r a) :
      rightIdeal m ⊆ rightIdeal r))

theorem twoIdeal_lt_of_mem_setF {m a r : M} (h : (a, r) ∈ setF m) :
    twoIdeal m ⊂ twoIdeal r := by
  obtain ⟨heq, hne⟩ := mem_setF.1 h
  have hmem : m ∈ leftIdeal (a * r) := by rw [heq]; exact self_mem_leftIdeal m
  obtain ⟨p, hp⟩ := mem_leftIdeal.1 hmem
  have hmr : m ∈ twoIdeal r :=
    mem_twoIdeal.2 ⟨p * a, 1, by rw [mul_one, mul_assoc]; exact hp⟩
  refine lt_of_le_of_ne (twoIdeal_subset_of_mem hmr) fun hcon => ?_
  have hrm : r ∈ twoIdeal m := by rw [hcon]; exact self_mem_twoIdeal r
  obtain ⟨u, v, huv⟩ := mem_twoIdeal.1 hrm
  have hsand : p * a * u * m * v = m := by
    calc p * a * u * m * v = p * a * (u * m * v) := by simp only [mul_assoc]
      _ = p * a * r := by rw [huv]
      _ = p * (a * r) := by rw [mul_assoc]
      _ = m := hp
  have hmv : m * v = m := sandwich_right hsand
  have hrmem : r ∈ leftIdeal m := by
    refine mem_leftIdeal.2 ⟨u, ?_⟩
    calc u * m = u * (m * v) := by rw [hmv]
      _ = u * m * v := by rw [mul_assoc]
      _ = r := huv
  exact hne (Finset.Subset.antisymm (leftIdeal_subset_of_mem hrmem)
    ((by rw [← heq]; exact leftIdeal_mul_subset a r) :
      leftIdeal m ⊆ leftIdeal r))

theorem twoIdeal_lt_of_mem_setG {m a r b : M} (h : (a, r, b) ∈ setG m) :
    twoIdeal m ⊂ twoIdeal r := by
  obtain ⟨har, hrb, hnarb⟩ := mem_setG.1 h
  have hmr : m ∈ twoIdeal r := twoIdeal_mul_subset_right a r har
  refine lt_of_le_of_ne (twoIdeal_subset_of_mem hmr) fun hcon => ?_
  have hrm : r ∈ twoIdeal m := by rw [hcon]; exact self_mem_twoIdeal r
  obtain ⟨u, v, huv⟩ := mem_twoIdeal.1 hrm
  obtain ⟨y, z, hyz⟩ := mem_twoIdeal.1 hrb
  -- `r = u m v = u (y (r b) z) v`, a sandwich of `r`, so `r · (b z v) = r`
  have hsand : u * y * r * (b * z * v) = r := by
    calc u * y * r * (b * z * v) = u * (y * (r * b) * z) * v := by
          simp only [mul_assoc]
      _ = u * m * v := by rw [hyz]
      _ = r := huv
  have hrbzv : r * (b * z * v) = r := sandwich_right hsand
  obtain ⟨w, t, hwt⟩ := mem_twoIdeal.1 har
  -- substituting `r` back into `m = w (a r) t` puts `m` inside `M a r b M`
  refine hnarb (mem_twoIdeal.2 ⟨w, z * v * t, ?_⟩)
  calc w * (a * r * b) * (z * v * t)
      = w * (a * (r * (b * z * v))) * t := by simp only [mul_assoc]
    _ = w * (a * r) * t := by rw [hrbzv]
    _ = m := hwt

/-! ### The level drops

These three inequalities are what every recursive call of the recursion
behind `thm:main-ags` is justified by.  Note that nothing cardinal is used:
the measure is the `J`-level
of `MonoidProduct/Aperiodic/Ideals.lean`, which drops by at least one at each strict
ideal ascent regardless of how the ideals' sizes compare. -/

theorem jLevel_lt_of_mem_setE {m r a : M} (h : (r, a) ∈ setE m) :
    jLevel r < jLevel m :=
  jLevel_lt_of_ssubset (twoIdeal_lt_of_mem_setE h)

theorem jLevel_lt_of_mem_setF {m a r : M} (h : (a, r) ∈ setF m) :
    jLevel r < jLevel m :=
  jLevel_lt_of_ssubset (twoIdeal_lt_of_mem_setF h)

theorem jLevel_lt_of_mem_setG {m a r b : M} (h : (a, r, b) ∈ setG m) :
    jLevel r < jLevel m :=
  jLevel_lt_of_ssubset (twoIdeal_lt_of_mem_setG h)

end

/-! ## The four conditions -/

section
variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M] {n : ℕ}

/-- `(U)`: some prefix `[0,i)` has product `r` and is followed by the letter
`a`, for some `(r,a) ∈ E m`. -/
def UEvent (m : M) (x : Fin n → M) : Prop :=
  ∃ i : ℕ, i < n ∧ ∃ r a : M, (r, a) ∈ setE m ∧
    rangeProd x 0 i = r ∧ padAt x i = a

/-- `(V)`: some suffix `[j+1,n)` has product `r` and is preceded by the letter
`a`, for some `(a,r) ∈ F m`. -/
def VEvent (m : M) (x : Fin n → M) : Prop :=
  ∃ j : ℕ, j < n ∧ ∃ a r : M, (a, r) ∈ setF m ∧
    padAt x j = a ∧ rangeProd x (j + 1) n = r

/-- `(C)` is the negation of this: a letter that cannot occur. -/
def badLetter (m : M) (x : Fin n → M) : Prop := ∃ i : Fin n, x i ∈ setC m

/-- `(W)` is the negation of this: a forbidden marked infix, with endpoint
positions `i < j` and middle `[i+1,j)`. -/
def badInfix (m : M) (x : Fin n → M) : Prop :=
  ∃ i j : ℕ, i < j ∧ j < n ∧ ∃ a r b : M, (a, r, b) ∈ setG m ∧
    padAt x i = a ∧ rangeProd x (i + 1) j = r ∧ padAt x j = b

/-! ### Deciding the four conditions

The unbounded `∃ i : ℕ` are all bounded by `n`, so each condition is decidable;
this is what lets `MonoidProduct/Aperiodic/Examples.lean` check the decomposition by
brute force on tiny monoids. -/

instance (m : M) (x : Fin n → M) : Decidable (UEvent m x) :=
  decidable_of_iff
    (∃ i : Fin n, ∃ r a : M, (r, a) ∈ setE m ∧
      rangeProd x 0 (i : ℕ) = r ∧ padAt x (i : ℕ) = a)
    ⟨fun ⟨i, h⟩ => ⟨i, i.isLt, h⟩, fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩⟩

instance (m : M) (x : Fin n → M) : Decidable (VEvent m x) :=
  decidable_of_iff
    (∃ j : Fin n, ∃ a r : M, (a, r) ∈ setF m ∧
      padAt x (j : ℕ) = a ∧ rangeProd x ((j : ℕ) + 1) n = r)
    ⟨fun ⟨j, h⟩ => ⟨j, j.isLt, h⟩, fun ⟨j, hj, h⟩ => ⟨⟨j, hj⟩, h⟩⟩

instance (m : M) (x : Fin n → M) : Decidable (badLetter m x) :=
  inferInstanceAs (Decidable (∃ _ : Fin n, _))

instance (m : M) (x : Fin n → M) : Decidable (badInfix m x) :=
  decidable_of_iff
    (∃ i : Fin n, ∃ j : Fin n, (i : ℕ) < (j : ℕ) ∧
      ∃ a r b : M, (a, r, b) ∈ setG m ∧
        padAt x (i : ℕ) = a ∧ rangeProd x ((i : ℕ) + 1) (j : ℕ) = r ∧
        padAt x (j : ℕ) = b)
    ⟨fun ⟨i, j, hij, h⟩ => ⟨i, j, hij, j.isLt, h⟩,
     fun ⟨i, j, hij, hjn, h⟩ => ⟨⟨i, Nat.lt_trans hij hjn⟩, ⟨j, hjn⟩, hij, h⟩⟩

end

/-! ## The decomposition theorem -/

section
variable {M : Type*} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
variable {n : ℕ}

/-- The first place a decidable predicate on `[0,n]` switches on. -/
private lemma exists_boundary (P : ℕ → Prop) [DecidablePred P] (n : ℕ)
    (h0 : ¬ P 0) (hn : P n) : ∃ i, i < n ∧ ¬ P i ∧ P (i + 1) := by
  have hex : ∃ k, P k := ⟨n, hn⟩
  have hPk : P (Nat.find hex) := Nat.find_spec hex
  have hkle : Nat.find hex ≤ n := Nat.find_le hn
  have hk0 : Nat.find hex ≠ 0 := fun hc => h0 (hc ▸ hPk)
  refine ⟨Nat.find hex - 1, by omega, Nat.find_min hex (by omega), ?_⟩
  rw [show Nat.find hex - 1 + 1 = Nat.find hex from by omega]
  exact hPk

/-- **Equation `eq:window`** in the proof of `thm:decomp`: under `(C)` and `(W)`, *every*
infix product generates a two-sided ideal containing the target.  Induction on
the length of the infix: the empty infix gives `M1M = M`, a single letter is
`(C)`, and a longer one splits as `a · r · b` and is handed to `(W)`. -/
theorem mem_twoIdeal_rangeProd {m : M} {x : Fin n → M}
    (hC : ¬ badLetter m x) (hW : ¬ badInfix m x) :
    ∀ d i j : ℕ, j ≤ i + d → i ≤ j → j ≤ n → m ∈ twoIdeal (rangeProd x i j) := by
  intro d
  induction d with
  | zero =>
      intro i j hd hij _
      rw [show j = i from by omega, rangeProd_self, twoIdeal_one]
      exact Finset.mem_univ _
  | succ d ih =>
      intro i j hd hij hjn
      rcases Nat.lt_or_ge j (i + 1) with h1 | h1
      · rw [show j = i from by omega, rangeProd_self, twoIdeal_one]
        exact Finset.mem_univ _
      rcases Nat.lt_or_ge j (i + 2) with h2 | h2
      · -- a single letter: this is exactly `(C)`
        have hji : j = i + 1 := by omega
        subst hji
        have hin : i < n := by omega
        rw [rangeProd_eq_padAt x i, padAt_of_lt x hin]
        by_contra hcon
        exact hC ⟨⟨i, hin⟩, mem_setC.2 hcon⟩
      -- two letters or more: split off the first and the last
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hij' : i + 1 ≤ j' := by omega
      have hj'n : j' < n := by omega
      have har : padAt x i * rangeProd x (i + 1) j' = rangeProd x i j' :=
        padAt_mul_rangeProd x hij'
      have hrb : rangeProd x (i + 1) j' * padAt x j'
          = rangeProd x (i + 1) (j' + 1) := (rangeProd_succ_right x hij').symm
      have hfull : padAt x i * rangeProd x (i + 1) j' * padAt x j'
          = rangeProd x i (j' + 1) := by
        rw [har, ← rangeProd_succ_right x (by omega : i ≤ j')]
      have hL : m ∈ twoIdeal (padAt x i * rangeProd x (i + 1) j') := by
        rw [har]; exact ih i j' (by omega) (by omega) (by omega)
      have hR : m ∈ twoIdeal (rangeProd x (i + 1) j' * padAt x j') := by
        rw [hrb]; exact ih (i + 1) (j' + 1) (by omega) (by omega) (by omega)
      rw [← hfull]
      by_contra hcon
      exact hW ⟨i, j', by omega, hj'n, _, _, _,
        mem_setG.2 ⟨hL, hR, hcon⟩, rfl, rfl, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **`thm:decomp`**, the Schützenberger decomposition of the target test: for
`m ≠ 1` in a finite aperiodic monoid, the ordered product of a word is `m`
exactly when `(U)`, `(V)`, `(C)` and `(W)` all hold. -/
theorem orderedProd_eq_iff {m : M} (hm : m ≠ 1) (x : Fin n → M) :
    orderedProd x = m ↔
      UEvent m x ∧ VEvent m x ∧ ¬ badLetter m x ∧ ¬ badInfix m x := by
  classical
  constructor
  · intro hprod
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (U): the first prefix whose right ideal has already dropped to `mM`
      obtain ⟨i, hin, hlt, heq⟩ := exists_boundary
        (fun k => rightIdeal (rangeProd x 0 k) = rightIdeal m) n
        (by
          show ¬ rightIdeal (rangeProd x 0 0) = rightIdeal m
          rw [rangeProd_self, rightIdeal_one]
          exact fun hc => rightIdeal_ne_univ hm hc.symm)
        (by
          show rightIdeal (rangeProd x 0 n) = rightIdeal m
          rw [← orderedProd_eq_rangeProd, hprod])
      refine ⟨i, hin, rangeProd x 0 i, padAt x i, mem_setE.2 ⟨?_, hlt⟩, rfl, rfl⟩
      rw [← rangeProd_succ_right x (Nat.zero_le i)]
      exact heq
    · -- (V): the last suffix whose left ideal is still `Mm`
      obtain ⟨t, htn, hlt, heq⟩ := exists_boundary
        (fun k => leftIdeal (rangeProd x (n - k) n) = leftIdeal m) n
        (by
          show ¬ leftIdeal (rangeProd x (n - 0) n) = leftIdeal m
          rw [Nat.sub_zero, rangeProd_self, leftIdeal_one]
          exact fun hc => leftIdeal_ne_univ hm hc.symm)
        (by
          show leftIdeal (rangeProd x (n - n) n) = leftIdeal m
          rw [Nat.sub_self, ← orderedProd_eq_rangeProd, hprod])
      refine ⟨n - (t + 1), by omega, padAt x (n - (t + 1)),
        rangeProd x (n - (t + 1) + 1) n, mem_setF.2 ⟨?_, ?_⟩, rfl, rfl⟩
      · rw [padAt_mul_rangeProd x (by omega : n - (t + 1) + 1 ≤ n)]
        exact heq
      · rw [show n - (t + 1) + 1 = n - t from by omega]
        exact hlt
    · -- (C): every letter of the word lies in the ideal generated by the word
      rintro ⟨i, hi⟩
      refine mem_setC.1 hi (mem_twoIdeal.2
        ⟨rangeProd x 0 (i : ℕ), rangeProd x ((i : ℕ) + 1) n, ?_⟩)
      have hx : x i = padAt x (i : ℕ) := (padAt_of_lt x i.isLt).symm
      rw [hx, mul_assoc, padAt_mul_rangeProd x (by omega : (i : ℕ) + 1 ≤ n),
        rangeProd_split x (Nat.zero_le _) (le_of_lt i.isLt),
        ← orderedProd_eq_rangeProd, hprod]
    · -- (W): likewise for a marked infix
      rintro ⟨i, j, hij, hjn, a, r, b, hG, rfl, rfl, rfl⟩
      refine (mem_setG.1 hG).2.2 (mem_twoIdeal.2
        ⟨rangeProd x 0 i, rangeProd x (j + 1) n, ?_⟩)
      have hmid : padAt x i * rangeProd x (i + 1) j * padAt x j
          = rangeProd x i (j + 1) := by
        rw [padAt_mul_rangeProd x (by omega : i + 1 ≤ j),
          ← rangeProd_succ_right x (by omega : i ≤ j)]
      rw [hmid, rangeProd_split x (Nat.zero_le i) (by omega : i ≤ j + 1),
        rangeProd_split x (Nat.zero_le (j + 1)) (by omega : j + 1 ≤ n),
        ← orderedProd_eq_rangeProd, hprod]
  · rintro ⟨hU, hV, hC, hW⟩
    -- `(U)` puts the product in `mM`, `(V)` in `Mm`, and `(C)`+`(W)` put `m` in
    -- its two-sided ideal; in an aperiodic monoid those three force equality.
    obtain ⟨i, hin, r, a, hE, hri, hai⟩ := hU
    obtain ⟨j, hjn, a', r', hF, haj, hrj⟩ := hV
    have hright : orderedProd x ∈ rightIdeal m := by
      have hpre : rangeProd x 0 (i + 1) = r * a := by
        rw [rangeProd_succ_right x (Nat.zero_le i), hri, hai]
      have h2 : orderedProd x ∈ rightIdeal (rangeProd x 0 (i + 1)) :=
        mem_rightIdeal.2 ⟨rangeProd x (i + 1) n, by
          rw [rangeProd_split x (Nat.zero_le _) (by omega : i + 1 ≤ n),
            ← orderedProd_eq_rangeProd]⟩
      rwa [hpre, (mem_setE.1 hE).1] at h2
    have hleft : orderedProd x ∈ leftIdeal m := by
      have hsuf : rangeProd x j n = a' * r' := by
        rw [← padAt_mul_rangeProd x (by omega : j + 1 ≤ n), haj, hrj]
      have h2 : orderedProd x ∈ leftIdeal (rangeProd x j n) :=
        mem_leftIdeal.2 ⟨rangeProd x 0 j, by
          rw [rangeProd_split x (Nat.zero_le _) (le_of_lt hjn),
            ← orderedProd_eq_rangeProd]⟩
      rwa [hsuf, (mem_setF.1 hF).1] at h2
    have htwo : m ∈ twoIdeal (orderedProd x) := by
      rw [orderedProd_eq_rangeProd]
      exact mem_twoIdeal_rangeProd hC hW n 0 n (by omega) (Nat.zero_le n)
        (le_refl n)
    exact (eq_iff_mem_ideals m (orderedProd x)).2 ⟨hright, hleft, htwo⟩

end

end MonoidProduct
