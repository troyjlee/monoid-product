import MonoidProduct.Trichotomy.Index
import MonoidProduct.Width.BreadthBounds
import MonoidProduct.Aperiodic.Ideals
import MonoidProduct.Capped.RTrivial
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Small clauses of the introduction: `β ≥ ι`, the three introductory examples,
and aperiodicity as the absence of subgroups

`monoid.tex`, introduction, and the remark after `thm:main-ags`.  Each clause below is stated in the paper in one
sentence and used only for orientation.

* a finite `M` is aperiodic iff it has no nontrivial subgroup:
  `isAperiodicMonoid_iff_not_hasNontrivialSubgroup`.
* `β(M) ≥ ι(M)` for nontrivial `M`: `aperiodicIndex_le_of_isBreadthBound`
  (every breadth bound), `aperiodicIndex_le_breadth`, `aperiodicIndex_le_breadth_comm`.
  The witness: some `a` has distinct powers `1, a, …, a^ι`
  (`exists_pow_injOn_aperiodicIndex`) and the word `a^ι` has no shorter core
  (`aperiodicIndex_le_card_of_isCore`).
* `ex:max`, `β(ℕ, max) = 1`: `MaxNat.isBreadthBound_one`,
  `MaxNat.breadth_eq_one`, `MaxNat.breadth_id_eq_one`.
* `ex:union`, `β(2^{[m]}, ∪) = m = log₂|M|`: `UnionSet.breadth_id_eq`,
  `UnionSet.breadth_id_eq_log`.
* remark after `thm:main-ags`, `D_J(2^{[m]}, ∪) = m`: `UnionSet.jDepth_eq`
  (via `UnionSet.jLevel_eq_card`).
* `ex:capped-addition`, `ι = m`, the powers of `1` being distinct:
  `Capped.aperiodicIndex_eq`, `Capped.gen_pow_val`.

**Conventions.**  `breadth` is an `sInf` over `ℕ` (`0` when no bound exists),
so the honest form of "`β ≥ ι`, where `β` may be infinite" is the statement
about *every* breadth bound, `aperiodicIndex_le_of_isBreadthBound`; the
`breadth` form needs a bound to exist, which `exists_isBreadthBound` supplies
in the commutative case.  `aperiodicIndex` is the least `k ≥ 1` with
`x^k = x^{k+1}` for all `x` (`Trichotomy/Index.lean`), so for `m = 0` the
trivial `Capped 0` has index `1`, and the capped clause is stated for
`m ≥ 1`.  The union monoid is modelled by the type synonym `UnionSet m` of
`Finset (Fin m)` with `∪` and `∅` (Mathlib's `Finset` monoid structures are
pointwise, not by union); `(ℕ, max)` is the synonym `MaxNat` with identity
`0`, an infinite monoid, for which breadth is defined without finiteness.

**Subgroups.**  A subgroup of a monoid need not share the monoid's identity,
so `IsSubgroupAt S e` asks for a subset `S` closed under products, with `e ∈ S`
a two-sided identity on `S` and every element of `S` invertible in `S`
relative to `e`.  One direction holds in every monoid
(`not_hasNontrivialSubgroup_of_aperiodic`); the other is where finiteness
enters: a non-stabilising `a` has eventually periodic powers, and the powers
`a^{t + s}` past a multiple `t` of the period form a cyclic group with
identity `a^t` (`hasNontrivialSubgroup_of_not_aperiodic`).
-/

namespace MonoidProduct

/-! ## Periodic powers -/

section Periodic

variable {M : Type*} [Monoid M]

/-- **Periodicity propagates**: if `a^{i+p} = a^i` then `a^{s + c·p} = a^s`
for every `s ≥ i` and every `c`. -/
lemma pow_add_mul_period {a : M} {i p : ℕ} (h : a ^ (i + p) = a ^ i) {s : ℕ}
    (hs : i ≤ s) (c : ℕ) : a ^ (s + c * p) = a ^ s := by
  induction c with
  | zero => simp
  | succ c ih =>
      have hsplit : s + (c + 1) * p = (i + p) + (s + c * p - i) := by
        rw [add_one_mul]; omega
      rw [hsplit, pow_add, h, ← pow_add, show i + (s + c * p - i) = s + c * p by omega, ih]

/-- In an aperiodic monoid a repetition `a^i = a^j` (`i < j`) among the powers
forces stabilisation from `i` on. -/
lemma pow_succ_eq_of_pow_eq [IsAperiodicMonoid M] {a : M} {i j : ℕ} (hij : i < j)
    (h : a ^ i = a ^ j) {t : ℕ} (ht : i ≤ t) : a ^ t = a ^ (t + 1) := by
  have hper : a ^ (i + (j - i)) = a ^ i := by rw [show i + (j - i) = j by omega, h]
  obtain ⟨N, -, hN⟩ := IsAperiodicMonoid.stabilizes a
  have hNp : N ≤ t + N * (j - i) := le_add_left (Nat.le_mul_of_pos_right N (by omega))
  calc a ^ t = a ^ (t + N * (j - i)) := (pow_add_mul_period hper ht N).symm
    _ = a ^ (t + N * (j - i) + 1) := pow_stab hN hNp
    _ = a ^ (t + 1 + N * (j - i)) := by rw [add_right_comm]
    _ = a ^ (t + 1) := pow_add_mul_period hper (by omega) N

end Periodic

/-! ## `β ≥ ι` -/

section IndexBreadth

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **Distinct powers below the index**: in a nontrivial finite aperiodic
monoid some `a` has pairwise distinct powers `1, a, …, a^ι`. -/
theorem exists_pow_injOn_aperiodicIndex [Nontrivial M] :
    ∃ a : M, ∀ i j : ℕ, i ≤ aperiodicIndex M → j ≤ aperiodicIndex M →
      a ^ i = a ^ j → i = j := by
  have hι := one_le_aperiodicIndex (M := M)
  obtain ⟨a, ha⟩ := exists_pow_ne_of_lt_aperiodicIndex (M := M)
    (r := aperiodicIndex M - 1) (by omega)
  refine ⟨a, fun i j hi hj hij => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ha (pow_succ_eq_of_pow_eq hlt hij (by omega))
  · exact ha (pow_succ_eq_of_pow_eq hlt hij.symm (by omega))

/-- The scattered subword of a constant word on `u` multiplies to a power. -/
lemma subwordProd_const {σ : Type} (letter : σ → M) (s : σ) {n : ℕ}
    (u : Finset (Fin n)) :
    subwordProd letter (fun _ : Fin n => s) u = letter s ^ u.card := by
  rw [subwordProd, ← orderedProd_eq_prod_ofFn, orderedProd_gLetter]

/-- **The word `a^ι` has no shorter core**: with `a` as in
`exists_pow_injOn_aperiodicIndex`, every core of the constant word of `ι`
copies of `a` has all `ι` positions. -/
theorem aperiodicIndex_le_card_of_isCore {σ : Type} {letter : σ → M} {s : σ}
    (hs : ∀ i j : ℕ, i ≤ aperiodicIndex M → j ≤ aperiodicIndex M →
      letter s ^ i = letter s ^ j → i = j)
    {u : Finset (Fin (aperiodicIndex M))}
    (hu : IsCore letter (fun _ => s) u) : aperiodicIndex M ≤ u.card := by
  have hcard : u.card ≤ aperiodicIndex M := by
    simpa using Finset.card_le_univ u
  have hprod : letter s ^ u.card = letter s ^ aperiodicIndex M := by
    rw [← subwordProd_const, hu, ← subwordProd_univ, subwordProd_const,
      Finset.card_univ, Fintype.card_fin]
  exact (hs _ _ hcard le_rfl hprod).ge

/-- **`β ≥ ι`, for every breadth bound**: if the alphabet reaches
every monoid element, every breadth bound of a nontrivial finite aperiodic
monoid is at least its aperiodicity index.  This is the paper's statement with
`β` possibly infinite. -/
theorem aperiodicIndex_le_of_isBreadthBound [Nontrivial M] {σ : Type} {letter : σ → M}
    (hsurj : Function.Surjective letter) {b : ℕ} (hb : IsBreadthBound letter b) :
    aperiodicIndex M ≤ b := by
  obtain ⟨a, ha⟩ := exists_pow_injOn_aperiodicIndex (M := M)
  obtain ⟨s, rfl⟩ := hsurj a
  obtain ⟨u, hub, hu⟩ := hb (aperiodicIndex M) fun _ => s
  exact (aperiodicIndex_le_card_of_isCore ha hu).trans hub

/-- **`ι ≤ β`** whenever the breadth is finite. -/
theorem aperiodicIndex_le_breadth [Nontrivial M] {σ : Type} {letter : σ → M}
    (hsurj : Function.Surjective letter) (h : ∃ b, IsBreadthBound letter b) :
    aperiodicIndex M ≤ breadth letter :=
  aperiodicIndex_le_of_isBreadthBound hsurj (isBreadthBound_breadth h)

end IndexBreadth

section IndexBreadthComm

variable {M : Type} [CommMonoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]

/-- **`ι(M) ≤ β(M)`** for a nontrivial finite commutative aperiodic monoid,
with no side condition (the breadth is finite, `exists_isBreadthBound`). -/
theorem aperiodicIndex_le_breadth_comm [Nontrivial M] :
    aperiodicIndex M ≤ breadth (id : M → M) :=
  aperiodicIndex_le_breadth Function.surjective_id (exists_isBreadthBound id)

end IndexBreadthComm

/-! ## `ex:capped-addition`: `ι = m` -/

namespace Capped

variable {m : ℕ}

/-- Adding `1` to itself `i ≤ m` times gives `i`: the powers `1̂^0, …, 1̂^m`
are distinct. -/
theorem gen_pow_val (hm : 1 ≤ m) {i : ℕ} (hi : i ≤ m) : ((gen : Capped m) ^ i).val = i := by
  rw [pow_val]
  have hg : (gen : Capped m).val = 1 := show min 1 m = 1 by omega
  rw [hg]
  omega

/-- **The aperiodicity index of the capped counter is `m`**
(`ex:capped-addition`), for `m ≥ 1`. -/
theorem aperiodicIndex_eq (hm : 1 ≤ m) : aperiodicIndex (Capped m) = m := by
  refine le_antisymm (aperiodicIndex_le hm fun x => (pow_index x).symm) ?_
  by_contra hlt
  push Not at hlt
  have h := congrArg Capped.val (pow_aperiodicIndex (gen : Capped m))
  rw [gen_pow_val hm hlt.le, gen_pow_val hm (by omega)] at h
  omega

end Capped

/-! ## `ex:union`: the union semilattice `(2^{[m]}, ∪)` -/

/-- The union semilattice `(2^{[m]}, ∪)` with identity `∅`, as a type synonym
of `Finset (Fin m)`. -/
def UnionSet (m : ℕ) : Type := Finset (Fin m)

namespace UnionSet

variable {m : ℕ}

instance : DecidableEq (UnionSet m) := inferInstanceAs (DecidableEq (Finset (Fin m)))
instance : Fintype (UnionSet m) := inferInstanceAs (Fintype (Finset (Fin m)))

/-- The underlying set. -/
def toFinset (a : UnionSet m) : Finset (Fin m) := a

/-- A set, as an element of the union monoid. -/
def ofFinset (s : Finset (Fin m)) : UnionSet m := s

@[simp] lemma toFinset_ofFinset (s : Finset (Fin m)) : toFinset (ofFinset s) = s := rfl

lemma ext {a b : UnionSet m} (h : a.toFinset = b.toFinset) : a = b := h

instance : CommMonoid (UnionSet m) where
  mul a b := ofFinset (a.toFinset ∪ b.toFinset)
  one := ofFinset ∅
  mul_assoc a b c := Finset.union_assoc a.toFinset b.toFinset c.toFinset
  one_mul a := Finset.empty_union a.toFinset
  mul_one a := Finset.union_empty a.toFinset
  mul_comm a b := Finset.union_comm a.toFinset b.toFinset

@[simp] lemma toFinset_mul (a b : UnionSet m) :
    (a * b).toFinset = a.toFinset ∪ b.toFinset := rfl

@[simp] lemma toFinset_one : (1 : UnionSet m).toFinset = ∅ := rfl

lemma card_eq : Fintype.card (UnionSet m) = 2 ^ m := by
  change Fintype.card (Finset (Fin m)) = 2 ^ m
  rw [Fintype.card_finset, Fintype.card_fin]

lemma mul_self (a : UnionSet m) : a * a = a := Finset.union_self a.toFinset

instance : IsAperiodicMonoid (UnionSet m) := isAperiodicMonoid_of_idem mul_self

/-- Products are unions. -/
lemma toFinset_prod {α : Type*} [DecidableEq α] (s : Finset α) (f : α → UnionSet m) :
    (∏ j ∈ s, f j).toFinset = s.biUnion fun j => (f j).toFinset := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.biUnion_insert, toFinset_mul, ih]

/-- The word of all singletons. -/
def singletonWord (m : ℕ) : Fin m → UnionSet m := fun i => ofFinset {i}

lemma prod_singletonWord (u : Finset (Fin m)) :
    (∏ i ∈ u, singletonWord m i).toFinset = u := by
  rw [toFinset_prod]
  exact Finset.biUnion_singleton_eq_self

/-- The only core of the word of all singletons is the whole word. -/
lemma card_le_of_isCore_singletonWord {u : Finset (Fin m)}
    (hu : IsCore (id : UnionSet m → UnionSet m) (singletonWord m) u) : m ≤ u.card := by
  rw [isCore_iff] at hu
  have h := congrArg toFinset hu
  simp only [id] at h
  rw [prod_singletonWord, prod_singletonWord] at h
  rw [h, Finset.card_univ, Fintype.card_fin]

/-- **`β(2^{[m]}, ∪) = m = log₂|M|`** (`ex:union`): one occurrence of each
atom preserves the union (the upper bound is the semilattice bound
`breadth_le_log_of_idem`), and the word of all singletons needs all `m`
positions. -/
theorem breadth_id_eq : breadth (id : UnionSet m → UnionSet m) = m := by
  refine le_antisymm ?_ ?_
  · have h := breadth_le_log_of_idem (M := UnionSet m) mul_self id
    rwa [card_eq, Nat.log_pow one_lt_two] at h
  · exact le_breadth_of_forall_core (exists_isBreadthBound id) (singletonWord m)
      fun _ hu => card_le_of_isCore_singletonWord hu

/-- `β = log₂|M|` for the union semilattice. -/
theorem breadth_id_eq_log : breadth (id : UnionSet m → UnionSet m)
    = Nat.log 2 (Fintype.card (UnionSet m)) := by
  rw [breadth_id_eq, card_eq, Nat.log_pow one_lt_two]

/-! ### The `J`-depth -/

lemma mem_twoIdeal_iff {a x : UnionSet m} : x ∈ twoIdeal a ↔ a.toFinset ⊆ x.toFinset := by
  rw [mem_twoIdeal]
  constructor
  · rintro ⟨p, q, rfl⟩
    intro i hi
    simp [hi]
  · intro h
    exact ⟨1, x, ext (by simp [Finset.union_eq_right.mpr h])⟩

lemma twoIdeal_subset_iff {a b : UnionSet m} :
    twoIdeal a ⊆ twoIdeal b ↔ b.toFinset ⊆ a.toFinset := by
  constructor
  · intro h
    exact mem_twoIdeal_iff.mp (h (self_mem_twoIdeal a))
  · intro h x hx
    exact mem_twoIdeal_iff.mpr (h.trans (mem_twoIdeal_iff.mp hx))

lemma twoIdeal_ssubset_iff {a b : UnionSet m} :
    twoIdeal a ⊂ twoIdeal b ↔ b.toFinset ⊂ a.toFinset := by
  rw [Finset.ssubset_iff_subset_ne, Finset.ssubset_iff_subset_ne, twoIdeal_subset_iff]
  refine and_congr_right fun h => not_congr ⟨fun hab => ?_, fun hab => ?_⟩
  · exact Finset.Subset.antisymm h (twoIdeal_subset_iff.mp hab.ge)
  · rw [ext hab]

/-- The `J`-level of a set is its size: the principal ideals above it are
those of its proper subsets. -/
theorem jLevel_eq_card (a : UnionSet m) : jLevel a = a.toFinset.card := by
  induction h : a.toFinset.card using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    rw [jLevel_eq]
    refine le_antisymm (Finset.sup_le fun b hb => ?_) ?_
    · have hlt := Finset.card_lt_card (twoIdeal_ssubset_iff.mp (mem_aboveJ.mp hb))
      rw [ih _ (h ▸ hlt) b rfl]
      omega
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · omega
      · obtain ⟨i, hi⟩ := Finset.card_pos.mp (h ▸ hk)
        let b : UnionSet m := ofFinset (a.toFinset.erase i)
        have hb : b ∈ aboveJ a :=
          mem_aboveJ.mpr (twoIdeal_ssubset_iff.mpr (Finset.erase_ssubset hi))
        have hbc : b.toFinset.card = k - 1 := by
          rw [toFinset_ofFinset, Finset.card_erase_of_mem hi, h]
        have hle := Finset.le_sup (f := fun c : UnionSet m => jLevel c + 1) hb
        rw [ih _ (by omega) b hbc] at hle
        omega

/-- **`D_J(2^{[m]}, ∪) = m`** (remark after `thm:main-ags`). -/
theorem jDepth_eq : jDepth (UnionSet m) = m := by
  refine le_antisymm (Finset.sup_le fun a _ => ?_) ?_
  · rw [jLevel_eq_card]
    simpa using Finset.card_le_univ a.toFinset
  · have h := jLevel_le_jDepth (ofFinset (Finset.univ : Finset (Fin m)))
    rwa [jLevel_eq_card, toFinset_ofFinset, Finset.card_univ, Fintype.card_fin] at h

end UnionSet

/-! ## `ex:max`: the infinite monoid `(ℕ, max)` -/

/-- `(ℕ, max)` with identity `0`, as a type synonym of `ℕ`. -/
def MaxNat : Type := ℕ

namespace MaxNat

/-- The underlying natural number. -/
def val (a : MaxNat) : ℕ := a

/-- A natural number, as an element of `(ℕ, max)`. -/
def mk (n : ℕ) : MaxNat := n

@[simp] lemma val_mk (n : ℕ) : (mk n).val = n := rfl

lemma ext {a b : MaxNat} (h : a.val = b.val) : a = b := h

instance : CommMonoid MaxNat where
  mul a b := mk (max a.val b.val)
  one := mk 0
  mul_assoc a b c := max_assoc a.val b.val c.val
  one_mul a := Nat.zero_max a.val
  mul_one a := Nat.max_zero a.val
  mul_comm a b := max_comm a.val b.val

@[simp] lemma val_mul (a b : MaxNat) : (a * b).val = max a.val b.val := rfl

@[simp] lemma val_one : (1 : MaxNat).val = 0 := rfl

instance : IsAperiodicMonoid MaxNat :=
  ⟨fun a => ⟨1, one_pos, ext (by simp [pow_succ])⟩⟩

/-- Products are maxima. -/
lemma val_prod {α : Type*} [DecidableEq α] (s : Finset α) (f : α → MaxNat) :
    (∏ j ∈ s, f j).val = s.sup fun j => (f j).val := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sup_insert, val_mul, ih]

/-- **Retaining a position attaining the maximum preserves the product**
(`ex:max`): every alphabet over `(ℕ, max)` has breadth bound `1`. -/
theorem isBreadthBound_one {σ : Type} (letter : σ → MaxNat) : IsBreadthBound letter 1 := by
  intro n x
  rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with he | hne
  · exact ⟨Finset.univ, by simp [he], isCore_univ letter x⟩
  · obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => (letter (x j)).val) hne
    refine ⟨{i}, by simp, (isCore_iff letter x _).mpr (ext ?_)⟩
    rw [Finset.prod_singleton, val_prod]
    exact le_antisymm (Finset.le_sup (f := fun j => (letter (x j)).val) (Finset.mem_univ i))
      (Finset.sup_le fun j _ => hi j (Finset.mem_univ j))

/-- **`β = 1`** for any alphabet with a letter other than the identity `0`. -/
theorem breadth_eq_one {σ : Type} {letter : σ → MaxNat} {s : σ} (hs : letter s ≠ 1) :
    breadth letter = 1 := by
  refine le_antisymm (breadth_le (isBreadthBound_one letter)) ?_
  refine le_breadth_of_forall_core ⟨1, isBreadthBound_one letter⟩ (fun _ : Fin 1 => s)
    fun u hu => ?_
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Finset.card_eq_zero] at h0
  subst h0
  rw [isCore_iff, Finset.prod_empty, Fin.prod_univ_one] at hu
  exact hs hu.symm

/-- **`β(ℕ, max) = 1`** (`ex:max`), all elements allowed. -/
theorem breadth_id_eq_one : breadth (id : MaxNat → MaxNat) = 1 :=
  breadth_eq_one (s := mk 1) fun h => by simpa using congrArg val h

end MaxNat

/-! ## Aperiodic iff no nontrivial subgroup -/

section Subgroup

variable {M : Type*} [Monoid M]

/-- `S` is a subgroup of `M` with identity `e`: `e ∈ S`, `S` is closed under
products, `e` is a two-sided identity on `S`, and every element of `S` has an
inverse in `S` relative to `e`.  (The identity `e` need not be `1`.) -/
def IsSubgroupAt (S : Set M) (e : M) : Prop :=
  e ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ (∀ a ∈ S, e * a = a ∧ a * e = a) ∧
    ∀ a ∈ S, ∃ b ∈ S, a * b = e ∧ b * a = e

/-- `M` contains a nontrivial subgroup. -/
def HasNontrivialSubgroup (M : Type*) [Monoid M] : Prop :=
  ∃ (S : Set M) (e : M), IsSubgroupAt S e ∧ ∃ g ∈ S, g ≠ e

/-- **An aperiodic monoid has no nontrivial subgroup** (any monoid). -/
theorem not_hasNontrivialSubgroup_of_aperiodic [IsAperiodicMonoid M] :
    ¬ HasNontrivialSubgroup M := by
  rintro ⟨S, e, ⟨-, hmul, hid, hinv⟩, g, hg, hne⟩
  obtain ⟨N, hN, hNe⟩ := IsAperiodicMonoid.stabilizes g
  have hpow : ∀ n, g ^ (n + 1) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hg
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hg
  obtain ⟨b, -, -, hb⟩ := hinv _ (show g ^ N ∈ S by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hN; simpa using hpow n)
  apply hne
  calc g = e * g := ((hid g hg).1).symm
    _ = b * g ^ N * g := by rw [hb]
    _ = b * g ^ (N + 1) := by rw [mul_assoc, pow_succ]
    _ = e := by rw [← hNe, hb]

/-- **A finite non-aperiodic monoid has a nontrivial subgroup**: past a
multiple `t` of the period of a non-stabilising `a`, the powers `a^{t+s}` form
a cyclic group with identity `a^t`, and `a^{t+1} ≠ a^t`. -/
theorem hasNontrivialSubgroup_of_not_aperiodic [Finite M] (h : ¬ IsAperiodicMonoid M) :
    HasNontrivialSubgroup M := by
  obtain ⟨a, ha⟩ : ∃ a : M, ∀ N, 0 < N → a ^ N ≠ a ^ (N + 1) := by
    by_contra hc
    push Not at hc
    exact h ⟨hc⟩
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite fun n : ℕ => a ^ (n + 1)
  -- a repetition `a^{i₀} = a^{i₀ + p}` with `i₀ ≥ 1`, `p ≥ 1`
  obtain ⟨i₀, p, hi₀, hp, hper⟩ : ∃ i₀ p : ℕ, 1 ≤ i₀ ∧ 1 ≤ p ∧ a ^ (i₀ + p) = a ^ i₀ := by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨i + 1, j - i, by omega, by omega,
        by rw [show i + 1 + (j - i) = j + 1 by omega]; exact heq.symm⟩
    · exact ⟨j + 1, i - j, by omega, by omega,
        by rw [show j + 1 + (i - j) = i + 1 by omega]; exact heq⟩
  set t := i₀ * p with ht
  have hti : i₀ ≤ t := Nat.le_mul_of_pos_right i₀ hp
  -- absorbing an extra `t` past `i₀`
  have habs : ∀ r, i₀ ≤ r → a ^ (r + t) = a ^ r := fun r hr => by
    rw [ht]; exact pow_add_mul_period hper hr i₀
  refine ⟨Set.range fun s : ℕ => a ^ (t + s), a ^ t, ⟨⟨0, by simp⟩, ?_, ?_, ?_⟩,
    a ^ (t + 1), ⟨1, rfl⟩, fun h1 => ha t (by omega) h1.symm⟩
  · rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩
    exact ⟨s + s', by
      rw [← pow_add, show t + s + (t + s') = (t + (s + s')) + t by omega, habs _ (by omega)]⟩
  · rintro _ ⟨s, rfl⟩
    constructor
    · rw [← pow_add, show t + (t + s) = (t + s) + t by omega, habs _ (by omega)]
    · rw [← pow_add, habs _ (by omega)]
  · rintro _ ⟨s, rfl⟩
    have hsp : s ≤ s * p := Nat.le_mul_of_pos_right s hp
    have hcyc : a ^ (t + s + (t + (s * p - s))) = a ^ t := by
      rw [show t + s + (t + (s * p - s)) = (t + s * p) + t by omega, habs _ (by omega),
        pow_add_mul_period hper hti s]
    refine ⟨a ^ (t + (s * p - s)), ⟨s * p - s, rfl⟩, ?_, ?_⟩
    · rw [← pow_add, hcyc]
    · rw [← pow_add, add_comm (t + (s * p - s)), hcyc]

/-- **For a finite monoid, aperiodic ⇔ no nontrivial subgroup**. -/
theorem isAperiodicMonoid_iff_not_hasNontrivialSubgroup [Finite M] :
    IsAperiodicMonoid M ↔ ¬ HasNontrivialSubgroup M :=
  ⟨fun _ => not_hasNontrivialSubgroup_of_aperiodic, fun h => by
    by_contra hna
    exact h (hasNontrivialSubgroup_of_not_aperiodic hna)⟩

end Subgroup

end MonoidProduct
