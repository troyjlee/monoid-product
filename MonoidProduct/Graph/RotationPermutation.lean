import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Set.Card
set_option linter.style.header false

/-!
# Cycle counts under transpositions and erasure

Permutation lemmas for surgery on rotation systems: how the number of cycles of a permutation
changes when a transposition is applied, or when elements are removed from their cycles.

* `cycleCount p`: the number of cycles of `p`, **fixed points included** (Mathlib's
  `cycleFactorsFinset` counts only the nontrivial cycles, so it cannot replace this count).
* `natCard_quotient_eq_add_one_of_join`: an equivalence relation with the classes of `a` and `b`
  joined has one class fewer, if `a` and `b` were in different classes.
* **Splitting and merging**: right multiplication by `swap a b` splits the cycle through `a` and
  `b` into two when they lie in one cycle (`cycleCount_mul_swap_of_sameCycle`), and merges the
  cycles of `a` and `b` into one otherwise (`cycleCount_mul_swap_of_not_sameCycle`).  The cycles
  through the other elements do not change (`sameCycle_or_of_agree`).
* `bypass p a = swap a (p a) * p`: `a` is skipped in its cycle, its predecessor sending to `p a`,
  and becomes a fixed point.  It adds a cycle exactly when `a` was not fixed already.
* `eraseOne p a` and `eraseTwo p a b`: the permutations of the remaining elements, with their
  application formulas, cycles (`sameCycle_eraseOne_iff`, `sameCycle_eraseTwo_iff`) and cycle
  counts (`cycleCount_eraseOne`, `cycleCount_eraseTwo`): erasing an element removes a cycle
  exactly when that element was a fixed point.
* `cycleCount_eq_add_of_sameCycle_iff`: cycles along a map, with the fixed points outside its
  range counted separately; `cycleCount_permCongr`, `sameCycle_permCongr`, `bypass_permCongr`:
  conjugation by an equivalence.
-/

namespace MonoidProduct.Graph

open Equiv Equiv.Perm

variable {α β : Type*}

/-! ## Cycle counts and joined classes -/

/-- **The number of cycles** of `p`: its orbits, fixed points counted as cycles of length one. -/
noncomputable def cycleCount (p : Perm α) : ℕ := Nat.card (Quotient (SameCycle.setoid p))

/-- **Joining two classes**: if `R'` is the equivalence relation `R` with the classes of `a` and
`b` joined, and `a` and `b` are not `R`-related, then `R` has one class more than `R'`. -/
theorem natCard_quotient_eq_add_one_of_join [Finite α] {R R' : Setoid α} {a b : α}
    (h : ∀ x y, R' x y ↔ R x y ∨ ((R x a ∨ R x b) ∧ (R y a ∨ R y b))) (hab : ¬ R a b) :
    Nat.card (Quotient R) = Nat.card (Quotient R') + 1 := by
  classical
  have hle : ∀ x y, R x y → R' x y := fun x y hxy => (h x y).mpr (Or.inl hxy)
  let f : Quotient R → Option (Quotient R') := Quotient.lift
    (fun x => if R x a then none else some (Quotient.mk R' x)) fun x y hxy => by
      have hxy' : R x y := hxy
      by_cases hx : R x a
      · have hy : R y a := R.iseqv.trans (R.iseqv.symm hxy') hx
        simp only [hx, hy, ite_true]
      · have hy : ¬ R y a := fun hy => hx (R.iseqv.trans hxy' hy)
        simp only [hx, hy, ite_false]
        exact congrArg some (Quotient.sound (hle x y hxy'))
  have hf : ∀ x, f (Quotient.mk R x) = if R x a then none else some (Quotient.mk R' x) :=
    fun _ => rfl
  rw [← Finite.card_option]
  refine Nat.card_eq_of_bijective f ⟨fun q q' hqq => ?_, fun o => ?_⟩
  · induction q using Quotient.inductionOn with | h x =>
    induction q' using Quotient.inductionOn with | h y =>
    apply Quotient.sound
    change R x y
    rw [hf, hf] at hqq
    by_cases hx : R x a <;> by_cases hy : R y a <;>
      simp only [hx, hy, ite_true, ite_false, reduceCtorEq] at hqq
    · exact R.iseqv.trans hx (R.iseqv.symm hy)
    · rcases (h x y).mp (Quotient.exact (Option.some.inj hqq)) with hxy | ⟨hx', hy'⟩
      · exact hxy
      · exact R.iseqv.trans (hx'.resolve_left hx) (R.iseqv.symm (hy'.resolve_left hy))
  · rcases o with _ | q
    · exact ⟨Quotient.mk R a, by rw [hf, ite_eq_left (R.iseqv.refl a)]⟩
    · induction q using Quotient.inductionOn with | h y =>
      by_cases hy : R y a
      · refine ⟨Quotient.mk R b, ?_⟩
        rw [hf, ite_eq_right fun h' => hab (R.iseqv.symm h')]
        exact congrArg some (Quotient.sound
          ((h b y).mpr (Or.inr ⟨Or.inr (R.iseqv.refl b), Or.inl hy⟩)))
      · exact ⟨Quotient.mk R y, by rw [hf, ite_eq_right hy]⟩

/-- **Equal relations have equally many classes**: the case where `a` and `b` were already
related. -/
theorem natCard_quotient_eq_of_join {R R' : Setoid α} {a b : α}
    (h : ∀ x y, R' x y ↔ R x y ∨ ((R x a ∨ R x b) ∧ (R y a ∨ R y b))) (hab : R a b) :
    Nat.card (Quotient R) = Nat.card (Quotient R') := by
  have heq : ∀ x y, R x y ↔ R' x y := fun x y => by
    rw [h]
    refine ⟨Or.inl, fun h' => h'.elim id fun ⟨hx, hy⟩ => ?_⟩
    have hxa : R x a := hx.elim id fun hxb => R.iseqv.trans hxb (R.iseqv.symm hab)
    have hya : R y a := hy.elim id fun hyb => R.iseqv.trans hyb (R.iseqv.symm hab)
    exact R.iseqv.trans hxa (R.iseqv.symm hya)
  exact Nat.card_congr (Quotient.congr (Equiv.refl α) heq)

/-! ## Orbits in a finite set -/

section Orbits

/-- Two permutations agreeing along the first `n` steps of the orbit of `x` agree on the `n`th
iterate. -/
theorem pow_apply_eq_of_forall_lt {p q : Perm α} {x : α} {n : ℕ}
    (h : ∀ i < n, q ((p ^ i) x) = p ((p ^ i) x)) : (q ^ n) x = (p ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply, ih fun i hi => h i (by omega), h n (by omega), pow_succ',
      mul_apply]

/-- Iterates are periodic: if `(p ^ m) x = x` then `(p ^ n) x = (p ^ (n % m)) x`. -/
theorem pow_apply_eq_pow_mod_apply (p : Perm α) {x : α} {m : ℕ} (hm : (p ^ m) x = x) (n : ℕ) :
    (p ^ n) x = (p ^ (n % m)) x := by
  have hk : ∀ k, (p ^ (m * k)) x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, mul_apply, hm, ih]
  conv_lhs => rw [← Nat.mod_add_div n m, pow_add, mul_apply, hk]

/-- **The first visit** after time `0` of the orbit of `x` to a set `S` that it visits. -/
theorem exists_first_pow_mem (p : Perm α) {S : Set α} {x : α}
    (h : ∃ n, 0 < n ∧ (p ^ n) x ∈ S) :
    ∃ m, 0 < m ∧ (p ^ m) x ∈ S ∧ ∀ i, 0 < i → i < m → (p ^ i) x ∉ S := by
  classical
  obtain ⟨hm0, hmS⟩ := Nat.find_spec h
  exact ⟨Nat.find h, hm0, hmS, fun i hi him hiS => Nat.find_min h him ⟨hi, hiS⟩⟩

variable [Finite α]

/-- In a finite set every element returns to itself: `(p ^ n) x = x` for some `n > 0`. -/
theorem exists_pos_pow_apply_eq_self (p : Perm α) (x : α) : ∃ n, 0 < n ∧ (p ^ n) x = x := by
  obtain ⟨n, hn, -, h⟩ := (SameCycle.refl p x).exists_pow_eq''
  exact ⟨n, hn, h⟩

/-- **Permutations agreeing off `{a, b}`** have the same cycle through every `x` whose cycle
avoids `a` and `b`. -/
theorem sameCycle_iff_of_agree {p q : Perm α} {a b x : α}
    (hpq : ∀ z, z ≠ a → z ≠ b → q z = p z) (ha : ¬ p.SameCycle x a) (hb : ¬ p.SameCycle x b)
    (y : α) : q.SameCycle x y ↔ p.SameCycle x y := by
  have hpow : ∀ n : ℕ, (q ^ n) x = (p ^ n) x := fun n =>
    pow_apply_eq_of_forall_lt fun i _ => hpq _
      (fun h => ha ⟨i, by rw [zpow_natCast]; exact h⟩)
      (fun h => hb ⟨i, by rw [zpow_natCast]; exact h⟩)
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← hpow]; exact hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, hpow]; exact hn⟩

/-- **The cycles of `p` are unions of cycles of `q`**, up to joining the cycles of `a` and `b`,
when `p` and `q` agree off `{a, b}`: two elements in one cycle of `p` are in one cycle of `q`,
or each of them is in the cycle of `a` or of `b` for `q`. -/
theorem sameCycle_or_of_agree {p q : Perm α} {a b : α}
    (hpq : ∀ z, z ≠ a → z ≠ b → q z = p z) {x y : α} (h : p.SameCycle x y) :
    q.SameCycle x y ∨
      ((q.SameCycle x a ∨ q.SameCycle x b) ∧ (q.SameCycle y a ∨ q.SameCycle y b)) := by
  have hqp : ∀ z, z ≠ a → z ≠ b → p z = q z := fun z ha hb => (hpq z ha hb).symm
  by_cases hx : q.SameCycle x a ∨ q.SameCycle x b
  · by_cases hy : q.SameCycle y a ∨ q.SameCycle y b
    · exact Or.inr ⟨hx, hy⟩
    · push Not at hy
      exact Or.inl ((sameCycle_iff_of_agree hqp hy.1 hy.2 x).mp h.symm).symm
  · push Not at hx
    exact Or.inl ((sameCycle_iff_of_agree hqp hx.1 hx.2 y).mp h)

end Orbits

/-! ## Splitting and merging cycles by a transposition -/

section Swap

variable [DecidableEq α]

/-- `p * swap a b` agrees with `p` off `{a, b}`. -/
theorem mul_swap_apply_of_ne (p : Perm α) {a b z : α} (ha : z ≠ a) (hb : z ≠ b) :
    (p * swap a b) z = p z := by
  rw [mul_apply, swap_apply_of_ne_of_ne ha hb]

/-- `p * swap a b` follows the orbit of `p` from `swap a b u` until it returns to `{a, b}`. -/
theorem pow_mul_swap_apply (p : Perm α) {a b u : α} {m : ℕ}
    (hmin : ∀ i, 0 < i → i < m → (p ^ i) (swap a b u) ∉ ({a, b} : Set α)) :
    ∀ i, 0 < i → i ≤ m → ((p * swap a b) ^ i) u = (p ^ i) (swap a b u) := by
  intro i hi him
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi'
    · simp
    · have hS := hmin i hi' (by omega)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hS
      rw [pow_succ', mul_apply, ih hi' (by omega), mul_swap_apply_of_ne p hS.1 hS.2, pow_succ',
        mul_apply]

variable [Finite α]

/-- **Merging**: if `a` and `b` lie in different cycles of `p`, they lie in one cycle of
`p * swap a b`. -/
theorem sameCycle_mul_swap_of_not_sameCycle {p : Perm α} {a b : α}
    (hab : ¬ p.SameCycle a b) : (p * swap a b).SameCycle a b := by
  -- The orbit of `b` first returns to `{a, b}` at `b`.
  obtain ⟨m, hm0, hmS, hmin⟩ := exists_first_pow_mem p (S := {a, b}) (x := b)
    (let ⟨n, hn, h⟩ := exists_pos_pow_apply_eq_self p b; ⟨n, hn, Or.inr h⟩)
  have hmb : (p ^ m) b = b := by
    rcases hmS with h | h
    · have hba : p.SameCycle b a := ⟨m, by rw [zpow_natCast]; exact h⟩
      exact absurd hba.symm hab
    · exact h
  have key := pow_mul_swap_apply p (u := a) (by rwa [swap_apply_left])
  refine ⟨m, ?_⟩
  rw [zpow_natCast, key m hm0 le_rfl, swap_apply_left, hmb]

/-- **Splitting**: if `a ≠ b` lie in one cycle of `p`, they lie in different cycles of
`p * swap a b`. -/
theorem not_sameCycle_mul_swap_of_sameCycle {p : Perm α} {a b : α} (hne : a ≠ b)
    (hab : p.SameCycle a b) : ¬ (p * swap a b).SameCycle a b := by
  -- The orbit of `a` first returns to `{a, b}` at `b`.
  obtain ⟨m, hm0, hmS, hmin⟩ := exists_first_pow_mem p (S := {a, b}) (x := a)
    (let ⟨n, hn, h⟩ := exists_pos_pow_apply_eq_self p a; ⟨n, hn, Or.inl h⟩)
  have hma : (p ^ m) a = b := by
    rcases hmS with h | h
    · exfalso
      obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
      rw [pow_apply_eq_pow_mod_apply p h n] at hn
      rcases Nat.eq_zero_or_pos (n % m) with h0 | hpos
      · rw [h0, pow_zero, one_apply] at hn
        exact hne hn
      · exact hmin _ hpos (Nat.mod_lt _ hm0) (Or.inr hn)
    · exact h
  -- `p * swap a b` follows the orbit of `a` from `b`, returning to `b` at time `m`.
  have key := pow_mul_swap_apply p (u := b) (by rwa [swap_apply_right])
  have hqm : ((p * swap a b) ^ m) b = b := by rw [key m hm0 le_rfl, swap_apply_right, hma]
  intro h
  obtain ⟨n, hn⟩ := h.symm.exists_nat_pow_eq
  rw [pow_apply_eq_pow_mod_apply _ hqm n] at hn
  rcases Nat.eq_zero_or_pos (n % m) with h0 | hpos
  · rw [h0, pow_zero, one_apply] at hn
    exact hne hn.symm
  · rw [key _ hpos (Nat.mod_lt _ hm0).le, swap_apply_right] at hn
    exact hmin _ hpos (Nat.mod_lt _ hm0) (Or.inl hn)

/-- When `a` and `b` lie in one cycle of `p`, the cycles of `p * swap a b` refine those of `p`. -/
theorem sameCycle_of_mul_swap {p : Perm α} {a b : α} (hab : p.SameCycle a b) {x y : α}
    (h : (p * swap a b).SameCycle x y) : p.SameCycle x y := by
  rcases sameCycle_or_of_agree (fun z ha hb => (mul_swap_apply_of_ne p ha hb).symm) h with
    h | ⟨hx, hy⟩
  · exact h
  · have hxa : p.SameCycle x a := hx.elim id fun h => h.trans hab.symm
    have hya : p.SameCycle y a := hy.elim id fun h => h.trans hab.symm
    exact hxa.trans hya.symm

/-- **The relation of `p` from that of `p * swap a b`** when `a` and `b` lie in one cycle of `p`:
the cycles of `a` and `b` for `p * swap a b` are joined. -/
theorem sameCycle_iff_mul_swap_of_sameCycle {p : Perm α} {a b : α} (hab : p.SameCycle a b)
    (x y : α) :
    p.SameCycle x y ↔ (p * swap a b).SameCycle x y ∨
      (((p * swap a b).SameCycle x a ∨ (p * swap a b).SameCycle x b) ∧
        ((p * swap a b).SameCycle y a ∨ (p * swap a b).SameCycle y b)) := by
  refine ⟨sameCycle_or_of_agree fun z ha hb => mul_swap_apply_of_ne p ha hb, fun h => ?_⟩
  rcases h with h | ⟨hx, hy⟩
  · exact sameCycle_of_mul_swap hab h
  · have hxa : p.SameCycle x a := hx.elim (sameCycle_of_mul_swap hab) fun h =>
      (sameCycle_of_mul_swap hab h).trans hab.symm
    have hya : p.SameCycle y a := hy.elim (sameCycle_of_mul_swap hab) fun h =>
      (sameCycle_of_mul_swap hab h).trans hab.symm
    exact hxa.trans hya.symm

/-- **The relation of `p * swap a b` from that of `p`** when `a` and `b` lie in different cycles
of `p`: the cycles of `a` and `b` are joined. -/
theorem sameCycle_mul_swap_iff_of_not_sameCycle {p : Perm α} {a b : α} (hab : ¬ p.SameCycle a b)
    (x y : α) :
    (p * swap a b).SameCycle x y ↔ p.SameCycle x y ∨
      ((p.SameCycle x a ∨ p.SameCycle x b) ∧ (p.SameCycle y a ∨ p.SameCycle y b)) := by
  have hq := sameCycle_mul_swap_of_not_sameCycle hab
  have hpq : ∀ z, z ≠ a → z ≠ b → (p * swap a b) z = p z := fun z ha hb =>
    mul_swap_apply_of_ne p ha hb
  -- The cycles of `p` refine those of `p * swap a b`.
  have href : ∀ x y, p.SameCycle x y → (p * swap a b).SameCycle x y := fun x y h => by
    rcases sameCycle_or_of_agree hpq h with h | ⟨hx, hy⟩
    · exact h
    · have hxa := hx.elim id fun h => h.trans hq.symm
      have hya := hy.elim id fun h => h.trans hq.symm
      exact hxa.trans hya.symm
  refine ⟨sameCycle_or_of_agree fun z ha hb => (hpq z ha hb).symm, fun h => ?_⟩
  rcases h with h | ⟨hx, hy⟩
  · exact href x y h
  · have hxa : (p * swap a b).SameCycle x a :=
      hx.elim (href x a) fun h => (href x b h).trans hq.symm
    have hya : (p * swap a b).SameCycle y a :=
      hy.elim (href y a) fun h => (href y b h).trans hq.symm
    exact hxa.trans hya.symm

/-- **A transposition inside a cycle splits it**: if `a ≠ b` lie in one cycle of `p`, then
`p * swap a b` has one cycle more. -/
theorem cycleCount_mul_swap_of_sameCycle {p : Perm α} {a b : α} (hne : a ≠ b)
    (hab : p.SameCycle a b) : cycleCount (p * swap a b) = cycleCount p + 1 :=
  natCard_quotient_eq_add_one_of_join (R := SameCycle.setoid (p * swap a b))
    (R' := SameCycle.setoid p) (sameCycle_iff_mul_swap_of_sameCycle hab)
    (not_sameCycle_mul_swap_of_sameCycle hne hab)

/-- **A transposition across two cycles merges them**: if `a` and `b` lie in different cycles of
`p`, then `p * swap a b` has one cycle fewer. -/
theorem cycleCount_mul_swap_of_not_sameCycle {p : Perm α} {a b : α}
    (hab : ¬ p.SameCycle a b) : cycleCount (p * swap a b) + 1 = cycleCount p :=
  (natCard_quotient_eq_add_one_of_join (R := SameCycle.setoid p)
    (R' := SameCycle.setoid (p * swap a b)) (sameCycle_mul_swap_iff_of_not_sameCycle hab)
    hab).symm

end Swap

/-! ## Cycles along a map, and conjugation -/

section Transport

/-- **Cycles along a map**: if `g` carries the cycles of `H` onto cycles of `F`, and `F` fixes
every element outside the range of `g`, then `F` has the cycles of `H` and one more cycle, a
fixed point, for each element outside the range. -/
theorem cycleCount_eq_add_of_sameCycle_iff [Finite α] [Finite β] {F : Perm β} {H : Perm α}
    (g : α → β) (hsc : ∀ x y, F.SameCycle (g x) (g y) ↔ H.SameCycle x y)
    (hfix : ∀ y, y ∉ Set.range g → F y = y) :
    cycleCount F = cycleCount H + (Set.range g)ᶜ.ncard := by
  classical
  let Φ : Quotient (SameCycle.setoid H) ⊕ ↥(Set.range g)ᶜ → Quotient (SameCycle.setoid F) :=
    Sum.elim (Quotient.map g fun x y h => (hsc x y).mpr h) fun y => Quotient.mk _ y.1
  have hΦ : Function.Bijective Φ := by
    refine ⟨?_, fun q => ?_⟩
    · rintro (q | ⟨y, hy⟩) (q' | ⟨y', hy'⟩) hqq
      · induction q using Quotient.inductionOn with | h x =>
        induction q' using Quotient.inductionOn with | h x' =>
        exact congrArg Sum.inl (Quotient.sound ((hsc x x').mp (Quotient.exact hqq)))
      · induction q using Quotient.inductionOn with | h x =>
        exact absurd ⟨x, (Quotient.exact hqq : F.SameCycle (g x) y').eq_of_right (hfix y' hy')⟩
          hy'
      · induction q' using Quotient.inductionOn with | h x' =>
        exact absurd ⟨x', ((Quotient.exact hqq : F.SameCycle y (g x')).eq_of_left
          (hfix y hy)).symm⟩ hy
      · have : y = y' := (Quotient.exact hqq : F.SameCycle y y').eq_of_left (hfix y hy)
        subst this
        rfl
    · induction q using Quotient.inductionOn with | h z =>
      by_cases hz : z ∈ Set.range g
      · obtain ⟨x, rfl⟩ := hz
        exact ⟨Sum.inl (Quotient.mk _ x), rfl⟩
      · exact ⟨Sum.inr ⟨z, hz⟩, rfl⟩
  unfold cycleCount
  rw [← Nat.card_eq_of_bijective Φ hΦ, Nat.card_sum, Nat.card_coe_set_eq]

/-- **Conjugation carries cycles to cycles.** -/
theorem sameCycle_permCongr (e : α ≃ β) (p : Perm α) {x y : α} :
    (e.permCongr p).SameCycle (e x) (e y) ↔ p.SameCycle x y := by
  have hpow : ∀ (i : ℤ) (x : α), ((e.permCongr p) ^ i) (e x) = e ((p ^ i) x) := fun i x => by
    have h := map_zpow e.permCongrHom p i
    change e.permCongr (p ^ i) = e.permCongr p ^ i at h
    rw [← h, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, e.injective (by rw [← hpow, hi])⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hpow, hi]⟩

/-- **Conjugation keeps the number of cycles.** -/
theorem cycleCount_permCongr (e : α ≃ β) (p : Perm α) :
    cycleCount (e.permCongr p) = cycleCount p :=
  (Nat.card_congr (Quotient.congr (ra := SameCycle.setoid p)
    (rb := SameCycle.setoid (e.permCongr p)) e fun _ _ =>
      (sameCycle_permCongr e p).symm)).symm

end Transport

/-! ## Bypassing and erasing elements -/

section Erase

variable [DecidableEq α]

/-- **Bypassing `a`**: the permutation that skips `a` in its cycle, sending the predecessor of `a`
to `p a`, and fixes `a`. -/
def bypass (p : Perm α) (a : α) : Perm α := swap a (p a) * p

@[simp] theorem bypass_apply_self (p : Perm α) (a : α) : bypass p a a = a := by
  rw [bypass, mul_apply, swap_apply_right]

/-- **The application formula**: the successor of `d ≠ a` is `p d`, unless that is `a`, in which
case it is `p a`. -/
theorem bypass_apply_of_ne (p : Perm α) {a d : α} (hd : d ≠ a) :
    bypass p a d = if p d = a then p a else p d := by
  rw [bypass, mul_apply]
  split_ifs with h
  · rw [h, swap_apply_left]
  · exact swap_apply_of_ne_of_ne h fun h' => hd (p.injective h')

/-- Bypassing a fixed point changes nothing. -/
theorem bypass_of_apply_eq (p : Perm α) {a : α} (ha : p a = a) : bypass p a = p := by
  rw [bypass, ha, swap_self]
  rfl

/-- Bypassing `a` is a transposition after `p`, of `a` and its predecessor. -/
theorem bypass_eq_mul_swap (p : Perm α) (a : α) : bypass p a = p * swap (p⁻¹ a) a := by
  rw [bypass, swap_mul_eq_mul_swap, Perm.inv_def p, Equiv.symm_apply_apply]

/-- Bypassing keeps any function that `p` keeps, such as the tail of a dart. -/
theorem apply_bypass_eq {γ : Type*} {g : α → γ} {p : Perm α} (hg : ∀ x, g (p x) = g x)
    (a x : α) : g (bypass p a x) = g x := by
  rw [bypass, mul_apply, apply_swap_eq_self ((hg a).symm), hg]

omit [DecidableEq α] in
/-- `a` and its predecessor lie in one cycle, and differ unless `a` is fixed. -/
private theorem inv_apply_ne_and_sameCycle (p : Perm α) {a : α} (ha : p a ≠ a) :
    p⁻¹ a ≠ a ∧ p.SameCycle (p⁻¹ a) a := by
  refine ⟨fun h => ha ?_, ⟨1, by rw [zpow_one, Perm.inv_def, Equiv.apply_symm_apply]⟩⟩
  have := congrArg p h
  rwa [Perm.inv_def, Equiv.apply_symm_apply, eq_comm] at this

variable [Finite α]

/-- **Bypassing keeps the cycles of the other elements.** -/
theorem sameCycle_bypass_iff (p : Perm α) {a d d' : α} (hd : d ≠ a) (hd' : d' ≠ a) :
    (bypass p a).SameCycle d d' ↔ p.SameCycle d d' := by
  by_cases ha : p a = a
  · rw [bypass_of_apply_eq p ha]
  obtain ⟨hne, hsc⟩ := inv_apply_ne_and_sameCycle p ha
  have hqa : Function.IsFixedPt (bypass p a) a := bypass_apply_self p a
  rw [bypass_eq_mul_swap] at hqa ⊢
  rw [sameCycle_iff_mul_swap_of_sameCycle hsc]
  refine ⟨Or.inl, fun h => h.elim id fun ⟨hx, hy⟩ => ?_⟩
  have hx' := hx.resolve_right fun h => hd (h.eq_of_right hqa)
  have hy' := hy.resolve_right fun h => hd' (h.eq_of_right hqa)
  exact hx'.trans hy'.symm

/-- **Bypassing adds a cycle exactly when `a` was not fixed**: `a` becomes a fixed point. -/
theorem cycleCount_bypass (p : Perm α) (a : α) :
    cycleCount (bypass p a) = cycleCount p + if p a = a then 0 else 1 := by
  by_cases ha : p a = a
  · rw [bypass_of_apply_eq p ha, ite_eq_left ha, add_zero]
  · obtain ⟨hne, hsc⟩ := inv_apply_ne_and_sameCycle p ha
    rw [ite_eq_right ha, bypass_eq_mul_swap, cycleCount_mul_swap_of_sameCycle hne hsc]

end Erase

section EraseSub

variable [DecidableEq α]

/-- `bypass p a` fixes `a`, so it keeps the other elements among themselves. -/
theorem bypass_apply_ne_iff (p : Perm α) (a d : α) : bypass p a d ≠ a ↔ d ≠ a :=
  not_congr ⟨fun h => (bypass p a).injective (h.trans (bypass_apply_self p a).symm),
    fun h => h ▸ bypass_apply_self p a⟩

/-- **Erasing `a`**: the permutation of the other elements that skips `a` in its cycle. -/
def eraseOne (p : Perm α) (a : α) : Perm {d // d ≠ a} :=
  (bypass p a).subtypePerm fun d => bypass_apply_ne_iff p a d

/-- **The application formula** for erasing `a`: the successor is `p d`, unless that is `a`, in
which case it is the next surviving element `p a`. -/
theorem eraseOne_apply (p : Perm α) (a : α) (d : {d // d ≠ a}) :
    (eraseOne p a d : α) = if p d = a then p a else p d :=
  bypass_apply_of_ne p d.2

variable [Finite α]

/-- **Erasing `a` keeps the cycles of the survivors.**  A cycle disappears only when it has no
surviving element, that is, when it is the fixed point `a`. -/
theorem sameCycle_eraseOne_iff (p : Perm α) (a : α) {d d' : {d // d ≠ a}} :
    (eraseOne p a).SameCycle d d' ↔ p.SameCycle d d' := by
  rw [eraseOne, sameCycle_subtypePerm]
  exact sameCycle_bypass_iff p d.2 d'.2

omit [DecidableEq α] in
/-- **Removing fixed points**: a permutation fixing every element outside `{d | P d}` has, besides
the cycles of its restriction, one cycle for each element outside. -/
theorem cycleCount_subtypePerm_add {P : α → Prop} (q : Perm α) (h : ∀ d, P (q d) ↔ P d)
    (hfix : ∀ d, ¬ P d → q d = d) :
    cycleCount (q.subtypePerm h) + {d | ¬ P d}.ncard = cycleCount q := by
  rw [cycleCount_eq_add_of_sameCycle_iff (H := q.subtypePerm h) Subtype.val
    (fun x y => sameCycle_subtypePerm.symm) fun y hy => hfix y fun hP => hy ⟨⟨y, hP⟩, rfl⟩,
    Subtype.range_coe_subtype]
  rfl

/-- **Erasing `a` removes a cycle exactly when `a` was a fixed point**, and otherwise keeps the
number of cycles. -/
theorem cycleCount_eraseOne (p : Perm α) (a : α) :
    cycleCount (eraseOne p a) + (if p a = a then 1 else 0) = cycleCount p := by
  have h := cycleCount_subtypePerm_add (P := (· ≠ a)) (bypass p a)
    (fun d => bypass_apply_ne_iff p a d) fun d hd => by
      rw [not_not] at hd
      rw [hd, bypass_apply_self]
  have hset : {d : α | ¬ d ≠ a} = {a} := by ext; simp
  rw [hset, Set.ncard_singleton, cycleCount_bypass] at h
  change cycleCount (eraseOne p a) + 1 = cycleCount p + _ at h
  split_ifs at h ⊢ <;> omega

end EraseSub

section EraseTwo

variable [DecidableEq α]

/-- Bypassing `a` and then `b` fixes both. -/
theorem bypass_bypass_apply_left (p : Perm α) (a b : α) : bypass (bypass p a) b a = a := by
  by_cases hab : a = b
  · rw [hab, bypass_apply_self]
  · rw [bypass_apply_of_ne _ hab, bypass_apply_self, ite_eq_right hab]

theorem bypass_bypass_apply_ne_iff (p : Perm α) (a b d : α) :
    (bypass (bypass p a) b d ≠ a ∧ bypass (bypass p a) b d ≠ b) ↔ (d ≠ a ∧ d ≠ b) := by
  have hinj := (bypass (bypass p a) b).injective
  refine and_congr (not_congr ⟨fun h => hinj (h.trans (bypass_bypass_apply_left p a b).symm),
    fun h => h ▸ bypass_bypass_apply_left p a b⟩) (bypass_apply_ne_iff _ b d)

/-- **Erasing two elements** `a` and `b` at once: the permutation of the others that skips both,
that is, `eraseOne` applied for `a` and then for `b`, on the elements other than `a` and `b`. -/
def eraseTwo (p : Perm α) (a b : α) : Perm {d // d ≠ a ∧ d ≠ b} :=
  (bypass (bypass p a) b).subtypePerm fun d => bypass_bypass_apply_ne_iff p a b d

/-- **The application formula** for erasing `a` and `b`: bypass `a`, then `b`. -/
theorem eraseTwo_apply (p : Perm α) (a b : α) (d : {d // d ≠ a ∧ d ≠ b}) :
    (eraseTwo p a b d : α) = bypass (bypass p a) b d := rfl

/-- **Erasing two elements is erasing one twice**: erasing `a`, and then `b` from the result, acts
on every survivor as `eraseTwo`. -/
theorem eraseOne_eraseOne_apply (p : Perm α) {a b : α} (hb : b ≠ a)
    (d : {d // d ≠ a ∧ d ≠ b}) :
    ((eraseOne (eraseOne p a) ⟨b, hb⟩ ⟨⟨d.1, d.2.1⟩, fun h => d.2.2 (congrArg Subtype.val h)⟩ :
      {d // d ≠ a}) : α) = eraseTwo p a b d := by
  change (swap (⟨b, hb⟩ : {d // d ≠ a}) (eraseOne p a ⟨b, hb⟩) (eraseOne p a ⟨d.1, d.2.1⟩) :
    {d // d ≠ a}).1 = swap b (bypass p a b) (bypass p a d.1)
  rw [Subtype.val_injective.map_swap]
  rfl

variable [Finite α]

/-- **Erasing `a` and `b` keeps the cycles of the survivors.** -/
theorem sameCycle_eraseTwo_iff (p : Perm α) (a b : α) {d d' : {d // d ≠ a ∧ d ≠ b}} :
    (eraseTwo p a b).SameCycle d d' ↔ p.SameCycle d d' := by
  rw [eraseTwo, sameCycle_subtypePerm, sameCycle_bypass_iff _ d.2.2 d'.2.2,
    sameCycle_bypass_iff _ d.2.1 d'.2.1]

/-- **Erasing two distinct elements** removes the two fixed points `a` and `b` of the double
bypass. -/
theorem cycleCount_eraseTwo (p : Perm α) {a b : α} (hab : a ≠ b) :
    cycleCount (eraseTwo p a b) + 2 = cycleCount (bypass (bypass p a) b) := by
  have h := cycleCount_subtypePerm_add (P := fun d => d ≠ a ∧ d ≠ b) (bypass (bypass p a) b)
    (fun d => bypass_bypass_apply_ne_iff p a b d) fun d hd => by
      rcases not_and_or.mp hd with hd | hd <;> rw [not_not] at hd <;> subst hd
      · exact bypass_bypass_apply_left p _ b
      · exact bypass_apply_self _ _
  have hset : {d : α | ¬ (d ≠ a ∧ d ≠ b)} = {a, b} := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset, Set.ncard_pair hab] at h
  exact h

/-- **The cycle count after erasing two distinct elements**: a cycle is lost for each erased
element that was fixed when it was erased. -/
theorem cycleCount_eraseTwo_add (p : Perm α) {a b : α} (hab : a ≠ b) :
    cycleCount (eraseTwo p a b) + (if p a = a then 1 else 0) +
      (if bypass p a b = b then 1 else 0) = cycleCount p := by
  have h := cycleCount_eraseTwo p hab
  rw [cycleCount_bypass, cycleCount_bypass] at h
  split_ifs at h ⊢ <;> omega

end EraseTwo

section Conj

variable [DecidableEq α] [DecidableEq β]

/-- **Bypassing commutes with conjugation.** -/
theorem bypass_permCongr (e : α ≃ β) (p : Perm α) (a : α) :
    e.permCongr (bypass p a) = bypass (e.permCongr p) (e a) := by
  ext x
  simp only [bypass, Equiv.permCongr_apply, mul_apply, Equiv.symm_apply_apply,
    e.injective.map_swap]

/-- **Erasing commutes with conjugation**: conjugating the erasure of `a` by `e`, restricted to
the other elements, gives the erasure of `e a` from the conjugate. -/
theorem eraseOne_permCongr (e : α ≃ β) (p : Perm α) (a : α) :
    (e.subtypeEquiv (p := (· ≠ a)) (q := (· ≠ e a)) fun _ => e.injective.ne_iff.symm).permCongr
      (eraseOne p a) =
      eraseOne (e.permCongr p) (e a) := by
  ext x
  change e (bypass p a (e.symm x)) = bypass (e.permCongr p) (e a) x
  rw [← bypass_permCongr, Equiv.permCongr_apply]

end Conj

end MonoidProduct.Graph
