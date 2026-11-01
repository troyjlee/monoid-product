import MonoidProduct.Dyck.ExactCount
import QuantumQueryComplexity.Quantum.Plurality
set_option linter.style.header false

/-!
# The enumeration adversary

`monoid.tex`, proof of `prop:failure-profile-complexity`, `eq:profile-enumeration-lower`:
identifying `r` independent `d`-element subsets of a `q`-element set from their membership bits
needs `Ω(r·√(d(q − d)))` queries, for `1 ≤ d < q`.

The inputs are the tuples `x : JTuple r q d` of `d`-element subsets `x u ⊆ Fin q`.  The adversary
matrix `johnsonΓ` joins two inputs when exactly one row changes by exchanging one present and one
absent element (`Exch`): the Cartesian sum of `r` Johnson exchange graphs.

* **The numerator.**  Every input has at least `r·d(q − d)` neighbours (`card_exch_ge`), so the
  all-ones vector gives `‖Γ‖ ≥ r·d(q − d)` (`johnsonΓ_norm_ge`).  The full Johnson spectrum is
  not needed.
* **The masks.**  Filtering by the membership bit of `b` in row `u` keeps the exchanges that move
  `b`.  An input with `b ∈ x u` keeps at most `q − d` neighbours, one with `b ∉ x u` at most `d`
  (`card_maskedExch_le_of_mem`, `card_maskedExch_le_of_notMem`); the neighbours lie on the other
  side.  The weighted Schur test (`l2_opNorm_le_of_weighted`) with weights `√(q − d)` and `√d`
  bounds the masked norm by `√(d(q − d))` (`johnsonΓ_hadamard_le`).
* **The bound.**  `enumeration_advPMOn_ge`: `r·√(d(q − d)) ≤ advPMOn` for any read map whose
  positions are constant or reveal one membership bit, and any output that separates exchanged
  inputs.  At error `1/3` the general-output bound of QuantumQueryComplexity
  (`mul_advPMOn_le_qQueryOn_third_finiteOutput`, through `43`-fold amplification of the error-`1/16`
  adversary theorem) gives `enumeration_qQuery_ge`:
  `Q_{1/3} ≥ (7/1376)·r·√(d(q − d))`.  No output-size logarithm enters.
* `one_le_advPMOn_of_ne`: any two inputs with different outputs give `1 ≤ advPMOn`.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Matrix
open scoped Matrix Matrix.Norms.L2Operator

/-! ## A weighted Schur test -/

section Schur

/-- `2|a||b| ≤ a²·(p'/p) + b²·(p/p')` for positive weights. -/
theorem two_mul_abs_mul_le_weighted {a b p p' : ℝ} (hp : 0 < p) (hp' : 0 < p') :
    2 * (|a| * |b|) ≤ a * a * (p' / p) + b * b * (p / p') := by
  have hpp : 0 < p * p' := mul_pos hp hp'
  rw [show a * a * (p' / p) + b * b * (p / p') = (a * a * (p' * p') + b * b * (p * p)) / (p * p')
    by field_simp, le_div_iff₀ hpp]
  nlinarith [sq_nonneg (|a| * p' - |b| * p), abs_mul_abs_self a, abs_mul_abs_self b,
    abs_nonneg a, abs_nonneg b]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The weighted Schur test**: if positive weights `p` satisfy `∑_y |A x y| p y ≤ c·p x` and
`∑_x |A x y| p x ≤ c·p y`, then `‖A‖ ≤ c`. -/
theorem l2_opNorm_le_of_weighted {A : Matrix n n ℝ} {p : n → ℝ} (hp : ∀ x, 0 < p x) {c : ℝ}
    (hc : 0 ≤ c) (hrow : ∀ x, ∑ y, |A x y| * p y ≤ c * p x)
    (hcol : ∀ y, ∑ x, |A x y| * p x ≤ c * p y) : ‖A‖ ≤ c := by
  refine l2_opNorm_le_of_quadratic hc fun u v => ?_
  rw [dotProduct_mulVec_eq_sum]
  have hterm : ∀ x y, |u x * A x y * v y| ≤
      (u x * u x / p x) * (|A x y| * p y) / 2 + (v y * v y / p y) * (|A x y| * p x) / 2 := by
    intro x y
    have h := two_mul_abs_mul_le_weighted (a := u x) (b := v y) (hp x) (hp y)
    rw [abs_mul, abs_mul]
    have hA := abs_nonneg (A x y)
    have e : (u x * u x / p x) * (|A x y| * p y) / 2 + (v y * v y / p y) * (|A x y| * p x) / 2
        = |A x y| * (u x * u x * (p y / p x) + v y * v y * (p x / p y)) / 2 := by ring
    rw [e]
    nlinarith
  have hU : ∑ x, ∑ y, (u x * u x / p x) * (|A x y| * p y) ≤ c * (u ⬝ᵥ u) := by
    calc ∑ x, ∑ y, (u x * u x / p x) * (|A x y| * p y)
        = ∑ x, (u x * u x / p x) * ∑ y, |A x y| * p y := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ x, (u x * u x / p x) * (c * p x) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hrow x)
            (div_nonneg (mul_self_nonneg _) (hp x).le)
      _ = c * (u ⬝ᵥ u) := by
          rw [dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          field_simp [(hp x).ne']
  have hV : ∑ x, ∑ y, (v y * v y / p y) * (|A x y| * p x) ≤ c * (v ⬝ᵥ v) := by
    calc ∑ x, ∑ y, (v y * v y / p y) * (|A x y| * p x)
        = ∑ y, (v y * v y / p y) * ∑ x, |A x y| * p x := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ ≤ ∑ y, (v y * v y / p y) * (c * p y) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hcol y)
            (div_nonneg (mul_self_nonneg _) (hp y).le)
      _ = c * (v ⬝ᵥ v) := by
          rw [dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          field_simp [(hp y).ne']
  calc |∑ x, ∑ y, u x * A x y * v y|
      ≤ ∑ x, ∑ y, |u x * A x y * v y| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x, ∑ y, ((u x * u x / p x) * (|A x y| * p y) / 2 +
          (v y * v y / p y) * (|A x y| * p x) / 2) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = (∑ x, ∑ y, (u x * u x / p x) * (|A x y| * p y)) / 2 +
          (∑ x, ∑ y, (v y * v y / p y) * (|A x y| * p x)) / 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ c * (u ⬝ᵥ u) / 2 + c * (v ⬝ᵥ v) / 2 := by linarith
    _ = c / 2 * ((u ⬝ᵥ u) + (v ⬝ᵥ v)) := by ring

end Schur

/-! ## Tuples of subsets and exchanges -/

/-- The `d`-element subsets of `Fin q`. -/
abbrev JSet (q d : ℕ) : Type := {S : Finset (Fin q) // S.card = d}

/-- The inputs of the enumeration problem: `r`-tuples of `d`-element subsets of `Fin q`. -/
abbrev JTuple (r q d : ℕ) : Type := Fin r → JSet q d

variable {r q d : ℕ}

/-- There is a `d`-element subset of `Fin q` when `d ≤ q`. -/
theorem nonempty_jTuple (hdq : d ≤ q) : Nonempty (JTuple r q d) := by
  have hcard : d ≤ (Finset.univ : Finset (Fin q)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hdq
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨fun _ => ⟨S, hS⟩⟩

/-- **One exchange**: `y` is `x` with one element `a` of one row `x u` replaced by an element `c`
outside it. -/
def Exch (x y : JTuple r q d) : Prop :=
  ∃ u, (∀ u', u' ≠ u → y u' = x u') ∧
    ∃ a ∈ (x u).1, ∃ c ∉ (x u).1, (y u).1 = insert c ((x u).1.erase a)

instance : DecidableRel (Exch (r := r) (q := q) (d := d)) := fun x y => by
  unfold Exch
  infer_instance

theorem card_insert_erase {S : Finset (Fin q)} {a c : Fin q} (ha : a ∈ S) (hc : c ∉ S) :
    (insert c (S.erase a)).card = S.card := by
  rw [Finset.card_insert_of_notMem (fun h => hc (Finset.mem_of_mem_erase h)),
    Finset.card_erase_of_mem ha]
  have : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
  omega

/-- The exchange of `a` for `c` in row `u` (the identity unless `a ∈ x u` and `c ∉ x u`). -/
def exch (x : JTuple r q d) (u : Fin r) (a c : Fin q) : JTuple r q d :=
  if h : a ∈ (x u).1 ∧ c ∉ (x u).1 then
    Function.update x u ⟨insert c ((x u).1.erase a), by rw [card_insert_erase h.1 h.2, (x u).2]⟩
  else x

theorem exch_self {x : JTuple r q d} {u : Fin r} {a c : Fin q} (ha : a ∈ (x u).1)
    (hc : c ∉ (x u).1) : (exch x u a c u).1 = insert c ((x u).1.erase a) := by
  simp [exch, ha, hc]

theorem exch_ne {x : JTuple r q d} {u u' : Fin r} {a c : Fin q} (hu : u' ≠ u) :
    exch x u a c u' = x u' := by
  unfold exch
  split_ifs
  · exact Function.update_of_ne hu _ _
  · rfl

theorem exch_exch {x : JTuple r q d} {u : Fin r} {a c : Fin q} (ha : a ∈ (x u).1)
    (hc : c ∉ (x u).1) : Exch x (exch x u a c) :=
  ⟨u, fun _ hu => exch_ne hu, a, ha, c, hc, exch_self ha hc⟩

/-- An exchange `x → y` in row `u` with `y u = insert c (x u \ {a})` is `exch x u a c`. -/
theorem eq_exch {x y : JTuple r q d} {u : Fin r} {a c : Fin q} (ha : a ∈ (x u).1)
    (hc : c ∉ (x u).1) (hoff : ∀ u', u' ≠ u → y u' = x u')
    (hy : (y u).1 = insert c ((x u).1.erase a)) : y = exch x u a c := by
  funext u'
  by_cases hu : u' = u
  · subst hu
    exact Subtype.ext (hy.trans (exch_self ha hc).symm)
  · rw [hoff u' hu, exch_ne hu]

theorem Exch.symm {x y : JTuple r q d} (h : Exch x y) : Exch y x := by
  obtain ⟨u, hoff, a, ha, c, hc, hy⟩ := h
  have hca : c ≠ a := fun h => hc (h ▸ ha)
  refine ⟨u, fun u' hu' => (hoff u' hu').symm, c, ?_, a, ?_, ?_⟩
  · rw [hy]
    exact Finset.mem_insert_self c _
  · rw [hy, Finset.mem_insert, Finset.mem_erase]
    rintro (h | ⟨h, -⟩)
    · exact hca h.symm
    · exact h rfl
  · rw [hy, Finset.erase_insert (fun h => hc (Finset.mem_of_mem_erase h)), Finset.insert_erase ha]

theorem Exch.ne {x y : JTuple r q d} (h : Exch x y) : x ≠ y := by
  rintro rfl
  obtain ⟨u, -, a, ha, c, hc, hy⟩ := h
  exact hc (hy ▸ Finset.mem_insert_self c _)

/-- **Every input has at least `r·d(q − d)` exchange neighbours**: the exchanges
`(u, a, c)`, `a ∈ x u`, `c ∉ x u`, give distinct neighbours. -/
theorem card_exch_ge (x : JTuple r q d) :
    r * (d * (q - d)) ≤ (Finset.univ.filter fun y => Exch x y).card := by
  classical
  let T : Finset (Σ _ : Fin r, Fin q × Fin q) :=
    Finset.univ.sigma fun u => (x u).1 ×ˢ (x u).1ᶜ
  have hT : T.card = r * (d * (q - d)) := by
    simp [T, Finset.card_sigma, Finset.card_product, Finset.card_compl, (x _).2]
  rw [← hT]
  refine Finset.card_le_card_of_injOn
    (fun t : Σ _ : Fin r, Fin q × Fin q => exch x t.1 t.2.1 t.2.2) ?_ ?_
  · rintro ⟨u, a, c⟩ ht
    simp only [T, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ, true_and,
      Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact exch_exch ht.1 ht.2
  · rintro ⟨u, a, c⟩ ht ⟨u', a', c'⟩ ht' heq
    simp only [T, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ, true_and,
      Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at ht ht'
    simp only at heq
    have hu : u = u' := by
      by_contra hne
      have h1 := congrArg (fun y => (y u).1) heq
      simp only [exch_self ht.1 ht.2, exch_ne hne] at h1
      exact ht.2 (h1 ▸ Finset.mem_insert_self c _)
    subst hu
    have h1 := congrArg (fun y => (y u).1) heq
    simp only [exch_self ht.1 ht.2, exch_self ht'.1 ht'.2] at h1
    have hc : c = c' := by
      have hmem : c ∈ insert c' ((x u).1.erase a') := h1 ▸ Finset.mem_insert_self c _
      rcases Finset.mem_insert.mp hmem with h | h
      · exact h
      · exact absurd (Finset.mem_of_mem_erase h) ht.2
    subst hc
    have h2 : (x u).1.erase a = (x u).1.erase a' := by
      have := congrArg (fun S => S.erase c) h1
      simp only [Finset.erase_insert (fun h => ht.2 (Finset.mem_of_mem_erase h))] at this
      exact this
    have ha : a = a' := by
      by_contra hne
      have : a ∈ (x u).1.erase a' := Finset.mem_erase.mpr ⟨hne, ht.1⟩
      rw [← h2] at this
      exact Finset.notMem_erase a _ this
    subst ha
    rfl

/-- The exchanges that move `b` in row `u`, from an input with `b ∈ x u`, are the exchanges of
`b` for an absent element: at most `q − d` of them. -/
theorem card_maskedExch_le_of_mem (x : JTuple r q d) {u : Fin r} {b : Fin q}
    (hb : b ∈ (x u).1) :
    (Finset.univ.filter fun y => Exch x y ∧ (b ∈ (x u).1 ↔ b ∉ (y u).1)).card ≤ q - d := by
  classical
  refine (Finset.card_le_card (t := (x u).1ᶜ.image fun c => exch x u b c) ?_).trans
    (Finset.card_image_le.trans ?_)
  · intro y hy
    obtain ⟨⟨u', hoff, a, ha, c, hc, hyu⟩, hmask⟩ := (Finset.mem_filter.mp hy).2
    have hby : b ∉ (y u).1 := hmask.mp hb
    have hu : u' = u := by
      by_contra hne
      exact hby (by rw [hoff u (Ne.symm hne)]; exact hb)
    subst hu
    have hba : b = a := by
      by_contra hne
      exact hby (by rw [hyu]; exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hb⟩))
    subst hba
    exact Finset.mem_image.mpr ⟨c, Finset.mem_compl.mpr hc, (eq_exch ha hc hoff hyu).symm⟩
  · rw [Finset.card_compl, Fintype.card_fin, (x u).2]

/-- The exchanges that move `b` in row `u`, from an input with `b ∉ x u`, are the exchanges of a
present element for `b`: at most `d` of them. -/
theorem card_maskedExch_le_of_notMem (x : JTuple r q d) {u : Fin r} {b : Fin q}
    (hb : b ∉ (x u).1) :
    (Finset.univ.filter fun y => Exch x y ∧ (b ∈ (x u).1 ↔ b ∉ (y u).1)).card ≤ d := by
  classical
  refine (Finset.card_le_card (t := (x u).1.image fun a => exch x u a b) ?_).trans
    (Finset.card_image_le.trans (le_of_eq (x u).2))
  intro y hy
  obtain ⟨⟨u', hoff, a, ha, c, hc, hyu⟩, hmask⟩ := (Finset.mem_filter.mp hy).2
  have hby : b ∈ (y u).1 := by
    by_contra h
    exact hb (hmask.mpr h)
  have hu : u' = u := by
    by_contra hne
    exact hb (by rw [← hoff u (Ne.symm hne)]; exact hby)
  subst hu
  have hbc : b = c := by
    rw [hyu, Finset.mem_insert, Finset.mem_erase] at hby
    rcases hby with h | ⟨-, h⟩
    · exact h
    · exact absurd h hb
  subst hbc
  exact Finset.mem_image.mpr ⟨a, ha, (eq_exch ha hc hoff hyu).symm⟩

/-! ## The adversary matrix -/

/-- **The Johnson-sum adversary matrix**: `1` on the pairs related by one exchange. -/
def johnsonΓ (r q d : ℕ) : Matrix (JTuple r q d) (JTuple r q d) ℝ :=
  Matrix.of fun x y => if Exch x y then 1 else 0

theorem johnsonΓ_apply (x y : JTuple r q d) :
    johnsonΓ r q d x y = if Exch x y then 1 else 0 :=
  rfl

theorem johnsonΓ_symm (x y : JTuple r q d) : johnsonΓ r q d x y = johnsonΓ r q d y x := by
  rw [johnsonΓ_apply, johnsonΓ_apply]
  exact if_congr ⟨Exch.symm, Exch.symm⟩ rfl rfl

theorem johnsonΓ_isHermitian : (johnsonΓ r q d).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact johnsonΓ_symm y x

/-- **The numerator**: `‖Γ‖ ≥ r·d(q − d)`, from the all-ones vector. -/
theorem johnsonΓ_norm_ge (hdq : d ≤ q) :
    (r : ℝ) * (d * (q - d : ℕ)) ≤ ‖johnsonΓ r q d‖ := by
  classical
  have : Nonempty (JTuple r q d) := nonempty_jTuple hdq
  have hX : (0 : ℝ) < Fintype.card (JTuple r q d) := by exact_mod_cast Fintype.card_pos
  have h := abs_dotProduct_mulVec_le (johnsonΓ r q d) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
  have h1 : (fun _ : JTuple r q d => (1 : ℝ)) ⬝ᵥ (fun _ => 1) = Fintype.card (JTuple r q d) := by
    simp [dotProduct]
  have hrow : ∀ x : JTuple r q d, ((r * (d * (q - d)) : ℕ) : ℝ) ≤ ∑ y, johnsonΓ r q d x y := by
    intro x
    simp only [johnsonΓ_apply]
    rw [Finset.sum_boole]
    exact_mod_cast card_exch_ge x
  have hsum : (Fintype.card (JTuple r q d) : ℝ) * ((r * (d * (q - d)) : ℕ) : ℝ) ≤
      (fun _ : JTuple r q d => (1 : ℝ)) ⬝ᵥ johnsonΓ r q d *ᵥ (fun _ => 1) := by
    rw [dotProduct_mulVec_eq_sum]
    simp only [one_mul, mul_one]
    calc (Fintype.card (JTuple r q d) : ℝ) * ((r * (d * (q - d)) : ℕ) : ℝ)
        = ∑ _x : JTuple r q d, ((r * (d * (q - d)) : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ x, ∑ y, johnsonΓ r q d x y := Finset.sum_le_sum fun x _ => hrow x
  rw [h1, mul_assoc, Real.mul_self_sqrt hX.le] at h
  have hle := hsum.trans (le_abs_self _) |>.trans h
  have hcast : ((r * (d * (q - d)) : ℕ) : ℝ) = (r : ℝ) * (d * (q - d : ℕ)) := by push_cast; ring
  rw [hcast, mul_comm ‖johnsonΓ r q d‖] at hle
  exact le_of_mul_le_mul_left hle hX

/-- **The masks**: if position `i` can only separate inputs that differ in the membership of `b`
in row `u`, the masked matrix has norm at most `√(d(q − d))`. -/
theorem johnsonΓ_hadamard_le {ι σ : Type*} [Finite ι] [DecidableEq σ]
    (hd : 0 < d) (hdq : d < q) (read : JTuple r q d → ι → σ) (i : ι) {u : Fin r} {b : Fin q}
    (hi : ∀ x y, read x i ≠ read y i → (b ∈ (x u).1 ↔ b ∉ (y u).1)) :
    ‖johnsonΓ r q d ⊙ advDOn read i‖ ≤ Real.sqrt (d * (q - d : ℕ)) := by
  classical
  have := Fintype.ofFinite ι
  set M := johnsonΓ r q d ⊙ advDOn read i with hM
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hqd : (0 : ℝ) < ((q - d : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hdq
  set p : JTuple r q d → ℝ := fun x =>
    if b ∈ (x u).1 then Real.sqrt ((q - d : ℕ) : ℝ) else Real.sqrt d with hp
  have hppos : ∀ x, 0 < p x := fun x => by
    simp only [hp]
    split_ifs
    · exact Real.sqrt_pos.mpr hqd
    · exact Real.sqrt_pos.mpr hd'
  set F : JTuple r q d → Finset (JTuple r q d) := fun x =>
    Finset.univ.filter fun y => Exch x y ∧ (b ∈ (x u).1 ↔ b ∉ (y u).1) with hF
  have hentry : ∀ x y, |M x y| ≤ if y ∈ F x then 1 else 0 := by
    intro x y
    rw [hM, hadamard_advDOn_apply, johnsonΓ_apply]
    by_cases hr : read x i = read y i
    · rw [ite_eq_left hr, abs_zero]
      split_ifs <;> norm_num
    · rw [ite_eq_right hr]
      by_cases he : Exch x y
      · rw [ite_eq_left he, ite_eq_left (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hi x y hr⟩)]
        norm_num
      · rw [ite_eq_right he, abs_zero]
        split_ifs <;> norm_num
  have hsymm : ∀ x y, |M x y| = |M y x| := by
    intro x y
    rw [hM, hadamard_advDOn_apply, hadamard_advDOn_apply, johnsonΓ_symm]
    exact congrArg _ (if_congr ⟨Eq.symm, Eq.symm⟩ rfl rfl)
  have hrow : ∀ x, ∑ y, |M x y| * p y ≤ Real.sqrt (d * (q - d : ℕ)) * p x := by
    intro x
    have hbound : ∑ y, |M x y| * p y ≤ ∑ y ∈ F x, p y := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => y ∈ F x)]
      have h0 : ∑ y ∈ Finset.univ.filter (fun y => y ∉ F x), |M x y| * p y ≤ 0 :=
        Finset.sum_nonpos fun y hy => by
          have := hentry x y
          rw [ite_eq_right (Finset.mem_filter.mp hy).2] at this
          nlinarith [abs_nonneg (M x y), hppos y]
      have h1 : ∑ y ∈ Finset.univ.filter (fun y => y ∈ F x), |M x y| * p y ≤ ∑ y ∈ F x, p y := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        refine Finset.sum_le_sum fun y hy => ?_
        have := hentry x y
        rw [ite_eq_left hy] at this
        nlinarith [hppos y]
      linarith
    refine hbound.trans ?_
    by_cases hb : b ∈ (x u).1
    · have hconst : ∀ y ∈ F x, p y = Real.sqrt d := fun y hy => by
        have := ((Finset.mem_filter.mp hy).2.2).mp hb
        simp only [hp, ite_eq_right this]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((F x).card : ℝ) ≤ ((q - d : ℕ) : ℝ) := by
        exact_mod_cast card_maskedExch_le_of_mem x hb
      have hpx : p x = Real.sqrt ((q - d : ℕ) : ℝ) := by simp only [hp, ite_eq_left hb]
      rw [hpx, Real.sqrt_mul hd'.le, mul_assoc, Real.mul_self_sqrt hqd.le]
      nlinarith [Real.sqrt_nonneg (d : ℝ)]
    · have hconst : ∀ y ∈ F x, p y = Real.sqrt ((q - d : ℕ) : ℝ) := fun y hy => by
        have : b ∈ (y u).1 := by
          by_contra h
          exact hb (((Finset.mem_filter.mp hy).2.2).mpr h)
        simp only [hp, ite_eq_left this]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((F x).card : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast card_maskedExch_le_of_notMem x hb
      have hpx : p x = Real.sqrt d := by simp only [hp, ite_eq_right hb]
      rw [hpx, Real.sqrt_mul hd'.le, mul_comm (Real.sqrt d), mul_assoc,
        Real.mul_self_sqrt hd'.le]
      nlinarith [Real.sqrt_nonneg ((q - d : ℕ) : ℝ)]
  refine l2_opNorm_le_of_weighted hppos (Real.sqrt_nonneg _) hrow fun y => ?_
  calc ∑ x, |M x y| * p x = ∑ x, |M y x| * p x :=
        Finset.sum_congr rfl fun x _ => by rw [hsymm]
    _ ≤ Real.sqrt (d * (q - d : ℕ)) * p y := hrow y

/-! ## The enumeration bounds -/

/-- **The enumeration adversary** (`eq:profile-enumeration-lower`): for `1 ≤ d < q`, any promise
read map on `r`-tuples of `d`-subsets of `Fin q` in which each position is constant or can only
separate inputs differing in one membership bit, and any output that separates exchanged inputs,
`r·√(d(q − d)) ≤ advPMOn`. -/
theorem enumeration_advPMOn_ge (hd : 0 < d) (hdq : d < q) {ι σ O : Type*} [Finite ι]
    [DecidableEq σ] (read : JTuple r q d → ι → σ) (f : JTuple r q d → O)
    (hdet : ∀ x y, read x = read y → f x = f y) (hsep : ∀ x y, Exch x y → f x ≠ f y)
    (hread : ∀ i, (∀ x y, read x i = read y i) ∨
      ∃ u b, ∀ x y, read x i ≠ read y i → (b ∈ (x u).1 ↔ b ∉ (y u).1)) :
    (r : ℝ) * Real.sqrt (d * (q - d : ℕ)) ≤ advPMOn read f := by
  classical
  have := Fintype.ofFinite ι
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hqd : (0 : ℝ) < ((q - d : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hdq
  have hlam : 0 < Real.sqrt (d * (q - d : ℕ)) := Real.sqrt_pos.mpr (mul_pos hd' hqd)
  have hadv : IsAdvMatrixOn f (johnsonΓ r q d) :=
    ⟨johnsonΓ_isHermitian, fun x y hxy => by
      rw [johnsonΓ_apply, ite_eq_right fun h => hsep x y h hxy]⟩
  have hmask : ∀ i, ‖johnsonΓ r q d ⊙ advDOn read i‖ ≤ Real.sqrt (d * (q - d : ℕ)) := by
    intro i
    rcases hread i with hc | ⟨u, b, hub⟩
    · have h0 : johnsonΓ r q d ⊙ advDOn read i = 0 := by
        ext x y
        rw [hadamard_advDOn_apply, ite_eq_left (hc x y), Matrix.zero_apply]
      rw [h0, norm_zero]
      exact hlam.le
    · exact johnsonΓ_hadamard_le hd hdq read i hub
  have h := norm_div_le_advPMOn hdet hadv hmask hlam
  have hnorm := johnsonΓ_norm_ge (r := r) hdq.le
  have heq : (r : ℝ) * Real.sqrt (d * (q - d : ℕ)) =
      (r : ℝ) * (d * (q - d : ℕ)) / Real.sqrt (d * (q - d : ℕ)) := by
    rw [mul_div_assoc, Real.div_sqrt]
  rw [heq]
  exact (div_le_div_of_nonneg_right hnorm hlam.le).trans h

/-- The membership bits of a tuple: the query at `(u, b)` returns whether `b ∈ x u`. -/
def enumRead (x : JTuple r q d) (p : Fin r × Fin q) : Bool := decide (p.2 ∈ (x p.1).1)

/-- **`eq:profile-enumeration-lower`**: identifying `r` independent `d`-element subsets of a
`q`-element set from their membership bits costs `Q_{1/3} ≥ (7/1376)·r·√(d(q − d))`, for
`1 ≤ d < q`. -/
theorem enumeration_qQuery_ge (hd : 0 < d) (hdq : d < q) :
    (7 / 1376 : ℝ) * (r * Real.sqrt (d * (q - d : ℕ))) ≤
      qQueryOn (enumRead (r := r) (q := q) (d := d)) id (1 / 3) := by
  classical
  have : Nonempty (JTuple r q d) := nonempty_jTuple hdq.le
  have hdet : ∀ x y : JTuple r q d, enumRead x = enumRead y → id x = id y := by
    intro x y h
    funext u
    refine Subtype.ext (Finset.ext fun b => ?_)
    have := congrFun h (u, b)
    simp only [enumRead, decide_eq_decide] at this
    exact this
  have hread : ∀ p : Fin r × Fin q, (∀ x y : JTuple r q d, enumRead x p = enumRead y p) ∨
      ∃ u b, ∀ x y : JTuple r q d, enumRead x p ≠ enumRead y p →
        (b ∈ (x u).1 ↔ b ∉ (y u).1) := fun p => Or.inr ⟨p.1, p.2, fun x y h => by
    simp only [enumRead, ne_eq, decide_eq_decide] at h
    tauto⟩
  refine le_trans ?_ (mul_advPMOn_le_qQueryOn_third_finiteOutput hdet)
  exact mul_le_mul_of_nonneg_left
    (enumeration_advPMOn_ge hd hdq enumRead id hdet (fun x y h => h.ne) hread) (by norm_num)

/-- **Two inputs with different outputs give `1 ≤ advPMOn`.** -/
theorem one_le_advPMOn_of_ne {ι σ X O : Type*} [Finite ι] [DecidableEq σ]
    [Fintype X] [DecidableEq X] {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) {x y : X} (hxy : f x ≠ f y) :
    1 ≤ advPMOn read f := by
  classical
  have := Fintype.ofFinite ι
  have hne : x ≠ y := fun h => hxy (h ▸ rfl)
  let Γ : Matrix X X ℝ := Matrix.of fun a b => if (a = x ∧ b = y) ∨ (a = y ∧ b = x) then 1 else 0
  have hΓ : ∀ a b, Γ a b = Γ b a := fun a b => by
    simp only [Γ, Matrix.of_apply]
    exact if_congr (by tauto) rfl rfl
  have hadv : IsAdvMatrixOn f Γ := by
    refine ⟨?_, fun a b hab => ?_⟩
    · ext a b
      simp only [Matrix.conjTranspose_apply, star_trivial]
      exact hΓ b a
    · simp only [Γ, Matrix.of_apply]
      rw [ite_eq_right]
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hxy hab
      · exact hxy hab.symm
  have hrow : ∀ a, ∑ b, |Γ a b| ≤ 1 := by
    intro a
    have habs : ∀ b, |Γ a b| = if (a = x ∧ b = y) ∨ (a = y ∧ b = x) then 1 else 0 := fun b => by
      simp only [Γ, Matrix.of_apply]
      split_ifs <;> simp
    simp only [habs]
    rw [Finset.sum_boole]
    have hcard : (Finset.univ.filter fun b => (a = x ∧ b = y) ∨ (a = y ∧ b = x)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun b hb b' hb' => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hb' with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h2, h4]
      · exact absurd (h1.symm.trans h3) hne
      · exact absurd (h3.symm.trans h1) hne
      · rw [h2, h4]
    exact_mod_cast hcard
  have hmask : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1 := by
    intro i
    have hent : ∀ a b, |(Γ ⊙ advDOn read i) a b| ≤ |Γ a b| := fun a b => by
      rw [hadamard_advDOn_apply]
      split_ifs <;> simp
    refine l2_opNorm_le_of_rowcol_le zero_le_one (fun a => ?_) (fun b => ?_)
    · exact (Finset.sum_le_sum fun b _ => hent a b).trans (hrow a)
    · refine (Finset.sum_le_sum fun a _ => hent a b).trans ?_
      calc ∑ a, |Γ a b| = ∑ a, |Γ b a| := Finset.sum_congr rfl fun a _ => by rw [hΓ]
        _ ≤ 1 := hrow b
  have h1 : 1 ≤ ‖Γ‖ := by
    have := abs_entry_le_l2_opNorm Γ x y
    simpa [Γ] using this
  exact h1.trans (le_advPMOn hdet hadv hmask)

end MonoidProduct.Graph
