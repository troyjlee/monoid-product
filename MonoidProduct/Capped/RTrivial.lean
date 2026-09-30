import MonoidProduct.Aperiodic.RTrivial
import MonoidProduct.Aperiodic.CommJTrivial
import MonoidProduct.Capped.Theta
import QuantumQueryComplexity.Promise.PostInjective
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Capped addition: `d_R = K`, and logarithmic size does not control the product

`monoid.tex` Proposition `prop:jtrivial-log-fails`: the capped counter
`M_K = ({0, …, K}, a ⊕ b = min{a + b, K})` (`Capped K`) is a finite commutative
`𝓙`-trivial monoid with right-ideal depth `d_R(M_K) = K`, yet its product on
binary inputs needs `Ω(√(n·min{n, K}))` queries.  So no uniform
`Õ(√(n·log|M|))` bound holds for finite `𝓙`-trivial monoids, and the `d_R`
dependence of Theorem `thm:rtrivial` is sharp.

* `Capped.rightIdeal_iff`: `b ∈ aM ↔ a ≤ b`; hence `rLevel a = a` and
  `rDepth (Capped K) = K`.
* `Capped.isRTrivialMonoid`, `Capped.isJTrivialMonoid` (the latter from
  commutativity + aperiodicity, `isJTrivialMonoid_of_comm`).
* `Capped.sqrt_le_advPM_binary`: the lower bound `√(n·min{n, K})/4 ≤ ADV±`
  for the product of binary letters `{0, 1}`, from the capped-counter
  certificate of `Capped/Theta.lean` at one coordinate.
-/

namespace MonoidProduct
open QuantumQueryComplexity

namespace Capped

variable {k : ℕ}

/-- The capped counter is aperiodic: `a^{k+1} = a^{k+2}`. -/
instance : IsAperiodicMonoid (Capped k) :=
  ⟨fun a => ⟨k + 1, Nat.succ_pos k, by
    rw [pow_succ a (k + 1), pow_index, ← pow_succ, pow_index]⟩⟩

/-- Building a counter value from a bounded natural (the anonymous constructor
elaborates at `Fin`, not at `Capped`, inside tactic blocks). -/
def ofVal (v : ℕ) (h : v ≤ k) : Capped k := ⟨v, by omega⟩

@[simp] lemma ofVal_val (v : ℕ) (h : v ≤ k) : (ofVal v h : Capped k).val = v := rfl

/-! ## Right ideals -/

lemma rightIdeal_iff (a b : Capped k) : b ∈ rightIdeal a ↔ a.val ≤ b.val := by
  rw [mem_rightIdeal]
  constructor
  · rintro ⟨q, rfl⟩
    rw [mul_val]
    have := a.val_le
    omega
  · intro h
    refine ⟨ofVal (b.val - a.val) (by have := b.val_le; omega), ?_⟩
    apply Capped.ext
    rw [mul_val, ofVal_val]
    have := b.val_le
    omega

lemma rightIdeal_ssubset_iff (a b : Capped k) :
    rightIdeal a ⊂ rightIdeal b ↔ b.val < a.val := by
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · rintro ⟨hsub, hne⟩
    have h1 : b.val ≤ a.val := (rightIdeal_iff b a).mp (hsub (self_mem_rightIdeal a))
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (by rw [Capped.ext h.symm]) hne
  · intro h
    refine ⟨fun c hc => ?_, fun heq => ?_⟩
    · rw [rightIdeal_iff] at hc ⊢
      omega
    · have : b ∈ rightIdeal a := by
        rw [heq]
        exact self_mem_rightIdeal b
      rw [rightIdeal_iff] at this
      omega

/-- **The level of a counter value is the value.** -/
lemma rLevel_eq_val (a : Capped k) : rLevel a = a.val := by
  induction hv : a.val using Nat.strong_induction_on generalizing a with
  | _ v ih =>
    rw [rLevel_eq]
    apply le_antisymm
    · refine Finset.sup_le fun b hb => ?_
      rw [mem_aboveR, rightIdeal_ssubset_iff] at hb
      have := ih b.val (by omega) b rfl
      omega
    · rcases Nat.eq_zero_or_pos v with hv0 | hv0
      · omega
      · have hle : v - 1 ≤ k := by have := a.val_le; omega
        have hbmem : ofVal (v - 1) hle ∈ aboveR a := by
          rw [mem_aboveR, rightIdeal_ssubset_iff, ofVal_val]
          omega
        have hsup := Finset.le_sup (f := fun c : Capped k => rLevel c + 1) hbmem
        have hb := ih (v - 1) (by omega) (ofVal (v - 1) hle) rfl
        omega

/-- **`d_R(M_K) = K`.** -/
theorem rDepth_eq : rDepth (Capped k) = k := by
  unfold rDepth
  apply le_antisymm
  · refine Finset.sup_le fun a _ => ?_
    rw [rLevel_eq_val]
    exact a.val_le
  · have := Finset.le_sup (f := (rLevel : Capped k → ℕ))
      (Finset.mem_univ (ofVal k le_rfl))
    rwa [rLevel_eq_val, ofVal_val] at this

/-! ## Green triviality -/

theorem isRTrivialMonoid : IsRTrivialMonoid (Capped k) := by
  intro a b h
  have hb : b ∈ rightIdeal a := by
    rw [h]
    exact self_mem_rightIdeal b
  have ha : a ∈ rightIdeal b := by
    rw [← h]
    exact self_mem_rightIdeal a
  rw [rightIdeal_iff] at ha hb
  exact Capped.ext (le_antisymm hb ha)

theorem isJTrivialMonoid : IsJTrivialMonoid (Capped k) :=
  isJTrivialMonoid_of_comm

/-! ## The lower bound on binary inputs -/

/-- The binary alphabet `{0, 1} ⊆ M_K`, as letters of the one-coordinate power
`Unit → Capped k`. -/
def binLetter (k : ℕ) : Bool → Unit → Capped k := fun b _ => if b then Capped.gen else 1

/-- **`√(n·min{n, K})/4 ≤ ADV±`** for the capped product of binary letters
(`prop:jtrivial-log-fails`); with `K ≤ n/2` this is the paper's `Ω(√(nK))`. -/
theorem sqrt_le_advPM_binary (hk : 0 < k) {n : ℕ} [Nonempty (Fin n)] :
    Real.sqrt ((n : ℝ) * ((min n k : ℕ) : ℝ)) / 4
      ≤ advPM (fun x : Fin n → Bool => ∏ i, binLetter k (x i)) := by
  have h := sqrt_le_advPM_prodFun (ι := Fin n) (σ := Bool) (ρ := Unit) (k := k)
    (m := binLetter k) (s0 := false) (e := fun _ => true) hk rfl
    (fun _ => by
      funext c
      simp [binLetter, cappedUnit])
    (fun _ => Bool.false_ne_true)
  simpa using h

/-- The same bound on the counter `M_K` itself, for the binary word product
`∏ᵢ (if xᵢ then 1 else 0)`: the one-coordinate power is an injective
relabelling of the output (`advPM_postcomp_injective`). -/
theorem sqrt_le_advPM_binary' (hk : 0 < k) {n : ℕ} [Nonempty (Fin n)] :
    Real.sqrt ((n : ℝ) * ((min n k : ℕ) : ℝ)) / 4
      ≤ advPM (fun x : Fin n → Bool => ∏ i, (if x i then Capped.gen else (1 : Capped k))) := by
  have hg : Function.Injective fun v : Unit → Capped k => v () :=
    fun a b h => funext fun _ => h
  have h := sqrt_le_advPM_binary hk (n := n)
  rw [← advPM_postcomp_injective hg] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  funext x
  simp [Function.comp, binLetter, Finset.prod_apply]

end Capped

end MonoidProduct
