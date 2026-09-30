import MonoidProduct.Quantum.RTrivialApplications
import MonoidProduct.Quantum.Applications
import MonoidProduct.Width.BreadthBounds
import MonoidProduct.Capped.Breadth
import MonoidProduct.Tropical.Breadth
import MonoidProduct.Aperiodic.CommJTrivial
import MonoidProduct.Trichotomy.Index
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance test: breadth, aperiodicity index, `R`-trivial monoids

The statement pins for three groups of results: product breadth and `κ = β`
with the β forms of the commutative theorems (part 1), the aperiodicity index
and its lower bound (part 2), and the `R`-trivial log-free bound with its
capped-counter sharpness (part 3).  Like the other acceptance files, this file
exists to be broken; `MonoidProduct.lean` imports it, so `lake build` runs it.

Manual axiom checks:

    #print axioms MonoidProduct.advPM_prodFun_le_breadth
      → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.sqrt_index_le_advPM_prodFun
      → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.rtrivial_qQuery_le_min
      → [propext, Classical.choice, Quot.sound]
    #print axioms MonoidProduct.capped_binary_qQuery_lower
      → [propext, Classical.choice, Quot.sound]
-/

namespace MonoidProduct
open QuantumQueryComplexity
namespace AcceptanceV

/-! ## 1. Product breadth -/

section A1

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Fintype M] [DecidableEq M] [CommMonoid M]

/-- `κ = β`: the width bounds of the subset-product summary are the breadth
bounds (`lem:comm-beta-width`). -/
theorem width_iff_breadth_pinned [IsAperiodicMonoid M] (m : σ → M) {b : ℕ} :
    (∀ (n : ℕ) (x : Fin n → σ) (T : Finset (Fin n)), (prodEss m x T).card ≤ b)
      ↔ IsBreadthBound m b :=
  isWidthBound_iff_isBreadthBound m

/-- `thm:commutative-beta`: `ADV± ≤ 16√(n·min{n, β})`. -/
theorem commutative_beta_pinned [IsAperiodicMonoid M] (m : σ → M) :
    advPM (fun x : ι → σ => ∏ i, m (x i))
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * (min (Fintype.card ι) (breadth m) : ℕ)) :=
  advPM_prodFun_le_breadth m

/-- `thm:semilattice-product`, breadth clause: `β ≤ ⌊log₂|M|⌋` under `x² = x`. -/
theorem idempotent_breadth_pinned (hidem : ∀ a : M, a * a = a) (m : σ → M) :
    breadth m ≤ Nat.log 2 (Fintype.card M) :=
  breadth_le_log_of_idem hidem m

/-- `thm:index-two-width`, breadth clause: `β < 5·log₂|M|` under `x³ = x²`. -/
theorem indexTwo_breadth_pinned (hx3 : ∀ z : M, z ^ 3 = z ^ 2) (hM : 2 ≤ Fintype.card M)
    (m : σ → M) : (breadth m : ℝ) < 5 * Real.logb 2 (Fintype.card M) :=
  breadth_lt_five_logb hx3 hM m

/-- `thm:index-k-width`, breadth clause, at the explicit constant. -/
theorem indexK_breadth_pinned {k : ℕ} (hxk : ∀ w : M, w ^ (k + 1) = w ^ k) (hk : 0 < k)
    (m : σ → M) :
    (breadth m : ℝ) ≤ 2 ^ 62 * ((k : ℝ) + 1) * bcwT M * Real.logb 2 (bcwT M) :=
  breadth_le_bcw hxk hk m

/-- `thm:capped-counter-product`, breadth clause: `β(M_{k,r}) = k·r`. -/
theorem capped_breadth_pinned {ρ : Type} [Fintype ρ] [DecidableEq ρ] {k : ℕ} (hk : 0 < k) :
    breadth (id : (ρ → Capped k) → (ρ → Capped k)) = Fintype.card ρ * k :=
  breadth_capped_eq hk

/-- `cor:unitriangular-beta`, breadth half: a core of at most
`(k−1)k(k+1)/6` positions for every unitriangular tropical word. -/
theorem unitriangular_core_pinned {k : ℕ} {letter : σ → TMat k}
    (hL : ∀ a, IsUtri (letter a)) (n : ℕ) (w : Fin n → σ) :
    ∃ C : Finset (Fin n), 6 * C.card ≤ (k - 1) * k * (k + 1) ∧
      linProd (optLetter letter) n (mask C w) = linProd letter n w :=
  exists_core_linProd_six_mul hL n w

/-- `prop:comm-jtrivial`. -/
theorem comm_jtrivial_pinned [IsAperiodicMonoid M] : IsJTrivialMonoid M :=
  isJTrivialMonoid_of_comm

end A1

/-! ## 2. The aperiodicity index -/

section A2

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] [IsAperiodicMonoid M]
  [Nontrivial M] {n : ℕ}

/-- `thm:aperiodicity-index-lower`: `√(n·min{n, ι(M)})/2 ≤ ADV±(Prod_{M,n})`. -/
theorem index_lower_pinned (hn : 1 ≤ n) :
    Real.sqrt ((n * min n (aperiodicIndex M) : ℕ) : ℝ) / 2
      ≤ advPM (fun w : Fin n → M => wordProd (id : M → M) w) :=
  sqrt_index_le_advPM_prodFun hn

/-- `thm:aperiodicity-index-lower`, operational, at the sharp Boolean `1/36`. -/
theorem index_qQuery_pinned (hn : 1 ≤ n) :
    (1 / 36 : ℝ) * (Real.sqrt ((n * min n (aperiodicIndex M) : ℕ) : ℝ) / 2)
      ≤ (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ) :=
  index_qQuery_lower hn

end A2

/-! ## 3. `R`-trivial monoids -/

section A3

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M] {n : ℕ} (letter : σ → M)

/-- `thm:rtrivial`: `ADV± ≤ 8√(n·min{n, d_R(M)})`. -/
theorem rtrivial_pinned (hR : IsRTrivialMonoid M) :
    advPM (fun x : Fin n → σ => wordProd letter x)
      ≤ 8 * Real.sqrt ((n : ℝ) * ((min n (rDepth M) : ℕ) : ℝ)) :=
  advPM_wordProd_le_of_isRTrivial letter hR

/-- `thm:rtrivial`, promise form: `ADV± ≤ 8√(n·C_𝒟)`. -/
theorem rtrivial_promise_pinned {X : Type} [Fintype X] [DecidableEq X]
    (read : X → Fin n → σ) {C : ℕ}
    (hC : ∀ x, changeCount (1 : M) (mulStep letter) (read x) ≤ C) :
    advPMOn read (fun x => wordProd letter (read x)) ≤ 8 * Real.sqrt ((n : ℝ) * (C : ℝ)) :=
  advPMOn_wordProd_le_of_changeCount letter read hC

/-- `thm:rtrivial`, operational: `Q_{1/3} ≤ min{n, 8192·(1 + 8√(n·min{n, d_R}))}`. -/
theorem rtrivial_qQuery_pinned (hR : IsRTrivialMonoid M) :
    (qQuery (fun x : Fin n → σ => wordProd letter x) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (8192
          * (1 + 8 * Real.sqrt ((n : ℝ) * ((min n (rDepth M) : ℕ) : ℝ)))) :=
  rtrivial_qQuery_le_min letter hR

/-- Every finite `R`-trivial monoid is aperiodic. -/
theorem rtrivial_aperiodic_pinned (hR : IsRTrivialMonoid M) : IsAperiodicMonoid M :=
  isAperiodicMonoid_of_isRTrivial hR

/-- `prop:jtrivial-log-fails`: `d_R(M_K) = K`. -/
theorem capped_depth_pinned {k : ℕ} : rDepth (Capped k) = k :=
  Capped.rDepth_eq

/-- `prop:jtrivial-log-fails`, operational: `(7/1376)·√(n·min{n, K})/4 ≤ Q_{1/3}`
for the capped counter on binary inputs. -/
theorem capped_binary_lower_pinned {k : ℕ} (hk : 0 < k) [Nonempty (Fin n)] :
    (7 / 1376 : ℝ) * (Real.sqrt ((n : ℝ) * ((min n k : ℕ) : ℝ)) / 4)
      ≤ (qQuery (fun x : Fin n → Bool => ∏ i, (if x i then Capped.gen else (1 : Capped k)))
          (1 / 3) : ℝ) :=
  capped_binary_qQuery_lower hk

end A3

end AcceptanceV

end MonoidProduct
