import MonoidProduct.Aperiodic.CubeRoot.MatrixRank
import MonoidProduct.Aperiodic.CubeRoot.AxisRecurrence
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The word product of a faithful matrix monoid

The rank ceiling (`lem:ags-matrix-rank-ceiling`) bounds every regular height
by the degree, and the regular-action compiler by height
(`prop:ags-action-height`) turns such a bound into a packet
for an arbitrary action.  The action to run is the **right Cayley action**: its
endpoint *is* the word product.

Two small points make the join exact rather than approximate.

* The Cayley action, totalized by an absorbing dead state, **never dies** from
  a live start, so its greatest live cut is the whole word and its packet is
  literally `(Fin.last ℓ, some (wordProd letter x))`.
* Reading `wordProd` off that packet is an **injective** recoding, so it is
  free (`HasDual.ofKer`) — not a postcomposition, which would cost a factor.

No new case splits arise: `hasDual_actionPacket_of_regHeight` already handles
length zero, and `regHeight_add_mrank_le` already handles `d = 0`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Cayley

variable {T : Type} [Monoid T] [Fintype T] [DecidableEq T]

/-- One step of the **right Cayley action**, totalized by an absorbing dead
state.  The live part never reaches it; the dead state is there only because
the compiler's interface asks for one. -/
def cayleyStep (s : Option T) (a : T) : Option T := s.map (· * a)

/-- **The right Cayley action.** -/
def cayleyAction : RightAction T (Option T) where
  act := cayleyStep
  act_one := by rintro (_ | p) <;> simp [cayleyStep]
  act_mul := by rintro (_ | p) a b <;> simp [cayleyStep, mul_assoc]

@[simp] lemma cayleyAction_act (s : Option T) (a : T) :
    (cayleyAction : RightAction T (Option T)).act s a = cayleyStep s a := rfl

lemma cayleyAction_none (a : T) :
    (cayleyAction : RightAction T (Option T)).act none a = none := rfl

variable {σ : Type} [Fintype σ] [DecidableEq σ] (letter : σ → T)

/-- **The Cayley run never dies**, and at every cut it is the prefix product. -/
lemma cutState_cayley {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    cutState (cayleyAction : RightAction T (Option T)) 1 letter x j
      = some (winProd letter x 0 j) := by
  rw [cutState, cayleyAction_act, cayleyStep]
  simp

/-- Hence the greatest live cut is the whole word. -/
lemma liveCut_cayley {n : ℕ} (x : Fin n → σ) :
    liveCut (cayleyAction : RightAction T (Option T)) 1 letter x = n :=
  le_antisymm (liveCut_le _ _ _ _)
    ((liveSet (cayleyAction : RightAction T (Option T)) 1 letter x).le_max' n
      ((mem_liveSet _ _ _).2 ⟨le_rfl, by rw [cutState_cayley]; rfl⟩))

/-- **The packet is the word product**, with the cut pinned at the end. -/
theorem packet_cayley {n : ℕ} (x : Fin n → σ) :
    (liveCutIdx (cayleyAction : RightAction T (Option T)) 1 letter x,
      cutState (cayleyAction : RightAction T (Option T)) 1 letter x
        (liveCut (cayleyAction : RightAction T (Option T)) 1 letter x))
      = (Fin.last n, some (wordProd letter x)) := by
  have hcut := liveCut_cayley letter x
  refine Prod.ext ?_ ?_
  · exact Fin.ext (by rw [liveCutIdx_val, hcut]; rfl)
  · rw [hcut, cutState_cayley, ← wordProd_eq_winProd]

end Cayley

/-! ## The dual for the word product -/

section Faithful

variable {T : Type} [Monoid T] [Fintype T] [DecidableEq T] [IsAperiodicMonoid T]
variable {d : ℕ} {ρ : T →* Matrix (Fin d) (Fin d) ℚ}
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Every owner of the Cayley action sits at regular height at most the degree:
owners are idempotent, hence regular, and the rank ceiling applies. -/
theorem regHeight_cayleyOwner_le (hρ : Function.Injective ρ) (z e : T)
    (hown : MinimalOwner (cayleyAction : RightAction T (Option T)) (some z) e) :
    regHeight e ≤ d :=
  regHeight_le_deg hρ (IsIdempotentElem.isVonNeumannRegular hown.idem)

/-- **The matrix bound.**  A faithfully represented finite aperiodic monoid has a
horizon-uniform dual for its word product, at a coefficient depending only on
the monoid's order, the degree, and the horizon. -/
theorem hasWordProdDualUpTo_of_faithful (hρ : Function.Injective ρ)
    (letter : σ → T) (n₀ : ℕ) :
    HasWordProdDualUpTo letter n₀
      (2 * (Fintype.card T : ℝ)
        * (axisConst (n₀ + d) T ^ (d + 1) + 2)) := by
  have hC1 : 1 ≤ axisConst (n₀ + d) T := one_le_axisConst _ _
  have hCp : (1 : ℝ) ≤ axisConst (n₀ + d) T ^ (d + 1) := one_le_pow₀ hC1
  have hcard : (0 : ℝ) ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
  refine ⟨by nlinarith, fun ℓ hℓ => ?_⟩
  have hpacket := hasDual_actionPacket_of_regHeight
    (cayleyAction : RightAction T (Option T)) letter cayleyAction_none
    (h := d) (H := n₀ + d) (n := ℓ) (regHeight_cayleyOwner_le hρ) (by omega) (1 : T)
  refine hpacket.ofKer fun x y => ?_
  rw [packet_cayley, packet_cayley]
  constructor
  · intro h
    exact Option.some_injective _ (congrArg Prod.snd h)
  · intro h
    rw [h]

end Faithful

/-! ## A general representation

A representation that is not faithful still bounds the heights of its **image**,
so the statement to make is about the image monoid.  `MonoidHom.mrange ρ` is
the right object — a submonoid, so a monoid with the inherited structure, and
aperiodic by `IsAperiodicMonoid.mrange` — and its subtype inclusion is the
faithful representation the ceiling wants.  The output is transported to
ambient matrices by an **injective** recoding, so that step is free too. -/

section Representation

variable {T : Type} [Monoid T] [Fintype T] [DecidableEq T] [IsAperiodicMonoid T]
variable {d : ℕ} (ρ : T →* Matrix (Fin d) (Fin d) ℚ)
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The image monoid of a representation. -/
abbrev repImage : Submonoid (Matrix (Fin d) (Fin d) ℚ) := MonoidHom.mrange ρ

noncomputable instance : Fintype (repImage ρ) := by
  classical
  exact Fintype.ofFinite _

/-- Its inclusion into the matrices is faithful — which is the whole point of
passing to it. -/
lemma repImage_subtype_injective :
    Function.Injective ((repImage ρ).subtype) := Subtype.val_injective

/-- **The matrix bound for an arbitrary representation.**  The word product *of the image*
has a horizon-uniform dual; when `ρ` is faithful this is the previous theorem
after transporting along the isomorphism onto the image. -/
theorem hasWordProdDualUpTo_mrange (letter : σ → T) (n₀ : ℕ) :
    HasWordProdDualUpTo (fun c => MonoidHom.mrangeRestrict ρ (letter c)) n₀
      (2 * (Fintype.card (repImage ρ) : ℝ)
        * (axisConst (n₀ + d) (repImage ρ) ^ (d + 1) + 2)) :=
  hasWordProdDualUpTo_of_faithful (ρ := (repImage ρ).subtype)
    (repImage_subtype_injective ρ) _ n₀

end Representation

end MonoidProduct
