import MonoidProduct.Tropical.Mask
import MonoidProduct.Tropical.Lower
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Transition supports: the paper's certificates, without a path API

The paper selects, for each requested entry `(s,t)` of a
tropical product, a maximizing path, and takes the positions at which it
makes strict state transitions; a path from `s` to `t` makes at most `t − s`
of them (`prop:path`), and retaining only those positions
preserves the entry.  Here the same content is proved **directly by
induction on the product**, with no paths:

`exists_transitionSupport` — for every word `w` and entry `(s,t)` there is a
set `S` of at most `t − s` positions with `[w|_S]_{st} = [w]_{st}`.

The induction on the last letter `X`: the entry `(P ⊗ X)_{st} = ⊔_v (P_{sv}
+ X_{vt})` is attained at some `v`; if the value is `−∞` nothing needs
retaining; otherwise unitriangularity forces `s ≤ v ≤ t`; at `v = t` the
last letter contributes `X_{tt} = 0`, so the support of `P_{st}` (at most
`t − s` positions) still works after dropping the last letter; at `v < t`
the last letter is a strict transition, and the support of `P_{sv}` (at
most `v − s` positions) plus the last position has at most `t − s`.

Taking the union over the requested entries gives the certificate
(`exists_certificate`): at most `ν(E) = ∑ (t − s)` positions, and the
retained word carries every requested entry (by the monotonicity of
`Mask.lean`, since each entry's own support is contained in the union).
`supportCert` chooses one such certificate per promise input; these are the
hypotheses `hν`/`hC` of `Packed.lean`, discharged.  The certificate is
stated in *support* language (the properties the proof uses), not as the
strict transitions of maximizing paths.

Also here: the transition volume of an explicit entry set (`volume`), the
enumeration `enumOf` that feeds a `Finset` of entries to the `Fin`-indexed
interface, and the full-entry count `∑_{s<t} (t − s) = k(k² − 1)/6`
(`six_mul_volume_strictPairs`).
-/

namespace MonoidProduct
open QuantumQueryComplexity

variable {k : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## Masks and the last letter -/

section MaskSucc

variable {n : ℕ}

/-- The embedding of the first `n` positions. -/
def castSuccEmb (n : ℕ) : Fin n ↪ Fin (n + 1) := ⟨Fin.castSucc, Fin.castSucc_injective n⟩

lemma mask_castSucc_map (S : Finset (Fin n)) (w : Fin (n + 1) → σ) :
    (fun i => mask (S.map (castSuccEmb n)) w i.castSucc)
      = mask S fun i => w i.castSucc := by
  funext i
  simp [mask, castSuccEmb]

lemma mask_map_last (S : Finset (Fin n)) (w : Fin (n + 1) → σ) :
    mask (S.map (castSuccEmb n)) w (Fin.last n) = none := by
  simp [mask, castSuccEmb, Finset.mem_map, (Fin.castSucc_lt_last _).ne]

lemma mask_castSucc_insert (S : Finset (Fin n)) (w : Fin (n + 1) → σ) :
    (fun i => mask (insert (Fin.last n) (S.map (castSuccEmb n))) w i.castSucc)
      = mask S fun i => w i.castSucc := by
  funext i
  simp [mask, castSuccEmb, Finset.mem_insert, (Fin.castSucc_lt_last i).ne]

lemma mask_insert_last (S : Finset (Fin n)) (w : Fin (n + 1) → σ) :
    mask (insert (Fin.last n) (S.map (castSuccEmb n))) w (Fin.last n)
      = some (w (Fin.last n)) := by
  simp [mask]

end MaskSucc

/-! ## The transition support of one entry -/

/-- **Every entry has a support of at most `t − s` positions**: retaining them
preserves the entry.  Proved by induction on the product; the paper's
maximizing paths never appear. -/
theorem exists_transitionSupport {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a)) :
    ∀ (n : ℕ) (w : Fin n → σ) (s t : Fin k), ∃ S : Finset (Fin n),
      S.card ≤ (t : ℕ) - s ∧
      linProd (optLetter letter) n (mask S w) s t = linProd letter n w s t ∧
      (linProd letter n w s t = ⊥ → S = ∅) := by
  intro n
  induction n with
  | zero =>
      intro w s t
      exact ⟨∅, by simp, rfl, fun _ => rfl⟩
  | succ n ih =>
      intro w s t
      have hval : linProd letter (n + 1) w s t
          = Finset.univ.sup fun v =>
              linProd letter n (fun i => w i.castSucc) s v + letter (w (Fin.last n)) v t :=
        rfl
      obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨s, Finset.mem_univ s⟩
        fun v => linProd letter n (fun i => w i.castSucc) s v + letter (w (Fin.last n)) v t
      have hle : ∀ S : Finset (Fin (n + 1)),
          linProd (optLetter letter) (n + 1) (mask S w) s t ≤ linProd letter (n + 1) w s t :=
        fun S => linProd_mask_le hL S w s t
      by_cases hbot : linProd letter n (fun i => w i.castSucc) s v + letter (w (Fin.last n)) v t = ⊥
      · refine ⟨∅, by simp, le_antisymm (hle ∅) ?_, fun _ => rfl⟩
        rw [hval, hv, hbot]
        exact bot_le
      · have hPv : linProd letter n (fun i => w i.castSucc) s v ≠ ⊥ :=
          fun h => hbot (by rw [h, WithBot.bot_add])
        have hXv : letter (w (Fin.last n)) v t ≠ ⊥ :=
          fun h => hbot (by rw [h, WithBot.add_bot])
        have hsv : (s : ℕ) ≤ v := by
          by_contra h
          exact hPv ((isUtri_linProd hL n _).below s v (Fin.lt_def.mpr (Nat.lt_of_not_le h)))
        have hvt : (v : ℕ) ≤ t := by
          by_contra h
          exact hXv ((hL _).below v t (Fin.lt_def.mpr (Nat.lt_of_not_le h)))
        have hnot : linProd letter (n + 1) w s t ≠ ⊥ := by
          rw [hval, hv]
          exact hbot
        obtain ⟨S, hS, hSeq, -⟩ := ih (fun i => w i.castSucc) s v
        by_cases hvt' : v = t
        · -- no transition at the last letter: it contributes `X_{tt} = 0`
          subst hvt'
          refine ⟨S.map (castSuccEmb n), by rw [Finset.card_map]; exact hS, ?_,
            fun h => absurd h hnot⟩
          rw [hval, hv, (hL _).diag, add_zero, linProd_succ, mask_castSucc_map, mask_map_last]
          change tmul _ (tone k) s v = _
          rw [tmul_tone, hSeq]
        · -- a strict transition at the last letter
          have hvlt : (v : ℕ) < t := lt_of_le_of_ne hvt fun h => hvt' (Fin.ext h)
          refine ⟨insert (Fin.last n) (S.map (castSuccEmb n)), ?_, le_antisymm (hle _) ?_,
            fun h => absurd h hnot⟩
          · calc (insert (Fin.last n) (S.map (castSuccEmb n))).card
                ≤ (S.map (castSuccEmb n)).card + 1 := Finset.card_insert_le _ _
              _ = S.card + 1 := by rw [Finset.card_map]
              _ ≤ (t : ℕ) - s := by omega
          · rw [hval, hv, linProd_succ, mask_castSucc_insert, mask_insert_last]
            change _ ≤ Finset.univ.sup fun u =>
              linProd (optLetter letter) n (mask S fun i => w i.castSucc) s u
                + letter (w (Fin.last n)) u t
            rw [← hSeq]
            exact Finset.le_sup (f := fun u =>
              linProd (optLetter letter) n (mask S fun i => w i.castSucc) s u
                + letter (w (Fin.last n)) u t) (Finset.mem_univ v)

/-! ## Certificates for a set of requested entries -/

variable {m : ℕ}

/-- **The transition volume** `ν(E) = ∑ (t − s)` of an enumerated entry set. -/
def nu (E : Fin m → Fin k × Fin k) : ℕ := ∑ j, (((E j).2 : ℕ) - (E j).1)

/-- **The certificate**: a set of at most `ν(E)` positions whose retained
word carries every requested entry, and which is empty when every requested
entry is `−∞` (the paper's convention for the empty certificate). -/
theorem exists_certificate {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (E : Fin m → Fin k × Fin k) (n : ℕ) (w : Fin n → σ) :
    ∃ C : Finset (Fin n), C.card ≤ nu E ∧
      entries E (linProd (optLetter letter) n (mask C w)) = entries E (linProd letter n w) ∧
      ((∀ j, linProd letter n w (E j).1 (E j).2 = ⊥) → C = ∅) := by
  classical
  choose S hS using fun j => exists_transitionSupport hL n w (E j).1 (E j).2
  refine ⟨Finset.univ.biUnion S, ?_, ?_, ?_⟩
  · exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun j _ => (hS j).1)
  · refine congrArg toLex (funext fun j => le_antisymm ?_ ?_)
    · exact linProd_mask_le hL _ w _ _
    · rw [← (hS j).2.1]
      exact linProd_mask_mono hL (Finset.subset_biUnion_of_mem S (Finset.mem_univ j)) w _ _
  · intro hbot
    refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hi
    rw [(hS j).2.2 (hbot j)] at hj
    simp at hj

variable {X : Type} [Fintype X]

/-- **The support certificates**: one transition-support certificate per
promise input, chosen from `exists_certificate`.  This is a *support*
certificate — at most `ν(E)` positions, the retained word carries every
requested entry, empty when every requested entry is `−∞` — which is exactly
what the assembly uses; it is not asserted to consist of the strict
transitions of maximizing paths, so its incidence is the incidence of
*these* supports, not the paper's path-defined `h_E` verbatim. -/
noncomputable def supportCert {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (E : Fin m → Fin k × Fin k) {n : ℕ} (read : X → Fin n → σ) (x : X) : Finset (Fin n) :=
  (exists_certificate hL E n (read x)).choose

lemma supportCert_card_le {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (E : Fin m → Fin k × Fin k) {n : ℕ} (read : X → Fin n → σ) (x : X) :
    (supportCert hL E read x).card ≤ nu E :=
  (exists_certificate hL E n (read x)).choose_spec.1

lemma supportCert_eq_empty_of_bot {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (E : Fin m → Fin k × Fin k) {n : ℕ} (read : X → Fin n → σ) (x : X)
    (hbot : ∀ j, linProd letter n (read x) (E j).1 (E j).2 = ⊥) :
    supportCert hL E read x = ∅ :=
  (exists_certificate hL E n (read x)).choose_spec.2.2 hbot

lemma supportCert_spec {letter : σ → TMat k} (hL : ∀ a, IsUtri (letter a))
    (E : Fin m → Fin k × Fin k) {n : ℕ} (read : X → Fin n → σ) (x : X) :
    entries E (linProd (optLetter letter) n (mask (supportCert hL E read x) (read x)))
      = entries E (linProd letter n (read x)) :=
  (exists_certificate hL E n (read x)).choose_spec.2.1

/-! ## Explicit entry sets, and the full-entry count -/

/-- All strict upper-triangular entries. -/
def strictPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter fun p => (p.1 : ℕ) < p.2

/-- The transition volume of an explicit entry set. -/
def volume (E' : Finset (Fin k × Fin k)) : ℕ := ∑ p ∈ E', ((p.2 : ℕ) - p.1)

/-- Feeding an explicit entry set to the enumerated interface. -/
noncomputable def enumOf (E' : Finset (Fin k × Fin k)) :
    Fin (Fintype.card E') → Fin k × Fin k :=
  fun j => ((Fintype.equivFin E').symm j).1

lemma nu_enumOf (E' : Finset (Fin k × Fin k)) : nu (enumOf E') = volume E' := by
  rw [nu, volume, ← Finset.sum_coe_sort E' fun p => ((p.2 : ℕ) - p.1)]
  exact Equiv.sum_comp (Fintype.equivFin E').symm fun p : E' => ((p.1.2 : ℕ) - p.1.1)

/-- The one-entry gap counts. -/
def gapCount (a b : ℕ) : ℕ := if a < b then b - a else 0

lemma gapCount_of_lt {a b : ℕ} (h : a < b) : gapCount a b = b - a := if_pos h

lemma gapCount_of_ge {a b : ℕ} (h : b ≤ a) : gapCount a b = 0 := if_neg (not_lt.mpr h)

lemma volume_strictPairs (m : ℕ) :
    volume (strictPairs m) = ∑ s : Fin m, ∑ t : Fin m, gapCount s t := by
  rw [volume, strictPairs, Finset.sum_filter, Fintype.sum_prod_type]
  rfl

lemma two_mul_sum_sub (m : ℕ) : 2 * (∑ s : Fin m, (m - (s : ℕ))) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hshift : (∑ s : Fin m, (m + 1 - (s : ℕ))) = (∑ s : Fin m, (m - (s : ℕ))) + m :=
        calc (∑ s : Fin m, (m + 1 - (s : ℕ)))
            = ∑ s : Fin m, ((m - (s : ℕ)) + 1) :=
              Finset.sum_congr rfl fun s _ => by have := s.isLt; omega
          _ = (∑ s : Fin m, (m - (s : ℕ))) + m := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                smul_eq_mul, mul_one]
      rw [hshift, Nat.add_sub_cancel_left]
      nlinarith [ih]

lemma sum_gapCount_succ (m : ℕ) :
    (∑ s : Fin (m + 1), ∑ t : Fin (m + 1), gapCount s t)
      = (∑ s : Fin m, ∑ t : Fin m, gapCount s t) + ∑ s : Fin m, (m - (s : ℕ)) := by
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ t : Fin m, gapCount m t) = 0 :=
    Finset.sum_eq_zero fun t _ => gapCount_of_ge (Nat.le_of_lt t.isLt)
  have h2 : (∑ s : Fin m, gapCount s m) = ∑ s : Fin m, (m - (s : ℕ)) :=
    Finset.sum_congr rfl fun s _ => gapCount_of_lt s.isLt
  rw [h1, h2, gapCount_of_ge le_rfl]
  ring

/-- **The full-entry count** `∑_{s<t} (t − s) = k(k² − 1)/6`, division-free:
in dimension `k` it reads `6·ν = (k − 1)·k·(k + 1)`; this is the same
identity in dimension `k + 1`, `6·ν = k·(k + 1)·(k + 2)`, which also avoids
the natural subtraction. -/
theorem six_mul_volume_strictPairs_succ (k : ℕ) :
    6 * volume (strictPairs (k + 1)) = k * (k + 1) * (k + 2) := by
  rw [volume_strictPairs]
  induction k with
  | zero => simp [gapCount]
  | succ k ih =>
      rw [sum_gapCount_succ, mul_add, ih,
        show 6 * (∑ s : Fin (k + 1), (k + 1 - (s : ℕ)))
            = 3 * (2 * ∑ s : Fin (k + 1), (k + 1 - (s : ℕ))) by ring,
        two_mul_sum_sub]
      ring

theorem six_mul_volume_strictPairs (k : ℕ) :
    6 * volume (strictPairs k) = (k - 1) * k * (k + 1) := by
  cases k with
  | zero => simp [volume, strictPairs]
  | succ k => rw [six_mul_volume_strictPairs_succ, Nat.add_sub_cancel]

end MonoidProduct
