import MonoidProduct.Aperiodic.CubeRoot.Basic
set_option linter.style.header false

/-!
# The carrier recurrence, and the numeric endgame

This file imports no monoid algebra.  It is the arithmetic the whole cube-root
layer is aimed at, isolated from every construction that will feed it:

* **the recurrence** (`le_pow_of_recurrence`).  A carrier-indexed coefficient
  `G` which at every size either stops at `B ^ t` or drops the carrier by `t²`
  at a cost of `B ^ c` satisfies `G m ≤ B ^ (t + (m / t² + 1) · c)`.  Nothing
  about monoids enters: the peel supplies the second alternative, the matrix
  compiler the first, and the radical tower fixes `c`.  Strong induction on the
  carrier; its arithmetic core is `exponent_step`, which is what the assembly's
  *type*-indexed induction reuses, since a maximum over representatives — and so
  a function `ℕ → ℝ` — is exactly what the assembly avoids;
* **the threshold, two-sided** (`cubeThreshold_spec`, upstream, and
  `cubeThreshold_pow_le`).  `s·L(s) ≤ t³ ≤ 8·s·L(s)` — a *Lean-friendly* way to
  say `t` is within a fixed factor of `(s log(s+2))^{1/3}`, with no real cube
  root anywhere;
* **the exponent** (`cubeExponent_le_four_mul`, `cubeExponent_pow_le`).  The two
  terms of `t + (⌈s/t²⌉ + 1)·Λ` balance: `s·Λ/t² ≤ t` is exactly what the
  threshold was chosen for, and `Λ ≤ t` (`clog_le_cubeThreshold`) is where the
  logarithm loses to the cube root.  The headline is
  `cubeExponent s ^ 3 ≤ 512·(s · cubeLog s)`;
* **the normalization** (`recurrenceExponent_le_cubeExponent`,
  `pow_recurrenceExponent_le_cubeRootFactor`), which is what the final assembly calls.  It
  mentions no `G`: the assembly's induction runs over monoid *types*, so it pairs
  `exponent_step` with this opaque normalization.  `cubeRootFactor_of_recurrence`
  is kept as an abstract regression on the packaged form, **not** as the assembly
  interface.

**The coefficient is not frozen.**  `cubeExponent` counts layers; `cubeRootFactor`
carries a multiplier `K` for what a layer costs, and `K` stays a parameter until
the final assembly — see its docstring in `Basic.lean` for the numbers that rule out `K = 1`.
Everything here is stated for every `K`, and `cubeExponent_pow_le_mul` is the
cube root with the multiplier carried through.

Two degenerate cases that must stay out of real arithmetic need no
separate treatment, and one boundary is sharper than it looks.  `s < t²` gives
`s / t² = 0`, so the recursion is one level deep and the exponent is `t + c`.
**Equality is not enough**: at `s = t²` the floor is `1` and the exponent
`t + 2c`, and this is not hypothetical — `s = 81` has `cubeThreshold 81 = 9`, so
`t² = s` exactly.  `s = 1` is just the smallest instance (`t = 2`).  `s = 0` is
genuinely excluded, and must be: with an empty carrier `8·s·L(s) = 0` while
`t = 2`, so the threshold's upper bound is false there.  Every consumer has
`1 ≤ Fintype.card M`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## Two elementary facts about powers, self-contained -/

section Powers

private lemma one_le_pow_of_one_le {B : ℝ} (hB : 1 ≤ B) (k : ℕ) : (1 : ℝ) ≤ B ^ k :=
  one_le_pow₀ hB

/-- `B ≥ 1` makes `B ^ ·` monotone. -/
lemma pow_le_pow_of_le_exponent {B : ℝ} (hB : 1 ≤ B) {m n : ℕ} (h : m ≤ n) :
    B ^ m ≤ B ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have h0 : (0 : ℝ) ≤ B ^ m := pow_nonneg (by linarith) m
  exact le_mul_of_one_le_right h0 (one_le_pow_of_one_le hB k)

end Powers

/-! ## The carrier recurrence

The one theorem the assembly's strong induction is: at each carrier size the
compiler either finishes (a monoid all of whose coordinates are small is paid
for by the matrix compiler) or peels a large coordinate, and a large coordinate
costs `t²` of carrier because its degree exceeds `t`. -/

section Recurrence

variable {B : ℝ} {t c : ℕ} {G : ℕ → ℝ}

/-- **The exponent bookkeeping of one peel.**  A peel costs `c` further layers
and buys `t²` of carrier; this is the statement that the second pays for the
first.

It is stated separately because it is the part of the recurrence a *type*-indexed
induction can still reuse.  The assembly's strong induction runs over monoids,
not over a function `ℕ → ℝ` — it avoids a maximum over representatives, so
no such function is available — and what it needs from this file is exactly this
inequality together with `pow_le_pow_of_le_exponent`. -/
theorem exponent_step {t c m m' : ℕ} (ht : 0 < t) (hm : m' + t ^ 2 ≤ m) :
    c + (t + (m' / t ^ 2 + 1) * c) ≤ t + (m / t ^ 2 + 1) * c := by
  have ht2 : 0 < t ^ 2 := pow_pos ht 2
  have hdiv : m' / t ^ 2 + 1 ≤ m / t ^ 2 := by
    have hstep' := Nat.div_le_div_right (c := t ^ 2) hm
    rwa [Nat.add_div_right m' ht2] at hstep'
  have hstep2 : (m' / t ^ 2 + 2) * c ≤ (m / t ^ 2 + 1) * c :=
    Nat.mul_le_mul (by omega) le_rfl
  have hring : (m' / t ^ 2 + 2) * c = (m' / t ^ 2 + 1) * c + c := by ring
  omega

/-- **The carrier recurrence.**  `t` is the size threshold, `t²` the carrier
drop a peel buys, `c` the number of layers a peel costs, and `B` the per-layer
multiplier.  The exponent `t + (m / t² + 1)·c` is the manuscript's, with
**floor** division — which is sharper than the ceiling `⌈m/t²⌉`, and
implies it.

The depth never appears as a separate quantity: `m / t²` *is* the depth, and the
`+ 1` is the base case's own level. -/
theorem le_pow_of_recurrence (hB : 1 ≤ B) (ht : 0 < t)
    (hrec : ∀ m : ℕ, G m ≤ B ^ t ∨ ∃ m', m' + t ^ 2 ≤ m ∧ G m ≤ B ^ c * G m') :
    ∀ m : ℕ, G m ≤ B ^ (t + (m / t ^ 2 + 1) * c) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases hrec m with hsmall | ⟨m', hm', hstep⟩
    · exact le_trans hsmall (pow_le_pow_of_le_exponent hB (Nat.le_add_right _ _))
    · have hlt : m' < m := by
        have : 0 < t ^ 2 := pow_pos ht 2
        omega
      calc G m ≤ B ^ c * G m' := hstep
        _ ≤ B ^ c * B ^ (t + (m' / t ^ 2 + 1) * c) :=
            mul_le_mul_of_nonneg_left (ih m' hlt) (by positivity)
        _ = B ^ (c + (t + (m' / t ^ 2 + 1) * c)) := (pow_add B _ _).symm
        _ ≤ B ^ (t + (m / t ^ 2 + 1) * c) :=
            pow_le_pow_of_le_exponent hB (exponent_step ht hm')

end Recurrence

/-! ## The threshold is a cube root, from both sides

`cubeThreshold_spec` is the definition's own half.  The other half is
minimality: `t - 1` fails the same test, and `t ≤ 2(t-1)`. -/

/-- **The threshold's upper half.**  Together with `cubeThreshold_spec` this
says `t³` is within a factor `8` of `s·L(s)` — the Lean-friendly reading of "`t`
is within a fixed factor of `(s log(s+2))^{1/3}`".

`1 ≤ s` cannot be dropped: at `s = 0` the right-hand side is `0` and `t = 2`. -/
theorem cubeThreshold_pow_le {s : ℕ} (hs : 1 ≤ s) :
    cubeThreshold s ^ 3 ≤ 8 * (s * cubeLog s) := by
  have ht2 : 2 ≤ cubeThreshold s := two_le_cubeThreshold s
  have hL : 2 ≤ cubeLog s := two_le_cubeLog s
  have hsL : 1 ≤ s * cubeLog s := Nat.one_le_iff_ne_zero.2 (by positivity)
  rcases Nat.lt_or_ge (cubeThreshold s) 3 with hsmall | hbig
  · have h2 : cubeThreshold s = 2 := by omega
    rw [h2]
    norm_num
    omega
  · have hdef : cubeThreshold s = Nat.find (exists_cubeThreshold s) := rfl
    have hmin : ¬ (2 ≤ cubeThreshold s - 1
        ∧ s * cubeLog s ≤ (cubeThreshold s - 1) ^ 3) := by
      refine Nat.find_min (exists_cubeThreshold s) (m := cubeThreshold s - 1) ?_
      rw [← hdef]
      omega
    have hgt : (cubeThreshold s - 1) ^ 3 < s * cubeLog s := by
      by_contra hc
      exact hmin ⟨by omega, by omega⟩
    calc cubeThreshold s ^ 3 ≤ (2 * (cubeThreshold s - 1)) ^ 3 :=
          Nat.pow_le_pow_left (by omega) 3
      _ = 8 * (cubeThreshold s - 1) ^ 3 := by ring
      _ ≤ 8 * (s * cubeLog s) := Nat.mul_le_mul le_rfl (by omega)

/-! ## The logarithm loses to the threshold

`Λ = ⌈log₂(s+2)⌉ ≤ t`.  This is the inequality that turns the exponent's two
terms into one, and it is where an exponential beats a cubic: `Λ` small forces
`s` small only through `s + 2 > 2^{Λ-1}`, and `(Λ-1)³` cannot keep up with
that. -/

private lemma cube_succ_le_two_pow : ∀ k : ℕ, 10 ≤ k → k ^ 3 + 1 ≤ 2 ^ k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
      intro hk
      rcases Nat.lt_or_ge k 10 with h | h
      · have hk9 : k = 9 := by omega
        subst hk9
        norm_num
      · have hprev := ih h
        have h10k : 10 * k ≤ k * k := Nat.mul_le_mul h le_rfl
        have hk3 : k * (3 * k + 3) ≤ k * (k * k) := Nat.mul_le_mul le_rfl (by omega)
        have e1 : (k + 1) ^ 3 = k ^ 3 + (3 * (k * k) + 3 * k) + 1 := by ring
        have e2 : k * (k * k) = k ^ 3 := by ring
        have e3 : k * (3 * k + 3) = 3 * (k * k) + 3 * k := by ring
        have hgrow : (k + 1) ^ 3 + 1 ≤ 2 * (k ^ 3 + 1) := by omega
        calc (k + 1) ^ 3 + 1 ≤ 2 * (k ^ 3 + 1) := hgrow
          _ ≤ 2 * 2 ^ k := Nat.mul_le_mul le_rfl hprev
          _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

private lemma key_cube_lt : ∀ k : ℕ, 2 ≤ k → k ^ 3 < (2 ^ k - 1) * (k + 3) := by
  intro k hk
  rcases Nat.lt_or_ge k 10 with h | h
  · interval_cases k <;> norm_num
  · have h1 := cube_succ_le_two_pow k h
    obtain ⟨Y, hY⟩ : ∃ Y, 2 ^ k = Y + 1 := ⟨2 ^ k - 1, by omega⟩
    rw [hY] at h1 ⊢
    simp only [Nat.add_sub_cancel]
    have hk3 : 1000 ≤ k ^ 3 := by
      have h10 := Nat.pow_le_pow_left h 3
      norm_num at h10
      exact h10
    have hmul : Y * 2 ≤ Y * (k + 3) := Nat.mul_le_mul le_rfl (by omega)
    omega

/-- **The logarithmic factor never exceeds the threshold.**  With
`cubeExponent`'s two terms this is what collapses `t + Λ`-shaped bounds to a
single cube root. -/
theorem clog_le_cubeThreshold {s : ℕ} (hs : 1 ≤ s) :
    Nat.clog 2 (s + 2) ≤ cubeThreshold s := by
  have ht2 : 2 ≤ cubeThreshold s := two_le_cubeThreshold s
  rcases Nat.lt_or_ge (Nat.clog 2 (s + 2)) 3 with hsmall | hbig
  · omega
  · by_contra hcon
    have hlt : cubeThreshold s < Nat.clog 2 (s + 2) := by omega
    have hlow : 2 ^ (Nat.clog 2 (s + 2) - 1) < s + 2 :=
      Nat.pow_pred_clog_lt_self (b := 2) (x := s + 2) (by norm_num) (by omega)
    have hLs : cubeLog s = Nat.clog 2 (s + 2) + 2 := rfl
    have hcube := cubeThreshold_spec s
    rw [hLs] at hcube
    have htl : cubeThreshold s ^ 3 ≤ (Nat.clog 2 (s + 2) - 1) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have hkey := key_cube_lt (Nat.clog 2 (s + 2) - 1) (by omega)
    have hrew : Nat.clog 2 (s + 2) - 1 + 3 = Nat.clog 2 (s + 2) + 2 := by omega
    rw [hrew] at hkey
    have hle : (2 ^ (Nat.clog 2 (s + 2) - 1) - 1) * (Nat.clog 2 (s + 2) + 2)
        ≤ s * (Nat.clog 2 (s + 2) + 2) := Nat.mul_le_mul (by omega) le_rfl
    omega

/-! ## The exponent -/

/-- **The exponent's two terms balance.**  `s·Λ / t² ≤ t` is precisely what the
threshold was chosen for, and the remaining `2Λ` is the ceiling's round-up plus
the base level. -/
theorem cubeExponent_le_add {s : ℕ} :
    cubeExponent s ≤ 2 * cubeThreshold s + 2 * Nat.clog 2 (s + 2) := by
  have ht2 : 2 ≤ cubeThreshold s := two_le_cubeThreshold s
  have hpos : 0 < cubeThreshold s ^ 2 := by positivity
  -- the ceiling is at most the floor plus one
  have hceil : (s + cubeThreshold s ^ 2 - 1) / cubeThreshold s ^ 2
      ≤ s / cubeThreshold s ^ 2 + 1 := by
    have h1 : (s + cubeThreshold s ^ 2 - 1) / cubeThreshold s ^ 2
        ≤ (s + cubeThreshold s ^ 2) / cubeThreshold s ^ 2 :=
      Nat.div_le_div_right (by omega)
    rwa [Nat.add_div_right s hpos] at h1
  -- the main term
  have hmain : (s / cubeThreshold s ^ 2) * Nat.clog 2 (s + 2) ≤ cubeThreshold s := by
    have hstep : (s / cubeThreshold s ^ 2) * Nat.clog 2 (s + 2)
        ≤ (s * Nat.clog 2 (s + 2)) / cubeThreshold s ^ 2 := by
      refine (Nat.le_div_iff_mul_le hpos).2 ?_
      calc s / cubeThreshold s ^ 2 * Nat.clog 2 (s + 2) * cubeThreshold s ^ 2
          = s / cubeThreshold s ^ 2 * cubeThreshold s ^ 2 * Nat.clog 2 (s + 2) := by ring
        _ ≤ s * Nat.clog 2 (s + 2) :=
            Nat.mul_le_mul (Nat.div_mul_le_self _ _) le_rfl
    have hnum : s * Nat.clog 2 (s + 2) ≤ cubeThreshold s ^ 3 := by
      refine le_trans (Nat.mul_le_mul le_rfl ?_) (cubeThreshold_spec s)
      simp only [cubeLog]
      omega
    have hdiv : (s * Nat.clog 2 (s + 2)) / cubeThreshold s ^ 2 ≤ cubeThreshold s := by
      refine le_trans (Nat.div_le_div_right hnum) (le_of_eq ?_)
      rw [show cubeThreshold s ^ 3 = cubeThreshold s * cubeThreshold s ^ 2 by ring]
      exact Nat.mul_div_cancel _ hpos
    exact le_trans hstep hdiv
  calc cubeExponent s
      = cubeThreshold s
        + ((s + cubeThreshold s ^ 2 - 1) / cubeThreshold s ^ 2 + 1)
          * Nat.clog 2 (s + 2) := rfl
    _ ≤ cubeThreshold s
        + ((s / cubeThreshold s ^ 2 + 1) + 1) * Nat.clog 2 (s + 2) :=
        Nat.add_le_add le_rfl (Nat.mul_le_mul (by omega) le_rfl)
    _ = cubeThreshold s + (s / cubeThreshold s ^ 2) * Nat.clog 2 (s + 2)
        + 2 * Nat.clog 2 (s + 2) := by ring
    _ ≤ 2 * cubeThreshold s + 2 * Nat.clog 2 (s + 2) := by omega

/-- **The exponent is four thresholds.** -/
theorem cubeExponent_le_four_mul {s : ℕ} (hs : 1 ≤ s) :
    cubeExponent s ≤ 4 * cubeThreshold s := by
  have h1 := cubeExponent_le_add (s := s)
  have h2 := clog_le_cubeThreshold hs
  omega

/-- **The cube root, integrally.**  `cubeExponent s ³ ≤ 512·s·L(s)`: the
exponent of the cube-root bound is `O((s log s)^{1/3})`, with no real cube root
in the statement and none in the proof. -/
theorem cubeExponent_pow_le {s : ℕ} (hs : 1 ≤ s) :
    cubeExponent s ^ 3 ≤ 512 * (s * cubeLog s) := by
  calc cubeExponent s ^ 3 ≤ (4 * cubeThreshold s) ^ 3 :=
        Nat.pow_le_pow_left (cubeExponent_le_four_mul hs) 3
    _ = 64 * cubeThreshold s ^ 3 := by ring
    _ ≤ 64 * (8 * (s * cubeLog s)) := Nat.mul_le_mul le_rfl (cubeThreshold_pow_le hs)
    _ = 512 * (s * cubeLog s) := by ring

/-! ## Normalization, and the packaged endpoint

`recurrenceExponent` is what the recurrence produces; `cubeExponent` is the
frozen shape.  The comparison between them is the only place the two meet, and
it is exported on its own — with no `G` in sight — because the assembly cannot
build a `G`. -/

/-- **The exponent the recurrence produces** at the top carrier, with the
recurrence's own **floor** division. -/
noncomputable def recurrenceExponent (s : ℕ) : ℕ :=
  cubeThreshold s + (s / cubeThreshold s ^ 2 + 1) * Nat.clog 2 (s + 2)

/-- **The normalization, at the level of exponents.**  The recurrence's floor
exponent is at most the frozen ceiling one. -/
theorem recurrenceExponent_le_cubeExponent (s : ℕ) :
    recurrenceExponent s ≤ cubeExponent s := by
  have ht : 0 < cubeThreshold s := by
    have := two_le_cubeThreshold s
    omega
  have ht2 : 0 < cubeThreshold s ^ 2 := pow_pos ht 2
  have hceil : s / cubeThreshold s ^ 2
      ≤ (s + cubeThreshold s ^ 2 - 1) / cubeThreshold s ^ 2 :=
    Nat.div_le_div_right (by omega)
  simp only [recurrenceExponent, cubeExponent]
  exact Nat.add_le_add le_rfl (Nat.mul_le_mul (by omega) le_rfl)

/-- **The normalization the final assembly calls.**  A bound at the recurrence's own exponent,
with the per-layer multiplier `K` carried, is a bound at `cubeRootFactor`.

There is deliberately no `G` here.  The assembly's strong induction runs over
monoid *types* — it avoids a maximum over representatives, so no function
`ℕ → ℝ` is available — and what it needs from this file is `exponent_step` for
the induction and this lemma for the final normalization. -/
theorem pow_recurrenceExponent_le_cubeRootFactor {K s n : ℕ} (hs : 1 ≤ s) :
    ((s : ℝ) * cubeLog n) ^ (K * recurrenceExponent s) ≤ cubeRootFactor K s n := by
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hLn : (2 : ℝ) ≤ (cubeLog n : ℝ) := by exact_mod_cast two_le_cubeLog n
  have hB : (1 : ℝ) ≤ (s : ℝ) * cubeLog n :=
    le_trans (by norm_num) (mul_le_mul hs1 hLn (by norm_num) (by linarith))
  exact pow_le_pow_of_le_exponent hB
    (Nat.mul_le_mul le_rfl (recurrenceExponent_le_cubeExponent s))

/-- **The cube root with the multiplier carried.**  Leaving `K` open costs
nothing asymptotically, which is the whole reason it can be left open. -/
theorem cubeExponent_pow_le_mul {K s : ℕ} (hs : 1 ≤ s) :
    (K * cubeExponent s) ^ 3 ≤ 512 * K ^ 3 * (s * cubeLog s) := by
  calc (K * cubeExponent s) ^ 3 = K ^ 3 * cubeExponent s ^ 3 := by ring
    _ ≤ K ^ 3 * (512 * (s * cubeLog s)) :=
        Nat.mul_le_mul le_rfl (cubeExponent_pow_le hs)
    _ = 512 * K ^ 3 * (s * cubeLog s) := by ring

/-- **An abstract regression on the packaged form.**  This is *not* the assembly
interface — it needs a `G : ℕ → ℝ`, which the type-indexed induction cannot
build.  It is kept because it exercises the whole chain end to end at the
concrete base and layer count: per-layer multiplier `B ^ K` with
`B = s·L(n)`, threshold `t = cubeThreshold s`, and `Λ = ⌈log₂(s+2)⌉` layers per
peel. -/
theorem cubeRootFactor_of_recurrence {K s n : ℕ} (hs : 1 ≤ s) {G : ℕ → ℝ}
    (hrec : ∀ m : ℕ,
        G m ≤ (((s : ℝ) * cubeLog n) ^ K) ^ cubeThreshold s
        ∨ ∃ m', m' + cubeThreshold s ^ 2 ≤ m
            ∧ G m ≤ (((s : ℝ) * cubeLog n) ^ K) ^ Nat.clog 2 (s + 2) * G m') :
    G s ≤ cubeRootFactor K s n := by
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hLn : (2 : ℝ) ≤ (cubeLog n : ℝ) := by exact_mod_cast two_le_cubeLog n
  have hB : (1 : ℝ) ≤ (s : ℝ) * cubeLog n :=
    le_trans (by norm_num) (mul_le_mul hs1 hLn (by norm_num) (by linarith))
  have hBK : (1 : ℝ) ≤ ((s : ℝ) * cubeLog n) ^ K := one_le_pow_of_one_le hB K
  have ht : 0 < cubeThreshold s := by
    have := two_le_cubeThreshold s
    omega
  have hmain := le_pow_of_recurrence hBK ht hrec s
  rw [← pow_mul] at hmain
  exact le_trans hmain (pow_recurrenceExponent_le_cubeRootFactor hs)

end MonoidProduct
