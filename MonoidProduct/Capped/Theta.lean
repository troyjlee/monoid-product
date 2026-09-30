import MonoidProduct.Capped.Width
import MonoidProduct.Capped.Lower
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Capped-counter products: the `Θ(√(n·min{n,kr}))` theorem

The numeric instantiation of the parametric lower bound
(`cubeTheta_le_advPM_prodFun`) and its packaging with the width upper bound
(`advPM_prodFun_le_capped`) into `thm:capped-counter-product`:

  `(1/4)·√(n·min{n, k·r}) ≤ ADV±(Prod_{M_{k,r},n}) ≤ 16·√(n·min{n, k·r})`.

Instantiation: `d = min r n` blocks.  A size-`d` subset of the coordinates
is used (as a subtype `ρ'`), and the conclusion transfers to the full
monoid along the coordinate projection, which is output post-processing
(`advPM_comp_le`).  The block map `x ↦ min (x/q) (d−1)` at `q = ⌊n/d⌋`
needs no exact balancing: every fiber has size ≥ `q`, and oversized fibers
only increase the bound.  The uniform layer choice is
`s = min k ((q+1)/2)`, and the constant chase
`4·s(q−s+1) ≥ q·min(k,q)`, `2dq ≥ n`, `2d·min(k,q) ≥ min(n,kr)` yields the
`1/4`.
-/

namespace MonoidProduct
open QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- **Output post-processing can only lower the adversary bound**: every
adversary matrix for `g ∘ f` is one for `f`. -/
lemma advPM_comp_le {O O' : Type*} (g : O → O') (f : (ι → σ) → O) :
    advPM (fun x => g (f x)) ≤ advPM f :=
  advPM_le fun Γ h1 h2 =>
    le_advPM ⟨h1.1, fun x y hxy => h1.2 x y (congrArg g hxy)⟩ h2

/-- The leftover-tolerant block map: `x ↦ min (x/q) (d−1)`. -/
def thetaBlk (n d q : ℕ) (hd : 0 < d) (x : Fin n) : Fin d :=
  ⟨min ((x : ℕ) / q) (d - 1), by omega⟩

lemma thetaBlk_apply {n d q : ℕ} (hd : 0 < d) (hq0 : 0 < q) {c : ℕ}
    (hc : c < d) (j : Fin q) (hbound : c * q + (j : ℕ) < n) :
    thetaBlk n d q hd ⟨c * q + (j : ℕ), hbound⟩ = ⟨c, hc⟩ := by
  apply Fin.ext
  show min ((c * q + (j : ℕ)) / q) (d - 1) = c
  have hdiv : (c * q + (j : ℕ)) / q = c := by
    rw [Nat.mul_comm c q, Nat.mul_add_div hq0, Nat.div_eq_of_lt j.isLt,
      Nat.add_zero]
  rw [hdiv]
  omega

section Omega

variable {k : ℕ} {m : σ → ρ → Capped k} {s0 : σ} {e : ρ → σ}

/-- **The `Ω(√(n·min{n,kr}))` lower bound** (`thm:capped-counter-product`,
lower half, numeric form): with explicit constant `1/4`. -/
theorem sqrt_le_advPM_prodFun [Nonempty ι] [Nonempty ρ] (hk : 0 < k)
    (hm0 : m s0 = 1) (hme : ∀ j, m (e j) = cappedUnit k j)
    (hs0e : ∀ j, s0 ≠ e j) :
    Real.sqrt ((Fintype.card ι : ℝ)
        * (min (Fintype.card ι) (k * Fintype.card ρ) : ℕ)) / 4
      ≤ advPM (fun x : ι → σ => ∏ i, m (x i)) := by
  classical
  set n := Fintype.card ι with hn
  set r := Fintype.card ρ with hr
  have hn0 : 0 < n := Fintype.card_pos
  have hr0 : 0 < r := Fintype.card_pos
  set d := min r n with hd
  have hd0 : 0 < d := lt_min_iff.mpr ⟨hr0, hn0⟩
  set q := n / d with hq
  have hq0 : 0 < q := Nat.div_pos (min_le_right r n) hd0
  -- the used coordinates
  obtain ⟨D, -, hD⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset ρ)) (n := d)
    (by rw [Finset.card_univ]; exact min_le_left r n)
  have hcardρ' : Fintype.card {c // c ∈ D} = d := by
    rw [Fintype.card_coe, hD]
  let eρ : {c // c ∈ D} ≃ Fin d := Fintype.equivFinOfCardEq hcardρ'
  let eι : ι ≃ Fin n := Fintype.equivFin ι
  set blk : ι → {c // c ∈ D} :=
    fun i => eρ.symm (thetaBlk n d q hd0 (eι i)) with hblk
  have hdqn : d * q ≤ n := by
    have h := Nat.div_mul_le_self n d
    calc d * q = q * d := Nat.mul_comm d q
      _ ≤ n := h
  -- every fiber has at least q elements
  have hfiber : ∀ c' : {c // c ∈ D}, q ≤ blkSize blk c' := by
    intro c'
    have hcd : ((eρ c' : Fin d) : ℕ) < d := (eρ c').isLt
    have hbound : ∀ j : Fin q, ((eρ c' : Fin d) : ℕ) * q + (j : ℕ) < n := by
      intro j
      have h1 : (((eρ c' : Fin d) : ℕ) + 1) * q ≤ d * q :=
        Nat.mul_le_mul_right q hcd
      have h2 : (((eρ c' : Fin d) : ℕ) + 1) * q
          = ((eρ c' : Fin d) : ℕ) * q + q := by ring
      have := j.isLt
      omega
    have hmap : ∀ j : Fin q,
        blk (eι.symm ⟨((eρ c' : Fin d) : ℕ) * q + (j : ℕ), hbound j⟩)
          = c' := by
      intro j
      rw [hblk]
      show eρ.symm (thetaBlk n d q hd0
        (eι (eι.symm ⟨((eρ c' : Fin d) : ℕ) * q + (j : ℕ), hbound j⟩)))
        = c'
      rw [Equiv.apply_symm_apply,
        thetaBlk_apply hd0 hq0 hcd j (hbound j)]
      have : (⟨((eρ c' : Fin d) : ℕ), hcd⟩ : Fin d) = eρ c' :=
        Fin.ext rfl
      rw [this, Equiv.symm_apply_apply]
    have hinj : Set.InjOn
        (fun j : Fin q =>
          eι.symm ⟨((eρ c' : Fin d) : ℕ) * q + (j : ℕ), hbound j⟩)
        ↑(Finset.univ : Finset (Fin q)) := by
      intro j _ j' _ hjj
      have h1 := eι.symm.injective hjj
      have h2 : ((eρ c' : Fin d) : ℕ) * q + (j : ℕ)
          = ((eρ c' : Fin d) : ℕ) * q + (j' : ℕ) := by
        have := congrArg Fin.val h1
        exact this
      exact Fin.ext (by omega)
    have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin q)),
        eι.symm ⟨((eρ c' : Fin d) : ℕ) * q + (j : ℕ), hbound j⟩
          ∈ Finset.univ.filter fun i => blk i = c' := by
      intro j _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmap j⟩
    have h := Finset.card_le_card_of_injOn _ hmaps hinj
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  -- the restricted letters
  set m' : σ → {c // c ∈ D} → Capped k := fun a c' => m a c'.val with hm'
  have hm0' : m' s0 = 1 := by
    funext c'
    rw [hm']
    show m s0 c'.val = 1
    rw [hm0]
    rfl
  have hme' : ∀ j' : {c // c ∈ D}, m' (e j'.val) = cappedUnit k j' := by
    intro j'
    funext c'
    rw [hm']
    show m (e j'.val) c'.val = cappedUnit k j' c'
    rw [hme j'.val, cappedUnit, cappedUnit]
    exact if_congr Subtype.ext_iff.symm rfl rfl
  have hs0e' : ∀ j' : {c // c ∈ D}, s0 ≠ e j'.val := fun j' => hs0e j'.val
  -- the uniform layer
  set sc := min k ((q + 1) / 2) with hsc
  have hsc1 : 1 ≤ sc := by omega
  have hsck : sc ≤ k := min_le_left _ _
  have hscq : sc ≤ q := by omega
  -- the parametric bound
  have hpar := cubeTheta_le_advPM_prodFun (blk := blk)
    (s := fun _ => sc) (m := m') (s0 := s0)
    (e := fun j' : {c // c ∈ D} => e j'.val) hk hm0'
    (fun j' => hme' j') hs0e' (fun _ => hsc1) (fun _ => hsck)
    (fun c' => hscq.trans (hfiber c'))
  -- transfer along the coordinate projection
  have hcomp : advPM (fun x : ι → σ => ∏ i, m' (x i))
      ≤ advPM (fun x : ι → σ => ∏ i, m (x i)) := by
    have heq : (fun x : ι → σ => ∏ i, m' (x i))
        = fun x : ι → σ =>
            (fun g : ρ → Capped k => fun c' : {c // c ∈ D} => g c'.val)
              (∏ i, m (x i)) := by
      funext x
      funext c'
      calc (∏ i, m' (x i)) c'
          = ∏ i, m' (x i) c' :=
            map_prod (Pi.evalMonoidHom
              (fun _ : {c // c ∈ D} => Capped k) c') _ _
        _ = ∏ i, m (x i) c'.val := rfl
        _ = (∏ i, m (x i)) c'.val :=
            (map_prod (Pi.evalMonoidHom (fun _ : ρ => Capped k)
              c'.val) _ _).symm
    rw [heq]
    exact advPM_comp_le
      (fun g : ρ → Capped k => fun c' : {c // c ∈ D} => g c'.val)
      (fun x : ι → σ => ∏ i, m (x i))
  -- the theta sum dominates d copies of the smallest block term
  have hunfold : cubeTheta blk (fun _ : {c // c ∈ D} => sc)
      = ∑ c' : {c // c ∈ D}, Real.sqrt ((sc : ℝ)
          * ((blkSize blk c' - sc + 1 : ℕ) : ℝ)) := rfl
  have hterm : ∀ c' : {c // c ∈ D},
      Real.sqrt ((sc : ℝ) * ((q - sc + 1 : ℕ) : ℝ))
        ≤ Real.sqrt ((sc : ℝ) * ((blkSize blk c' - sc + 1 : ℕ) : ℝ)) := by
    intro c'
    apply Real.sqrt_le_sqrt
    have h1 : q - sc + 1 ≤ blkSize blk c' - sc + 1 := by
      have := hfiber c'
      omega
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h1)
      (Nat.cast_nonneg _)
  have hθ : (d : ℝ) * Real.sqrt ((sc : ℝ) * ((q - sc + 1 : ℕ) : ℝ))
      ≤ cubeTheta blk (fun _ : {c // c ∈ D} => sc) := by
    rw [hunfold]
    have h := Finset.card_nsmul_le_sum
      (Finset.univ : Finset {c // c ∈ D})
      (fun c' => Real.sqrt ((sc : ℝ)
        * ((blkSize blk c' - sc + 1 : ℕ) : ℝ)))
      (Real.sqrt ((sc : ℝ) * ((q - sc + 1 : ℕ) : ℝ)))
      (fun c' _ => hterm c')
    rwa [Finset.card_univ, hcardρ', nsmul_eq_mul] at h
  -- ℕ arithmetic
  have hF1 : min k q * q ≤ 4 * (sc * (q - sc + 1)) := by
    have a1 : min k q ≤ 2 * sc := by omega
    have a2 : q ≤ 2 * (q - sc + 1) := by omega
    have h := Nat.mul_le_mul a1 a2
    have hexp : 2 * sc * (2 * (q - sc + 1)) = 4 * (sc * (q - sc + 1)) := by
      ring
    omega
  have hF2 : n ≤ 2 * (d * q) := by
    have hdm : d * q + n % d = n := by
      rw [hq]
      exact Nat.div_add_mod n d
    have hmod := Nat.mod_lt n hd0
    have hdq : d ≤ d * q := Nat.le_mul_of_pos_right d hq0
    omega
  have hF3 : min n (k * r) ≤ 2 * (d * min k q) := by
    by_cases hqk : q ≤ k
    · have hmin : min k q = q := min_eq_right hqk
      rw [hmin]
      omega
    · push_neg at hqk
      have hmin : min k q = k := min_eq_left hqk.le
      rw [hmin]
      by_cases hrn : r ≤ n
      · have hdr : d = r := min_eq_left hrn
        have hcomm : k * r = r * k := Nat.mul_comm k r
        rw [hdr]
        omega
      · push_neg at hrn
        have hdn : d = n := min_eq_right hrn.le
        have hnk : n ≤ n * k := Nat.le_mul_of_pos_right n hk
        rw [hdn]
        omega
  -- the real chain
  have h1 : ((n : ℝ)) * ((min n (k * r) : ℕ) : ℝ)
      ≤ (2 * ((d : ℝ) * q)) * (2 * ((d : ℝ) * (min k q : ℕ))) := by
    have h := Nat.mul_le_mul hF2 hF3
    calc ((n : ℝ)) * ((min n (k * r) : ℕ) : ℝ)
        = ((n * min n (k * r) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * (d * q) * (2 * (d * min k q)) : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = (2 * ((d : ℝ) * q)) * (2 * ((d : ℝ) * (min k q : ℕ))) := by
          push_cast; ring
  have h3 : ((min k q : ℕ) : ℝ) * (q : ℝ)
      ≤ 4 * ((sc * (q - sc + 1) : ℕ) : ℝ) := by
    calc ((min k q : ℕ) : ℝ) * (q : ℝ)
        = ((min k q * q : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((4 * (sc * (q - sc + 1)) : ℕ) : ℝ) := by exact_mod_cast hF1
      _ = 4 * ((sc * (q - sc + 1) : ℕ) : ℝ) := by push_cast; ring
  set X : ℝ := ((sc * (q - sc + 1) : ℕ) : ℝ) with hX
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have h4 : ((n : ℝ)) * ((min n (k * r) : ℕ) : ℝ)
      ≤ (4 * (d : ℝ)) ^ 2 * X := by
    have h5 : (2 * ((d : ℝ) * q)) * (2 * ((d : ℝ) * (min k q : ℕ)))
        = 4 * (d : ℝ) ^ 2 * (((min k q : ℕ) : ℝ) * (q : ℝ)) := by ring
    have h6 : 4 * (d : ℝ) ^ 2 * (((min k q : ℕ) : ℝ) * (q : ℝ))
        ≤ 4 * (d : ℝ) ^ 2 * (4 * X) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    calc ((n : ℝ)) * ((min n (k * r) : ℕ) : ℝ)
        ≤ (2 * ((d : ℝ) * q)) * (2 * ((d : ℝ) * (min k q : ℕ))) := h1
      _ = 4 * (d : ℝ) ^ 2 * (((min k q : ℕ) : ℝ) * (q : ℝ)) := h5
      _ ≤ 4 * (d : ℝ) ^ 2 * (4 * X) := h6
      _ = (4 * (d : ℝ)) ^ 2 * X := by ring
  have h7 : Real.sqrt ((n : ℝ) * ((min n (k * r) : ℕ) : ℝ))
      ≤ 4 * (d : ℝ) * Real.sqrt X := by
    calc Real.sqrt ((n : ℝ) * ((min n (k * r) : ℕ) : ℝ))
        ≤ Real.sqrt ((4 * (d : ℝ)) ^ 2 * X) := Real.sqrt_le_sqrt h4
      _ = 4 * (d : ℝ) * Real.sqrt X := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- X is the block term
  have hXsqrt : Real.sqrt X
      = Real.sqrt ((sc : ℝ) * ((q - sc + 1 : ℕ) : ℝ)) := by
    rw [hX]
    congr 1
    push_cast
    ring
  calc Real.sqrt ((n : ℝ) * ((min n (k * r) : ℕ) : ℝ)) / 4
      ≤ (d : ℝ) * Real.sqrt X := by linarith [h7]
    _ = (d : ℝ) * Real.sqrt ((sc : ℝ) * ((q - sc + 1 : ℕ) : ℝ)) := by
        rw [hXsqrt]
    _ ≤ cubeTheta blk (fun _ : {c // c ∈ D} => sc) := hθ
    _ ≤ advPM (fun x : ι → σ => ∏ i, m' (x i)) := hpar
    _ ≤ advPM (fun x : ι → σ => ∏ i, m (x i)) := hcomp

end Omega

/-! ## The capped-counter theorem -/

/-- **The capped-counter theorem** (`thm:capped-counter-product`): for the
canonical product problem over `M_{k,r} = Capped k ^ ρ`,

  `(1/4)·√(n·min{n,kr}) ≤ ADV± ≤ 16·√(n·min{n,kr})`. -/
theorem advPM_cappedProd_sandwich [Nonempty ι] [Nonempty ρ] {k : ℕ}
    (hk : 0 < k) :
    Real.sqrt ((Fintype.card ι : ℝ)
        * (min (Fintype.card ι) (k * Fintype.card ρ) : ℕ)) / 4
      ≤ advPM (fun x : ι → ρ → Capped k => ∏ i, x i)
    ∧ advPM (fun x : ι → ρ → Capped k => ∏ i, x i)
      ≤ 16 * Real.sqrt ((Fintype.card ι : ℝ)
          * (min (Fintype.card ι) (k * Fintype.card ρ) : ℕ)) := by
  constructor
  · refine sqrt_le_advPM_prodFun (m := fun a => a) (s0 := 1)
      (e := cappedUnit k) hk rfl (fun j => rfl) ?_
    intro j h
    have hval := congrArg (fun g : ρ → Capped k => (g j).val) h
    have h1 : ((1 : ρ → Capped k) j).val = 0 := rfl
    have h2 : ((cappedUnit k j) j).val = min 1 k := by
      rw [cappedUnit, if_pos rfl]
      rfl
    rw [h1, h2] at hval
    omega
  · have h := advPM_prodFun_le_capped (ι := ι) (ρ := ρ) hk
      (fun a : ρ → Capped k => a)
    rwa [Nat.mul_comm (Fintype.card ρ) k] at h

end MonoidProduct
