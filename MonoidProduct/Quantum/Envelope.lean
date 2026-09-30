import MonoidProduct.Quantum.CubeRootApplications
import MonoidProduct.Quantum.DyckApplications
import MonoidProduct.Capped.RTrivial
import MonoidProduct.Capped.Breadth
import MonoidProduct.Width.Breadth
import QuantumQueryComplexity.Quantum.Plurality
import QuantumQueryComplexity.Promise.Post
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The worst-case aperiodic envelope (`monoid.tex`, `thm:aperiodic-envelope`,
`cor:aperiodic-envelope-transition`)

`aperiodicEnvelope N n = sup { Q_{1/3}(Prod_{M,n}) : M finite aperiodic, |M| ≤ N }`.

* `aperiodic_envelope_lower` — the lower half of `thm:aperiodic-envelope` with
  the in-house Dyck constant: for `(k+2)³ ≤ N`, even `n ≥ 4·8^ℓ` and
  `4 + 10ℓ ≤ k`, `7·√n·√2^ℓ/(2752√2) ≤ 𝒬_ap(N, n)`.  The witness is `DyckNF k`
  (`|DyckNF k| ≤ (k+2)³`), reached from the binary Dyck product through the
  injective letter relabelling (`dyck_qQuery_lower_total`).
* `aperiodic_envelope_lower_cbrt` — the `√n·2^{bN^{1/3}}` reading at
  `b = 1/20`, with `k = cubeDepth N` the largest `k` with `(k+2)³ ≤ N`.
* `aperiodic_envelope_linear` — `cor:aperiodic-envelope-transition`, second
  clause: for `n ≥ 2` and `N ≥ ⌊n/2⌋ + 1`, `(7/11008)·n ≤ 𝒬_ap(N, n) ≤ n`
  (witness: the capped counter `M_{⌊n/2⌋}` on binary inputs).
* `aperiodicEnvelope_le_length` — `𝒬_ap(N, n) ≤ n`.

* `aperiodicEnvelope_le_cubeRoot` — the cube-root upper bound in envelope
  form, via `cubeExponentMax` (`cubeExponent` itself is not monotone).

The `n^{1−ε}` clause of `cor:aperiodic-envelope-transition` is proved in-house
in `Quantum/DyckNearLinear.lean` (`dyckNL_aperiodicEnvelope_nearLinear`), and
`thm:dyck-lb` itself in `Quantum/DyckLanguageLower.lean`; neither depends on
ABIKPSSV20.
-/

namespace MonoidProduct
open QuantumQueryComplexity

/-! ## The envelope -/

/-- The values `Q_{1/3}(Prod_{M,n})` over finite aperiodic monoids of order at
most `N`. -/
def envelopeSet (N n : ℕ) : Set ℝ :=
  {q | ∃ (M : Type) (_ : Monoid M) (_ : Fintype M) (_ : DecidableEq M) (_ : IsAperiodicMonoid M),
      Fintype.card M ≤ N ∧
        q = (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ)}

/-- **The worst-case aperiodic envelope** `𝒬_ap(N, n)`. -/
noncomputable def aperiodicEnvelope (N n : ℕ) : ℝ := sSup (envelopeSet N n)

lemma envelopeSet_bddAbove (N n : ℕ) : BddAbove (envelopeSet N n) := by
  refine ⟨n, ?_⟩
  rintro q ⟨M, _, _, _, _, _, rfl⟩
  exact_mod_cast aperiodic_qQuery_upper_length

instance instIsAperiodicUnit : IsAperiodicMonoid Unit :=
  ⟨fun _ => ⟨1, one_pos, Subsingleton.elim _ _⟩⟩

lemma envelopeSet_nonempty {N : ℕ} (hN : 1 ≤ N) (n : ℕ) : (envelopeSet N n).Nonempty :=
  ⟨_, Unit, inferInstance, inferInstance, inferInstance, inferInstance, by simpa using hN, rfl⟩

lemma mem_envelopeSet {M : Type} [Monoid M] [Fintype M] [DecidableEq M]
    [IsAperiodicMonoid M] {N n : ℕ} (hM : Fintype.card M ≤ N) :
    (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ) ∈ envelopeSet N n := by
  refine ⟨M, ‹Monoid M›, ‹Fintype M›, ‹DecidableEq M›, ‹IsAperiodicMonoid M›, hM, ?_⟩
  rfl

/-- Every admissible monoid's query complexity is below the envelope. -/
theorem le_aperiodicEnvelope {M : Type} [Monoid M] [Fintype M] [DecidableEq M]
    [IsAperiodicMonoid M] {N n : ℕ} (hM : Fintype.card M ≤ N) :
    (qQuery (fun w : Fin n → M => wordProd (id : M → M) w) (1 / 3) : ℝ)
      ≤ aperiodicEnvelope N n := by
  apply le_csSup (envelopeSet_bddAbove N n)
  exact mem_envelopeSet hM

/-- **Reading everything**: `𝒬_ap(N, n) ≤ n`. -/
theorem aperiodicEnvelope_le_length {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    aperiodicEnvelope N n ≤ n := by
  refine csSup_le (envelopeSet_nonempty hN n) ?_
  rintro q ⟨M, _, _, _, _, _, rfl⟩
  exact_mod_cast aperiodic_qQuery_upper_length

/-! ## The Dyck witness -/

lemma dyckLetter_injective {k : ℕ} (hk : 1 ≤ k) : Function.Injective (dyckLetter k) := by
  intro x y h
  cases x <;> cases y <;> simp_all [dyckLetter, upT, downT]

/-- **The Dyck lower bound for the honest total product** over the alphabet
`DyckNF k`: the binary product is its restriction along an injective letter
relabelling. -/
theorem dyck_qQuery_lower_total {k ℓ n : ℕ} (hk1 : 1 ≤ k) (heven : Even n)
    (hfit : 4 * 8 ^ ℓ ≤ n) (hk : 4 + 10 * ℓ ≤ k) :
    7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (2752 * Real.sqrt 2)
      ≤ (qQuery (fun w : Fin n → DyckNF k => wordProd (id : DyckNF k → DyckNF k) w)
          (1 / 3) : ℝ) := by
  have : Nonempty (DyckNF k) := ⟨1⟩
  have hadv := dyckMonoid_product_lower_fixedBase ℓ n k heven hfit hk
  let read : (Fin n → Bool) → Fin n → DyckNF k := fun x j => dyckLetter k (x j)
  have hread : Function.Injective read := fun x y h =>
    funext fun j => dyckLetter_injective hk1 (congrFun h j)
  have hcomp : advPMOn read (dyckProduct k n) = advPM (dyckProduct k n) :=
    advPMOn_comp_injective (dyckLetter_injective hk1)
      (id : (Fin n → Bool) → Fin n → Bool) (dyckProduct k n)
  have hpar := mul_advPMOn_le_qQueryOn_third_finiteOutput (read := read) (f := dyckProduct k n)
    (fun x y hxy => by rw [hread hxy])
  have hQ := qQueryOn_comp_read_le_qQuery read
    (fun w : Fin n → DyckNF k => wordProd (id : DyckNF k → DyckNF k) w)
    (queryCounts_nonempty (read := (id : (Fin n → DyckNF k) → Fin n → DyckNF k))
      (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3))
  change qQueryOn read (dyckProduct k n) (1 / 3) ≤ _ at hQ
  have h2 : Real.sqrt n * Real.sqrt 2 ^ ℓ / (2 * Real.sqrt 2)
      ≤ advPM (dyckProduct k n) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)]
    nlinarith [hadv]
  calc 7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (2752 * Real.sqrt 2)
      = (7 / 1376 : ℝ) * (Real.sqrt n * Real.sqrt 2 ^ ℓ / (2 * Real.sqrt 2)) := by ring
    _ ≤ (7 / 1376 : ℝ) * advPM (dyckProduct k n) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = (7 / 1376 : ℝ) * advPMOn read (dyckProduct k n) := by rw [hcomp]
    _ ≤ (qQueryOn read (dyckProduct k n) (1 / 3) : ℝ) := hpar
    _ ≤ _ := by exact_mod_cast hQ

/-- **`thm:aperiodic-envelope`, lower half, parametric form**: for
`(k+2)³ ≤ N`, even `n ≥ 4·8^ℓ` and `4 + 10ℓ ≤ k`,
`7·√n·√2^ℓ/(2752√2) ≤ 𝒬_ap(N, n)`. -/
theorem aperiodic_envelope_lower {k ℓ n N : ℕ} (heven : Even n) (hfit : 4 * 8 ^ ℓ ≤ n)
    (hk : 4 + 10 * ℓ ≤ k) (hN : (k + 2) ^ 3 ≤ N) :
    7 * (Real.sqrt n * Real.sqrt 2 ^ ℓ) / (2752 * Real.sqrt 2) ≤ aperiodicEnvelope N n :=
  (dyck_qQuery_lower_total (by omega) heven hfit hk).trans
    (le_aperiodicEnvelope ((card_dyckNF_le_cube k).trans hN))

/-! ## The cube-root reading -/

/-- The largest `k` with `(k+2)³ ≤ N`. -/
def cubeDepth (N : ℕ) : ℕ := Nat.findGreatest (fun k => (k + 2) ^ 3 ≤ N) N

/-- The Dyck level used at order `N`: `ℓ(N) = ⌊(cubeDepth N − 4)/10⌋`. -/
def envLevel (N : ℕ) : ℕ := (cubeDepth N - 4) / 10

lemma cubeDepth_spec {N : ℕ} (hN : 8 ≤ N) : (cubeDepth N + 2) ^ 3 ≤ N :=
  Nat.findGreatest_spec (P := fun k => (k + 2) ^ 3 ≤ N) (Nat.zero_le N) (by simpa using hN)

lemma lt_cubeDepth_succ_cube (N : ℕ) : N < (cubeDepth N + 3) ^ 3 := by
  by_contra h
  have h2 : (cubeDepth N + 3) ^ 3 ≤ N := Nat.le_of_not_lt h
  have hle : cubeDepth N + 1 ≤ N := by
    have : (cubeDepth N + 1) ≤ (cubeDepth N + 3) ^ 3 := by
      calc cubeDepth N + 1 ≤ cubeDepth N + 3 := by omega
        _ ≤ (cubeDepth N + 3) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  exact Nat.findGreatest_is_greatest (P := fun k => (k + 2) ^ 3 ≤ N) (Nat.lt_succ_self _) hle h2

lemma four_le_cubeDepth {N : ℕ} (hN : 216 ≤ N) : 4 ≤ cubeDepth N :=
  Nat.le_findGreatest (P := fun k => (k + 2) ^ 3 ≤ N) (by omega) (by norm_num; omega)

/-- **`thm:aperiodic-envelope`, lower half, at `k = cubeDepth N`**: for `N ≥ 216`
and even `n ≥ 4·8^{ℓ(N)}`, `7·√n·√2^{ℓ(N)}/(2752√2) ≤ 𝒬_ap(N, n)`. -/
theorem aperiodic_envelope_lower_cubeDepth {n N : ℕ} (hN : 216 ≤ N) (heven : Even n)
    (hfit : 4 * 8 ^ envLevel N ≤ n) :
    7 * (Real.sqrt n * Real.sqrt 2 ^ envLevel N) / (2752 * Real.sqrt 2)
      ≤ aperiodicEnvelope N n :=
  aperiodic_envelope_lower heven hfit
    (by have := four_le_cubeDepth hN; unfold envLevel; omega) (cubeDepth_spec (by omega))

/-- `√2^{ℓ(N)} ≥ 2^{(N^{1/3} − 16)/20}`: the exponent constant `b = 1/20`. -/
theorem two_rpow_le_sqrt_two_pow_envLevel (N : ℕ) :
    (2 : ℝ) ^ (((N : ℝ) ^ ((1 : ℝ) / 3) - 16) / 20) ≤ Real.sqrt 2 ^ envLevel N := by
  have hcb : (N : ℝ) ^ ((1 : ℝ) / 3) < cubeDepth N + 3 := by
    have h := lt_cubeDepth_succ_cube N
    have h' : (N : ℝ) < ((cubeDepth N + 3 : ℕ) : ℝ) ^ (3 : ℕ) := by exact_mod_cast h
    have hpos : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    calc (N : ℝ) ^ ((1 : ℝ) / 3)
        < (((cubeDepth N + 3 : ℕ) : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_lt_rpow hpos h' (by norm_num)
      _ = ((cubeDepth N + 3 : ℕ) : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
          norm_num
      _ = cubeDepth N + 3 := by push_cast; ring
  have hℓ : (cubeDepth N : ℝ) ≤ 10 * envLevel N + 13 := by
    have : cubeDepth N ≤ 10 * envLevel N + 13 := by unfold envLevel; omega
    exact_mod_cast this
  have hexp : ((N : ℝ) ^ ((1 : ℝ) / 3) - 16) / 20 ≤ (envLevel N : ℝ) / 2 := by linarith
  calc (2 : ℝ) ^ (((N : ℝ) ^ ((1 : ℝ) / 3) - 16) / 20)
      ≤ (2 : ℝ) ^ ((envLevel N : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = Real.sqrt 2 ^ envLevel N := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring

/-- **`thm:aperiodic-envelope`, lower half, paper form**: for `N ≥ 216` and even
`n ≥ 4·8^{ℓ(N)}`,

  `(7 / (2752·√2·2^{4/5})) · √n · 2^{N^{1/3}/20} ≤ 𝒬_ap(N, n)`,

the fixed exponential `2^{bN^{1/3}}` at `b = 1/20`. -/
theorem aperiodic_envelope_lower_cbrt {n N : ℕ} (hN : 216 ≤ N) (heven : Even n)
    (hfit : 4 * 8 ^ envLevel N ≤ n) :
    7 / (2752 * Real.sqrt 2 * (2 : ℝ) ^ ((4 : ℝ) / 5)) * Real.sqrt n
        * (2 : ℝ) ^ ((N : ℝ) ^ ((1 : ℝ) / 3) / 20)
      ≤ aperiodicEnvelope N n := by
  have H := aperiodic_envelope_lower_cubeDepth hN heven hfit
  have hAB := two_rpow_le_sqrt_two_pow_envLevel N
  have hsplit : (2 : ℝ) ^ ((N : ℝ) ^ ((1 : ℝ) / 3) / 20)
      = (2 : ℝ) ^ (((N : ℝ) ^ ((1 : ℝ) / 3) - 16) / 20) * (2 : ℝ) ^ ((4 : ℝ) / 5) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hc : (0 : ℝ) < 2752 * Real.sqrt 2 := by positivity
  have h45 : (0 : ℝ) < (2 : ℝ) ^ ((4 : ℝ) / 5) := by positivity
  have hn0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  calc 7 / (2752 * Real.sqrt 2 * (2 : ℝ) ^ ((4 : ℝ) / 5)) * Real.sqrt n
        * (2 : ℝ) ^ ((N : ℝ) ^ ((1 : ℝ) / 3) / 20)
      = 7 * (Real.sqrt n * (2 : ℝ) ^ (((N : ℝ) ^ ((1 : ℝ) / 3) - 16) / 20))
          / (2752 * Real.sqrt 2) := by
        rw [hsplit]
        field_simp
    _ ≤ 7 * (Real.sqrt n * Real.sqrt 2 ^ envLevel N) / (2752 * Real.sqrt 2) := by
        rw [div_le_div_iff_of_pos_right hc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAB hn0) (by norm_num)
    _ ≤ aperiodicEnvelope N n := H

/-! ## The capped-counter witness and the `Θ(n)` clause -/

lemma cappedBin_injective {K : ℕ} (hK : 0 < K) :
    Function.Injective (fun b : Bool => if b then Capped.gen else (1 : Capped K)) := by
  intro x y h
  have hv := congrArg Capped.val h
  cases x <;> cases y <;>
    simp only [Bool.false_eq_true, if_false, if_true, Capped.one_val, gen_val_of_pos hK] at hv <;>
    first | rfl | omega

/-- **The capped-counter lower bound for the honest total product** over the
alphabet `M_K`: the binary product is its restriction along the injective
relabelling `0 ↦ 1`, `1 ↦ 1̂`. -/
theorem capped_qQuery_lower_total {K n : ℕ} (hK : 0 < K) [Nonempty (Fin n)] :
    (7 / 1376 : ℝ) * (Real.sqrt ((n : ℝ) * ((min n K : ℕ) : ℝ)) / 4)
      ≤ (qQuery (fun w : Fin n → Capped K => wordProd (id : Capped K → Capped K) w)
          (1 / 3) : ℝ) := by
  have : Nonempty (Capped K) := ⟨1⟩
  let φ : Bool → Capped K := fun b => if b then Capped.gen else 1
  let read : (Fin n → Bool) → Fin n → Capped K := fun x j => φ (x j)
  let f : (Fin n → Bool) → Capped K :=
    fun x => ∏ i, (if x i then Capped.gen else (1 : Capped K))
  have hread : Function.Injective read := fun x y h =>
    funext fun j => cappedBin_injective hK (congrFun h j)
  have hcomp : advPMOn read f = advPM f :=
    advPMOn_comp_injective (cappedBin_injective hK) (id : (Fin n → Bool) → Fin n → Bool) f
  have hpar := mul_advPMOn_le_qQueryOn_third_finiteOutput (read := read) (f := f)
    (fun x y hxy => by rw [hread hxy])
  have hQ := qQueryOn_comp_read_le_qQuery read
    (fun w : Fin n → Capped K => wordProd (id : Capped K → Capped K) w)
    (queryCounts_nonempty (read := (id : (Fin n → Capped K) → Fin n → Capped K))
      (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3))
  have hf : (fun x => wordProd (id : Capped K → Capped K) (read x)) = f := by
    funext x
    exact wordProd_eq_prod φ x
  rw [hf] at hQ
  calc (7 / 1376 : ℝ) * (Real.sqrt ((n : ℝ) * ((min n K : ℕ) : ℝ)) / 4)
      ≤ (7 / 1376 : ℝ) * advPM f :=
        mul_le_mul_of_nonneg_left (Capped.sqrt_le_advPM_binary' hK) (by norm_num)
    _ = (7 / 1376 : ℝ) * advPMOn read f := by rw [hcomp]
    _ ≤ (qQueryOn read f (1 / 3) : ℝ) := hpar
    _ ≤ _ := by exact_mod_cast hQ

/-- **`cor:aperiodic-envelope-transition`, second clause**: for `n ≥ 2` and
`N ≥ ⌊n/2⌋ + 1`, `(7/11008)·n ≤ 𝒬_ap(N, n) ≤ n`; the witness is the capped
counter `M_{⌊n/2⌋}` of order `⌊n/2⌋ + 1`. -/
theorem aperiodic_envelope_linear {n N : ℕ} (hn : 2 ≤ n) (hN : n / 2 + 1 ≤ N) :
    (7 / 11008 : ℝ) * n ≤ aperiodicEnvelope N n ∧ aperiodicEnvelope N n ≤ n := by
  refine ⟨?_, aperiodicEnvelope_le_length (by omega) n⟩
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hK : 0 < n / 2 := by omega
  have hcard : Fintype.card (Capped (n / 2)) ≤ N := by
    rw [show Fintype.card (Capped (n / 2)) = n / 2 + 1 from Fintype.card_fin _]
    exact hN
  refine le_trans ?_ ((capped_qQuery_lower_total hK).trans (le_aperiodicEnvelope hcard))
  have hmin : min n (n / 2) = n / 2 := min_eq_right (Nat.div_le_self n 2)
  rw [hmin]
  have h1 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : n ≤ 2 * (n / 2) + 1)
  have h2 : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hK
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : ((n : ℝ) / 2) ^ 2 ≤ (n : ℝ) * ((n / 2 : ℕ) : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ n)]
  have hsqrt : (n : ℝ) / 2 ≤ Real.sqrt ((n : ℝ) * ((n / 2 : ℕ) : ℝ)) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)]
    exact Real.sqrt_le_sqrt hsq
  calc (7 / 11008 : ℝ) * n = (7 / 1376 : ℝ) * ((n : ℝ) / 2 / 4) := by ring
    _ ≤ (7 / 1376 : ℝ) * (Real.sqrt ((n : ℝ) * ((n / 2 : ℕ) : ℝ)) / 4) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsqrt (by norm_num)) (by norm_num)

end MonoidProduct

/-! ## The cube-root upper bound in envelope form -/

namespace MonoidProduct

open QuantumQueryComplexity

/-- The running maximum of the cube-root exponent over orders `≤ N`.  (`cubeExponent`
itself is not monotone: the ceiling `⌈s / T(s)²⌉` drops when the threshold `T(s)`
jumps, e.g. at `s = 112`.) -/
noncomputable def cubeExponentMax (N : ℕ) : ℕ := (Finset.range (N + 1)).sup cubeExponent

lemma cubeExponent_le_cubeExponentMax {s N : ℕ} (h : s ≤ N) :
    cubeExponent s ≤ cubeExponentMax N :=
  Finset.le_sup (f := cubeExponent) (Finset.mem_range.2 (by omega))

/-- The envelope dual cost `√n·(N·L(n))^{256·cubeExponentMax N}`, monotone in `N`. -/
noncomputable def cubeRootEnvelopeCost (N n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * ((N : ℝ) * cubeLog n) ^ (256 * cubeExponentMax N)

lemma cubeRootEnvelopeCost_nonneg (N n : ℕ) : 0 ≤ cubeRootEnvelopeCost N n := by
  unfold cubeRootEnvelopeCost; positivity

/-- Every order `1 ≤ s ≤ N` is dominated by the envelope cost. -/
lemma cubeRootDualCost_le_envelopeCost {s N n : ℕ} (hs : 1 ≤ s) (hsN : s ≤ N) :
    cubeRootDualCost 256 s n ≤ cubeRootEnvelopeCost N n := by
  unfold cubeRootDualCost cubeRootFactor cubeRootEnvelopeCost
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hL : (2 : ℝ) ≤ cubeLog n := by exact_mod_cast two_le_cubeLog n
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsN' : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have h1 : (1 : ℝ) ≤ (s : ℝ) * cubeLog n := by nlinarith
  have hbase : (s : ℝ) * cubeLog n ≤ (N : ℝ) * cubeLog n :=
    mul_le_mul_of_nonneg_right hsN' (by linarith)
  calc ((s : ℝ) * cubeLog n) ^ (256 * cubeExponent s)
      ≤ ((N : ℝ) * cubeLog n) ^ (256 * cubeExponent s) :=
        pow_le_pow_left₀ (by linarith) hbase _
    _ ≤ ((N : ℝ) * cubeLog n) ^ (256 * cubeExponentMax N) :=
        pow_le_pow_right₀ (h1.trans hbase)
          (by have := cubeExponent_le_cubeExponentMax hsN; omega)

/-- **`thm:aperiodic-envelope`, upper half, in the Lean vocabulary**:
`𝒬_ap(N, n) ≤ min{n, 8192·(1 + √n·(N·L(n))^{256·cubeExponentMax N})}`. -/
theorem aperiodicEnvelope_le_cubeRoot {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    aperiodicEnvelope N n
      ≤ min (n : ℝ) (uniformExtractionConstant * (1 + cubeRootEnvelopeCost N n)) := by
  refine csSup_le (envelopeSet_nonempty hN n) ?_
  rintro q ⟨M, _, _, _, _, hM, rfl⟩
  refine (aperiodic_qQuery_le_min (M := M) (n := n)).trans (min_le_min le_rfl ?_)
  have hs : 1 ≤ Fintype.card M := Fintype.card_pos_iff.2 ⟨1⟩
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by unfold uniformExtractionConstant; norm_num)
  exact cubeRootDualCost_le_envelopeCost hs hM

end MonoidProduct
