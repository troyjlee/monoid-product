import MonoidProduct.Aperiodic.CubeRoot.Rees
import QuantumQueryComplexity.Adaptive
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# First entry into the apex ideal by geometric boundary search

What the geometric boundary search halves is the **gap
minus one**, `hi - lo - 1`; the queried block length does not halve, but is
dominated by that envelope at every level.  So the *envelope* costs sum as
`√n + √(n/2) + √(n/4) + ⋯`, which is `O(√n)` — where a threshold search over
`⌈log₂ n⌉` full-width tests would give `√n log n`.

The four deliverables, in order:

* `hasDual_blockProj` — **the query**: the exact quotient product of a block,
  priced by the supplied contract for the quotient's word product.  Freezing
  the coordinates outside the block is free, as everywhere else here;
* `sum_sqrt_halving` — **the geometric sum**, at constant `4`.  The pattern is
  `LDS/OuterCost.lean`'s but the lemma is not: that file's summation is tied to
  its slot indexing, so this is proved locally.  The proof is a shift
  induction rather than a closed form, which keeps `√2` out of it entirely:
  one level contributes `√(b 0)` and the rest is the same statement for the
  shifted sequence, whose head is at most `b 0 / 2`, and
  `√(b 0 / 2) ≤ (3/4)·√(b 0)` closes it at `1 + 3 = 4`;
* `hasDual_trace` — **the finite padded trace and its dual**, at `4D√n`, by a
  local variable-cost induction (`hasDual_preTrans`).  The trace is **total**:
  it is built for every word, and the zero-product promise does not appear;
* `conf_horizon_spec` — **what it means**: the promise occurs only in the
  semantic section, of which this is the sole public endpoint, and it holds at
  every `n` (at `n = 0` the promise is self-contradictory).  Then
  `hasDual_traceLetter` — the crossing-letter joint, at `4D√n + 2`; that one
  does need `0 < n`, there being no letter to return otherwise;
* `paidOf` / `entryOf` / `cutOf` — **the decoder.**  `paidOf` is exactly the
  joint priced above, and the other two compute the first-entry value and the
  continuation's window bound *from that joint alone*, which is what an
  adaptive consumer can actually do.  They are total, and free: the only
  nontrivial step is `ReesQuot.proj_lift`, an injectivity rather than a query.
  `entryOf_paidOf` says the decoding is correct on the promise.

**What halves is not the queried length.**  With integer midpoints the
queried block lengths need not halve at all: a gap of `3` taken through the
right branch queries length `1`, and then length `1` again.  The sequence the
geometric sum runs on is the **gap minus one**,

    `b = ((hi - lo - 1 : ℕ) : ℝ)`,

which does halve at every child (`envelope_step`) and dominates the queried
length (`queried_le_envelope`).  So `n / 2^i` is a dyadic *envelope*, never the
literal block-length sequence — reading it as the latter is a real error, and
the reason this is spelled out here.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Query

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M] {I : ReesIdeal M}

/-- **The block query.**  The exact quotient product of the block
`[lo, lo + len)`, at the cost the quotient's word product has on a word of
length `len`. -/
theorem hasDual_blockProj (letter : σ → M) {n : ℕ} {D : ℝ}
    (hQ : HasWordProdDualUpTo (fun c => ReesQuot.proj I (letter c)) n D)
    {lo len : ℕ} (h : lo + len ≤ n) :
    HasDual (fun x : Fin n → σ =>
        ReesQuot.proj I (winProd letter x lo (lo + len)))
      (D * Real.sqrt (len : ℝ)) := by
  refine ((hQ.apply (le_trans (Nat.le_add_left len lo) h)).pullback
    (winEmb_injective h)).ofEq fun x => ?_
  rw [pullbackFun_apply, ReesQuot.wordProd_proj, wordProd_winEmb letter x h]

end Query

section GeometricSum

/-- **The geometric sum**, at constant `4`.  A sequence whose terms at least
halve has square roots summing to at most `4` times the first.

The proof is a shift induction, not a closed form: that is what keeps `√2` out
of the statement and the arithmetic rational throughout. -/
theorem sum_sqrt_halving :
    ∀ (L : ℕ) (b : ℕ → ℝ), (∀ i, 0 ≤ b i) → (∀ i, b (i + 1) ≤ b i / 2) →
      ∑ i ∈ Finset.range L, Real.sqrt (b i) ≤ 4 * Real.sqrt (b 0) := by
  intro L
  induction L with
  | zero =>
      intro b hb _
      simp only [Finset.range_zero, Finset.sum_empty]
      have := Real.sqrt_nonneg (b 0)
      linarith
  | succ L ih =>
      intro b hb hstep
      have hshift : ∑ i ∈ Finset.range (L + 1), Real.sqrt (b i)
          = (∑ i ∈ Finset.range L, Real.sqrt (b (i + 1))) + Real.sqrt (b 0) :=
        Finset.sum_range_succ' (fun i => Real.sqrt (b i)) L
      have hIH := ih (fun i => b (i + 1)) (fun i => hb (i + 1)) (fun i => hstep (i + 1))
      have hhalf : Real.sqrt (b 1) ≤ (3 / 4) * Real.sqrt (b 0) := by
        have hle : b 1 ≤ (3 / 4 : ℝ) ^ 2 * b 0 := by
          have := hstep 0
          have := hb 0
          nlinarith
        calc Real.sqrt (b 1) ≤ Real.sqrt ((3 / 4 : ℝ) ^ 2 * b 0) :=
              Real.sqrt_le_sqrt hle
          _ = (3 / 4) * Real.sqrt (b 0) := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      rw [hshift]
      linarith

/-! ### The envelope

`envelope_step` and `queried_le_envelope` are what connect the search's integer
arithmetic to the halving hypothesis above. -/

/-- **The gap minus one halves.**  A child gap is at most `⌈g/2⌉ = g - g/2`, and
then `g' - 1 ≤ (g - 1)/2` — with equality at odd `g`, which is why the *gap*
itself is not the right quantity. -/
theorem envelope_step {g g' : ℕ} (hg : g' ≤ g - g / 2) :
    ((g' - 1 : ℕ) : ℝ) ≤ ((g - 1 : ℕ) : ℝ) / 2 := by
  have h : 2 * (g' - 1) ≤ g - 1 := by omega
  have hc : ((2 * (g' - 1) : ℕ) : ℝ) ≤ ((g - 1 : ℕ) : ℝ) := Nat.cast_le.2 h
  rw [Nat.cast_mul] at hc
  norm_num at hc
  linarith

/-- **The queried length is under the envelope.**  The block `[lo, lo + g/2)` is
never longer than the gap minus one. -/
theorem queried_le_envelope (g : ℕ) : g / 2 ≤ g - 1 := by omega

/-- The dyadic envelope itself, as a halving sequence. -/
theorem sum_sqrt_halves (n L : ℕ) :
    ∑ i ∈ Finset.range L, Real.sqrt ((n : ℝ) / 2 ^ i) ≤ 4 * Real.sqrt (n : ℝ) := by
  have h := sum_sqrt_halving L (fun i => (n : ℝ) / 2 ^ i)
    (fun i => by positivity) (fun i => by rw [pow_succ, div_div])
  simpa using h

end GeometricSum

/-! ## The padded trace

The search itself, in the `conf`/`confOf` shape of `ActionCompiler.lean`'s search.
Its **configuration** is `(lo, hi, qlo)`: the live interval together with the
quotient product of the prefix `[0, lo)`.  The step is *defined* from the level
record — the raw block quotient — so the configuration after `j` levels is a
function of the first `j` records and nothing else (`conf_eq_confOf`).  That is
what makes each level a **total** dual, and it is why the whole trace is total:
the zero-product promise never enters here, only the semantic theorem.

Two things are structural rather than semantic, and both are load-bearing:

* `IsValid` — `lo ≤ hi ≤ n`, with `lo < n` once `0 < n`.  It holds at every
  trace value, not just the promise-satisfying ones, because `adaptiveCall`'s
  branch family is indexed by *all* of them.  The `lo ≤ hi` conjunct is not
  decoration: it is what discharges `lo + (hi - lo)/2 ≤ n`, the side condition
  of `hasDual_blockProj` on every branch;
* `env_confOf` — the envelope bound `hi - lo - 1 ≤ (n-1)/2^j`, again at every
  trace value, so the branch cost `D√((n-1)/2^j)` is *uniform* over the branch
  family, which is exactly what `adaptiveCall` asks for.
-/

section Trace

variable {σ M : Type} [Fintype σ] [DecidableEq σ] [Monoid M] [Fintype M]
  [DecidableEq M]

namespace FirstEntry

/-- **The search configuration**: the live interval `[lo, hi)` and `qlo`, the
quotient product of the prefix `[0, lo)`.  Under the promise `qlo` is nonzero
and the prefix product at `hi` is zero — but nothing below assumes that. -/
abbrev SearchConf (I : ReesIdeal M) : Type := ℕ × ℕ × ReesQuot I

variable {I : ReesIdeal M}

/-- The live interval's width. -/
def gap (c : SearchConf I) : ℕ := c.2.1 - c.1

/-- **The queried length**: half the gap, rounded down.  At gap `≤ 1` it is
zero, so a finished search queries the empty block at cost `D√0 = 0` and stays
put — which is why no `Option` is needed to mark the search as done. -/
def queryLen (c : SearchConf I) : ℕ := gap c / 2

/-- **The step, read off the level record.**  The branch is on `qlo * b = 0`,
**not** on `b = 0`: the Rees quotient has zero divisors, so a nonzero block can
still kill a nonzero prefix, and branching on the block alone is a different —
and wrong — predicate. -/
def step (c : SearchConf I) (b : ReesQuot I) : SearchConf I :=
  if c.2.2 * b = ReesQuot.zero then (c.1, c.1 + queryLen c, c.2.2)
  else (c.1 + queryLen c, c.2.1, c.2.2 * b)

lemma step_fst (c : SearchConf I) (b : ReesQuot I) :
    (step c b).1 = if c.2.2 * b = ReesQuot.zero then c.1 else c.1 + queryLen c := by
  simp only [step]; split_ifs <;> rfl

lemma step_snd_fst (c : SearchConf I) (b : ReesQuot I) :
    (step c b).2.1
      = if c.2.2 * b = ReesQuot.zero then c.1 + queryLen c else c.2.1 := by
  simp only [step]; split_ifs <;> rfl

lemma step_snd_snd (c : SearchConf I) (b : ReesQuot I) :
    (step c b).2.2 = if c.2.2 * b = ReesQuot.zero then c.2.2 else c.2.2 * b := by
  simp only [step]; split_ifs <;> rfl

/-- **The level record**: the raw block quotient of `[lo, lo + queryLen)`.  The
product `qlo * b` is recomputed inside the step and never stored, so the slot
type stays `ReesQuot I`. -/
def blockOf (letter : σ → M) {n : ℕ} (x : Fin n → σ) (c : SearchConf I) :
    ReesQuot I :=
  ReesQuot.proj I (winProd letter x c.1 (c.1 + queryLen c))

/-- The configuration after `j` levels of the search on the word `x`. -/
def conf (I : ReesIdeal M) (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    ℕ → SearchConf I
  | 0 => (0, n, 1)
  | j + 1 => step (conf I letter x j) (blockOf letter x (conf I letter x j))

/-- The record at level `j`. -/
def levelAt (I : ReesIdeal M) (letter : σ → M) {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    ReesQuot I :=
  blockOf letter x (conf I letter x j)

@[simp] lemma conf_zero (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    conf I letter x 0 = (0, n, 1) := rfl

lemma conf_succ (letter : σ → M) {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    conf I letter x (j + 1) = step (conf I letter x j) (levelAt I letter x j) := rfl

/-- **The reconstruction**: the same recursion run on a supplied sequence of
block quotients instead of on the word. -/
def confOf (n : ℕ) (t : ℕ → ReesQuot I) : ℕ → SearchConf I
  | 0 => (0, n, 1)
  | j + 1 => step (confOf n t j) (t j)

@[simp] lemma confOf_zero (n : ℕ) (t : ℕ → ReesQuot I) :
    confOf n t 0 = (0, n, 1) := rfl

lemma confOf_succ (n : ℕ) (t : ℕ → ReesQuot I) (j : ℕ) :
    confOf n t (j + 1) = step (confOf n t j) (t j) := rfl

/-- **Determinism.**  The configuration after `j` levels is a function of the
first `j` records — no further access to the word.  This is what turns each
level into a total dual on a fiber. -/
theorem conf_eq_confOf (letter : σ → M) {n : ℕ} (x : Fin n → σ)
    (t : ℕ → ReesQuot I) (j : ℕ)
    (ht : ∀ i, i < j → levelAt I letter x i = t i) :
    conf I letter x j = confOf n t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hprev := ih fun i hi => ht i (by omega)
      have hj := ht j (Nat.lt_succ_self j)
      rw [levelAt, hprev] at hj
      rw [conf_succ, confOf_succ, hprev, levelAt, hprev, hj]

/-! ### The structural interval invariant -/

/-- **The interval invariant, structurally.**  Every reconstructed
configuration satisfies it — promise or not — since `adaptiveCall`'s branch
family is indexed by all trace values. -/
structure IsValid (n : ℕ) (c : SearchConf I) : Prop where
  /-- The interval is not inverted.  This conjunct is what discharges the
  block query's side condition. -/
  lo_le_hi : c.1 ≤ c.2.1
  /-- The interval stays inside the word. -/
  hi_le : c.2.1 ≤ n
  /-- On a nonempty word the low endpoint is a genuine position. -/
  lo_lt : 0 < n → c.1 < n

theorem isValid_step {n : ℕ} {c : SearchConf I} (h : IsValid n c) (b : ReesQuot I) :
    IsValid n (step c b) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [step_fst, step_snd_fst, queryLen, gap]
      split_ifs <;> omega

theorem isValid_confOf (n : ℕ) (t : ℕ → ReesQuot I) (j : ℕ) :
    IsValid n (confOf n t j) := by
  induction j with
  | zero => exact ⟨Nat.zero_le n, le_rfl, fun h => h⟩
  | succ j ih => exact isValid_step ih (t j)

/-- **The queried block fits inside the word.**  This is the side condition
`hasDual_blockProj` needs, on every branch. -/
theorem query_le {n : ℕ} {c : SearchConf I} (h : IsValid n c) :
    c.1 + queryLen c ≤ n := by
  have h1 := h.lo_le_hi
  have h2 := h.hi_le
  simp only [queryLen, gap]
  omega

/-! ### The envelope, structurally -/

/-- The dyadic envelope of a configuration: the gap minus one. -/
noncomputable def env (c : SearchConf I) : ℝ := ((gap c - 1 : ℕ) : ℝ)

/-- **A child's gap is at most `g - g/2`** — the left child takes `g/2`, the
right child `g - g/2`, and the right one is the larger. -/
theorem gap_step (c : SearchConf I) (b : ReesQuot I) :
    gap (step c b) ≤ gap c - gap c / 2 := by
  simp only [gap, step_fst, step_snd_fst, queryLen]
  split_ifs <;> omega

/-- **The envelope halves at every level**, at every trace value. -/
theorem env_step (c : SearchConf I) (b : ReesQuot I) :
    env (step c b) ≤ env c / 2 :=
  envelope_step (gap_step c b)

/-- **The depth-uniform envelope bound.**  `(n-1)/2^j` dominates the gap minus
one after `j` levels, for **every** trace `t` — structurally, not merely on the
promise.  This is what makes the level-`j` branch cost uniform over the branch
family. -/
theorem env_confOf (n : ℕ) (t : ℕ → ReesQuot I) (j : ℕ) :
    env (confOf n t j) ≤ ((n - 1 : ℕ) : ℝ) / 2 ^ j := by
  induction j with
  | zero => simp [env, gap]
  | succ j ih =>
      have h1 : env (confOf n t (j + 1)) ≤ env (confOf n t j) / 2 :=
        env_step (confOf n t j) (t j)
      have h2 : ((n - 1 : ℕ) : ℝ) / 2 ^ (j + 1) = (((n - 1 : ℕ) : ℝ) / 2 ^ j) / 2 := by
        rw [pow_succ, div_div]
      rw [h2]
      linarith

/-- **The queried length is under the envelope.**  With integer midpoints the
queried lengths need not halve; the envelope does, and dominates them. -/
theorem queryLen_le_env (c : SearchConf I) : ((queryLen c : ℕ) : ℝ) ≤ env c :=
  Nat.cast_le.2 (queried_le_envelope (gap c))

/-- **One level's query, at the depth-uniform cost.**  The bound holds at every
trace value, so `adaptiveCall` may charge it once for the whole branch
family. -/
theorem hasDual_level (letter : σ → M) {n : ℕ} {D : ℝ}
    (hQ : HasWordProdDualUpTo (fun c => ReesQuot.proj I (letter c)) n D)
    (t : ℕ → ReesQuot I) (j : ℕ) :
    HasDual (fun x : Fin n → σ => blockOf letter x (confOf n t j))
      (D * Real.sqrt (((n - 1 : ℕ) : ℝ) / 2 ^ j)) := by
  refine (hasDual_blockProj letter hQ (query_le (isValid_confOf n t j))).mono ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hQ.nonneg
  exact le_trans (queryLen_le_env _) (env_confOf n t j)

/-! ### The trace and its dual -/

/-- The level family the padded trace is built from. -/
def traceLevel (I : ReesIdeal M) (letter : σ → M) (n : ℕ) (i : Fin n)
    (x : Fin n → σ) : ReesQuot I :=
  levelAt I letter x (i : ℕ)

/-- Reading a padded trace as a sequence: past the horizon it is the pad. -/
def unpad {n : ℕ} (d : Fin n → ReesQuot I) (i : ℕ) : ReesQuot I :=
  if h : i < n then d ⟨i, h⟩ else 1

/-- **Determinism at the fiber**: on the fiber where the first `j` slots of the
padded trace are fixed, the level-`j` configuration is fixed too. -/
lemma conf_eq_confOf_preTrans (letter : σ → M) {n : ℕ} (x : Fin n → σ) {j : ℕ}
    (hj : j ≤ n) :
    conf I letter x j
      = confOf n (unpad (preTrans (traceLevel I letter n) (1 : ReesQuot I) j x)) j := by
  refine conf_eq_confOf letter x _ j fun i hi => ?_
  have hin : i < n := lt_of_lt_of_le hi hj
  simp only [unpad, dif_pos hin, preTrans, if_pos hi, traceLevel]

/-- **The prefix trace, at the geometric cost** `D ∑_{i<j} √((n-1)/2^i)`.

A *local* variable-cost induction.  `HasDual.adaptiveTranscript` is not the
right endpoint: it charges `m·g` for one **uniform** per-level cost, whereas
level `j` here costs `D√((n-1)/2^j)`.  The step is `HasDual.adaptiveCall` — the
prefix trace as descriptor, the level-`j` block query as the branch, at the
uniform branch cost `env_confOf` supplies — folded back into `preTrans` by
`ofKer` and `preTrans_succ_iff`.  A `postcomp` per level would compound
instead. -/
theorem hasDual_preTrans (letter : σ → M) {n : ℕ} {D : ℝ}
    (hQ : HasWordProdDualUpTo (fun c => ReesQuot.proj I (letter c)) n D) :
    ∀ j : ℕ, j ≤ n →
      HasDual (preTrans (traceLevel I letter n) (1 : ReesQuot I) j)
        (D * ∑ i ∈ Finset.range j, Real.sqrt (((n - 1 : ℕ) : ℝ) / 2 ^ i)) := by
  intro j
  induction j with
  | zero =>
      intro _
      have h0 : HasDual (preTrans (traceLevel I letter n) (1 : ReesQuot I) 0) 0 := by
        refine hasDual_const fun x y => ?_
        funext i
        simp [preTrans]
      exact h0.mono (by simp)
  | succ j ih =>
      intro hj
      have hjn : j < n := hj
      have hcall := HasDual.adaptiveCall (ih (Nat.le_of_succ_le hj))
        (T := fun d x => blockOf letter x (confOf n (unpad d) j))
        (fun d => hasDual_level letter hQ (unpad d) j)
      have hpair := hcall.ofEq fun x => by
        rw [← conf_eq_confOf_preTrans letter x (le_of_lt hjn)]
      have hker := hpair.ofKer
        (f' := preTrans (traceLevel I letter n) (1 : ReesQuot I) (j + 1))
        fun x y => by
          rw [Prod.mk.injEq]
          exact preTrans_succ_iff (traceLevel I letter n) 1 hjn x y
      refine hker.mono (le_of_eq ?_)
      rw [Finset.sum_range_succ]
      ring

/-- **The trace the algorithm exports**, as one function of the word.  This is
the descriptor an adaptive consumer branches on, so everything the fixed-apex
peel needs must be computable from it. -/
def traceOf (I : ReesIdeal M) (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    Fin n → ReesQuot I :=
  fun i => levelAt I letter x (i : ℕ)

/-- **The full padded trace**, at `4D√n`.

The horizon is `n` itself.  The cost is a geometric sum, so the level count
never enters the bound — there is nothing to gain from a tight `⌈log₂⌉` horizon
and something to lose: `n` levels cover `n = 0` with no `clog` arithmetic and no
nonemptiness side condition. -/
theorem hasDual_trace (letter : σ → M) {n : ℕ} {D : ℝ}
    (hQ : HasWordProdDualUpTo (fun c => ReesQuot.proj I (letter c)) n D) :
    HasDual (fun x : Fin n → σ => traceOf I letter x)
      (4 * D * Real.sqrt (n : ℝ)) := by
  refine ((hasDual_preTrans letter hQ n le_rfl).ofEq fun x => ?_).mono ?_
  · funext i
    simp [preTrans, i.isLt, traceLevel, traceOf]
  · have hsum := sum_sqrt_halves (n - 1) n
    have hle : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n 1)
    have hD := hQ.nonneg
    have h1 : D * ∑ i ∈ Finset.range n, Real.sqrt (((n - 1 : ℕ) : ℝ) / 2 ^ i)
        ≤ D * (4 * Real.sqrt ((n - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hD
    nlinarith [Real.sqrt_nonneg ((n - 1 : ℕ) : ℝ), Real.sqrt_nonneg (n : ℝ)]

/-! ### The crossing letter

The fourth deliverable.  `0 < n` is a hypothesis and cannot be dropped: at
`n = 0` there is no crossing letter and none can be manufactured — the promise
is empty and `σ` is not assumed nonempty, so no total `σ`-valued output exists.
Every consumer of a crossing letter already has a nonempty word.
-/

/-- The low endpoint a trace decodes to, as a position of the word.  It is a
genuine position by `IsValid.lo_lt`, structurally — at every trace value. -/
def loOf (n : ℕ) (hn : 0 < n) (d : Fin n → ReesQuot I) : Fin n :=
  ⟨(confOf n (unpad d) n).1, (isValid_confOf n (unpad d) n).lo_lt hn⟩

/-- **The reconstruction from the exported trace is the search itself.**  This
is what makes every decoder below a function of the paid descriptor. -/
lemma confOf_traceOf (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    confOf n (unpad (traceOf I letter x)) n = conf I letter x n :=
  (conf_eq_confOf letter x _ n fun i hi => by
    simp only [unpad, dif_pos hi, traceOf]).symm

/-- The decoded low endpoint is the search's own. -/
lemma loOf_trace (letter : σ → M) {n : ℕ} (hn : 0 < n) (x : Fin n → σ) :
    ((loOf n hn (traceOf I letter x)) : ℕ) = (conf I letter x n).1 := by
  simp only [loOf]
  rw [confOf_traceOf]

/-- **The trace and the crossing letter, jointly**, at `4D√n + 2` — comfortably
below `8D√n + 2`.

The joint is kept whole: projecting the letter out of it would cost a factor
two (`HasDual.postcomp`), and the descriptor chain is what the fixed-apex peel
consumes.  The collapse happens once, at the end. -/
theorem hasDual_traceLetter (letter : σ → M) {n : ℕ} (hn : 0 < n) {D : ℝ}
    (hQ : HasWordProdDualUpTo (fun c => ReesQuot.proj I (letter c)) n D) :
    HasDual (fun x : Fin n → σ =>
        (traceOf I letter x, x (loOf n hn (traceOf I letter x))))
      (4 * D * Real.sqrt (n : ℝ) + 2) :=
  HasDual.adaptiveCall (T := fun d x => x (loOf n hn d)) (hasDual_trace letter hQ)
    fun d => hasDual_ofCoord (loOf n hn d) id

/-! ### The decoder

The algorithm pays for the joint `(trace, crossing letter)` and for nothing
else, so a consumer must be able to compute the first-entry **value** from that
joint alone.  `preOf` and `entryOf` do, and `entryOf_paidOf` says they are
right.  Two properties are what make them usable inside an adaptive call:

* they are **total** — defined at every descriptor value, not only the ones the
  promise admits, because the branch family of `HasDual.adaptiveCall` is
  indexed by all of them;
* they are **free** — the only nontrivial step is `ReesQuot.proj_lift`, and
  that is the injectivity `proj_eq_iff_of_ne_zero`, not a query.
-/

/-- **The paid joint**: exactly the function `hasDual_traceLetter` prices. -/
def paidOf (I : ReesIdeal M) (letter : σ → M) {n : ℕ} (hn : 0 < n)
    (x : Fin n → σ) : (Fin n → ReesQuot I) × σ :=
  (traceOf I letter x, x (loOf n hn (traceOf I letter x)))

/-- The paid joint's dual, at `4D√n + 2`. -/
theorem hasDual_paidOf (letter : σ → M) {n : ℕ} (hn : 0 < n) {D : ℝ}
    (hQ : HasWordProdDualUpTo (fun c => ReesQuot.proj I (letter c)) n D) :
    HasDual (paidOf I letter hn) (4 * D * Real.sqrt (n : ℝ) + 2) :=
  hasDual_traceLetter letter hn hQ

/-- **The predecessor `p`, decoded from the trace**: the total lift of the
stored `qlo`. -/
def preOf {n : ℕ} (d : Fin n → ReesQuot I) : M :=
  (confOf n (unpad d) n).2.2.lift

/-- **The first-entry value `h = p·a`, decoded from the paid joint.** -/
def entryOf (letter : σ → M) {n : ℕ} (d : (Fin n → ReesQuot I) × σ) : M :=
  preOf d.1 * letter d.2

/-- **The cut just past the first entry**, decoded from the trace: the window
bound the continuation runs from. -/
def cutOf {n : ℕ} (d : Fin n → ReesQuot I) : ℕ := (confOf n (unpad d) n).1 + 1

/-- **The first entry consumes a letter.**  The decoded cut is at least `1`, so
the continuation it names has length at most `n - 1` — which is what keeps the
peel's horizon from growing under repeated carrier recursion. -/
lemma one_le_cutOf {n : ℕ} (d : Fin n → ReesQuot I) : 1 ≤ cutOf d := by
  simp only [cutOf]
  omega

/-- **The decoded cut is a genuine bound**, at every trace value — structural,
so the window it names is well formed on every branch of an adaptive call. -/
lemma cutOf_le {n : ℕ} (hn : 0 < n) (d : Fin n → ReesQuot I) : cutOf d ≤ n := by
  have := (isValid_confOf n (unpad d) n).lo_lt hn
  simp only [cutOf]
  omega

@[simp] lemma cutOf_paidOf (letter : σ → M) {n : ℕ} (hn : 0 < n) (x : Fin n → σ) :
    cutOf (paidOf I letter hn x).1 = (conf I letter x n).1 + 1 := by
  simp only [cutOf, paidOf, confOf_traceOf]

/-- One more letter extends the prefix product. -/
lemma winProd_succ (letter : σ → M) {n : ℕ} (x : Fin n → σ) (i : Fin n) :
    winProd letter x 0 ((i : ℕ) + 1)
      = winProd letter x 0 (i : ℕ) * letter (x i) := by
  simp only [winProd]
  rw [rangeProd_succ_right (fun t => letter (x t)) (Nat.zero_le (i : ℕ)),
    padAt_of_lt _ i.isLt]

/-! ### What the trace means

Everything above is total — the padded trace is built for every word and its
dual never mentions a promise.  The zero-product **promise** enters only here,
in the semantic theorem, which says what the trace *locates*. -/

/-- The quotient product of the prefix `[0, k)`. -/
def pre (I : ReesIdeal M) (letter : σ → M) {n : ℕ} (x : Fin n → σ) (k : ℕ) :
    ReesQuot I :=
  ReesQuot.proj I (winProd letter x 0 k)

@[simp] lemma pre_zero (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    pre I letter x 0 = 1 := by
  simp [pre, winProd]

lemma pre_full (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    pre I letter x n = ReesQuot.proj I (wordProd letter x) := by
  rw [wordProd_eq_winProd]
  rfl

/-- **The prefix splits at the block.**  This is where `qlo * b` comes from: the
step recomputes it and never stores it. -/
lemma pre_add (letter : σ → M) {n : ℕ} (x : Fin n → σ) (lo len : ℕ) :
    pre I letter x (lo + len)
      = pre I letter x lo * ReesQuot.proj I (winProd letter x lo (lo + len)) := by
  simp only [pre, winProd]
  rw [← ReesQuot.proj_mul,
    rangeProd_split (fun i => letter (x i)) (Nat.zero_le lo) (Nat.le_add_right lo len)]

/-- **The semantic invariant**: the stored prefix product really is the prefix
product at `lo` and is nonzero, and the prefix product at `hi` is zero. -/
structure IsLocating (letter : σ → M) {n : ℕ} (x : Fin n → σ)
    (c : SearchConf I) : Prop where
  /-- The third component is the prefix product at `lo`. -/
  qlo_eq : c.2.2 = pre I letter x c.1
  /-- The prefix has not entered the ideal at `lo`. -/
  qlo_ne : c.2.2 ≠ ReesQuot.zero
  /-- It has entered by `hi`. -/
  hi_zero : pre I letter x c.2.1 = ReesQuot.zero

/-- **The step preserves the meaning.**  Both branches use the same split; which
one is taken is decided by `qlo * b`, and that is exactly the prefix product at
the midpoint. -/
theorem isLocating_step (letter : σ → M) {n : ℕ} (x : Fin n → σ)
    {c : SearchConf I} (h : IsLocating letter x c) :
    IsLocating letter x (step c (blockOf letter x c)) := by
  have hsplit : pre I letter x (c.1 + queryLen c) = c.2.2 * blockOf letter x c := by
    rw [pre_add, ← h.qlo_eq]
    rfl
  by_cases hb : c.2.2 * blockOf letter x c = ReesQuot.zero
  · exact ⟨by rw [step_snd_snd, step_fst, if_pos hb, if_pos hb]; exact h.qlo_eq,
      by rw [step_snd_snd, if_pos hb]; exact h.qlo_ne,
      by rw [step_snd_fst, if_pos hb, hsplit]; exact hb⟩
  · exact ⟨by rw [step_snd_snd, step_fst, if_neg hb, if_neg hb]; exact hsplit.symm,
      by rw [step_snd_snd, if_neg hb]; exact hb,
      by rw [step_snd_fst, if_neg hb]; exact h.hi_zero⟩

/-- Under the promise the invariant holds at every level. -/
theorem isLocating_conf (letter : σ → M) {n : ℕ} (x : Fin n → σ)
    (hz : ReesQuot.proj I (wordProd letter x) = ReesQuot.zero) (j : ℕ) :
    IsLocating letter x (conf I letter x j) := by
  induction j with
  | zero =>
      exact ⟨(pre_zero letter x).symm, ReesQuot.one_ne_zero,
        (pre_full letter x).trans hz⟩
  | succ j ih => exact isLocating_step letter x ih

/-- The real search's configuration satisfies the structural invariant too. -/
theorem isValid_conf (letter : σ → M) {n : ℕ} (x : Fin n → σ) (j : ℕ) :
    IsValid n (conf I letter x j) := by
  induction j with
  | zero => exact ⟨Nat.zero_le n, le_rfl, fun h => h⟩
  | succ j ih => exact isValid_step ih _

/-! ### Termination -/

/-- **The envelope, kept in `ℕ`.**  The same halving as `env_confOf`, integral,
so that at the horizon it is zero. -/
theorem gap_confOf_le (n : ℕ) (t : ℕ → ReesQuot I) (j : ℕ) :
    gap (confOf n t j) - 1 ≤ (n - 1) / 2 ^ j := by
  induction j with
  | zero => simp [gap]
  | succ j ih =>
      have h1 : gap (confOf n t (j + 1))
          ≤ gap (confOf n t j) - gap (confOf n t j) / 2 :=
        gap_step (confOf n t j) (t j)
      calc gap (confOf n t (j + 1)) - 1 ≤ (gap (confOf n t j) - 1) / 2 := by omega
        _ ≤ ((n - 1) / 2 ^ j) / 2 := Nat.div_le_div_right ih
        _ = (n - 1) / 2 ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]

/-- **At the horizon the interval has collapsed.**  `n` levels are enough for
every `n`: `n - 1 < 2 ^ n`. -/
theorem gap_confOf_horizon (n : ℕ) (t : ℕ → ReesQuot I) :
    gap (confOf n t n) ≤ 1 := by
  have h := gap_confOf_le n t n
  have hlt : n - 1 < 2 ^ n := lt_of_le_of_lt (Nat.sub_le n 1) n.lt_two_pow_self
  rw [Nat.div_eq_of_lt hlt] at h
  omega

/-- **The first entry, located.**  On the promise that the whole word's quotient
product is zero, the search's final configuration is `[lo, lo + 1)`, the stored
value is the prefix product at `lo`, that value is nonzero, and the single
letter at `lo` kills it.

**Every `n`.**  `0 < n` is *not* a hypothesis: at `n = 0` the promise is
self-contradictory, since the empty word's quotient product is `1` and
`ReesQuot.one_ne_zero`, so the existential follows by elimination.  Only the
total `σ`-valued crossing letter of `hasDual_traceLetter` genuinely needs
positivity — there is no letter to return at `n = 0`.

The promise appears nowhere outside this section, and this is its only public
endpoint; `isLocating_conf` carries it internally. -/
theorem conf_horizon_spec (letter : σ → M) {n : ℕ} (x : Fin n → σ)
    (hz : ReesQuot.proj I (wordProd letter x) = ReesQuot.zero) :
    ∃ lo : Fin n,
      (conf I letter x n).1 = (lo : ℕ)
        ∧ (conf I letter x n).2.1 = (lo : ℕ) + 1
        ∧ (conf I letter x n).2.2 = pre I letter x (lo : ℕ)
        ∧ pre I letter x (lo : ℕ) ≠ ReesQuot.zero
        ∧ pre I letter x (lo : ℕ) * ReesQuot.proj I (letter (x lo))
            = ReesQuot.zero := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd ((pre_zero letter x).symm.trans ((pre_full letter x).trans hz))
      ReesQuot.one_ne_zero
  have hv := isValid_conf (I := I) letter x n
  have hl := isLocating_conf letter x hz n
  have hlo : (conf I letter x n).1 < n := hv.lo_lt hn
  have hcf : conf I letter x n = confOf n (fun i => levelAt I letter x i) n :=
    conf_eq_confOf letter x _ n fun _ _ => rfl
  have hgap : gap (conf I letter x n) ≤ 1 := by
    rw [hcf]; exact gap_confOf_horizon n _
  have hne : (conf I letter x n).1 ≠ (conf I letter x n).2.1 := by
    intro hEq
    exact hl.qlo_ne (by rw [hl.qlo_eq, hEq]; exact hl.hi_zero)
  have hhi : (conf I letter x n).2.1 = (conf I letter x n).1 + 1 := by
    have h1 := hv.lo_le_hi
    simp only [gap] at hgap
    omega
  refine ⟨⟨(conf I letter x n).1, hlo⟩, rfl, hhi, hl.qlo_eq, ?_, ?_⟩
  · rw [← hl.qlo_eq]; exact hl.qlo_ne
  · have hkill : pre I letter x ((conf I letter x n).1 + 1)
        = pre I letter x (conf I letter x n).1
          * ReesQuot.proj I (letter (x ⟨(conf I letter x n).1, hlo⟩)) := by
      rw [pre_add]
      simp only [winProd]
      rw [rangeProd_singleton (fun i => letter (x i)) hlo]
    have hzero := hl.hi_zero
    rw [hhi] at hzero
    exact hkill.symm.trans hzero

/-! ### The decoder is correct

The two statements below use the promise; every definition above is total. -/

/-- **The decoded predecessor is the real one.**  On the promise, the lift of
the stored `qlo` is the prefix product at the located cut. -/
theorem preOf_paidOf (letter : σ → M) {n : ℕ} (hn : 0 < n) (x : Fin n → σ)
    (hz : ReesQuot.proj I (wordProd letter x) = ReesQuot.zero) :
    preOf (paidOf I letter hn x).1
      = winProd letter x 0 (conf I letter x n).1 := by
  obtain ⟨lo, hlo, -, hq, hne, -⟩ := conf_horizon_spec letter x hz
  simp only [preOf, paidOf, confOf_traceOf, hq, hlo]
  exact ReesQuot.lift_proj hne

/-- **The decoder is correct.**  On the promise, the value computed from the
paid joint — and from nothing else — is the actual first-entry value
`h = p·a`. -/
theorem entryOf_paidOf (letter : σ → M) {n : ℕ} (hn : 0 < n) (x : Fin n → σ)
    (hz : ReesQuot.proj I (wordProd letter x) = ReesQuot.zero) :
    entryOf letter (paidOf I letter hn x)
      = winProd letter x 0 ((conf I letter x n).1 + 1) := by
  obtain ⟨lo, hlo, -, hq, hne, -⟩ := conf_horizon_spec letter x hz
  have hfin : loOf n hn (traceOf I letter x) = lo :=
    Fin.ext (by rw [loOf_trace letter hn x, hlo])
  simp only [entryOf]
  rw [preOf_paidOf letter hn x hz, hlo]
  simp only [paidOf, hfin]
  exact (winProd_succ letter x lo).symm

end FirstEntry

end Trace

end MonoidProduct
