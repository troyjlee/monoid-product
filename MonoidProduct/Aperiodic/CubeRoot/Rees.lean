import MonoidProduct.Aperiodic.CubeRoot.ApexData
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The Rees quotient

The fixed-apex peel (the paper's `lem:ags-fixed-apex-peel`) works modulo

    `I_J = M¹JM¹ = twoIdeal apex`,

the principal two-sided ideal of the apex — which **contains `J` itself**, and
so collapses the apex class along with everything below it.  That is the point
of the construction and the reason the first-entry search and the killed axis exist: the quotient throws the
`J`-coordinate away, and first entry into the ideal together with the killed
`R`-axis inside `J` is how it is recovered.  The quotient is *not* by the
elements strictly below the apex; that would leave `J` visible and there would
be nothing to recover.

Two facts are wanted of the construction, and they are what this file proves.

* **Unique nonzero lifts** (`proj_eq_iff_of_ne_zero`): a nonzero element of the
  quotient has exactly one preimage, so reading a quotient answer back into `M`
  costs nothing and loses nothing.  Off zero the projection is injective.
* **The cardinality** `|M/I| = |M| - |I| + 1` (`card_reesQuot`), which is what
  turns "the ideal is large" into "the carrier drops", and hence the peel's
  progress measure.

The quotient is `Option` of the complement, with `none` the collapsed zero:
that is the definition that makes both facts immediate rather than a
quotient-type argument.  Nothing here is specific to the apex; the ideal is
supplied.
-/

namespace MonoidProduct
open QuantumQueryComplexity

section Rees

variable {M : Type} [Monoid M] [Fintype M] [DecidableEq M]

/-- **A proper two-sided ideal**, as a `Finset`.  `mul_mem` is stated in the
sandwich form, which gives both one-sided laws by taking a factor `1`. -/
structure ReesIdeal (M : Type) [Monoid M] [Fintype M] [DecidableEq M] where
  /-- The underlying set. -/
  carrier : Finset M
  /-- It absorbs multiplication on both sides. -/
  mul_mem : ∀ (p : M) {a : M}, a ∈ carrier → ∀ q : M, p * a * q ∈ carrier
  /-- It is nonempty.  Without this the "quotient" would be `M` with an
  unreachable new zero: `proj` would not be surjective and the cardinality
  would be `|M| + 1`, a carrier *rise*.  The intended carrier
  `twoIdeal apex` contains its own generator, so this costs nothing. -/
  carrier_nonempty : carrier.Nonempty
  /-- It is proper. -/
  one_notMem : (1 : M) ∉ carrier

namespace ReesIdeal

variable (I : ReesIdeal M)

lemma mul_left (p : M) {a : M} (ha : a ∈ I.carrier) : p * a ∈ I.carrier := by
  have := I.mul_mem p ha 1
  rwa [mul_one] at this

lemma mul_right {a : M} (ha : a ∈ I.carrier) (q : M) : a * q ∈ I.carrier := by
  have := I.mul_mem 1 ha q
  rwa [one_mul] at this

end ReesIdeal

/-! ## The underlying multiplication

Everything about the product is proved here, on the plain `Option`, where no
instance resolution is involved; the quotient type below is a one-field wrapper
that inherits it.  Doing it the other way round — a bare `def` for the quotient
— makes `some`/`none` elaborate at `Option` while the `Mul` instance lives at
the quotient, and every rewrite fails. -/

/-- Multiplication of the underlying options: the ideal absorbs. -/
def rmul (I : ReesIdeal M) :
    Option {a : M // a ∉ I.carrier} → Option {a : M // a ∉ I.carrier} →
      Option {a : M // a ∉ I.carrier}
  | none, _ => none
  | some _, none => none
  | some a, some b =>
      if h : a.val * b.val ∈ I.carrier then none else some ⟨a.val * b.val, h⟩

variable (I : ReesIdeal M)

@[simp] lemma rmul_none_left (y) : rmul I none y = none := by cases y <;> rfl

@[simp] lemma rmul_none_right (x) : rmul I x none = none := by cases x <;> rfl

lemma rmul_some (a b : {x : M // x ∉ I.carrier}) :
    rmul I (some a) (some b)
      = if h : a.val * b.val ∈ I.carrier then none else some ⟨a.val * b.val, h⟩ := rfl

lemma rmul_one_left (x) : rmul I (some ⟨1, I.one_notMem⟩) x = x := by
  cases x with
  | none => rfl
  | some a =>
      rw [rmul_some, dif_neg (by rw [one_mul]; exact a.2)]
      simp

lemma rmul_one_right (x) : rmul I x (some ⟨1, I.one_notMem⟩) = x := by
  cases x with
  | none => rfl
  | some a =>
      rw [rmul_some, dif_neg (by rw [mul_one]; exact a.2)]
      simp

lemma rmul_assoc (x y z) : rmul I (rmul I x y) z = rmul I x (rmul I y z) := by
  cases x with
  | none => simp
  | some a =>
    cases y with
    | none => simp
    | some b =>
      cases z with
      | none => simp
      | some c =>
        rw [rmul_some I a b]
        by_cases hab : a.val * b.val ∈ I.carrier
        · rw [dif_pos hab, rmul_none_left, rmul_some I b c]
          by_cases hbc : b.val * c.val ∈ I.carrier
          · rw [dif_pos hbc, rmul_none_right]
          · rw [dif_neg hbc, rmul_some I a ⟨b.val * c.val, hbc⟩,
              dif_pos (by rw [← mul_assoc]; exact I.mul_right hab c.val)]
        · rw [dif_neg hab, rmul_some I ⟨a.val * b.val, hab⟩ c, rmul_some I b c]
          by_cases hbc : b.val * c.val ∈ I.carrier
          · rw [dif_pos hbc, rmul_none_right,
              dif_pos (by rw [mul_assoc]; exact I.mul_left a.val hbc)]
          · rw [dif_neg hbc, rmul_some I a ⟨b.val * c.val, hbc⟩]
            by_cases habc : a.val * b.val * c.val ∈ I.carrier
            · rw [dif_pos habc, dif_pos (by rwa [mul_assoc] at habc)]
            · rw [dif_neg habc, dif_neg (by rwa [mul_assoc] at habc)]
              simp [mul_assoc]

/-! ## The quotient -/

/-- **The Rees quotient**: the complement of the ideal with a single adjoined
zero standing for the whole ideal.  A one-field wrapper, so that its algebraic
instances are unambiguously its own. -/
structure ReesQuot (I : ReesIdeal M) where
  /-- The underlying value; `none` is the collapsed ideal. -/
  val : Option {a : M // a ∉ I.carrier}

namespace ReesQuot

variable {I}

@[ext] lemma ext {x y : ReesQuot I} (h : x.val = y.val) : x = y := by
  cases x; cases y; simp_all

instance : DecidableEq (ReesQuot I) := fun x y =>
  decidable_of_iff (x.val = y.val) ⟨fun h => ext h, fun h => by rw [h]⟩

/-- The quotient is the option type it wraps. -/
def equivOption : ReesQuot I ≃ Option {a : M // a ∉ I.carrier} where
  toFun x := x.val
  invFun v := ⟨v⟩
  left_inv x := by cases x; rfl
  right_inv v := rfl

instance : Fintype (ReesQuot I) := Fintype.ofEquiv _ (equivOption (I := I)).symm

/-- The collapsed zero. -/
def zero : ReesQuot I := ⟨none⟩

/-- The class of an element outside the ideal. -/
def cls {a : M} (ha : a ∉ I.carrier) : ReesQuot I := ⟨some ⟨a, ha⟩⟩

instance : Mul (ReesQuot I) := ⟨fun x y => ⟨rmul I x.val y.val⟩⟩

instance : One (ReesQuot I) := ⟨⟨some ⟨1, I.one_notMem⟩⟩⟩

@[simp] lemma mul_val (x y : ReesQuot I) : (x * y).val = rmul I x.val y.val := rfl

@[simp] lemma one_val : (1 : ReesQuot I).val = some ⟨1, I.one_notMem⟩ := rfl

@[simp] lemma zero_val : (zero : ReesQuot I).val = none := rfl

/-- The identity is not the collapsed zero — the ideal is proper.  The
first-entry search branches on a quotient value being zero, so this is what makes a nonzero
prefix a meaningful state. -/
theorem one_ne_zero : (1 : ReesQuot I) ≠ zero := by
  intro h
  have := congrArg ReesQuot.val h
  rw [one_val, zero_val] at this
  exact absurd this (by simp)

instance : Monoid (ReesQuot I) where
  mul_assoc x y z := ext (by simp [rmul_assoc])
  one_mul x := ext (by simp [rmul_one_left])
  mul_one x := ext (by simp [rmul_one_right])

@[simp] lemma zero_mul (y : ReesQuot I) : (zero : ReesQuot I) * y = zero :=
  ext (by simp)

@[simp] lemma mul_zero (x : ReesQuot I) : x * (zero : ReesQuot I) = zero :=
  ext (by simp)

/-- **The projection**, collapsing the ideal to zero. -/
def proj (I : ReesIdeal M) (a : M) : ReesQuot I :=
  if h : a ∈ I.carrier then zero else cls h

@[simp] lemma proj_of_mem {a : M} (ha : a ∈ I.carrier) : proj I a = zero := dif_pos ha

@[simp] lemma proj_of_notMem {a : M} (ha : a ∉ I.carrier) : proj I a = cls ha := dif_neg ha

/-- **Unique nonzero lifts.**  Off the collapsed zero the projection is
injective, so a nonzero quotient answer names exactly one element of `M` and
reading it back costs nothing. -/
theorem proj_eq_iff_of_ne_zero {a b : M} (ha : proj I a ≠ zero) :
    proj I a = proj I b ↔ a = b := by
  constructor
  · intro h
    by_cases hb : b ∈ I.carrier
    · rw [proj_of_mem hb] at h
      exact absurd h ha
    · by_cases ha' : a ∈ I.carrier
      · exact absurd (proj_of_mem ha') ha
      · rw [proj_of_notMem ha', proj_of_notMem hb, cls, cls] at h
        have := congrArg ReesQuot.val h
        simp only at this
        exact congrArg Subtype.val (Option.some_injective _ this)
  · intro h
    rw [h]

/-- **The total nonzero lift.**  Off the collapsed zero the projection is
injective, so a nonzero class names exactly one element and reading it back
costs nothing; on zero the value is `1`, chosen only to keep the lift
**total** — an adaptive branch family is indexed by every descriptor value,
including the ones a promise excludes. -/
def lift (q : ReesQuot I) : M := q.val.elim 1 Subtype.val

@[simp] lemma lift_zero : (zero : ReesQuot I).lift = 1 := rfl

@[simp] lemma lift_one : (1 : ReesQuot I).lift = 1 := rfl

@[simp] lemma lift_cls {a : M} (ha : a ∉ I.carrier) : (cls ha).lift = a := rfl

/-- The projection is zero exactly on the ideal. -/
theorem proj_eq_zero_iff {a : M} : proj I a = zero ↔ a ∈ I.carrier := by
  by_cases ha : a ∈ I.carrier
  · exact ⟨fun _ => ha, fun _ => proj_of_mem ha⟩
  · refine ⟨fun h => ?_, fun h => absurd h ha⟩
    rw [proj_of_notMem ha] at h
    have hv := congrArg ReesQuot.val h
    rw [cls, zero_val] at hv
    exact absurd hv (by simp)

/-- **The lift is a section off zero.**  This is the free half of the fixed-apex
decoder: recovering the element a nonzero class names is an *injectivity*, not
a query. -/
theorem proj_lift {q : ReesQuot I} (hq : q ≠ zero) : proj I q.lift = q := by
  rcases hv : q.val with _ | a
  · exact absurd (ext hv) hq
  · have hl : q.lift = a.val := by simp only [lift, hv, Option.elim]
    rw [hl, proj_of_notMem a.2]
    exact ext hv.symm

/-- The other side: a class off the ideal lifts back to its own element. -/
@[simp] theorem lift_proj {a : M} (ha : proj I a ≠ zero) : (proj I a).lift = a := by
  rw [proj_of_notMem fun h => ha (proj_of_mem h)]
  rfl

/-- **The projection is multiplicative** — the quotient really is a quotient of
monoids, not merely a set with a collapsed part. -/
theorem proj_mul (a b : M) : proj I (a * b) = proj I a * proj I b := by
  by_cases ha : a ∈ I.carrier
  · rw [proj_of_mem ha, proj_of_mem (I.mul_right ha b), zero_mul]
  by_cases hb : b ∈ I.carrier
  · rw [proj_of_mem hb, proj_of_mem (I.mul_left a hb), proj_of_notMem ha, mul_zero]
  refine ext ?_
  rw [proj_of_notMem ha, proj_of_notMem hb]
  simp only [mul_val, cls, rmul_some]
  by_cases hab : a * b ∈ I.carrier
  · rw [dif_pos hab, proj_of_mem hab, zero_val]
  · rw [dif_neg hab, proj_of_notMem hab, cls]

/-- The projection sends `1` to `1`: the ideal is proper. -/
@[simp] theorem proj_one : proj I (1 : M) = 1 := by
  rw [proj_of_notMem I.one_notMem, cls]
  rfl

/-- **The projection as a monoid homomorphism** — the form the first-entry
search transports word products through. -/
def projHom (I : ReesIdeal M) : M →* ReesQuot I where
  toFun := proj I
  map_one' := proj_one
  map_mul' := proj_mul

@[simp] lemma projHom_apply (a : M) : projHom I a = proj I a := rfl

/-- **The projection is onto.**  This is where nonemptiness of the ideal is
used: without it the collapsed zero would have no preimage. -/
theorem proj_surjective (I : ReesIdeal M) : Function.Surjective (proj I) := by
  rintro ⟨_ | a⟩
  · obtain ⟨z, hz⟩ := I.carrier_nonempty
    exact ⟨z, proj_of_mem hz⟩
  · exact ⟨a.val, proj_of_notMem a.2⟩

/-- **The quotient of an aperiodic monoid is aperiodic.**  Powers stabilise
downstairs because they stabilise upstairs and `proj` is a surjective
homomorphism.  Without this the peel's recursion could not be *stated* on the
quotient: every layer of the cube-root development assumes aperiodicity. -/
instance instIsAperiodicReesQuot (I : ReesIdeal M) [IsAperiodicMonoid M] :
    IsAperiodicMonoid (ReesQuot I) where
  stabilizes q := by
    obtain ⟨a, ha⟩ := proj_surjective I q
    obtain ⟨N, hN, hstab⟩ := IsAperiodicMonoid.stabilizes a
    refine ⟨N, hN, ?_⟩
    rw [← ha, ← projHom_apply, ← map_pow, ← map_pow, hstab]

/-- **Word products transport.**  The quotient of a word's product is the
product of the quotients — routine, but it is what the first-entry search runs on. -/
theorem wordProd_proj {σ : Type} (letter : σ → M) {n : ℕ} (x : Fin n → σ) :
    wordProd (fun c => proj I (letter c)) x = proj I (wordProd letter x) := by
  rw [wordProd, wordProd, orderedProd_eq_prod_ofFn, orderedProd_eq_prod_ofFn,
    ← projHom_apply (I := I), map_list_prod, List.map_ofFn]
  simp [Function.comp_def]

/-- **The quotient cardinality.**  Collapsing the ideal to one point
removes `|I| - 1` elements, which is the peel's progress measure. -/
theorem card_reesQuot (I : ReesIdeal M) :
    Fintype.card (ReesQuot I) = Fintype.card M - I.carrier.card + 1 := by
  have hcard : Fintype.card {a : M // a ∉ I.carrier}
      = Fintype.card M - I.carrier.card := by
    rw [Fintype.card_subtype]
    rw [show (Finset.univ.filter fun a : M => a ∉ I.carrier)
        = Finset.univ \ I.carrier from by
      ext a
      simp]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  rw [Fintype.card_congr (equivOption (I := I)), Fintype.card_option, hcard]

/-! ## The ideal the peel uses

`twoIdeal apex` — the principal two-sided ideal of the apex, which contains the
apex class.  Properness is exactly `ApexCoordinate.IsProper.ideal_proper`, and
nonemptiness is free: an ideal contains its own generator. -/

/-- **The apex ideal.**  Note what it collapses: the apex class as well as
everything below it.  The `J`-coordinate the quotient discards is what items
3–6 recover. -/
def apexIdeal (c : ApexCoordinate M) (hc : c.IsProper) : ReesIdeal M where
  carrier := twoIdeal c.apex
  mul_mem := by
    intro p a ha q
    obtain ⟨u, v, huv⟩ := mem_twoIdeal.1 ha
    refine mem_twoIdeal.2 ⟨p * u, v * q, ?_⟩
    rw [← huv]
    simp only [mul_assoc]
  carrier_nonempty := ⟨c.apex, self_mem_twoIdeal c.apex⟩
  one_notMem := hc.ideal_proper

@[simp] lemma apexIdeal_carrier (c : ApexCoordinate M) (hc : c.IsProper) :
    (apexIdeal c hc).carrier = twoIdeal c.apex := rfl

/-- The apex itself is collapsed — the fact that makes the peel nontrivial. -/
theorem proj_apex_eq_zero (c : ApexCoordinate M) (hc : c.IsProper) :
    ReesQuot.proj (apexIdeal c hc) c.apex = ReesQuot.zero :=
  ReesQuot.proj_of_mem (self_mem_twoIdeal c.apex)

/-- **Exactly what is collapsed**: everything whose two-sided ideal sits inside
the apex's — the whole apex class included, not just the chosen
representative. -/
theorem proj_apexIdeal_eq_zero_iff (c : ApexCoordinate M) (hc : c.IsProper)
    {a : M} :
    ReesQuot.proj (apexIdeal c hc) a = ReesQuot.zero
      ↔ twoIdeal a ⊆ twoIdeal c.apex := by
  rw [ReesQuot.proj_eq_zero_iff, apexIdeal_carrier]
  exact ⟨twoIdeal_subset_of_mem, fun h => h (self_mem_twoIdeal a)⟩

/-- In particular the entire apex `J`-class goes to zero. -/
theorem proj_jClass_eq_zero (c : ApexCoordinate M) (hc : c.IsProper) {a : M}
    (ha : a ∈ jClass M c.apex) :
    ReesQuot.proj (apexIdeal c hc) a = ReesQuot.zero :=
  (proj_apexIdeal_eq_zero_iff c hc).2 (le_of_eq (mem_jClass.1 ha))

/-- The apex class sits inside the ideal. -/
theorem jClass_subset_apexIdeal (c : ApexCoordinate M) (hc : c.IsProper) :
    jClass M c.apex ⊆ (apexIdeal c hc).carrier := fun _ ha =>
  ReesQuot.proj_eq_zero_iff.1 (proj_jClass_eq_zero c hc ha)

/-- **The charge is carried by the ideal.**  With `card_reesQuot` this is the
carrier drop: collapsing the apex ideal removes at least
`degree² - 1` elements. -/
theorem degree_sq_le_apexIdeal_card (c : ApexCoordinate M) (hc : c.IsProper) :
    c.degree ^ 2 ≤ (apexIdeal c hc).carrier.card :=
  le_trans c.degree_sq_le (Finset.card_le_card (jClass_subset_apexIdeal c hc))

/-- **The carrier drop.**  Peeling one apex costs the carrier at least
`degree² - 1`.  Stated additively: nested `Nat` subtraction is fragile, and
this is the form the recurrence consumes. -/
theorem card_reesQuot_add_charge_le (c : ApexCoordinate M) (hc : c.IsProper) :
    Fintype.card (ReesQuot (apexIdeal c hc)) + (c.degree ^ 2 - 1)
      ≤ Fintype.card M := by
  have hcharge := degree_sq_le_apexIdeal_card c hc
  have hone : 1 ≤ (apexIdeal c hc).carrier.card :=
    Finset.card_pos.2 (apexIdeal c hc).carrier_nonempty
  have hle : (apexIdeal c hc).carrier.card ≤ Fintype.card M :=
    (apexIdeal c hc).carrier.card_le_univ.trans_eq Finset.card_univ
  rw [card_reesQuot]
  omega

/-- The form the recurrence faces: any degree strictly below the coordinate's
fits in the drop, with no subtraction anywhere. -/
theorem card_reesQuot_add_sq_le (c : ApexCoordinate M) (hc : c.IsProper)
    {t : ℕ} (ht : t < c.degree) :
    Fintype.card (ReesQuot (apexIdeal c hc)) + t ^ 2 ≤ Fintype.card M := by
  have hlt : t ^ 2 < c.degree ^ 2 := Nat.pow_lt_pow_left ht (by norm_num)
  have hmain := card_reesQuot_add_charge_le c hc
  omega

/-- **The peel's progress measure.**  A coordinate whose degree exceeds a
positive threshold drops the carrier strictly — `degree² - 1 ≥ t² ≥ 1` — which
is what makes the assembly's strong induction on `Fintype.card M` terminate. -/
theorem card_reesQuot_lt (c : ApexCoordinate M) (hc : c.IsProper) {t : ℕ}
    (ht0 : 0 < t) (ht : t < c.degree) :
    Fintype.card (ReesQuot (apexIdeal c hc)) < Fintype.card M := by
  have h := card_reesQuot_add_sq_le c hc ht
  have h1 : 1 ≤ t ^ 2 := Nat.one_le_pow 2 t ht0
  omega

end ReesQuot

end Rees

end MonoidProduct
