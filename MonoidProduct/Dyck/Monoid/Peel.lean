import MonoidProduct.Dyck.Monoid.Green
set_option linter.style.header false

/-!
# Dyck principal factors and exact apex peeling (`monoid.tex`, `prop:dyck-munn-peel`,
items 1, 2, 4)

In the coordinates `[s; i, j] = (i, s − i, j − i)` of `prop:dyck-munn-peel`
(`i = t.a`, `j = t.a + t.e`, `s = t.a + t.b`):

1. `M_k` is an inverse monoid: `[s; i, j]⁻¹ = [s; j, i]` is `invT`, with
   `mul_inv_mul`, `inv_mul_inv`, and the uniqueness `inv_unique`
   (so the inverse is unique, the defining property of an inverse monoid);
2. the level-`s` class multiplies as the Brandt semigroup of `(s+1)×(s+1)`
   matrix units: `[s; i, j]·[s; p, q] = [s; i, q]` when `j = p`
   (`live_mul_live_of_eq`) and otherwise falls strictly below level `s`
   (`lt_dyckLevel_mul_of_ne`, i.e. into `I_{s+1}`), and `|J_s| = (s+1)²`
   (`card_level`);
4. the top class peels exactly: `peelHom : M_{k+1} →* M_k` is surjective
   (`peel_surjective`), its fibre over `0` is `I_{k+1} = J_{k+1} ∪ {0}`, the
   two-sided ideal of any level-`(k+1)` element (`peel_eq_zero_iff`,
   `peel_eq_zero_iff_mem_twoIdeal`), and it is injective off that fibre
   (`peel_injOn`) — the Rees-quotient isomorphism `M_{k+1}/I_{k+1} ≅ M_k`;
   `card_dyckNF_succ` is `|M_{k+1}| − |M_k| = (k+2)²`.

Item 3 (`ℚ₀[M_k]` semisimple, one `M_{s+1}(ℚ)` block per level) is in
`Dyck/Monoid/Algebra.lean` (`dyckContractedEquiv`, `jacobson_dyckContracted`), and the
sandwich-rank form `d_{J_s} = s + 1` of item 2 is in `Dyck/Monoid/Sandwich.lean`.
-/

namespace MonoidProduct

open DyckNF DyckTriple

variable {k : ℕ}

/-! ## Products in coordinates -/

/-- A live product with prescribed coordinates. -/
lemma live_mul_live_eq {t₁ t₂ u : DyckTriple k}
    (ha : max (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e) = u.a)
    (hb : max (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e) = u.b) (he : t₁.e + t₂.e = u.e) :
    (DyckNF.live t₁ : DyckNF k) * DyckNF.live t₂ = DyckNF.live u := by
  have hk : max (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e) + max (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e) ≤ k := by
    rw [ha, hb]; exact_mod_cast u.budget
  rw [live_mul_live, DyckTriple.comp_of_le _ _ hk]
  congr 1
  refine DyckTriple.ext ?_ ?_ he
  · rw [compT_a]; omega
  · rw [compT_b]; omega

/-- The level of a live product, in both branches. -/
lemma dyckLevel_live_mul_live (t₁ t₂ : DyckTriple k) :
    dyckLevel (DyckNF.live t₁ * DyckNF.live t₂)
      = if max (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e) + max (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e) ≤ k then
          (max (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e)).toNat + (max (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e)).toNat
        else k + 1 := by
  rw [live_mul_live]
  unfold DyckTriple.comp
  split_ifs with hk
  · rw [dyckLevel_live, compT_a, compT_b]
  · rfl

/-! ## Item 1: the inverse -/

/-- `[s; i, j]⁻¹ = [s; j, i]`: the triple `(a + e, b − e, −e)`. -/
def DyckTriple.invT (t : DyckTriple k) : DyckTriple k :=
  ⟨((t.a : ℤ) + t.e).toNat, ((t.b : ℤ) - t.e).toNat, -t.e,
    by have := t.budget; have := t.lower; have := t.upper; omega,
    by have := t.lower; omega,
    by have := t.upper; omega⟩

@[simp] lemma invT_a (t : DyckTriple k) : (t.invT).a = ((t.a : ℤ) + t.e).toNat := rfl
@[simp] lemma invT_b (t : DyckTriple k) : (t.invT).b = ((t.b : ℤ) - t.e).toNat := rfl
@[simp] lemma invT_e (t : DyckTriple k) : (t.invT).e = -t.e := rfl

/-- The inverse of a normal form. -/
def DyckNF.inv : DyckNF k → DyckNF k
  | .zero => .zero
  | .live t => .live t.invT

@[simp] lemma inv_zero : DyckNF.inv (DyckNF.zero : DyckNF k) = DyckNF.zero := rfl
@[simp] lemma inv_live (t : DyckTriple k) : DyckNF.inv (DyckNF.live t) = DyckNF.live t.invT := rfl

/-- The idempotent `[s; i, i]` at the domain of `t`. -/
def DyckTriple.domT (t : DyckTriple k) : DyckTriple k :=
  ⟨t.a, t.b, 0, t.budget, by simp, by simp⟩

lemma live_mul_inv (t : DyckTriple k) :
    (DyckNF.live t : DyckNF k) * DyckNF.live t.invT = DyckNF.live t.domT := by
  have := t.lower; have := t.upper
  refine live_mul_live_eq ?_ ?_ ?_ <;> simp [DyckTriple.domT] <;> omega

lemma inv_mul_live (t : DyckTriple k) :
    (DyckNF.live t.invT : DyckNF k) * DyckNF.live t = DyckNF.live t.invT.domT := by
  have := t.lower; have := t.upper
  refine live_mul_live_eq ?_ ?_ ?_ <;> simp [DyckTriple.domT]

lemma dom_mul_live (t : DyckTriple k) :
    (DyckNF.live t.domT : DyckNF k) * DyckNF.live t = DyckNF.live t := by
  refine live_mul_live_eq ?_ ?_ ?_ <;> simp [DyckTriple.domT]

/-- **`x·x⁻¹·x = x`.** -/
theorem mul_inv_mul (x : DyckNF k) : x * x.inv * x = x := by
  cases x with
  | zero => rfl
  | live t => rw [inv_live, live_mul_inv, dom_mul_live]

/-- **`x⁻¹·x·x⁻¹ = x⁻¹`.** -/
theorem inv_mul_inv (x : DyckNF k) : x.inv * x * x.inv = x.inv := by
  cases x with
  | zero => rfl
  | live t => rw [inv_live, inv_mul_live, dom_mul_live]

theorem inv_inv (x : DyckNF k) : x.inv.inv = x := by
  cases x with
  | zero => rfl
  | live t =>
      rw [inv_live, inv_live]
      congr 1
      have := t.lower; have := t.upper
      refine DyckTriple.ext ?_ ?_ ?_ <;> simp <;> omega

/-- A product equal to a live element has live factors, with the coordinate
relations of `compT`. -/
lemma of_mul_eq_live {x y : DyckNF k} {u : DyckTriple k} (h : x * y = DyckNF.live u) :
    ∃ t₁ t₂ : DyckTriple k, x = DyckNF.live t₁ ∧ y = DyckNF.live t₂ ∧
      (max (t₁.a : ℤ) ((t₂.a : ℤ) - t₁.e)).toNat = u.a ∧
      (max (t₁.b : ℤ) ((t₂.b : ℤ) + t₁.e)).toNat = u.b ∧ t₁.e + t₂.e = u.e := by
  cases x with
  | zero => exact absurd h (by simp)
  | live t₁ =>
      cases y with
      | zero => exact absurd h (by simp)
      | live t₂ =>
          refine ⟨t₁, t₂, rfl, rfl, ?_⟩
          rw [live_mul_live] at h
          unfold DyckTriple.comp at h
          split_ifs at h with hk
          · have h' := DyckNF.live.inj h
            rw [← h']
            exact ⟨compT_a _ _ hk, compT_b _ _ hk, rfl⟩

/-- **Uniqueness of the inverse**: `M_k` is an inverse monoid. -/
theorem inv_unique {x y : DyckNF k} (h1 : x * y * x = x) (h2 : y * x * y = y) : y = x.inv := by
  cases x with
  | zero =>
      rw [DyckNF.mul_zero_eq, DyckNF.zero_mul_eq] at h2
      rw [← h2]; rfl
  | live t =>
      -- `x y x = x` in coordinates
      obtain ⟨p, t₂, hp, ht2, ha, hb, he⟩ := of_mul_eq_live h1
      rw [← DyckNF.live.inj ht2] at ha hb he
      obtain ⟨t₁, u, h₁, hy, ha1, hb1, he1⟩ := of_mul_eq_live hp
      rw [← DyckNF.live.inj h₁] at ha1 hb1 he1
      subst hy
      -- `y x y = y` in coordinates
      obtain ⟨q, u₂, hq, hu2, ha', hb', he'⟩ := of_mul_eq_live h2
      rw [← DyckNF.live.inj hu2] at ha' hb' he'
      obtain ⟨u₁, t₃, h₂, ht3, ha2, hb2, he2⟩ := of_mul_eq_live hq
      rw [← DyckNF.live.inj h₂] at ha2 hb2 he2
      rw [← DyckNF.live.inj ht3] at ha2 hb2 he2
      rw [inv_live]
      congr 1
      have := t.lower; have := t.upper; have := u.lower; have := u.upper
      refine DyckTriple.ext ?_ ?_ ?_ <;> simp only [invT_a, invT_b, invT_e] <;> omega

/-! ## Item 2: the Brandt principal factor -/

/-- **Matrix units**: `[s; i, j]·[s; p, q] = [s; i, q]` when `j = p`. -/
theorem live_mul_live_of_eq {t t' : DyckTriple k} (hs : t.a + t.b = t'.a + t'.b)
    (hj : (t.a : ℤ) + t.e = t'.a) :
    (DyckNF.live t : DyckNF k) * DyckNF.live t'
      = DyckNF.live ⟨t.a, t.b, t.e + t'.e, t.budget,
          by have := t.lower; have := t'.lower; omega,
          by have := t'.upper; omega⟩ := by
  refine live_mul_live_eq ?_ ?_ rfl <;> simp <;> omega

/-- **Off the diagonal the product drops a level**: `[s; i, j]·[s; p, q] ∈ I_{s+1}`
when `j ≠ p`. -/
theorem lt_dyckLevel_mul_of_ne {t t' : DyckTriple k} (hs : t.a + t.b = t'.a + t'.b)
    (hj : (t.a : ℤ) + t.e ≠ t'.a) :
    t.a + t.b < dyckLevel (DyckNF.live t * DyckNF.live t') := by
  rw [dyckLevel_live_mul_live]
  have := t.budget
  split_ifs with hk <;> omega

/-- The coordinates `(i, j)` of a level-`s` triple. -/
def levelCoord {s : ℕ} (t : {t : DyckTriple k // t.a + t.b = s}) : Fin (s + 1) × Fin (s + 1) :=
  (Fin.mk t.1.a (by have h := t.2; omega),
    Fin.mk ((t.1.a : ℤ) + t.1.e).toNat
      (by have h := t.2; have := t.1.upper; have := t.1.lower; omega))

/-- The level-`s` triple `[s; i, j]`. -/
def levelTriple {s : ℕ} (hs : s ≤ k) (p : Fin (s + 1) × Fin (s + 1)) :
    {t : DyckTriple k // t.a + t.b = s} :=
  ⟨⟨(p.1 : ℕ), s - (p.1 : ℕ), ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ),
      by have := p.1.isLt; omega, by omega, by have := p.1.isLt; have := p.2.isLt; omega⟩,
    by have := p.1.isLt; change (p.1 : ℕ) + (s - (p.1 : ℕ)) = s; omega⟩

/-- The level-`s` class in the coordinates `(i, j)`. -/
def levelEquiv {s : ℕ} (hs : s ≤ k) :
    {t : DyckTriple k // t.a + t.b = s} ≃ Fin (s + 1) × Fin (s + 1) where
  toFun := levelCoord
  invFun := levelTriple hs
  left_inv t := by
    apply Subtype.ext
    have := t.2; have := t.1.lower
    refine DyckTriple.ext rfl ?_ ?_
    · change s - t.1.a = t.1.b; omega
    · change ((((t.1.a : ℤ) + t.1.e).toNat : ℕ) : ℤ) - ((t.1.a : ℕ) : ℤ) = t.1.e; omega
  right_inv p := by
    have := p.1.isLt; have := p.2.isLt
    refine Prod.ext (Fin.ext rfl) (Fin.ext ?_)
    change ((((p.1 : ℕ) : ℤ) + (((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ))).toNat) = (p.2 : ℕ)
    omega

/-- **`|J_s| = (s+1)²`.** -/
theorem card_level {s : ℕ} (hs : s ≤ k) :
    Fintype.card {t : DyckTriple k // t.a + t.b = s} = (s + 1) ^ 2 := by
  rw [Fintype.card_congr (levelEquiv hs), Fintype.card_prod, Fintype.card_fin, sq]

/-! ## Item 4: exact apex peeling `M_{k+1} → M_k` -/

/-- A triple of level at most `k` in `M_{k+1}`, read in `M_k`. -/
def DyckTriple.peelT (t : DyckTriple (k + 1)) (h : t.a + t.b ≤ k) : DyckTriple k :=
  ⟨t.a, t.b, t.e, h, t.lower, t.upper⟩

@[simp] lemma peelT_a (t : DyckTriple (k + 1)) (h) : (t.peelT h).a = t.a := rfl
@[simp] lemma peelT_b (t : DyckTriple (k + 1)) (h) : (t.peelT h).b = t.b := rfl
@[simp] lemma peelT_e (t : DyckTriple (k + 1)) (h) : (t.peelT h).e = t.e := rfl

/-- **The peel**: the identity on levels `≤ k`, zero on `I_{k+1} = J_{k+1} ∪ {0}`. -/
def peel : DyckNF (k + 1) → DyckNF k
  | .zero => .zero
  | .live t => if h : t.a + t.b ≤ k then .live (t.peelT h) else .zero

@[simp] lemma peel_zero : peel (DyckNF.zero : DyckNF (k + 1)) = DyckNF.zero := rfl

lemma peel_live_of_le {t : DyckTriple (k + 1)} (h : t.a + t.b ≤ k) :
    peel (DyckNF.live t) = DyckNF.live (t.peelT h) := dif_pos h

lemma peel_live_of_lt {t : DyckTriple (k + 1)} (h : k < t.a + t.b) :
    peel (DyckNF.live t) = DyckNF.zero := dif_neg (by omega)

lemma peel_eq_zero_of_le {x : DyckNF (k + 1)} (h : k + 1 ≤ dyckLevel x) :
    peel x = DyckNF.zero := by
  cases x with
  | zero => rfl
  | live t => exact peel_live_of_lt (by rw [dyckLevel_live] at h; omega)

/-- **The fibre over zero is `I_{k+1}`**: the levels `≥ k + 1`. -/
theorem peel_eq_zero_iff (x : DyckNF (k + 1)) :
    peel x = DyckNF.zero ↔ k + 1 ≤ dyckLevel x := by
  refine ⟨fun h => ?_, peel_eq_zero_of_le⟩
  cases x with
  | zero => rw [dyckLevel_zero]; omega
  | live t =>
      by_contra hlt
      rw [dyckLevel_live] at hlt
      rw [peel_live_of_le (t := t) (by omega)] at h
      exact absurd h (by simp)

/-- **`M¹ J_{k+1} M¹ = I_{k+1}`**: the fibre over zero is the two-sided ideal of any
level-`(k+1)` element. -/
theorem peel_eq_zero_iff_mem_twoIdeal {x : DyckNF (k + 1)} (hx : dyckLevel x = k + 1)
    (y : DyckNF (k + 1)) : peel y = DyckNF.zero ↔ y ∈ twoIdeal x := by
  rw [peel_eq_zero_iff, mem_twoIdeal_iff_dyckLevel, hx]

theorem peel_one : peel (1 : DyckNF (k + 1)) = 1 := by
  rw [one_def, peel_live_of_le (by change 0 + 0 ≤ k; omega)]
  rfl

/-- **The peel is multiplicative**: the composition formula does not see the
depth bound except through the survival test. -/
theorem peel_mul (x y : DyckNF (k + 1)) : peel (x * y) = peel x * peel y := by
  cases x with
  | zero => rw [DyckNF.zero_mul_eq, peel_zero, DyckNF.zero_mul_eq]
  | live t =>
      cases y with
      | zero => rw [DyckNF.mul_zero_eq, peel_zero, DyckNF.mul_zero_eq]
      | live t' =>
          by_cases ht : t.a + t.b ≤ k
          · by_cases ht' : t'.a + t'.b ≤ k
            · rw [peel_live_of_le ht, peel_live_of_le ht', live_mul_live, live_mul_live]
              unfold DyckTriple.comp
              have hlo := t.lower; have hup := t.upper
              have hlo' := t'.lower; have hup' := t'.upper
              split_ifs with h1 h2
              · -- both survive: the same coordinates
                rw [peel_live_of_le (by
                  rw [compT_a, compT_b]; simp only [peelT_a, peelT_b, peelT_e] at h2; omega)]
                congr 1
              · -- the product sits at level `k + 1`
                exact peel_live_of_lt (by
                  rw [compT_a, compT_b]; simp only [peelT_a, peelT_b, peelT_e] at h2; omega)
              · exfalso
                simp only [peelT_a, peelT_b, peelT_e] at *
                push_cast at *
                omega
              · rfl
            · rw [peel_live_of_lt (t := t') (by omega), DyckNF.mul_zero_eq]
              apply peel_eq_zero_of_le
              calc k + 1 ≤ dyckLevel (DyckNF.live t') := by rw [dyckLevel_live]; omega
                _ ≤ _ := dyckLevel_le_mul_right _ _
          · rw [peel_live_of_lt (t := t) (by omega), DyckNF.zero_mul_eq]
            apply peel_eq_zero_of_le
            calc k + 1 ≤ dyckLevel (DyckNF.live t) := by rw [dyckLevel_live]; omega
              _ ≤ _ := dyckLevel_le_mul_left _ _

/-- **The apex peel as a monoid homomorphism** `M_{k+1} →* M_k`. -/
def peelHom (k : ℕ) : DyckNF (k + 1) →* DyckNF k where
  toFun := peel
  map_one' := peel_one
  map_mul' := peel_mul

theorem peel_surjective : Function.Surjective (peel : DyckNF (k + 1) → DyckNF k) := by
  intro y
  cases y with
  | zero => exact ⟨.zero, rfl⟩
  | live u =>
      refine ⟨.live ⟨u.a, u.b, u.e, by have := u.budget; omega, u.lower, u.upper⟩, ?_⟩
      rw [peel_live_of_le (t := ⟨u.a, u.b, u.e, by have := u.budget; omega, u.lower, u.upper⟩)
        u.budget]
      rfl

/-- **Injective off the fibre**: distinct surviving elements stay distinct. -/
theorem peel_injOn {x y : DyckNF (k + 1)} (hx : dyckLevel x ≤ k) (hy : dyckLevel y ≤ k)
    (h : peel x = peel y) : x = y := by
  cases x with
  | zero => rw [dyckLevel_zero] at hx; omega
  | live t =>
      cases y with
      | zero => rw [dyckLevel_zero] at hy; omega
      | live t' =>
          rw [dyckLevel_live] at hx hy
          rw [peel_live_of_le hx, peel_live_of_le hy] at h
          have h' := DyckNF.live.inj h
          have ha := congrArg DyckTriple.a h'
          have hb := congrArg DyckTriple.b h'
          have he := congrArg DyckTriple.e h'
          congr 1
          exact DyckTriple.ext ha hb he

/-- **`|M_{k+1}| − |M_k| = (k+2)²`**, the size of the peeled class. -/
theorem card_dyckNF_succ (k : ℕ) :
    Fintype.card (DyckNF (k + 1)) = Fintype.card (DyckNF k) + (k + 2) ^ 2 := by
  rw [card_dyckNF_sum, card_dyckNF_sum, Finset.sum_range_succ]
  ring

end MonoidProduct
