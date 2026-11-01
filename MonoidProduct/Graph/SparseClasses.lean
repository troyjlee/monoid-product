import MonoidProduct.Graph.Mader
import MonoidProduct.Graph.Outerplanar
import MonoidProduct.Graph.PlanarCertificate
import MonoidProduct.Graph.Surface
import MonoidProduct.Graph.Treewidth
set_option linter.style.header false

/-!
# Certificates for the sparse graph classes

`monoid.tex`, section `sec:graph-certificates`, paragraph "Planarity and minor-closed
properties": every fixed proper minor-closed graph class `P` has `b_P = O_P(v)` and
`Q_list(P; n) = O_P(min{n, √(nv)})`, with outerplanarity, embeddability in a fixed surface and
treewidth at most a fixed constant as examples; and the row of `tab:graph-certificates` for
minor-closed properties, `Q_matrix = O_P(v^{3/2})`.  Write `v = #V` and `N = C(v, 2)`.

* `strongCertificateSize_le_mul_of_linear`: a property whose members on `V` have at most `C·v`
  edges has `b_P ≤ (C + 1)·v`, by `prop:sparse-certificates`.
* `minorClosed_strongCertificateSize_le_linear`: for a proper minor-closed class `P`, a constant
  `C` with `b_P ≤ C·v` for every finite vertex type, from Mader's theorem
  (`IsMinorClosed.exists_ncard_edgeSet_le`).  The classes without a `K_t` minor are an instance
  (`isMinorClosed_not_isMinor_top`).
* `outerplanarity_strongCertificateSize_le`: `≤ min{N, 2v − 2}`, from `|E| ≤ 2v − 3`.
* `treewidth_strongCertificateSize_le`: `≤ min{N, t·v + 1}`, from `|E| ≤ t·v`.
* `surfaceEmbedding_strongCertificateSize_le`: Euler genus at most `k`, `≤ (3k + 4)·v`, from
  `|E| ≤ 3v − 6 + 3k`; every fixed surface, orientable or not, has some Euler genus `k`.  The
  orientable genus `g` gives `≤ (6g + 4)·v` (`genus_strongCertificateSize_le`).
* The query bounds: `Q_list ≤ min{n, 2^18·√(n·C·v)}` and `Q_matrix ≤ 2^18·√C·v·√v` for the
  constants above.

Each bound is linear in `v` with a constant depending only on the class.  The linear bounds for
outerplanarity, surfaces and treewidth are proved directly from their edge bounds; that these
classes are minor-closed is not needed and not proved.
-/

namespace MonoidProduct.Graph

open QuantumQueryComplexity Certificates SimpleGraph

/-! ## Linear edge bounds give linear certificates -/

section Linear

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Linear edge bounds give linear certificate sizes**: if the members of `P` on `V` have at
most `C·v` edges, then `b_P ≤ (C + 1)·v`. -/
theorem strongCertificateSize_le_mul_of_linear (P : SimpleGraph V → Prop) [DecidablePred P]
    {C : ℕ} (hP : ∀ G, P G → G.edgeSet.ncard ≤ C * Fintype.card V) :
    strongCertificateSize (fun S : Finset (Edge V) => decide (P (toGraph S))) ≤
      (C + 1) * Fintype.card V := by
  have h := sparseYes_strongCertificateSize_le P hP
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hv | hv
  · rw [hv] at h ⊢
    simpa using h
  · refine h.trans ((min_le_right _ _).trans ?_)
    nlinarith

end Linear

/-! ## Proper minor-closed classes -/

/-- **A class as an output** on the edge sets over `V`: whether `toGraph S` belongs to `P`. -/
noncomputable def classIndicator (P : ∀ V : Type, SimpleGraph V → Prop) (V : Type)
    (S : Finset (Edge V)) : Bool := by
  classical exact decide (P V (toGraph S))

theorem classIndicator_eq_true_iff {P : ∀ V : Type, SimpleGraph V → Prop} {V : Type}
    {S : Finset (Edge V)} : classIndicator P V S = true ↔ P V (toGraph S) := by
  simp [classIndicator]

/-- **Proper minor-closed classes** (`sec:graph-certificates`): a constant `C`, depending only on
the class, with `b_P ≤ C·v` on every finite vertex type. -/
theorem minorClosed_strongCertificateSize_le_linear {P : ∀ V : Type, SimpleGraph V → Prop}
    (hP : IsMinorClosed P) (hprop : IsProperClass P) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V],
      strongCertificateSize (classIndicator P V) ≤ C * Fintype.card V := by
  classical
  obtain ⟨C, hC⟩ := hP.exists_ncard_edgeSet_le hprop
  refine ⟨C + 1, fun V _ _ => ?_⟩
  have heq : classIndicator P V = fun S : Finset (Edge V) => decide (P V (toGraph S)) :=
    funext fun S => Bool.eq_iff_iff.mpr (by rw [classIndicator_eq_true_iff, decide_eq_true_iff])
  rw [heq]
  exact strongCertificateSize_le_mul_of_linear (P V) fun G hG => hC V G hG

/-- **Excluding a complete minor** is a proper minor-closed class. -/
theorem isMinorClosed_not_isMinor_top (t : ℕ) :
    IsMinorClosed fun _ G => ¬IsMinor (⊤ : SimpleGraph (Fin t)) G :=
  fun hHG hG hK => hG (hK.trans hHG)

theorem isProperClass_not_isMinor_top (t : ℕ) :
    IsProperClass fun _ G => ¬IsMinor (⊤ : SimpleGraph (Fin t)) G :=
  ⟨Fin t, inferInstance, ⊤, fun h => h (IsMinor.refl _)⟩

/-! ## Outerplanarity, treewidth and surfaces -/

section Classes

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Outerplanarity** of `toGraph S`. -/
noncomputable def isOuterplanar (S : Finset (Edge V)) : Bool := by
  classical exact decide (IsOuterplanar (toGraph S))

/-- **Treewidth at most `t`** of `toGraph S`. -/
noncomputable def hasTreewidthLE (t : ℕ) (S : Finset (Edge V)) : Bool := by
  classical exact decide (TreewidthLE t (toGraph S))

/-- **Euler genus at most `k`** of `toGraph S`: an embedding in a surface of Euler genus at most
`k`. -/
noncomputable def hasEulerGenusLE (k : ℕ) (S : Finset (Edge V)) : Bool := by
  classical exact decide (EulerGenusLE (toGraph S) k)

/-- **Orientable genus at most `g`** of `toGraph S`. -/
noncomputable def hasGenusLE (g : ℕ) (S : Finset (Edge V)) : Bool := by
  classical exact decide (GenusLE (toGraph S) g)

omit [Fintype V] [DecidableEq V] in
theorem isOuterplanar_eq_true_iff {S : Finset (Edge V)} :
    isOuterplanar S = true ↔ IsOuterplanar (toGraph S) := by
  simp [isOuterplanar]

omit [Fintype V] [DecidableEq V] in
theorem hasTreewidthLE_eq_true_iff {t : ℕ} {S : Finset (Edge V)} :
    hasTreewidthLE t S = true ↔ TreewidthLE t (toGraph S) := by
  simp [hasTreewidthLE]

omit [Fintype V] [DecidableEq V] in
theorem hasEulerGenusLE_eq_true_iff {k : ℕ} {S : Finset (Edge V)} :
    hasEulerGenusLE k S = true ↔ EulerGenusLE (toGraph S) k := by
  simp [hasEulerGenusLE]

omit [Fintype V] [DecidableEq V] in
theorem hasGenusLE_eq_true_iff {g : ℕ} {S : Finset (Edge V)} :
    hasGenusLE g S = true ↔ GenusLE (toGraph S) g := by
  simp [hasGenusLE]

omit [Fintype V] in
/-- A Boolean output that is the decision of `P` has the certificate size of that decision. -/
private theorem strongCertificateSize_congr_decide {P : SimpleGraph V → Prop} [DecidablePred P]
    {f : Finset (Edge V) → Bool} (hf : ∀ S, f S = true ↔ P (toGraph S)) :
    strongCertificateSize f =
      strongCertificateSize (fun S : Finset (Edge V) => decide (P (toGraph S))) := by
  congr 1
  funext S
  exact Bool.eq_iff_iff.mpr ((hf S).trans decide_eq_true_iff.symm)

/-- **Outerplanarity** (`sec:graph-certificates`): `b ≤ min{C(v, 2), 2v − 2}`. -/
theorem outerplanarity_strongCertificateSize_le :
    strongCertificateSize (isOuterplanar (V := V)) ≤
      min ((Fintype.card V).choose 2) (2 * Fintype.card V - 2) := by
  classical
  rw [strongCertificateSize_congr_decide (P := IsOuterplanar) fun S => isOuterplanar_eq_true_iff]
  by_cases hv : 2 ≤ Fintype.card V
  · have h := sparseYes_strongCertificateSize_le (V := V) IsOuterplanar
      (L := 2 * Fintype.card V - 3) fun G hG => hG.ncard_edgeSet_le hv
    rwa [show 2 * Fintype.card V - 3 + 1 = 2 * Fintype.card V - 2 by omega] at h
  · have hcap := strongCertificateSize_le_card
      (fun S : Finset (Edge V) => decide (IsOuterplanar (toGraph S)))
    rw [card_edge] at hcap
    refine hcap.trans (le_min le_rfl ?_)
    rcases (show Fintype.card V = 0 ∨ Fintype.card V = 1 by omega) with h | h <;> rw [h] <;>
      decide

/-- **Outerplanarity, linearly**: `b ≤ 2v`. -/
theorem outerplanarity_strongCertificateSize_le_linear :
    strongCertificateSize (isOuterplanar (V := V)) ≤ 2 * Fintype.card V :=
  outerplanarity_strongCertificateSize_le.trans ((min_le_right _ _).trans (Nat.sub_le _ _))

/-- **Treewidth at most `t`** (`sec:graph-certificates`): `b ≤ min{C(v, 2), t·v + 1}`. -/
theorem treewidth_strongCertificateSize_le (t : ℕ) :
    strongCertificateSize (hasTreewidthLE (V := V) t) ≤
      min ((Fintype.card V).choose 2) (t * Fintype.card V + 1) := by
  classical
  rw [strongCertificateSize_congr_decide (P := TreewidthLE t)
    fun S => hasTreewidthLE_eq_true_iff]
  exact sparseYes_strongCertificateSize_le (V := V) (TreewidthLE t) fun G hG => hG.ncard_edgeSet_le

/-- **Treewidth at most `t`, linearly**: `b ≤ (t + 1)·v`. -/
theorem treewidth_strongCertificateSize_le_linear (t : ℕ) :
    strongCertificateSize (hasTreewidthLE (V := V) t) ≤ (t + 1) * Fintype.card V := by
  classical
  rw [strongCertificateSize_congr_decide (P := TreewidthLE t)
    fun S => hasTreewidthLE_eq_true_iff]
  exact strongCertificateSize_le_mul_of_linear (TreewidthLE t) fun G hG => hG.ncard_edgeSet_le

omit [DecidableEq V] in
/-- Euler genus at most `k` gives at most `(3k + 3)·v` edges, for every `v`. -/
theorem EulerGenusLE.ncard_edgeSet_le_mul {G : SimpleGraph V} {k : ℕ} (h : EulerGenusLE G k) :
    G.edgeSet.ncard ≤ (3 * k + 3) * Fintype.card V := by
  by_cases hv : 3 ≤ Fintype.card V
  · have hE := h.ncard_edgeSet_le hv
    have hk : 3 * k ≤ 3 * k * Fintype.card V := Nat.le_mul_of_pos_right _ (by omega)
    calc G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 + 3 * k := hE
      _ ≤ 3 * Fintype.card V + 3 * k * Fintype.card V := by omega
      _ = (3 * k + 3) * Fintype.card V := by ring
  · -- At most two vertices: at most one edge.
    classical
    have hE : G.edgeSet.ncard ≤ (Fintype.card V).choose 2 := by
      rw [← coe_edgeFinset, Set.ncard_coe_finset]
      exact card_edgeFinset_le_card_choose_two
    have hc : (Fintype.card V).choose 2 ≤ Fintype.card V := by
      rcases (show Fintype.card V = 0 ∨ Fintype.card V = 1 ∨ Fintype.card V = 2 by omega)
        with h | h | h <;> rw [h] <;> decide
    calc G.edgeSet.ncard ≤ Fintype.card V := hE.trans hc
      _ ≤ (3 * k + 3) * Fintype.card V := Nat.le_mul_of_pos_left _ (by omega)

/-- **Embeddability in a fixed surface** (`sec:graph-certificates`): for Euler genus at most
`k`, `b ≤ (3k + 4)·v`. -/
theorem surfaceEmbedding_strongCertificateSize_le (k : ℕ) :
    strongCertificateSize (hasEulerGenusLE (V := V) k) ≤ (3 * k + 4) * Fintype.card V := by
  classical
  rw [strongCertificateSize_congr_decide (P := fun G => EulerGenusLE G k)
    fun S => hasEulerGenusLE_eq_true_iff]
  exact strongCertificateSize_le_mul_of_linear (fun G => EulerGenusLE G k)
    fun G hG => hG.ncard_edgeSet_le_mul

/-- **The orientable surface of genus `g`**: `b ≤ (6g + 4)·v`. -/
theorem genus_strongCertificateSize_le (g : ℕ) :
    strongCertificateSize (hasGenusLE (V := V) g) ≤ (6 * g + 4) * Fintype.card V := by
  classical
  rw [strongCertificateSize_congr_decide (P := fun G => GenusLE G g)
    fun S => hasGenusLE_eq_true_iff]
  refine strongCertificateSize_le_mul_of_linear (C := 6 * g + 3) (fun G => GenusLE G g)
    fun G hG => ?_
  have := hG.eulerGenusLE.ncard_edgeSet_le_mul
  rw [show 3 * (2 * g) + 3 = 6 * g + 3 by ring] at this
  exact this

end Classes

/-! ## Examples -/

/-- **`K₄` has orientable genus `0`**, being planar. -/
theorem genusLE_zero_top_four : GenusLE (⊤ : SimpleGraph (Fin 4)) 0 :=
  isPlanar_top_four.genusLE_zero

/-- **`K₅` does not have Euler genus `0`**: it has `10 > 3·5 − 6` edges. -/
theorem not_eulerGenusLE_zero_top_five : ¬EulerGenusLE (⊤ : SimpleGraph (Fin 5)) 0 := fun h => by
  have := h.ncard_edgeSet_le (by simp)
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin] at this
  exact absurd this (by decide)

/-- **Graphs without edges have Euler genus `0`.** -/
theorem eulerGenusLE_zero_bot {V : Type*} [Finite V] : EulerGenusLE (⊥ : SimpleGraph V) 0 :=
  isPlanar_bot.genusLE_zero.eulerGenusLE

/-! ## Query bounds -/

section Queries

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Proper minor-closed classes from an edge list** (`sec:graph-certificates`): a constant `C`,
depending only on the class, with `Q_list(P; n) ≤ min{n, 2^18·√(n·C·v)}`, the paper's
`O_P(min{n, √(nv)})`, and `Q_matrix(P) ≤ 2^18·√C·v·√v`, the `O_P(v^{3/2})` of
`tab:graph-certificates`. -/
theorem minorClosed_query_le {P : ∀ V : Type, SimpleGraph V → Prop} (hP : IsMinorClosed P)
    (hprop : IsProperClass P) :
    ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (n : ℕ),
      (qList (classIndicator P V) n : ℝ) ≤
          min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (C * Fintype.card V : ℕ))) ∧
        (qMatrix (classIndicator P V) : ℝ) ≤
          2 ^ 18 * Real.sqrt C * Fintype.card V * Real.sqrt (Fintype.card V) := by
  obtain ⟨C, hC⟩ := minorClosed_strongCertificateSize_le_linear hP hprop
  refine ⟨C, fun V _ _ n => ⟨qList_le_min_sqrt_of_le (hC V) n, ?_⟩⟩
  refine (qMatrix_le_mul_sqrt_of_le (hC V)).trans (le_of_eq ?_)
  push_cast
  rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  ring

/-- `Q_matrix ≤ 2^18·√C·v·√v` from a certificate bound `C·v`. -/
private theorem qMatrix_le_of_le_mul {f : Finset (Edge V) → Bool} {C : ℕ}
    (h : strongCertificateSize f ≤ C * Fintype.card V) :
    (qMatrix f : ℝ) ≤ 2 ^ 18 * Real.sqrt C * Fintype.card V * Real.sqrt (Fintype.card V) := by
  refine (qMatrix_le_mul_sqrt_of_le h).trans (le_of_eq ?_)
  push_cast
  rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  ring

/-- **Outerplanarity from an edge list and from an adjacency matrix**:
`Q_list ≤ min{n, 2^18·√(n(2v − 2))}` and `Q_matrix ≤ 2^18·√2·v·√v`. -/
theorem outerplanarity_query_le (n : ℕ) :
    (qList (isOuterplanar (V := V)) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (2 * Fintype.card V - 2 : ℕ))) ∧
      (qMatrix (isOuterplanar (V := V)) : ℝ) ≤
        2 ^ 18 * Real.sqrt 2 * Fintype.card V * Real.sqrt (Fintype.card V) :=
  ⟨qList_le_min_sqrt_of_le (outerplanarity_strongCertificateSize_le.trans (min_le_right _ _)) n,
    by exact_mod_cast qMatrix_le_of_le_mul outerplanarity_strongCertificateSize_le_linear⟩

/-- **Treewidth at most `t` from an edge list and from an adjacency matrix**:
`Q_list ≤ min{n, 2^18·√(n(t·v + 1))}` and `Q_matrix ≤ 2^18·√(t + 1)·v·√v`. -/
theorem treewidth_query_le (t n : ℕ) :
    (qList (hasTreewidthLE (V := V) t) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * (t * Fintype.card V + 1 : ℕ))) ∧
      (qMatrix (hasTreewidthLE (V := V) t) : ℝ) ≤
        2 ^ 18 * Real.sqrt (t + 1) * Fintype.card V * Real.sqrt (Fintype.card V) :=
  ⟨qList_le_min_sqrt_of_le ((treewidth_strongCertificateSize_le t).trans (min_le_right _ _)) n,
    by exact_mod_cast qMatrix_le_of_le_mul (treewidth_strongCertificateSize_le_linear t)⟩

/-- **Euler genus at most `k` from an edge list and from an adjacency matrix**:
`Q_list ≤ min{n, 2^18·√(n(3k + 4)v)}` and `Q_matrix ≤ 2^18·√(3k + 4)·v·√v`. -/
theorem surfaceEmbedding_query_le (k n : ℕ) :
    (qList (hasEulerGenusLE (V := V) k) n : ℝ)
        ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt (n * ((3 * k + 4) * Fintype.card V : ℕ))) ∧
      (qMatrix (hasEulerGenusLE (V := V) k) : ℝ) ≤
        2 ^ 18 * Real.sqrt (3 * k + 4) * Fintype.card V * Real.sqrt (Fintype.card V) :=
  ⟨qList_le_min_sqrt_of_le (surfaceEmbedding_strongCertificateSize_le k) n,
    by exact_mod_cast qMatrix_le_of_le_mul (surfaceEmbedding_strongCertificateSize_le k)⟩

end Queries

end MonoidProduct.Graph
