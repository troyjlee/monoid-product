import MonoidProduct.Certificates.Quantum
import MonoidProduct.Matroid.Certificates
set_option linter.style.header false

/-!
# Acceptance statements for strong certificates

The paper-facing statements of `monoid.tex`, section `sec:strong-certificates`, and of the
certificate interpretation of section `sec:matroid-bases`, restated with the definitions
unfolded where that makes their meaning visible, followed by small sanity checks.  Every
`example` here is checked by Lean against the library's statement.

* `eq:certificate-equivalence`, `def:strong-certificate` and `eq:strong-certificate-size` as
  formulas in `f`, and the operations of `def:extension-monoid`;
* `thm:certificate-breadth` as displayed, `β_{A_f}(M_f) = β(M_f) = b_f(U)`;
* `cor:certificate-queries` with the set of nonnull records written out, and the cardinality
  bound after it;
* the matroid instance: `S ∼_B T ↔ B(S) = B(T)`, `b_B = β_{A_B}(M_B) = r`, the isomorphism
  with the greedy-basis monoid, and `thm:matroid-basis-query` through certificates.

The sanity checks cover the empty universe, the empty input, constant functions, an injective
function (certificate size `#U`), a function whose value is preserved by a subset that is not a
strong certificate (so the extension clause matters), repeated and null records, and Boolean
"is some record present" with certificate size at most one.
-/

namespace MonoidProduct.Certificates

open QuantumQueryComplexity ExtensionMonoid

/-! ## The definitions -/

section Definitions

variable {U O : Type*} [DecidableEq U] (f : Finset U → O)

/-- `eq:certificate-equivalence`: the extension `K` ranges over all subsets. -/
example (S T : Finset U) :
    ExtensionEquiv f S T ↔ ∀ K : Finset U, f (S ∪ K) = f (T ∪ K) :=
  Iff.rfl

/-- `def:strong-certificate`. -/
example (C S : Finset U) :
    IsStrongCertificate f C S ↔ C ⊆ S ∧ ∀ K : Finset U, f (C ∪ K) = f (S ∪ K) :=
  Iff.rfl

/-- `eq:strong-certificate-size`: `b_f(U) = max_S min{|C| : C ⊆ S, C ∼_f S}`. -/
example [Fintype U] :
    strongCertificateSize f = Finset.univ.sup fun S : Finset U =>
      sInf {k | ∃ C : Finset U, (C ⊆ S ∧ ∀ K, f (C ∪ K) = f (S ∪ K)) ∧ C.card = k} :=
  strongCertificateSize_eq_sup f

/-- `def:extension-monoid`: `[S][T] = [S ∪ T]`, `1 = [∅]`, classes are `∼_f`-classes, and the
readout `[S] ↦ f(S)` is well defined. -/
example (S T : Finset U) :
    mk f S * mk f T = mk f (S ∪ T) ∧ (1 : ExtensionMonoid f) = mk f ∅ ∧
      (mk f S = mk f T ↔ ExtensionEquiv f S T) ∧ readout f (mk f S) = f S :=
  ⟨mk_mul_mk S T, rfl, mk_eq_mk, readout_mk S⟩

/-- `M_f` is a commutative idempotent, hence aperiodic, monoid. -/
example : (∀ a b : ExtensionMonoid f, a * b = b * a) ∧ (∀ a : ExtensionMonoid f, a * a = a) ∧
    IsAperiodicMonoid (ExtensionMonoid f) :=
  ⟨mul_comm, mul_self, inferInstance⟩

end Definitions

/-! ## `thm:certificate-breadth` -/

section Breadth

variable {U O : Type} [DecidableEq U] (f : Finset U → O)

/-- The alphabet `A_f = {[∅]} ∪ {[{u}] : u ∈ U}`. -/
example : extensionLetter f none = 1 ∧ ∀ u : U, extensionLetter f (some u) = mk f {u} :=
  ⟨rfl, fun _ => rfl⟩

/-- `thm:certificate-breadth` as displayed: `β_{A_f}(M_f) = β(M_f) = b_f(U)`. -/
example :
    breadth (extensionLetter f) = breadth (id : ExtensionMonoid f → ExtensionMonoid f) ∧
      breadth (id : ExtensionMonoid f → ExtensionMonoid f) = strongCertificateSize f :=
  certificate_breadth f

end Breadth

/-! ## `cor:certificate-queries` -/

section Queries

variable {U O : Type} [Fintype U] [DecidableEq U] [DecidableEq O] (f : Finset U → O)

/-- `cor:certificate-queries`, with the set `{x_i : x_i ≠ ⊥}` of nonnull records written out. -/
example (n : ℕ) :
    (qQuery (fun x : Fin n → Option U => f (Finset.univ.biUnion fun i => (x i).toFinset))
        (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * strongCertificateSize f)) :=
  strongCertificate_qQuery_le_min_sqrt f n

/-- The cardinality bound `|M_f| ≤ ∑_{j=0}^{b_f(U)} C(|U|, j)`. -/
example :
    Fintype.card (ExtensionMonoid f) ≤
      ∑ j ∈ Finset.range (strongCertificateSize f + 1), (Fintype.card U).choose j :=
  card_extensionMonoid_le_sum_choose f

/-- The empty input needs no query. -/
example : qQuery (fun x : Fin 0 → Option U => f (recordSet x)) (1 / 3) = 0 := by
  have h := strongCertificate_qQuery_le_min_sqrt f 0
  rw [Nat.cast_zero, zero_mul, Real.sqrt_zero, mul_zero, min_self] at h
  exact_mod_cast le_antisymm h (Nat.cast_nonneg _)

/-- The identity encoding recovers the records. -/
example (n : ℕ) (x : Fin n → Option U) : encodedSet (fun _ (o : Option U) => o) x = recordSet x :=
  rfl

end Queries

/-! ## Sanity checks -/

section Checks

/-- The empty universe has certificate size zero. -/
example {O : Type*} (f : Finset Empty → O) : strongCertificateSize f = 0 :=
  Nat.le_zero.mp ((strongCertificateSize_le_card f).trans_eq Fintype.card_eq_zero)

/-- A constant function has certificate size zero and needs no query. -/
example {U O : Type} [Fintype U] [DecidableEq U] [DecidableEq O] (c : O) (n : ℕ) :
    strongCertificateSize (fun _ : Finset U => c) = 0 ∧
      qQuery (fun x : Fin n → Option U => (fun _ : Finset U => c) (recordSet x)) (1 / 3) = 0 :=
  have h0 : strongCertificateSize (fun _ : Finset U => c) = 0 :=
    strongCertificateSize_eq_zero_iff.mpr fun _ _ => rfl
  ⟨h0, strongCertificate_qQuery_eq_zero h0 (by norm_num)⟩

/-- The identity on subsets has certificate size `#U`: no set has a proper strong
certificate. -/
example {U : Type*} [Fintype U] [DecidableEq U] :
    strongCertificateSize (id : Finset U → Finset U) = Fintype.card U :=
  strongCertificateSize_of_injective Function.injective_id

/-- **Equal values are not enough**: for the parity of `|S|` on `U = Fin 2`, the empty set has
the same value as `U` but is not a strong certificate for it (extend by `{0}`). -/
example :
    (fun S : Finset (Fin 2) => S.card % 2) ∅ = (fun S : Finset (Fin 2) => S.card % 2) Finset.univ ∧
      ¬ IsStrongCertificate (fun S : Finset (Fin 2) => S.card % 2) ∅ Finset.univ :=
  ⟨by decide, fun h => absurd (h.2 {0}) (by decide)⟩

/-- Repeated and null records contribute their distinct nonnull values. -/
example : recordSet ![some (0 : Fin 3), none, some 0, some 2] = {0, 2} := by
  decide

/-- "Some record is present" has certificate size at most one: a nonempty set is certified by
any one of its elements, and the empty set by itself. -/
example {U : Type*} [DecidableEq U] :
    HasStrongCertificateBound (fun S : Finset U => decide S.Nonempty) 1 := by
  intro S
  rcases S.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
  · exact ⟨∅, isStrongCertificate_self _ _, by simp⟩
  · refine ⟨{u}, ⟨Finset.singleton_subset_iff.mpr hu, fun K => ?_⟩, by simp⟩
    have h2 : (S ∪ K).Nonempty := ⟨u, Finset.mem_union_left K hu⟩
    simp [h2]

end Checks

/-! ## The matroid instance (`sec:matroid-bases`) -/

section Matroid

open MonoidProduct.Matroid

variable {E : Type} [Fintype E] [LinearOrder E] {M : _root_.Matroid E}

/-- For the greedy-basis map `B` of a rank-`r` matroid: `S ∼_B T ↔ B(S) = B(T)`, `B(S)` is a
strong certificate for `S`, and `b_B = β_{A_B}(M_B) = r`. -/
example (hM : M.E = Set.univ) {r : ℕ} (hr : M.eRank = r) :
    (∀ S T : Finset E, ExtensionEquiv (greedy M) S T ↔ greedy M S = greedy M T) ∧
      (∀ S : Finset E, IsStrongCertificate (greedy M) (greedy M S) S) ∧
      strongCertificateSize (greedy M) = r ∧ breadth (extensionLetter (greedy M)) = r :=
  ⟨fun _ _ => extensionEquiv_greedy_iff hM, greedy_isStrongCertificate hM,
    greedy_strongCertificateSize_eq_rank hM hr,
    (extensionLetter_breadth_eq _).trans (greedy_strongCertificateSize_eq_rank hM hr)⟩

/-- `M_B ≃* H`, carrying the alphabet `A_B` to the alphabet `G` of `prop:matroid-greedy-monoid`. -/
example (hM : M.E = Set.univ) (o : Option E) :
    extensionMonoidGreedyMulEquiv hM (extensionLetter (greedy M) o) = greedyBasisLetter M hM o :=
  extensionMonoidGreedyMulEquiv_extensionLetter hM o

/-- `thm:matroid-basis-query` through `cor:certificate-queries`: the same bound as the
operational endpoint `matroidBasisRecords_qQuery_le_min_sqrt`. -/
example {W : Type} [Fintype W] [LinearOrder W] (hM : M.E = Set.univ) {r : ℕ} (hr : M.eRank ≤ r)
    (n : ℕ) :
    (qQuery (fun x : Fin n → Option (E × W) => basisRecords M x Finset.univ) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (2 ^ 18 * Real.sqrt ((n : ℝ) * r)) :=
  matroidBasisRecords_qQuery_le_min_sqrt_of_certificates hM hr n

end Matroid

end MonoidProduct.Certificates
