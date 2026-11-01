import MonoidProduct.Graph.FaceWalk
import MonoidProduct.Graph.PlanarContraction
set_option linter.style.header false

/-!
# Inserting a chord into a face of a rotation system

Two vertices on one face of a rotation system can be joined by a new edge drawn inside that face;
the face splits in two.  This keeps the Euler defect, so a spherical rotation system stays
spherical.  Faces are read as lists of darts, so their walks may repeat vertices.

* `IsAddEdge G G' u v`: `G'` is `G` with the edge `uv` added, for instance `G ⊔ edge u v`
  (`isAddEdge_sup_edge`).  When `u` and `v` are not adjacent in `G`, the darts of `G'` are those
  of `G` (`IsAddEdge.incl`), the new dart `IsAddEdge.dart` from `u` to `v`, and its reversal
  (`IsAddEdge.dartEquiv`).
* `RotationSystem.insertChord ρ h hn`: for darts `a` and `b` of `G` whose tails are not adjacent,
  the rotation system of `G'` that puts the new dart `c` just before `a` around its tail, and
  `c.symm` just before `b` around its tail.  Its rotation is the old one, extended to fix `c` and
  `c.symm`, followed by two transpositions (`chordRot`); so is its face permutation, with one more
  transposition (`insertChord_face_eq`).
* **The two new faces** (`faceDarts_insertChord`): if the face through `a` reads
  `a :: P ++ b :: Q`, then the face through `c.symm` reads `c.symm :: a :: P` and the face through
  `c` reads `c :: b :: Q`.  On tails, a face walk `[u] ++ P' ++ [v] ++ Q'` splits into
  `[v, u] ++ P'` and `[u, v] ++ Q'` (`faceWalk_insertChord`).  Away from the two corners every dart
  keeps its successor (`insertChord_face_incl`), so the other faces keep their darts
  (`faceDarts_insertChord_of_not_sameCycle`).
* **Counts**, for `a` and `b` on one face: one edge and one face more, with the same components and
  isolated vertices.  Joining the two new darts into one cycle and that into the face through `a`
  merges cycles, and the last transposition splits the joined cycle
  (`chord_cycleCount_extendDomain_mul_swap_mul_swap_mul_swap`).  So the Euler defect does not
  change (`eulerDefect_insertChord`), and a spherical rotation system stays spherical
  (`IsSpherical.insertChord`).
* `isPlanar_sup_edge_of_sameCycle`: **joining the tails of two darts of one face of a spherical
  rotation system keeps planarity**.
* Identifying orbits after splicing a new element into a cycle (`chord_orbitList_splice`), from the
  identification of a list that a permutation shifts cyclically (`orbitList_eq_of_getElem`,
  `Graph/FaceWalk.lean`).
-/

namespace MonoidProduct.Graph

open SimpleGraph Equiv Equiv.Perm

/-! ## Extending a permutation by two fixed points -/

section Extend

variable {α β : Type*} [DecidableEq β] {c c' : β} (f : α ≃ {b : β // b ≠ c ∧ b ≠ c'})

/-- The extension of `p` fixes the first new point. -/
theorem chord_extendDomain_apply_left (p : Perm α) : p.extendDomain f c = c :=
  extendDomain_apply_not_subtype p f (by simp)

/-- The extension of `p` fixes the second new point. -/
theorem chord_extendDomain_apply_right (p : Perm α) : p.extendDomain f c' = c' :=
  extendDomain_apply_not_subtype p f (by simp)

omit [DecidableEq β] in
/-- An element whose image under `q` is itself lies in no other cycle. -/
theorem chord_not_sameCycle_of_apply_eq {q : Perm β} {s z : β} (hz : q z = z) (hsz : s ≠ z) :
    ¬ q.SameCycle s z :=
  fun h => hsz (h.eq_of_right hz)

variable [Finite β]

/-- **A transposition with a fixed point** keeps the cycles of `q`, with the fixed point joined to
the cycle of the other element. -/
theorem chord_sameCycle_mul_swap_of_apply_eq {q : Perm β} {s z : β} (hz : q z = z) (hsz : s ≠ z)
    {x y : β} (h : q.SameCycle x y) : (q * swap s z).SameCycle x y :=
  (sameCycle_mul_swap_iff_of_not_sameCycle (chord_not_sameCycle_of_apply_eq hz hsz) x y).mpr
    (Or.inl h)

theorem chord_sameCycle_mul_swap_self_of_apply_eq {q : Perm β} {s z : β} (hz : q z = z)
    (hsz : s ≠ z) :
    (q * swap s z).SameCycle s z :=
  sameCycle_mul_swap_of_not_sameCycle (chord_not_sameCycle_of_apply_eq hz hsz)

/-- **Extending by two fixed points adds two cycles.** -/
theorem chord_cycleCount_extendDomain (hcc : c ≠ c') (p : Perm α) :
    cycleCount (p.extendDomain f) = cycleCount p + 2 := by
  have : Finite α := Finite.of_equiv _ f.symm
  have hrange : Set.range (fun x => (f x : β)) = {b | b ≠ c ∧ b ≠ c'} := by
    ext b
    refine ⟨?_, fun hb => ⟨f.symm ⟨b, hb⟩, by simp⟩⟩
    rintro ⟨x, rfl⟩
    exact (f x).2
  have hcompl : (Set.range (fun x => (f x : β)))ᶜ = {c, c'} := by
    rw [hrange]
    ext b
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [cycleCount_eq_add_of_sameCycle_iff (F := p.extendDomain f) (H := p) (fun x => (f x : β))
    (fun x y => sameCycle_extendDomain) (fun y hy => extendDomain_apply_not_subtype p f
      fun hp => hy ⟨f.symm ⟨y, hp⟩, by simp⟩), hcompl, Set.ncard_pair hcc]

omit [Finite β] in
theorem chord_not_sameCycle_extendDomain (hcc : c ≠ c') (p : Perm α) :
    ¬ (p.extendDomain f).SameCycle c c' :=
  fun h => hcc (h.eq_of_left (chord_extendDomain_apply_left f p))

theorem chord_not_sameCycle_extendDomain_mul_swap (hcc : c ≠ c') (p : Perm α) (x : α) :
    ¬ (p.extendDomain f * swap c c').SameCycle (f x) c' := by
  rw [sameCycle_mul_swap_iff_of_not_sameCycle (chord_not_sameCycle_extendDomain f hcc p)]
  have hxc : ¬ (p.extendDomain f).SameCycle (f x) c :=
    chord_not_sameCycle_of_apply_eq (chord_extendDomain_apply_left f p) (f x).2.1
  have hxc' : ¬ (p.extendDomain f).SameCycle (f x) c' :=
    chord_not_sameCycle_of_apply_eq (chord_extendDomain_apply_right f p) (f x).2.2
  tauto

/-- **Joining the two new fixed points into one cycle, and that into the cycle of `f x`**: back to
the cycle count of `p`. -/
theorem chord_cycleCount_extendDomain_mul_swap_mul_swap (hcc : c ≠ c') (p : Perm α) (x : α) :
    cycleCount (p.extendDomain f * swap c c' * swap (f x : β) c') = cycleCount p := by
  have h0 := chord_cycleCount_extendDomain f hcc p
  have h1 := cycleCount_mul_swap_of_not_sameCycle (chord_not_sameCycle_extendDomain f hcc p)
  have h2 := cycleCount_mul_swap_of_not_sameCycle
    (chord_not_sameCycle_extendDomain_mul_swap f hcc p x)
  omega

/-- **Then splitting the joined cycle** at `f y`, for `y` in the cycle of `x`: one cycle more
than `p`. -/
theorem chord_cycleCount_extendDomain_mul_swap_mul_swap_mul_swap (hcc : c ≠ c') (p : Perm α)
    {x y : α} (hxy : p.SameCycle x y) :
    cycleCount (p.extendDomain f * swap c c' * swap (f x : β) c' * swap (f y : β) c) =
      cycleCount p + 1 := by
  have hn1 := chord_not_sameCycle_extendDomain f hcc p
  have hn2 := chord_not_sameCycle_extendDomain_mul_swap f hcc p x
  have hs : (p.extendDomain f * swap c c' * swap (f x : β) c').SameCycle (f y) c := by
    rw [sameCycle_mul_swap_iff_of_not_sameCycle hn2]
    refine Or.inr ⟨Or.inl ?_, Or.inr ?_⟩
    · exact (sameCycle_mul_swap_iff_of_not_sameCycle hn1 _ _).mpr
        (Or.inl (sameCycle_extendDomain.mpr hxy.symm))
    · exact sameCycle_mul_swap_of_not_sameCycle hn1
  rw [cycleCount_mul_swap_of_sameCycle (f y).2.1 hs,
    chord_cycleCount_extendDomain_mul_swap_mul_swap f hcc p x]

omit [Finite β] in
/-- **A permutation of the extended set agreeing with `s` on `α` and swapping the two new points**
is the extension of `s` followed by their transposition. -/
theorem chord_eq_extendDomain_mul_swap (s : Perm α) (s' : Perm β) (hs : ∀ e, s' (f e) = f (s e))
    (hc : s' c = c') (hc' : s' c' = c) : s' = s.extendDomain f * swap c c' := by
  ext b
  by_cases hb : b ≠ c ∧ b ≠ c'
  · obtain ⟨e, he⟩ := f.surjective ⟨b, hb⟩
    have hbe : b = f e := by rw [he]
    rw [hbe, hs, mul_apply, swap_apply_of_ne_of_ne (f e).2.1 (f e).2.2, extendDomain_apply_image]
  · rcases not_and_or.mp hb with h | h <;> rw [not_not] at h <;> subst h
    · rw [hc, mul_apply, swap_apply_left, chord_extendDomain_apply_right]
    · rw [hc', mul_apply, swap_apply_right, chord_extendDomain_apply_left]

omit [Finite β] in
/-- **Moving two transpositions past an involution** `s'` that extends `s` and swaps the two new
points. -/
theorem chord_extendDomain_mul_swap_mul_swap_mul (r s : Perm α) (s' : Perm β)
    (hs : ∀ e, s' (f e) = f (s e)) (hc : s' c = c') (hc' : s' c' = c) (hss : ∀ e, s (s e) = e)
    (x y : α) :
    r.extendDomain f * swap (f x : β) c * swap (f y : β) c' * s' =
      (r * s).extendDomain f * swap c c' * swap (f (s x) : β) c' * swap (f (s y) : β) c := by
  have h1 : s'⁻¹ (f x : β) = f (s x) := Perm.inv_eq_iff_eq.mpr (by rw [hs, hss])
  have h2 : s'⁻¹ (f y : β) = f (s y) := Perm.inv_eq_iff_eq.mpr (by rw [hs, hss])
  have h3 : s'⁻¹ c = c' := Perm.inv_eq_iff_eq.mpr hc'.symm
  have h4 : s'⁻¹ c' = c := Perm.inv_eq_iff_eq.mpr hc.symm
  have hr : r.extendDomain f * s' = (r * s).extendDomain f * swap c c' := by
    rw [chord_eq_extendDomain_mul_swap f s s' hs hc hc', ← mul_assoc, extendDomain_mul]
  calc r.extendDomain f * swap (f x : β) c * swap (f y : β) c' * s'
      = r.extendDomain f * swap (f x : β) c * (swap (f y : β) c' * s') := by rw [mul_assoc]
    _ = r.extendDomain f * (swap (f x : β) c * s') * swap (f (s y) : β) c := by
        rw [swap_mul_eq_mul_swap, h2, h4]; simp only [mul_assoc]
    _ = r.extendDomain f * s' * swap (f (s x) : β) c' * swap (f (s y) : β) c := by
        rw [swap_mul_eq_mul_swap, h1, h3]; simp only [mul_assoc]
    _ = _ := by rw [hr]

omit [Finite β] in
/-- **Moving one transposition past the involution.** -/
theorem chord_extendDomain_mul_swap_mul (r s : Perm α) (s' : Perm β)
    (hs : ∀ e, s' (f e) = f (s e)) (hc : s' c = c') (hc' : s' c' = c) (hss : ∀ e, s (s e) = e)
    (x : α) :
    r.extendDomain f * swap (f x : β) c * s' =
      (r * s).extendDomain f * swap c c' * swap (f (s x) : β) c' := by
  have h1 : s'⁻¹ (f x : β) = f (s x) := Perm.inv_eq_iff_eq.mpr (by rw [hs, hss])
  have h3 : s'⁻¹ c = c' := Perm.inv_eq_iff_eq.mpr hc'.symm
  have hr : r.extendDomain f * s' = (r * s).extendDomain f * swap c c' := by
    rw [chord_eq_extendDomain_mul_swap f s s' hs hc hc', ← mul_assoc, extendDomain_mul]
  rw [mul_assoc, swap_mul_eq_mul_swap, h1, h3, ← mul_assoc, hr]

end Extend

/-! ## Orbits of spliced cycles -/

section Splice

variable {α β : Type*}

/-- **A list `z :: M` that `p` shifts cyclically is the orbit of `z`**: `p` sends `z` to the
first entry of `M`, each entry of `M` to the next, and the last entry back to `z`. -/
theorem chord_orbitList_eq_cons {p : Perm α} {z : α} {M : List α} (hnd : (z :: M).Nodup)
    (hM : M ≠ [])
    (h0 : p z = M.head hM) (hsucc : ∀ (i : ℕ) (hi : i + 1 < M.length), p M[i] = M[i + 1])
    (hlast : p (M.getLast hM) = z) : orbitList p z = z :: M := by
  have hlen : 0 < M.length := List.length_pos_iff.mpr hM
  refine orbitList_eq_of_getElem (p := p) (L := z :: M) hnd (by simp) fun i hi => ?_
  simp only [List.length_cons] at hi ⊢
  rcases i with _ | i
  · simp only [Nat.mod_eq_of_lt (by omega : 0 + 1 < M.length + 1), List.getElem_cons_zero,
      List.getElem_cons_succ]
    rw [h0, List.head_eq_getElem]
  · by_cases hi' : i + 1 < M.length
    · simp only [Nat.mod_eq_of_lt (by omega : i + 1 + 1 < M.length + 1), List.getElem_cons_succ]
      exact hsucc i hi'
    · have hi'' : i = M.length - 1 := by omega
      simp only [show i + 1 + 1 = M.length + 1 by omega, Nat.mod_self, List.getElem_cons_succ,
        List.getElem_cons_zero]
      rw [← hlast, List.getLast_eq_getElem]
      simp only [hi'']

/-- **Entries of a piece of an orbit**: if the orbit of `w` is `L ++ R`, the entries of `L` are
the first iterates of `w`. -/
theorem chord_getElem_left_of_orbitList_eq_append {p : Perm α} {w : α} {L R : List α}
    (h : orbitList p w = L ++ R) (i : ℕ) (hi : i < L.length) : L[i] = (p ^ i) w := by
  have hlen : i < (orbitList p w).length := by rw [h, List.length_append]; omega
  rw [← getElem_orbitList p w i hlen, List.getElem_of_eq h hlen, List.getElem_append_left hi]

theorem chord_getElem_right_of_orbitList_eq_append {p : Perm α} {w : α} {L R : List α}
    (h : orbitList p w = L ++ R) (j : ℕ) (hj : j < R.length) : R[j] = (p ^ (L.length + j)) w := by
  have hlen : L.length + j < (orbitList p w).length := by rw [h, List.length_append]; omega
  rw [← getElem_orbitList p w _ hlen, List.getElem_of_eq h hlen,
    List.getElem_append_right (by omega)]
  simp

/-- In an orbit read as `L ++ R`, `p` sends each entry of `L` but the last to the next one. -/
theorem chord_apply_getElem_of_orbitList_eq_append {p : Perm α} {w : α} {L R : List α}
    (h : orbitList p w = L ++ R) (i : ℕ) (hi : i + 1 < L.length) : p L[i] = L[i + 1] := by
  rw [chord_getElem_left_of_orbitList_eq_append h i (by omega),
    chord_getElem_left_of_orbitList_eq_append h (i + 1) hi, pow_succ', mul_apply]

/-- In an orbit read as `L ++ R`, `p` sends the last entry of `L` to the first of `R`. -/
theorem chord_apply_getLast_of_orbitList_eq_append {p : Perm α} {w : α} {L R : List α}
    (h : orbitList p w = L ++ R) (hL : L ≠ []) (hR : R ≠ []) : p (L.getLast hL) = R.head hR := by
  have hL0 := List.length_pos_iff.mpr hL
  have hR0 := List.length_pos_iff.mpr hR
  rw [List.getLast_eq_getElem, List.head_eq_getElem,
    chord_getElem_left_of_orbitList_eq_append h _ (by omega),
    chord_getElem_right_of_orbitList_eq_append h 0 hR0, ← mul_apply, ← pow_succ']
  congr 2
  omega

/-- In an orbit read as `L ++ R`, `p` sends the last entry of `R` back to `w`. -/
theorem chord_apply_getLast_right_of_orbitList_eq_append {p : Perm α} {w : α} {L R : List α}
    (h : orbitList p w = L ++ R) (hR : R ≠ []) : p (R.getLast hR) = w := by
  have hR0 := List.length_pos_iff.mpr hR
  have hlen : (orbitList p w).length = L.length + R.length := by rw [h, List.length_append]
  rw [List.getLast_eq_getElem, chord_getElem_right_of_orbitList_eq_append h _ (by omega),
    ← mul_apply,
    ← pow_succ', show L.length + (R.length - 1) + 1 = Function.minimalPeriod p w by
      rw [← length_orbitList, hlen]; omega]
  exact pow_minimalPeriod_apply p w

/-- **The orbit read from the start of `R`** is `R ++ L`. -/
theorem chord_orbitList_head_of_orbitList_eq_append [Finite α] {p : Perm α} {w : α} {L R : List α}
    (h : orbitList p w = L ++ R) (hR : R ≠ []) : orbitList p (R.head hR) = R ++ L := by
  have hR0 := List.length_pos_iff.mpr hR
  rw [List.head_eq_getElem, chord_getElem_right_of_orbitList_eq_append h 0 hR0, add_zero,
    orbitList_pow_apply, h, List.rotate_append_length_eq]

/-- **Splicing a new element into an orbit**: if the orbit of `w` under `p` reads `L ++ R`, and
`p'` agrees with `p` along `L` except at its last entry (through an injection `ι`), sends that
entry to a new element `z`, and sends `z` to `ι w`, then the orbit of `z` under `p'` is
`z :: L.map ι`. -/
theorem chord_orbitList_splice {p : Perm α} {p' : Perm β} {ι : α → β} (hι : Function.Injective ι)
    {z : β} (hz : ∀ e, ι e ≠ z) {w : α} {L R : List α} (hLR : orbitList p w = L ++ R)
    (hL : L ≠ []) (hR : R ≠ [])
    (hp' : ∀ e, e ≠ L.getLast hL → e ≠ R.getLast hR → p' (ι e) = ι (p e))
    (hz0 : p' z = ι w) (hzl : p' (ι (L.getLast hL)) = z) : orbitList p' z = z :: L.map ι := by
  have hnd : (L ++ R).Nodup := hLR ▸ nodup_orbitList p w
  obtain ⟨hLnd, -, hdisj⟩ := List.nodup_append.mp hnd
  have hM : L.map ι ≠ [] := by rw [Ne, List.map_eq_nil_iff]; exact hL
  have hL0 := List.length_pos_iff.mpr hL
  refine chord_orbitList_eq_cons ?_ hM ?_ (fun i hi => ?_) ?_
  · refine List.nodup_cons.mpr ⟨fun hzM => ?_, hLnd.map hι⟩
    obtain ⟨e, -, he⟩ := List.mem_map.mp hzM
    exact hz e he
  · rw [hz0, List.head_map]
    congr 1
    rw [List.head_eq_getElem, chord_getElem_left_of_orbitList_eq_append hLR 0 hL0, pow_zero,
      one_apply]
  · rw [List.length_map] at hi
    simp only [List.getElem_map]
    have hne : L[i] ≠ L.getLast hL := by
      rw [List.getLast_eq_getElem, Ne, hLnd.getElem_inj_iff]
      omega
    have hne' : L[i] ≠ R.getLast hR :=
      hdisj _ (List.getElem_mem _) _ (List.getLast_mem hR)
    rw [hp' _ hne hne', chord_apply_getElem_of_orbitList_eq_append hLR i hi]
  · rw [List.getLast_map]
    exact hzl

end Splice

/-! ## Graphs with one more edge -/

section AddEdge

variable {V W : Type*} {G G' : SimpleGraph V} {u v : V}

/-- **Reachability along a map** that sends adjacent vertices to reachable ones. -/
theorem chord_reachable_map_of_adj {H : SimpleGraph W} (π : W → V)
    (hπ : ∀ s t, H.Adj s t → G.Reachable (π s) (π t)) {s t : W} (hst : H.Reachable s t) :
    G.Reachable (π s) (π t) := by
  obtain ⟨p⟩ := hst
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hπ _ _ hadj).trans ih

variable (G G' u v) in
/-- **`G'` is `G` with the edge `uv` added**: two vertices are adjacent in `G'` exactly when they
are adjacent in `G` or are `u` and `v`. -/
def IsAddEdge : Prop := ∀ x y, G'.Adj x y ↔ G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)

/-- `G ⊔ edge u v` is `G` with the edge `uv` added, for `u ≠ v`. -/
theorem isAddEdge_sup_edge (huv : u ≠ v) : IsAddEdge G (G ⊔ edge u v) u v := by
  intro x y
  rw [sup_adj, edge_adj]
  constructor
  · rintro (h | ⟨h | h, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl h, by rw [h.1, h.2]; exact huv⟩
    · exact Or.inr ⟨Or.inr h, by rw [h.1, h.2]; exact huv.symm⟩

namespace IsAddEdge

variable (h : IsAddEdge G G' u v)
include h

/-- `G` is a subgraph of `G'`. -/
theorem le : G ≤ G' := fun _ _ hxy => (h _ _).mpr (Or.inl hxy)

/-- `u` and `v` are adjacent in `G'`. -/
theorem adj : G'.Adj u v := (h u v).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem ne : u ≠ v := h.adj.ne

/-- **The new dart**, from `u` to `v`. -/
def dart : G'.Dart := ⟨(u, v), h.adj⟩

/-- **The darts of `G` as darts of `G'`.** -/
def incl (d : G.Dart) : G'.Dart := ⟨d.toProd, h.le d.adj⟩

@[simp] theorem fst_dart : h.dart.fst = u := rfl

@[simp] theorem snd_dart : h.dart.snd = v := rfl

@[simp] theorem fst_incl (d : G.Dart) : (h.incl d).fst = d.fst := rfl

@[simp] theorem snd_incl (d : G.Dart) : (h.incl d).snd = d.snd := rfl

theorem incl_symm (d : G.Dart) : h.incl d.symm = (h.incl d).symm := rfl

theorem incl_injective : Function.Injective h.incl := fun d e hde => by
  have h' := congrArg Dart.toProd hde
  exact Dart.ext d e h'

theorem dart_symm_ne : h.dart.symm ≠ h.dart := h.dart.symm_ne

/-- **`G'` is `G ⊔ edge u v`.** -/
theorem eq_sup_edge : G' = G ⊔ edge u v := by
  ext x y
  rw [h x y, sup_adj, edge_adj]
  constructor
  · rintro (h' | h' | h')
    · exact Or.inl h'
    · exact Or.inr ⟨Or.inl h', by rw [h'.1, h'.2]; exact h.ne⟩
    · exact Or.inr ⟨Or.inr h', by rw [h'.1, h'.2]; exact h.ne.symm⟩
  · rintro (h' | ⟨h' | h', -⟩)
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

variable (hn : ¬ G.Adj u v)
include hn

theorem incl_ne_dart (d : G.Dart) : h.incl d ≠ h.dart := fun he => hn (by
  have h1 : d.fst = u := congrArg (fun d : G'.Dart => d.fst) he
  have h2 : d.snd = v := congrArg (fun d : G'.Dart => d.snd) he
  rw [← h1, ← h2]
  exact d.adj)

theorem incl_ne_dart_symm (d : G.Dart) : h.incl d ≠ h.dart.symm := fun he => hn (by
  have h1 : d.fst = v := congrArg (fun d : G'.Dart => d.fst) he
  have h2 : d.snd = u := congrArg (fun d : G'.Dart => d.snd) he
  rw [← h1, ← h2]
  exact d.adj.symm)

/-- **The darts of `G'`**: those of `G`, and the new dart and its reversal. -/
def dartEquiv : G.Dart ≃ {d : G'.Dart // d ≠ h.dart ∧ d ≠ h.dart.symm} where
  toFun d := ⟨h.incl d, h.incl_ne_dart hn d, h.incl_ne_dart_symm hn d⟩
  invFun d := ⟨d.1.toProd, ((h _ _).mp d.1.adj).resolve_right fun h' => by
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact d.2.1 (Dart.ext _ _ (Prod.ext h1 h2))
    · exact d.2.2 (Dart.ext _ _ (Prod.ext h1 h2))⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coe_dartEquiv (d : G.Dart) : (h.dartEquiv hn d : G'.Dart) = h.incl d := rfl

/-- Every dart of `G'` is the new dart, its reversal, or a dart of `G`. -/
theorem eq_dart_or (d : G'.Dart) : d = h.dart ∨ d = h.dart.symm ∨ ∃ e, d = h.incl e := by
  by_cases h1 : d = h.dart
  · exact Or.inl h1
  by_cases h2 : d = h.dart.symm
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr ⟨(h.dartEquiv hn).symm ⟨d, h1, h2⟩, rfl⟩)

/-- **One edge more**, counting darts: two more darts, and twice the edges are the darts. -/
theorem ncard_edgeSet [Finite V] : G'.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  have := finite_dart (G := G')
  have h1 := two_mul_ncard_edgeSet_eq_natCard_dart (G := G')
  have h2 := two_mul_ncard_edgeSet_eq_natCard_dart (G := G)
  have h3 := Nat.card_congr (h.dartEquiv hn)
  have h4 := natCard_subtype_ne_and_ne_add_two h.dart_symm_ne.symm
  omega

omit hn in
/-- **The same components**, when `u` and `v` are already joined in `G`. -/
theorem natCard_connectedComponent (huv : G.Reachable u v) :
    Nat.card G'.ConnectedComponent = Nat.card G.ConnectedComponent := by
  have key : ∀ x y, G'.Reachable x y ↔ G.Reachable x y := fun x y =>
    ⟨fun hr => chord_reachable_map_of_adj id (fun s t hst => by
      rcases (h s t).mp hst with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h'.reachable
      · exact huv
      · exact huv.symm) hr, fun hr => hr.mono h.le⟩
  exact Nat.card_congr (Quot.congr (Equiv.refl V) key)

omit hn in
/-- **The same isolated vertices**, when `u` and `v` have neighbours in `G`. -/
theorem isolatedVerts_eq (hu : u ∉ isolatedVerts G) (hv : v ∉ isolatedVerts G) :
    isolatedVerts G' = isolatedVerts G := by
  ext x
  constructor
  · intro hx y hxy
    exact hx y (h.le hxy)
  · intro hx y hxy
    rcases (h x y).mp hxy with h' | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hx y h'
    · exact hu hx
    · exact hv hx

end IsAddEdge

end AddEdge

/-! ## Inserting a chord -/

namespace RotationSystem

variable {V : Type*} {G G' : SimpleGraph V} (ρ : RotationSystem G)

/-- The inverse rotation keeps tails too. -/
theorem chord_fst_rot_symm (d : G.Dart) : (ρ.rot.symm d).fst = d.fst := by
  conv_rhs => rw [← Equiv.apply_symm_apply ρ.rot d]
  rw [ρ.fst_rot]

/-- **The dart before `d` along its face** is the reversal of the dart before `d` around its
tail. -/
theorem chord_face_symm_rot_symm (d : G.Dart) : ρ.face (ρ.rot.symm d).symm = d := by
  rw [face_apply, Dart.symm_symm, Equiv.apply_symm_apply]

theorem chord_sameCycle_face_symm_rot_symm (d : G.Dart) :
    ρ.face.SameCycle (ρ.rot.symm d).symm d := by
  conv_rhs => rw [← ρ.chord_face_symm_rot_symm d]
  exact sameCycle_apply_right.mpr (SameCycle.refl _ _)

variable [DecidableEq V] {a b : G.Dart} (h : IsAddEdge G G' a.fst b.fst)
  (hn : ¬ G.Adj a.fst b.fst)

/-- **The rotation after inserting a chord** from the tail of `a` to the tail of `b`: the new dart
`c` goes just before `a` around its tail, and its reversal just before `b` around its tail. -/
def chordRot : Perm G'.Dart :=
  ρ.rot.extendDomain (h.dartEquiv hn) * swap (h.dartEquiv hn (ρ.rot.symm a) : G'.Dart) h.dart *
    swap (h.dartEquiv hn (ρ.rot.symm b) : G'.Dart) h.dart.symm

theorem chord_fst_extendDomain_rot (d : G'.Dart) :
    (ρ.rot.extendDomain (h.dartEquiv hn) d).fst = d.fst := by
  by_cases hd : d ≠ h.dart ∧ d ≠ h.dart.symm
  · obtain ⟨e, he⟩ := (h.dartEquiv hn).surjective ⟨d, hd⟩
    have hde : d = h.dartEquiv hn e := by rw [he]
    rw [hde, extendDomain_apply_image, IsAddEdge.coe_dartEquiv, IsAddEdge.coe_dartEquiv,
      IsAddEdge.fst_incl, IsAddEdge.fst_incl, ρ.fst_rot]
  · rw [extendDomain_apply_not_subtype ρ.rot (h.dartEquiv hn) hd]

theorem fst_chordRot (d : G'.Dart) : (ρ.chordRot h hn d).fst = d.fst := by
  simp only [chordRot, mul_apply]
  rw [chord_fst_extendDomain_rot]
  refine (apply_swap_eq_self (v := fun d : G'.Dart => d.fst) ?_ _).trans
    (apply_swap_eq_self (v := fun d : G'.Dart => d.fst) ?_ _)
  · exact ρ.chord_fst_rot_symm a
  · exact ρ.chord_fst_rot_symm b

private theorem chordRot_aux_apply :
    (ρ.rot.extendDomain (h.dartEquiv hn) *
      swap (h.dartEquiv hn (ρ.rot.symm a) : G'.Dart) h.dart) h.dart.symm = h.dart.symm := by
  rw [mul_apply, swap_apply_of_ne_of_ne (h.dartEquiv hn _).2.2.symm h.dart_symm_ne,
    chord_extendDomain_apply_right]

theorem sameCycle_chordRot_incl [Finite V] {e e' : G.Dart} (he : ρ.rot.SameCycle e e') :
    (ρ.chordRot h hn).SameCycle (h.incl e) (h.incl e') := by
  have := finite_dart (G := G')
  exact chord_sameCycle_mul_swap_of_apply_eq (ρ.chordRot_aux_apply h hn) (h.dartEquiv hn _).2.2
    (chord_sameCycle_mul_swap_of_apply_eq (chord_extendDomain_apply_left _ _) (h.dartEquiv hn _).2.1
      (sameCycle_extendDomain.mpr he))

theorem sameCycle_chordRot_dart [Finite V] :
    (ρ.chordRot h hn).SameCycle (h.incl (ρ.rot.symm a)) h.dart := by
  have := finite_dart (G := G')
  exact chord_sameCycle_mul_swap_of_apply_eq (ρ.chordRot_aux_apply h hn) (h.dartEquiv hn _).2.2
    (chord_sameCycle_mul_swap_self_of_apply_eq (chord_extendDomain_apply_left _ _)
      (h.dartEquiv hn _).2.1)

theorem sameCycle_chordRot_dart_symm [Finite V] :
    (ρ.chordRot h hn).SameCycle (h.incl (ρ.rot.symm b)) h.dart.symm := by
  have := finite_dart (G := G')
  exact chord_sameCycle_mul_swap_self_of_apply_eq (ρ.chordRot_aux_apply h hn) (h.dartEquiv hn _).2.2

/-- Every dart of `G'` lies in the rotation cycle of a dart of `G` with the same tail. -/
theorem exists_sameCycle_chordRot [Finite V] (d : G'.Dart) :
    ∃ e : G.Dart, e.fst = d.fst ∧ (ρ.chordRot h hn).SameCycle d (h.incl e) := by
  rcases h.eq_dart_or hn d with rfl | rfl | ⟨e, rfl⟩
  · exact ⟨ρ.rot.symm a, ρ.chord_fst_rot_symm a, (ρ.sameCycle_chordRot_dart h hn).symm⟩
  · exact ⟨ρ.rot.symm b, ρ.chord_fst_rot_symm b, (ρ.sameCycle_chordRot_dart_symm h hn).symm⟩
  · exact ⟨e, rfl, SameCycle.refl _ _⟩

/-- **Inserting a chord** between the tails of `a` and `b`, two nonadjacent vertices: the rotation
system of `G'`, which is `G` with the edge added, that puts the new dart `c` from the tail of `a`
just before `a` around its tail, and its reversal just before `b` around its tail.  The face
through `a` and `b` splits in two (`faceDarts_insertChord`). -/
def insertChord [Finite V] : RotationSystem G' where
  rot := ρ.chordRot h hn
  fst_rot := ρ.fst_chordRot h hn
  sameCycle_rot d d' hdd' := by
    obtain ⟨e, he, hde⟩ := ρ.exists_sameCycle_chordRot h hn d
    obtain ⟨e', he', hde'⟩ := ρ.exists_sameCycle_chordRot h hn d'
    exact hde.trans ((ρ.sameCycle_chordRot_incl h hn
      (ρ.sameCycle_rot e e' (he.trans (hdd'.trans he'.symm)))).trans hde'.symm)

theorem chordRot_apply_incl {e : G.Dart} (hx : e ≠ ρ.rot.symm a) (hy : e ≠ ρ.rot.symm b) :
    ρ.chordRot h hn (h.incl e) = h.incl (ρ.rot e) := by
  simp only [chordRot, mul_apply, IsAddEdge.coe_dartEquiv]
  rw [swap_apply_of_ne_of_ne (fun he => hy (h.incl_injective he)) (h.incl_ne_dart_symm hn e),
    swap_apply_of_ne_of_ne (fun he => hx (h.incl_injective he)) (h.incl_ne_dart hn e)]
  exact extendDomain_apply_image _ _ e

theorem chordRot_apply_left : ρ.chordRot h hn (h.incl (ρ.rot.symm a)) = h.dart := by
  have hab : ρ.rot.symm a ≠ ρ.rot.symm b := fun he =>
    h.ne (congrArg (fun d : G.Dart => d.fst) (ρ.rot.symm.injective he))
  simp only [chordRot, mul_apply, IsAddEdge.coe_dartEquiv]
  rw [swap_apply_of_ne_of_ne (fun he => hab (h.incl_injective he)) (h.incl_ne_dart_symm hn _),
    swap_apply_left, chord_extendDomain_apply_left]

theorem chordRot_apply_dart : ρ.chordRot h hn h.dart = h.incl a := by
  simp only [chordRot, mul_apply, IsAddEdge.coe_dartEquiv]
  rw [swap_apply_of_ne_of_ne (h.incl_ne_dart hn _).symm h.dart_symm_ne.symm, swap_apply_right]
  refine (extendDomain_apply_image _ _ (ρ.rot.symm a)).trans ?_
  rw [Equiv.apply_symm_apply]
  rfl

theorem chordRot_apply_right : ρ.chordRot h hn (h.incl (ρ.rot.symm b)) = h.dart.symm := by
  simp only [chordRot, mul_apply, IsAddEdge.coe_dartEquiv]
  rw [swap_apply_left, swap_apply_of_ne_of_ne (h.incl_ne_dart_symm hn _).symm h.dart_symm_ne,
    chord_extendDomain_apply_right]

theorem chordRot_apply_dart_symm : ρ.chordRot h hn h.dart.symm = h.incl b := by
  have hab : ρ.rot.symm b ≠ ρ.rot.symm a := fun he =>
    h.ne (congrArg (fun d : G.Dart => d.fst) (ρ.rot.symm.injective he)).symm
  simp only [chordRot, mul_apply, IsAddEdge.coe_dartEquiv]
  rw [swap_apply_right, swap_apply_of_ne_of_ne (fun he => hab (h.incl_injective he))
    (h.incl_ne_dart hn _)]
  refine (extendDomain_apply_image _ _ (ρ.rot.symm b)).trans ?_
  rw [Equiv.apply_symm_apply]
  rfl

variable [Finite V]

/-- **The faces away from the two corners do not change.** -/
theorem insertChord_face_incl {e : G.Dart} (hx : e ≠ (ρ.rot.symm a).symm)
    (hy : e ≠ (ρ.rot.symm b).symm) : (ρ.insertChord h hn).face (h.incl e) = h.incl (ρ.face e) := by
  rw [face_apply, ← IsAddEdge.incl_symm]
  exact ρ.chordRot_apply_incl h hn (fun he => hx (by rw [← he, Dart.symm_symm]))
    (fun he => hy (by rw [← he, Dart.symm_symm]))

/-- The dart before `a` along the face is followed by the new dart. -/
theorem insertChord_face_left :
    (ρ.insertChord h hn).face (h.incl (ρ.rot.symm a).symm) = h.dart := by
  rw [face_apply, ← IsAddEdge.incl_symm, Dart.symm_symm]
  exact ρ.chordRot_apply_left h hn

/-- The new dart is followed by `b`. -/
theorem insertChord_face_dart : (ρ.insertChord h hn).face h.dart = h.incl b := by
  rw [face_apply]
  exact ρ.chordRot_apply_dart_symm h hn

/-- The dart before `b` along the face is followed by the reversal of the new dart. -/
theorem insertChord_face_right :
    (ρ.insertChord h hn).face (h.incl (ρ.rot.symm b).symm) = h.dart.symm := by
  rw [face_apply, ← IsAddEdge.incl_symm, Dart.symm_symm]
  exact ρ.chordRot_apply_right h hn

/-- The reversal of the new dart is followed by `a`. -/
theorem insertChord_face_dart_symm : (ρ.insertChord h hn).face h.dart.symm = h.incl a := by
  rw [face_apply, Dart.symm_symm]
  exact ρ.chordRot_apply_dart h hn

/-- **The face permutation after inserting a chord**: the old one with the two new darts joined,
then joined to the face through the dart before `a`, then split at the dart before `b`. -/
theorem insertChord_face_eq :
    (ρ.insertChord h hn).face = ρ.face.extendDomain (h.dartEquiv hn) * swap h.dart h.dart.symm *
      swap (h.dartEquiv hn (ρ.rot.symm a).symm : G'.Dart) h.dart.symm *
      swap (h.dartEquiv hn (ρ.rot.symm b).symm : G'.Dart) h.dart :=
  chord_extendDomain_mul_swap_mul_swap_mul (h.dartEquiv hn) ρ.rot (dartReverse G) (dartReverse G')
    (fun _ => rfl) rfl rfl (fun e => Dart.symm_symm e) _ _

/-- **A chord inside one face adds a face.** -/
theorem natCard_face_insertChord (hab : ρ.face.SameCycle a b) :
    Nat.card (ρ.insertChord h hn).Face = Nat.card ρ.Face + 1 := by
  have := finite_dart (G := G')
  change cycleCount (ρ.insertChord h hn).face = cycleCount ρ.face + 1
  rw [insertChord_face_eq]
  exact chord_cycleCount_extendDomain_mul_swap_mul_swap_mul_swap _ h.dart_symm_ne.symm ρ.face
    (((ρ.chord_sameCycle_face_symm_rot_symm a).trans hab).trans
      (ρ.chord_sameCycle_face_symm_rot_symm b).symm)

/-- **A chord inside one face keeps the Euler defect**: one edge more and one face more, with the
same components and isolated vertices. -/
theorem eulerDefect_insertChord (hab : ρ.face.SameCycle a b) :
    (ρ.insertChord h hn).eulerDefect = ρ.eulerDefect := by
  have hreach : G.Reachable a.fst b.fst := ConnectedComponent.eq.mp
    (eq_of_sameCycle_of_forall (g := fun d : G.Dart => G.connectedComponentMk d.fst)
      ρ.connectedComponentMk_fst_face hab)
  have hC := h.natCard_connectedComponent hreach
  have hE := h.ncard_edgeSet hn
  have hF := ρ.natCard_face_insertChord h hn hab
  have hI := h.isolatedVerts_eq (fun hiso => hiso a.snd a.adj) (fun hiso => hiso b.snd b.adj)
  unfold eulerDefect completedFaceCount
  rw [hC, hE, hF, hI]
  push_cast
  ring

variable {ρ} in
/-- **A chord inside one face keeps a spherical rotation system spherical.** -/
theorem IsSpherical.insertChord (hρ : ρ.IsSpherical) (hab : ρ.face.SameCycle a b) :
    (ρ.insertChord h hn).IsSpherical := by
  rw [isSpherical_iff_eulerDefect_eq_zero] at hρ ⊢
  rw [eulerDefect_insertChord ρ h hn hab, hρ]

/-- **The two faces of a chord**: if the face through `a` reads `a :: P ++ b :: Q`, then after
inserting the chord `c` from the tail of `a` to the tail of `b`, the face through the reversal of
`c` reads `c.symm :: a :: P` and the face through `c` reads `c :: b :: Q`.  On tails: a face walk
`[u] ++ P' ++ [v] ++ Q'` splits into `[v, u] ++ P'` and `[u, v] ++ Q'`. -/
theorem faceDarts_insertChord {P Q : List G.Dart} (hPQ : ρ.faceDarts a = a :: P ++ b :: Q) :
    (ρ.insertChord h hn).faceDarts h.dart.symm = h.dart.symm :: (a :: P).map h.incl ∧
      (ρ.insertChord h hn).faceDarts h.dart = h.dart :: (b :: Q).map h.incl := by
  have := finite_dart (G := G)
  have hLR : orbitList ρ.face a = (a :: P) ++ (b :: Q) := hPQ
  have hy : (a :: P).getLast (List.cons_ne_nil _ _) = (ρ.rot.symm b).symm := by
    apply ρ.face.injective
    rw [chord_apply_getLast_of_orbitList_eq_append hLR _ (List.cons_ne_nil _ _),
      chord_face_symm_rot_symm]
    rfl
  have hx : (b :: Q).getLast (List.cons_ne_nil _ _) = (ρ.rot.symm a).symm := by
    apply ρ.face.injective
    rw [chord_apply_getLast_right_of_orbitList_eq_append hLR, chord_face_symm_rot_symm]
  have hRL : orbitList ρ.face b = (b :: Q) ++ (a :: P) :=
    chord_orbitList_head_of_orbitList_eq_append hLR (List.cons_ne_nil _ _)
  constructor
  · refine chord_orbitList_splice h.incl_injective (h.incl_ne_dart_symm hn) hLR
      (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (fun e he1 he2 => ?_)
      (ρ.insertChord_face_dart_symm h hn) ?_
    · rw [hy] at he1
      rw [hx] at he2
      exact ρ.insertChord_face_incl h hn he2 he1
    · rw [hy]
      exact ρ.insertChord_face_right h hn
  · refine chord_orbitList_splice h.incl_injective (h.incl_ne_dart hn) hRL (List.cons_ne_nil _ _)
      (List.cons_ne_nil _ _) (fun e he1 he2 => ?_) (ρ.insertChord_face_dart h hn) ?_
    · rw [hx] at he1
      rw [hy] at he2
      exact ρ.insertChord_face_incl h hn he1 he2
    · rw [hx]
      exact ρ.insertChord_face_left h hn

/-- **The other faces do not change**: a face of `ρ` that does not contain `a`, and so not `b`,
keeps its darts. -/
theorem faceDarts_insertChord_of_not_sameCycle (hab : ρ.face.SameCycle a b) {e : G.Dart}
    (he : ¬ ρ.face.SameCycle a e) :
    (ρ.insertChord h hn).faceDarts (h.incl e) = (ρ.faceDarts e).map h.incl := by
  have := finite_dart (G := G)
  have h0 : 0 < ((ρ.faceDarts e).map h.incl).length := by
    rw [List.length_map]
    have := ρ.two_le_length_faceDarts e
    omega
  have key := orbitList_eq_of_getElem (p := (ρ.insertChord h hn).face)
    ((ρ.nodup_faceDarts e).map h.incl_injective) h0 fun i hi => by
      rw [List.length_map] at hi
      simp only [List.getElem_map, List.length_map]
      have hmem : ρ.face.SameCycle e (ρ.faceDarts e)[i] :=
        ρ.mem_faceDarts_iff.mp (List.getElem_mem _)
      rw [ρ.insertChord_face_incl h hn
        (fun hx => he ((ρ.chord_sameCycle_face_symm_rot_symm a).symm.trans (hx ▸ hmem.symm)))
        (fun hy => he (hab.trans ((ρ.chord_sameCycle_face_symm_rot_symm b).symm.trans
          (hy ▸ hmem.symm)))), ← ρ.getElem_faceDarts_succ_mod e i hi]
  have he0 : ((ρ.faceDarts e).map h.incl)[0] = h.incl e := by
    rw [List.getElem_map, getElem_faceDarts, pow_zero, one_apply]
  rw [← he0]
  exact key

/-- **The two faces of a chord, on tails**: if the face through `a` reads `a :: P ++ b :: Q`, so
that its walk is `[u] ++ P' ++ [v] ++ Q'` with `u`, `v` the tails of `a`, `b` and `P'`, `Q'` the
tails of `P`, `Q`, then the two new face walks are `[v, u] ++ P'` and `[u, v] ++ Q'`. -/
theorem faceWalk_insertChord {P Q : List G.Dart} (hPQ : ρ.faceDarts a = a :: P ++ b :: Q) :
    (ρ.insertChord h hn).faceWalk h.dart.symm = [b.fst, a.fst] ++ P.map (·.fst) ∧
      (ρ.insertChord h hn).faceWalk h.dart = [a.fst, b.fst] ++ Q.map (·.fst) := by
  obtain ⟨h1, h2⟩ := ρ.faceDarts_insertChord h hn hPQ
  refine ⟨?_, ?_⟩
  · simp only [faceWalk, h1, List.map_cons, List.map_map, List.cons_append, List.nil_append]
    rfl
  · simp only [faceWalk, h2, List.map_cons, List.map_map, List.cons_append, List.nil_append]
    rfl

end RotationSystem

/-- **Inserting a chord into a face keeps planarity**: joining the tails of two darts of one face
of a spherical rotation system gives a planar graph.  If the tails are already adjacent, the graph
does not change. -/
theorem isPlanar_sup_edge_of_sameCycle {V : Type*} {G : SimpleGraph V} [Finite V]
    {ρ : RotationSystem G} (hρ : ρ.IsSpherical) {a b : G.Dart} (hab : ρ.face.SameCycle a b)
    (hne : a.fst ≠ b.fst) : IsPlanar (G ⊔ edge a.fst b.fst) := by
  classical
  by_cases hadj : G.Adj a.fst b.fst
  · have hG : G ⊔ edge a.fst b.fst = G := by
      refine le_antisymm (sup_le le_rfl fun x y hxy => ?_) le_sup_left
      rw [edge_adj] at hxy
      rcases hxy.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm
    rw [hG]
    exact ⟨ρ, hρ⟩
  · exact ⟨_, hρ.insertChord (isAddEdge_sup_edge hne) hadj hab⟩

end MonoidProduct.Graph
