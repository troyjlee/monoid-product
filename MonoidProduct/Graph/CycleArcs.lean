import MonoidProduct.Graph.Minor
set_option linter.style.header false

/-!
# Arcs of cyclic lists

A cycle is a list of distinct vertices read cyclically: each entry is adjacent to the next, and the
last to the first (`IsCycleList`).  Its intervals are read off the rotation that starts at a chosen
vertex.

* `startAt C a`: the rotation of `C` starting at `a`; it does not depend on which rotation of `C`
  is given (`startAt_rotate`).
* `cycDist C a b`: the position of `b` in `startAt C a`, the number of steps forward from `a` to
  `b`.  Distances add along the cycle (`cycDist_add_cycDist`, `cycDist_add_cycDist_of_lt`), and
  `cycDist C a b + cycDist C b a = C.length` for `a ≠ b` (`cycDist_add_cycDist_comm`).
* `arc C a b`: the half-open interval from `a`, included, forward to `b`, excluded;
  `closedArc C a b`: the interval with `b` added.  Membership is a comparison of distances from
  `a` (`mem_arc_iff`, `mem_closedArc_iff`); arcs are invariant under rotating `C`
  (`arc_rotate`, `closedArc_rotate`).
* Successive arcs concatenate (`arc_append_arc`), and the arcs between successive marked vertices
  make up the whole cycle (`arc_append_arc_self`, `arc_append_arc_append_arc`,
  `arc_append_arc_append_arc_append_arc`), so they are pairwise disjoint.  For a set `X` of at
  least two marks, every vertex of the cycle lies on the arc between some pair of consecutive marks
  (`exists_isConsecutive_mem_arc`), and on only one such arc (`IsConsecutive.eq_of_mem_arc`).
* In a cycle of `G`, arcs induce connected subgraphs (`IsCycleList.isConnectedSet_arc`,
  `IsCycleList.isConnectedSet_closedArc`), and some vertex of `arc C a b` is adjacent to `b`
  (`IsCycleList.exists_mem_arc_adj`).
-/

namespace MonoidProduct.Graph

open SimpleGraph

variable {V : Type*}

/-! ## Connected sets -/

/-- **Adding a neighbour to a connected set keeps it connected.** -/
theorem IsConnectedSet.insert_of_adj {G : SimpleGraph V} {s : Set V} (h : IsConnectedSet G s)
    {a b : V} (hb : b ∈ s) (hab : G.Adj a b) : IsConnectedSet G (insert a s) := by
  have hsub : s ⊆ insert a s := Set.subset_insert a s
  have hab' : (restrictTo G (insert a s)).Adj a b := ⟨hab, Set.mem_insert a s, hsub hb⟩
  have hto : ∀ w ∈ insert a s, (restrictTo G (insert a s)).Reachable a w := by
    rintro w (rfl | hw)
    · rfl
    · exact hab'.reachable.trans ((h.2 b hb w hw).mono (restrictTo_mono hsub))
  refine ⟨⟨a, Set.mem_insert a s⟩, fun u hu w hw => ?_⟩
  exact (hto u hu).symm.trans (hto w hw)

/-- **A chain is connected**: the entries of a nonempty list whose consecutive entries are adjacent
form a connected set. -/
theorem isConnectedSet_of_isChain {G : SimpleGraph V} :
    ∀ {L : List V}, L.IsChain G.Adj → L ≠ [] → IsConnectedSet G {v | v ∈ L}
  | [], _, h => absurd rfl h
  | [a], _, _ => by
    rw [show {v | v ∈ [a]} = ({a} : Set V) by ext; simp]
    exact isConnectedSet_singleton G a
  | a :: b :: l, hL, _ => by
    obtain ⟨hab, hL'⟩ := List.isChain_cons_cons.mp hL
    rw [show {v | v ∈ a :: b :: l} = insert a {v | v ∈ b :: l} by ext; simp]
    exact (isConnectedSet_of_isChain hL' (List.cons_ne_nil b l)).insert_of_adj
      List.mem_cons_self hab

/-! ## Positions in a list without repetitions -/

/-- **A rotation of a list without repetitions is determined by its first entry.** -/
theorem rotate_eq_rotate_of_getElem?_zero {L : List V} (hL : L.Nodup) {i j : ℕ}
    (h0 : 0 < L.length) (h : (L.rotate i)[0]? = (L.rotate j)[0]?) : L.rotate i = L.rotate j := by
  rw [List.getElem?_rotate h0, List.getElem?_rotate h0, zero_add, zero_add,
    List.getElem?_eq_getElem (Nat.mod_lt _ h0), List.getElem?_eq_getElem (Nat.mod_lt _ h0),
    Option.some_inj, hL.getElem_inj_iff] at h
  rw [← List.rotate_mod L i, ← List.rotate_mod L j, h]

/-- A prefix of a rotation, short enough not to wrap around, is a prefix of the dropped list. -/
theorem take_rotate_of_add_le {L : List V} {d m : ℕ} (h : d + m ≤ L.length) :
    (L.rotate d).take m = (L.drop d).take m := by
  rw [List.rotate_eq_drop_append_take (by omega), List.take_append_of_le_length (by simp; omega)]

section Positions

variable [DecidableEq V]

/-- **A prefix of a list without repetitions** consists of the entries of small position. -/
theorem mem_take_iff_idxOf_lt {L : List V} (hL : L.Nodup) {m : ℕ} {v : V} :
    v ∈ L.take m ↔ v ∈ L ∧ L.idxOf v < m := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp h
    refine ⟨List.getElem_mem _, ?_⟩
    rw [hL.idxOf_getElem]
    exact lt_of_lt_of_le hj (min_le_left _ _)
  · rintro ⟨hv, hlt⟩
    have h := List.idxOf_lt_length_iff.mpr hv
    exact List.mem_take_iff_getElem.mpr ⟨L.idxOf v, lt_min hlt h, List.getElem_idxOf h⟩

end Positions

/-! ## Reading a cyclic list from a vertex -/

section Arcs

variable [DecidableEq V] {C : List V} {a b c d v : V}

/-- **The cyclic list read from `a`**: the rotation of `C` that starts at `a`. -/
def startAt (C : List V) (a : V) : List V := C.rotate (C.idxOf a)

theorem length_startAt : (startAt C a).length = C.length := List.length_rotate _ _

theorem mem_startAt : v ∈ startAt C a ↔ v ∈ C := List.mem_rotate

theorem nodup_startAt : (startAt C a).Nodup ↔ C.Nodup := List.nodup_rotate

/-- `startAt C a` starts at `a`. -/
theorem getElem?_startAt_zero (ha : a ∈ C) : (startAt C a)[0]? = some a := by
  rw [startAt, List.getElem?_rotate (List.length_pos_of_mem ha), zero_add,
    Nat.mod_eq_of_lt (List.idxOf_lt_length_iff.mpr ha)]
  exact List.getElem?_idxOf ha

/-- **Reading a rotation of `C` from `a` is reading `C` from `a`.** -/
theorem startAt_rotate (hC : C.Nodup) (ha : a ∈ C) (k : ℕ) :
    startAt (C.rotate k) a = startAt C a := by
  have h0 := getElem?_startAt_zero (List.mem_rotate.mpr ha : a ∈ C.rotate k)
  have h1 := getElem?_startAt_zero ha
  unfold startAt at h0 h1 ⊢
  rw [List.rotate_rotate] at h0 ⊢
  exact rotate_eq_rotate_of_getElem?_zero hC (List.length_pos_of_mem ha) (h0.trans h1.symm)

/-- **The distance from `a` forward to `b`**: the position of `b` in `C` read from `a`. -/
def cycDist (C : List V) (a b : V) : ℕ := (startAt C a).idxOf b

/-- **The half-open arc** from `a`, included, forward to `b`, excluded. -/
def arc (C : List V) (a b : V) : List V := (startAt C a).take (cycDist C a b)

/-- **The closed arc** from `a` forward to `b`, both included. -/
def closedArc (C : List V) (a b : V) : List V := (startAt C a).take (cycDist C a b + 1)

theorem cycDist_rotate (hC : C.Nodup) (ha : a ∈ C) (k : ℕ) :
    cycDist (C.rotate k) a b = cycDist C a b := by
  rw [cycDist, cycDist, startAt_rotate hC ha]

/-- **Arcs do not depend on where the cyclic list starts.** -/
theorem arc_rotate (hC : C.Nodup) (ha : a ∈ C) (k : ℕ) : arc (C.rotate k) a b = arc C a b := by
  rw [arc, arc, cycDist_rotate hC ha, startAt_rotate hC ha]

theorem closedArc_rotate (hC : C.Nodup) (ha : a ∈ C) (k : ℕ) :
    closedArc (C.rotate k) a b = closedArc C a b := by
  rw [closedArc, closedArc, cycDist_rotate hC ha, startAt_rotate hC ha]

theorem cycDist_lt_length (hb : b ∈ C) : cycDist C a b < C.length := by
  rw [← length_startAt (a := a)]
  exact List.idxOf_lt_length_iff.mpr (mem_startAt.mpr hb)

theorem getElem?_startAt_cycDist (hb : b ∈ C) : (startAt C a)[cycDist C a b]? = some b :=
  List.getElem?_idxOf (mem_startAt.mpr hb)

theorem getElem_startAt_cycDist (hb : b ∈ C) :
    (startAt C a)[cycDist C a b]'(by rw [length_startAt]; exact cycDist_lt_length hb) = b :=
  List.getElem_idxOf _

/-- A vertex is at distance `t` from `a` when it is entry `t` of `C` read from `a`. -/
theorem cycDist_eq_of_getElem? (hC : C.Nodup) {t : ℕ} (h : (startAt C a)[t]? = some b) :
    cycDist C a b = t := by
  obtain ⟨ht, hb⟩ := List.getElem?_eq_some_iff.mp h
  rw [cycDist, ← hb, (nodup_startAt.mpr hC).idxOf_getElem]

theorem cycDist_self (hC : C.Nodup) (ha : a ∈ C) : cycDist C a a = 0 :=
  cycDist_eq_of_getElem? hC (getElem?_startAt_zero ha)

/-- Distinct vertices are at a positive distance. -/
theorem cycDist_eq_zero_iff (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) :
    cycDist C a b = 0 ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ cycDist_self hC ha⟩
  have hb' := getElem?_startAt_cycDist (a := a) hb
  rw [h, getElem?_startAt_zero ha] at hb'
  exact Option.some_inj.mp hb'

theorem cycDist_pos (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    0 < cycDist C a b :=
  Nat.pos_of_ne_zero fun h => hab ((cycDist_eq_zero_iff hC ha hb).mp h)

/-- **Distances determine vertices**: two vertices of `C` at the same distance from `a` are
equal. -/
theorem eq_of_cycDist_eq (hb : b ∈ C) (hc : c ∈ C) (h : cycDist C a b = cycDist C a c) :
    b = c := by
  have hb' := getElem?_startAt_cycDist (a := a) hb
  rw [h, getElem?_startAt_cycDist hc] at hb'
  exact (Option.some_inj.mp hb').symm

/-- **Reading from `b` is reading from `a`, rotated by the distance from `a` to `b`.** -/
theorem startAt_eq_rotate (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) :
    startAt C b = (startAt C a).rotate (cycDist C a b) := by
  have h0 := getElem?_startAt_zero hb
  have h1 : ((startAt C a).rotate (cycDist C a b))[0]? = some b := by
    rw [List.getElem?_rotate (by rw [length_startAt]; exact List.length_pos_of_mem ha), zero_add,
      length_startAt, Nat.mod_eq_of_lt (cycDist_lt_length hb)]
    exact getElem?_startAt_cycDist hb
  unfold startAt at h0 h1 ⊢
  rw [List.rotate_rotate] at h1 ⊢
  exact rotate_eq_rotate_of_getElem?_zero hC (List.length_pos_of_mem ha) (h0.trans h1.symm)

/-- **Distances add along the cycle**, when `b` comes no later than `c` from `a`. -/
theorem cycDist_add_cycDist (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (h : cycDist C a b ≤ cycDist C a c) : cycDist C a b + cycDist C b c = cycDist C a c := by
  have hlt := cycDist_lt_length (a := a) hc
  have hrot := startAt_eq_rotate hC ha hb
  have hget : (startAt C b)[cycDist C a c - cycDist C a b]? = some c := by
    rw [hrot, List.getElem?_rotate (by rw [length_startAt]; omega), length_startAt,
      show cycDist C a c - cycDist C a b + cycDist C a b = cycDist C a c by omega,
      Nat.mod_eq_of_lt hlt]
    exact getElem?_startAt_cycDist hc
  rw [cycDist_eq_of_getElem? hC hget]
  omega

/-- **Distances add around the cycle**, when `c` comes before `b` from `a`. -/
theorem cycDist_add_cycDist_of_lt (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (h : cycDist C a c < cycDist C a b) :
    cycDist C a b + cycDist C b c = cycDist C a c + C.length := by
  have hltb := cycDist_lt_length (a := a) hb
  have hrot := startAt_eq_rotate hC ha hb
  have hget : (startAt C b)[C.length - cycDist C a b + cycDist C a c]? = some c := by
    rw [hrot, List.getElem?_rotate (by rw [length_startAt]; omega), length_startAt,
      show C.length - cycDist C a b + cycDist C a c + cycDist C a b =
        cycDist C a c + C.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (cycDist_lt_length hc)]
    exact getElem?_startAt_cycDist hc
  rw [cycDist_eq_of_getElem? hC hget]
  omega

/-- **The two distances between distinct vertices add up to the length.** -/
theorem cycDist_add_cycDist_comm (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    cycDist C a b + cycDist C b a = C.length := by
  have h := cycDist_add_cycDist_of_lt hC ha hb ha
    (by rw [cycDist_self hC ha]; exact cycDist_pos hC ha hb hab)
  rw [cycDist_self hC ha] at h
  omega

/-! ## Membership in arcs -/

/-- **Membership in an arc**: a vertex of `C` lies on the arc from `a` to `b` when it comes strictly
before `b`, reading from `a`. -/
theorem mem_arc_iff (hC : C.Nodup) : v ∈ arc C a b ↔ v ∈ C ∧ cycDist C a v < cycDist C a b := by
  rw [arc, mem_take_iff_idxOf_lt (nodup_startAt.mpr hC), mem_startAt]
  rfl

/-- **Membership in a closed arc.** -/
theorem mem_closedArc_iff (hC : C.Nodup) :
    v ∈ closedArc C a b ↔ v ∈ C ∧ cycDist C a v ≤ cycDist C a b := by
  rw [closedArc, mem_take_iff_idxOf_lt (nodup_startAt.mpr hC), mem_startAt, Nat.lt_succ_iff]
  rfl

theorem nodup_arc (hC : C.Nodup) : (arc C a b).Nodup :=
  (List.take_sublist _ _).nodup (nodup_startAt.mpr hC)

theorem nodup_closedArc (hC : C.Nodup) : (closedArc C a b).Nodup :=
  (List.take_sublist _ _).nodup (nodup_startAt.mpr hC)

theorem mem_of_mem_arc (hv : v ∈ arc C a b) : v ∈ C :=
  mem_startAt.mp (List.mem_of_mem_take hv)

theorem mem_of_mem_closedArc (hv : v ∈ closedArc C a b) : v ∈ C :=
  mem_startAt.mp (List.mem_of_mem_take hv)

/-- **An arc between distinct vertices contains its start.** -/
theorem left_mem_arc (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) : a ∈ arc C a b :=
  (mem_arc_iff hC).mpr ⟨ha, by rw [cycDist_self hC ha]; exact cycDist_pos hC ha hb hab⟩

/-- **An arc does not contain its end.** -/
theorem right_not_mem_arc (hC : C.Nodup) : b ∉ arc C a b := fun h =>
  lt_irrefl _ ((mem_arc_iff hC).mp h).2

theorem arc_ne_nil (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) : arc C a b ≠ [] :=
  List.ne_nil_of_mem (left_mem_arc hC ha hb hab)

theorem left_mem_closedArc (hC : C.Nodup) (ha : a ∈ C) : a ∈ closedArc C a b :=
  (mem_closedArc_iff hC).mpr ⟨ha, by rw [cycDist_self hC ha]; exact Nat.zero_le _⟩

theorem right_mem_closedArc (hC : C.Nodup) (hb : b ∈ C) : b ∈ closedArc C a b :=
  (mem_closedArc_iff hC).mpr ⟨hb, le_rfl⟩

/-- **A closed arc is the arc followed by its end.** -/
theorem closedArc_eq_arc_append (hb : b ∈ C) : closedArc C a b = arc C a b ++ [b] := by
  rw [closedArc, arc, List.take_add_one, getElem?_startAt_cycDist hb]
  rfl

/-! ## Successive arcs -/

/-- **Successive arcs concatenate**: if `b` comes no later than `c` from `a`, the arc from `a` to
`b` followed by the arc from `b` to `c` is the arc from `a` to `c`. -/
theorem arc_append_arc (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (h : cycDist C a b ≤ cycDist C a c) : arc C a b ++ arc C b c = arc C a c := by
  have hsum := cycDist_add_cycDist hC ha hb hc h
  have hlt := cycDist_lt_length (a := a) hc
  rw [arc, arc, arc, startAt_eq_rotate hC ha hb,
    take_rotate_of_add_le (by rw [length_startAt]; omega), ← List.take_add, hsum]

/-- **Two arcs between distinct vertices make up the cycle**, read from the first. -/
theorem arc_append_arc_self (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    arc C a b ++ arc C b a = startAt C a := by
  have hsum := cycDist_add_cycDist_comm hC ha hb hab
  rw [arc, arc, startAt_eq_rotate hC ha hb,
    take_rotate_of_add_le (by rw [length_startAt]; omega), ← List.take_add, hsum,
    ← length_startAt (a := a), List.take_length]

/-- **Successive arcs are disjoint.** -/
theorem disjoint_arc_arc (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (h : cycDist C a b ≤ cycDist C a c) : (arc C a b).Disjoint (arc C b c) :=
  List.disjoint_of_nodup_append (by rw [arc_append_arc hC ha hb hc h]; exact nodup_arc hC)

/-- **The two arcs between distinct vertices are disjoint.** -/
theorem disjoint_arc_arc_self (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    (arc C a b).Disjoint (arc C b a) :=
  List.disjoint_of_nodup_append
    (by rw [arc_append_arc_self hC ha hb hab]; exact nodup_startAt.mpr hC)

/-- **The two arcs between distinct vertices cover the cycle.** -/
theorem mem_arc_or_mem_arc (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) (hv : v ∈ C) :
    v ∈ arc C a b ∨ v ∈ arc C b a := by
  have : v ∈ arc C a b ++ arc C b a := by
    rw [arc_append_arc_self hC ha hb hab]
    exact mem_startAt.mpr hv
  exact List.mem_append.mp this

/-- **Three marks in cyclic order cut the cycle into three arcs.** -/
theorem arc_append_arc_append_arc (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (hac : a ≠ c) (h : cycDist C a b ≤ cycDist C a c) :
    arc C a b ++ arc C b c ++ arc C c a = startAt C a := by
  rw [arc_append_arc hC ha hb hc h, arc_append_arc_self hC ha hc hac]

/-- **Four marks in cyclic order cut the cycle into four arcs.** -/
theorem arc_append_arc_append_arc_append_arc (hC : C.Nodup) (ha : a ∈ C) (hb : b ∈ C)
    (hc : c ∈ C) (hd : d ∈ C) (had : a ≠ d) (hbc : cycDist C a b ≤ cycDist C a c)
    (hcd : cycDist C a c ≤ cycDist C a d) :
    arc C a b ++ arc C b c ++ arc C c d ++ arc C d a = startAt C a := by
  rw [arc_append_arc hC ha hb hc hbc, arc_append_arc hC ha hc hd hcd,
    arc_append_arc_self hC ha hd had]

/-! ## Consecutive marks -/

/-- **`p` and `q` are consecutive marks of `X` along `C`**: distinct marks with no mark strictly
between them, that is, no mark other than `p` on the arc from `p` to `q`. -/
def IsConsecutive (C : List V) (X : Finset V) (p q : V) : Prop :=
  p ∈ X ∧ q ∈ X ∧ p ≠ q ∧ ∀ r ∈ X, r ∈ arc C p q → r = p

/-- **Every vertex of the cycle lies between two consecutive marks**, for a set of at least two
marks on the cycle. -/
theorem exists_isConsecutive_mem_arc (hC : C.Nodup) {X : Finset V} (hXC : ∀ x ∈ X, x ∈ C)
    (hX : 1 < X.card) (hv : v ∈ C) : ∃ p q, IsConsecutive C X p q ∧ v ∈ arc C p q := by
  obtain ⟨p, hp, hpmin⟩ := X.exists_min_image (fun p => cycDist C p v)
    (Finset.card_pos.mp (by omega))
  have hne : (X.erase p).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hp]; omega
  obtain ⟨q, hq, hqmin⟩ := (X.erase p).exists_min_image (fun q => cycDist C p q) hne
  have hqp : q ≠ p := Finset.ne_of_mem_erase hq
  have hqX : q ∈ X := Finset.mem_of_mem_erase hq
  refine ⟨p, q, ⟨hp, hqX, hqp.symm, fun r hr hrarc => ?_⟩, (mem_arc_iff hC).mpr ⟨hv, ?_⟩⟩
  · by_contra hrp
    exact absurd (hqmin r (Finset.mem_erase.mpr ⟨hrp, hr⟩))
      (not_le.mpr ((mem_arc_iff hC).mp hrarc).2)
  · by_contra hle
    push Not at hle
    have hsum := cycDist_add_cycDist hC (hXC p hp) (hXC q hqX) hv hle
    have hpos := cycDist_pos hC (hXC p hp) (hXC q hqX) hqp.symm
    have := hpmin q hqX
    omega

/-- **The next mark is unique.** -/
theorem IsConsecutive.right_eq (hC : C.Nodup) {X : Finset V} (hXC : ∀ x ∈ X, x ∈ C) {p q q' : V}
    (h : IsConsecutive C X p q) (h' : IsConsecutive C X p q') : q = q' := by
  obtain ⟨hp, hq, hpq, hmid⟩ := h
  obtain ⟨-, hq', hpq', hmid'⟩ := h'
  rcases lt_trichotomy (cycDist C p q) (cycDist C p q') with hlt | heq | hgt
  · exact absurd (hmid' q hq ((mem_arc_iff hC).mpr ⟨hXC q hq, hlt⟩)) (Ne.symm hpq)
  · exact eq_of_cycDist_eq (hXC q hq) (hXC q' hq') heq
  · exact absurd (hmid q' hq' ((mem_arc_iff hC).mpr ⟨hXC q' hq', hgt⟩)) (Ne.symm hpq')

/-- **A vertex lies between only one pair of consecutive marks.** -/
theorem IsConsecutive.eq_of_mem_arc (hC : C.Nodup) {X : Finset V} (hXC : ∀ x ∈ X, x ∈ C)
    {p q p' q' : V} (h : IsConsecutive C X p q) (h' : IsConsecutive C X p' q')
    (hv : v ∈ arc C p q) (hv' : v ∈ arc C p' q') : p = p' ∧ q = q' := by
  have hpp : p = p' := by
    by_contra hne
    obtain ⟨hp, hq, -, hmid⟩ := h
    obtain ⟨hp', hq', -, hmid'⟩ := h'
    have hpC := hXC p hp
    have hp'C := hXC p' hp'
    obtain ⟨hvC, hvlt⟩ := (mem_arc_iff hC).mp hv
    obtain ⟨-, hvlt'⟩ := (mem_arc_iff hC).mp hv'
    -- `p'` is not strictly between `p` and `q`, so it comes after `v` from `p`.
    have hp'far : cycDist C p q ≤ cycDist C p p' := by
      by_contra hlt
      exact hne (hmid p' hp' ((mem_arc_iff hC).mpr ⟨hp'C, not_le.mp hlt⟩)).symm
    -- Then `p` comes before `v` from `p'`, and lies on the arc from `p'` to `q'`.
    have h1 := cycDist_add_cycDist_of_lt hC hpC hp'C hvC (by omega)
    have h2 := cycDist_add_cycDist_comm hC hpC hp'C hne
    have hpin : p ∈ arc C p' q' := (mem_arc_iff hC).mpr ⟨hpC, by omega⟩
    exact hne (hmid' p hp hpin)
  subst hpp
  exact ⟨rfl, h.right_eq hC hXC h'⟩

end Arcs

/-! ## Cycles of a graph -/

section Cycles

variable {G : SimpleGraph V} {C : List V} {a b : V}

/-- **A cycle of `G`, as a list**: no repeated vertex, and each entry adjacent to the next, the
last to the first. -/
def IsCycleList (G : SimpleGraph V) (C : List V) : Prop :=
  C.Nodup ∧ ∀ (i : ℕ) (hi : i < C.length),
    G.Adj C[i] (C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega)))

/-- **Rotating a cycle gives a cycle.** -/
theorem IsCycleList.rotate (h : IsCycleList G C) (k : ℕ) : IsCycleList G (C.rotate k) := by
  refine ⟨List.nodup_rotate.mpr h.1, fun i hi => ?_⟩
  have hn : 0 < C.length := by rw [List.length_rotate] at hi; omega
  simp only [List.getElem_rotate, List.length_rotate]
  have hlt : (i + k) % C.length < C.length := Nat.mod_lt _ hn
  have hidx : ((i + 1) % C.length + k) % C.length = ((i + k) % C.length + 1) % C.length := by
    rw [Nat.mod_add_mod, Nat.mod_add_mod, show i + 1 + k = i + k + 1 by omega]
  simp only [hidx]
  exact h.2 _ hlt

/-- **A cycle is a chain.** -/
theorem IsCycleList.isChain (h : IsCycleList G C) : C.IsChain G.Adj := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have := h.2 i (by omega)
  simp only [Nat.mod_eq_of_lt hi] at this
  exact this

variable [DecidableEq V]

/-- **A cycle read from a vertex is a chain.** -/
theorem IsCycleList.isChain_startAt (h : IsCycleList G C) (a : V) :
    (startAt C a).IsChain G.Adj :=
  (h.rotate _).isChain

/-- **Arcs of a cycle are connected.** -/
theorem IsCycleList.isConnectedSet_arc (h : IsCycleList G C) (ha : a ∈ C) (hb : b ∈ C)
    (hab : a ≠ b) : IsConnectedSet G {v | v ∈ arc C a b} :=
  isConnectedSet_of_isChain ((h.isChain_startAt a).take _) (arc_ne_nil h.1 ha hb hab)

/-- **Closed arcs of a cycle are connected.** -/
theorem IsCycleList.isConnectedSet_closedArc (h : IsCycleList G C) (ha : a ∈ C) :
    IsConnectedSet G {v | v ∈ closedArc C a b} :=
  isConnectedSet_of_isChain ((h.isChain_startAt a).take _)
    (List.ne_nil_of_mem (left_mem_closedArc h.1 ha))

/-- **An arc has a vertex adjacent to its end**: some vertex of `arc C a b` is adjacent to `b`.
The proof uses the vertex just before `b` along the cycle; the statement does not say which vertex
it is, since a chord can join `b` to an earlier one. -/
theorem IsCycleList.exists_mem_arc_adj (h : IsCycleList G C) (ha : a ∈ C) (hb : b ∈ C)
    (hab : a ≠ b) : ∃ x ∈ arc C a b, G.Adj x b := by
  have hpos := cycDist_pos h.1 ha hb hab
  have hlt : cycDist C a b < (startAt C a).length := by
    rw [length_startAt]; exact cycDist_lt_length hb
  have hadj := (List.isChain_iff_getElem.mp (h.isChain_startAt a)) (cycDist C a b - 1)
    (by omega)
  simp only [show cycDist C a b - 1 + 1 = cycDist C a b by omega,
    getElem_startAt_cycDist hb] at hadj
  refine ⟨_, ?_, hadj⟩
  rw [arc]
  exact List.mem_take_iff_getElem.mpr ⟨cycDist C a b - 1, lt_min (by omega) (by omega), rfl⟩

end Cycles

end MonoidProduct.Graph
