import WeiqiObsmetrologia.Board

/-!
# Weiqi — ko regimes and their termination bound

A **trace** is a game's move-by-move history of positions. This module states
the three ko regimes the kernel's ruleset parameter `ko_regime` names —
`simpleKo`, `positionalSuperko`, `situationalSuperko` — as `Prop`-valued
predicates over a trace, proves the two implications between them (and a
decide-checked witness that the missing third implication is genuinely
missing), and proves the **termination theorem**: under positional superko, a
trace on a board of `n` points has length at most `3 ^ n`.

This ties `lib/emsenn/services/561-group/services/science-services-section/…`'s
kernel ruleset field
`weiqi-services-section/apps/weiqi-kernel/src/rulesets.mts` (`ko_regime`, one of
`"simple_ko" | "positional_superko" | "situational_superko"`) to a proved bound
rather than a comment: whichever regime the kernel selects, this module is
where "how long can this run" stops being folklore.
-/

namespace WeiqiObsmetrologia
namespace Ko

/-- A **trace**: a game's positions in move order. -/
abbrev Trace (Point : Type) := List (Position Point)

/-- A **situation**: a position together with whose turn it is to move
(`true` = black to move). -/
abbrev Situation (Point : Type) := Position Point × Bool

/-- **Simple ko.** No position equals the one two plies back: whenever the
trace holds `a` at index `i` and `b` two plies later, `a ≠ b`. This is the
one-move-of-memory rule (forbid immediately recapturing the same shape). -/
def SimpleKo {Point : Type} (trace : Trace Point) : Prop :=
  ∀ (i : Nat) (a b : Position Point),
    trace[i]? = some a → trace[i + 2]? = some b → a ≠ b

/-- **Positional superko.** No position recurs anywhere in the trace — the
whole-trace generalization of simple ko. -/
def PositionalSuperko {Point : Type} (trace : Trace Point) : Prop :=
  trace.Nodup

/-- **Situational superko.** No `(position, side-to-move)` pair recurs — the
same board position may recur once, as long as it is not the same side's turn
both times. -/
def SituationalSuperko {Point : Type} (strace : List (Situation Point)) : Prop :=
  strace.Nodup

/-! ## Positional superko implies simple ko -/

/-- **Positional superko ⇒ simple ko.** If no position recurs anywhere, in
particular the position two plies back never recurs. -/
theorem positionalSuperko_implies_simpleKo {Point : Type} {trace : Trace Point}
    (h : PositionalSuperko trace) : SimpleKo trace := by
  intro i a b hia hib heq
  have hi : i < trace.length := (List.getElem?_eq_some_iff.mp hia).1
  have heq' : trace[i]? = trace[i + 2]? := by rw [hia, hib, heq]
  have hidx := (List.getElem?_inj hi h).mp heq'
  omega

/-! ## Positional superko implies situational superko, and not conversely -/

/-- **Positional superko ⇒ situational superko.** If a situational trace's
positions never recur (positional superko on the projected trace), then a
fortiori the `(position, side-to-move)` pairs never recur: equal pairs have
equal first components, so distinct first components force distinct pairs. -/
theorem positionalSuperko_implies_situationalSuperko {Point : Type}
    {strace : List (Situation Point)}
    (h : PositionalSuperko (strace.map Prod.fst)) : SituationalSuperko strace :=
  List.Pairwise.imp (fun hab heq => hab (congrArg Prod.fst heq))
    (List.pairwise_map.mp h)

/-- **Situational superko does not imply positional superko, in general.** A
position may legally recur under situational superko as long as it is not the
same side's turn both times — exhibited here on a one-point board: the
situations `(p0, black-to-move)` and `(p0, white-to-move)` are distinct (their
second components differ), so the two-situation trace `[(p0,true),(p0,false)]`
satisfies situational superko, yet its projected position trace `[p0,p0]`
repeats and so fails positional superko. This is the missing third
implication, made a concrete counterexample rather than left unstated. -/
theorem situationalSuperko_not_implies_positionalSuperko :
    ¬ (∀ {Point : Type} (strace : List (Situation Point)),
        SituationalSuperko strace → PositionalSuperko (strace.map Prod.fst)) := by
  intro h
  let p0 : Position Unit := fun _ => Stone.empty
  have hsit : SituationalSuperko ([(p0, true), (p0, false)] : List (Situation Unit)) := by
    show ([(p0, true), (p0, false)] : List (Situation Unit)).Nodup
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · intro hmem
      have heq : (p0, (true : Bool)) = (p0, (false : Bool)) := List.mem_singleton.mp hmem
      exact Bool.noConfusion (congrArg Prod.snd heq)
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.Pairwise.nil⟩
  have hpos := h ([(p0, true), (p0, false)] : List (Situation Unit)) hsit
  have hcontra :
      ¬ PositionalSuperko (([(p0, true), (p0, false)] : List (Situation Unit)).map Prod.fst) := by
    show ¬ ([p0, p0] : List (Position Unit)).Nodup
    intro hnd
    exact (List.nodup_cons.mp hnd).1 (List.mem_singleton.mpr rfl)
  exact hcontra hpos

/-! ## The termination bound: positional superko caps trace length at `3 ^ n` -/

/-- All length-`n` stone-tuples, built by prepending each of the three `Stone`s
onto every length-`(n-1)` tuple. Used only to bound `Position` under positional
superko — an executable witness that a board of `n` points has at most
`3 ^ n` positions, without a `Fintype` typeclass (this library has none;
`Obsmetrologia/Calculus/Order/ColoringEntropy.lean` records the same gap and
the same fix — a concrete `List` in place of `Fintype.card`). -/
def allTuples : Nat → List (List Stone)
  | 0 => [[]]
  | n + 1 =>
      (allTuples n).map (Stone.empty :: ·) ++
      (allTuples n).map (Stone.black :: ·) ++
      (allTuples n).map (Stone.white :: ·)

theorem allTuples_length : ∀ n, (allTuples n).length = 3 ^ n
  | 0 => rfl
  | n + 1 => by
      show ((allTuples n).map (Stone.empty :: ·) ++ (allTuples n).map (Stone.black :: ·) ++
        (allTuples n).map (Stone.white :: ·)).length = 3 ^ (n + 1)
      rw [List.length_append, List.length_append, List.length_map, List.length_map,
        List.length_map, allTuples_length n, Nat.pow_succ]
      omega

theorem allTuples_complete : ∀ n (v : List Stone), v.length = n → v ∈ allTuples n
  | 0, v, hv => by
      have hv0 : v = [] := List.eq_nil_of_length_eq_zero hv
      subst hv0
      simp [allTuples]
  | n + 1, v, hv => by
      cases v with
      | nil => simp at hv
      | cons s v' =>
          have hv' : v'.length = n := by
            simp only [List.length_cons] at hv
            omega
          have hmem := allTuples_complete n v' hv'
          show s :: v' ∈ (allTuples n).map (Stone.empty :: ·) ++
              (allTuples n).map (Stone.black :: ·) ++ (allTuples n).map (Stone.white :: ·)
          cases s with
          | empty =>
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (List.mem_map.mpr ⟨v', hmem, rfl⟩))))
          | black =>
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inr (List.mem_map.mpr ⟨v', hmem, rfl⟩))))
          | white =>
              exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨v', hmem, rfl⟩))

/-- **A duplicate-free list injected into a complete enumeration is no longer
than the enumeration.** The pigeonhole step of the termination theorem: no
new connectivity/enumeration typeclass, a direct induction removing one
matched element of the target list per source element. -/
theorem nodup_length_le_of_subset {α : Type} :
    ∀ (l allB : List α), l.Nodup → (∀ x, x ∈ l → x ∈ allB) → l.length ≤ allB.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, allB, hnodup, hsub => by
      have ha_notin_t : a ∉ t := (List.nodup_cons.mp hnodup).1
      have ht_nodup : t.Nodup := (List.nodup_cons.mp hnodup).2
      have ha_mem : a ∈ allB := hsub a (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨before, after, heq⟩ := List.append_of_mem ha_mem
      have ht_sub : ∀ x, x ∈ t → x ∈ before ++ after := by
        intro x hx
        have hx_allB : x ∈ allB := hsub x (List.mem_cons.mpr (Or.inr hx))
        rw [heq] at hx_allB
        rcases List.mem_append.mp hx_allB with hxb | hxa
        · exact List.mem_append.mpr (Or.inl hxb)
        · rcases List.mem_cons.mp hxa with hxeq | hxafter
          · subst hxeq; exact absurd hx ha_notin_t
          · exact List.mem_append.mpr (Or.inr hxafter)
      have ih := nodup_length_le_of_subset t (before ++ after) ht_nodup ht_sub
      have hlen : (before ++ after).length + 1 = allB.length := by
        simp [heq, List.length_append, List.length_cons]; omega
      show t.length + 1 ≤ allB.length
      omega

end Ko

namespace Board

variable {Point : Type} (B : Board Point)

/-- Read a position off as the tuple of its values on the board's points, in
enumeration order. -/
def toTuple (pos : Position Point) : List Stone := B.points.map pos

theorem toTuple_length (pos : Position Point) : (B.toTuple pos).length = B.card := by
  simp [Board.toTuple, Board.card]

/-- `toTuple` is injective — because `B.points` names every point
(`points_complete`), agreement of the tuples is agreement of the positions
everywhere. -/
theorem toTuple_injective {pos1 pos2 : Position Point}
    (h : B.toTuple pos1 = B.toTuple pos2) : pos1 = pos2 := by
  have hp : ∀ p, p ∈ B.points → pos1 p = pos2 p := List.map_eq_map_iff.mp h
  funext p
  exact hp p (B.points_complete p)

/-- **Termination under positional superko.** A trace on a board of `n = B.card`
points that satisfies positional superko has length at most `3 ^ n`: `toTuple`
injects the trace's (duplicate-free) positions into the `3 ^ n`-element
complete list of length-`n` stone-tuples, so the pigeonhole bound applies. -/
theorem positionalSuperko_length_le (trace : Ko.Trace Point)
    (h : Ko.PositionalSuperko trace) : trace.length ≤ 3 ^ B.card := by
  have hnodup : (trace.map B.toTuple).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp (R := (· ≠ ·)) (S := fun a b => B.toTuple a ≠ B.toTuple b)
    · intro a b hab heq
      exact hab (B.toTuple_injective heq)
    · exact h
  have hsub : ∀ x, x ∈ trace.map B.toTuple → x ∈ Ko.allTuples B.card := by
    intro x hx
    obtain ⟨pos, _, rfl⟩ := List.mem_map.mp hx
    exact Ko.allTuples_complete B.card (B.toTuple pos) (B.toTuple_length pos)
  have hle := Ko.nodup_length_le_of_subset (trace.map B.toTuple) (Ko.allTuples B.card) hnodup hsub
  rw [List.length_map, Ko.allTuples_length] at hle
  exact hle

end Board

end WeiqiObsmetrologia

#print axioms WeiqiObsmetrologia.Ko.positionalSuperko_implies_simpleKo
#print axioms WeiqiObsmetrologia.Ko.positionalSuperko_implies_situationalSuperko
#print axioms WeiqiObsmetrologia.Ko.situationalSuperko_not_implies_positionalSuperko
#print axioms WeiqiObsmetrologia.Ko.allTuples_length
#print axioms WeiqiObsmetrologia.Ko.allTuples_complete
#print axioms WeiqiObsmetrologia.Ko.nodup_length_le_of_subset
#print axioms WeiqiObsmetrologia.Board.toTuple_length
#print axioms WeiqiObsmetrologia.Board.toTuple_injective
#print axioms WeiqiObsmetrologia.Board.positionalSuperko_length_le
