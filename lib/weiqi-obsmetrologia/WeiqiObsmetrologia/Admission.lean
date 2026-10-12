import ObsmetrologiaComputing.HoareProgram
import Obsmetrologia.Calculus.Logic.LinearLogicChu
import WeiqiObsmetrologia.Board
import WeiqiObsmetrologia.Ko

/-!
# Weiqi — admitting a move as a Hoare program, and the predicate-Chu bridge

Two constructions, both against existing library carriers, neither redefining
them:

1. **A predicate-Chu bridge** (`boolPredicateChu`, `functionPredicateChuMap`,
   `boolean_hoare_is_lax_chu`), against `Obsmetrologia.ChuSpace`/`Obsmetrologia.ChuMap`
   (`Obsmetrologia/Calculus/Logic/LinearLogicChu.lean`). Committed, cleaned,
   from the 2026-07-18 territory audit's "A predicate-Chu bridge compiled
   during this audit"
   (`lib/emsenn/services/561-group/services/561-group-services-section/
   services/561-group-operations-services-section/services/561-group-
   enterprise-services-section/services/561-group-board-of-directors/lib/
   legacy/2026-08-03-executive-office/services/leader-movement-team/content/
   documents/articles/notes/2026/07/18/2026-07-18-gyrobifastigial-chu-hoare-
   territory-audit.md`, §"A predicate-Chu bridge compiled during this
   audit"), which recorded it as **lean-checked but not committed**. It is
   general (no weiqi content); it lands here because this module is the first
   Obsmetrologia consumer that needed a Hoare/Chu correspondence.

2. **Move admission** (`MoveInput`, `Legal`, `admission`), against
   `Obsmetrologia.Computing.HoareProgram`
   (`Obsmetrologia/Computing/HoareProgram.lean`) and the ko regimes of
   `Ko.lean`. A move's precondition is the conjunction of its legality
   predicates; its postcondition is that the extended trace still satisfies
   positional superko. `admission_seq` is the transport theorem: two
   admissions along a shared trace compose, with the second admission's
   history-regime obligation discharged by the first's postcondition rather
   than independently assumed — genuine Hoare sequencing, not two
   side-by-side facts.
-/

namespace WeiqiObsmetrologia

/-! ## A predicate-Chu bridge -/

/-- The **predicate Chu space** over a state carrier `S`: points are states,
states (as a Chu carrier) are Boolean predicates `S → Bool`, and the
FOUR-valued matrix records `⟨s, p⟩ ↦ Obsmetrologia.Reading.ofSlots (p s) false` — the
predicate evaluated at the state, told positively (and never negatively). -/
def boolPredicateChu (S : Type) : Obsmetrologia.ChuSpace where
  pts := S
  sts := S → Bool
  r := fun s p => Obsmetrologia.Reading.ofSlots (p s) false

/-- A deterministic state transition `move : S → T` induces a **Chu transform**
`boolPredicateChu S → boolPredicateChu T`: forward on states by `move`,
backward on predicates by precomposition (pullback), `post ↦ post ∘ move`.
Adjointness is the definitional equality `post (move s) = (post ∘ move) s`. -/
def functionPredicateChuMap {S T : Type} (move : S → T) :
    Obsmetrologia.ChuMap (boolPredicateChu S) (boolPredicateChu T) where
  fwd := move
  bwd := fun post s => post (move s)
  adj := fun _ _ => rfl

/-- **Boolean Hoare preservation is pulled-back postcondition inclusion.** For
a deterministic Boolean program `pre / move / post`, ordinary Hoare
preservation `∀ s, pre s = true → post (move s) = true` is *exactly* `∀ s,
pre s = true → (functionPredicateChuMap move).bwd post s = true` — the Chu
transform's backward (pullback) action applied to `post`. A Boolean
`HoareProgram` *is* a lax Chu-space inclusion `pre ≤ move*(post)` on the
predicate Chu space, structurally, not by analogy. -/
theorem boolean_hoare_is_lax_chu
    {S T : Type} (pre : S → Bool) (move : S → T) (post : T → Bool)
    (h : ∀ s, pre s = true → post (move s) = true) :
    ∀ s, pre s = true → (functionPredicateChuMap move).bwd post s = true :=
  h

end WeiqiObsmetrologia

namespace WeiqiObsmetrologia
namespace Admission

open Obsmetrologia.Computing

variable {Point : Type}

/-- The data of a candidate move: the trace so far (`history`, guaranteed
non-empty), the point played, the colour played, and the position that
results from playing it. `Admission` does not derive `next` from `history`
(no captures are computed — Board.lean and this module state board statics
and legality shape, not play); it only checks that whichever resulting
position is supplied satisfies the legality predicates below. -/
structure MoveInput (Point : Type) where
  /-- The trace so far. -/
  history : Ko.Trace Point
  /-- `history` is never empty — there is always a current position. -/
  history_ne : history ≠ []
  /-- The position that results from playing the move. -/
  next : Position Point
  /-- The point played. -/
  point : Point
  /-- The stone colour played. -/
  color : Stone

namespace MoveInput

/-- The current position: the last entry of `history`. -/
def current (m : MoveInput Point) : Position Point := m.history.getLast m.history_ne

end MoveInput

/-- **Not off-board.** Vacuous by construction: `Point` already ranges over
exactly the board's points (`Board.lean`), so there is no off-board point to
exclude. Named `True`, not faked as a nontrivial check the encoding cannot
state. -/
def NotOffBoard (_ : Point) : Prop := True

/-- **Not occupied.** The point played must be empty in the current position. -/
def NotOccupied (m : MoveInput Point) : Prop := m.current m.point = Stone.empty

/-- **Not suicide**, under the simplest suicide rule: the group the played
stone joins, read off in the supplied resulting position `m.next`, has at
least one liberty there. -/
def NotSuicide (B : Board Point) (m : MoveInput Point) : Prop :=
  ∃ p, B.Liberties m.next m.point p

/-- **The history already satisfies positional superko** — the regime
predicate on the trace, checked on what came *before* this move. -/
def HistoryRegimeOk (m : MoveInput Point) : Prop := Ko.PositionalSuperko m.history

/-- **The candidate position is fresh**: it has not occurred anywhere in
`history`. Together with `HistoryRegimeOk` this is exactly what a positional
superko check performs before admitting a move. -/
def FreshPosition (m : MoveInput Point) : Prop := m.next ∉ m.history

/-- **Legality**: the conjunction of the board-static and ko-regime
predicates. -/
def Legal (B : Board Point) (m : MoveInput Point) : Prop :=
  NotOffBoard m.point ∧ NotOccupied m ∧ NotSuicide B m ∧
    HistoryRegimeOk m ∧ FreshPosition m

/-- **The resulting trace still satisfies positional superko.** -/
def RegimeHolds (m : MoveInput Point) : Prop :=
  Ko.PositionalSuperko (m.history ++ [m.next])

/-- Appending a fresh element to a duplicate-free list keeps it duplicate-free
— the one list fact `admission`'s `preserves` obligation reduces to. -/
theorem nodup_append_of_fresh {α : Type} {l : List α} {x : α}
    (h : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨h, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.Pairwise.nil⟩
  · intro a ha b hb heq
    subst heq
    have hbx : a = x := List.mem_singleton.mp hb
    subst hbx
    exact hx ha

/-- **The admission**: a `HoareProgram` whose precondition is `Legal` and
whose postcondition is that the extended trace still satisfies positional
superko. The move itself is the identity on `MoveInput` — admission checks and
certifies a proposed move, it does not compute one. -/
def admission (B : Board Point) : HoareProgram (MoveInput Point) (MoveInput Point) where
  precondition := Legal B
  move := id
  postcondition := RegimeHolds
  preserves := fun _ ⟨_, _, _, hreg, hfresh⟩ => nodup_append_of_fresh hreg hfresh

/-- **Transport of the invariant.** Two admissions along a shared trace
compose: if `m1` is admitted, `m2`'s history is exactly `m1`'s resulting
trace, and `m2` meets every legality predicate *except* `HistoryRegimeOk`
(which is not independently assumed), then `m2`'s resulting trace still
satisfies positional superko. `m2`'s history-regime obligation is discharged
by `m1`'s admitted postcondition (`admission B`'s `preserves`), not
re-derived — this is Hoare-program sequencing, not two side-by-side facts. -/
theorem admission_seq (B : Board Point) (m1 m2 : MoveInput Point)
    (hlink : m2.history = m1.history ++ [m1.next])
    (h1 : Legal B m1)
    (h2rest : NotOffBoard m2.point ∧ NotOccupied m2 ∧ NotSuicide B m2 ∧ FreshPosition m2) :
    RegimeHolds m2 := by
  have hreg1 : RegimeHolds m1 := (admission B).preserves m1 h1
  have hreg2 : HistoryRegimeOk m2 := by
    show Ko.PositionalSuperko m2.history
    rw [hlink]
    exact hreg1
  exact nodup_append_of_fresh hreg2 h2rest.2.2.2

end Admission
end WeiqiObsmetrologia

#print axioms WeiqiObsmetrologia.boolPredicateChu
#print axioms WeiqiObsmetrologia.functionPredicateChuMap
#print axioms WeiqiObsmetrologia.boolean_hoare_is_lax_chu
#print axioms WeiqiObsmetrologia.Admission.nodup_append_of_fresh
#print axioms WeiqiObsmetrologia.Admission.admission
#print axioms WeiqiObsmetrologia.Admission.admission_seq
