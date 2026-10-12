import Obsmetrologia.Calculus.Order.SetNumberGraphTheory

/-!
# Weiqi — the board, positions, groups, and liberties

Raises the corpus's weiqi (go) claims from prose to a checked record. A **board**
is a finite type of points carrying a symmetric, irreflexive adjacency; a
**position** assigns each point a stone (or empty); a **group** is a maximal
connected set of same-colour occupied points; its **liberties** are the empty
points adjacent to it.

Groups are **not** given a fresh connectivity primitive. The corpus already
proves general finite-graph connectivity in
`Obsmetrologia/Calculus/Order/SetNumberGraphTheory.lean` (`namespace
Obsmetrologia.Discrete.Graph`): the reflexive/symmetric/transitive-closure
relation `Reach` (with `Reach.trans`, `Reach.symm` already proved there) is
exactly "there is a path in an undirected graph". A group is the `Reach`
component of `sameColorGraph` — the board's adjacency restricted to edges whose
both endpoints are occupied by the same stone. This module reuses `Reach`,
`Reach.trans`, and `Reach.symm` verbatim; it adds no union-find or connectivity
machinery of its own.
-/

namespace WeiqiObsmetrologia

/-- A board point's contents: empty, or occupied by a black or white stone. -/
inductive Stone
  | empty
  | black
  | white
  deriving DecidableEq, Repr

/-- A **position** assigns every board point a stone (or empty). -/
abbrev Position (Point : Type) := Point → Stone

/-- A **board**: a finite type of points (realized as an explicit duplicate-free,
complete enumeration — the same shape as `Obsmetrologia.Discrete.Graph.FinGraph.ExactPresentation`
in `SetNumberGraphTheory.lean`) together with a symmetric, irreflexive adjacency.
Definitions here are only executable enough to state the theorems below; no play
(placing stones, capturing) is implemented. -/
structure Board (Point : Type) where
  /-- The board's points, listed once each. -/
  points : List Point
  /-- `points` has no duplicate. -/
  points_nodup : points.Nodup
  /-- `points` names every point of the board. -/
  points_complete : ∀ p, p ∈ points
  /-- Adjacency between two points. -/
  adjacent : Point → Point → Bool
  /-- Adjacency is symmetric. -/
  adjacent_symm : ∀ p q, adjacent p q = adjacent q p
  /-- Adjacency is irreflexive: no point is adjacent to itself. -/
  adjacent_irrefl : ∀ p, adjacent p p = false

namespace Board

variable {Point : Type} (B : Board Point)

/-- The number of points on the board — `n` in "a board of `n` points". -/
def card : Nat := B.points.length

/-- The board's adjacency read as the library's `Graph` type
(`Obsmetrologia.Discrete.Graph`, `V → V → Bool`). -/
abbrev graph : Obsmetrologia.Discrete.Graph Point := B.adjacent

/-- The **same-colour-occupied restriction** of the board's adjacency at a
position: an edge `p ~ q` survives exactly when `p` and `q` are adjacent, carry
the same stone, and that stone is not empty. Groups are the `Reach`-components
of this graph. -/
def sameColorGraph (pos : Position Point) : Obsmetrologia.Discrete.Graph Point :=
  fun p q => B.adjacent p q && decide (pos p = pos q) && decide (pos p ≠ Stone.empty)

/-- `sameColorGraph` is symmetric (needed nowhere below as a hypothesis — `Reach`
is already closed under both edge orientations — but recorded because it is the
board-theoretic reason `Reach` is the right closure to reuse here). -/
theorem sameColorGraph_symm (pos : Position Point) (p q : Point) :
    B.sameColorGraph pos p q = B.sameColorGraph pos q p := by
  unfold sameColorGraph
  by_cases h : pos p = pos q
  · rw [h, B.adjacent_symm p q]
  · have hpq : decide (pos p = pos q) = false := decide_eq_false h
    have hqp : decide (pos q = pos p) = false := decide_eq_false (fun he => h he.symm)
    rw [hpq, hqp]
    simp

/-- An edge of `sameColorGraph` joins two points carrying the same stone. -/
theorem sameColorGraph_edge_same_color {pos : Position Point} {p q : Point}
    (h : B.sameColorGraph pos p q = true) : pos p = pos q := by
  unfold sameColorGraph at h
  have h2 := (Bool.and_eq_true _ _).mp h
  have h3 := (Bool.and_eq_true _ _).mp h2.1
  exact of_decide_eq_true h3.2

/-- A **group**: the points reachable from `root` through the same-colour-occupied
restricted graph, i.e. the `Obsmetrologia.Discrete.Graph.Reach`-component of `root` in
`sameColorGraph` — the connected component of same-colour occupied points
containing `root`. -/
def Group (pos : Position Point) (root : Point) : Point → Prop :=
  fun q => Obsmetrologia.Discrete.Graph.Reach (B.sameColorGraph pos) root q

/-- Every point of a group carries the same stone as the group's root — the
group is genuinely single-coloured. -/
theorem group_same_color {pos : Position Point} {root q : Point}
    (h : B.Group pos root q) : pos q = pos root := by
  induction h with
  | refl v => rfl
  | @step u v w hedge _ ih =>
      have huv : pos u = pos v := by
        rcases hedge with hedge | hedge
        · exact B.sameColorGraph_edge_same_color hedge
        · exact (B.sameColorGraph_edge_same_color hedge).symm
      rw [huv]
      exact ih

/-- The **liberties** of the group rooted at `root`: the empty points adjacent to
some stone of that group. -/
def Liberties (pos : Position Point) (root : Point) : Point → Prop :=
  fun p => pos p = Stone.empty ∧ ∃ q, B.Group pos root q ∧ B.adjacent q p = true

/-- **Liberties of a group are disjoint from its stones.** No point of an occupied
group's own liberties is itself a point of that group — a liberty is empty, every
group point carries the group's (non-empty) colour. -/
theorem liberties_disjoint_from_stones {pos : Position Point} {root : Point}
    (hocc : pos root ≠ Stone.empty) :
    ∀ p, B.Liberties pos root p → ¬ B.Group pos root p := by
  intro p hlib hgroup
  have hcolor : pos p = pos root := B.group_same_color hgroup
  exact hocc (hcolor.symm.trans hlib.1)

/-- **Groups sharing a point coincide.** If two roots' groups share a common
point, the groups are the very same set — this is exactly the disjoint-or-equal
law for `Reach`-components (the analogue of
`Obsmetrologia.Discrete.EquivalenceRelation.cls_eq_of_overlap` in `SetNumberGraphTheory.lean`,
here for reachability instead of an explicit equivalence relation). -/
theorem groups_eq_or_disjoint {pos : Position Point} {r1 r2 : Point}
    (hoverlap : ∃ p, B.Group pos r1 p ∧ B.Group pos r2 p) :
    ∀ q, B.Group pos r1 q ↔ B.Group pos r2 q := by
  obtain ⟨p, h1, h2⟩ := hoverlap
  have hr2r1 : Obsmetrologia.Discrete.Graph.Reach (B.sameColorGraph pos) r2 r1 :=
    Obsmetrologia.Discrete.Graph.Reach.trans h2 (Obsmetrologia.Discrete.Graph.Reach.symm h1)
  have hr1r2 : Obsmetrologia.Discrete.Graph.Reach (B.sameColorGraph pos) r1 r2 :=
    Obsmetrologia.Discrete.Graph.Reach.trans h1 (Obsmetrologia.Discrete.Graph.Reach.symm h2)
  intro q
  constructor
  · intro hq; exact Obsmetrologia.Discrete.Graph.Reach.trans hr2r1 hq
  · intro hq; exact Obsmetrologia.Discrete.Graph.Reach.trans hr1r2 hq

/-- **Two distinct groups of the same colour share no point.** Groups are
components: if the point-sets of two groups are not identical, they cannot
overlap — the contrapositive of `groups_eq_or_disjoint`. (Every group is
automatically single-coloured, by `group_same_color`, so "distinct groups of the
same colour" is exactly "distinct groups".) -/
theorem groups_disjoint_of_ne {pos : Position Point} {r1 r2 : Point}
    (hne : ¬ (∀ q, B.Group pos r1 q ↔ B.Group pos r2 q)) :
    ¬ ∃ p, B.Group pos r1 p ∧ B.Group pos r2 p :=
  fun hoverlap => hne (B.groups_eq_or_disjoint hoverlap)

end Board

end WeiqiObsmetrologia

#print axioms WeiqiObsmetrologia.Board.sameColorGraph_symm
#print axioms WeiqiObsmetrologia.Board.sameColorGraph_edge_same_color
#print axioms WeiqiObsmetrologia.Board.group_same_color
#print axioms WeiqiObsmetrologia.Board.liberties_disjoint_from_stones
#print axioms WeiqiObsmetrologia.Board.groups_eq_or_disjoint
#print axioms WeiqiObsmetrologia.Board.groups_disjoint_of_ne
