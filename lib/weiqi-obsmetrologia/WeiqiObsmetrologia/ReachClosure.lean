import WeiqiObsmetrologia.Board

/-!
# Weiqi — source-preserving connected carriers and their closure

The Board module already transports the original Obsmetrologia finite-graph
Reach relation into same-colour strings. This module derives the induced
closure on predicates over that SAME graph, without inventing a second
connectivity engine or identifying it with Settling.Closure on Charges.

At a fixed board position, reachClosure is extensive, monotone, and idempotent.
Its closed predicates form a preorder of subobjects, and reachClosure is
left adjoint to their inclusion (the least closed carrier above a seed).
Singleton closure recovers the existing Board.Group and its liberty boundary.

The occupied-carrier qualification is essential: Reach is reflexive, so the
unqualified Group at an empty root contains that empty root. Such a value is
a valid Reach component but NOT an occupied Go string. Proofs below refuse
to turn that distinction into a claim of territory, ownership, a legal move,
a stable future group, or an independently received result.

The closure is position-indexed. It does not prove monotonicity across legal
moves, positional superko, causal-set interval transport, or the original
Mark-generated Settling closure. Those require separate source-bound maps.
-/

namespace WeiqiObsmetrologia
namespace Board

open Obsmetrologia.Discrete.Graph

variable {Point : Type} (B : Board Point)

/-- Close a seed predicate under paths of the EXISTING same-colour occupied
board graph. A seed at an empty point remains in its closure by reflexivity;
the occupied carrier below enforces the Go-string reading. -/
def reachClosure (pos : Position Point) (seed : Point → Prop) : Point → Prop :=
  fun target => ∃ origin, seed origin ∧ Reach (B.sameColorGraph pos) origin target

/-- Every seed point survives the closure; Reach.refl is its witness. -/
theorem reachClosure_extensive (pos : Position Point) (seed : Point → Prop) :
    ∀ q, seed q → B.reachClosure pos seed q := by
  intro q hseed
  exact ⟨q, hseed, Reach.refl q⟩

/-- Inclusion between seed predicates is preserved by closure. -/
theorem reachClosure_monotone (pos : Position Point)
    {seed carrier : Point → Prop}
    (h : ∀ q, seed q → carrier q) :
    ∀ q, B.reachClosure pos seed q → B.reachClosure pos carrier q := by
  intro q hq
  obtain ⟨origin, horigin, path⟩ := hq
  exact ⟨origin, h origin horigin, path⟩

/-- A second closure adds no points: original Reach.trans supplies composition. -/
theorem reachClosure_idempotent (pos : Position Point) (seed : Point → Prop) :
    B.reachClosure pos (B.reachClosure pos seed) = B.reachClosure pos seed := by
  funext q
  apply propext
  constructor
  · intro hq
    obtain ⟨middle, ⟨origin, horigin, first⟩, last⟩ := hq
    exact ⟨origin, horigin, Reach.trans first last⟩
  · intro hq
    obtain ⟨origin, horigin, path⟩ := hq
    exact ⟨origin, ⟨origin, horigin, Reach.refl origin⟩, path⟩

/-- A carrier predicate is closed under the existing position-specific paths. -/
def ReachClosed (pos : Position Point) (carrier : Point → Prop) : Prop :=
  ∀ (p q : Point), carrier p →
    Reach (B.sameColorGraph pos) p q → carrier q

/-- Reach closure constructs a closed carrier, not just a finite search result. -/
theorem reachClosure_closed (pos : Position Point) (seed : Point → Prop) :
    B.ReachClosed pos (B.reachClosure pos seed) := by
  intro p q hp path
  obtain ⟨origin, horigin, first⟩ := hp
  exact ⟨origin, horigin, Reach.trans first path⟩

/-- Leastness: every closed carrier containing the seed contains its closure. -/
theorem reachClosure_least (pos : Position Point)
    (seed carrier : Point → Prop) (hclosed : B.ReachClosed pos carrier)
    (hcontains : ∀ q, seed q → carrier q) :
    ∀ q, B.reachClosure pos seed q → carrier q := by
  intro q hq
  obtain ⟨origin, horigin, path⟩ := hq
  exact hclosed origin q (hcontains origin horigin) path

/-- Preorder-reflection / Galois connection into closed subobjects. For a closed
target, a map from the closure is equivalent to a map from its seed. This is the
precise thin-category fact, not an asserted equivalence of whole categories. -/
theorem reachClosure_adjunction (pos : Position Point)
    (seed carrier : Point → Prop) (hclosed : B.ReachClosed pos carrier) :
    (∀ q, B.reachClosure pos seed q → carrier q) ↔
    (∀ q, seed q → carrier q) := by
  constructor
  · intro h q hseed
    exact h q (B.reachClosure_extensive pos seed q hseed)
  · intro h q hq
    exact B.reachClosure_least pos seed carrier hclosed h q hq

/-- Closed carriers are exactly fixed points of the reachability closure. -/
theorem reachClosure_fixed_iff_closed (pos : Position Point)
    (carrier : Point → Prop) :
    (B.reachClosure pos carrier = carrier) ↔ B.ReachClosed pos carrier := by
  constructor
  · intro h p q hp path
    have hq : B.reachClosure pos carrier q := ⟨p, hp, path⟩
    rw [h] at hq
    exact hq
  · intro h
    funext q
    apply propext
    constructor
    · exact B.reachClosure_least pos carrier carrier h (fun _ hp => hp) q
    · exact B.reachClosure_extensive pos carrier q

/-- The existing rooted Board.Group is precisely singleton reach closure. -/
theorem reachClosure_singleton_iff_group (pos : Position Point) (root q : Point) :
    B.reachClosure pos (fun p => p = root) q ↔ B.Group pos root q := by
  constructor
  · rintro ⟨origin, heq, path⟩
    subst origin
    exact path
  · intro path
    exact ⟨root, rfl, path⟩

/-- A type-level witness that every contained point is an occupied stone.
This prevents empty-root reach components from masquerading as Go strings. -/
structure OccupiedCarrier (pos : Position Point) where
  contains : Point → Prop
  occupied : ∀ q, contains q → pos q ≠ Stone.empty

/-- Reach along same-colour stone edges preserves occupancy of qualified seeds. -/
theorem reachClosure_preserves_occupation (pos : Position Point)
    (seed : Point → Prop)
    (hseed : ∀ q, seed q → pos q ≠ Stone.empty) :
    ∀ q, B.reachClosure pos seed q → pos q ≠ Stone.empty := by
  intro q hq
  obtain ⟨origin, horigin, path⟩ := hq
  have hgroup : B.Group pos origin q := path
  have hcolor : pos q = pos origin := B.group_same_color hgroup
  rw [hcolor]
  exact hseed origin horigin

/-- Reach closure lifted to genuine occupied carriers, keeping its witness. -/
def closeOccupiedCarrier (pos : Position Point)
    (carrier : OccupiedCarrier pos) : OccupiedCarrier pos where
  contains := B.reachClosure pos carrier.contains
  occupied := B.reachClosure_preserves_occupation pos carrier.contains carrier.occupied

/-- Negative control: an empty root cannot furnish an occupied singleton
carrier, even though reflexive Reach does give it a Group membership. -/
theorem empty_root_not_occupied (pos : Position Point) (root : Point)
    (hempty : pos root = Stone.empty) :
    ¬ (∀ q, B.reachClosure pos (fun p => p = root) q →
        pos q ≠ Stone.empty) := by
  intro h
  exact h root (B.reachClosure_extensive pos (fun p => p = root) root rfl) hempty

/-- The outside empty-point boundary of a closed seed carrier at this position.
This is a liberty FRONTIER, not territory, life, influence, or authorization. -/
def libertyBoundary (pos : Position Point) (seed : Point → Prop) : Point → Prop :=
  fun q => pos q = Stone.empty ∧
    ∃ p, B.reachClosure pos seed p ∧ B.adjacent p q = true

/-- The new carrier's empty frontier is exactly the pre-existing Go Liberties
predicate when seeded by a root. There is no second liberties definition. -/
theorem libertyBoundary_singleton_iff_liberties
    (pos : Position Point) (root q : Point) :
    B.libertyBoundary pos (fun p => p = root) q ↔
    B.Liberties pos root q := by
  constructor
  · rintro ⟨hempty, p, hreach, hadj⟩
    exact ⟨hempty, p, (B.reachClosure_singleton_iff_group pos root p).mp hreach, hadj⟩
  · rintro ⟨hempty, p, hgroup, hadj⟩
    exact ⟨hempty, p, (B.reachClosure_singleton_iff_group pos root p).mpr hgroup, hadj⟩

/-- On an occupied carrier, an empty liberty cannot already be in its closure.
Thus the frontier is distinguished from the supported connected body. -/
theorem libertyBoundary_disjoint_occupied (pos : Position Point)
    (carrier : OccupiedCarrier pos) :
    ∀ q, B.libertyBoundary pos carrier.contains q →
      ¬ B.reachClosure pos carrier.contains q := by
  intro q hboundary hmember
  have hoccupied : pos q ≠ Stone.empty :=
    B.reachClosure_preserves_occupation pos carrier.contains
      carrier.occupied q hmember
  exact hoccupied hboundary.1

end Board
end WeiqiObsmetrologia

#print axioms WeiqiObsmetrologia.Board.reachClosure_extensive
#print axioms WeiqiObsmetrologia.Board.reachClosure_monotone
#print axioms WeiqiObsmetrologia.Board.reachClosure_idempotent
#print axioms WeiqiObsmetrologia.Board.reachClosure_adjunction
#print axioms WeiqiObsmetrologia.Board.reachClosure_fixed_iff_closed
#print axioms WeiqiObsmetrologia.Board.reachClosure_preserves_occupation
#print axioms WeiqiObsmetrologia.Board.empty_root_not_occupied
#print axioms WeiqiObsmetrologia.Board.libertyBoundary_singleton_iff_liberties
#print axioms WeiqiObsmetrologia.Board.libertyBoundary_disjoint_occupied
