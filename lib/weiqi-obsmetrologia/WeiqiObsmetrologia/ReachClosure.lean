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

/-- Closure preserves joins of seed predicates at one fixed position. There
is no need to recompute the graph: every path's origin lies in one seed. -/
theorem reachClosure_union (pos : Position Point)
    (seed other : Point → Prop) :
    B.reachClosure pos (fun q => seed q ∨ other q) =
      (fun q => B.reachClosure pos seed q ∨ B.reachClosure pos other q) := by
  funext target
  apply propext
  constructor
  · rintro ⟨origin, horigin, path⟩
    rcases horigin with hseed | hother
    · exact Or.inl ⟨origin, hseed, path⟩
    · exact Or.inr ⟨origin, hother, path⟩
  · intro h
    rcases h with ⟨origin, hseed, path⟩ | ⟨origin, hother, path⟩
    · exact ⟨origin, Or.inl hseed, path⟩
    · exact ⟨origin, Or.inr hother, path⟩

/-- Saturate, merge a new seed, and saturate again = merge then saturate.
This is an exact incremental reuse law, not a measured performance claim.
It is specific to this fixed-position graph; ko/capture can change its edges. -/
theorem reachClosure_merge (pos : Position Point)
    (seed other : Point → Prop) :
    B.reachClosure pos (fun q => B.reachClosure pos seed q ∨ other q) =
    B.reachClosure pos (fun q => seed q ∨ other q) := by
  calc
    B.reachClosure pos (fun q => B.reachClosure pos seed q ∨ other q) =
        (fun q => B.reachClosure pos (B.reachClosure pos seed) q ∨
          B.reachClosure pos other q) :=
      B.reachClosure_union pos (B.reachClosure pos seed) other
    _ = (fun q => B.reachClosure pos seed q ∨
        B.reachClosure pos other q) := by
      rw [B.reachClosure_idempotent pos seed]
    _ = B.reachClosure pos (fun q => seed q ∨ other q) :=
      (B.reachClosure_union pos seed other).symm

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


/-! ## Qi as the typed external boundary of an occupied connected carrier -/

/-- In conventional weiqi, `qi` (liberties) names the empty frontier of a
stone string. This is a QUALIFIED interface to the existing liberty boundary,
not a scalar vitality score: an empty root cannot be supplied as an
`OccupiedCarrier`. No ko or capture-history legality is inferred here. -/
def qi (pos : Position Point) (carrier : OccupiedCarrier pos) : Point → Prop :=
  B.libertyBoundary pos carrier.contains

/-- Qi is outside the occupied string, by the previously proved boundary
disjointness. It is not itself an occupied territory claim. -/
theorem qi_disjoint_occupied (pos : Position Point) (carrier : OccupiedCarrier pos) :
    ∀ q, B.qi pos carrier q →
      ¬ (B.closeOccupiedCarrier pos carrier).contains q := by
  exact B.libertyBoundary_disjoint_occupied pos carrier

/-- More seed evidence cannot erase a fixed-position liberty boundary;
capture/ko transitions are NOT fixed-position seed inclusions. -/
theorem libertyBoundary_monotone (pos : Position Point)
    {seed other : Point → Prop} (h : ∀ q, seed q → other q) :
    ∀ q, B.libertyBoundary pos seed q → B.libertyBoundary pos other q := by
  intro q hq
  obtain ⟨hempty, p, hreach, hadj⟩ := hq
  exact ⟨hempty, p, B.reachClosure_monotone pos h p hreach, hadj⟩

/-- Qi/frontier respects a join of seed carriers at one position. Shared
liberties are sets, not summed counts: this is an exact union law suitable
for incremental deduplication, not a life, influence, or strategy theorem. -/
theorem libertyBoundary_union (pos : Position Point)
    (seed other : Point → Prop) :
    B.libertyBoundary pos (fun p => seed p ∨ other p) =
      (fun q => B.libertyBoundary pos seed q ∨ B.libertyBoundary pos other q) := by
  funext q
  apply propext
  constructor
  · rintro ⟨hempty, p, ⟨origin, horigin, path⟩, hadj⟩
    rcases horigin with hseed | hother
    · exact Or.inl ⟨hempty, p, ⟨origin, hseed, path⟩, hadj⟩
    · exact Or.inr ⟨hempty, p, ⟨origin, hother, path⟩, hadj⟩
  · intro h
    rcases h with ⟨hempty, p, ⟨origin, hseed, path⟩, hadj⟩ |
                   ⟨hempty, p, ⟨origin, hother, path⟩, hadj⟩
    · exact ⟨hempty, p, ⟨origin, Or.inl hseed, path⟩, hadj⟩
    · exact ⟨hempty, p, ⟨origin, Or.inr hother, path⟩, hadj⟩

/-- Once the connected carrier has been saturated, a second saturation
does not discover new qi. This is a fixed-position caching/invalidation law;
it deliberately says nothing about which frontiers survive the next move. -/
theorem libertyBoundary_saturated (pos : Position Point) (seed : Point → Prop) :
    B.libertyBoundary pos (B.reachClosure pos seed) =
      B.libertyBoundary pos seed := by
  funext q
  apply propext
  constructor
  · rintro ⟨hempty, p, ⟨mid, ⟨origin, horigin, first⟩, last⟩, hadj⟩
    exact ⟨hempty, p, ⟨origin, horigin, Reach.trans first last⟩, hadj⟩
  · rintro ⟨hempty, p, ⟨origin, horigin, path⟩, hadj⟩
    exact ⟨hempty, p, ⟨origin, ⟨origin, horigin, Reach.refl origin⟩, path⟩, hadj⟩

/-! ## Contact incidence: an edge witness, not a holographic length -/

/-- A liberty CONTACT retains the occupied endpoint and the adjacent empty
endpoint of a qualified frontier. It is the source-facing incidence relation
from which a future finite crossing count could be measured. In contrast,
`qi` only remembers whether a given empty endpoint has SOME such contact;
distinct contacts may share that endpoint. Neither object is an RT surface,
a Crofton geodesic, a territory claim, or a move-history invariant. -/
def LibertyContact (pos : Position Point) (carrier : OccupiedCarrier pos)
    (stone emptyPoint : Point) : Prop :=
  B.reachClosure pos carrier.contains stone ∧
    pos emptyPoint = Stone.empty ∧
    B.adjacent stone emptyPoint = true

/-- A liberty exists precisely when at least one qualified contact ends there.
This is a loss-of-multiplicity projection: contact evidence can be kept for
intersection accounting, whereas qi deduplicates by empty endpoint. -/
theorem qi_iff_exists_libertyContact (pos : Position Point)
    (carrier : OccupiedCarrier pos) (q : Point) :
    B.qi pos carrier q ↔ ∃ p, B.LibertyContact pos carrier p q := by
  constructor
  · rintro ⟨hempty, p, hreach, hadj⟩
    exact ⟨p, hreach, hempty, hadj⟩
  · rintro ⟨p, hreach, hempty, hadj⟩
    exact ⟨hempty, p, hreach, hadj⟩

/-- A qualified contact really starts at an occupied stone. In particular
the reflexive reachability of an empty root is not a contact witness. -/
theorem libertyContact_stone_occupied (pos : Position Point)
    (carrier : OccupiedCarrier pos) (p q : Point)
    (h : B.LibertyContact pos carrier p q) :
    pos p ≠ Stone.empty := by
  exact B.reachClosure_preserves_occupation pos carrier.contains
    carrier.occupied p h.1

/-- A contact ends outside the closed occupied carrier. Its exterior point
cannot be silently counted as one more stone or as settled territory. -/
theorem libertyContact_exterior (pos : Position Point)
    (carrier : OccupiedCarrier pos) (p q : Point)
    (h : B.LibertyContact pos carrier p q) :
    ¬ B.reachClosure pos carrier.contains q := by
  intro hmember
  have hoccupied : pos q ≠ Stone.empty :=
    B.reachClosure_preserves_occupation pos carrier.contains
      carrier.occupied q hmember
  exact hoccupied h.2.1

/-! ## Exactly when liberty endpoints retain their contact witnesses -/

/-- A contact witness retains both endpoints and the original proof of
qualified fixed-position stone–empty adjacency. This is a dependent witness
over the original Board/Reach carrier, not a separate graph representation. -/
structure ContactWitness (B : Board Point) (pos : Position Point)
    (carrier : B.OccupiedCarrier pos) where
  stone : Point
  endpoint : Point
  incidence : B.LibertyContact pos carrier stone endpoint

/-- Forget the occupied endpoint and its proof, keeping only the liberty.
That is the same information discarded by the ordinary qi-set projection. -/
def contactEndpoint (pos : Position Point) (carrier : B.OccupiedCarrier pos)
    (w : B.ContactWitness pos carrier) : Point :=
  w.endpoint

/-- A liberty is supported precisely when a source-qualified contact witness
ends there. We do not infer a boundary measure from mere existence. -/
theorem qi_iff_contactEndpoint_supported (pos : Position Point)
    (carrier : B.OccupiedCarrier pos) (q : Point) :
    B.qi pos carrier q ↔
      ∃ w : B.ContactWitness pos carrier, B.contactEndpoint pos carrier w = q := by
  constructor
  · intro hqi
    obtain ⟨p, hcontact⟩ := (B.qi_iff_exists_libertyContact pos carrier q).mp hqi
    exact ⟨⟨p, q, hcontact⟩, rfl⟩
  · rintro ⟨⟨p, endpoint, hcontact⟩, hq⟩
    change endpoint = q at hq
    subst endpoint
    exact (B.qi_iff_exists_libertyContact pos carrier q).mpr ⟨p, hcontact⟩

/-- Exact source-reconstruction gate: forgetting the stone is injective
IF AND ONLY IF every liberty has at most one qualified contact stone.
Crossing counts and distinct-liberty counts can coincide without claiming
this stronger source-recovery law, so do not reverse this implication by a
mere equality of totals. -/
theorem contactEndpoint_injective_iff_unique (pos : Position Point)
    (carrier : B.OccupiedCarrier pos) :
    Function.Injective (B.contactEndpoint pos carrier) ↔
      ∀ (q p₁ p₂ : Point),
        B.LibertyContact pos carrier p₁ q →
        B.LibertyContact pos carrier p₂ q → p₁ = p₂ := by
  constructor
  · intro hinj q p₁ p₂ h₁ h₂
    have heq : (⟨p₁, q, h₁⟩ : B.ContactWitness pos carrier) =
        ⟨p₂, q, h₂⟩ := hinj rfl
    exact congrArg (fun w : B.ContactWitness pos carrier => w.stone) heq
  · intro unique w₁ w₂ heq
    rcases w₁ with ⟨s₁, q₁, h₁⟩
    rcases w₂ with ⟨s₂, q₂, h₂⟩
    change q₁ = q₂ at heq
    subst q₂
    have hs : s₁ = s₂ := unique q₁ s₁ s₂ h₁ h₂
    subst s₂
    rfl

/-- Two different stones touching one liberty prove genuine non-recovery
of contact incidence from the liberty endpoint alone. This is a general
theorem requiring actual witnesses, not a hard-coded diagram or quantum
entanglement premise. -/
theorem contactEndpoint_noninjective_of_shared (pos : Position Point)
    (carrier : B.OccupiedCarrier pos) (q p₁ p₂ : Point)
    (hne : p₁ ≠ p₂)
    (h₁ : B.LibertyContact pos carrier p₁ q)
    (h₂ : B.LibertyContact pos carrier p₂ q) :
    ¬ Function.Injective (B.contactEndpoint pos carrier) := by
  intro hinj
  exact hne ((B.contactEndpoint_injective_iff_unique pos carrier).mp
    hinj q p₁ p₂ h₁ h₂)

end Board
end WeiqiObsmetrologia

#print axioms WeiqiObsmetrologia.Board.reachClosure_extensive
#print axioms WeiqiObsmetrologia.Board.reachClosure_monotone
#print axioms WeiqiObsmetrologia.Board.reachClosure_idempotent
#print axioms WeiqiObsmetrologia.Board.reachClosure_union
#print axioms WeiqiObsmetrologia.Board.reachClosure_merge
#print axioms WeiqiObsmetrologia.Board.reachClosure_adjunction
#print axioms WeiqiObsmetrologia.Board.reachClosure_fixed_iff_closed
#print axioms WeiqiObsmetrologia.Board.reachClosure_preserves_occupation
#print axioms WeiqiObsmetrologia.Board.empty_root_not_occupied
#print axioms WeiqiObsmetrologia.Board.libertyBoundary_singleton_iff_liberties
#print axioms WeiqiObsmetrologia.Board.libertyBoundary_disjoint_occupied
#print axioms WeiqiObsmetrologia.Board.qi_iff_exists_libertyContact
#print axioms WeiqiObsmetrologia.Board.libertyContact_stone_occupied
#print axioms WeiqiObsmetrologia.Board.libertyContact_exterior
#print axioms WeiqiObsmetrologia.Board.qi_iff_contactEndpoint_supported
#print axioms WeiqiObsmetrologia.Board.contactEndpoint_injective_iff_unique
#print axioms WeiqiObsmetrologia.Board.contactEndpoint_noninjective_of_shared
