import Obsmetrologia.Language.Positing.Valuation
import Obsmetrologia.Language.Positing.TruthOrder

/-!
# Weiqi — evidence moves are knowledge-monotone but not truth-monotone

Glass-sponge §17.5 made exact. This module reuses the corpus's existing FOUR
reading bilattice verbatim — `Obsmetrologia.Reading` and its knowledge join `Obsmetrologia.Reading.joinK`
(`Obsmetrologia/Language/Positing/Reading.lean`), the pointwise `Obsmetrologia.Valuation`
and its `Obsmetrologia.Valuation.leK`/`Obsmetrologia.Valuation.joinK` (`Obsmetrologia/Language/Positing/
Valuation.lean`), and the truth order `Obsmetrologia.Reading.leT`/`Obsmetrologia.Reading.TLE`
(`Obsmetrologia/Language/Positing/TruthOrder.lean`) — and adds no new reading
algebra. An **evidence move** at a locus is exactly `Obsmetrologia.Valuation.joinK v ev` for
an evidence valuation `ev` that is `Obsmetrologia.Reading.kBot` off the locus and carries
positive or negative evidence at it: joining new evidence into the knowledge
order is the reused primitive, not a new one.

* `knowledge_monotone_of_evidence` — every evidence move is `Obsmetrologia.Valuation.leK`
  above the valuation it starts from (reuses `Obsmetrologia.Reading.leK_joinK_left`
  pointwise).
* `evidence_not_truth_monotone` — a decide-checked witness that the *same*
  move is not truth-monotone: joining negative evidence onto the truth-top
  reading `t` (told true only) produces `⊤ₖ` (told both), which is *strictly
  below* `t` in the truth order `≤ₜ` — the move told more, and so, by the
  bilattice's own truth order, is *less true*.
* `not_forall_truth_monotone` — the general negative statement: no evidence
  move is truth-monotone for every reading, witnessed by the same instance.
-/

namespace WeiqiObsmetrologia
namespace Evidence

/-! ## Knowledge-order monotonicity -/

/-- **Every evidence move is knowledge-monotone.** Joining an evidence
valuation into `v` only ever raises `v` in the pointwise knowledge order — the
reused fact is `Obsmetrologia.Reading.leK_joinK_left`, lifted pointwise across the claim
points a `Obsmetrologia.Valuation` assigns. -/
theorem knowledge_monotone_of_evidence (v ev : Obsmetrologia.Valuation) :
    Obsmetrologia.Valuation.leK v (Obsmetrologia.Valuation.joinK v ev) := by
  intro phi
  exact Obsmetrologia.Reading.leK_joinK_left (v phi) (ev phi)

/-! ## Truth-order non-monotonicity -/

/-- **The witness.** Joining negative evidence (`ofSlots false true`) onto the
truth-top reading `tTop` ("told true only") produces `kTop` ("told both") — and
`kTop` sits *strictly below* `tTop` in the truth order: it is `≤ₜ`-below, and
it is not equal. Adding negative evidence lowers truth. -/
theorem evidence_lowers_truth :
    Obsmetrologia.Reading.TLE (Obsmetrologia.Reading.joinK Obsmetrologia.Reading.tTop (Obsmetrologia.Reading.ofSlots false true)) Obsmetrologia.Reading.tTop ∧
      Obsmetrologia.Reading.joinK Obsmetrologia.Reading.tTop (Obsmetrologia.Reading.ofSlots false true) ≠ Obsmetrologia.Reading.tTop := by
  constructor
  · decide
  · decide

/-- **Evidence moves are not truth-monotone.** The forward direction
`Obsmetrologia.Reading.leT a (joinK a e) = true` (the move never *lowers* truth) fails at the
same instance: negative evidence onto `tTop` is not `≤ₜ`-above `tTop`. -/
theorem evidence_not_truth_monotone :
    Obsmetrologia.Reading.leT Obsmetrologia.Reading.tTop (Obsmetrologia.Reading.joinK Obsmetrologia.Reading.tTop (Obsmetrologia.Reading.ofSlots false true)) = false := by
  decide

/-- **No evidence move is truth-monotone in general.** Restated as the
existential failure of the universally-quantified truth-monotonicity claim,
witnessed by `evidence_not_truth_monotone`. -/
theorem not_forall_truth_monotone :
    ¬ (∀ a e : Obsmetrologia.Reading, Obsmetrologia.Reading.leT a (Obsmetrologia.Reading.joinK a e) = true) := by
  intro h
  exact absurd (h Obsmetrologia.Reading.tTop (Obsmetrologia.Reading.ofSlots false true)) (by decide)

end Evidence
end WeiqiObsmetrologia

#print axioms WeiqiObsmetrologia.Evidence.knowledge_monotone_of_evidence
#print axioms WeiqiObsmetrologia.Evidence.evidence_lowers_truth
#print axioms WeiqiObsmetrologia.Evidence.evidence_not_truth_monotone
#print axioms WeiqiObsmetrologia.Evidence.not_forall_truth_monotone
