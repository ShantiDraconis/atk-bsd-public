import MCore.K13

namespace MCore.BackwardAudit

/-- Specification oracle for the rank part only; this is not full BSD. -/
def HypotheticalRankPartClosure : Prop :=
  ∀ d : BSDArithmeticAnalyticData, BSDRankPart d

theorem hypothetical_rank_part
    (H : HypotheticalRankPartClosure)
    (d : BSDArithmeticAnalyticData) :
    BSDRankPart d :=
  H d

#print axioms MCore.BackwardAudit.hypothetical_rank_part

end MCore.BackwardAudit
