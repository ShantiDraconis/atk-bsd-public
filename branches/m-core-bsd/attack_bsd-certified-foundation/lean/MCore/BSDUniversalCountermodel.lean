import MCore.K12

namespace MCore

/-- Countermodel to the current over-broad abstract producer.  The record
    BSDArithmeticAnalyticData currently permits arbitrary pairs of naturals,
    including pairs that do not arise from any elliptic curve. -/
def rankOrderMismatchData : BSDArithmeticAnalyticData :=
  { mordellWeilRank := 0
    analyticOrderAtOne := 1 }

/-- The mismatch record refutes BSDRankPart definitionally. -/
theorem rankOrderMismatchData_not_BSDRankPart :
    ¬ BSDRankPart rankOrderMismatchData := by
  simp [BSDRankPart, rankOrderMismatchData]

/-- Therefore universal quantification over all current abstract records is
    false. This is a semantic countermodel to the abstraction, not a
    counterexample to BSD for elliptic curves. -/
theorem universal_abstract_BSDRankPart_false :
    ¬ (∀ d : BSDArithmeticAnalyticData, BSDRankPart d) := by
  intro h
  exact rankOrderMismatchData_not_BSDRankPart (h rankOrderMismatchData)

/-- The repaired terminal producer must quantify only realizable arithmetic /
    analytic data coming from the intended elliptic-curve semantics. -/
def BSDRankPartRestricted
    (Realizable : BSDArithmeticAnalyticData → Prop) : Prop :=
  ∀ d : BSDArithmeticAnalyticData, Realizable d → BSDRankPart d

theorem unrestricted_not_a_valid_terminal_producer :
    ¬ (∀ d : BSDArithmeticAnalyticData, BSDRankPart d) :=
  universal_abstract_BSDRankPart_false

#print axioms rankOrderMismatchData_not_BSDRankPart
#print axioms universal_abstract_BSDRankPart_false
#print axioms unrestricted_not_a_valid_terminal_producer

end MCore
