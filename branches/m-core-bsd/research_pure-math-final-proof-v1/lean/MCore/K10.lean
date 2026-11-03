import MCore.K9
namespace MCore

/-- The exact conjunction of the two K9 directional obligations. -/
def BSDRankTwoDirections (d : BSDRankData) : Prop :=
  BSDAnalyticToArithmetic d ∧ BSDArithmeticToAnalytic d

/-- K10 closes only the propositional equivalence between equality and the
    pair of inequalities. It does not prove either arithmetic/analytic direction. -/
theorem k10_rank_equality_iff_two_directions (d : BSDRankData) :
    BSDRankEquality d ↔ BSDRankTwoDirections d := by
  constructor
  · intro h
    exact ⟨k9_equality_implies_analytic_to_arithmetic d h,
      k9_equality_implies_arithmetic_to_analytic d h⟩
  · intro h
    exact k9_two_directions_imply_equality d h.1 h.2

/-- The substantive conjunction remains an open bridge. -/
def k10_two_directions_node : CertNode :=
  { status := .openBridge,
    statement := k9_analytic_to_arithmetic_node.status = .openBridge ∧
      k9_arithmetic_to_analytic_node.status = .openBridge }

theorem k10_two_directions_open :
    k10_two_directions_node.status = .openBridge := rfl

theorem k10_two_directions_not_proved :
    k10_two_directions_node.status ≠ .provedProperty := by decide

theorem k10_two_directions_not_certified :
    ¬ Nonempty (ProofCertificate k10_two_directions_node) := by
  intro h
  rcases h with ⟨c⟩
  exact k10_two_directions_not_proved c.status_proved

end MCore
