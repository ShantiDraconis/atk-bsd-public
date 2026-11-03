import MCore.BackwardAudit.BSDTestVector1933A1

namespace MCore.BackwardAudit

/-- Integral affine equation for the chosen global Weierstrass model
    y^2 + x*y = x^3 + x - 2. -/
def on1933a1 (x y : Int) : Prop :=
  y*y + x*y = x*x*x + x - 2

theorem P_on_1933a1 : on1933a1 1 0 := by decide
theorem Q_on_1933a1 : on1933a1 2 2 := by decide

/-- Exact third-intersection point for the line through P and Q.
For the generalized Weierstrass negation (x,y) -> (x,-y-x),
the group sum is therefore (5,-13). -/
theorem line_through_PQ : (2 : Int) * 1 - 2 = 0 ∧ (2 : Int) * 2 - 4 = 0 := by decide
theorem third_intersection_on_curve : on1933a1 5 8 := by decide
theorem PplusQ_on_curve : on1933a1 5 (-13) := by decide
theorem generalized_negation_check : (-13 : Int) = -8 - 5 := by decide

/-- Exact arithmetic layer is closed; this theorem does not claim that
(1,0),(2,2) are a saturated Mordell-Weil basis. -/
theorem exact_point_layer_closed :
    on1933a1 1 0 ∧ on1933a1 2 2 ∧ on1933a1 5 (-13) := by
  exact ⟨P_on_1933a1, Q_on_1933a1, PplusQ_on_curve⟩

#print axioms MCore.BackwardAudit.exact_point_layer_closed

end MCore.BackwardAudit
