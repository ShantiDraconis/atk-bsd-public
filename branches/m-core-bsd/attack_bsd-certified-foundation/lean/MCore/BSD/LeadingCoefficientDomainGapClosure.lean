import MCore.BSD.HighRankDomainGapClosure

namespace MCore

/-- The repository currently has no kernel-level carrier tying a leading Taylor
    coefficient to period, regulator, Sha, Tamagawa and torsion data for one
    concrete elliptic curve.  Therefore the existing FRONTIER label is a
    specification boundary, not yet a mathematical proposition. -/
inductive BSDLeadingCoefficientRouteStatus where
  | closedNegativeDomainGap
  | concreteDomainOpen
deriving DecidableEq, Repr

def currentBSDLeadingCoefficientRouteStatus : BSDLeadingCoefficientRouteStatus :=
  .closedNegativeDomainGap

theorem current_leading_coefficient_route_closed_negative :
    currentBSDLeadingCoefficientRouteStatus =
      .closedNegativeDomainGap := by
  rfl

/-- The current abstract/open label is closed as a formulation gap. -/
def abstractLeadingCoefficientOpenMathClosed : Bool := true

theorem abstract_leading_coefficient_open_math_closed :
    abstractLeadingCoefficientOpenMathClosed = true := by
  rfl

/-- A replacement theorem cannot be enabled until a concrete same-curve domain
    is supplied; this boolean is intentionally separate from formulation
    closure. -/
def concreteLeadingCoefficientTheoremEnabled : Bool := false

theorem concrete_leading_coefficient_theorem_not_enabled :
    concreteLeadingCoefficientTheoremEnabled = false := by
  rfl

#print axioms MCore.current_leading_coefficient_route_closed_negative
#print axioms MCore.abstract_leading_coefficient_open_math_closed
#print axioms MCore.concrete_leading_coefficient_theorem_not_enabled

end MCore
