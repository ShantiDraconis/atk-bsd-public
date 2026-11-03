import MCore.BSD.CertifiedFoundation

namespace MCore

/-- Concrete short Weierstrass presentation
    y^2 = x^3 + A*x + B
    with integer coefficients, viewed over Q.
    The non-singularity condition is 4*A^3 + 27*B^2 != 0.
    This is a concrete carrier for the next ATK lane; no claim is made here
    that it is definitionally identical to every possible repository-level
    notion of EllipticCurveQ. -/
structure ShortWeierstrassCurveQ where
  A : Int
  B : Int
  nonsingular : 4 * A * A * A + 27 * B * B ≠ 0

/-- Forgetful concrete same-curve rank interface.  Both ranks are attached
    to the exact same curve object. -/
structure SameCurveRankData where
  curve : ShortWeierstrassCurveQ
  mordellWeilRank : Nat
  analyticOrderAtOne : Nat

def SameCurveRankData.toBSDArithmeticAnalyticData
    (d : SameCurveRankData) : BSDArithmeticAnalyticData :=
  { mordellWeilRank := d.mordellWeilRank
    analyticOrderAtOne := d.analyticOrderAtOne }

def SameCurveRankPart (d : SameCurveRankData) : Prop :=
  BSDRankPart d.toBSDArithmeticAnalyticData

theorem same_curve_rank_part_iff (d : SameCurveRankData) :
    SameCurveRankPart d ↔ d.analyticOrderAtOne = d.mordellWeilRank := by
  rfl

/-- Concrete carrier now exists for the restricted short-Weierstrass lane. -/
def shortWeierstrassConcreteCarrierEnabled : Bool := true

theorem short_weierstrass_concrete_carrier_enabled :
    shortWeierstrassConcreteCarrierEnabled = true := by
  rfl

/-- This carrier construction alone does not produce the BSD rank equality. -/
def sameCurveRankTheoremEnabled : Bool := false

theorem same_curve_rank_theorem_not_enabled :
    sameCurveRankTheoremEnabled = false := by
  rfl

#print axioms MCore.same_curve_rank_part_iff
#print axioms MCore.short_weierstrass_concrete_carrier_enabled
#print axioms MCore.same_curve_rank_theorem_not_enabled

end MCore
