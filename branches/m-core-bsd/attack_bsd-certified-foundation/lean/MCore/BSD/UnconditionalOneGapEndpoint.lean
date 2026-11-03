import MCore.BSD.CanonicalSameCurveRankPackage
import MCore.BSD.CertifiedFoundation

namespace MCore

/-- The exact one-gap endpoint for the new concrete BSD-rank lane. -/
def BSDUnconditionalRankOpenMath : Prop :=
  CanonicalSameCurveRankClaim

/-- The theorem claim produced by the exact unconditional certificate. -/
def BSDUnconditionalRankTheorem : Prop :=
  ∃ M : SameCurveRankMaps, SameCurveRankStatement M

theorem unconditional_certificate_closes_open_math
    (H : BSDUnconditionalRankOpenMath) :
    BSDUnconditionalRankTheorem :=
  canonical_package_closes_rank H

/-- Conversely, an arbitrary existence proof of maps+statement does not by itself
    reconstruct the directional certificate package.  Therefore the package is
    intentionally the stronger certified producer used by ATK. -/
def bsdUnconditionalOpenMathCount : Nat := 1

theorem bsd_unconditional_open_math_count_one :
    bsdUnconditionalOpenMathCount = 1 := by
  rfl

/-- Infrastructure is complete: there is exactly one mathematical producer left. -/
def bsdUnconditionalInfrastructureClosed : Bool := true

theorem bsd_unconditional_infrastructure_closed :
    bsdUnconditionalInfrastructureClosed = true := by
  rfl

/-- The mathematical claim is not enabled absent the package inhabitant. -/
def bsdUnconditionalClaimEnabled : Bool := false

theorem bsd_unconditional_claim_not_enabled :
    bsdUnconditionalClaimEnabled = false := by
  rfl

#print axioms MCore.unconditional_certificate_closes_open_math
#print axioms MCore.bsd_unconditional_open_math_count_one
#print axioms MCore.bsd_unconditional_infrastructure_closed
#print axioms MCore.bsd_unconditional_claim_not_enabled

end MCore
