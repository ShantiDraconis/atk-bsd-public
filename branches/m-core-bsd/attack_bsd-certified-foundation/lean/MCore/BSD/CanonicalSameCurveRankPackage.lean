import MCore.BSD.UnconditionalRankClaim
import MCore.BackwardAudit.WithoutOracle

namespace MCore

/-- Canonical package required for a legitimate unconditional rank theorem:
    concrete same-curve maps plus their exact directional certificate. -/
structure CanonicalSameCurveRankPackage where
  maps : SameCurveRankMaps
  certificate : SameCurveRankDirectionalCertificate maps

def CanonicalSameCurveRankClaim : Prop :=
  Nonempty CanonicalSameCurveRankPackage

theorem canonical_package_closes_rank
    (H : CanonicalSameCurveRankClaim) :
    ∃ M : SameCurveRankMaps, SameCurveRankStatement M := by
  rcases H with ⟨P⟩
  exact ⟨P.maps, create_same_curve_rank_theorem P.maps P.certificate⟩

/-- The legacy arbitrary-pair witness contract cannot be converted into the
    new canonical same-curve package without an explicit map-construction bridge. -/
def LegacyToCanonicalBridge : Prop :=
  RankPartWitnessContract → CanonicalSameCurveRankClaim

def legacyToCanonicalBridgeAvailable : Bool := false

theorem legacy_to_canonical_bridge_not_available :
    legacyToCanonicalBridgeAvailable = false := by
  rfl

/-- Exact remaining OPEN_MATH producer. -/
def canonicalSameCurveRankPackageAvailable : Bool := false

theorem canonical_same_curve_rank_package_not_available :
    canonicalSameCurveRankPackageAvailable = false := by
  rfl

/-- The final rank theorem switch is enabled only by an actual canonical package. -/
def canonicalRankTheoremEnabled : CanonicalSameCurveRankClaim → Bool :=
  fun _ => true

theorem canonical_rank_theorem_enabled_of_package
    (H : CanonicalSameCurveRankClaim) :
    canonicalRankTheoremEnabled H = true := by
  rfl

#print axioms MCore.canonical_package_closes_rank
#print axioms MCore.legacy_to_canonical_bridge_not_available
#print axioms MCore.canonical_same_curve_rank_package_not_available
#print axioms MCore.canonical_rank_theorem_enabled_of_package

end MCore
