import MCore.BSD.SameCurveRankTheoremFactory

namespace MCore

/-- Deliberately mismatched maps on the concrete carrier. -/
def mismatchSameCurveRankMaps : SameCurveRankMaps :=
  { mordellWeilRank := fun _ => 0
    analyticOrderAtOne := fun _ => 1 }

/-- A concrete nonsingular short-Weierstrass curve: y^2 = x^3 - x.
    Here 4*(-1)^3 + 27*0^2 = -4 != 0. -/
def witnessCurve : ShortWeierstrassCurveQ :=
  { A := -1
    B := 0
    nonsingular := by decide }

theorem mismatch_same_curve_statement_false :
    ¬ SameCurveRankStatement mismatchSameCurveRankMaps := by
  intro H
  have h := H witnessCurve
  norm_num [mismatchSameCurveRankMaps] at h

/-- Therefore the over-broad unconditional claim for arbitrary rank maps is
    formally false.  Any valid unconditional BSD-rank claim must name concrete
    canonical maps and provide their actual mathematical certificate. -/
theorem arbitrary_maps_unconditional_claim_false :
    ¬ (∀ M : SameCurveRankMaps, SameCurveRankStatement M) := by
  intro H
  exact mismatch_same_curve_statement_false (H mismatchSameCurveRankMaps)

/-- The exact remaining producer type for a fixed concrete map package. -/
def UnconditionalSameCurveRankClaim (M : SameCurveRankMaps) : Prop :=
  Nonempty (SameCurveRankDirectionalCertificate M)

theorem unconditional_claim_closes_rank
    (M : SameCurveRankMaps)
    (H : UnconditionalSameCurveRankClaim M) :
    SameCurveRankStatement M := by
  rcases H with ⟨C⟩
  exact create_same_curve_rank_theorem M C

/-- Current repository does not yet provide canonical same-curve maps, hence
    there is no legitimate unconditional certificate to inhabit here. -/
def unconditionalRankClaimCertificateAvailable : Bool := false

theorem unconditional_rank_claim_certificate_not_available :
    unconditionalRankClaimCertificateAvailable = false := by
  rfl

#print axioms MCore.mismatch_same_curve_statement_false
#print axioms MCore.arbitrary_maps_unconditional_claim_false
#print axioms MCore.unconditional_claim_closes_rank
#print axioms MCore.unconditional_rank_claim_certificate_not_available

end MCore
