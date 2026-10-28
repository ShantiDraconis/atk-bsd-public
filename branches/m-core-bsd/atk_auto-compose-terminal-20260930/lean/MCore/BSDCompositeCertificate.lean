import MCore.BSDOperatorSemantics

namespace MCore

/-- Full per-curve certificate bundle.  The height certificate is supplied
separately because the current habitant interface only carries the regulator
value, not a construction of its height pairing. -/
structure BSDCurveCertificate {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar)
    (E : Curve) where
  rank : BSDRankCertificate (H.state E)
  sha : BSDShaCertificate (H.state E)
  height : BSDHeightCertificate (H.state E)
  leading : BSDLeadingCertificate H.algebra (H.state E)

/-- Exact composition law: atomic certificates compose into the curve bundle. -/
def composeBSDCurveCertificate
    {Curve Scalar : Type}
    {H : GroundedBSDHabitant Curve Scalar}
    {E : Curve}
    (rank : BSDRankCertificate (H.state E))
    (sha : BSDShaCertificate (H.state E))
    (height : BSDHeightCertificate (H.state E))
    (leading : BSDLeadingCertificate H.algebra (H.state E)) :
    BSDCurveCertificate H E :=
  ⟨rank, sha, height, leading⟩

/-- Universal endpoint type.  An inhabitant is deliberately not asserted. -/
def BSDUniversalCertificate (Curve Scalar : Type) : Type :=
  Σ H : GroundedBSDHabitant Curve Scalar, ∀ E : Curve, BSDCurveCertificate H E

/-- The universal certificate always exposes the old K13 rank target. -/
theorem universalCertificate_closes_old_rank_core
    {Curve Scalar : Type}
    (C : BSDUniversalCertificate Curve Scalar)
    (E : Curve) :
    BSDOpenCore (((C.1).state E).toArithmeticAnalyticData) :=
  groundedHabitant_closes_rank_interface C.1 E

end MCore
