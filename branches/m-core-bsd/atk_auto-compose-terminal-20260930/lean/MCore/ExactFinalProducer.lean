import MCore.FinalExternal

namespace MCore
namespace BSDFinal

def groundedHabitant_of_fields
    {Curve Scalar : Type}
    (algebra : BSDScalarAlgebra Scalar)
    (state : Curve → GroundedBSDState Curve Scalar)
    (sameCurve : ∀ E, (state E).curve = E)
    (rankLaw : ∀ E, (state E).analyticOrderAtOne = (state E).algebraicRank)
    (shaFiniteWitness : ∀ E, 0 < (state E).shaOrder)
    (leadingLaw : ∀ E,
      (state E).leadingCoefficient = bsdArithmeticSide algebra (state E)) :
    GroundedBSDHabitant Curve Scalar :=
  {
    algebra := algebra
    state := state
    sameCurve := sameCurve
    rankLaw := rankLaw
    shaFiniteWitness := shaFiniteWitness
    leadingLaw := leadingLaw
  }

/-- The current BSDHeightCertificate interface is mechanically inhabited from
    the grounded state: its compatibility proposition can be chosen as True,
    while curve and regulator are definitionally the same carrier values. -/
def heightCertificate_of_grounded
    {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar)
    (E : Curve) :
    BSDHeightCertificate (H.state E) :=
  {
    witness := {
      curve := (H.state E).curve
      regulator := (H.state E).regulator
      compatible := True
      proof := trivial
    }
    sameCurve := rfl
    sameRegulator := rfl
  }

/-- Hence the exact FinalExternal residual of the current formal model is the
    grounded habitant itself; rank, Sha, height and leading certificates are
    constructed field-by-field. -/
def finalExternal_of_grounded
    {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar) :
    FinalExternalCertificate Curve Scalar :=
  ⟨H, fun E =>
    composeBSDCurveCertificate
      (H.rankCertificate E)
      (H.shaCertificate E)
      (heightCertificate_of_grounded H E)
      (H.leadingCertificate E)⟩

#print axioms MCore.BSDFinal.groundedHabitant_of_fields
#print axioms MCore.BSDFinal.heightCertificate_of_grounded
#print axioms MCore.BSDFinal.finalExternal_of_grounded

end BSDFinal
end MCore
