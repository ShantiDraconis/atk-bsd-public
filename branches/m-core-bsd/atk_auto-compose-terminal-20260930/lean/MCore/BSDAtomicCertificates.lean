import MCore.GroundedBSDHabitant

namespace MCore

/-- Atomic obligations extracted from a single grounded BSD state. -/
def BSDRankObligation {Curve Scalar : Type}
    (s : GroundedBSDState Curve Scalar) : Prop :=
  s.analyticOrderAtOne = s.algebraicRank

def BSDShaObligation {Curve Scalar : Type}
    (s : GroundedBSDState Curve Scalar) : Prop :=
  0 < s.shaOrder

def BSDLeadingObligation {Curve Scalar : Type}
    (A : BSDScalarAlgebra Scalar)
    (s : GroundedBSDState Curve Scalar) : Prop :=
  s.leadingCoefficient = bsdArithmeticSide A s

/-- A lightweight height/regulator interface.  It separates the existence and
compatibility of a regulator witness from the refined coefficient identity. -/
structure BSDHeightWitness (Curve Scalar : Type) where
  curve : Curve
  regulator : Scalar
  compatible : Prop
  proof : compatible

structure BSDRankCertificate {Curve Scalar : Type}
    (s : GroundedBSDState Curve Scalar) where
  proof : BSDRankObligation s

structure BSDShaCertificate {Curve Scalar : Type}
    (s : GroundedBSDState Curve Scalar) where
  proof : BSDShaObligation s

structure BSDHeightCertificate {Curve Scalar : Type}
    (s : GroundedBSDState Curve Scalar) where
  witness : BSDHeightWitness Curve Scalar
  sameCurve : witness.curve = s.curve
  sameRegulator : witness.regulator = s.regulator

structure BSDLeadingCertificate {Curve Scalar : Type}
    (A : BSDScalarAlgebra Scalar)
    (s : GroundedBSDState Curve Scalar) where
  proof : BSDLeadingObligation A s

def GroundedBSDHabitant.rankCertificate
    {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar) (E : Curve) :
    BSDRankCertificate (H.state E) :=
  ⟨H.rankLaw E⟩

def GroundedBSDHabitant.shaCertificate
    {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar) (E : Curve) :
    BSDShaCertificate (H.state E) :=
  ⟨H.shaFiniteWitness E⟩

def GroundedBSDHabitant.leadingCertificate
    {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar) (E : Curve) :
    BSDLeadingCertificate H.algebra (H.state E) :=
  ⟨H.leadingLaw E⟩

end MCore
