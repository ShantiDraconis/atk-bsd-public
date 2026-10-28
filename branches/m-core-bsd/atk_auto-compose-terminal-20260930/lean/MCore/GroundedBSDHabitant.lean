import MCore.K14

namespace MCore

/-- Candidate realization routes for the missing BSD producer.
These are tags only; none is promoted to a theorem by this file. -/
inductive BSDProducerRoute where
  | eulerSystem
  | iwasawaMainConjecture
  | grossZagierKolyvagin
  | selmerDescent
  | derivedHeight
  | hybrid
  deriving DecidableEq, Repr

/-- A same-carrier arithmetic/analytic state for one elliptic curve.
All quantities compared by BSD are bundled together so that no theorem may
silently switch curves, normalizations, periods, regulators, or Sha data. -/
structure GroundedBSDState (Curve Scalar : Type) where
  curve : Curve
  algebraicRank : Nat
  analyticOrderAtOne : Nat
  leadingCoefficient : Scalar
  realPeriod : Scalar
  regulator : Scalar
  tamagawaProduct : Scalar
  shaOrder : Nat
  torsionOrder : Nat
  route : BSDProducerRoute

/-- Algebra carried by the candidate BSD producer.  We keep it explicit
instead of importing field laws implicitly, so the semantic dependencies are
auditable. -/
structure BSDScalarAlgebra (Scalar : Type) where
  zero : Scalar
  one : Scalar
  mul : Scalar → Scalar → Scalar
  div : Scalar → Scalar → Scalar
  natCast : Nat → Scalar
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one : ∀ a, mul a one = a
  one_mul : ∀ a, mul one a = a
  natCast_one : natCast 1 = one

/-- Arithmetic side of the refined BSD expression under one frozen
normalization convention. -/
def bsdArithmeticSide {Scalar : Type}
    (A : BSDScalarAlgebra Scalar)
    {Curve : Type}
    (s : GroundedBSDState Curve Scalar) : Scalar :=
  A.div
    (A.mul
      (A.mul
        (A.mul (A.natCast s.shaOrder) s.realPeriod)
        s.regulator)
      s.tamagawaProduct)
    (A.mul (A.natCast s.torsionOrder) (A.natCast s.torsionOrder))

/-- Semantic law package for the assumed missing object.
An inhabitant would simultaneously discharge the rank bridge and the refined
leading-coefficient bridge on the same elliptic-curve carrier. -/
structure GroundedBSDHabitant (Curve Scalar : Type) where
  algebra : BSDScalarAlgebra Scalar
  state : Curve → GroundedBSDState Curve Scalar

  sameCurve : ∀ E, (state E).curve = E

  /-- Rank BSD. -/
  rankLaw : ∀ E, (state E).analyticOrderAtOne = (state E).algebraicRank

  /-- Finiteness is represented here by a finite positive cardinal supplied
  by the same state.  This is intentionally data carried by the habitant,
  not a theorem manufactured by the scaffold. -/
  shaFiniteWitness : ∀ E, 0 < (state E).shaOrder

  /-- Refined BSD leading coefficient identity, under the state's fixed
  normalization. -/
  leadingLaw : ∀ E,
    (state E).leadingCoefficient =
      bsdArithmeticSide algebra (state E)

/-- Projection from a grounded state to the already frozen rank interface. -/
def GroundedBSDState.toArithmeticAnalyticData
    {Curve Scalar : Type} (s : GroundedBSDState Curve Scalar) :
    BSDArithmeticAnalyticData :=
  { mordellWeilRank := s.algebraicRank,
    analyticOrderAtOne := s.analyticOrderAtOne }

/-- Once a GroundedBSDHabitant is supplied, the old K13 open rank core is
consumed without altering K11--K14 themselves. -/
theorem groundedHabitant_closes_rank_interface
    {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar)
    (E : Curve) :
    BSDOpenCore ((H.state E).toArithmeticAnalyticData) := by
  exact H.rankLaw E

/-- The refined coefficient equality is exposed independently so certification
can freeze rank and refined BSD as distinct gates. -/
theorem groundedHabitant_exposes_leading_identity
    {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar)
    (E : Curve) :
    (H.state E).leadingCoefficient =
      bsdArithmeticSide H.algebra (H.state E) :=
  H.leadingLaw E

/-- The scaffold remains fail-closed: this file defines the exact shape of
the required object, but does not assert Nonempty (GroundedBSDHabitant ...). -/
def groundedBSDHabitantRequired (Curve Scalar : Type) : Prop :=
  Nonempty (GroundedBSDHabitant Curve Scalar)

end MCore
