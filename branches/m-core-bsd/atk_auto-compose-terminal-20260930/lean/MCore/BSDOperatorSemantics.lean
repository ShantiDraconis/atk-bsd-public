import MCore.BSDAtomicCertificates

namespace MCore

/-- Observable decomposition of the assumed BSD producer. -/
structure BSDAnalyticView (Scalar : Type) where
  orderAtOne : Nat
  leadingCoefficient : Scalar

structure BSDArithmeticView (Scalar : Type) where
  rank : Nat
  realPeriod : Scalar
  regulator : Scalar
  tamagawaProduct : Scalar
  shaOrder : Nat
  torsionOrder : Nat

def analyticOperator {Curve Scalar : Type}
    (s : GroundedBSDState Curve Scalar) : BSDAnalyticView Scalar :=
  ⟨s.analyticOrderAtOne, s.leadingCoefficient⟩

def arithmeticOperator {Curve Scalar : Type}
    (s : GroundedBSDState Curve Scalar) : BSDArithmeticView Scalar :=
  ⟨s.algebraicRank, s.realPeriod, s.regulator, s.tamagawaProduct,
    s.shaOrder, s.torsionOrder⟩

/-- Same-carrier semantic compatibility. -/
structure BSDGlueSemantics (Curve Scalar : Type) where
  analytic : Curve → BSDAnalyticView Scalar
  arithmetic : Curve → BSDArithmeticView Scalar
  rankCompatible : ∀ E, (analytic E).orderAtOne = (arithmetic E).rank

def GroundedBSDHabitant.toGlueSemantics
    {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar) : BSDGlueSemantics Curve Scalar :=
  { analytic := fun E => analyticOperator (H.state E)
    arithmetic := fun E => arithmeticOperator (H.state E)
    rankCompatible := H.rankLaw }

/-- The rank defect vanishes under a grounded habitant, expressed without
integer subtraction to keep the invariant exact over Nat. -/
theorem grounded_rank_views_equal
    {Curve Scalar : Type}
    (H : GroundedBSDHabitant Curve Scalar) (E : Curve) :
    (analyticOperator (H.state E)).orderAtOne =
      (arithmeticOperator (H.state E)).rank :=
  H.rankLaw E

end MCore
