import MCore.BSDUniversalCountermodel
import MCore.BSD.OpenMathRankGE2

namespace MCore

/-- A realizability predicate is kept abstract at this layer: it marks exactly
    the arithmetic/analytic records that come from the intended elliptic-curve
    semantics. This file does not invent a curve model. -/
variable (Realizable : BSDArithmeticAnalyticData → Prop)

def BSDRealizableUniversalRankProducer : Prop :=
  ∀ d : BSDArithmeticAnalyticData, Realizable d → BSDRankPart d

def BSDRealizableLowRankExternalContract : Prop :=
  ∀ d : BSDArithmeticAnalyticData,
    Realizable d →
    BSDLowAnalyticRank d →
    BSDRankPart d

def BSDRealizableHighRankProducer : Prop :=
  ∀ d : BSDArithmeticAnalyticData,
    Realizable d →
    BSDHighAnalyticRankResidual d →
    BSDRankPart d

theorem bsd_realizable_low_plus_high_closes_universal
    (L : BSDRealizableLowRankExternalContract Realizable)
    (H : BSDRealizableHighRankProducer Realizable) :
    BSDRealizableUniversalRankProducer Realizable := by
  intro d hd
  rcases bsd_rank_domain_dichotomy d with hlow | hhigh
  · exact L d hd hlow
  · exact H d hd hhigh

theorem bsd_realizable_universal_implies_high
    (U : BSDRealizableUniversalRankProducer Realizable) :
    BSDRealizableHighRankProducer Realizable := by
  intro d hd _
  exact U d hd

theorem bsd_realizable_universal_iff_high_given_low
    (L : BSDRealizableLowRankExternalContract Realizable) :
    BSDRealizableUniversalRankProducer Realizable ↔
      BSDRealizableHighRankProducer Realizable := by
  constructor
  · exact bsd_realizable_universal_implies_high Realizable
  · intro H
    exact bsd_realizable_low_plus_high_closes_universal Realizable L H

/-- The exact residual OPEN_MATH target after excluding the invalid unrestricted
    producer. This remains deliberately uninhabited here. -/
def bsdRealizableHighRankProducerClosed : Bool := false

theorem bsd_realizable_high_rank_still_open :
    bsdRealizableHighRankProducerClosed = false := by
  rfl

#print axioms MCore.bsd_realizable_low_plus_high_closes_universal
#print axioms MCore.bsd_realizable_universal_iff_high_given_low
#print axioms MCore.bsd_realizable_high_rank_still_open

end MCore
