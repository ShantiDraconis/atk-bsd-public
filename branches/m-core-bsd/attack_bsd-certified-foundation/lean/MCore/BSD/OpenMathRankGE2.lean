import MCore.K13

namespace MCore

/-- The low-analytic-rank domain isolated from the universal BSD rank target. -/
def BSDLowAnalyticRank (d : BSDArithmeticAnalyticData) : Prop :=
  d.analyticOrderAtOne ≤ 1

/-- The exact residual domain after removing analytic ranks 0 and 1. -/
def BSDHighAnalyticRankResidual (d : BSDArithmeticAnalyticData) : Prop :=
  2 ≤ d.analyticOrderAtOne

/-- External mathematics may discharge this contract on the low-rank domain.
    The repository does not manufacture such a theorem. -/
structure BSDLowRankExternalContract where
  witness : ∀ d : BSDArithmeticAnalyticData, BSDLowAnalyticRank d → BSDRankPart d

/-- The remaining independent producer after low-rank discharge. -/
def BSDHighRankProducer : Prop :=
  ∀ d : BSDArithmeticAnalyticData, BSDHighAnalyticRankResidual d → BSDRankPart d

/-- The original universal rank producer. -/
def BSDUniversalRankProducer : Prop :=
  ∀ d : BSDArithmeticAnalyticData, BSDRankPart d

theorem bsd_rank_domain_dichotomy (d : BSDArithmeticAnalyticData) :
    BSDLowAnalyticRank d ∨ BSDHighAnalyticRankResidual d := by
  unfold BSDLowAnalyticRank BSDHighAnalyticRankResidual
  omega

/-- Low-rank closure plus the high-rank residual reconstructs the exact
    universal rank producer. No strengthening or weakening of BSDRankPart occurs. -/
theorem bsd_low_plus_high_closes_universal
    (L : BSDLowRankExternalContract)
    (H : BSDHighRankProducer) :
    BSDUniversalRankProducer := by
  intro d
  rcases bsd_rank_domain_dichotomy d with hlow | hhigh
  · exact L.witness d hlow
  · exact H d hhigh

/-- Any universal proof necessarily contains the high-rank residual producer. -/
theorem bsd_universal_implies_high
    (U : BSDUniversalRankProducer) :
    BSDHighRankProducer := by
  intro d _
  exact U d

/-- Any universal proof also supplies the low-rank contract. -/
theorem bsd_universal_implies_low
    (U : BSDUniversalRankProducer) :
    BSDLowRankExternalContract :=
  { witness := fun d _ => U d }

/-- Exact compression theorem: after a valid low-rank theorem is supplied,
    the universal BSD rank producer is equivalent to the rank >= 2 residual. -/
theorem bsd_universal_iff_high_given_low
    (L : BSDLowRankExternalContract) :
    BSDUniversalRankProducer ↔ BSDHighRankProducer := by
  constructor
  · exact bsd_universal_implies_high
  · intro H
    exact bsd_low_plus_high_closes_universal L H

/-- Fail-closed marker: this file compresses the frontier but does not inhabit
    BSDHighRankProducer. -/
def bsdHighRankProducerClosed : Bool := false

theorem bsd_high_rank_producer_still_open :
    bsdHighRankProducerClosed = false := by
  rfl

#print axioms MCore.bsd_rank_domain_dichotomy
#print axioms MCore.bsd_low_plus_high_closes_universal
#print axioms MCore.bsd_universal_iff_high_given_low
#print axioms MCore.bsd_high_rank_producer_still_open

end MCore
