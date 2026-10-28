import MCore.B6.Decomposition

namespace MCore.B6

/-- B6.0: the rank-two datum records rank = 2 by construction. -/
theorem rankTwo_typed (D : RankTwoData) : D.analyticRank = 2 :=
  D.analyticRankIsTwo

/-- B6.1: expose the factorial-two normalization symbolically, without
    asserting an analytic L-value theorem or requiring field division. -/
theorem analyticLeading_def (D : RankTwoData) :
    analyticLeading D = (D.LDerivTwoAtOne, 2) := rfl

/-- B6.1 normalization packaging. The first component is the symbolic
    numerator/factorial pair; no BSD equality is encoded here. -/
def normalizedAnalyticPackage (D : RankTwoData) : (Int × Nat) × Int × Int :=
  (analyticLeading D, D.period, D.localFactor)

/-- B6.2 normalization packaging. No existence/nondegeneracy theorem is encoded here. -/
def normalizedHeightPackage (D : RankTwoData) : Int × Int :=
  (D.archHeightZ2, D.neronTateRegulator)

/-- The two missing bridges compose mechanically if supplied as hypotheses.
    This is deliberately conditional and does not prove either bridge. -/
theorem bridgeComposition_is_conditional (D : RankTwoData)
    (h3 : DerivativeHeightBridge D)
    (h4 : HeightRegulatorBridge D) :
    D.LDerivTwoAtOne = (2 : Int) * D.neronTateRegulator :=
  conditionalAssembly D h3 h4

end MCore.B6
