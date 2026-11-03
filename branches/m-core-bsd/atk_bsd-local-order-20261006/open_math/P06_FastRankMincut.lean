import P06.BSD.AnalyticOrderAtOne
import P06.BSD.RankRealization
import P06.BSD.Spec

namespace P06.BSD.OpenMath

/-- Family of genuine local analytic germs, one for each genuine Q-elliptic curve. -/
abbrev AnalyticGermFamily :=
  ∀ E : EllipticCurveQ, FiniteAnalyticGermAtOne

/--
Concrete BSD model with both rank fields realized:
* algebraic side = finrank of the actual rational-point group;
* analytic side = finite vanishing order of the supplied analytic germ at s = 1.
Only the refined payload remains externally supplied here.
-/
noncomputable def fullyRealizedRankModel
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ConcreteBSDModel where
  mordellWeilRank := MCore.BSD.genuineMordellWeilRank
  analyticOrderAtOne := fun E => analyticRankAtOne (G E)
  refinedData := refined

/-- Single exact rank-part leaf after both sides have been materialized. -/
def UniversalRealizedRankEquality (G : AnalyticGermFamily) : Prop :=
  ∀ E : EllipticCurveQ,
    analyticRankAtOne (G E) = MCore.BSD.genuineMordellWeilRank E

/-- The single leaf produces the concrete BSD rank producer mechanically. -/
noncomputable def rankProducer_of_universalRealizedRankEquality
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    (h : UniversalRealizedRankEquality G) :
    MCore.BSD.ConcreteBSDRankProducer (fullyRealizedRankModel G refined) where
  rankProof := by
    intro E _
    exact h E

/-- Conversely, any rank producer for the fully realized model is exactly that universal equality. -/
theorem universalRealizedRankEquality_of_rankProducer
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    (R : MCore.BSD.ConcreteBSDRankProducer (fullyRealizedRankModel G refined)) :
    UniversalRealizedRankEquality G := by
  intro E
  exact R.rankProof E trivial

theorem rankProducer_iff_universalRealizedRankEquality
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData} :
    Nonempty (MCore.BSD.ConcreteBSDRankProducer (fullyRealizedRankModel G refined)) ↔
      UniversalRealizedRankEquality G := by
  constructor
  · rintro ⟨R⟩
    exact universalRealizedRankEquality_of_rankProducer R
  · intro h
    exact ⟨rankProducer_of_universalRealizedRankEquality h⟩

end P06.BSD.OpenMath
