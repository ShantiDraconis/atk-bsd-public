import MCore.K14

namespace MCore.BSD

universe u

/-- Genuine-domain binding for the BSD terminal lane.
The carrier is intentionally abstract here, but every terminal statement is restricted
by `Realizable`; unlike the rejected unrestricted `BSDArithmeticAnalyticData`
universe, arbitrary pairs of natural numbers are not terminal objects. -/
structure RealizableEllipticCurveDomain where
  Curve : Type u
  Realizable : Curve → Prop
  mordellWeilRank : Curve → Nat
  analyticOrderAtOne : Curve → Nat
  RefinedFormula : Curve → Prop

namespace RealizableEllipticCurveDomain

variable (D : RealizableEllipticCurveDomain)

/-- The existing K12 rank datum attached to one curve in the realizable domain. -/
def toArithmeticAnalyticData (E : D.Curve) : MCore.BSDArithmeticAnalyticData :=
  { mordellWeilRank := D.mordellWeilRank E
    analyticOrderAtOne := D.analyticOrderAtOne E }

/-- Rank equality on one curve, expressed using the already audited K12 target. -/
def RankEquality (E : D.Curve) : Prop :=
  MCore.BSDRankPart (D.toArithmeticAnalyticData E)

theorem rankEquality_iff (E : D.Curve) :
    D.RankEquality E ↔
      D.analyticOrderAtOne E = D.mordellWeilRank E := by
  rfl

end RealizableEllipticCurveDomain

/-- Exact material BSD producer on a realizable elliptic-curve domain.
No new logical postulate, oracle, or proof placeholder is present.
The rejected unrestricted abstract-natural-number quantifier is also absent.  The two fields are the two remaining scientific obligations. -/
structure RealizableBSDProducer (D : RealizableEllipticCurveDomain) where
  rankProof :
    ∀ E : D.Curve, D.Realizable E → D.RankEquality E
  refinedProof :
    ∀ E : D.Curve, D.Realizable E → D.RefinedFormula E

namespace RealizableBSDProducer

variable {D : RealizableEllipticCurveDomain}

/-- Reuse the K8 rank target for every realizable curve. -/
theorem toK8RankEquality
    (P : RealizableBSDProducer D)
    (E : D.Curve) (hE : D.Realizable E) :
    MCore.BSDRankEquality (D.toArithmeticAnalyticData E).toRankData := by
  exact (MCore.k12_rank_part_iff_k8_target (D.toArithmeticAnalyticData E)).1
    (P.rankProof E hE)

/-- Reuse K9 to obtain the analytic-to-arithmetic inequality. -/
theorem toAnalyticToArithmetic
    (P : RealizableBSDProducer D)
    (E : D.Curve) (hE : D.Realizable E) :
    MCore.BSDAnalyticToArithmetic (D.toArithmeticAnalyticData E).toRankData :=
  MCore.k9_equality_implies_analytic_to_arithmetic _
    (P.toK8RankEquality E hE)

/-- Reuse K9 to obtain the arithmetic-to-analytic inequality. -/
theorem toArithmeticToAnalytic
    (P : RealizableBSDProducer D)
    (E : D.Curve) (hE : D.Realizable E) :
    MCore.BSDArithmeticToAnalytic (D.toArithmeticAnalyticData E).toRankData :=
  MCore.k9_equality_implies_arithmetic_to_analytic _
    (P.toK8RankEquality E hE)

/-- Reuse K10: the two directional inequalities are exactly equivalent to rank equality. -/
theorem toRankTwoDirections
    (P : RealizableBSDProducer D)
    (E : D.Curve) (hE : D.Realizable E) :
    MCore.BSDRankTwoDirections (D.toArithmeticAnalyticData E).toRankData :=
  (MCore.k10_rank_equality_iff_two_directions _).1
    (P.toK8RankEquality E hE)

/-- Reuse K13: a material realizable proof can feed the open-core consumer
for the corresponding curve datum. -/
theorem toK13OpenCore
    (P : RealizableBSDProducer D)
    (E : D.Curve) (hE : D.Realizable E) :
    MCore.BSDOpenCore (D.toArithmeticAnalyticData E) :=
  MCore.k13_consume_open_core _ (P.rankProof E hE)

/-- Projection of the refined full-BSD obligation. -/
theorem refined
    (P : RealizableBSDProducer D)
    (E : D.Curve) (hE : D.Realizable E) :
    D.RefinedFormula E :=
  P.refinedProof E hE

end RealizableBSDProducer

end MCore.BSD
