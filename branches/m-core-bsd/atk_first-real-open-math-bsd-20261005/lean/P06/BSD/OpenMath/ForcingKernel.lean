import P06.BSD.Frontier

namespace P06.BSD.OpenMath

def FirstRealOpenMathP1
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  Nonempty (RankOnResidual M S)

def FirstRealOpenMathP2
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  Nonempty (RefinedOnResidual M S)

theorem close_terminal_from_residuals
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (hRankKnown : Nonempty (RankOnSubdomain M S))
    (hRefinedKnown : Nonempty (RefinedOnSubdomain M S))
    (hP1 : FirstRealOpenMathP1 M S)
    (hP2 : FirstRealOpenMathP2 M S) :
    BSDTerminal M :=
  terminal_from_partition hRankKnown hP1 hRefinedKnown hP2

#print axioms P06.BSD.OpenMath.close_terminal_from_residuals

end P06.BSD.OpenMath
