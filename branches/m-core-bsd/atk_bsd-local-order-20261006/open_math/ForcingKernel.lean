import P06.BSD.PartitionKernel
import MCore.BSD.RefinedAlgebra
import MCore.BSD.SubdomainAlgebra

namespace P06.BSD.OpenMath

abbrev BSD_P1_Producer
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  Nonempty (RankOnResidual M S)

abbrev BSD_P2_Producer
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  Nonempty (RefinedOnResidual M S)

/-- Frozen facts available to the forcing layer.  This contains only
already-certified composition laws; it does not add any BSD inhabitant. -/
structure ForcingInput
    (M : ConcreteBSDModel) (S T : CertifiedCurveSubdomain) : Prop where
  knownRankUnion :
    RankOnSubdomain M S →
    RankOnSubdomain M T →
    RankOnSubdomain M (MCore.BSD.CertifiedCurveSubdomain.union S T)
  knownRefinedUnion :
    RefinedOnSubdomain M S →
    RefinedOnSubdomain M T →
    RefinedOnSubdomain M (MCore.BSD.CertifiedCurveSubdomain.union S T)
  residualRankMono :
    S ⊑ T →
    RankOnResidual M S →
    RankOnResidual M T
  residualRefinedMono :
    S ⊑ T →
    RefinedOnResidual M S →
    RefinedOnResidual M T

def frozenForcingInput
    (M : ConcreteBSDModel) (S T : CertifiedCurveSubdomain) :
    ForcingInput M S T where
  knownRankUnion := fun hS hT => MCore.BSD.RankOnSubdomain.union hS hT
  knownRefinedUnion := fun hS hT => MCore.BSD.RefinedOnSubdomain.union hS hT
  residualRankMono := fun hST hR => MCore.BSD.RankOnResidual.of_le hST hR
  residualRefinedMono := fun hST hR => MCore.BSD.RefinedOnResidual.of_le hST hR

end P06.BSD.OpenMath
