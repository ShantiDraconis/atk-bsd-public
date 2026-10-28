import P06.BSD.ConcreteBSDProducer
import MCore.BSD.ResidualFrontier
import MCore.BSD.RefinedAlgebra

namespace P06.BSD

abbrev CertifiedCurveSubdomain := MCore.BSD.CertifiedCurveSubdomain
abbrev RankOnSubdomain := MCore.BSD.RankOnSubdomain
abbrev RankOnResidual := MCore.BSD.RankOnResidual
abbrev RefinedOnSubdomain := MCore.BSD.RefinedOnSubdomain
abbrev RefinedOnResidual := MCore.BSD.RefinedOnResidual

/-- Exact P1 frontier relative to any already-certified curve subdomain. -/
theorem p1_frontier_exact
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain} :
    BSDP1 M ↔
      Nonempty (RankOnSubdomain M S) ∧
      Nonempty (RankOnResidual M S) :=
  MCore.BSD.p1_iff_subdomain_and_residual

/-- Exact P2 frontier relative to the same certified curve subdomain. -/
theorem p2_frontier_exact
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain} :
    BSDP2 M ↔
      Nonempty (RefinedOnSubdomain M S) ∧
      Nonempty (RefinedOnResidual M S) :=
  MCore.BSD.p2_iff_subdomain_and_residual

/-- Once known and residual P1/P2 are all supplied, terminal closure is mechanical. -/
theorem terminal_from_partition
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (hRK : Nonempty (RankOnSubdomain M S))
    (hRR : Nonempty (RankOnResidual M S))
    (hFK : Nonempty (RefinedOnSubdomain M S))
    (hFR : Nonempty (RefinedOnResidual M S)) :
    BSDTerminal M := by
  have hP1 : BSDP1 M :=
    (p1_frontier_exact (M := M) (S := S)).2 ⟨hRK, hRR⟩
  have hP2 : BSDP2 M :=
    (p2_frontier_exact (M := M) (S := S)).2 ⟨hFK, hFR⟩
  exact terminal_of_p1_p2 hP1 hP2

#print axioms P06.BSD.p1_frontier_exact
#print axioms P06.BSD.p2_frontier_exact
#print axioms P06.BSD.terminal_from_partition

end P06.BSD
