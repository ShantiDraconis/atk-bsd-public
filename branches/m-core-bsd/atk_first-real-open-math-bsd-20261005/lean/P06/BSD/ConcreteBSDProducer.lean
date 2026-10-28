import P06.BSD.Spec
import MCore.BSD.DomainCover

namespace P06.BSD

/-- Mechanical assembly from the two genuine P06 inhabitants. -/
def assemble
    {M : ConcreteBSDModel}
    (rank : ConcreteBSDRankProducer M)
    (refined : ConcreteBSDRefinedProducer M) :
    ConcreteBSDProducer M :=
  MCore.BSD.combine rank refined

theorem terminal_of_p1_p2
    {M : ConcreteBSDModel}
    (hP1 : BSDP1 M)
    (hP2 : BSDP2 M) :
    BSDTerminal M := by
  rcases hP1 with ⟨rank⟩
  rcases hP2 with ⟨refined⟩
  exact ⟨assemble rank refined⟩

theorem p1_of_rank_family
    {M : ConcreteBSDModel}
    (h : Nonempty (ConcreteRankCertificateFamily M)) :
    BSDP1 M := by
  rcases h with ⟨F⟩
  exact ⟨MCore.BSD.ConcreteRankCertificateFamily.toProducer F⟩

theorem p2_of_refined_family
    {M : ConcreteBSDModel}
    (h : Nonempty (ConcreteRefinedCertificateFamily M)) :
    BSDP2 M :=
  MCore.BSD.refined_family_sufficient h

theorem terminal_of_certificate_families
    {M : ConcreteBSDModel}
    (hRank : Nonempty (ConcreteRankCertificateFamily M))
    (hRefined : Nonempty (ConcreteRefinedCertificateFamily M)) :
    BSDTerminal M :=
  MCore.BSD.certificate_families_close_kernel hRank hRefined

end P06.BSD
