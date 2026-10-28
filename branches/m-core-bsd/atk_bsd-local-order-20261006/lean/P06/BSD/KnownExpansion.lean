import P06.BSD.Frontier
import MCore.BSD.SubdomainAlgebra

namespace P06.BSD

abbrev SubdomainLe := MCore.BSD.CertifiedCurveSubdomain.Le

/-- Adding a new certified P1 class enlarges the known region. -/
def extendRankKnown
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hS : RankOnSubdomain M S)
    (hT : RankOnSubdomain M T) :
    RankOnSubdomain M (MCore.BSD.CertifiedCurveSubdomain.union S T) :=
  MCore.BSD.RankOnSubdomain.union hS hT

/-- Adding a new certified P2 class enlarges the known region. -/
def extendRefinedKnown
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hS : RefinedOnSubdomain M S)
    (hT : RefinedOnSubdomain M T) :
    RefinedOnSubdomain M (MCore.BSD.CertifiedCurveSubdomain.union S T) :=
  MCore.BSD.RefinedOnSubdomain.union hS hT

/-- Residual P1 obligations transport automatically when the known set grows. -/
def shrinkRankResidual
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hST : SubdomainLe S T)
    (hResidual : RankOnResidual M S) :
    RankOnResidual M T :=
  MCore.BSD.RankOnResidual.of_le hST hResidual

/-- Residual P2 obligations transport automatically when the known set grows. -/
def shrinkRefinedResidual
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hST : SubdomainLe S T)
    (hResidual : RefinedOnResidual M S) :
    RefinedOnResidual M T :=
  MCore.BSD.RefinedOnResidual.of_le hST hResidual

/-- Incremental P1 closure: known proofs for S and T plus a residual proof
outside S ∪ T suffice for universal P1. -/
theorem p1_from_two_known_classes
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hS : Nonempty (RankOnSubdomain M S))
    (hT : Nonempty (RankOnSubdomain M T))
    (hR : Nonempty
      (RankOnResidual M (MCore.BSD.CertifiedCurveSubdomain.union S T))) :
    BSDP1 M := by
  rcases hS with ⟨pS⟩
  rcases hT with ⟨pT⟩
  have hKnown :
      Nonempty
        (RankOnSubdomain M
          (MCore.BSD.CertifiedCurveSubdomain.union S T)) :=
    ⟨extendRankKnown pS pT⟩
  exact
    (p1_frontier_exact
      (M := M)
      (S := MCore.BSD.CertifiedCurveSubdomain.union S T)).2
      ⟨hKnown, hR⟩

/-- Incremental P2 closure on the union of two certified classes. -/
theorem p2_from_two_known_classes
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hS : Nonempty (RefinedOnSubdomain M S))
    (hT : Nonempty (RefinedOnSubdomain M T))
    (hR : Nonempty
      (RefinedOnResidual M (MCore.BSD.CertifiedCurveSubdomain.union S T))) :
    BSDP2 M := by
  rcases hS with ⟨pS⟩
  rcases hT with ⟨pT⟩
  have hKnown :
      Nonempty
        (RefinedOnSubdomain M
          (MCore.BSD.CertifiedCurveSubdomain.union S T)) :=
    ⟨extendRefinedKnown pS pT⟩
  exact
    (p2_frontier_exact
      (M := M)
      (S := MCore.BSD.CertifiedCurveSubdomain.union S T)).2
      ⟨hKnown, hR⟩

/-- Full terminal closure after two rounds of class mining. Still conditional
on the exact residual inhabitants, and therefore safe for lean/. -/
theorem terminal_from_two_known_classes
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (rS : Nonempty (RankOnSubdomain M S))
    (rT : Nonempty (RankOnSubdomain M T))
    (rR : Nonempty
      (RankOnResidual M (MCore.BSD.CertifiedCurveSubdomain.union S T)))
    (fS : Nonempty (RefinedOnSubdomain M S))
    (fT : Nonempty (RefinedOnSubdomain M T))
    (fR : Nonempty
      (RefinedOnResidual M (MCore.BSD.CertifiedCurveSubdomain.union S T))) :
    BSDTerminal M :=
  terminal_of_p1_p2
    (p1_from_two_known_classes rS rT rR)
    (p2_from_two_known_classes fS fT fR)

#print axioms P06.BSD.p1_from_two_known_classes
#print axioms P06.BSD.p2_from_two_known_classes
#print axioms P06.BSD.terminal_from_two_known_classes

end P06.BSD
