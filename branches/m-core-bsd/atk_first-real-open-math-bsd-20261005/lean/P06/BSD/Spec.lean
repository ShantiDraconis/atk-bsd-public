import MCore.BSD.TerminalKernel

namespace P06.BSD

abbrev EllipticCurveQ := MCore.BSD.EllipticCurveQ
abbrev ConcreteBSDModel := MCore.BSD.ConcreteBSDModel
abbrev RankEqualityCertificate := MCore.BSD.RankEqualityCertificate
abbrev ConcreteRankCertificateFamily := MCore.BSD.ConcreteRankCertificateFamily
abbrev BSDRefinedData := MCore.BSD.BSDRefinedData
abbrev RefinedBSDIdentity := MCore.BSD.RefinedBSDIdentity
abbrev RefinedBSDInvariantCertificate := MCore.BSD.RefinedBSDInvariantCertificate
abbrev RefinedBSDEqualityCertificate := MCore.BSD.RefinedBSDEqualityCertificate
abbrev RefinedBSDCurveCertificate := MCore.BSD.RefinedBSDCurveCertificate
abbrev ConcreteRefinedCertificateFamily := MCore.BSD.ConcreteRefinedCertificateFamily
abbrev ConcreteBSDRankProducer := MCore.BSD.ConcreteBSDRankProducer
abbrev ConcreteBSDRefinedProducer := MCore.BSD.ConcreteBSDRefinedProducer
abbrev ConcreteBSDProducer := MCore.BSD.ConcreteBSDProducer

/-- P06-P1: exact universal rank inhabitant on the genuine Q-elliptic-curve model. -/
def BSDP1 (M : ConcreteBSDModel) : Prop :=
  Nonempty (ConcreteBSDRankProducer M)

/-- P06-P2: exact universal refined-BSD inhabitant on the same model. -/
def BSDP2 (M : ConcreteBSDModel) : Prop :=
  Nonempty (ConcreteBSDRefinedProducer M)

/-- Terminal P06 inhabitant. -/
def BSDTerminal (M : ConcreteBSDModel) : Prop :=
  Nonempty (ConcreteBSDProducer M)

theorem terminal_iff_p1_and_p2 (M : ConcreteBSDModel) :
    BSDTerminal M ↔ BSDP1 M ∧ BSDP2 M :=
  MCore.BSD.concrete_terminal_kernel_iff_atomic

end P06.BSD
