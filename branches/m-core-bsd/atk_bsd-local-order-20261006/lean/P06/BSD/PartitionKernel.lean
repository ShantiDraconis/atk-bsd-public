import P06.BSD.Frontier

namespace P06.BSD

/-- Complete conditional partition certificate for P1 relative to S.
It stores no universal theorem beyond the known+literal-residual split. -/
structure P1PartitionCertificate
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) where
  known : RankOnSubdomain M S
  residual : RankOnResidual M S

/-- Complete conditional partition certificate for P2 relative to S. -/
structure P2PartitionCertificate
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) where
  known : RefinedOnSubdomain M S
  residual : RefinedOnResidual M S

/-- Full conditional BSD partition certificate on one common subdomain S. -/
structure BSDPartitionCertificate
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) where
  p1 : P1PartitionCertificate M S
  p2 : P2PartitionCertificate M S

def P1PartitionCertificate.toP1
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (C : P1PartitionCertificate M S) :
    BSDP1 M :=
  (p1_frontier_exact (M := M) (S := S)).2
    ⟨⟨C.known⟩, ⟨C.residual⟩⟩

def P2PartitionCertificate.toP2
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (C : P2PartitionCertificate M S) :
    BSDP2 M :=
  (p2_frontier_exact (M := M) (S := S)).2
    ⟨⟨C.known⟩, ⟨C.residual⟩⟩

def BSDPartitionCertificate.toTerminal
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (C : BSDPartitionCertificate M S) :
    BSDTerminal M :=
  terminal_of_p1_p2 C.p1.toP1 C.p2.toP2

theorem p1_iff_partition_certificate
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain} :
    BSDP1 M ↔ Nonempty (P1PartitionCertificate M S) := by
  constructor
  · intro h
    have hp :=
      (p1_frontier_exact (M := M) (S := S)).1 h
    rcases hp with ⟨⟨known⟩, ⟨residual⟩⟩
    exact ⟨{ known := known, residual := residual }⟩
  · rintro ⟨C⟩
    exact C.toP1

theorem p2_iff_partition_certificate
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain} :
    BSDP2 M ↔ Nonempty (P2PartitionCertificate M S) := by
  constructor
  · intro h
    have hp :=
      (p2_frontier_exact (M := M) (S := S)).1 h
    rcases hp with ⟨⟨known⟩, ⟨residual⟩⟩
    exact ⟨{ known := known, residual := residual }⟩
  · rintro ⟨C⟩
    exact C.toP2

theorem terminal_iff_partition_certificate
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain} :
    BSDTerminal M ↔ Nonempty (BSDPartitionCertificate M S) := by
  constructor
  · intro hT
    have hp := (terminal_iff_p1_and_p2 M).1 hT
    have h1 :=
      (p1_iff_partition_certificate (M := M) (S := S)).1 hp.1
    have h2 :=
      (p2_iff_partition_certificate (M := M) (S := S)).1 hp.2
    rcases h1 with ⟨C1⟩
    rcases h2 with ⟨C2⟩
    exact ⟨{ p1 := C1, p2 := C2 }⟩
  · rintro ⟨C⟩
    exact C.toTerminal

/-- Flattened four-way conditional terminal criterion. -/
theorem terminal_iff_four_partition_terms
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain} :
    BSDTerminal M ↔
      Nonempty (RankOnSubdomain M S) ∧
      Nonempty (RankOnResidual M S) ∧
      Nonempty (RefinedOnSubdomain M S) ∧
      Nonempty (RefinedOnResidual M S) := by
  constructor
  · intro h
    have hp := (terminal_iff_p1_and_p2 M).1 h
    have h1 := (p1_frontier_exact (M := M) (S := S)).1 hp.1
    have h2 := (p2_frontier_exact (M := M) (S := S)).1 hp.2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  · rintro ⟨hRK, hRR, hFK, hFR⟩
    exact terminal_from_partition hRK hRR hFK hFR

#print axioms P06.BSD.p1_iff_partition_certificate
#print axioms P06.BSD.p2_iff_partition_certificate
#print axioms P06.BSD.terminal_iff_partition_certificate
#print axioms P06.BSD.terminal_iff_four_partition_terms

end P06.BSD
