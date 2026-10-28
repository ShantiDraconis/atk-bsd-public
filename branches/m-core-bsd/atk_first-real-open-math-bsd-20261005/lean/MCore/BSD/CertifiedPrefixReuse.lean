import MCore.BSD.CertificateFamilies

namespace MCore.BSD

/-- Audit object collecting every reusable certified prefix fact without
promoting any open mathematical bridge. -/
structure CertifiedPrefixReuse where
  k1Open : MCore.k1Target.status = .openBridge
  k2Blocked : ¬ Nonempty (MCore.ProofCertificate MCore.k1_node)
  k3Blocked : ¬ Nonempty (MCore.ProofCertificate MCore.k3_gap_node)
  k4Blocked : ¬ Nonempty (MCore.ProofCertificate MCore.k4_open_node)
  k5Blocked : ¬ Nonempty (MCore.ProofCertificate MCore.k4_open_node)
  k6Blocked : ¬ Nonempty (MCore.ProofCertificate MCore.k6_dependency.target)
  k7RankBridgeBlocked :
    ¬ Nonempty (MCore.ProofCertificate (MCore.bsd_obligation_node .rankEqualityBridge))
  k8RankBlocked : ¬ Nonempty (MCore.ProofCertificate MCore.k8_rank_bridge_node)
  k10TwoDirectionsBlocked :
    ¬ Nonempty (MCore.ProofCertificate MCore.k10_two_directions_node)
  k11RankCoreBlocked :
    ¬ Nonempty (MCore.ProofCertificate MCore.k11_rank_core_node)
  k12RankPartBlocked :
    ¬ Nonempty (MCore.ProofCertificate MCore.k12_rank_part_node)
  k13OpenCoreBlocked :
    ¬ Nonempty (MCore.ProofCertificate MCore.k13_open_core_node)
  k14FinalBlocked :
    ¬ Nonempty (MCore.ProofCertificate MCore.k14_final_node)

/-- All K0-K14 fail-closed facts that are mechanically reusable. -/
def certifiedPrefixReuse : CertifiedPrefixReuse where
  k1Open := MCore.k1_status_openBridge
  k2Blocked := MCore.bridge_not_certified
  k3Blocked := MCore.k3_gap_not_certified
  k4Blocked := MCore.k4_no_promotion
  k5Blocked := MCore.k5_openBridge_cannot_certify
  k6Blocked := MCore.k6_target_not_certified
  k7RankBridgeBlocked := MCore.k7_obligation_not_certified .rankEqualityBridge
  k8RankBlocked := MCore.k8_rank_bridge_not_certified
  k10TwoDirectionsBlocked := MCore.k10_two_directions_not_certified
  k11RankCoreBlocked := MCore.k11_rank_core_not_certified
  k12RankPartBlocked := MCore.k12_rank_part_not_certified
  k13OpenCoreBlocked := MCore.k13_open_core_not_certified
  k14FinalBlocked := MCore.k14_final_node_not_certified

/-- Reuse K11 provenance exactly as stated: these inputs are established
externally, not locally reconstructed. -/
theorem modularity_provenance_reused :
    MCore.bsdInputStatus .modularity = .establishedExternal :=
  MCore.k11_modularity_external

theorem analytic_continuation_provenance_reused :
    MCore.bsdInputStatus .analyticContinuation = .establishedExternal :=
  MCore.k11_analytic_continuation_external

theorem functional_equation_provenance_reused :
    MCore.bsdInputStatus .functionalEquation = .establishedExternal :=
  MCore.k11_functional_equation_external

/-- The genuine Q-elliptic-curve source domain is nonempty independently of BSD. -/
theorem genuine_curve_domain_reused : Nonempty EllipticCurveQ :=
  ellipticCurveQ_nonempty

/-- Even after all reusable prefix facts and the genuine source binding are
assembled, the exact scientific min-cut remains rank + refined. -/
theorem reusable_prefix_does_not_change_min_cut
    {D : RealizableEllipticCurveDomain} :
    Nonempty (RealizableBSDProducer D) ↔
      Nonempty (RealizableBSDRankProducer D) ∧
      Nonempty (RealizableBSDRefinedProducer D) :=
  nonempty_producer_iff_rank_and_refined

end MCore.BSD
