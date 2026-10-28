import MCore.BSD.CertificateFamilies

namespace MCore.BSD

theorem producer_min_cut_kernel_statement
    {D : RealizableEllipticCurveDomain} :
    Nonempty (RealizableBSDProducer D) ↔
      Nonempty (RealizableBSDRankProducer D) ∧
      Nonempty (RealizableBSDRefinedProducer D) :=
  nonempty_producer_iff_rank_and_refined

#print axioms MCore.BSD.RealizableBSDProducer.toK8RankEquality
#print axioms MCore.BSD.RealizableBSDProducer.toAnalyticToArithmetic
#print axioms MCore.BSD.RealizableBSDProducer.toArithmeticToAnalytic
#print axioms MCore.BSD.RealizableBSDProducer.toRankTwoDirections
#print axioms MCore.BSD.RealizableBSDProducer.toK13OpenCore
#print axioms MCore.BSD.nonempty_producer_iff_rank_and_refined
#print axioms MCore.BSD.ellipticCurveQ_nonempty
#print axioms MCore.BSD.ConcreteRefinedCertificateFamily.toProducer
#print axioms MCore.BSD.refined_family_sufficient
#print axioms MCore.BSD.ConcreteRankCertificateFamily.toProducer
#print axioms MCore.BSD.assembleFromCertificateFamilies
#print axioms MCore.BSD.producer_min_cut_kernel_statement

end MCore.BSD
