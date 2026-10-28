import MCore.BSD.DomainCover

namespace MCore.BSD

/-- Kernel-facing endpoint for the material BSD package.
This theorem states exactly that the full producer is equivalent to the two
atomic inhabitants already isolated by the forward-only min-cut. -/
theorem terminal_kernel_iff_atomic
    {D : RealizableEllipticCurveDomain} :
    Nonempty (RealizableBSDProducer D) ↔
      Nonempty (RealizableBSDRankProducer D) ∧
      Nonempty (RealizableBSDRefinedProducer D) :=
  nonempty_producer_iff_rank_and_refined

/-- Concrete-Q specialization of the terminal min-cut. -/
theorem concrete_terminal_kernel_iff_atomic
    {M : ConcreteBSDModel} :
    Nonempty (ConcreteBSDProducer M) ↔
      Nonempty (ConcreteBSDRankProducer M) ∧
      Nonempty (ConcreteBSDRefinedProducer M) :=
  nonempty_producer_iff_rank_and_refined

/-- Certificate-family route into the concrete terminal producer. -/
theorem certificate_families_close_kernel
    {M : ConcreteBSDModel}
    (hRank : Nonempty (ConcreteRankCertificateFamily M))
    (hRefined : Nonempty (ConcreteRefinedCertificateFamily M)) :
    Nonempty (ConcreteBSDProducer M) := by
  rcases hRank with ⟨R⟩
  rcases hRefined with ⟨F⟩
  exact ⟨assembleFromCertificateFamilies R F⟩

/-- Exhaustive-cover route into the terminal producer. -/
theorem exhaustive_cover_closes_kernel
    {M : ConcreteBSDModel} {C : CurveDomainCover}
    (hRank : Nonempty (PiecewiseRankProducer M C))
    (hRefined : Nonempty (PiecewiseRefinedProducer M C)) :
    Nonempty (ConcreteBSDProducer M) :=
  exhaustive_cover_sufficient hRank hRefined

#print axioms MCore.BSD.terminal_kernel_iff_atomic
#print axioms MCore.BSD.concrete_terminal_kernel_iff_atomic
#print axioms MCore.BSD.certificate_families_close_kernel
#print axioms MCore.BSD.exhaustive_cover_closes_kernel

end MCore.BSD
