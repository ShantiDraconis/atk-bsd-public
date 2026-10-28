import MCore.BSD.RealizableProducer

namespace MCore.BSD

universe u

/-- Rank half isolated as a producer so it can be solved and kernel-checked
independently of the refined BSD formula. -/
structure RealizableBSDRankProducer (D : RealizableEllipticCurveDomain) where
  rankProof :
    ∀ E : D.Curve, D.Realizable E → D.RankEquality E

/-- Refined leading-coefficient half isolated on exactly the same domain. -/
structure RealizableBSDRefinedProducer (D : RealizableEllipticCurveDomain) where
  refinedProof :
    ∀ E : D.Curve, D.Realizable E → D.RefinedFormula E

namespace RealizableBSDRankProducer

variable {D : RealizableEllipticCurveDomain}

theorem toK12
    (R : RealizableBSDRankProducer D)
    (E : D.Curve) (hE : D.Realizable E) :
    MCore.BSDRankPart (D.toArithmeticAnalyticData E) :=
  R.rankProof E hE

theorem toK8
    (R : RealizableBSDRankProducer D)
    (E : D.Curve) (hE : D.Realizable E) :
    MCore.BSDRankEquality (D.toArithmeticAnalyticData E).toRankData :=
  (MCore.k12_rank_part_iff_k8_target _).1 (R.toK12 E hE)

theorem toK10
    (R : RealizableBSDRankProducer D)
    (E : D.Curve) (hE : D.Realizable E) :
    MCore.BSDRankTwoDirections (D.toArithmeticAnalyticData E).toRankData :=
  (MCore.k10_rank_equality_iff_two_directions _).1 (R.toK8 E hE)

end RealizableBSDRankProducer

/-- Forward-only composition: once the two genuine producers exist on the same
realizable domain, the full material producer is obtained with no further
mathematics. -/
def combine
    {D : RealizableEllipticCurveDomain}
    (rank : RealizableBSDRankProducer D)
    (refined : RealizableBSDRefinedProducer D) :
    RealizableBSDProducer D :=
  { rankProof := rank.rankProof
    refinedProof := refined.refinedProof }

/-- Nonempty-level terminal assembly.  This theorem is purely mechanical and
therefore may be GREEN even while both source inhabitants remain OPEN_MATH. -/
theorem nonempty_combine
    {D : RealizableEllipticCurveDomain}
    (hRank : Nonempty (RealizableBSDRankProducer D))
    (hRefined : Nonempty (RealizableBSDRefinedProducer D)) :
    Nonempty (RealizableBSDProducer D) := by
  rcases hRank with ⟨rank⟩
  rcases hRefined with ⟨refined⟩
  exact ⟨combine rank refined⟩

/-- Exact decomposition of a material producer into the two remaining atomic
producers.  This makes the min-cut explicit and prevents hiding either half. -/
theorem nonempty_producer_iff_rank_and_refined
    {D : RealizableEllipticCurveDomain} :
    Nonempty (RealizableBSDProducer D) ↔
      Nonempty (RealizableBSDRankProducer D) ∧
      Nonempty (RealizableBSDRefinedProducer D) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨⟨{ rankProof := P.rankProof }⟩,
      ⟨{ refinedProof := P.refinedProof }⟩⟩
  · rintro ⟨hRank, hRefined⟩
    exact nonempty_combine hRank hRefined

/-- Administrative min-cut: exactly two scientific producers remain after the
realizable-domain binding is fixed. -/
def remainingAtomicProducerCount : Nat := 2

theorem remainingAtomicProducerCount_eq_two :
    remainingAtomicProducerCount = 2 := by
  rfl

end MCore.BSD
