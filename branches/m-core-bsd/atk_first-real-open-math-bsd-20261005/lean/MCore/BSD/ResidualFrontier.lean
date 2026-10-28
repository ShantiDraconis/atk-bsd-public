import MCore.BSD.DomainCover

namespace MCore.BSD

/-- A mathematically certified subdomain of genuine Q-elliptic curves. -/
structure CertifiedCurveSubdomain where
  contains : EllipticCurveQ → Prop

namespace CertifiedCurveSubdomain

variable (S : CertifiedCurveSubdomain)

/-- Exact complement of the certified subdomain. -/
def residual (E : EllipticCurveQ) : Prop := ¬ S.contains E

theorem partition (E : EllipticCurveQ) :
    S.contains E ∨ S.residual E := by
  exact Classical.em (S.contains E)

end CertifiedCurveSubdomain

/-- P1 proved on a certified subdomain. -/
structure RankOnSubdomain
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) where
  proof :
    ∀ E : EllipticCurveQ, S.contains E →
      M.analyticOrderAtOne E = M.mordellWeilRank E

/-- P1 proved on the exact residual complement. -/
structure RankOnResidual
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) where
  proof :
    ∀ E : EllipticCurveQ, S.residual E →
      M.analyticOrderAtOne E = M.mordellWeilRank E

/-- P2 proved on a certified subdomain. -/
structure RefinedOnSubdomain
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) where
  proof :
    ∀ E : EllipticCurveQ, S.contains E →
      RefinedBSDIdentity (M.refinedData E)

/-- P2 proved on the exact residual complement. -/
structure RefinedOnResidual
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) where
  proof :
    ∀ E : EllipticCurveQ, S.residual E →
      RefinedBSDIdentity (M.refinedData E)

/-- Exact P1 assembly from a known subdomain plus its literal complement. -/
def assembleRankFromPartition
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (known : RankOnSubdomain M S)
    (residual : RankOnResidual M S) :
    ConcreteBSDRankProducer M :=
  { rankProof := fun E _ =>
      match S.partition E with
      | Or.inl h => known.proof E h
      | Or.inr h => residual.proof E h }

/-- Exact P2 assembly from the same partition. -/
def assembleRefinedFromPartition
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (known : RefinedOnSubdomain M S)
    (residual : RefinedOnResidual M S) :
    ConcreteBSDRefinedProducer M :=
  { refinedProof := fun E _ =>
      match S.partition E with
      | Or.inl h => known.proof E h
      | Or.inr h => residual.proof E h }

/-- Universal P1 is exactly equivalent to proving P1 on any chosen subdomain
and on its exact complement. -/
theorem p1_iff_subdomain_and_residual
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain} :
    Nonempty (ConcreteBSDRankProducer M) ↔
      Nonempty (RankOnSubdomain M S) ∧
      Nonempty (RankOnResidual M S) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨
      ⟨{ proof := fun E _ => P.rankProof E trivial }⟩,
      ⟨{ proof := fun E _ => P.rankProof E trivial }⟩
    ⟩
  · rintro ⟨⟨known⟩, ⟨residual⟩⟩
    exact ⟨assembleRankFromPartition known residual⟩

/-- Universal P2 is exactly equivalent to proving P2 on any chosen subdomain
and on its exact complement. -/
theorem p2_iff_subdomain_and_residual
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain} :
    Nonempty (ConcreteBSDRefinedProducer M) ↔
      Nonempty (RefinedOnSubdomain M S) ∧
      Nonempty (RefinedOnResidual M S) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨
      ⟨{ proof := fun E _ => P.refinedProof E trivial }⟩,
      ⟨{ proof := fun E _ => P.refinedProof E trivial }⟩
    ⟩
  · rintro ⟨⟨known⟩, ⟨residual⟩⟩
    exact ⟨assembleRefinedFromPartition known residual⟩

end MCore.BSD
