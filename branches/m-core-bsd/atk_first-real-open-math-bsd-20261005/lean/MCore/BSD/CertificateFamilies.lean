import MCore.BSD.ConcreteDomain

namespace MCore.BSD

/-- Atomic decomposition of the refined identity into independently auditable
normalization/data obligations plus the one substantive equality. -/
structure RefinedBSDInvariantCertificate (d : BSDRefinedData) where
  torsionPositive : 0 < d.torsionOrder
  shaFiniteOrder : 0 < d.shaOrder
  tamagawaPositive : 0 < d.tamagawaProduct
  realPeriodPositive : 0 < d.realPeriod
  regulatorNonnegative : 0 ≤ d.regulator

/-- The exact refined equality certificate.  It contains no rank information. -/
structure RefinedBSDEqualityCertificate (d : BSDRefinedData) where
  identity : RefinedBSDIdentity d

/-- Full refined certificate for one curve.  Normalization side conditions are
kept distinct from the actual BSD leading-coefficient equality. -/
structure RefinedBSDCurveCertificate (d : BSDRefinedData) where
  invariants : RefinedBSDInvariantCertificate d
  equality : RefinedBSDEqualityCertificate d

namespace RefinedBSDCurveCertificate

theorem toIdentity {d : BSDRefinedData}
    (C : RefinedBSDCurveCertificate d) :
    RefinedBSDIdentity d :=
  C.equality.identity

end RefinedBSDCurveCertificate

/-- A curvewise family of independently normalized refined-BSD certificates. -/
structure ConcreteRefinedCertificateFamily (M : ConcreteBSDModel) where
  certificate :
    ∀ E : EllipticCurveQ, RefinedBSDCurveCertificate (M.refinedData E)

/-- Mechanical promotion from a genuine curvewise refined certificate family to
the exact terminal refined producer. -/
def ConcreteRefinedCertificateFamily.toProducer
    {M : ConcreteBSDModel}
    (F : ConcreteRefinedCertificateFamily M) :
    ConcreteBSDRefinedProducer M :=
  { refinedProof := fun E _ => (F.certificate E).toIdentity }

/-- Exact equivalence at Nonempty level: once the domain/model is fixed,
providing a curvewise refined certificate family is sufficient for the refined
terminal producer.  The reverse direction recovers only the equality component;
normalization certificates are deliberately not fabricated. -/
theorem refined_family_sufficient
    {M : ConcreteBSDModel}
    (h : Nonempty (ConcreteRefinedCertificateFamily M)) :
    Nonempty (ConcreteBSDRefinedProducer M) := by
  rcases h with ⟨F⟩
  exact ⟨F.toProducer⟩

/-- Rank certificate for one genuine elliptic curve. -/
structure RankEqualityCertificate (M : ConcreteBSDModel) (E : EllipticCurveQ) where
  equality :
    M.analyticOrderAtOne E = M.mordellWeilRank E

/-- Curvewise family of rank-equality certificates. -/
structure ConcreteRankCertificateFamily (M : ConcreteBSDModel) where
  certificate :
    ∀ E : EllipticCurveQ, RankEqualityCertificate M E

/-- Mechanical promotion of curvewise rank equalities into the exact rank
producer used by the terminal min-cut. -/
def ConcreteRankCertificateFamily.toProducer
    {M : ConcreteBSDModel}
    (F : ConcreteRankCertificateFamily M) :
    ConcreteBSDRankProducer M :=
  { rankProof := fun E _ => (F.certificate E).equality }

/-- Once rank and refined certificate families exist for the same concrete model,
the full BSD terminal producer is mechanical. -/
def assembleFromCertificateFamilies
    {M : ConcreteBSDModel}
    (R : ConcreteRankCertificateFamily M)
    (F : ConcreteRefinedCertificateFamily M) :
    ConcreteBSDProducer M :=
  combine R.toProducer F.toProducer

end MCore.BSD
