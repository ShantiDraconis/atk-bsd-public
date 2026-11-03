import open_math.ForcingKernel

namespace P06.BSD.OpenMath

/-- Computational target for one residual curve: positivity of torsion order
plus the quotient-normalized refined BSD identity. -/
structure ResidualP2QuotientWitness
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain)
    (E : EllipticCurveQ) : Prop where
  residual : S.residual E
  torsionPositive : 0 < (M.refinedData E).torsionOrder
  quotientIdentity :
    (M.refinedData E).leadingCoefficient =
      MCore.BSD.refinedRHS (M.refinedData E) /
        ((M.refinedData E).torsionOrder : ℝ)^2

/-- A quotient witness yields the refined identity for that residual curve. -/
theorem quotientWitness_to_identity
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    {E : EllipticCurveQ}
    (W : ResidualP2QuotientWitness M S E) :
    RefinedBSDIdentity (M.refinedData E) :=
  (MCore.BSD.refinedIdentity_iff_quotient
    (M.refinedData E) W.torsionPositive).2 W.quotientIdentity

/-- Family form: quotient witnesses for every residual curve close P2. -/
def p2_of_quotient_family
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (W :
      ∀ E : EllipticCurveQ, S.residual E →
        ResidualP2QuotientWitness M S E) :
    RefinedOnResidual M S :=
  { proof := fun E hE => quotientWitness_to_identity (W E hE) }

/-- Isolated positivity sub-obligation for the quotient route. -/
def Lemma_Torsion_Nontrivial
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  ∀ E : EllipticCurveQ, S.residual E →
    0 < (M.refinedData E).torsionOrder

/-- Exact material P2 target once a specific intended model and known
subdomain have been selected. -/
abbrev P2MaterialTarget
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  BSD_P2_Producer M S

/-- OPEN_MATH target marker.  A proof must provide the residual refined
identity for the selected genuine model; this definition fabricates nothing. -/
def attempt_P2
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  P2MaterialTarget M S

end P06.BSD.OpenMath
