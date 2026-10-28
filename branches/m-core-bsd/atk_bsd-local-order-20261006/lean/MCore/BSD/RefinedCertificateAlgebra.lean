import MCore.BSD.RefinedAlgebra
import MCore.BSD.CertificateFamilies

namespace MCore.BSD

/-- Equality certificate from the additive residual form. -/
def RefinedBSDEqualityCertificate.ofDefectZero
    {d : BSDRefinedData}
    (h : refinedDefect d = 0) :
    RefinedBSDEqualityCertificate d :=
  { identity := (refinedIdentity_iff_defect_eq_zero d).2 h }

/-- Equality certificate from the literal LHS = RHS form. -/
def RefinedBSDEqualityCertificate.ofSides
    {d : BSDRefinedData}
    (h : refinedLHS d = refinedRHS d) :
    RefinedBSDEqualityCertificate d :=
  { identity := (refinedIdentity_iff_lhs_eq_rhs d).2 h }

/-- Equality certificate from the quotient normalization. -/
def RefinedBSDEqualityCertificate.ofQuotient
    {d : BSDRefinedData}
    (hTor : 0 < d.torsionOrder)
    (h :
      d.leadingCoefficient =
        refinedRHS d / (d.torsionOrder : ℝ)^2) :
    RefinedBSDEqualityCertificate d :=
  { identity := (refinedIdentity_iff_quotient d hTor).2 h }

/-- Recover the defect-zero presentation from a refined equality certificate. -/
theorem RefinedBSDEqualityCertificate.defect_eq_zero
    {d : BSDRefinedData}
    (C : RefinedBSDEqualityCertificate d) :
    refinedDefect d = 0 :=
  (refinedIdentity_iff_defect_eq_zero d).1 C.identity

/-- Recover the side-equality presentation. -/
theorem RefinedBSDEqualityCertificate.sides_eq
    {d : BSDRefinedData}
    (C : RefinedBSDEqualityCertificate d) :
    refinedLHS d = refinedRHS d :=
  (refinedIdentity_iff_lhs_eq_rhs d).1 C.identity

/-- Recover the quotient form whenever torsion normalization is available. -/
theorem RefinedBSDEqualityCertificate.quotient_eq
    {d : BSDRefinedData}
    (C : RefinedBSDEqualityCertificate d)
    (hTor : 0 < d.torsionOrder) :
    d.leadingCoefficient =
      refinedRHS d / (d.torsionOrder : ℝ)^2 :=
  (refinedIdentity_iff_quotient d hTor).1 C.identity

/-- Build a full curve certificate from invariant normalization plus any
defect-zero proof. -/
def RefinedBSDCurveCertificate.ofDefectZero
    {d : BSDRefinedData}
    (inv : RefinedBSDInvariantCertificate d)
    (h : refinedDefect d = 0) :
    RefinedBSDCurveCertificate d :=
  { invariants := inv
    equality := RefinedBSDEqualityCertificate.ofDefectZero h }

/-- Build a full curve certificate from invariant normalization plus quotient
form. -/
def RefinedBSDCurveCertificate.ofQuotient
    {d : BSDRefinedData}
    (inv : RefinedBSDInvariantCertificate d)
    (h :
      d.leadingCoefficient =
        refinedRHS d / (d.torsionOrder : ℝ)^2) :
    RefinedBSDCurveCertificate d :=
  { invariants := inv
    equality :=
      RefinedBSDEqualityCertificate.ofQuotient inv.torsionPositive h }

/-- A family of defect-zero proofs is sufficient for P2 once normalization
certificates are supplied curvewise. -/
structure ConcreteRefinedDefectFamily (M : ConcreteBSDModel) where
  invariants :
    ∀ E : EllipticCurveQ,
      RefinedBSDInvariantCertificate (M.refinedData E)
  defectZero :
    ∀ E : EllipticCurveQ,
      refinedDefect (M.refinedData E) = 0

def ConcreteRefinedDefectFamily.toCertificateFamily
    {M : ConcreteBSDModel}
    (F : ConcreteRefinedDefectFamily M) :
    ConcreteRefinedCertificateFamily M :=
  { certificate := fun E =>
      RefinedBSDCurveCertificate.ofDefectZero
        (F.invariants E) (F.defectZero E) }

def ConcreteRefinedDefectFamily.toProducer
    {M : ConcreteBSDModel}
    (F : ConcreteRefinedDefectFamily M) :
    ConcreteBSDRefinedProducer M :=
  F.toCertificateFamily.toProducer

theorem refined_defect_family_sufficient
    {M : ConcreteBSDModel}
    (h : Nonempty (ConcreteRefinedDefectFamily M)) :
    Nonempty (ConcreteBSDRefinedProducer M) := by
  rcases h with ⟨F⟩
  exact ⟨F.toProducer⟩

#print axioms MCore.BSD.RefinedBSDEqualityCertificate.ofDefectZero
#print axioms MCore.BSD.RefinedBSDEqualityCertificate.ofSides
#print axioms MCore.BSD.RefinedBSDEqualityCertificate.ofQuotient
#print axioms MCore.BSD.refined_defect_family_sufficient

end MCore.BSD
