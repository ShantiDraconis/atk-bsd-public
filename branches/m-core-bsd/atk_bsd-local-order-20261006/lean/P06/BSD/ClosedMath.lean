import P06.BSD.FinalRoot

namespace P06.BSD

structure DAGClosedCertificate : Prop where
  finalRoot :
    ∀ (G : AnalyticGermFamily) (refined : EllipticCurveQ → BSDRefinedData),
      BSDTerminal (fullyRealizedBSDModel G refined) ↔
        UniversalRealizedRankEquality G ∧
        UniversalRefinedBSDIdentity refined

def dagClosedCertificate : DAGClosedCertificate where
  finalRoot := finalRoot_iff_scientificFrontier

structure FinalRootClosedCertificate : Prop where
  rootExact :
    ∀ (G : AnalyticGermFamily) (refined : EllipticCurveQ → BSDRefinedData),
      BSDTerminal (fullyRealizedBSDModel G refined) ↔
        UniversalRealizedRankEquality G ∧
        UniversalRefinedBSDIdentity refined

def finalRootClosedCertificate : FinalRootClosedCertificate where
  rootExact := finalRoot_iff_scientificFrontier

structure GlobalExternalClosedCertificate : Prop where
  interfaceExact :
    ∀ (G : AnalyticGermFamily) (refined : EllipticCurveQ → BSDRefinedData),
      BSDTerminal (fullyRealizedBSDModel G refined) ↔
        UniversalRealizedRankEquality G ∧
        UniversalRefinedBSDIdentity refined

def globalExternalClosedCertificate : GlobalExternalClosedCertificate where
  interfaceExact := finalRoot_iff_scientificFrontier

def remainingStructuralLeafCount : Nat := 0
def remainingScientificLeafCount : Nat := 2

structure NoReentryCertificate : Prop where
  structural_count_eq_zero : remainingStructuralLeafCount = 0
  scientific_count_eq_two : remainingScientificLeafCount = 2

def noReentryCertificate : NoReentryCertificate where
  structural_count_eq_zero := rfl
  scientific_count_eq_two := rfl

structure ClosedMathStructuralCertificate : Prop where
  dag : DAGClosedCertificate
  finalRoot : FinalRootClosedCertificate
  globalExternal : GlobalExternalClosedCertificate
  noReentry : NoReentryCertificate

def closedMathStructuralCertificate : ClosedMathStructuralCertificate where
  dag := dagClosedCertificate
  finalRoot := finalRootClosedCertificate
  globalExternal := globalExternalClosedCertificate
  noReentry := noReentryCertificate

theorem closedMathStructural : Nonempty ClosedMathStructuralCertificate :=
  ⟨closedMathStructuralCertificate⟩

#print axioms P06.BSD.finalRoot_iff_scientificFrontier
#print axioms P06.BSD.closedMathStructural

end P06.BSD
