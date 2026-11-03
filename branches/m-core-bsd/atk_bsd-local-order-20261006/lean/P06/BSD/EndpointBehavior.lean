import P06.BSD.FinalRoot

namespace P06.BSD

/-- The exact scientific endpoint below FINAL_ROOT. -/
def ScientificEndpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  UniversalRealizedRankEquality G ∧
    UniversalRefinedBSDIdentity refined

/-- Reopening FINAL_ROOT changes only presentation: it returns the same endpoint. -/
theorem finalRoot_eq_mathematicalEndpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    BSDTerminal (fullyRealizedBSDModel G refined) ↔
      ScientificEndpoint G refined := by
  exact finalRoot_iff_scientificFrontier G refined

/-- The reverse leg of the same cycle. -/
theorem mathematicalEndpoint_eq_finalRoot
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ScientificEndpoint G refined ↔
      BSDTerminal (fullyRealizedBSDModel G refined) := by
  exact (finalRoot_eq_mathematicalEndpoint G refined).symm

/--
Behavioral signature of the truncation frontier:
expanding ROOT to ENDPOINT and folding ENDPOINT back to ROOT is a closed cycle.
No additional structural proposition is produced by another pass.
-/
theorem finalRoot_endpoint_cycle
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    (BSDTerminal (fullyRealizedBSDModel G refined) ↔
        ScientificEndpoint G refined) ∧
    (ScientificEndpoint G refined ↔
        BSDTerminal (fullyRealizedBSDModel G refined)) := by
  exact ⟨finalRoot_eq_mathematicalEndpoint G refined,
    mathematicalEndpoint_eq_finalRoot G refined⟩

/-- Repeating the normalization step is propositionally idempotent. -/
theorem endpoint_normalization_idempotent
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ScientificEndpoint G refined ↔ ScientificEndpoint G refined := by
  rfl

#print axioms P06.BSD.finalRoot_eq_mathematicalEndpoint
#print axioms P06.BSD.finalRoot_endpoint_cycle
#print axioms P06.BSD.endpoint_normalization_idempotent

end P06.BSD
