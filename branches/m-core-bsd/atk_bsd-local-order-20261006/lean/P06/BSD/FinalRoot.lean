import P06.BSD.Spec

namespace P06.BSD

/-- Family of finite analytic germs at s = 1, one for each genuine Q-elliptic curve. -/
abbrev AnalyticGermFamily :=
  ∀ E : EllipticCurveQ, FiniteAnalyticGermAtOne

/-- Concrete model with both rank fields materially realized. -/
noncomputable def fullyRealizedBSDModel
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ConcreteBSDModel where
  mordellWeilRank := MCore.BSD.genuineMordellWeilRank
  analyticOrderAtOne := fun E => analyticRankAtOne (G E)
  refinedData := refined

/-- Final scientific rank leaf. -/
def UniversalRealizedRankEquality (G : AnalyticGermFamily) : Prop :=
  ∀ E : EllipticCurveQ,
    analyticRankAtOne (G E) = MCore.BSD.genuineMordellWeilRank E

/-- Final scientific refined-BSD leaf. -/
def UniversalRefinedBSDIdentity
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  ∀ E : EllipticCurveQ, RefinedBSDIdentity (refined E)

/-- The rank leaf is exactly the rank producer for the fully realized model. -/
theorem p1_iff_universalRealizedRankEquality
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    BSDP1 (fullyRealizedBSDModel G refined) ↔
      UniversalRealizedRankEquality G := by
  constructor
  · rintro ⟨R⟩ E
    exact R.rankProof E trivial
  · intro h
    exact ⟨{
      rankProof := by
        intro E _
        exact h E
    }⟩

/-- The refined leaf is exactly the refined producer for the same model. -/
theorem p2_iff_universalRefinedBSDIdentity
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    BSDP2 (fullyRealizedBSDModel G refined) ↔
      UniversalRefinedBSDIdentity refined := by
  constructor
  · rintro ⟨R⟩ E
    exact R.refinedProof E trivial
  · intro h
    exact ⟨{
      refinedProof := by
        intro E _
        exact h E
    }⟩

/--
FINAL_ROOT: the full material BSD terminal is equivalent to exactly two
scientific leaves. No residual partition, subdomain, oracle, scaffold, or
open-math wrapper remains below this theorem.
-/
theorem finalRoot_iff_scientificFrontier
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    BSDTerminal (fullyRealizedBSDModel G refined) ↔
      UniversalRealizedRankEquality G ∧
      UniversalRefinedBSDIdentity refined := by
  rw [terminal_iff_p1_and_p2,
      p1_iff_universalRealizedRankEquality,
      p2_iff_universalRefinedBSDIdentity]

#print axioms P06.BSD.p1_iff_universalRealizedRankEquality
#print axioms P06.BSD.p2_iff_universalRefinedBSDIdentity
#print axioms P06.BSD.finalRoot_iff_scientificFrontier

end P06.BSD
