import MCore

open MCore

namespace MCore.StableHoleExtraction

/-- Canonical normalized residual. -/
def BSDStableHole (F : BSDRealizableFamily) : Prop :=
  ∀ E : F.Curve,
    (F.toData E).analyticOrderAtOne = (F.toData E).mordellWeilRank

/-- PASS_A residual normalizes definitionally to the canonical hole. -/
theorem passA_normalizes (F : BSDRealizableFamily) :
    BSDRankPartOnFamily F ↔ BSDStableHole F := by
  rfl

/-- The expanded PASS_B/PASS_C residual is the same canonical hole. -/
theorem expanded_normalizes (F : BSDRealizableFamily) :
    (∀ E : F.Curve,
      (F.toData E).analyticOrderAtOne = (F.toData E).mordellWeilRank) ↔
      BSDStableHole F := by
  rfl

/-- Fence: unrestricted abstract rank-part is already refuted. -/
theorem unrestricted_fence :
    ¬ (∀ d : BSDArithmeticAnalyticData, BSDRankPart d) :=
  unrestricted_not_a_valid_terminal_producer

#print axioms MCore.StableHoleExtraction.passA_normalizes
#print axioms MCore.StableHoleExtraction.expanded_normalizes
#print axioms MCore.StableHoleExtraction.unrestricted_fence

end MCore.StableHoleExtraction
