import MCore.BSD.ShortWeierstrassCurveQ

namespace MCore

/-- Exact same-curve data producer contract.  The two numerical invariants are
    functions of the same concrete curve, preventing the old arbitrary-pair
    abstraction from reappearing. -/
structure SameCurveRankMaps where
  mordellWeilRank : ShortWeierstrassCurveQ → Nat
  analyticOrderAtOne : ShortWeierstrassCurveQ → Nat

def SameCurveRankStatement (M : SameCurveRankMaps) : Prop :=
  ∀ E : ShortWeierstrassCurveQ,
    M.analyticOrderAtOne E = M.mordellWeilRank E

def SameCurveRankMaps.toData
    (M : SameCurveRankMaps) (E : ShortWeierstrassCurveQ) : SameCurveRankData :=
  { curve := E
    mordellWeilRank := M.mordellWeilRank E
    analyticOrderAtOne := M.analyticOrderAtOne E }

theorem same_curve_statement_iff_rank_part (M : SameCurveRankMaps) :
    SameCurveRankStatement M ↔
      ∀ E : ShortWeierstrassCurveQ, SameCurveRankPart (M.toData E) := by
  rfl

/-- A witness of this contract is exactly what enables the restricted theorem. -/
structure SameCurveRankCertificate (M : SameCurveRankMaps) where
  proof : SameCurveRankStatement M

theorem same_curve_rank_theorem_of_certificate
    (M : SameCurveRankMaps) (C : SameCurveRankCertificate M) :
    SameCurveRankStatement M :=
  C.proof

/-- No canonical analytic/arithmetic map implementations exist in the repo yet,
    so there is no inhabitant supplied here. -/
def canonicalSameCurveRankMapsAvailable : Bool := false

theorem canonical_same_curve_rank_maps_not_available :
    canonicalSameCurveRankMapsAvailable = false := by
  rfl

def restrictedBSDRankTheoremEnabled : Bool := false

theorem restricted_bsd_rank_theorem_not_enabled :
    restrictedBSDRankTheoremEnabled = false := by
  rfl

#print axioms MCore.same_curve_statement_iff_rank_part
#print axioms MCore.same_curve_rank_theorem_of_certificate
#print axioms MCore.canonical_same_curve_rank_maps_not_available
#print axioms MCore.restricted_bsd_rank_theorem_not_enabled

end MCore
