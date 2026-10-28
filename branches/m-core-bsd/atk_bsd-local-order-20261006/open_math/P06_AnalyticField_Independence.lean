import open_math.P06_MordellWeil_Realization
import P06.BSD.Spec

namespace P06.BSD.OpenMath

/-
Analytic-field independence audit.

ConcreteBSDModel stores analyticOrderAtOne independently from the genuine
rational-point group and from refinedData.  This file proves that P1 can be
destroyed by changing only analyticOrderAtOne while holding the other two
fields fixed.
-/

/-- Replace only the analytic-order field of a concrete BSD model. -/
def withAnalyticOrder
    (M : ConcreteBSDModel)
    (a : EllipticCurveQ → Nat) :
    ConcreteBSDModel where
  mordellWeilRank := M.mordellWeilRank
  analyticOrderAtOne := a
  refinedData := M.refinedData

@[simp] theorem withAnalyticOrder_rank
    (M : ConcreteBSDModel)
    (a : EllipticCurveQ → Nat)
    (E : EllipticCurveQ) :
    (withAnalyticOrder M a).mordellWeilRank E =
      M.mordellWeilRank E := rfl

@[simp] theorem withAnalyticOrder_refined
    (M : ConcreteBSDModel)
    (a : EllipticCurveQ → Nat)
    (E : EllipticCurveQ) :
    (withAnalyticOrder M a).refinedData E =
      M.refinedData E := rfl

@[simp] theorem withAnalyticOrder_analytic
    (M : ConcreteBSDModel)
    (a : EllipticCurveQ → Nat)
    (E : EllipticCurveQ) :
    (withAnalyticOrder M a).analyticOrderAtOne E = a E := rfl

/-- Shift analytic order by one while preserving the arithmetic-rank and
refined fields exactly. -/
def analyticShiftModel (M : ConcreteBSDModel) : ConcreteBSDModel :=
  withAnalyticOrder M (fun E => M.mordellWeilRank E + 1)

/-- The shifted model cannot satisfy universal P1. -/
theorem analyticShiftModel_not_P1
    (M : ConcreteBSDModel) :
    ¬ P06.BSD.BSDP1 (analyticShiftModel M) := by
  intro hP1
  rcases hP1 with ⟨P⟩
  let E := MCore.BSD.positiveControl
  have hEq :=
    (MCore.BSD.RealizableEllipticCurveDomain.rankEquality_iff
      ((analyticShiftModel M).toRealizableDomain) E).1
      (P.rankProof E trivial)
  change M.mordellWeilRank E + 1 = M.mordellWeilRank E at hEq
  apply Nat.ne_of_gt (Nat.lt_succ_self (M.mordellWeilRank E))
  simpa [Nat.succ_eq_add_one] using hEq

/-- Exact independence statement: rank and refined data do not determine P1
under the current model interface. -/
theorem analytic_field_independence
    (M : ConcreteBSDModel) :
    ∃ M' : ConcreteBSDModel,
      (∀ E, M'.mordellWeilRank E = M.mordellWeilRank E) ∧
      (∀ E, M'.refinedData E = M.refinedData E) ∧
      ¬ P06.BSD.BSDP1 M' := by
  refine ⟨analyticShiftModel M, ?_, ?_, analyticShiftModel_not_P1 M⟩
  · intro E
    rfl
  · intro E
    rfl

#check withAnalyticOrder
#check analyticShiftModel
#check analyticShiftModel_not_P1
#check analytic_field_independence

end P06.BSD.OpenMath
