import open_math.P2_TorsionRealization
import open_math.ObstructionKernel

namespace P06.BSD.OpenMath

/-
Refined-field independence audit.

This file changes only ConcreteBSDModel.refinedData while preserving
mordellWeilRank and analyticOrderAtOne exactly.  It proves that the refined
BSD residual identity is an independent material input even after torsion
positivity is made trivial by choosing torsionOrder = 1.
-/

/-- Replace only the refined-data field of a concrete BSD model. -/
def withRefinedData
    (M : ConcreteBSDModel)
    (d : EllipticCurveQ → BSDRefinedData) :
    ConcreteBSDModel where
  mordellWeilRank := M.mordellWeilRank
  analyticOrderAtOne := M.analyticOrderAtOne
  refinedData := d

@[simp] theorem withRefinedData_rank
    (M : ConcreteBSDModel)
    (d : EllipticCurveQ → BSDRefinedData)
    (E : EllipticCurveQ) :
    (withRefinedData M d).mordellWeilRank E =
      M.mordellWeilRank E := rfl

@[simp] theorem withRefinedData_analytic
    (M : ConcreteBSDModel)
    (d : EllipticCurveQ → BSDRefinedData)
    (E : EllipticCurveQ) :
    (withRefinedData M d).analyticOrderAtOne E =
      M.analyticOrderAtOne E := rfl

@[simp] theorem withRefinedData_refined
    (M : ConcreteBSDModel)
    (d : EllipticCurveQ → BSDRefinedData)
    (E : EllipticCurveQ) :
    (withRefinedData M d).refinedData E = d E := rfl

/-- Positive-torsion payload with deliberately nonzero refined defect:
LHS = 0, RHS = 1. -/
def positiveTorsionBadRefinedData : BSDRefinedData where
  leadingCoefficient := 0
  realPeriod := 1
  regulator := 1
  shaOrder := 1
  tamagawaProduct := 1
  torsionOrder := 1

theorem positiveTorsionBadRefinedData_torsion :
    0 < positiveTorsionBadRefinedData.torsionOrder := by
  norm_num [positiveTorsionBadRefinedData]

theorem positiveTorsionBadRefinedData_defect :
    MCore.BSD.refinedDefect positiveTorsionBadRefinedData = -1 := by
  norm_num [positiveTorsionBadRefinedData,
    MCore.BSD.refinedDefect,
    MCore.BSD.refinedLHS,
    MCore.BSD.refinedRHS]

theorem positiveTorsionBadRefinedData_defect_ne_zero :
    MCore.BSD.refinedDefect positiveTorsionBadRefinedData ≠ 0 := by
  rw [positiveTorsionBadRefinedData_defect]
  norm_num

/-- If S has one residual curve, changing only refinedData to the bad positive-
torsion payload destroys P2 while leaving both rank fields unchanged. -/
theorem refined_field_independence_on_nonempty_residual
    (M : ConcreteBSDModel)
    (S : CertifiedCurveSubdomain)
    (hResidual : ∃ E : EllipticCurveQ, S.residual E) :
    ∃ M' : ConcreteBSDModel,
      (∀ E, M'.mordellWeilRank E = M.mordellWeilRank E) ∧
      (∀ E, M'.analyticOrderAtOne E = M.analyticOrderAtOne E) ∧
      (∀ E : EllipticCurveQ, S.residual E →
        0 < (M'.refinedData E).torsionOrder) ∧
      ¬ P2MaterialTarget M' S := by
  let M' :=
    withRefinedData M (fun _ => positiveTorsionBadRefinedData)
  refine ⟨M', ?_, ?_, ?_, ?_⟩
  · intro E
    rfl
  · intro E
    rfl
  · intro E hE
    exact positiveTorsionBadRefinedData_torsion
  · rcases hResidual with ⟨E0, hE0⟩
    apply p2_obstruction_of_residual_defect_ne_zero
      (M := M') (S := S) hE0
    simpa [M', withRefinedData] using
      positiveTorsionBadRefinedData_defect_ne_zero

/-- Stronger min-cut statement: torsion positivity alone cannot imply the
quotient identity or P2, even with all rank data held fixed. -/
theorem torsion_positive_does_not_force_P2 :
    ¬ (∀ M : ConcreteBSDModel, ∀ S : CertifiedCurveSubdomain,
      (∀ E : EllipticCurveQ, S.residual E →
        0 < (M.refinedData E).torsionOrder) →
      P2MaterialTarget M S) := by
  intro h
  let S : CertifiedCurveSubdomain :=
    MCore.BSD.CertifiedCurveSubdomain.empty
  let M : ConcreteBSDModel :=
    withRefinedData p1ToyGoodModel
      (fun _ => positiveTorsionBadRefinedData)
  have hTor :
      ∀ E : EllipticCurveQ, S.residual E →
        0 < (M.refinedData E).torsionOrder := by
    intro E hE
    exact positiveTorsionBadRefinedData_torsion
  have hP2 := h M S hTor
  have hResidual : S.residual MCore.BSD.positiveControl := by
    simp [S, MCore.BSD.CertifiedCurveSubdomain.empty,
      MCore.BSD.CertifiedCurveSubdomain.residual]
  exact
    (p2_obstruction_of_residual_defect_ne_zero
      (M := M) (S := S) hResidual
      (by
        simpa [M, withRefinedData] using
          positiveTorsionBadRefinedData_defect_ne_zero))
      hP2

#check withRefinedData
#check positiveTorsionBadRefinedData_torsion
#check positiveTorsionBadRefinedData_defect_ne_zero
#check refined_field_independence_on_nonempty_residual
#check torsion_positive_does_not_force_P2

end P06.BSD.OpenMath
