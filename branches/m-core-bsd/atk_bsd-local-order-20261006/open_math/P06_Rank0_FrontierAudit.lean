import open_math.P06_Rank0_Class

namespace P06.BSD.OpenMath

/-
Rank-0 material frontier audit.

The current ConcreteBSDModel stores analyticOrderAtOne and mordellWeilRank as
independently supplied functions.  Therefore Rank0ArithmeticMaterial is not a
theorem for arbitrary ConcreteBSDModel values: a model can assign analytic
order zero and Mordell-Weil rank one to every genuine curve.

This is not a counterexample to BSD.  It is a counterexample to deriving the
rank-zero theorem from the present abstract model fields alone.
-/

/-- Toy model separating the two rank fields at analytic order zero. -/
def rank0ToyModel : ConcreteBSDModel where
  mordellWeilRank := fun _ => 1
  analyticOrderAtOne := fun _ => 0
  refinedData := fun _ =>
    { leadingCoefficient := 0
      realPeriod := 0
      regulator := 0
      shaOrder := 1
      tamagawaProduct := 1
      torsionOrder := 1 }

/-- Every genuine source curve belongs to the analytic-rank-zero class of the
toy model. -/
theorem rank0_toy_all_in_class (E : EllipticCurveQ) :
    (Rank0Subdomain rank0ToyModel).contains E := by
  rfl

/-- Exact obstruction: the present ConcreteBSDModel interface alone cannot
force Rank0ArithmeticMaterial for arbitrary M. -/
theorem rank0_toy_no_material :
    ¬ Rank0ArithmeticMaterial rank0ToyModel := by
  intro h
  let E := MCore.BSD.positiveControl
  have hRank := h E rfl
  norm_num [rank0ToyModel] at hRank

/-- Hence no theorem universally quantifying over all ConcreteBSDModel values
can inhabit the rank-zero material leaf without an additional hypothesis that
binds M to the genuine arithmetic/analytic invariants of E. -/
theorem no_universal_rank0_material :
    ¬ (∀ M : ConcreteBSDModel, Rank0ArithmeticMaterial M) := by
  intro h
  exact rank0_toy_no_material (h rank0ToyModel)

#check rank0ToyModel
#check rank0_toy_all_in_class
#check rank0_toy_no_material
#check no_universal_rank0_material

end P06.BSD.OpenMath
