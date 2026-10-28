import Mathlib.GroupTheory.Index
import MCore.BSD.MordellWeilDescentReduction

namespace MCore.BSD

/-- Exact weak Mordell--Weil predecessor for the descent reduction:
finiteness of E(Q)/2E(Q) supplies finite index of the doubling image. -/
theorem double_range_finiteIndex_of_finite_quotient
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    [Finite
      (W.toAffine.Point ⧸
        (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range)] :
    (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex := by
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- Forward-only weak Mordell--Weil reduction:
the only remaining arithmetic input is finiteness of E(Q)/2E(Q).
The height/descent layer then gives finite generation of E(Q). -/
theorem moduleFinite_rationalPoints_of_finite_double_quotient
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    [Finite
      (W.toAffine.Point ⧸
        (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range)] :
    Module.Finite ℤ W.toAffine.Point := by
  exact moduleFinite_rationalPoints_of_double_finiteIndex W
    (double_range_finiteIndex_of_finite_quotient W)

#print axioms MCore.BSD.double_range_finiteIndex_of_finite_quotient
#print axioms MCore.BSD.moduleFinite_rationalPoints_of_finite_double_quotient

end MCore.BSD
