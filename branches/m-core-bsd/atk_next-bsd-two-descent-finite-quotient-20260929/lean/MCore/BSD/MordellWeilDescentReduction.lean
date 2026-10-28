import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.Finiteness.Defs

namespace MCore.BSD

open Height

/-- Forward-only Mordell--Weil reduction available in pinned Mathlib:
if the doubling image has finite index in the rational point group, then
the rational points are finitely generated, hence finite as a Z-module. -/
theorem moduleFinite_rationalPoints_of_double_finiteIndex
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (Hdouble :
      (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex) :
    Module.Finite ℤ W.toAffine.Point := by
  apply Module.Finite.iff_addGroup_fg.mpr
  obtain ⟨C, hC⟩ :=
    WeierstrassCurve.Affine.approx_parallelogram_law W.toAffine
  exact
    AddCommGroup.fg_of_descent'
      (h := fun P : W.toAffine.Point => P.naiveHeight)
      (C := C)
      Hdouble
      (fun P => by
        rw [WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight₁]
        exact Height.zero_le_logHeight₁ _)
      hC

#print axioms MCore.BSD.moduleFinite_rationalPoints_of_double_finiteIndex

end MCore.BSD
