import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.RingTheory.Finiteness.Defs

namespace MCore
namespace BSDDoublingDescent

open Height
open WeierstrassCurve.Affine

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]

/-- Strict Mordell-Weil predecessor: once the image of multiplication by 2
has finite index in the rational-point group, the existing Mathlib height
descent machinery yields finite generation of that same point group. -/
theorem moduleFinite_of_doubling_finiteIndex
    (h2 :
      (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex) :
    Module.Finite ℤ W.toAffine.Point := by
  have hnonneg :
      ∀ P : W.toAffine.Point, 0 ≤ P.naiveHeight := by
    intro P
    rw [Point.naiveHeight_eq_logHeight₁]
    exact zero_le_logHeight₁ _
  obtain ⟨C, hpar⟩ := approx_parallelogram_law W.toAffine
  have hfg : AddGroup.FG W.toAffine.Point :=
    AddCommGroup.fg_of_descent' h2 hnonneg hpar
  exact Module.Finite.iff_addGroup_fg.mpr hfg

/-- The exact remaining algebraic input after reusing the height/descent
library is the finite index of doubling, i.e. finiteness of E(Q)/2E(Q). -/
def DoublingFiniteIndexTarget : Prop :=
  (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex

theorem doubling_target_closes_module_finite
    (h : DoublingFiniteIndexTarget W) :
    Module.Finite ℤ W.toAffine.Point :=
  moduleFinite_of_doubling_finiteIndex W h

#print axioms MCore.BSDDoublingDescent.moduleFinite_of_doubling_finiteIndex
#print axioms MCore.BSDDoublingDescent.doubling_target_closes_module_finite

end BSDDoublingDescent
end MCore
