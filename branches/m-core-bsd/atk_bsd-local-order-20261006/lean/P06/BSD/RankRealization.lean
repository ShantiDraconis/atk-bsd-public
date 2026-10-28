import MCore.BSD.ConcreteDomain
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

namespace MCore.BSD

abbrev RationalPointGroup (E : EllipticCurveQ) :=
  E.curve.toAffine.Point

noncomputable def genuineMordellWeilRank (E : EllipticCurveQ) : Nat :=
  Module.finrank ℤ (RationalPointGroup E)

end MCore.BSD
