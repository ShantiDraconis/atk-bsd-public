import open_math.P06_RankField_Independence
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

namespace P06.BSD.OpenMath

/-
Kernel-forced Mordell-Weil realization.

Unlike the previous abstract ConcreteBSDModel field, this file defines the
arithmetic rank directly from the actual additive group of Q-rational points on
the Weierstrass elliptic curve already carried by EllipticCurveQ.

No new rank symbol and no equality hypothesis are introduced.
-/

/-- The actual group of rational points of E in the mathlib affine model. -/
abbrev RationalPointGroup (E : EllipticCurveQ) :=
  E.curve.toAffine.Point

/-- Concrete Nat-valued rank candidate forced from the existing rational-point
group.  The pinned dependency does not provide the later Nat-finrank
torsion-quotient theorem, so no such claim is made here. -/
noncomputable def genuineMordellWeilRank (E : EllipticCurveQ) : Nat :=
  Module.finrank ℤ (RationalPointGroup E)

/-- Construct a ConcreteBSDModel whose Mordell-Weil-rank field is no longer
free: it is definitionally the Z-finrank of the actual rational-point group. -/
noncomputable def mordellWeilRealizedModel
    (analytic : EllipticCurveQ → Nat)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ConcreteBSDModel where
  mordellWeilRank := genuineMordellWeilRank
  analyticOrderAtOne := analytic
  refinedData := refined

@[simp] theorem mordellWeilRealizedModel_rank
    (analytic : EllipticCurveQ → Nat)
    (refined : EllipticCurveQ → BSDRefinedData)
    (E : EllipticCurveQ) :
    (mordellWeilRealizedModel analytic refined).mordellWeilRank E =
      genuineMordellWeilRank E := rfl

@[simp] theorem mordellWeilRealizedModel_analytic
    (analytic : EllipticCurveQ → Nat)
    (refined : EllipticCurveQ → BSDRefinedData)
    (E : EllipticCurveQ) :
    (mordellWeilRealizedModel analytic refined).analyticOrderAtOne E =
      analytic E := rfl

@[simp] theorem mordellWeilRealizedModel_refined
    (analytic : EllipticCurveQ → Nat)
    (refined : EllipticCurveQ → BSDRefinedData)
    (E : EllipticCurveQ) :
    (mordellWeilRealizedModel analytic refined).refinedData E =
      refined E := rfl

/-- Exact rank-zero statement after the kernel has forced genuine arithmetic
rank.  This is now about the actual rational-point group, not a free Nat field. -/
def GenuineRank0Material
    (analytic : EllipticCurveQ → Nat) : Prop :=
  ∀ E : EllipticCurveQ,
    analytic E = 0 →
      genuineMordellWeilRank E = 0

/-- No wiring remains between genuine rank-zero material and the previously
isolated Rank0ArithmeticMaterial: they are definitionally the same statement
for the realized model. -/
theorem genuine_rank0_material_iff
    (analytic : EllipticCurveQ → Nat)
    (refined : EllipticCurveQ → BSDRefinedData) :
    GenuineRank0Material analytic ↔
      Rank0ArithmeticMaterial
        (mordellWeilRealizedModel analytic refined) := by
  rfl

/-- A genuine rank-zero theorem immediately mines the first nonempty-shaped P1
class using the already-frozen union machinery. -/
noncomputable def mineGenuineRank0
    {analytic : EllipticCurveQ → Nat}
    {refined : EllipticCurveQ → BSDRefinedData}
    (h : GenuineRank0Material analytic) :
    RankOnSubdomain
      (mordellWeilRealizedModel analytic refined)
      (Rank0Subdomain (mordellWeilRealizedModel analytic refined)) :=
  rank0Known_of_material ((genuine_rank0_material_iff analytic refined).1 h)

#check RationalPointGroup
#check genuineMordellWeilRank
#check mordellWeilRealizedModel
#check GenuineRank0Material
#check genuine_rank0_material_iff
#check mineGenuineRank0

end P06.BSD.OpenMath
