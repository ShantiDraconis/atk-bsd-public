import MCore.BSDLowRankMaterial
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

namespace MCore.BSDConcreteLowRank

/-- Genuine nonsingular Weierstrass elliptic curve over Q. -/
structure EllipticCurveQ where
  curve : WeierstrassCurve ℚ
  elliptic : IsUnit curve.Δ

instance (E : EllipticCurveQ) : E.curve.IsElliptic where
  isUnit := E.elliptic

/-- Actual group of Q-rational affine points used by the arithmetic side. -/
abbrev RationalPointGroup (E : EllipticCurveQ) :=
  E.curve.toAffine.Point

/-- Arithmetic rank forced by the genuine rational-point group. -/
noncomputable def genuineMordellWeilRank (E : EllipticCurveQ) : Nat :=
  Module.finrank ℤ (RationalPointGroup E)

/--
Concrete analytic input.  The order is independently supplied by the analytic
L-function layer; no rank equality is stored here.
-/
structure AnalyticRankData (E : EllipticCurveQ) where
  analyticOrderAtOne : Nat

/-- K12 datum attached to one genuine elliptic curve. -/
noncomputable def toBSDDatum
    (E : EllipticCurveQ)
    (A : AnalyticRankData E) :
    MCore.BSDArithmeticAnalyticData :=
  { mordellWeilRank := genuineMordellWeilRank E
    analyticOrderAtOne := A.analyticOrderAtOne }

/--
Exact low-rank arithmetic material on a genuine curve.

These implications are the only mathematical inputs still required from the
rank-0/rank-1 BSD theorems.  Equality is not a field.
-/
structure ConcreteLowRankMaterial
    (E : EllipticCurveQ)
    (A : AnalyticRankData E) : Prop where
  rank_zero :
    A.analyticOrderAtOne = 0 →
      genuineMordellWeilRank E = 0
  rank_one :
    A.analyticOrderAtOne = 1 →
      genuineMordellWeilRank E = 1

/-- Concrete material transports definitionally into the audited K12 adapter. -/
noncomputable def ConcreteLowRankMaterial.toCertificate
    {E : EllipticCurveQ}
    {A : AnalyticRankData E}
    (h : ConcreteLowRankMaterial E A) :
    MCore.BSDLowRankMaterialCertificate (toBSDDatum E A) where
  rank_zero := by
    intro h0
    exact h.rank_zero h0
  rank_one := by
    intro h1
    exact h.rank_one h1

/--
Concrete inhabitant for a genuine elliptic curve in analytic rank <= 1.
-/
structure ConcreteLowRankInhabitant
    (E : EllipticCurveQ)
    (A : AnalyticRankData E) : Prop where
  analyticOrder_le_one : A.analyticOrderAtOne ≤ 1
  material : ConcreteLowRankMaterial E A

/--
A concrete low-rank inhabitant reaches the existing K13 BSD open core.
-/
theorem ConcreteLowRankInhabitant.openCore
    {E : EllipticCurveQ}
    {A : AnalyticRankData E}
    (h : ConcreteLowRankInhabitant E A) :
    MCore.BSDOpenCore (toBSDDatum E A) := by
  exact MCore.bsdLowRank_material_to_openCore
    (toBSDDatum E A)
    h.analyticOrder_le_one
    h.material.toCertificate

/--
It also yields the exact K12 rank-part equality on the genuine curve.
-/
theorem ConcreteLowRankInhabitant.rankPart
    {E : EllipticCurveQ}
    {A : AnalyticRankData E}
    (h : ConcreteLowRankInhabitant E A) :
    MCore.BSDRankPart (toBSDDatum E A) := by
  exact MCore.bsdLowRank_material_to_rankPart
    (toBSDDatum E A)
    h.analyticOrder_le_one
    h.material.toCertificate

/--
Expanded theorem: analytic order equals the actual finrank of Q-rational points.
-/
theorem ConcreteLowRankInhabitant.rank_eq_analyticOrder
    {E : EllipticCurveQ}
    {A : AnalyticRankData E}
    (h : ConcreteLowRankInhabitant E A) :
    A.analyticOrderAtOne = genuineMordellWeilRank E := by
  exact h.rankPart

end MCore.BSDConcreteLowRank
