import MCore.BSD.TerminalAssembly
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Data.Real.Basic

namespace MCore.BSD

/-- Genuine nonsingular Weierstrass elliptic curve over Q. -/
structure EllipticCurveQ where
  curve : WeierstrassCurve ℚ
  elliptic : IsUnit curve.Δ

instance (E : EllipticCurveQ) : E.curve.IsElliptic where
  isUnit := E.elliptic

/-- A concrete nonempty control of the genuine geometric source domain:
y^2 = x^3 - x.  This proves only that the curve domain is nonempty. -/
def positiveControlCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -1
  a₆ := 0

theorem positiveControlCurve_delta :
    positiveControlCurve.Δ = (64 : ℚ) := by
  norm_num [positiveControlCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

def positiveControl : EllipticCurveQ where
  curve := positiveControlCurve
  elliptic := by
    rw [positiveControlCurve_delta]
    norm_num

theorem ellipticCurveQ_nonempty : Nonempty EllipticCurveQ :=
  ⟨positiveControl⟩

/-- Exact arithmetic/analytic invariant payload used to state the refined BSD
identity.  The fields are data only; no BSD equality is stored in the payload. -/
structure BSDRefinedData where
  leadingCoefficient : ℝ
  realPeriod : ℝ
  regulator : ℝ
  shaOrder : Nat
  tamagawaProduct : Nat
  torsionOrder : Nat

/-- Refined BSD identity in cross-multiplied form.
This avoids silently dividing by the torsion order and keeps the normalization
obligation visible. -/
def RefinedBSDIdentity (d : BSDRefinedData) : Prop :=
  d.leadingCoefficient * (d.torsionOrder : ℝ)^2 =
    d.realPeriod * d.regulator *
      (d.shaOrder : ℝ) * (d.tamagawaProduct : ℝ)

/-- A concrete model binds genuine elliptic curves to independently supplied
arithmetic and analytic invariants.  It still contains no rank equality or
refined BSD proof. -/
structure ConcreteBSDModel where
  mordellWeilRank : EllipticCurveQ → Nat
  analyticOrderAtOne : EllipticCurveQ → Nat
  refinedData : EllipticCurveQ → BSDRefinedData

namespace ConcreteBSDModel

def toRealizableDomain (M : ConcreteBSDModel) : RealizableEllipticCurveDomain where
  Curve := EllipticCurveQ
  Realizable := fun _ => True
  mordellWeilRank := M.mordellWeilRank
  analyticOrderAtOne := M.analyticOrderAtOne
  RefinedFormula := fun E => RefinedBSDIdentity (M.refinedData E)

theorem every_curve_realizable (M : ConcreteBSDModel) (E : EllipticCurveQ) :
    (M.toRealizableDomain).Realizable E := by
  trivial

end ConcreteBSDModel

/-- The rank producer on the genuine Q-elliptic-curve domain. -/
abbrev ConcreteBSDRankProducer (M : ConcreteBSDModel) :=
  RealizableBSDRankProducer M.toRealizableDomain

/-- The refined producer on the same genuine domain. -/
abbrev ConcreteBSDRefinedProducer (M : ConcreteBSDModel) :=
  RealizableBSDRefinedProducer M.toRealizableDomain

/-- The full terminal producer on the same genuine domain. -/
abbrev ConcreteBSDProducer (M : ConcreteBSDModel) :=
  RealizableBSDProducer M.toRealizableDomain

end MCore.BSD
