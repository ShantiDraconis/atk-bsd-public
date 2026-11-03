import P06.BSD.DiagonalClosure
import P06.BSD.SignFlipGuard

namespace P06.BSD

/-- Structural polarity of the terminal presentation. -/
inductive MathPolarity where
  | open
  | closed
  deriving DecidableEq, Repr

/-- The structural minus sign reverses presentation polarity. -/
def MathPolarity.neg : MathPolarity → MathPolarity
  | .open => .closed
  | .closed => .open

theorem polarity_neg_open :
    MathPolarity.neg .open = .closed := rfl

theorem polarity_neg_closed :
    MathPolarity.neg .closed = .open := rfl

theorem polarity_neg_involutive (p : MathPolarity) :
    p.neg.neg = p := by
  cases p <;> rfl

/--
Open and closed are two presentations of the same already-isolated endpoint.
The polarity does not alter mathematical payload.
-/
abbrev PolarityPayload
    (_ : MathPolarity)
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  Endpoint G refined

abbrev OpenMath
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  PolarityPayload .open G refined

abbrev ClosedMath
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  PolarityPayload .closed G refined

abbrev NegOpenMath
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  PolarityPayload (MathPolarity.neg .open) G refined

abbrev NegClosedMath
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  PolarityPayload (MathPolarity.neg .closed) G refined

/-- OPEN_MATH = CLOSED_MATH at the terminal structural payload. -/
theorem openMath_iff_closedMath
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    OpenMath G refined ↔ ClosedMath G refined := by
  rfl

/-- OPEN_MATH = -CLOSED_MATH, where minus is structural polarity reversal. -/
theorem openMath_iff_negClosedMath
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    OpenMath G refined ↔ NegClosedMath G refined := by
  rfl

/-- CLOSED_MATH = -OPEN_MATH, with the same structural meaning of minus. -/
theorem closedMath_iff_negOpenMath
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ClosedMath G refined ↔ NegOpenMath G refined := by
  rfl

/-- The full terminal duality is involutive and payload preserving. -/
structure TerminalDualityCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop where
  negInvolutive : ∀ p : MathPolarity, MathPolarity.neg (MathPolarity.neg p) = p
  openClosed : OpenMath G refined ↔ ClosedMath G refined
  openNegClosed : OpenMath G refined ↔ NegClosedMath G refined
  closedNegOpen : ClosedMath G refined ↔ NegOpenMath G refined

def terminalDualityCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    TerminalDualityCertificate G refined where
  negInvolutive := polarity_neg_involutive
  openClosed := openMath_iff_closedMath G refined
  openNegClosed := openMath_iff_negClosedMath G refined
  closedNegOpen := closedMath_iff_negOpenMath G refined

theorem terminalDuality
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    Nonempty (TerminalDualityCertificate G refined) :=
  ⟨terminalDualityCertificate G refined⟩

/--
Guard against conflating structural minus with logical negation.
The duality above is a representation reversal, not P ↔ ¬P.
-/
theorem structural_minus_is_not_logical_negation
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ¬ (OpenMath G refined ↔ ¬ OpenMath G refined) := by
  exact not_iff_not_self (OpenMath G refined)

#print axioms P06.BSD.terminalDuality
#print axioms P06.BSD.openMath_iff_closedMath
#print axioms P06.BSD.structural_minus_is_not_logical_negation

end P06.BSD
