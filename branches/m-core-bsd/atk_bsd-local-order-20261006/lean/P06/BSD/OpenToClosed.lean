import P06.BSD.ViewSeparation

namespace P06.BSD

/-- Deterministic tendency from the open presentation to the closed presentation. -/
def MathView.tend : MathView → MathView
  | .open => .closed
  | .closed => .closed

theorem open_tends_closed :
    MathView.open.tend = .closed := rfl

theorem closed_stays_closed :
    MathView.closed.tend = .closed := rfl

theorem tend_idempotent (v : MathView) :
    v.tend.tend = v.tend := by
  cases v <;> rfl

/--
The open-to-closed tendency changes only representation.
The terminal endpoint payload is preserved exactly.
-/
theorem tend_preserves_payload
    (v : MathView)
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ViewPayload v G refined ↔
      ViewPayload v.tend G refined := by
  rfl

theorem open_tends_closed_same_endpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ViewPayload .open G refined ↔
      ViewPayload .closed G refined := by
  exact tend_preserves_payload .open G refined

structure OpenToClosedCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop where
  openCloses : MathView.open.tend = .closed
  closedFixed : MathView.closed.tend = .closed
  idempotent : ∀ v : MathView, MathView.tend (MathView.tend v) = MathView.tend v
  payloadPreserved :
    ∀ v : MathView, ViewPayload v G refined ↔ ViewPayload (MathView.tend v) G refined

def openToClosedCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    OpenToClosedCertificate G refined where
  openCloses := open_tends_closed
  closedFixed := closed_stays_closed
  idempotent := tend_idempotent
  payloadPreserved := fun v => tend_preserves_payload v G refined

theorem openToClosed
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    Nonempty (OpenToClosedCertificate G refined) :=
  ⟨openToClosedCertificate G refined⟩

#print axioms P06.BSD.openToClosed
#print axioms P06.BSD.open_tends_closed_same_endpoint
#print axioms P06.BSD.tend_idempotent

end P06.BSD
