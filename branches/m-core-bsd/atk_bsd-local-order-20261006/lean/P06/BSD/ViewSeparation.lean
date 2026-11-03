import P06.BSD.TerminalDuality

namespace P06.BSD

/-- Distinct presentation tags for the same terminal mathematical payload. -/
inductive MathView where
  | open
  | closed
  deriving DecidableEq, Repr

theorem openView_ne_closedView :
    MathView.open ≠ MathView.closed := by
  decide

theorem closedView_ne_openView :
    MathView.closed ≠ MathView.open := by
  decide

def MathView.reverse : MathView → MathView
  | .open => .closed
  | .closed => .open

theorem reverse_open :
    MathView.open.reverse = .closed := rfl

theorem reverse_closed :
    MathView.closed.reverse = .open := rfl

theorem reverse_involutive (v : MathView) :
    v.reverse.reverse = v := by
  cases v <;> rfl

/--
The view tag is not the proposition. Both distinct views project to the same
terminal endpoint.
-/
abbrev ViewPayload
    (_ : MathView)
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  Endpoint G refined

theorem open_closed_views_distinct :
    MathView.open ≠ MathView.closed :=
  openView_ne_closedView

theorem open_closed_payload_equivalent
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ViewPayload .open G refined ↔
      ViewPayload .closed G refined := by
  rfl

theorem open_reverse_payload_equivalent
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ViewPayload .open G refined ↔
      ViewPayload MathView.open.reverse G refined := by
  rfl

theorem closed_reverse_payload_equivalent
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ViewPayload .closed G refined ↔
      ViewPayload MathView.closed.reverse G refined := by
  rfl

/--
Representation/content separation:
  OPEN_VIEW != CLOSED_VIEW
while
  payload(OPEN_VIEW) <-> payload(CLOSED_VIEW).
-/
structure ViewSeparationCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop where
  viewsDistinct : MathView.open ≠ MathView.closed
  reverseOpen : MathView.open.reverse = .closed
  reverseClosed : MathView.closed.reverse = .open
  payloadSame :
    ViewPayload .open G refined ↔
      ViewPayload .closed G refined

def viewSeparationCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ViewSeparationCertificate G refined where
  viewsDistinct := openView_ne_closedView
  reverseOpen := reverse_open
  reverseClosed := reverse_closed
  payloadSame := open_closed_payload_equivalent G refined

theorem viewSeparation
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    Nonempty (ViewSeparationCertificate G refined) :=
  ⟨viewSeparationCertificate G refined⟩

#print axioms P06.BSD.openView_ne_closedView
#print axioms P06.BSD.open_closed_payload_equivalent
#print axioms P06.BSD.viewSeparation

end P06.BSD
