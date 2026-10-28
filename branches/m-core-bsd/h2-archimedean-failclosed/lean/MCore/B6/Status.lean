import MCore.B6.Normalization

namespace MCore.B6

/-- Status record is metadata encoded as an ordinary value, never a proof certificate. -/
structure B6Status where
  b60 : MechanicalStatus
  b61 : MechanicalStatus
  b62 : MechanicalStatus
  b63 : ScientificStatus
  b64 : ScientificStatus
  b65 : ScientificStatus
  b6 : ScientificStatus
  cBSD : ScientificStatus

/-- S1 target state: definitions/normalizations are mechanically closed while B6 remains open. -/
def s1Status : B6Status where
  b60 := .green
  b61 := .green
  b62 := .green
  b63 := .openMath
  b64 := .openMath
  b65 := .conditional
  b6 := .openBridge
  cBSD := .openMath

/-- Negative firewall: the status value cannot silently classify B6 as conditional. -/
theorem b6_remains_open : s1Status.b6 = ScientificStatus.openBridge := rfl

theorem b63_remains_open_math : s1Status.b63 = ScientificStatus.openMath := rfl

theorem b64_remains_open_math : s1Status.b64 = ScientificStatus.openMath := rfl

theorem b65_is_only_conditional : s1Status.b65 = ScientificStatus.conditional := rfl

end MCore.B6
