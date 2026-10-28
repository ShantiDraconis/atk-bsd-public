import MCore.BSDCompositeCertificate

namespace MCore

/-!
Concrete terminal law for the current grounded BSD certificate architecture.
This identifies certification with an actual inhabitant of the universal
certificate type; it does not construct such an inhabitant.
-/

def BSDTerminalCertifies (Curve Scalar : Type) : Prop :=
  Nonempty (BSDUniversalCertificate Curve Scalar)

def BSDTerminalRefutes (Curve Scalar : Type) : Prop :=
  ¬ Nonempty (BSDUniversalCertificate Curve Scalar)

theorem bsd_terminal_cert_refute_disjoint (Curve Scalar : Type) :
    ¬ (BSDTerminalCertifies Curve Scalar ∧
       BSDTerminalRefutes Curve Scalar) := by
  rintro ⟨hcert, href⟩
  exact href hcert

theorem not_bsdTerminalCertifies_iff_refutes
    (Curve Scalar : Type) :
    ¬ BSDTerminalCertifies Curve Scalar ↔
      BSDTerminalRefutes Curve Scalar := by
  rfl

theorem universalCertificate_certifies_terminal
    {Curve Scalar : Type}
    (C : BSDUniversalCertificate Curve Scalar) :
    BSDTerminalCertifies Curve Scalar :=
  ⟨C⟩

theorem terminalCertificate_exposes_rank
    {Curve Scalar : Type}
    (C : BSDUniversalCertificate Curve Scalar)
    (E : Curve) :
    BSDOpenCore (((C.1).state E).toArithmeticAnalyticData) :=
  universalCertificate_closes_old_rank_core C E

end MCore
