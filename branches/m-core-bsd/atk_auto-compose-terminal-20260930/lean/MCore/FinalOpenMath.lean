import MCore.ExactFinalProducer

namespace MCore.BSDFinal

/-- Exact BSD residual of the present carrier.  The independent height
certificate is already constructible from the current interface, so the full
residual is precisely the grounded habitant. -/
def OpenMathResidual (Curve Scalar : Type) : Prop :=
  Nonempty (GroundedBSDHabitant Curve Scalar)

theorem residual_closes_final
    {Curve Scalar : Type}
    (h : OpenMathResidual Curve Scalar) :
    Nonempty (FinalExternalCertificate Curve Scalar) := by
  rcases h with ⟨H⟩
  exact ⟨finalExternal_of_grounded H⟩

end MCore.BSDFinal
