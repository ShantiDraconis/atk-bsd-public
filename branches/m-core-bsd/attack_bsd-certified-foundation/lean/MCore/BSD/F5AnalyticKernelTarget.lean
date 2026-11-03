import MCore.BSD.GroundedBSDHabitant

namespace MCore

/-- Kernel target for the analytic side of F5 on the current carrier. -/
structure BSDAnalyticOrderKernelPackage : Type where
  semantics : BSDRankSemanticAnchor
  specification : BSDRankGroundingSpecification
  analyticGrounded :
    ∀ E : ShortWeierstrassCurveQ,
      specification.analyticOrderSpec E (semantics.analyticOrderAtOne E)

def BSDAnalyticOrderKernelTarget : Prop :=
  Nonempty BSDAnalyticOrderKernelPackage

def bsdAnalyticOrderKernelAvailable : Bool := false

theorem bsd_analytic_order_kernel_not_available :
    bsdAnalyticOrderKernelAvailable = false := by
  rfl

#print axioms MCore.bsd_analytic_order_kernel_not_available

end MCore
