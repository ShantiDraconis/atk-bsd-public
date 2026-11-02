import MCore.BSD.ExternalRouteClosure

namespace MCore

/-- Post-frontier project state: the current OPEN_MATH inventory is exhausted,
    but the concrete theorem-producing domain has not yet been constructed. -/
structure BSDPostFrontierState where
  openMathCount : Nat
  frontierClosureEnabled : Bool
  bsdTargetEnabled : Bool

def bsdPostFrontierState : BSDPostFrontierState :=
  { openMathCount := 0
    frontierClosureEnabled := true
    bsdTargetEnabled := false }

theorem bsd_post_frontier_open_math_zero :
    bsdPostFrontierState.openMathCount = 0 := by
  rfl

theorem bsd_post_frontier_closure_enabled :
    bsdPostFrontierState.frontierClosureEnabled = true := by
  rfl

theorem bsd_target_not_enabled_after_frontier_retirement :
    bsdPostFrontierState.bsdTargetEnabled = false := by
  rfl

#print axioms MCore.bsd_post_frontier_open_math_zero
#print axioms MCore.bsd_post_frontier_closure_enabled
#print axioms MCore.bsd_target_not_enabled_after_frontier_retirement

end MCore
