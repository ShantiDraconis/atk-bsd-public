import MCore.BSD.PostFrontierState

namespace MCore

/-- Kernel-level status of the intended concrete elliptic-curve carrier. -/
inductive BSDConcreteCarrierStatus where
  | missing
  | present
deriving DecidableEq, Repr

/-- Current repository fact: no Lean carrier named EllipticCurveQ (or an equivalent
    concrete same-domain elliptic-curve object) is implemented in the theorem path. -/
def currentBSDConcreteCarrierStatus : BSDConcreteCarrierStatus :=
  .missing

theorem current_bsd_concrete_carrier_missing :
    currentBSDConcreteCarrierStatus = .missing := by
  rfl

/-- The post-frontier theorem target cannot be enabled before a concrete carrier
    and the associated arithmetic/analytic maps exist. -/
def bsdConcreteTheoremEnabled : Bool := false

theorem bsd_concrete_theorem_not_enabled :
    bsdConcreteTheoremEnabled = false := by
  rfl

/-- This closes the present post-frontier blocker classification.  It does not
    close the mathematical theorem itself. -/
def concreteCarrierBlockerClassified : Bool := true

theorem concrete_carrier_blocker_classified :
    concreteCarrierBlockerClassified = true := by
  rfl

#print axioms MCore.current_bsd_concrete_carrier_missing
#print axioms MCore.bsd_concrete_theorem_not_enabled
#print axioms MCore.concrete_carrier_blocker_classified

end MCore
