import MCore.BSD.ConcreteCarrierGap

namespace MCore

/-- Final post-frontier blocker classification.  The repository contains no
    kernel term witnessing the same-curve rank/leading/height/Sha package. -/
inductive BSDProofTermStatus where
  | missing
  | present
deriving DecidableEq, Repr

def currentBSDProofTermStatus : BSDProofTermStatus :=
  .missing

theorem current_bsd_proof_term_missing :
    currentBSDProofTermStatus = .missing := by
  rfl

def postFrontierHardAtomicRemaining : Nat := 0

theorem post_frontier_hard_atomic_zero :
    postFrontierHardAtomicRemaining = 0 := by
  rfl

def postFrontierGateClosed : Bool := true

theorem post_frontier_gate_closed :
    postFrontierGateClosed = true := by
  rfl

def bsdMathematicalClosure : Bool := false

theorem bsd_mathematical_closure_not_claimed :
    bsdMathematicalClosure = false := by
  rfl

#print axioms MCore.current_bsd_proof_term_missing
#print axioms MCore.post_frontier_hard_atomic_zero
#print axioms MCore.post_frontier_gate_closed
#print axioms MCore.bsd_mathematical_closure_not_claimed

end MCore
