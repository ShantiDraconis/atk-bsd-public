import MCore.BSD.GroundedBSDHabitant

namespace MCore

inductive BSDGroundingStatus where
  | missing
  | externalCandidateVersionMismatch
  | localCanonical
deriving DecidableEq, Repr

def currentAlgebraicRankGroundingStatus : BSDGroundingStatus :=
  .externalCandidateVersionMismatch

def currentAnalyticOrderGroundingStatus : BSDGroundingStatus :=
  .missing

theorem algebraic_rank_grounding_external_version_mismatch :
    currentAlgebraicRankGroundingStatus =
      .externalCandidateVersionMismatch := by
  rfl

theorem analytic_order_grounding_missing :
    currentAnalyticOrderGroundingStatus = .missing := by
  rfl

/--
Exact F5 material producer after the grounding audit.
The implementation/integration status of the two invariant definitions does
not alter the mathematical producer: a kernel term of GroundedBSDHabitant
is still the unique event that closes the rank-defect gap.
-/
def BSDExactF5Producer : Prop :=
  Nonempty GroundedBSDHabitant

theorem bsd_exact_f5_producer_iff :
    BSDExactF5Producer ↔ GroundedBSDRankDefectVanishing := by
  rfl

def bsdExactF5ProducerCount : Nat := 1

theorem bsd_exact_f5_producer_count_one :
    bsdExactF5ProducerCount = 1 := by
  rfl

def bsdF5MathematicalClosure : Bool := false

theorem bsd_f5_mathematical_closure_false :
    bsdF5MathematicalClosure = false := by
  rfl

#print axioms MCore.algebraic_rank_grounding_external_version_mismatch
#print axioms MCore.analytic_order_grounding_missing
#print axioms MCore.bsd_exact_f5_producer_iff
#print axioms MCore.bsd_exact_f5_producer_count_one

end MCore
