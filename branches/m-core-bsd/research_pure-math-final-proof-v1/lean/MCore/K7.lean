import MCore.K6
namespace MCore

/-- BSD-specific obligations are represented as typed audit labels only.
    Their presence records what must be discharged; it is not evidence of discharge. -/
inductive BSDObligation where
  | ellipticCurveArithmetic
  | hasseWeilLFunction
  | analyticContinuation
  | functionalEquation
  | analyticRank
  | mordellWeilRank
  | rankEqualityBridge
  deriving DecidableEq, Repr

def bsd_obligations : List BSDObligation :=
  [ .ellipticCurveArithmetic,
    .hasseWeilLFunction,
    .analyticContinuation,
    .functionalEquation,
    .analyticRank,
    .mordellWeilRank,
    .rankEqualityBridge ]

structure BSDObligationLedger where
  obligation : BSDObligation
  node : CertNode

/-- Every unresolved BSD obligation inherits the fail-closed K6 target. -/
def bsd_obligation_node (_ : BSDObligation) : CertNode := k6_dependency.target

def bsd_ledger : List BSDObligationLedger :=
  bsd_obligations.map fun o => { obligation := o, node := bsd_obligation_node o }

theorem k7_obligation_open (o : BSDObligation) :
    (bsd_obligation_node o).status = .openBridge := k6_target_open

theorem k7_obligation_not_certified (o : BSDObligation) :
    ¬ Nonempty (ProofCertificate (bsd_obligation_node o)) := k6_target_not_certified

theorem k7_target_still_open : k6_dependency.target.status = .openBridge := k6_target_open

theorem k7_target_not_certified :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k6_target_not_certified

end MCore
