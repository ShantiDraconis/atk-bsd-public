import MCore.K10
namespace MCore

/-- Provenance classification for BSD ingredients.  `establishedExternal`
records mathematical input established outside this repository; it is not a
local proof certificate. -/
inductive BSDInputStatus where
  | establishedExternal
  | definitionInterface
  | openBridge
  deriving DecidableEq, Repr

inductive BSDInput where
  | ellipticCurveArithmetic
  | modularity
  | analyticContinuation
  | functionalEquation
  | mordellWeilRank
  | analyticRank
  | rankEquality
  deriving DecidableEq, Repr

def bsdInputStatus : BSDInput → BSDInputStatus
  | .ellipticCurveArithmetic => .definitionInterface
  | .modularity => .establishedExternal
  | .analyticContinuation => .establishedExternal
  | .functionalEquation => .establishedExternal
  | .mordellWeilRank => .definitionInterface
  | .analyticRank => .definitionInterface
  | .rankEquality => .openBridge

theorem k11_modularity_external :
    bsdInputStatus .modularity = .establishedExternal := rfl

theorem k11_analytic_continuation_external :
    bsdInputStatus .analyticContinuation = .establishedExternal := rfl

theorem k11_functional_equation_external :
    bsdInputStatus .functionalEquation = .establishedExternal := rfl

theorem k11_rank_equality_open :
    bsdInputStatus .rankEquality = .openBridge := rfl

/-- External provenance must never be confused with a local provedProperty. -/
def k11_rank_core_node : CertNode :=
  { status := .openBridge,
    statement := bsdInputStatus .rankEquality = .openBridge }

theorem k11_rank_core_open : k11_rank_core_node.status = .openBridge := rfl

theorem k11_rank_core_not_proved :
    k11_rank_core_node.status ≠ .provedProperty := by decide

theorem k11_rank_core_not_certified :
    ¬ Nonempty (ProofCertificate k11_rank_core_node) := by
  intro h
  rcases h with ⟨c⟩
  exact k11_rank_core_not_proved c.status_proved

end MCore
