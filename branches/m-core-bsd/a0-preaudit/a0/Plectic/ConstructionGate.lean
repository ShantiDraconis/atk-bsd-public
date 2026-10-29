/-
  Plectic/ConstructionGate.lean

  Formal decomposition of the first genuine mathematical frontier in the
  plectic BSD research route.  This file does not assert any open proposition.
  A subgate is promoted only by supplying an actual proof term separately.
-/

namespace MCoreBSD.Plectic.ConstructionGate

inductive BridgeStatus where
  | proven
  | openBridge (reason : String) (decomposition : List String)
  | conjectural (dependsOn : List String)
  deriving Repr, DecidableEq

inductive SubgateId where
  | localSystem
  | capProduct
  | integrality
  | galoisCompat
  deriving Repr, DecidableEq

structure Subgate where
  id : SubgateId
  status : BridgeStatus
  literatureEvidenceId : String
  proofArtifactId : String
  deriving Repr

/-- The four-way decomposition is an audit specification.  Empty proofArtifactId
    means that no proof artifact is registered by this file. -/
def constructionSubgates : List Subgate := [
  { id := .localSystem,
    status := .openBridge
      "Exact published theorem and domain match have not yet been certified for the universal E/Q, arbitrary-r target."
      [],
    literatureEvidenceId := "TO_AUDIT_EXACT_THEOREM",
    proofArtifactId := "" },
  { id := .capProduct,
    status := .openBridge
      "Well-defined cap-product in the exact universal target has not yet been certified; required homological vanishing and coefficient hypotheses must be explicit."
      ["LOCAL_SYSTEM"],
    literatureEvidenceId := "TO_AUDIT_EXACT_THEOREM",
    proofArtifactId := "" },
  { id := .integrality,
    status := .openBridge
      "Global Selmer integrality of the universal cycle is not supplied by the currently registered restricted published constructions."
      ["LOCAL_SYSTEM", "CAP_PRODUCT"],
    literatureEvidenceId := "OPEN_SCOPE_EXTENSION",
    proofArtifactId := "" },
  { id := .galoisCompat,
    status := .openBridge
      "Galois compatibility and any required variation in p-adic families must be proved in the exact domain rather than inferred from restricted cases."
      ["LOCAL_SYSTEM", "CAP_PRODUCT", "INTEGRALITY"],
    literatureEvidenceId := "OPEN_SCOPE_EXTENSION",
    proofArtifactId := "" }
]

/-- A proof term, not a string or status flag, is required to close a
    mathematical subgate. -/
structure Discharge (P : Prop) where
  proof : P
  evidenceId : String
  evidenceId_nonempty : evidenceId ≠ ""

/-- Abstract propositions are parameters of the conditional composition;
    this file introduces no axiom claiming any of them. -/
structure ConstructionObligations where
  LOCAL_SYSTEM : Prop
  CAP_PRODUCT : Prop
  INTEGRALITY : Prop
  GALOIS_COMPAT : Prop

/-- Honest composition: universal construction may be concluded only from
    explicit proof terms for all four obligations. -/
def constructionConditional
    (o : ConstructionObligations)
    (_hLocal : Discharge o.LOCAL_SYSTEM)
    (_hCap : Discharge o.CAP_PRODUCT)
    (_hIntegral : Discharge o.INTEGRALITY)
    (_hGalois : Discharge o.GALOIS_COMPAT) : Prop :=
  o.LOCAL_SYSTEM ∧ o.CAP_PRODUCT ∧ o.INTEGRALITY ∧ o.GALOIS_COMPAT

theorem constructionConditional_proved
    (o : ConstructionObligations)
    (hLocal : Discharge o.LOCAL_SYSTEM)
    (hCap : Discharge o.CAP_PRODUCT)
    (hIntegral : Discharge o.INTEGRALITY)
    (hGalois : Discharge o.GALOIS_COMPAT) :
    constructionConditional o hLocal hCap hIntegral hGalois := by
  exact ⟨hLocal.proof, hCap.proof, hIntegral.proof, hGalois.proof⟩

/-- Binding state: infrastructure decomposition exists, mathematics remains open. -/
def plecticConstructionStatus : BridgeStatus :=
  .openBridge
    "Universal Z_r construction is not discharged by the currently certified evidence."
    ["LOCAL_SYSTEM", "CAP_PRODUCT", "INTEGRALITY", "GALOIS_COMPAT"]

def auditInfrastructureClosed : Bool := true
def plecticConstructionProved : Bool := false
def bsdProved : Bool := false
def rankBridgeProved : Bool := false
def leadingBridgeProved : Bool := false
def openMathUsedAsProof : Bool := false

end MCoreBSD.Plectic.ConstructionGate
