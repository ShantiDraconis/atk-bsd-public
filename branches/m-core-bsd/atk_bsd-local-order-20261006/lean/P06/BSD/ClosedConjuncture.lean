import P06.BSD.TerminalSignature

namespace P06.BSD

/-- Three-state structural signature: start / core / end. -/
inductive TerminalPhase where
  | start
  | core
  | finish
  deriving DecidableEq, Repr

/-- Binary code carried by the three phases. -/
def TerminalPhase.code : TerminalPhase → Nat
  | .start => 0
  | .core => 1
  | .finish => 2

/-- Reverse image: start and finish exchange, core is fixed. -/
def TerminalPhase.reverse : TerminalPhase → TerminalPhase
  | .start => .finish
  | .core => .core
  | .finish => .start

/-- Closed contraction: every phase normalizes to the same core. -/
def TerminalPhase.contract (_ : TerminalPhase) : TerminalPhase :=
  .core

theorem terminalPhase_reverse_involutive (p : TerminalPhase) :
    p.reverse.reverse = p := by
  cases p <;> rfl

theorem terminalPhase_contract_idempotent (p : TerminalPhase) :
    (p.contract).contract = p.contract := by
  cases p <;> rfl

theorem terminalPhase_reverse_contract (p : TerminalPhase) :
    p.reverse.contract = p.contract := by
  cases p <;> rfl

theorem terminalPhase_start_to_core :
    TerminalPhase.start.contract = .core := rfl

theorem terminalPhase_finish_to_core :
    TerminalPhase.finish.contract = .core := rfl

theorem terminalPhase_codes :
    TerminalPhase.start.code = 0 ∧
    TerminalPhase.core.code = 1 ∧
    TerminalPhase.finish.code = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/--
Every structural phase carries the same terminal mathematical payload.
The 0/1/2 dynamics changes presentation only, never the endpoint proposition.
-/
abbrev PhasePayload
    (_ : TerminalPhase)
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  Endpoint G refined

theorem phase_payload_preserved_by_reverse
    (p : TerminalPhase)
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    PhasePayload p G refined ↔ PhasePayload p.reverse G refined := by
  rfl

theorem phase_payload_preserved_by_contraction
    (p : TerminalPhase)
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    PhasePayload p G refined ↔ PhasePayload p.contract G refined := by
  rfl

/--
Closed conjuncture certificate:
start and finish are reverse images, both contract to core, and the endpoint
payload is invariant throughout the full 0/1/2 cycle.
-/
structure ClosedConjunctureCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop where
  reverseInvolutive : ∀ p : TerminalPhase, p.reverse.reverse = p
  contractionIdempotent : ∀ p : TerminalPhase, p.contract.contract = p.contract
  reverseContractsSame : ∀ p : TerminalPhase, p.reverse.contract = p.contract
  payloadReverse : ∀ p : TerminalPhase, PhasePayload p G refined ↔ PhasePayload p.reverse G refined
  payloadContract : ∀ p : TerminalPhase, PhasePayload p G refined ↔ PhasePayload p.contract G refined

def closedConjunctureCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    ClosedConjunctureCertificate G refined where
  reverseInvolutive := terminalPhase_reverse_involutive
  contractionIdempotent := terminalPhase_contract_idempotent
  reverseContractsSame := terminalPhase_reverse_contract
  payloadReverse := fun p => phase_payload_preserved_by_reverse p G refined
  payloadContract := fun p => phase_payload_preserved_by_contraction p G refined

theorem closedConjuncture
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    Nonempty (ClosedConjunctureCertificate G refined) :=
  ⟨closedConjunctureCertificate G refined⟩

#print axioms P06.BSD.closedConjuncture
#print axioms P06.BSD.terminalPhase_reverse_involutive
#print axioms P06.BSD.phase_payload_preserved_by_contraction

end P06.BSD
