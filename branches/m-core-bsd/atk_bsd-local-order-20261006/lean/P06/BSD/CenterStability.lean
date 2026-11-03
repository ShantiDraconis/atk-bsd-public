import P06.BSD.ClosedConjuncture

namespace P06.BSD

/-- Boolean side choice around the stable core. -/
def TerminalPhase.chooseSide : Bool → TerminalPhase
  | false => .start
  | true => .finish

/-- Without a side choice, the stable state is the core. -/
def TerminalPhase.stable : TerminalPhase := .core

theorem stable_is_core :
    TerminalPhase.stable = .core := rfl

theorem choose_false_is_start :
    TerminalPhase.chooseSide false = .start := rfl

theorem choose_true_is_finish :
    TerminalPhase.chooseSide true = .finish := rfl

/-- Either Boolean choice contracts back to the same core. -/
theorem chosen_side_contracts_to_core (b : Bool) :
    (TerminalPhase.chooseSide b).contract = .core := by
  cases b <;> rfl

/-- Reversal swaps Boolean sides. -/
theorem reverse_chooseSide (b : Bool) :
    (TerminalPhase.chooseSide b).reverse =
      TerminalPhase.chooseSide (!b) := by
  cases b <;> rfl

/--
Three-way convergence at the terminal bit:
start, core and finish all normalize to the same core.
-/
theorem three_paths_hit_same_terminal_bit :
    TerminalPhase.start.contract =
      TerminalPhase.core.contract ∧
    TerminalPhase.finish.contract =
      TerminalPhase.core.contract := by
  exact ⟨rfl, rfl⟩

/--
The terminal payload is invariant under choosing true/false and contracting.
Thus the Boolean branch changes only presentation, not the endpoint proposition.
-/
theorem boolean_choice_payload_invariant
    (b : Bool)
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    PhasePayload (TerminalPhase.chooseSide b) G refined ↔
      PhasePayload TerminalPhase.core G refined := by
  rfl

/--
Center-stability certificate: no choice leaves the system at core; either
Boolean choice moves to a side whose contraction returns to that same core.
-/
structure CenterStabilityCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop where
  stableCore : TerminalPhase.stable = .core
  falseBranch : TerminalPhase.chooseSide false = .start
  trueBranch : TerminalPhase.chooseSide true = .finish
  bothReturn : ∀ b, (TerminalPhase.chooseSide b).contract = .core
  payloadInvariant :
    ∀ b, PhasePayload (TerminalPhase.chooseSide b) G refined ↔
      PhasePayload TerminalPhase.core G refined

def centerStabilityCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    CenterStabilityCertificate G refined where
  stableCore := stable_is_core
  falseBranch := choose_false_is_start
  trueBranch := choose_true_is_finish
  bothReturn := chosen_side_contracts_to_core
  payloadInvariant := fun b => boolean_choice_payload_invariant b G refined

theorem centerStability
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    Nonempty (CenterStabilityCertificate G refined) :=
  ⟨centerStabilityCertificate G refined⟩

#print axioms P06.BSD.centerStability
#print axioms P06.BSD.three_paths_hit_same_terminal_bit
#print axioms P06.BSD.boolean_choice_payload_invariant

end P06.BSD
