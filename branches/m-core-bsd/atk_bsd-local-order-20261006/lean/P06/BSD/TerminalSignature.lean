import P06.BSD.EndpointBehavior
import P06.BSD.ClosedMath

namespace P06.BSD

/--
Terminal signature names. These are deliberately abbreviations of the same
scientific endpoint; opening any one of them exposes no new proposition.
-/
abbrev Endpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  ScientificEndpoint G refined

abbrev Gap
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  Endpoint G refined

abbrev Habitant
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  Gap G refined

abbrev Inhabitant
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  Habitant G refined

theorem endpoint_to_gap
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData} :
    Endpoint G refined → Gap G refined := id

theorem gap_to_habitant
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData} :
    Gap G refined → Habitant G refined := id

theorem habitant_to_inhabitant
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData} :
    Habitant G refined → Inhabitant G refined := id

theorem inhabitant_to_endpoint
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData} :
    Inhabitant G refined → Endpoint G refined := id

theorem terminal_signature_cycle
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    (Endpoint G refined ↔ Gap G refined) ∧
    (Gap G refined ↔ Habitant G refined) ∧
    (Habitant G refined ↔ Inhabitant G refined) ∧
    (Inhabitant G refined ↔ Endpoint G refined) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/--
The terminal names carry exactly the same inhabitance information.
No name is weaker or stronger than the endpoint.
-/
theorem terminal_inhabitance_equivalence
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    Nonempty (Endpoint G refined) ↔
    Nonempty (Gap G refined) := by
  rfl

/--
Guard: a cycle of equivalences for an arbitrary proposition does not itself
manufacture an inhabitant. Supplying the inhabitant remains logically identical
to supplying the endpoint proposition.
-/
theorem terminal_cycle_inhabited_iff_endpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    Nonempty (Inhabitant G refined) ↔ Endpoint G refined := by
  constructor
  · rintro ⟨h⟩
    exact h
  · intro h
    exact ⟨h⟩

/-- FINAL_ROOT and the terminal signature are the same terminal proposition. -/
theorem finalRoot_iff_terminalSignature
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    BSDTerminal (fullyRealizedBSDModel G refined) ↔
      Endpoint G refined := by
  exact finalRoot_eq_mathematicalEndpoint G refined

#print axioms P06.BSD.terminal_signature_cycle
#print axioms P06.BSD.terminal_cycle_inhabited_iff_endpoint
#print axioms P06.BSD.finalRoot_iff_terminalSignature

end P06.BSD
