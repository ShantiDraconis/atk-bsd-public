import P06.BSD.CenterStability

namespace P06.BSD

/-- Discrete terminal ratio code. This is a structural code, not field division. -/
structure TerminalRatio where
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

def ratio01 : TerminalRatio := ⟨0, 1⟩
def ratio11 : TerminalRatio := ⟨1, 1⟩
def ratio02 : TerminalRatio := ⟨0, 2⟩
def ratio22 : TerminalRatio := ⟨2, 2⟩

/-- Terminal normalization sends a zero numerator to its diagonal representative. -/
def TerminalRatio.normalize : TerminalRatio → TerminalRatio
  | ⟨0, 1⟩ => ratio11
  | ⟨0, 2⟩ => ratio22
  | r => r

theorem normalize_01 :
    ratio01.normalize = ratio11 := rfl

theorem normalize_02 :
    ratio02.normalize = ratio22 := rfl

theorem normalize_11 :
    ratio11.normalize = ratio11 := rfl

theorem normalize_22 :
    ratio22.normalize = ratio22 := rfl

theorem terminalRatio_normalize_idempotent_on_01 :
    ratio01.normalize.normalize = ratio01.normalize := by
  rfl

theorem terminalRatio_normalize_idempotent_on_02 :
    ratio02.normalize.normalize = ratio02.normalize := by
  rfl

/-- Diagonal representative determines the corresponding side code. -/
def TerminalRatio.toPhase : TerminalRatio → TerminalPhase
  | ⟨1, 1⟩ => .core
  | ⟨2, 2⟩ => .finish
  | _ => .start

theorem ratio01_to_core_after_normalize :
    ratio01.normalize.toPhase = .core := rfl

theorem ratio02_to_finish_after_normalize :
    ratio02.normalize.toPhase = .finish := rfl

theorem ratio02_to_core_after_contract :
    ratio02.normalize.toPhase.contract = .core := rfl

theorem ratio01_to_core_after_contract :
    ratio01.normalize.toPhase.contract = .core := rfl

/--
Both terminal normalizations hit the same contracted core.
This is the exact structural reading of 0/1 -> 1/1 and 0/2 -> 2/2.
-/
theorem ratio_paths_hit_same_core :
    ratio01.normalize.toPhase.contract =
      ratio02.normalize.toPhase.contract := by
  rfl

/-- Every ratio stage carries the same terminal endpoint payload. -/
abbrev RatioPayload
    (_ : TerminalRatio)
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  Endpoint G refined

theorem ratio01_payload_normalized
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    RatioPayload ratio01 G refined ↔
      RatioPayload ratio11 G refined := by
  rfl

theorem ratio02_payload_normalized
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    RatioPayload ratio02 G refined ↔
      RatioPayload ratio22 G refined := by
  rfl

theorem diagonal_payloads_same_endpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    RatioPayload ratio11 G refined ↔
      RatioPayload ratio22 G refined := by
  rfl

structure TerminalRatioCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop where
  zeroOneToOneOne : ratio01.normalize = ratio11
  zeroTwoToTwoTwo : ratio02.normalize = ratio22
  onePathCore : ratio01.normalize.toPhase.contract = .core
  twoPathCore : ratio02.normalize.toPhase.contract = .core
  payload01 : RatioPayload ratio01 G refined ↔ RatioPayload ratio11 G refined
  payload02 : RatioPayload ratio02 G refined ↔ RatioPayload ratio22 G refined
  diagonalSame :
    RatioPayload ratio11 G refined ↔ RatioPayload ratio22 G refined

def terminalRatioCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    TerminalRatioCertificate G refined where
  zeroOneToOneOne := normalize_01
  zeroTwoToTwoTwo := normalize_02
  onePathCore := ratio01_to_core_after_contract
  twoPathCore := ratio02_to_core_after_contract
  payload01 := ratio01_payload_normalized G refined
  payload02 := ratio02_payload_normalized G refined
  diagonalSame := diagonal_payloads_same_endpoint G refined

theorem terminalRatioClosed
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    Nonempty (TerminalRatioCertificate G refined) :=
  ⟨terminalRatioCertificate G refined⟩

#print axioms P06.BSD.terminalRatioClosed
#print axioms P06.BSD.ratio_paths_hit_same_core
#print axioms P06.BSD.diagonal_payloads_same_endpoint

end P06.BSD
