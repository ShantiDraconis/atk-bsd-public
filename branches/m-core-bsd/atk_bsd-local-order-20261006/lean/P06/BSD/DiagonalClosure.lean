import P06.BSD.CenterStability

namespace P06.BSD

/-- Finite two-coordinate signature used only to encode the user's terminal ratios. -/
structure TerminalRatioState where
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def ratio01 : TerminalRatioState := ⟨0, 1⟩
def ratio11 : TerminalRatioState := ⟨1, 1⟩
def ratio02 : TerminalRatioState := ⟨0, 2⟩
def ratio22 : TerminalRatioState := ⟨2, 2⟩

/-- Exact terminal diagonalization requested by the 0/1 and 0/2 signatures. -/
def diagonalize : TerminalRatioState → TerminalRatioState
  | ⟨0, 1⟩ => ratio11
  | ⟨0, 2⟩ => ratio22
  | s => s

theorem diagonalize_01 :
    diagonalize ratio01 = ratio11 := rfl

theorem diagonalize_02 :
    diagonalize ratio02 = ratio22 := rfl

theorem diagonalize_11_fixed :
    diagonalize ratio11 = ratio11 := rfl

theorem diagonalize_22_fixed :
    diagonalize ratio22 = ratio22 := rfl

theorem diagonalize_terminal_idempotent_01 :
    diagonalize (diagonalize ratio01) = diagonalize ratio01 := by
  rfl

theorem diagonalize_terminal_idempotent_02 :
    diagonalize (diagonalize ratio02) = diagonalize ratio02 := by
  rfl

/-- Both terminal diagonals carry exactly the same scientific endpoint payload. -/
abbrev RatioPayload
    (_ : TerminalRatioState)
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  Endpoint G refined

theorem ratio01_to_11_preserves_endpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    RatioPayload ratio01 G refined ↔ RatioPayload ratio11 G refined := by
  rfl

theorem ratio02_to_22_preserves_endpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    RatioPayload ratio02 G refined ↔ RatioPayload ratio22 G refined := by
  rfl

theorem both_diagonals_same_endpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    RatioPayload ratio11 G refined ↔ RatioPayload ratio22 G refined := by
  rfl

/--
Closed ratio signature:
  0/1 -> 1/1
  0/2 -> 2/2
and both diagonals are fixed and carry the same terminal endpoint.
-/
structure DiagonalClosureCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop where
  path01 : diagonalize ratio01 = ratio11
  path02 : diagonalize ratio02 = ratio22
  fixed11 : diagonalize ratio11 = ratio11
  fixed22 : diagonalize ratio22 = ratio22
  endpoint01 : RatioPayload ratio01 G refined ↔ RatioPayload ratio11 G refined
  endpoint02 : RatioPayload ratio02 G refined ↔ RatioPayload ratio22 G refined
  sameEndpoint : RatioPayload ratio11 G refined ↔ RatioPayload ratio22 G refined

def diagonalClosureCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    DiagonalClosureCertificate G refined where
  path01 := diagonalize_01
  path02 := diagonalize_02
  fixed11 := diagonalize_11_fixed
  fixed22 := diagonalize_22_fixed
  endpoint01 := ratio01_to_11_preserves_endpoint G refined
  endpoint02 := ratio02_to_22_preserves_endpoint G refined
  sameEndpoint := both_diagonals_same_endpoint G refined

theorem diagonalClosure
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    Nonempty (DiagonalClosureCertificate G refined) :=
  ⟨diagonalClosureCertificate G refined⟩

#print axioms P06.BSD.diagonalClosure
#print axioms P06.BSD.diagonalize_terminal_idempotent_01
#print axioms P06.BSD.diagonalize_terminal_idempotent_02

end P06.BSD
