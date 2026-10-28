import MCore.K13

namespace MCore.BackwardAudit

/-- Semantic signature of the missing BSD rank-two operator.
This is a target specification, not an existence assertion. -/
structure NumberFieldComplexSecondDerivativeHeightOperatorSignature where
  numberFieldQ : Bool
  rankTwo : Bool
  complexAnalytic : Bool
  secondOrder : Bool
  archimedeanHeight : Bool
  exactLeadingConstant : Bool
  nonCircular : Bool
  deriving DecidableEq, Repr

def requiredComplexRankTwoSignature :
    NumberFieldComplexSecondDerivativeHeightOperatorSignature :=
  ⟨true, true, true, true, true, true, true⟩

/-- Candidate-family compatibility is kept as audit data.
No field here constructs the missing mathematical operator. -/
structure OperatorCandidateAudit where
  name : String
  signature : NumberFieldComplexSecondDerivativeHeightOperatorSignature
  exactMatch : Bool
  deriving Repr

def grossZagierAudit : OperatorCandidateAudit :=
  ⟨"Gross-Zagier", ⟨true, false, true, false, true, true, true⟩, false⟩

def yunZhangAudit : OperatorCandidateAudit :=
  ⟨"Yun-Zhang higher Gross-Zagier", ⟨false, true, false, true, true, true, true⟩, false⟩

def banwaitAudit : OperatorCandidateAudit :=
  ⟨"Banwait p-adic rank-two criterion", ⟨true, true, false, true, false, false, true⟩, false⟩

theorem gross_zagier_not_exact : grossZagierAudit.exactMatch = false := by rfl
theorem yun_zhang_not_exact : yunZhangAudit.exactMatch = false := by rfl
theorem banwait_not_exact : banwaitAudit.exactMatch = false := by rfl

/-- Fail-closed frontier: no exact operator is certified by the audited
candidate set. This does not assert global nonexistence. -/
def exactOperatorCertifiedInAuditedSet : Bool := false

theorem audited_set_leaves_operator_open :
    exactOperatorCertifiedInAuditedSet = false := by rfl

#print axioms MCore.BackwardAudit.gross_zagier_not_exact
#print axioms MCore.BackwardAudit.yun_zhang_not_exact
#print axioms MCore.BackwardAudit.banwait_not_exact
#print axioms MCore.BackwardAudit.audited_set_leaves_operator_open

end MCore.BackwardAudit
