import MCore.BackwardAudit.BSDBridgeLabCertificate

namespace MCore.BackwardAudit

structure RankTwoTestVector where
  conductor : Nat
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  a6 : Int
  mwRank : Nat
  analyticRank : Nat
  tamagawaProduct : Nat
  torsionOrder : Nat
  deriving DecidableEq, Repr

def testVector1933a1 : RankTwoTestVector :=
  { conductor := 1933
    a1 := 1, a2 := 0, a3 := 0, a4 := 1, a6 := -2
    mwRank := 2, analyticRank := 2
    tamagawaProduct := 1, torsionOrder := 1 }

theorem testVector1933a1_rank2 :
    testVector1933a1.mwRank = 2 ∧ testVector1933a1.analyticRank = 2 := by
  decide

theorem testVector1933a1_constants :
    testVector1933a1.tamagawaProduct = 1 ∧
    testVector1933a1.torsionOrder = 1 := by
  decide

/-- Numerical reference values are intentionally not promoted to proofs.
The rigorous-enclosure layer must replace them before collision promotion. -/
def testVector1933a1NumericsCertified : Bool := false

theorem testVector1933a1_fail_closed :
    testVector1933a1NumericsCertified = false := by rfl

#print axioms MCore.BackwardAudit.testVector1933a1_rank2
#print axioms MCore.BackwardAudit.testVector1933a1_constants
#print axioms MCore.BackwardAudit.testVector1933a1_fail_closed

end MCore.BackwardAudit
