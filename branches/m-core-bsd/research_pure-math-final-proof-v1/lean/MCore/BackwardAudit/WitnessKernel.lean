import MCore.BackwardAudit.WithoutOracle

namespace MCore.BackwardAudit

/-- The rank-part obligation localized to a single arithmetic/analytic datum. -/
def BSDInstanceClosed (d : MCore.BSDArithmeticAnalyticData) : Prop :=
  MCore.BSDRankPart d

structure BSDWitnessConstructor : Prop where
  construct : ∀ d : MCore.BSDArithmeticAnalyticData, BSDInstanceClosed d

theorem constructor_to_rank_contract
    (W : BSDWitnessConstructor) :
    RankPartWitnessContract :=
  ⟨W.construct⟩

theorem rank_contract_to_constructor
    (W : RankPartWitnessContract) :
    BSDWitnessConstructor :=
  ⟨W.witness⟩

theorem bsd_constructor_iff_rank_contract :
    BSDWitnessConstructor ↔ RankPartWitnessContract :=
  ⟨constructor_to_rank_contract, rank_contract_to_constructor⟩

theorem bsd_constructor_closes_rank_part
    (W : BSDWitnessConstructor) :
    ∀ d : MCore.BSDArithmeticAnalyticData, MCore.BSDOpenCore d :=
  rank_witness_contract_closes (constructor_to_rank_contract W)

def bsdWitnessConstructorBuilt : Bool := false

theorem bsd_witness_constructor_still_open :
    bsdWitnessConstructorBuilt = false := by rfl

#print axioms bsd_constructor_iff_rank_contract
#print axioms bsd_constructor_closes_rank_part
#print axioms bsd_witness_constructor_still_open

end MCore.BackwardAudit
