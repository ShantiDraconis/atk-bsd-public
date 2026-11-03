import MCore.BSD.GroundedBSDHabitant

namespace MCore

/-- Exact F5 equality producer once both invariant semantics are fixed. -/
structure BSDSameCarrierRankEqualityPackage : Type where
  semantics : BSDRankSemanticAnchor
  specification : BSDRankGroundingSpecification
  analyticGrounded :
    ∀ E : ShortWeierstrassCurveQ,
      specification.analyticOrderSpec E (semantics.analyticOrderAtOne E)
  algebraicGrounded :
    ∀ E : ShortWeierstrassCurveQ,
      specification.mordellWeilRankSpec E (semantics.mordellWeilRank E)
  rankEquality :
    ∀ E : ShortWeierstrassCurveQ,
      semantics.analyticOrderAtOne E = semantics.mordellWeilRank E

def BSDSameCarrierRankEqualityTarget : Prop :=
  Nonempty BSDSameCarrierRankEqualityPackage

def BSDSameCarrierRankEqualityPackage.toGroundedHabitant
    (P : BSDSameCarrierRankEqualityPackage) : GroundedBSDHabitant :=
  { semantics := P.semantics
    grounding :=
      { specification := P.specification
        analyticOrderCanonical := P.analyticGrounded
        mordellWeilRankCanonical := P.algebraicGrounded }
    rank_eq := P.rankEquality }

theorem same_carrier_rank_equality_closes_f5
    (H : BSDSameCarrierRankEqualityTarget) :
    GroundedBSDRankDefectVanishing := by
  rcases H with ⟨P⟩
  exact ⟨P.toGroundedHabitant⟩

def bsdSameCarrierRankEqualityAvailable : Bool := false

theorem bsd_same_carrier_rank_equality_not_available :
    bsdSameCarrierRankEqualityAvailable = false := by
  rfl

#print axioms MCore.same_carrier_rank_equality_closes_f5
#print axioms MCore.bsd_same_carrier_rank_equality_not_available

end MCore
