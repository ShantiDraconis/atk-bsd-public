import MCore.BSD.SemanticCanonicalRankPackage

namespace MCore

/--
F5 BSD inhabitant: the rank defect vanishes identically on the canonical
same-curve semantics.  This packages exactly the substantive rank equality;
all transport/certification layers consume this object.
-/
structure BSDHabitant where
  semantics : BSDRankSemanticAnchor
  rank_eq : ∀ E : ShortWeierstrassCurveQ,
    semantics.analyticOrderAtOne E = semantics.mordellWeilRank E

/-- Natural-valued rank defect. -/
def rankDefect (H : BSDHabitant) (E : ShortWeierstrassCurveQ) : Nat :=
  Nat.dist
    (H.semantics.analyticOrderAtOne E)
    (H.semantics.mordellWeilRank E)

theorem bsd_rank_of_habitant
    (H : BSDHabitant) :
    ∀ E : ShortWeierstrassCurveQ,
      H.semantics.analyticOrderAtOne E =
        H.semantics.mordellWeilRank E :=
  H.rank_eq

theorem rank_defect_zero
    (H : BSDHabitant)
    (E : ShortWeierstrassCurveQ) :
    rankDefect H E = 0 := by
  simp [rankDefect, H.rank_eq E]

/--
Exact material producer: existence of one BSDHabitant.
This is a proposition only; no inhabitant is manufactured here.
-/
def BSDRankDefectVanishing : Prop :=
  Nonempty BSDHabitant

theorem rank_defect_vanishing_closes_rank
    (H : BSDRankDefectVanishing) :
    ∃ S : BSDRankSemanticAnchor,
      ∀ E : ShortWeierstrassCurveQ,
        S.analyticOrderAtOne E = S.mordellWeilRank E := by
  rcases H with ⟨h⟩
  exact ⟨h.semantics, h.rank_eq⟩

/--
ATK state: the schema is closed, the mathematical inhabitant is still open.
-/
def bsdMaterialProducerGaps : Nat := 1

def bsdFinalProofReadyConditional : Bool := true

def bsdRankClaims : Nat := 0

theorem bsd_material_producer_gaps_one :
    bsdMaterialProducerGaps = 1 := by
  rfl

theorem bsd_final_proof_ready_conditional :
    bsdFinalProofReadyConditional = true := by
  rfl

theorem bsd_rank_claims_zero :
    bsdRankClaims = 0 := by
  rfl

#print axioms MCore.bsd_rank_of_habitant
#print axioms MCore.rank_defect_zero
#print axioms MCore.rank_defect_vanishing_closes_rank
#print axioms MCore.bsd_material_producer_gaps_one

end MCore
