import MCore.BSD.BSDHabitant

namespace MCore

/--
Independent semantic predicates for the two BSD rank invariants.

A future concrete carrier implementation must define these predicates from:
- order of vanishing of the Hasse-Weil L-function at s = 1;
- Mordell-Weil rank of E(Q).

This file does not postulate either definition.
-/
structure BSDRankGroundingSpecification : Type where
  analyticOrderSpec : ShortWeierstrassCurveQ → Nat → Prop
  mordellWeilRankSpec : ShortWeierstrassCurveQ → Nat → Prop

/--
Semantic grounding contract for the two sides of the BSD rank equality.

Unlike the previous placeholder shape, the fields below are actual evidence:
for every curve, the chosen Nat-valued invariant must satisfy the independently
supplied semantic specification.
-/
structure BSDCanonicalRankGrounding
    (S : BSDRankSemanticAnchor) : Type where
  specification : BSDRankGroundingSpecification
  analyticOrderCanonical :
    ∀ E : ShortWeierstrassCurveQ,
      specification.analyticOrderSpec E (S.analyticOrderAtOne E)
  mordellWeilRankCanonical :
    ∀ E : ShortWeierstrassCurveQ,
      specification.mordellWeilRankSpec E (S.mordellWeilRank E)

/--
Hardened F5 habitant: same-curve semantic grounding plus universal rank equality.
-/
structure GroundedBSDHabitant : Type where
  semantics : BSDRankSemanticAnchor
  grounding : BSDCanonicalRankGrounding semantics
  rank_eq : ∀ E : ShortWeierstrassCurveQ,
    semantics.analyticOrderAtOne E = semantics.mordellWeilRank E

def GroundedBSDRankDefectVanishing : Prop :=
  Nonempty GroundedBSDHabitant

def groundedRankDefect
    (H : GroundedBSDHabitant)
    (E : ShortWeierstrassCurveQ) : Nat :=
  Nat.dist
    (H.semantics.analyticOrderAtOne E)
    (H.semantics.mordellWeilRank E)

theorem grounded_rank_defect_zero
    (H : GroundedBSDHabitant)
    (E : ShortWeierstrassCurveQ) :
    groundedRankDefect H E = 0 := by
  simp [groundedRankDefect, H.rank_eq E]

theorem grounded_bsd_of_habitant
    (H : GroundedBSDHabitant) :
    ∀ E : ShortWeierstrassCurveQ,
      H.semantics.analyticOrderAtOne E =
        H.semantics.mordellWeilRank E :=
  H.rank_eq

/--
The analytic semantic evidence can be projected from any genuine habitant.
-/
theorem grounded_habitant_has_analytic_semantics
    (H : GroundedBSDHabitant) :
    ∀ E : ShortWeierstrassCurveQ,
      H.grounding.specification.analyticOrderSpec E
        (H.semantics.analyticOrderAtOne E) :=
  H.grounding.analyticOrderCanonical

/--
The algebraic semantic evidence can be projected from any genuine habitant.
-/
theorem grounded_habitant_has_mordell_weil_semantics
    (H : GroundedBSDHabitant) :
    ∀ E : ShortWeierstrassCurveQ,
      H.grounding.specification.mordellWeilRankSpec E
        (H.semantics.mordellWeilRank E) :=
  H.grounding.mordellWeilRankCanonical

/--
Current repository state: no concrete canonical semantic specification and no
kernel inhabitant are supplied here.
-/
def groundedBSDHabitantAvailable : Bool := false

theorem grounded_bsd_habitant_not_available :
    groundedBSDHabitantAvailable = false := by
  rfl

def bsdGroundedMaterialProducerGaps : Nat := 1

theorem bsd_grounded_material_producer_gaps_one :
    bsdGroundedMaterialProducerGaps = 1 := by
  rfl

#print axioms MCore.grounded_rank_defect_zero
#print axioms MCore.grounded_bsd_of_habitant
#print axioms MCore.grounded_habitant_has_analytic_semantics
#print axioms MCore.grounded_habitant_has_mordell_weil_semantics
#print axioms MCore.grounded_bsd_habitant_not_available
#print axioms MCore.bsd_grounded_material_producer_gaps_one

end MCore
