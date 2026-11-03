import MCore.BSD.CanonicalSameCurveRankPackage

namespace MCore

/-- Semantic anchor for the two invariants.  This layer deliberately separates
    "some Nat-valued maps" from maps that are intended to be the actual
    Mordell-Weil rank and analytic order of vanishing.  No canonical inhabitant
    is supplied by this repository yet. -/
structure BSDRankSemanticAnchor where
  mordellWeilRank : ShortWeierstrassCurveQ → Nat
  analyticOrderAtOne : ShortWeierstrassCurveQ → Nat

def BSDRankSemanticAnchor.toMaps (S : BSDRankSemanticAnchor) : SameCurveRankMaps :=
  { mordellWeilRank := S.mordellWeilRank
    analyticOrderAtOne := S.analyticOrderAtOne }

/-- A mathematically meaningful unconditional rank package must be tied to a
    semantic anchor, not merely to arbitrary maps. -/
structure SemanticCanonicalSameCurveRankPackage where
  semantics : BSDRankSemanticAnchor
  certificate : SameCurveRankDirectionalCertificate semantics.toMaps

def SemanticCanonicalSameCurveRankClaim : Prop :=
  Nonempty SemanticCanonicalSameCurveRankPackage

theorem semantic_canonical_package_closes_rank
    (H : SemanticCanonicalSameCurveRankClaim) :
    ∃ S : BSDRankSemanticAnchor,
      SameCurveRankStatement S.toMaps := by
  rcases H with ⟨P⟩
  exact ⟨P.semantics,
    create_same_curve_rank_theorem P.semantics.toMaps P.certificate⟩

/-- The older map-only package is infrastructure only: without a semantic anchor
    it must not be promoted to a BSD claim. -/
def mapOnlyPackagePromotableToBSD : Bool := false

theorem map_only_package_not_promotable_to_bsd :
    mapOnlyPackagePromotableToBSD = false := by
  rfl

/-- Current repository has no canonical semantic anchor implementation. -/
def canonicalBSDRankSemanticAnchorAvailable : Bool := false

theorem canonical_bsd_rank_semantic_anchor_not_available :
    canonicalBSDRankSemanticAnchorAvailable = false := by
  rfl

/-- Consequently the exact unconditional BSD-rank claim remains disabled. -/
def semanticUnconditionalBSDRankClaimEnabled : Bool := false

theorem semantic_unconditional_bsd_rank_claim_not_enabled :
    semanticUnconditionalBSDRankClaimEnabled = false := by
  rfl

#print axioms MCore.semantic_canonical_package_closes_rank
#print axioms MCore.map_only_package_not_promotable_to_bsd
#print axioms MCore.canonical_bsd_rank_semantic_anchor_not_available
#print axioms MCore.semantic_unconditional_bsd_rank_claim_not_enabled

end MCore
