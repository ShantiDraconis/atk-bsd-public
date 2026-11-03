import open_math.P06_MiningStatus
import P06.BSD.KnownExpansion

namespace P06.BSD.OpenMath

/-
P06 KNOWN mining audit against frozen
  a3edf6209a143db063939ada57869b41e49a708f

What the frozen source supplies:
  * exact subdomain algebra;
  * union of already-proved RankOnSubdomain inhabitants;
  * union of already-proved RefinedOnSubdomain inhabitants;
  * residual transport after a genuine enlargement of the known region.

What the frozen source does not supply:
  * a concrete nonempty rank-0/rank-1/Gross-Zagier/Kolyvagin subdomain inhabitant;
  * a concrete nonempty refined-BSD subdomain inhabitant;
  * a bridge identifying BSDRefinedData.torsionOrder with the cardinality of
    the geometric torsion subgroup.

Therefore this file does not fabricate a positive KNOWN class.  It records the
maximal unconditional seed already derivable from the frozen structures:
the empty known subdomain.  Its residual is the whole genuine curve domain, so
it produces no material compression.
-/

abbrev FrozenKnownSeed : CertifiedCurveSubdomain :=
  MCore.BSD.CertifiedCurveSubdomain.empty

/-- P1 is vacuously known on the empty seed. -/
def frozenEmptyRankKnown
    (M : ConcreteBSDModel) :
    RankOnSubdomain M FrozenKnownSeed where
  proof := by
    intro E hE
    contradiction

/-- P2 is vacuously known on the empty seed. -/
def frozenEmptyRefinedKnown
    (M : ConcreteBSDModel) :
    RefinedOnSubdomain M FrozenKnownSeed where
  proof := by
    intro E hE
    contradiction

/-- The empty frozen seed does not shrink P1 at all: every genuine curve lies
in its exact residual. -/
theorem frozenEmptySeed_rank_residual_is_universal
    (E : EllipticCurveQ) :
    FrozenKnownSeed.residual E := by
  simp [FrozenKnownSeed, MCore.BSD.CertifiedCurveSubdomain.empty,
    MCore.BSD.CertifiedCurveSubdomain.residual]

/-- Same fact for the P2 mining lane: the starting residual remains universal. -/
theorem frozenEmptySeed_refined_residual_is_universal
    (E : EllipticCurveQ) :
    FrozenKnownSeed.residual E :=
  frozenEmptySeed_rank_residual_is_universal E

/-- Any genuine P1 compression must enter as a new certified nonempty class T.
Once such a T exists, frozen union machinery performs the enlargement
mechanically; this theorem adds no mathematical assumption. -/
def mineRankKnown
    {M : ConcreteBSDModel} {T : CertifiedCurveSubdomain}
    (hT : RankOnSubdomain M T) :
    RankOnSubdomain M
      (MCore.BSD.CertifiedCurveSubdomain.union FrozenKnownSeed T) :=
  P06.BSD.extendRankKnown (frozenEmptyRankKnown M) hT

/-- Any genuine P2 compression likewise requires an independently certified
nonempty class T before frozen union machinery can reduce the residual. -/
def mineRefinedKnown
    {M : ConcreteBSDModel} {T : CertifiedCurveSubdomain}
    (hT : RefinedOnSubdomain M T) :
    RefinedOnSubdomain M
      (MCore.BSD.CertifiedCurveSubdomain.union FrozenKnownSeed T) :=
  P06.BSD.extendRefinedKnown (frozenEmptyRefinedKnown M) hT

/-
Current mining result:

  POSITIVE_KNOWN_P1_CLASS   = NONE FOUND IN FROZEN
  POSITIVE_KNOWN_P2_CLASS   = NONE FOUND IN FROZEN
  TORSION_CARDINAL_BRIDGE   = NONE FOUND IN FROZEN

Hence the material frontier is unchanged:
  P1RankResidualObligation        0/1
  P2TorsionPositiveObligation     0/1
  P2QuotientIdentityObligation    0/1

A future mining commit may add a concrete T only after an existing theorem or
certificate actually inhabits RankOnSubdomain M T and/or RefinedOnSubdomain M T.
-/

#check frozenEmptyRankKnown
#check frozenEmptyRefinedKnown
#check frozenEmptySeed_rank_residual_is_universal
#check mineRankKnown
#check mineRefinedKnown
#check P06.BSD.extendRankKnown
#check P06.BSD.extendRefinedKnown

end P06.BSD.OpenMath
