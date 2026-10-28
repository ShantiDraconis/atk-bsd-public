import MCore.BSD.DomainCover

namespace P06.BSD.Coverage

open MCore.BSD

/-- A partial, not necessarily exhaustive, class of genuine Q-elliptic curves. -/
structure CurveSubdomain where
  contains : EllipticCurveQ → Prop

def CurveSubdomain.residual
    (S : CurveSubdomain)
    (E : EllipticCurveQ) : Prop :=
  ¬ S.contains E

def expandCoverage
    (S SNew : CurveSubdomain) :
    CurveSubdomain :=
  { contains := fun E => S.contains E ∨ SNew.contains E }

theorem old_coverage_in_expansion
    (S SNew : CurveSubdomain)
    {E : EllipticCurveQ}
    (hE : S.contains E) :
    (expandCoverage S SNew).contains E :=
  Or.inl hE

theorem new_coverage_in_expansion
    (S SNew : CurveSubdomain)
    {E : EllipticCurveQ}
    (hE : SNew.contains E) :
    (expandCoverage S SNew).contains E :=
  Or.inr hE

theorem residual_expansion_iff
    (S SNew : CurveSubdomain)
    (E : EllipticCurveQ) :
    (expandCoverage S SNew).residual E ↔
      S.residual E ∧ SNew.residual E := by
  simp [CurveSubdomain.residual, expandCoverage]

/-- Rank equality certified only on one partial class. -/
structure RankOnSubdomain
    (M : ConcreteBSDModel)
    (S : CurveSubdomain) where
  rankProof :
    ∀ E : EllipticCurveQ, S.contains E →
      M.analyticOrderAtOne E = M.mordellWeilRank E

/-- Refined identity certified only on one partial class. -/
structure RefinedOnSubdomain
    (M : ConcreteBSDModel)
    (S : CurveSubdomain) where
  refinedProof :
    ∀ E : EllipticCurveQ, S.contains E →
      RefinedBSDIdentity (M.refinedData E)

/--
Partial coverage can be promoted to the universal producer only with an
explicit exhaustion theorem.
-/
def RankOnSubdomain.toUniversal
    {M : ConcreteBSDModel}
    {S : CurveSubdomain}
    (R : RankOnSubdomain M S)
    (covers : ∀ E : EllipticCurveQ, S.contains E) :
    ConcreteBSDRankProducer M :=
  { rankProof := fun E _ => R.rankProof E (covers E) }

def RefinedOnSubdomain.toUniversal
    {M : ConcreteBSDModel}
    {S : CurveSubdomain}
    (R : RefinedOnSubdomain M S)
    (covers : ∀ E : EllipticCurveQ, S.contains E) :
    ConcreteBSDRefinedProducer M :=
  { refinedProof := fun E _ => R.refinedProof E (covers E) }

#print axioms P06.BSD.Coverage.residual_expansion_iff
#print axioms P06.BSD.Coverage.RankOnSubdomain.toUniversal
#print axioms P06.BSD.Coverage.RefinedOnSubdomain.toUniversal

end P06.BSD.Coverage
