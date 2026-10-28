import MCore.BSD.ResidualFrontier

namespace MCore.BSD

namespace CertifiedCurveSubdomain

/-- Extensional inclusion of certified curve subdomains. -/
def Le (S T : CertifiedCurveSubdomain) : Prop :=
  ∀ E : EllipticCurveQ, S.contains E → T.contains E

infix:50 " ⊑ " => Le

theorem le_refl (S : CertifiedCurveSubdomain) : S ⊑ S := by
  intro E h
  exact h

theorem le_trans {S T U : CertifiedCurveSubdomain}
    (hST : S ⊑ T) (hTU : T ⊑ U) : S ⊑ U := by
  intro E hS
  exact hTU E (hST E hS)

/-- Empty certified subdomain. -/
def empty : CertifiedCurveSubdomain where
  contains := fun _ => False

/-- Universal certified subdomain. This is only a set-theoretic object; it
contains no BSD proof. -/
def univ : CertifiedCurveSubdomain where
  contains := fun _ => True

/-- Union of two certified predicates. -/
def union (S T : CertifiedCurveSubdomain) : CertifiedCurveSubdomain where
  contains := fun E => S.contains E ∨ T.contains E

/-- Intersection of two certified predicates. -/
def inter (S T : CertifiedCurveSubdomain) : CertifiedCurveSubdomain where
  contains := fun E => S.contains E ∧ T.contains E

theorem empty_le (S : CertifiedCurveSubdomain) : empty ⊑ S := by
  intro E h
  contradiction

theorem le_univ (S : CertifiedCurveSubdomain) : S ⊑ univ := by
  intro E h
  trivial

theorem le_union_left (S T : CertifiedCurveSubdomain) : S ⊑ union S T := by
  intro E h
  exact Or.inl h

theorem le_union_right (S T : CertifiedCurveSubdomain) : T ⊑ union S T := by
  intro E h
  exact Or.inr h

theorem inter_le_left (S T : CertifiedCurveSubdomain) : inter S T ⊑ S := by
  intro E h
  exact h.1

theorem inter_le_right (S T : CertifiedCurveSubdomain) : inter S T ⊑ T := by
  intro E h
  exact h.2

/-- Enlarging the known subdomain shrinks the literal residual. -/
theorem residual_antitone {S T : CertifiedCurveSubdomain}
    (hST : S ⊑ T) :
    ∀ E : EllipticCurveQ, T.residual E → S.residual E := by
  intro E hT hS
  exact hT (hST E hS)

end CertifiedCurveSubdomain

namespace RankOnSubdomain

/-- Restrict a known P1 proof to a smaller certified subdomain. -/
def restrict
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hST : S ⊑ T)
    (P : RankOnSubdomain M T) :
    RankOnSubdomain M S :=
  { proof := fun E hS => P.proof E (hST E hS) }

/-- Merge two known P1 class proofs into their union. -/
def union
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (PS : RankOnSubdomain M S)
    (PT : RankOnSubdomain M T) :
    RankOnSubdomain M (CertifiedCurveSubdomain.union S T) :=
  { proof := fun E h =>
      match h with
      | Or.inl hS => PS.proof E hS
      | Or.inr hT => PT.proof E hT }

end RankOnSubdomain

namespace RefinedOnSubdomain

/-- Restrict a known P2 proof to a smaller certified subdomain. -/
def restrict
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hST : S ⊑ T)
    (P : RefinedOnSubdomain M T) :
    RefinedOnSubdomain M S :=
  { proof := fun E hS => P.proof E (hST E hS) }

/-- Merge two known P2 class proofs into their union. -/
def union
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (PS : RefinedOnSubdomain M S)
    (PT : RefinedOnSubdomain M T) :
    RefinedOnSubdomain M (CertifiedCurveSubdomain.union S T) :=
  { proof := fun E h =>
      match h with
      | Or.inl hS => PS.proof E hS
      | Or.inr hT => PT.proof E hT }

end RefinedOnSubdomain

namespace RankOnResidual

/-- A residual P1 proof for a smaller known set can be transported to the
residual of a larger known set, because the latter residual is smaller. -/
def of_le
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hST : S ⊑ T)
    (P : RankOnResidual M S) :
    RankOnResidual M T :=
  { proof := fun E hT =>
      P.proof E (CertifiedCurveSubdomain.residual_antitone hST E hT) }

end RankOnResidual

namespace RefinedOnResidual

/-- Residual P2 transport under enlargement of the known subdomain. -/
def of_le
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (hST : S ⊑ T)
    (P : RefinedOnResidual M S) :
    RefinedOnResidual M T :=
  { proof := fun E hT =>
      P.proof E (CertifiedCurveSubdomain.residual_antitone hST E hT) }

end RefinedOnResidual

/-- If both P1 and P2 are known on S and on T, they are known on S ∪ T. -/
def mergeKnownPair
    {M : ConcreteBSDModel} {S T : CertifiedCurveSubdomain}
    (rS : RankOnSubdomain M S) (rT : RankOnSubdomain M T)
    (fS : RefinedOnSubdomain M S) (fT : RefinedOnSubdomain M T) :
    RankOnSubdomain M (CertifiedCurveSubdomain.union S T) ∧
      RefinedOnSubdomain M (CertifiedCurveSubdomain.union S T) :=
  ⟨RankOnSubdomain.union rS rT, RefinedOnSubdomain.union fS fT⟩

end MCore.BSD
