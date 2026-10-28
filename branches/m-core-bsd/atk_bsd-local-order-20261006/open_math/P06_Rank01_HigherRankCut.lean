import open_math.P06_Rank0_Exclusion
import P06.BSD.KnownExpansion

namespace P06.BSD.OpenMath

/-- Analytic-rank-one class for the selected concrete model. -/
def Rank1Subdomain (M : ConcreteBSDModel) : CertifiedCurveSubdomain where
  contains := fun E => M.analyticOrderAtOne E = 1

/-- Exact material theorem needed to certify the rank-one class. -/
def Rank1ArithmeticMaterial (M : ConcreteBSDModel) : Prop :=
  ∀ E : EllipticCurveQ,
    M.analyticOrderAtOne E = 1 →
      M.mordellWeilRank E = 1

def rank1Known_of_material
    {M : ConcreteBSDModel}
    (h : Rank1ArithmeticMaterial M) :
    RankOnSubdomain M (Rank1Subdomain M) where
  proof := by
    intro E hAnalytic1
    rw [hAnalytic1, h E hAnalytic1]

/-- Union of the rank-zero and rank-one analytic classes. -/
def Rank01Subdomain (M : ConcreteBSDModel) : CertifiedCurveSubdomain :=
  MCore.BSD.CertifiedCurveSubdomain.union
    (Rank0Subdomain M) (Rank1Subdomain M)

/-- If both low-rank material inputs are supplied, the whole rank-0/1 union is
certified by frozen union machinery. -/
def rank01Known_of_material
    {M : ConcreteBSDModel}
    (h0 : Rank0ArithmeticMaterial M)
    (h1 : Rank1ArithmeticMaterial M) :
    RankOnSubdomain M (Rank01Subdomain M) :=
  MCore.BSD.RankOnSubdomain.union
    (rank0Known_of_material h0)
    (rank1Known_of_material h1)

/-- Exact complement after low-rank mining. -/
theorem rank01_residual_iff
    {M : ConcreteBSDModel} {E : EllipticCurveQ} :
    (Rank01Subdomain M).residual E ↔
      M.analyticOrderAtOne E ≠ 0 ∧
      M.analyticOrderAtOne E ≠ 1 := by
  simp [Rank01Subdomain, Rank0Subdomain, Rank1Subdomain,
    MCore.BSD.CertifiedCurveSubdomain.union,
    MCore.BSD.CertifiedCurveSubdomain.residual]

/-- For natural-valued analytic order, the rank-0/1 residual is exactly the
higher-rank regime. -/
theorem rank01_residual_implies_ge_two
    {M : ConcreteBSDModel} {E : EllipticCurveQ}
    (h : (Rank01Subdomain M).residual E) :
    2 ≤ M.analyticOrderAtOne E := by
  have hh := (rank01_residual_iff (M := M) (E := E)).1 h
  omega

theorem ge_two_implies_rank01_residual
    {M : ConcreteBSDModel} {E : EllipticCurveQ}
    (h : 2 ≤ M.analyticOrderAtOne E) :
    (Rank01Subdomain M).residual E := by
  apply (rank01_residual_iff (M := M) (E := E)).2
  omega

theorem rank01_residual_iff_ge_two
    {M : ConcreteBSDModel} {E : EllipticCurveQ} :
    (Rank01Subdomain M).residual E ↔
      2 ≤ M.analyticOrderAtOne E := by
  constructor
  · exact rank01_residual_implies_ge_two
  · exact ge_two_implies_rank01_residual

/-- Exact remaining P1 obligation after successful rank-0/1 mining. -/
def HigherRankResidualP1 (M : ConcreteBSDModel) : Prop :=
  ∀ E : EllipticCurveQ,
    2 ≤ M.analyticOrderAtOne E →
      M.analyticOrderAtOne E = M.mordellWeilRank E

/-- Low-rank material plus the higher-rank residual closes universal P1
through the frozen exact frontier. -/
theorem p1_of_rank01_and_higher_rank
    {M : ConcreteBSDModel}
    (h0 : Rank0ArithmeticMaterial M)
    (h1 : Rank1ArithmeticMaterial M)
    (hHigher : HigherRankResidualP1 M) :
    P06.BSD.BSDP1 M := by
  have hKnown :
      Nonempty (RankOnSubdomain M (Rank01Subdomain M)) :=
    ⟨rank01Known_of_material h0 h1⟩
  have hResidual :
      Nonempty (RankOnResidual M (Rank01Subdomain M)) := by
    exact ⟨{ proof := fun E hR =>
      hHigher E (rank01_residual_implies_ge_two hR) }⟩
  exact
    (P06.BSD.p1_frontier_exact
      (M := M) (S := Rank01Subdomain M)).2
      ⟨hKnown, hResidual⟩

/-- Conversely, a residual P1 producer on Rank01Subdomain is exactly the
higher-rank equality statement. -/
theorem higher_rank_of_p1_rank01_residual
    {M : ConcreteBSDModel}
    (hP1 : BSD_P1_Producer M (Rank01Subdomain M)) :
    HigherRankResidualP1 M := by
  rcases hP1 with ⟨P⟩
  intro E hGe2
  exact P.proof E (ge_two_implies_rank01_residual hGe2)

theorem rank01_residual_P1_iff_higher_rank
    {M : ConcreteBSDModel} :
    BSD_P1_Producer M (Rank01Subdomain M) ↔
      HigherRankResidualP1 M := by
  constructor
  · exact higher_rank_of_p1_rank01_residual
  · intro hHigher
    exact ⟨{ proof := fun E hR =>
      hHigher E (rank01_residual_implies_ge_two hR) }⟩

#check Rank1Subdomain
#check Rank1ArithmeticMaterial
#check Rank01Subdomain
#check rank01_residual_iff_ge_two
#check HigherRankResidualP1
#check rank01_residual_P1_iff_higher_rank

end P06.BSD.OpenMath
