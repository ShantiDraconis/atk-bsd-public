import open_math.P06_KNOWN_Mining

namespace P06.BSD.OpenMath

/-
First concrete mining class for P1.

This file defines the exact analytic-rank-zero class and the material statement
needed to turn it into a genuine RankOnSubdomain inhabitant.

Important: Rank0ArithmeticMaterial is NOT derivable for arbitrary
ConcreteBSDModel values.  P06_Rank0_FrontierAudit.lean gives an explicit toy
countermodel.  Therefore this file contains no universal attempt theorem and no
placeholder proof.
-/

/-- Curves whose analytic order at s=1 is exactly zero, relative to the concrete
model M. -/
def Rank0Subdomain (M : ConcreteBSDModel) : CertifiedCurveSubdomain where
  contains := fun E => M.analyticOrderAtOne E = 0

/-- Exact material input required on the analytic-rank-zero class. -/
def Rank0ArithmeticMaterial (M : ConcreteBSDModel) : Prop :=
  ∀ E : EllipticCurveQ,
    M.analyticOrderAtOne E = 0 →
      M.mordellWeilRank E = 0

/-- Once the arithmetic rank-zero statement is supplied, the rank equality on
Rank0Subdomain is mechanical. -/
def rank0Known_of_material
    {M : ConcreteBSDModel}
    (h : Rank0ArithmeticMaterial M) :
    RankOnSubdomain M (Rank0Subdomain M) where
  proof := by
    intro E hAnalytic0
    rw [hAnalytic0, h E hAnalytic0]

/-- The residual after mining rank zero is literally the complement of analytic
rank zero. -/
theorem rank0_residual_iff
    {M : ConcreteBSDModel} {E : EllipticCurveQ} :
    (Rank0Subdomain M).residual E ↔
      M.analyticOrderAtOne E ≠ 0 := by
  rfl

/-- Mining rank zero enlarges the frozen empty seed once genuine material for
this particular model M has been supplied. -/
def mineRank0
    {M : ConcreteBSDModel}
    (h : Rank0ArithmeticMaterial M) :
    RankOnSubdomain M
      (MCore.BSD.CertifiedCurveSubdomain.union
        FrozenKnownSeed (Rank0Subdomain M)) :=
  mineRankKnown (rank0Known_of_material h)

/-- Explicit conditional form of the first residual compression.
No inhabitant is manufactured here. -/
theorem rank0_compression_requires_material
    {M : ConcreteBSDModel}
    (h : Rank0ArithmeticMaterial M) :
    Nonempty
      (RankOnSubdomain M
        (MCore.BSD.CertifiedCurveSubdomain.union
          FrozenKnownSeed (Rank0Subdomain M))) :=
  ⟨mineRank0 h⟩

#check Rank0Subdomain
#check Rank0ArithmeticMaterial
#check rank0Known_of_material
#check rank0_residual_iff
#check mineRank0
#check rank0_compression_requires_material

end P06.BSD.OpenMath
