import MCore.K12

namespace MCore

/-- A typed family of realizable inputs.  The map into
BSDArithmeticAnalyticData prevents the terminal producer from quantifying over
arbitrary unrelated pairs of natural numbers. -/
structure BSDRealizableFamily where
  Curve : Type
  toData : Curve → BSDArithmeticAnalyticData

/-- Rank-part target on the image of one realizable family. -/
def BSDRankPartOnFamily (F : BSDRealizableFamily) : Prop :=
  ∀ E : F.Curve, BSDRankPart (F.toData E)

theorem bsd_rank_part_on_family_apply
    (F : BSDRealizableFamily)
    (h : BSDRankPartOnFamily F)
    (E : F.Curve) :
    BSDRankPart (F.toData E) :=
  h E

#print axioms MCore.bsd_rank_part_on_family_apply

end MCore
