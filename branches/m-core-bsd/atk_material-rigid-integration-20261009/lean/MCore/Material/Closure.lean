import MCore
namespace MCore.Material
structure BSDClosure (RankResidual Torsion Quotient : Prop) where
  rankResidual : RankResidual
  torsionPositive : Torsion
  quotientIdentity : Quotient

def MaterialBSDProducer (RankResidual Torsion Quotient : Prop) : Prop :=
  Nonempty (BSDClosure RankResidual Torsion Quotient)
end MCore.Material
