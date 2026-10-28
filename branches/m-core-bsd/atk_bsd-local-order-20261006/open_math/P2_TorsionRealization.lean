import open_math.P06_MordellWeil_Realization
import Mathlib.GroupTheory.Torsion

namespace P06.BSD.OpenMath

/-- The generic rational torsion subgroup. -/
abbrev RationalTorsionSubgroup (E : EllipticCurveQ) :=
  AddCommGroup.torsion (RationalPointGroup E)

/-- The rational torsion subgroup always contains zero. -/
theorem rationalTorsionSubgroup_nonempty (E : EllipticCurveQ) :
    Nonempty (RationalTorsionSubgroup E) :=
  ⟨0⟩

/-- A finite nonempty torsion subgroup has positive cardinality. -/
theorem rationalTorsion_card_pos_of_finite
    (E : EllipticCurveQ)
    [Finite (RationalTorsionSubgroup E)] :
    0 < Nat.card (RationalTorsionSubgroup E) := by
  exact Nat.card_pos_iff.mpr
    ⟨rationalTorsionSubgroup_nonempty E, inferInstance⟩

/-- Semantic bridge from the abstract refined field to genuine torsion size. -/
structure TorsionOrderRealized
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop where
  eq_card :
    ∀ E : EllipticCurveQ, S.residual E →
      (M.refinedData E).torsionOrder =
        Nat.card (RationalTorsionSubgroup E)

/-- Finiteness payload for genuine rational torsion on the residual. -/
structure RationalTorsionFiniteOnResidual
    (S : CertifiedCurveSubdomain) : Prop where
  finite :
    ∀ E : EllipticCurveQ, S.residual E →
      Finite (RationalTorsionSubgroup E)

/-- Once finiteness and the realization bridge are supplied, torsion
positivity is purely mechanical. -/
theorem torsion_nontrivial_of_realization
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (hFinite : RationalTorsionFiniteOnResidual S)
    (hRealized : TorsionOrderRealized M S) :
    Lemma_Torsion_Nontrivial M S := by
  intro E hResidual
  letI : Finite (RationalTorsionSubgroup E) :=
    hFinite.finite E hResidual
  rw [hRealized.eq_card E hResidual]
  exact rationalTorsion_card_pos_of_finite E

#check RationalTorsionSubgroup
#check rationalTorsion_card_pos_of_finite
#check TorsionOrderRealized
#check RationalTorsionFiniteOnResidual
#check torsion_nontrivial_of_realization

end P06.BSD.OpenMath
