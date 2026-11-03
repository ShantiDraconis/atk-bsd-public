import open_math.P2_ATTACK

namespace P06.BSD.OpenMath

/-- Toy model showing that torsion positivity is not derivable from the frozen
ConcreteBSDModel structure alone: torsionOrder is currently supplied as an
arbitrary Nat in BSDRefinedData. -/
def p2TorsionToyModel : ConcreteBSDModel where
  mordellWeilRank := fun _ => 0
  analyticOrderAtOne := fun _ => 0
  refinedData := fun _ =>
    { leadingCoefficient := 0
      realPeriod := 1
      regulator := 1
      shaOrder := 1
      tamagawaProduct := 1
      torsionOrder := 0 }

/-- Empty known region, so every genuine curve is residual. -/
def p2TorsionToySubdomain : CertifiedCurveSubdomain where
  contains := fun _ => False

theorem p2_torsion_toy_all_residual (E : EllipticCurveQ) :
    p2TorsionToySubdomain.residual E := by
  simp [p2TorsionToySubdomain, MCore.BSD.CertifiedCurveSubdomain.residual]

/-- The frozen data model does not force torsion positivity. Any proof of
Lemma_Torsion_Nontrivial for all ConcreteBSDModel values would contradict this
toy instance. -/
theorem p2_toy_no_torsion_nontrivial :
    ¬ Lemma_Torsion_Nontrivial p2TorsionToyModel p2TorsionToySubdomain := by
  intro h
  let E := MCore.BSD.positiveControl
  have hpos := h E (p2_torsion_toy_all_residual E)
  norm_num [p2TorsionToyModel] at hpos

/-- The same torsion-zero toy also falsifies the refined BSD residual identity:
LHS = 0 while RHS = 1. -/
theorem p2_toy_no_residual :
    ¬ P2MaterialTarget p2TorsionToyModel p2TorsionToySubdomain := by
  intro h
  rcases h with ⟨R⟩
  let E := MCore.BSD.positiveControl
  have hId := R.proof E (p2_torsion_toy_all_residual E)
  norm_num [p2TorsionToyModel, MCore.BSD.RefinedBSDIdentity] at hId

/-- Toy model where the refined residual identity is true everywhere. -/
def p2ToyGoodModel : ConcreteBSDModel where
  mordellWeilRank := fun _ => 0
  analyticOrderAtOne := fun _ => 0
  refinedData := fun _ =>
    { leadingCoefficient := 1
      realPeriod := 1
      regulator := 1
      shaOrder := 1
      tamagawaProduct := 1
      torsionOrder := 1 }

theorem p2_toy_good_residual :
    P2MaterialTarget p2ToyGoodModel p2TorsionToySubdomain := by
  exact ⟨
    { proof := by
        intro E hResidual
        norm_num [p2ToyGoodModel, MCore.BSD.RefinedBSDIdentity] }⟩

/-- As for P1, the bare ConcreteBSDModel interface admits both P2-success and
P2-failure instances, so no uniform P2 theorem can be extracted from structure
alone. -/
theorem no_uniform_P2 :
    ¬ (∀ M : ConcreteBSDModel, ∀ S : CertifiedCurveSubdomain,
        P2MaterialTarget M S) := by
  intro h
  exact p2_toy_no_residual (h p2TorsionToyModel p2TorsionToySubdomain)

end P06.BSD.OpenMath
