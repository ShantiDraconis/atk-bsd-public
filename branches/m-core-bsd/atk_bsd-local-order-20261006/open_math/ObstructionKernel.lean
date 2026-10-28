import open_math.P1_ATTACK
import open_math.P2_ATTACK

namespace P06.BSD.OpenMath

/-- One genuine residual rank mismatch is enough to refute a proposed P1
producer for the selected model/subdomain. -/
theorem p1_obstruction_of_residual_rank_mismatch
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    {E : EllipticCurveQ}
    (hResidual : S.residual E)
    (hMismatch :
      M.analyticOrderAtOne E ≠ M.mordellWeilRank E) :
    ¬ P1MaterialTarget M S := by
  intro hP1
  rcases hP1 with ⟨P⟩
  exact hMismatch (P.proof E hResidual)

/-- Conversely, a P1 producer rules out every residual rank mismatch. -/
theorem p1_producer_forces_no_residual_mismatch
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (hP1 : P1MaterialTarget M S) :
    ∀ E : EllipticCurveQ, S.residual E →
      M.analyticOrderAtOne E = M.mordellWeilRank E := by
  rcases hP1 with ⟨P⟩
  exact P.proof

/-- One residual nonzero refined defect refutes P2 for the selected
model/subdomain. -/
theorem p2_obstruction_of_residual_defect_ne_zero
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    {E : EllipticCurveQ}
    (hResidual : S.residual E)
    (hDefect :
      MCore.BSD.refinedDefect (M.refinedData E) ≠ 0) :
    ¬ P2MaterialTarget M S := by
  intro hP2
  rcases hP2 with ⟨P⟩
  have hId := P.proof E hResidual
  have hZero :=
    (MCore.BSD.refinedIdentity_iff_defect_eq_zero
      (M.refinedData E)).1 hId
  exact hDefect hZero

/-- P2 forces defect zero on every residual curve. -/
theorem p2_producer_forces_residual_defect_zero
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (hP2 : P2MaterialTarget M S) :
    ∀ E : EllipticCurveQ, S.residual E →
      MCore.BSD.refinedDefect (M.refinedData E) = 0 := by
  rcases hP2 with ⟨P⟩
  intro E hResidual
  exact
    (MCore.BSD.refinedIdentity_iff_defect_eq_zero
      (M.refinedData E)).1
      (P.proof E hResidual)

/-- With positive torsion, one residual quotient mismatch refutes P2. -/
theorem p2_obstruction_of_residual_quotient_mismatch
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    {E : EllipticCurveQ}
    (hResidual : S.residual E)
    (hTor : 0 < (M.refinedData E).torsionOrder)
    (hMismatch :
      (M.refinedData E).leadingCoefficient ≠
        MCore.BSD.refinedRHS (M.refinedData E) /
          ((M.refinedData E).torsionOrder : ℝ)^2) :
    ¬ P2MaterialTarget M S := by
  intro hP2
  rcases hP2 with ⟨P⟩
  have hId := P.proof E hResidual
  have hQ :=
    (MCore.BSD.refinedIdentity_iff_quotient
      (M.refinedData E) hTor).1 hId
  exact hMismatch hQ

end P06.BSD.OpenMath
