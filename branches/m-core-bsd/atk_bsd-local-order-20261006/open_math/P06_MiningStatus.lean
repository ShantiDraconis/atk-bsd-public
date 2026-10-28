import open_math.P1_ATTACK
import open_math.P2_TORSION_ATTACK

namespace P06.BSD.OpenMath

/-
P06 BSD mining status.

Frozen source of truth:
  a3edf6209a143db063939ada57869b41e49a708f

The frozen layer already supplies the structural/wiring machinery:
  * RankOnSubdomain / RefinedOnSubdomain
  * union closure for certified subdomains
  * p1_frontier_exact / p2_frontier_exact
  * terminal_from_partition

This file does not add a producer, model field, axiom, or theorem of BSD.
It only names the remaining material obligations exposed by the forcing attack.

Top-level OPEN_MATH:
  P1: residual rank equality
  P2: residual refined identity

Material leaves:
  (1) P1 rank_eq_residual
  (2) P2 torsion_pos
  (3) P2 quotient_id
-/

/-- Material P1 leaf: rank equality on the exact residual complement. -/
def P1RankResidualObligation
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  ∀ E : EllipticCurveQ, S.residual E →
    M.analyticOrderAtOne E = M.mordellWeilRank E

/-- Material P2 leaf 1: positivity of the torsion-order field on the residual.
This is intentionally about `M.refinedData E`; it is not inferred from the
geometric torsion group of `E`. -/
def P2TorsionPositiveObligation
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  ∀ E : EllipticCurveQ, S.residual E →
    0 < (M.refinedData E).torsionOrder

/-- Material P2 leaf 2: quotient-normalized refined BSD identity on the residual. -/
def P2QuotientIdentityObligation
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  ∀ E : EllipticCurveQ, S.residual E →
    (M.refinedData E).leadingCoefficient =
      MCore.BSD.refinedRHS (M.refinedData E) /
        ((M.refinedData E).torsionOrder : ℝ)^2

/-- Audit: the named P1 material leaf is exactly the residual P1 producer. -/
theorem p1_material_obligation_iff_producer
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain} :
    P1RankResidualObligation M S ↔ BSD_P1_Producer M S := by
  constructor
  · intro h
    exact ⟨{ proof := h }⟩
  · rintro ⟨R⟩
    exact R.proof

/-- Audit: once the two material P2 leaves are supplied, the existing quotient
transport closes the residual P2 producer mechanically. -/
theorem p2_material_obligations_suffice
    {M : ConcreteBSDModel} {S : CertifiedCurveSubdomain}
    (hTor : P2TorsionPositiveObligation M S)
    (hQuot : P2QuotientIdentityObligation M S) :
    BSD_P2_Producer M S := by
  refine ⟨p2_of_quotient_family ?_⟩
  intro E hE
  exact
    { residual := hE
      torsionPositive := hTor E hE
      quotientIdentity := hQuot E hE }

/-
Mining rule from here forward:
  if S and T are already certified GREEN subdomains, use only the frozen
  union laws to enlarge KNOWN(S) to KNOWN(S ∪ T).  The residual then shrinks.
  No additional forcing kernel or structural scaffold belongs in this lane.
-/

#check P1RankResidualObligation
#check P2TorsionPositiveObligation
#check P2QuotientIdentityObligation
#check p1_material_obligation_iff_producer
#check p2_material_obligations_suffice
#check MCore.BSD.RankOnSubdomain.union
#check MCore.BSD.RefinedOnSubdomain.union
#check P06.BSD.terminal_from_partition

end P06.BSD.OpenMath
