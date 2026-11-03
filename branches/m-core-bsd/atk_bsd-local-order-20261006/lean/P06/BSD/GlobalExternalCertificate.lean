import P06.BSD.DualEndpointCube
import P06.BSD.ClosedMath

namespace P06.BSD

/-!
# BSD global external certificate

This aggregate is deliberately split into two layers:

* structural certificate: inhabited from already-proved equivalences, guards and
  finite endpoint-word structure;
* material certificate: requires an explicit BSDMaterialPayload and therefore
  cannot be manufactured by the structural layer.

The file is the canonical shortest path for external/kernel audit.
-/

/-- Everything structurally established without assuming the BSD endpoint. -/
structure BSDGlobalExternalStructuralCertificate : Prop where
  closedMath : ClosedMathStructuralCertificate
  cubeCount : BSDCubeUpToThree.length = 14
  openClosedWordsDistinct : OPEN_BSD ≠ CLOSED_BSD
  openClosedViewsDistinct : MathView.open ≠ MathView.closed
  viewPayloadIdentity :
    ∀ (G : AnalyticGermFamily) (refined : EllipticCurveQ → BSDRefinedData),
      ViewPayload .open G refined ↔ ViewPayload .closed G refined
  openToClosedIdentity :
    ∀ (G : AnalyticGermFamily) (refined : EllipticCurveQ → BSDRefinedData),
      ViewPayload .open G refined ↔ ViewPayload .closed G refined
  finalRootExact :
    ∀ (G : AnalyticGermFamily) (refined : EllipticCurveQ → BSDRefinedData),
      BSDTerminal (fullyRealizedBSDModel G refined) ↔
        UniversalRealizedRankEquality G ∧
        UniversalRefinedBSDIdentity refined
  structuralLeavesClosed : remainingStructuralLeafCount = 0
  scientificLeavesRemain : remainingScientificLeafCount = 2

/-- Canonical structural inhabitant. This does not inhabit the BSD endpoint. -/
def bsdGlobalExternalStructuralCertificate :
    BSDGlobalExternalStructuralCertificate where
  closedMath := closedMathStructuralCertificate
  cubeCount := BSDCubeUpToThree_count
  openClosedWordsDistinct := OPEN_BSD_ne_CLOSED_BSD
  openClosedViewsDistinct := openView_ne_closedView
  viewPayloadIdentity := open_closed_payload_equivalent
  openToClosedIdentity := open_tends_closed_same_endpoint
  finalRootExact := finalRoot_iff_scientificFrontier
  structuralLeavesClosed := rfl
  scientificLeavesRemain := rfl

theorem global_external_structural_certified :
    Nonempty BSDGlobalExternalStructuralCertificate :=
  ⟨bsdGlobalExternalStructuralCertificate⟩

/--
Fail-closed material boundary: FULL/GLOBAL material state is exactly the
endpoint-carrying dual state. This theorem is an equivalence only; it does not
construct that state.
-/
theorem global_material_state_iff_dual_endpoint
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    GLOBAL_EXTERNAL_CERTIFICATE_BSD G refined ↔
      BSDDualEndpointState G refined := by
  rfl

/-- A real material payload is sufficient for the material global state. -/
theorem payload_implies_global_material_state
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    {ShaFinite : EllipticCurveQ → Prop}
    (p : BSDMaterialPayload G refined ShaFinite) :
    GLOBAL_EXTERNAL_CERTIFICATE_BSD G refined := by
  exact bsd_dual_endpoint_from_material_endpoint
    (bsdPayload_implies_scientificEndpoint p)

/--
A real material payload gives the final closure certificate. The premise is
kept explicit so the structural certificate cannot promote itself.
-/
theorem payload_implies_global_final_certificate
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    {ShaFinite : EllipticCurveQ → Prop}
    (p : BSDMaterialPayload G refined ShaFinite) :
    BSDFinalClosureCertificate G refined ShaFinite :=
  bsd_final_closure p

#print axioms P06.BSD.global_external_structural_certified
#print axioms P06.BSD.global_material_state_iff_dual_endpoint
#print axioms P06.BSD.payload_implies_global_material_state
#print axioms P06.BSD.payload_implies_global_final_certificate

end P06.BSD
