import P06.BSD.OpenToClosed

namespace P06.BSD

/-!
# BSD dual-endpoint cube through length three

This file separates:

1. the structural OPEN/CLOSED path lattice;
2. the FULL structural state;
3. the material BSD payload required for any scientific closure claim.

No material BSD inhabitant is manufactured here.
-/

/-- Ordered endpoint symbol. -/
inductive BSDEndpointAtom where
  | open
  | closed
  deriving DecidableEq, Repr

abbrev BSDWord := List BSDEndpointAtom

def OPEN_BSD : BSDWord := [.open]
def CLOSED_BSD : BSDWord := [.closed]

def OPEN_OPEN_BSD : BSDWord := [.open, .open]
def OPEN_CLOSED_BSD : BSDWord := [.open, .closed]
def CLOSED_OPEN_BSD : BSDWord := [.closed, .open]
def CLOSED_CLOSED_BSD : BSDWord := [.closed, .closed]

def OPEN_OPEN_OPEN_BSD : BSDWord := [.open, .open, .open]
def OPEN_OPEN_CLOSED_BSD : BSDWord := [.open, .open, .closed]
def OPEN_CLOSED_OPEN_BSD : BSDWord := [.open, .closed, .open]
def OPEN_CLOSED_CLOSED_BSD : BSDWord := [.open, .closed, .closed]
def CLOSED_OPEN_OPEN_BSD : BSDWord := [.closed, .open, .open]
def CLOSED_OPEN_CLOSED_BSD : BSDWord := [.closed, .open, .closed]
def CLOSED_CLOSED_OPEN_BSD : BSDWord := [.closed, .closed, .open]
def CLOSED_CLOSED_CLOSED_BSD : BSDWord := [.closed, .closed, .closed]

def FULL_BSD : BSDWord := [.open, .open, .closed, .closed]

theorem OPEN_BSD_ne_CLOSED_BSD :
    OPEN_BSD ≠ CLOSED_BSD := by
  decide

theorem OPEN_CLOSED_BSD_ne_CLOSED_OPEN_BSD :
    OPEN_CLOSED_BSD ≠ CLOSED_OPEN_BSD := by
  decide

theorem OPEN_OPEN_BSD_defined :
    OPEN_OPEN_BSD = [.open, .open] := rfl

theorem CLOSED_CLOSED_BSD_defined :
    CLOSED_CLOSED_BSD = [.closed, .closed] := rfl

theorem OPEN_OPEN_OPEN_BSD_defined :
    OPEN_OPEN_OPEN_BSD = [.open, .open, .open] := rfl

theorem CLOSED_CLOSED_CLOSED_BSD_defined :
    CLOSED_CLOSED_CLOSED_BSD = [.closed, .closed, .closed] := rfl

theorem OPEN_OPEN_CLOSED_BSD_defined :
    OPEN_OPEN_CLOSED_BSD = [.open, .open, .closed] := rfl

theorem OPEN_CLOSED_OPEN_BSD_defined :
    OPEN_CLOSED_OPEN_BSD = [.open, .closed, .open] := rfl

theorem CLOSED_OPEN_OPEN_BSD_defined :
    CLOSED_OPEN_OPEN_BSD = [.closed, .open, .open] := rfl

theorem OPEN_CLOSED_CLOSED_BSD_defined :
    OPEN_CLOSED_CLOSED_BSD = [.open, .closed, .closed] := rfl

theorem CLOSED_OPEN_CLOSED_BSD_defined :
    CLOSED_OPEN_CLOSED_BSD = [.closed, .open, .closed] := rfl

theorem CLOSED_CLOSED_OPEN_BSD_defined :
    CLOSED_CLOSED_OPEN_BSD = [.closed, .closed, .open] := rfl

def BSDCubeUpToThree : List BSDWord :=
  [OPEN_BSD, CLOSED_BSD,
   OPEN_OPEN_BSD, OPEN_CLOSED_BSD, CLOSED_OPEN_BSD, CLOSED_CLOSED_BSD,
   OPEN_OPEN_OPEN_BSD, OPEN_OPEN_CLOSED_BSD, OPEN_CLOSED_OPEN_BSD,
   OPEN_CLOSED_CLOSED_BSD, CLOSED_OPEN_OPEN_BSD, CLOSED_OPEN_CLOSED_BSD,
   CLOSED_CLOSED_OPEN_BSD, CLOSED_CLOSED_CLOSED_BSD]

theorem BSDCubeUpToThree_count :
    BSDCubeUpToThree.length = 14 := by
  rfl

/--
Structural dual state: the OPEN and CLOSED views are distinct, but preserve the
same scientific endpoint proposition.
-/
structure BSDDualEndpointState
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop where
  endpointsDistinct : MathView.open ≠ MathView.closed
  openEndpoint : ViewPayload .open G refined
  closedEndpoint : ViewPayload .closed G refined
  identityPreserved :
    ViewPayload .open G refined ↔ ViewPayload .closed G refined

theorem bsd_dual_endpoint_from_material_endpoint
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    (h : Endpoint G refined) :
    BSDDualEndpointState G refined := by
  exact {
    endpointsDistinct := openView_ne_closedView
    openEndpoint := h
    closedEndpoint := h
    identityPreserved := open_closed_payload_equivalent G refined
  }

theorem bsd_dual_endpoint_projects_open
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    (h : BSDDualEndpointState G refined) :
    ViewPayload .open G refined :=
  h.openEndpoint

theorem bsd_dual_endpoint_projects_closed
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    (h : BSDDualEndpointState G refined) :
    ViewPayload .closed G refined :=
  h.closedEndpoint

/--
FULL is a structural lattice definition. It is not a BSD theorem and does not
construct the scientific endpoint.
-/
def FULL_BSD_State
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  BSDDualEndpointState G refined

def GLOBAL_EXTERNAL_CERTIFICATE_BSD
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  FULL_BSD_State G refined

theorem FULL_BSD_eq_GLOBAL_EXTERNAL_CERTIFICATE
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData) :
    FULL_BSD_State G refined ↔
      GLOBAL_EXTERNAL_CERTIFICATE_BSD G refined := by
  rfl

/-- Explicit material finiteness leaf, supplied externally until proved. -/
def UniversalTateShafarevichFinite
    (ShaFinite : EllipticCurveQ → Prop) : Prop :=
  ∀ E : EllipticCurveQ, ShaFinite E

/--
Material BSD payload contract.
The three fields must be independently supplied; this structure does not prove
any of them.
-/
structure BSDMaterialPayload
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData)
    (ShaFinite : EllipticCurveQ → Prop) : Prop where
  regulator_formula : UniversalRefinedBSDIdentity refined
  proof_rank_eq_analytic_rank : UniversalRealizedRankEquality G
  proof_Tate_Shafarevich_finite :
    UniversalTateShafarevichFinite ShaFinite

/-- The material payload projects the exact existing scientific endpoint. -/
theorem bsdPayload_implies_scientificEndpoint
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    {ShaFinite : EllipticCurveQ → Prop}
    (p : BSDMaterialPayload G refined ShaFinite) :
    ScientificEndpoint G refined := by
  exact ⟨p.proof_rank_eq_analytic_rank, p.regulator_formula⟩

/-- Hence a supplied material payload reaches the existing FINAL_ROOT. -/
theorem bsdPayload_implies_finalRoot
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    {ShaFinite : EllipticCurveQ → Prop}
    (p : BSDMaterialPayload G refined ShaFinite) :
    BSDTerminal (fullyRealizedBSDModel G refined) := by
  exact (mathematicalEndpoint_eq_finalRoot G refined).1
    (bsdPayload_implies_scientificEndpoint p)

/--
Final closure is conditional on a real BSDMaterialPayload. FULL_BSD alone is
only the structural lattice state and cannot produce this theorem.
-/
structure BSDFinalClosureCertificate
    (G : AnalyticGermFamily)
    (refined : EllipticCurveQ → BSDRefinedData)
    (ShaFinite : EllipticCurveQ → Prop) : Prop where
  payload : BSDMaterialPayload G refined ShaFinite
  full : FULL_BSD_State G refined
  finalRoot : BSDTerminal (fullyRealizedBSDModel G refined)

def bsd_final_closure
    {G : AnalyticGermFamily}
    {refined : EllipticCurveQ → BSDRefinedData}
    {ShaFinite : EllipticCurveQ → Prop}
    (payload : BSDMaterialPayload G refined ShaFinite) :
    BSDFinalClosureCertificate G refined ShaFinite where
  payload := payload
  full := bsd_dual_endpoint_from_material_endpoint
    (bsdPayload_implies_scientificEndpoint payload)
  finalRoot := bsdPayload_implies_finalRoot payload

#print axioms P06.BSD.BSDCubeUpToThree_count
#print axioms P06.BSD.OPEN_BSD_ne_CLOSED_BSD
#print axioms P06.BSD.FULL_BSD_eq_GLOBAL_EXTERNAL_CERTIFICATE
#print axioms P06.BSD.bsdPayload_implies_scientificEndpoint
#print axioms P06.BSD.bsdPayload_implies_finalRoot
#print axioms P06.BSD.bsd_final_closure

end P06.BSD
