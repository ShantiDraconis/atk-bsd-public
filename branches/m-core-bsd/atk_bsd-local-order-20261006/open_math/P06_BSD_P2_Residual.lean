import P06.BSD.Frontier

namespace P06.BSD.OpenMath

/-
Legacy P2 residual boundary rewritten fail-closed.

The refined residual is named but not inhabited.  Universal P2 is recovered
only from an existing known-subdomain proof plus a genuine residual producer.
-/

variable (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain)

/-- Exact remaining P2 obligation on the literal residual. -/
abbrev BSDP2ResidualOpenMath : Prop :=
  Nonempty (RefinedOnResidual M S)

/-- Conditional reconstruction of universal P2. -/
theorem bsd_p2_from_known_and_residual
    (hKnown : Nonempty (RefinedOnSubdomain M S))
    (hResidual : BSDP2ResidualOpenMath M S) :
    BSDP2 M :=
  (p2_frontier_exact (M := M) (S := S)).2
    ⟨hKnown, hResidual⟩

#check BSDP2ResidualOpenMath
#check bsd_p2_from_known_and_residual

end P06.BSD.OpenMath
