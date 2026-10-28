import P06.BSD.Frontier

namespace P06.BSD.OpenMath

/-
Legacy P1 residual boundary rewritten fail-closed.

The residual proposition is named but not inhabited.  Universal P1 is recovered
only when both the known-subdomain certificate and a genuine residual producer
are supplied.
-/

variable (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain)

/-- Exact remaining P1 obligation on the literal residual. -/
abbrev BSDP1ResidualOpenMath : Prop :=
  Nonempty (RankOnResidual M S)

/-- Conditional reconstruction of universal P1. -/
theorem bsd_p1_from_known_and_residual
    (hKnown : Nonempty (RankOnSubdomain M S))
    (hResidual : BSDP1ResidualOpenMath M S) :
    BSDP1 M :=
  (p1_frontier_exact (M := M) (S := S)).2
    ⟨hKnown, hResidual⟩

#check BSDP1ResidualOpenMath
#check bsd_p1_from_known_and_residual

end P06.BSD.OpenMath
