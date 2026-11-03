import MCore.BSD.GroundedBSDHabitant

namespace MCore

/-- Kernel target for the Mordell-Weil side of F5 on the current carrier. -/
structure BSDMordellWeilRankKernelPackage : Type where
  semantics : BSDRankSemanticAnchor
  specification : BSDRankGroundingSpecification
  rankGrounded :
    ∀ E : ShortWeierstrassCurveQ,
      specification.mordellWeilRankSpec E (semantics.mordellWeilRank E)

def BSDMordellWeilRankKernelTarget : Prop :=
  Nonempty BSDMordellWeilRankKernelPackage

def bsdMordellWeilRankKernelAvailable : Bool := false

theorem bsd_mordell_weil_rank_kernel_not_available :
    bsdMordellWeilRankKernelAvailable = false := by
  rfl

#print axioms MCore.bsd_mordell_weil_rank_kernel_not_available

end MCore
