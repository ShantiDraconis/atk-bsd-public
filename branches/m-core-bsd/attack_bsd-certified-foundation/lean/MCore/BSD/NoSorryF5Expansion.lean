import MCore.BSD.GroundedBSDHabitant

namespace MCore

inductive ExternalBSDReuseStatus where
  | rejectedSorry
  | rejectedAxiom
  | rejectedPlaceholder
  | reusableDefinitionOnly
deriving DecidableEq, Repr

/--
Audit result for the historical classical BSD repository.

The algebraic rank file contains:
- axiomatized Mordell-Weil/torsion facts;
- algebraicRank := 0 placeholder;
- incomplete proof characterizations.

The analytic rank/L-function chain contains non-kernel external dependencies.

Therefore none of those proof terms may inhabit GroundedBSDHabitant.
-/
def externalClassicalBSDProofReuseStatus : ExternalBSDReuseStatus :=
  .rejectedSorry

def externalClassicalBSDAlgebraicRankStatus : ExternalBSDReuseStatus :=
  .rejectedPlaceholder

def externalClassicalBSDKnownCaseStatus : ExternalBSDReuseStatus :=
  .rejectedAxiom

theorem external_classical_bsd_proof_reuse_rejected :
    externalClassicalBSDProofReuseStatus = .rejectedSorry := by
  rfl

theorem external_classical_bsd_algebraic_rank_rejected :
    externalClassicalBSDAlgebraicRankStatus = .rejectedPlaceholder := by
  rfl

theorem external_classical_bsd_known_cases_rejected :
    externalClassicalBSDKnownCaseStatus = .rejectedAxiom := by
  rfl

/--
Kernel-clean expansion of the missing work.

Instead of a placeholder theorem, the exact kernel target is a structure whose
fields are the three independent obligations:
1. grounded analytic-order semantics;
2. grounded Mordell-Weil-rank semantics;
3. equality of those exact values for the same curve.
-/
structure BSDNoSorryKernelCertificate : Type where
  semantics : BSDRankSemanticAnchor
  grounding : BSDCanonicalRankGrounding semantics
  rankEquality : ∀ E : ShortWeierstrassCurveQ,
    semantics.analyticOrderAtOne E = semantics.mordellWeilRank E

def BSDNoSorryKernelTarget : Prop :=
  Nonempty BSDNoSorryKernelCertificate

def BSDNoSorryKernelCertificate.toGroundedHabitant
    (C : BSDNoSorryKernelCertificate) : GroundedBSDHabitant :=
  { semantics := C.semantics
    grounding := C.grounding
    rank_eq := C.rankEquality }

theorem no_sorry_kernel_target_closes_f5
    (H : BSDNoSorryKernelTarget) :
    GroundedBSDRankDefectVanishing := by
  rcases H with ⟨C⟩
  exact ⟨C.toGroundedHabitant⟩

def bsdNoSorryMaterialProducerCount : Nat := 1

theorem bsd_no_sorry_material_producer_count_one :
    bsdNoSorryMaterialProducerCount = 1 := by
  rfl

#print axioms MCore.external_classical_bsd_proof_reuse_rejected
#print axioms MCore.external_classical_bsd_algebraic_rank_rejected
#print axioms MCore.external_classical_bsd_known_cases_rejected
#print axioms MCore.no_sorry_kernel_target_closes_f5
#print axioms MCore.bsd_no_sorry_material_producer_count_one

end MCore
