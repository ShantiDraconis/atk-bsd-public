import MCore.BSDCompositeCertificate

namespace MCore

/-- Explicit construction frontier.  These are construction obligations,
not assertions that the corresponding mathematics is already known. -/
structure BSDConstructionFrontier (Curve Scalar : Type) where
  habitant : Prop := groundedBSDHabitantRequired Curve Scalar
  heightProducer : Prop
  normalizationCompatibility : Prop
  universalCurveCoverage : Prop

/-- A producer may only be promoted when all construction obligations are
supplied together. -/
structure BSDPromotionWitness (Curve Scalar : Type)
    (F : BSDConstructionFrontier Curve Scalar) where
  habitant : F.habitant
  heightProducer : F.heightProducer
  normalizationCompatibility : F.normalizationCompatibility
  universalCurveCoverage : F.universalCurveCoverage

def bsd_habitant_node (Curve Scalar : Type) : CertNode :=
  { status := .openBridge
    statement := groundedBSDHabitantRequired Curve Scalar }

def bsd_universal_certificate_node (Curve Scalar : Type) : CertNode :=
  { status := .openBridge
    statement := Nonempty (BSDUniversalCertificate Curve Scalar) }

theorem bsd_habitant_node_open (Curve Scalar : Type) :
    (bsd_habitant_node Curve Scalar).status = .openBridge := rfl

theorem bsd_universal_certificate_node_open (Curve Scalar : Type) :
    (bsd_universal_certificate_node Curve Scalar).status = .openBridge := rfl

theorem bsd_habitant_not_false_certified (Curve Scalar : Type) :
    ¬ Nonempty (ProofCertificate (bsd_habitant_node Curve Scalar)) := by
  intro h
  rcases h with ⟨c⟩
  cases c.status_proved

theorem bsd_universal_not_false_certified (Curve Scalar : Type) :
    ¬ Nonempty (ProofCertificate (bsd_universal_certificate_node Curve Scalar)) := by
  intro h
  rcases h with ⟨c⟩
  cases c.status_proved

end MCore
