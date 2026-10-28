import MCore.BSDConstructionFrontier

namespace MCore

/-- Structural layers that a complete BSD resolution mechanism must expose.
The fields are interfaces for the mathematical constructions; no inhabitant is
asserted by this file. -/
structure BSDSelmerLayer (Curve : Type) where
  selmerObject : Curve → Type
  shaObject : Curve → Type
  rankBound : Curve → Nat
  finiteSha : Curve → Prop

structure BSDHeightLayer (Curve Scalar : Type) where
  heightPairing : Curve → Scalar
  regulatorFromHeight : Curve → Scalar
  regulatorLaw : Curve → Prop

structure BSDLocalLayer (Curve Scalar : Type) where
  period : Curve → Scalar
  tamagawa : Curve → Scalar
  torsionOrder : Curve → Nat
  localCompatibility : Curve → Prop

structure BSDAnalyticLayer (Curve Scalar : Type) where
  analyticRank : Curve → Nat
  leadingCoefficient : Curve → Scalar
  continuationCompatible : Curve → Prop
  functionalEquationCompatible : Curve → Prop

/-- Comparison layer: the genuine bridge of a hypothetical complete proof.
It links independently specified analytic, Selmer, height and local data. -/
structure BSDComparisonLayer
    (Curve Scalar : Type)
    (S : BSDSelmerLayer Curve)
    (H : BSDHeightLayer Curve Scalar)
    (L : BSDLocalLayer Curve Scalar)
    (A : BSDAnalyticLayer Curve Scalar) where
  algebraicRank : Curve → Nat
  rankComparison : ∀ E, A.analyticRank E = algebraicRank E
  shaCardinality : Curve → Nat
  shaPositive : ∀ E, 0 < shaCardinality E
  selmerRankCompatibility : ∀ E, S.rankBound E = algebraicRank E
  heightCompatibility : ∀ E, H.regulatorLaw E
  localCompatibility : ∀ E, L.localCompatibility E

/-- Full hypothetical resolution mechanism.
Unlike GroundedBSDHabitant, this records the internal decomposition that
produces its state. -/
structure BSDResolutionMechanism (Curve Scalar : Type) where
  algebra : BSDScalarAlgebra Scalar
  selmer : BSDSelmerLayer Curve
  height : BSDHeightLayer Curve Scalar
  local : BSDLocalLayer Curve Scalar
  analytic : BSDAnalyticLayer Curve Scalar
  compare : BSDComparisonLayer Curve Scalar selmer height local analytic

  arithmeticState : Curve → GroundedBSDState Curve Scalar

  stateCurve : ∀ E, (arithmeticState E).curve = E
  stateRank : ∀ E, (arithmeticState E).algebraicRank = compare.algebraicRank E
  stateAnalyticRank : ∀ E,
    (arithmeticState E).analyticOrderAtOne = analytic.analyticRank E
  stateLeading : ∀ E,
    (arithmeticState E).leadingCoefficient = analytic.leadingCoefficient E
  statePeriod : ∀ E, (arithmeticState E).realPeriod = local.period E
  stateRegulator : ∀ E,
    (arithmeticState E).regulator = height.regulatorFromHeight E
  stateTamagawa : ∀ E,
    (arithmeticState E).tamagawaProduct = local.tamagawa E
  stateSha : ∀ E, (arithmeticState E).shaOrder = compare.shaCardinality E
  stateTorsion : ∀ E, (arithmeticState E).torsionOrder = local.torsionOrder E

  /-- Determinant / refined-BSD law produced by the comparison mechanism. -/
  determinantLaw : ∀ E,
    analytic.leadingCoefficient E =
      bsdArithmeticSide algebra (arithmeticState E)

/-- A complete mechanism deterministically yields the earlier output contract. -/
def BSDResolutionMechanism.toGroundedBSDHabitant
    {Curve Scalar : Type}
    (M : BSDResolutionMechanism Curve Scalar) :
    GroundedBSDHabitant Curve Scalar :=
  { algebra := M.algebra
    state := M.arithmeticState
    sameCurve := M.stateCurve
    rankLaw := by
      intro E
      calc
        (M.arithmeticState E).analyticOrderAtOne
            = M.analytic.analyticRank E := M.stateAnalyticRank E
        _ = M.compare.algebraicRank E := M.compare.rankComparison E
        _ = (M.arithmeticState E).algebraicRank := (M.stateRank E).symm
    shaFiniteWitness := by
      intro E
      rw [M.stateSha E]
      exact M.compare.shaPositive E
    leadingLaw := by
      intro E
      calc
        (M.arithmeticState E).leadingCoefficient
            = M.analytic.leadingCoefficient E := M.stateLeading E
        _ = bsdArithmeticSide M.algebra (M.arithmeticState E) :=
          M.determinantLaw E }

/-- Therefore a supplied resolution mechanism closes the old rank interface. -/
theorem resolutionMechanism_closes_rank
    {Curve Scalar : Type}
    (M : BSDResolutionMechanism Curve Scalar)
    (E : Curve) :
    BSDOpenCore
      (((M.toGroundedBSDHabitant).state E).toArithmeticAnalyticData) :=
  groundedHabitant_closes_rank_interface M.toGroundedBSDHabitant E

/-- It also produces the refined leading-coefficient identity. -/
theorem resolutionMechanism_closes_leading
    {Curve Scalar : Type}
    (M : BSDResolutionMechanism Curve Scalar)
    (E : Curve) :
    ((M.toGroundedBSDHabitant).state E).leadingCoefficient =
      bsdArithmeticSide
        (M.toGroundedBSDHabitant).algebra
        ((M.toGroundedBSDHabitant).state E) :=
  (M.toGroundedBSDHabitant).leadingLaw E

/-- Mathematical frontier: existence of this mechanism is precisely the
unproved object at this abstraction level. -/
def bsdResolutionMechanismRequired (Curve Scalar : Type) : Prop :=
  Nonempty (BSDResolutionMechanism Curve Scalar)

def bsd_resolution_mechanism_node (Curve Scalar : Type) : CertNode :=
  { status := .openBridge
    statement := bsdResolutionMechanismRequired Curve Scalar }

theorem bsd_resolution_mechanism_node_open (Curve Scalar : Type) :
    (bsd_resolution_mechanism_node Curve Scalar).status = .openBridge := rfl

theorem bsd_resolution_mechanism_not_false_certified (Curve Scalar : Type) :
    ¬ Nonempty (ProofCertificate (bsd_resolution_mechanism_node Curve Scalar)) := by
  intro h
  rcases h with ⟨c⟩
  cases c.status_proved

end MCore
