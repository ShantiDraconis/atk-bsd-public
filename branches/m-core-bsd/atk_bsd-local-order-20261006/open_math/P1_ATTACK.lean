import open_math.ForcingKernel

namespace P06.BSD.OpenMath

/-- Toy subdomain with empty known region: every genuine curve is residual. -/
def p1ToySubdomain : CertifiedCurveSubdomain where
  contains := fun _ => False

/-- Toy model deliberately separates analytic order and Mordell-Weil rank.
It demonstrates that the GREEN wiring alone cannot manufacture P1. -/
def p1ToyModel : ConcreteBSDModel where
  mordellWeilRank := fun _ => 0
  analyticOrderAtOne := fun _ => 1
  refinedData := fun _ =>
    { leadingCoefficient := 0
      realPeriod := 0
      regulator := 0
      shaOrder := 1
      tamagawaProduct := 1
      torsionOrder := 1 }

/-- In the toy model every curve lies in the residual. -/
theorem p1_toy_all_residual (E : EllipticCurveQ) :
    p1ToySubdomain.residual E := by
  simp [p1ToySubdomain, MCore.BSD.CertifiedCurveSubdomain.residual]

/-- Exact obstruction exposed by the toy model:
a residual P1 producer would force 1 = 0. -/
theorem p1_toy_no_residual :
    ¬ BSD_P1_Producer p1ToyModel p1ToySubdomain := by
  intro h
  rcases h with ⟨R⟩
  let E := MCore.BSD.positiveControl
  have hEq := R.proof E (p1_toy_all_residual E)
  norm_num [p1ToyModel] at hEq

/-- The exact material P1 target once a specific intended model and known
subdomain have been selected.  No universal inhabitant over arbitrary models is
claimed. -/
abbrev P1MaterialTarget
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  BSD_P1_Producer M S

/-- A toy model where P1 closes, showing that ConcreteBSDModel by itself does
not identify the intended arithmetic semantics. -/
def p1ToyGoodModel : ConcreteBSDModel where
  mordellWeilRank := fun _ => 0
  analyticOrderAtOne := fun _ => 0
  refinedData := fun _ =>
    { leadingCoefficient := 0
      realPeriod := 0
      regulator := 0
      shaOrder := 1
      tamagawaProduct := 1
      torsionOrder := 1 }

theorem p1_toy_good_residual :
    P1MaterialTarget p1ToyGoodModel p1ToySubdomain := by
  exact ⟨{ proof := fun E _ => by rfl }⟩

/-- Therefore no theorem depending only on the bare ConcreteBSDModel interface
can decide P1 uniformly: both success and failure models inhabit that interface. -/
theorem no_uniform_P1 :
    ¬ (∀ M : ConcreteBSDModel, ∀ S : CertifiedCurveSubdomain,
        P1MaterialTarget M S) := by
  intro h
  exact p1_toy_no_residual (h p1ToyModel p1ToySubdomain)

/-- OPEN_MATH target marker.  This is a proposition, not a fabricated proof.
A future attack must instantiate M and S with genuinely interpreted BSD data. -/
def attempt_P1
    (M : ConcreteBSDModel) (S : CertifiedCurveSubdomain) : Prop :=
  P1MaterialTarget M S

end P06.BSD.OpenMath
