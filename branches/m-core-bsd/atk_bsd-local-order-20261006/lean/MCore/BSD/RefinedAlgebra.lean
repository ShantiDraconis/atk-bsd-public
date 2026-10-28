import MCore.BSD.ConcreteDomain
import Mathlib.Tactic

namespace MCore.BSD

/-- Left-hand side of the refined BSD identity. -/
def refinedLHS (d : BSDRefinedData) : ℝ :=
  d.leadingCoefficient * (d.torsionOrder : ℝ)^2

/-- Right-hand side of the refined BSD identity. -/
def refinedRHS (d : BSDRefinedData) : ℝ :=
  d.realPeriod * d.regulator *
    (d.shaOrder : ℝ) * (d.tamagawaProduct : ℝ)

/-- Additive residual of the refined BSD identity. -/
def refinedDefect (d : BSDRefinedData) : ℝ :=
  refinedLHS d - refinedRHS d

theorem refinedIdentity_iff_lhs_eq_rhs (d : BSDRefinedData) :
    RefinedBSDIdentity d ↔ refinedLHS d = refinedRHS d := by
  rfl

theorem refinedIdentity_iff_defect_eq_zero (d : BSDRefinedData) :
    RefinedBSDIdentity d ↔ refinedDefect d = 0 := by
  unfold RefinedBSDIdentity refinedDefect refinedLHS refinedRHS
  constructor <;> intro h
  · linarith
  · linarith

theorem torsion_ne_zero_of_positive {d : BSDRefinedData}
    (h : 0 < d.torsionOrder) :
    (d.torsionOrder : ℝ) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt h

theorem torsion_sq_ne_zero_of_positive {d : BSDRefinedData}
    (h : 0 < d.torsionOrder) :
    (d.torsionOrder : ℝ)^2 ≠ 0 := by
  exact pow_ne_zero 2 (torsion_ne_zero_of_positive h)

/-- Quotient form of refined BSD, valid only after positivity/nonvanishing of
the torsion order has been supplied independently. -/
theorem refinedIdentity_iff_quotient
    (d : BSDRefinedData)
    (hTor : 0 < d.torsionOrder) :
    RefinedBSDIdentity d ↔
      d.leadingCoefficient =
        refinedRHS d / (d.torsionOrder : ℝ)^2 := by
  have hne : (d.torsionOrder : ℝ)^2 ≠ 0 :=
    torsion_sq_ne_zero_of_positive hTor
  unfold RefinedBSDIdentity refinedRHS
  constructor
  · intro h
    apply (eq_div_iff hne).2
    simpa [mul_comm] using h
  · intro h
    have h' := (eq_div_iff hne).1 h
    simpa [mul_comm] using h'

theorem refinedRHS_nonnegative
    (d : BSDRefinedData)
    (hPeriod : 0 ≤ d.realPeriod)
    (hReg : 0 ≤ d.regulator) :
    0 ≤ refinedRHS d := by
  unfold refinedRHS
  positivity

theorem refinedRHS_positive
    (d : BSDRefinedData)
    (hPeriod : 0 < d.realPeriod)
    (hReg : 0 < d.regulator)
    (hSha : 0 < d.shaOrder)
    (hTam : 0 < d.tamagawaProduct) :
    0 < refinedRHS d := by
  unfold refinedRHS
  positivity

/-- If the normalized arithmetic side is positive and refined BSD holds,
the leading coefficient is positive as well. -/
theorem leadingCoefficient_positive_of_identity
    (d : BSDRefinedData)
    (hId : RefinedBSDIdentity d)
    (hTor : 0 < d.torsionOrder)
    (hPeriod : 0 < d.realPeriod)
    (hReg : 0 < d.regulator)
    (hSha : 0 < d.shaOrder)
    (hTam : 0 < d.tamagawaProduct) :
    0 < d.leadingCoefficient := by
  have hR : 0 < refinedRHS d :=
    refinedRHS_positive d hPeriod hReg hSha hTam
  have hq := (refinedIdentity_iff_quotient d hTor).1 hId
  rw [hq]
  positivity

end MCore.BSD
