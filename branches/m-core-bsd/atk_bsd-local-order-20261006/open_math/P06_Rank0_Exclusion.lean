import open_math.P06_Rank0_FrontierAudit
import open_math.ObstructionKernel

namespace P06.BSD.OpenMath

/-
Exact exclusion form of the rank-zero material frontier.

No new invariant is introduced here.  The only data used are the two fields
already present in ConcreteBSDModel:
  analyticOrderAtOne
  mordellWeilRank

The material rank-zero theorem is equivalent to excluding a concrete witness:
a genuine curve with analytic order zero but positive Mordell-Weil rank.
-/

/-- A concrete witness against the rank-zero material statement for M. -/
structure Rank0Counterexample (M : ConcreteBSDModel) where
  curve : EllipticCurveQ
  analytic_zero : M.analyticOrderAtOne curve = 0
  arithmetic_positive : 0 < M.mordellWeilRank curve

/-- Any rank-zero counterexample refutes Rank0ArithmeticMaterial immediately. -/
theorem rank0_counterexample_refutes_material
    {M : ConcreteBSDModel}
    (C : Rank0Counterexample M) :
    ¬ Rank0ArithmeticMaterial M := by
  intro h
  have hZero : M.mordellWeilRank C.curve = 0 :=
    h C.curve C.analytic_zero
  exact (Nat.ne_of_gt C.arithmetic_positive) hZero

/-- Conversely, failure of Rank0ArithmeticMaterial produces a concrete curve
with analytic order zero and positive Mordell-Weil rank. -/
theorem not_material_produces_rank0_counterexample
    {M : ConcreteBSDModel}
    (h : ¬ Rank0ArithmeticMaterial M) :
    Nonempty (Rank0Counterexample M) := by
  unfold Rank0ArithmeticMaterial at h
  push_neg at h
  rcases h with ⟨E, hAnalytic, hRankNe⟩
  exact ⟨
    { curve := E
      analytic_zero := hAnalytic
      arithmetic_positive := Nat.pos_of_ne_zero hRankNe }⟩

/-- Exact material cut: rank-zero closure is equivalent to exclusion of every
analytic-zero / positive-arithmetic-rank witness. -/
theorem rank0_material_iff_no_counterexample
    {M : ConcreteBSDModel} :
    Rank0ArithmeticMaterial M ↔
      ¬ Nonempty (Rank0Counterexample M) := by
  constructor
  · intro hMat hC
    rcases hC with ⟨C⟩
    exact rank0_counterexample_refutes_material C hMat
  · intro hNo
    by_contra hMat
    exact hNo (not_material_produces_rank0_counterexample hMat)

/-- Equivalent pointwise exclusion form, useful for direct mining/attack. -/
theorem rank0_material_iff_no_positive_rank_at_zero
    {M : ConcreteBSDModel} :
    Rank0ArithmeticMaterial M ↔
      ∀ E : EllipticCurveQ,
        M.analyticOrderAtOne E = 0 →
        ¬ 0 < M.mordellWeilRank E := by
  constructor
  · intro h E hA hPos
    have hZero := h E hA
    exact (Nat.ne_of_gt hPos) hZero
  · intro h E hA
    exact Nat.eq_zero_of_not_pos (h E hA)

/-- The toy model from the frontier audit gives an explicit inhabitant of the
counterexample type, explaining exactly why arbitrary ConcreteBSDModel cannot
support universal rank-zero closure. -/
def rank0ToyCounterexample : Rank0Counterexample rank0ToyModel where
  curve := MCore.BSD.positiveControl
  analytic_zero := rfl
  arithmetic_positive := by
    norm_num [rank0ToyModel]

theorem rank0_toy_counterexample_nonempty :
    Nonempty (Rank0Counterexample rank0ToyModel) :=
  ⟨rank0ToyCounterexample⟩

#check Rank0Counterexample
#check rank0_counterexample_refutes_material
#check not_material_produces_rank0_counterexample
#check rank0_material_iff_no_counterexample
#check rank0_material_iff_no_positive_rank_at_zero
#check rank0ToyCounterexample

end P06.BSD.OpenMath
