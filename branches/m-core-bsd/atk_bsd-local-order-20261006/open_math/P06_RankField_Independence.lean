import open_math.P06_Rank0_Exclusion

namespace P06.BSD.OpenMath

/-
Rank-field independence audit.

This file proves that the present ConcreteBSDModel interface leaves
mordellWeilRank independent of both analyticOrderAtOne and refinedData.

Therefore no theorem using only the latter two fields can force the rank-zero
material statement.  The missing mathematical object is specifically a
realization of mordellWeilRank by genuine elliptic-curve arithmetic.
-/

/-- Replace only the Mordell-Weil-rank field of a concrete model. -/
def withMordellWeilRank
    (M : ConcreteBSDModel)
    (r : EllipticCurveQ → Nat) :
    ConcreteBSDModel where
  mordellWeilRank := r
  analyticOrderAtOne := M.analyticOrderAtOne
  refinedData := M.refinedData

@[simp] theorem withMordellWeilRank_analytic
    (M : ConcreteBSDModel) (r : EllipticCurveQ → Nat) (E : EllipticCurveQ) :
    (withMordellWeilRank M r).analyticOrderAtOne E =
      M.analyticOrderAtOne E := rfl

@[simp] theorem withMordellWeilRank_refined
    (M : ConcreteBSDModel) (r : EllipticCurveQ → Nat) (E : EllipticCurveQ) :
    (withMordellWeilRank M r).refinedData E =
      M.refinedData E := rfl

@[simp] theorem withMordellWeilRank_rank
    (M : ConcreteBSDModel) (r : EllipticCurveQ → Nat) (E : EllipticCurveQ) :
    (withMordellWeilRank M r).mordellWeilRank E = r E := rfl

/-- If M has even one analytic-rank-zero curve E, changing only the independent
rank field to the constant value 1 manufactures a rank-zero counterexample
without changing analyticOrderAtOne or refinedData. -/
def counterexampleByRankMutation
    {M : ConcreteBSDModel} {E : EllipticCurveQ}
    (hE : M.analyticOrderAtOne E = 0) :
    Rank0Counterexample (withMordellWeilRank M (fun _ => 1)) where
  curve := E
  analytic_zero := by
    simpa using hE
  arithmetic_positive := by
    norm_num

/-- Pointed version of the independence obstruction. -/
theorem rank_field_independence_at_analytic_zero
    {M : ConcreteBSDModel} {E : EllipticCurveQ}
    (hE : M.analyticOrderAtOne E = 0) :
    ¬ Rank0ArithmeticMaterial
      (withMordellWeilRank M (fun _ => 1)) := by
  exact rank0_counterexample_refutes_material
    (counterexampleByRankMutation hE)

/-- Global min-cut statement: whenever the analytic-zero subdomain is nonempty,
the current model API admits another model with exactly the same analytic and
refined data but for which rank-zero material fails. -/
theorem same_analytic_refined_data_do_not_force_rank0
    (M : ConcreteBSDModel)
    (hZero : ∃ E : EllipticCurveQ, M.analyticOrderAtOne E = 0) :
    ∃ M' : ConcreteBSDModel,
      (∀ E, M'.analyticOrderAtOne E = M.analyticOrderAtOne E) ∧
      (∀ E, M'.refinedData E = M.refinedData E) ∧
      ¬ Rank0ArithmeticMaterial M' := by
  rcases hZero with ⟨E0, hE0⟩
  refine ⟨withMordellWeilRank M (fun _ => 1), ?_, ?_, ?_⟩
  · intro E
    rfl
  · intro E
    rfl
  · exact rank_field_independence_at_analytic_zero hE0

#check withMordellWeilRank
#check counterexampleByRankMutation
#check rank_field_independence_at_analytic_zero
#check same_analytic_refined_data_do_not_force_rank0

end P06.BSD.OpenMath
