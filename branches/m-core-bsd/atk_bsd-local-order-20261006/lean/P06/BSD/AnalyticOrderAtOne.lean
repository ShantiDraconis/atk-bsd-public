import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

namespace P06.BSD

structure FiniteAnalyticGermAtOne where
  L : ℂ → ℂ
  analyticAtOne : AnalyticAt ℂ L (1 : ℂ)
  orderFinite : analyticAtOne.order ≠ ⊤

noncomputable def analyticRankAtOne (D : FiniteAnalyticGermAtOne) : ℕ :=
  D.analyticAtOne.order.toNat

theorem analyticRankAtOne_coe_order
    (D : FiniteAnalyticGermAtOne) :
    (analyticRankAtOne D : ENat) = D.analyticAtOne.order := by
  exact ENat.coe_toNat D.orderFinite

theorem analyticRankAtOne_eq_zero_iff
    (D : FiniteAnalyticGermAtOne) :
    analyticRankAtOne D = 0 ↔ D.L 1 ≠ 0 := by
  rw [← ENat.coe_inj, analyticRankAtOne_coe_order]
  simpa using D.analyticAtOne.order_eq_zero_iff

theorem centralValue_eq_zero_of_analyticRank_pos
    (D : FiniteAnalyticGermAtOne)
    (h : 0 < analyticRankAtOne D) :
    D.L 1 = 0 := by
  apply D.analyticAtOne.apply_eq_zero_of_order_toNat_ne_zero
  exact Nat.ne_of_gt h

end P06.BSD
