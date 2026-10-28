import MCore.BSDMaterialPromotion
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

namespace MCore.BSDAnalyticMaterial

open MCore
open MCore.BSDConcreteLowRank
open MCore.BSDMaterialPromotion

/--
Analytic germ at s = 1 with finite vanishing order.
This is the concrete analytic object from which analytic rank is extracted.
-/
structure FiniteAnalyticGermAtOne where
  L : ℂ → ℂ
  analyticAtOne : AnalyticAt ℂ L (1 : ℂ)
  orderFinite : analyticAtOne.order ≠ ⊤

noncomputable def analyticRankAtOne
    (D : FiniteAnalyticGermAtOne) : ℕ :=
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

/--
Analytic data attached to a genuine elliptic curve.
The field Lgerm is intentionally separate from the arithmetic point group.
-/
structure EllipticCurveAnalyticData
    (E : EllipticCurveQ) where
  Lgerm : FiniteAnalyticGermAtOne

noncomputable def EllipticCurveAnalyticData.toRankData
    {E : EllipticCurveQ}
    (A : EllipticCurveAnalyticData E) :
    AnalyticRankData E where
  analyticOrderAtOne := analyticRankAtOne A.Lgerm

/--
Concrete low-rank material stated using the actual analytic vanishing order
and the genuine Mordell-Weil finrank.
-/
structure AnalyticLowRankMaterial
    (E : EllipticCurveQ)
    (A : EllipticCurveAnalyticData E) : Prop where
  analyticOrder_le_one :
    analyticRankAtOne A.Lgerm ≤ 1
  rank_zero :
    analyticRankAtOne A.Lgerm = 0 →
      genuineMordellWeilRank E = 0
  rank_one :
    analyticRankAtOne A.Lgerm = 1 →
      genuineMordellWeilRank E = 1

noncomputable def AnalyticLowRankMaterial.toEndpoint
    {E : EllipticCurveQ}
    {A : EllipticCurveAnalyticData E}
    (h : AnalyticLowRankMaterial E A) :
    BSDLowRankMaterialEndpoint E A.toRankData where
  analyticOrder_le_one := h.analyticOrder_le_one
  rank_zero := h.rank_zero
  rank_one := h.rank_one

theorem AnalyticLowRankMaterial.openCore
    {E : EllipticCurveQ}
    {A : EllipticCurveAnalyticData E}
    (h : AnalyticLowRankMaterial E A) :
    BSDOpenCore (toBSDDatum E A.toRankData) :=
  material_apriori_bound_BSD_lowRank h.toEndpoint

theorem AnalyticLowRankMaterial.rank_eq_analyticOrder
    {E : EllipticCurveQ}
    {A : EllipticCurveAnalyticData E}
    (h : AnalyticLowRankMaterial E A) :
    analyticRankAtOne A.Lgerm = genuineMordellWeilRank E :=
  rank_eq_analyticRank_lowRank h.toEndpoint

/--
Universal analytic material: one finite analytic germ for each genuine curve,
plus the exact arithmetic consequences in the 0, 1, and >=2 regimes.
-/
structure BSDUniversalAnalyticRankMaterial where
  analyticData :
    ∀ E : EllipticCurveQ, EllipticCurveAnalyticData E
  rank_zero :
    ∀ E,
      analyticRankAtOne (analyticData E).Lgerm = 0 →
        genuineMordellWeilRank E = 0
  rank_one :
    ∀ E,
      analyticRankAtOne (analyticData E).Lgerm = 1 →
        genuineMordellWeilRank E = 1
  higher_rank :
    ∀ E,
      2 ≤ analyticRankAtOne (analyticData E).Lgerm →
        analyticRankAtOne (analyticData E).Lgerm =
          genuineMordellWeilRank E

noncomputable def BSDUniversalAnalyticRankMaterial.toRankMaterial
    (P : BSDUniversalAnalyticRankMaterial) :
    BSDUniversalRankMaterial
      (fun E => analyticRankAtOne (P.analyticData E).Lgerm) where
  rank_zero := P.rank_zero
  rank_one := P.rank_one
  higher_rank := P.higher_rank

theorem BSDUniversalAnalyticRankMaterial.rank_equality
    (P : BSDUniversalAnalyticRankMaterial)
    (E : EllipticCurveQ) :
    analyticRankAtOne (P.analyticData E).Lgerm =
      genuineMordellWeilRank E :=
  P.toRankMaterial.rank_equality E

end MCore.BSDAnalyticMaterial
