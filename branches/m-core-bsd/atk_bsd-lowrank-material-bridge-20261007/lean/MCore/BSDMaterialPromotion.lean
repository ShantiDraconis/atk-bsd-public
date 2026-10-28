import MCore.BSDConcreteLowRank
import Mathlib.Data.Real.Basic

namespace MCore.BSDMaterialPromotion

open MCore
open MCore.BSDConcreteLowRank

inductive PromotionStatus where
  | structureOnly
  | promotedLowRankMaterial
  | promotedUniversalRankMaterial
  | promotedFullMaterial
  deriving DecidableEq, Repr

structure BSDLowRankMaterialEndpoint
    (E : EllipticCurveQ)
    (A : AnalyticRankData E) : Prop where
  analyticOrder_le_one : A.analyticOrderAtOne ≤ 1
  rank_zero :
    A.analyticOrderAtOne = 0 →
      genuineMordellWeilRank E = 0
  rank_one :
    A.analyticOrderAtOne = 1 →
      genuineMordellWeilRank E = 1

noncomputable def BSDLowRankMaterialEndpoint.toInhabitant
    {E : EllipticCurveQ}
    {A : AnalyticRankData E}
    (h : BSDLowRankMaterialEndpoint E A) :
    ConcreteLowRankInhabitant E A where
  analyticOrder_le_one := h.analyticOrder_le_one
  material := {
    rank_zero := h.rank_zero
    rank_one := h.rank_one
  }

theorem material_apriori_bound_BSD_lowRank
    {E : EllipticCurveQ}
    {A : AnalyticRankData E}
    (hMaterial : BSDLowRankMaterialEndpoint E A) :
    BSDOpenCore (toBSDDatum E A) :=
  hMaterial.toInhabitant.openCore

theorem rank_eq_analyticRank_lowRank
    {E : EllipticCurveQ}
    {A : AnalyticRankData E}
    (hMaterial : BSDLowRankMaterialEndpoint E A) :
    A.analyticOrderAtOne = genuineMordellWeilRank E :=
  hMaterial.toInhabitant.rank_eq_analyticOrder

structure BSDUniversalRankMaterial
    (analyticOrderAtOne : EllipticCurveQ → Nat) : Prop where
  rank_zero :
    ∀ E, analyticOrderAtOne E = 0 →
      genuineMordellWeilRank E = 0
  rank_one :
    ∀ E, analyticOrderAtOne E = 1 →
      genuineMordellWeilRank E = 1
  higher_rank :
    ∀ E, 2 ≤ analyticOrderAtOne E →
      analyticOrderAtOne E = genuineMordellWeilRank E

theorem BSDUniversalRankMaterial.rank_equality
    {analyticOrderAtOne : EllipticCurveQ → Nat}
    (P : BSDUniversalRankMaterial analyticOrderAtOne)
    (E : EllipticCurveQ) :
    analyticOrderAtOne E = genuineMordellWeilRank E := by
  by_cases h0 : analyticOrderAtOne E = 0
  · calc
      analyticOrderAtOne E = 0 := h0
      _ = genuineMordellWeilRank E := (P.rank_zero E h0).symm
  · by_cases h1 : analyticOrderAtOne E = 1
    · calc
        analyticOrderAtOne E = 1 := h1
        _ = genuineMordellWeilRank E := (P.rank_one E h1).symm
    · have h2 : 2 ≤ analyticOrderAtOne E := by omega
      exact P.higher_rank E h2

noncomputable def universalRankDatum
    (analyticOrderAtOne : EllipticCurveQ → Nat)
    (E : EllipticCurveQ) :
    BSDArithmeticAnalyticData :=
  { mordellWeilRank := genuineMordellWeilRank E
    analyticOrderAtOne := analyticOrderAtOne E }

theorem BSDUniversalRankMaterial.openCore
    {analyticOrderAtOne : EllipticCurveQ → Nat}
    (P : BSDUniversalRankMaterial analyticOrderAtOne)
    (E : EllipticCurveQ) :
    BSDOpenCore (universalRankDatum analyticOrderAtOne E) := by
  apply k13_consume_open_core
  unfold BSDRankPart universalRankDatum
  exact P.rank_equality E

structure BSDRefinedMaterialData where
  leadingCoefficient : ℝ
  realPeriod : ℝ
  regulator : ℝ
  shaOrder : Nat
  tamagawaProduct : Nat
  torsionOrder : Nat

def BSDRefinedIdentity (d : BSDRefinedMaterialData) : Prop :=
  d.leadingCoefficient * (d.torsionOrder : ℝ)^2 =
    d.realPeriod * d.regulator *
      (d.shaOrder : ℝ) * (d.tamagawaProduct : ℝ)

structure BSDFullMaterialPayload where
  analyticOrderAtOne : EllipticCurveQ → Nat
  shaFinite : EllipticCurveQ → Prop
  refinedData : EllipticCurveQ → BSDRefinedMaterialData
  rankMaterial :
    BSDUniversalRankMaterial analyticOrderAtOne
  shaFiniteProof :
    ∀ E, shaFinite E
  refinedIdentity :
    ∀ E, BSDRefinedIdentity (refinedData E)

theorem BSDFullMaterialPayload.rankPart
    (P : BSDFullMaterialPayload)
    (E : EllipticCurveQ) :
    BSDOpenCore (universalRankDatum P.analyticOrderAtOne E) :=
  P.rankMaterial.openCore E

theorem BSDFullMaterialPayload.sha_finite
    (P : BSDFullMaterialPayload)
    (E : EllipticCurveQ) :
    P.shaFinite E :=
  P.shaFiniteProof E

theorem BSDFullMaterialPayload.refined
    (P : BSDFullMaterialPayload)
    (E : EllipticCurveQ) :
    BSDRefinedIdentity (P.refinedData E) :=
  P.refinedIdentity E

structure BSDMaterialPromotionCertificate where
  payload : BSDFullMaterialPayload

def BSDMaterialPromotionCertificate.status
    (_ : BSDMaterialPromotionCertificate) :
    PromotionStatus :=
  .promotedFullMaterial

theorem BSDMaterialPromotionCertificate.sound
    (C : BSDMaterialPromotionCertificate) :
    (∀ E, BSDOpenCore
      (universalRankDatum C.payload.analyticOrderAtOne E)) ∧
    (∀ E, C.payload.shaFinite E) ∧
    (∀ E, BSDRefinedIdentity (C.payload.refinedData E)) := by
  exact ⟨C.payload.rankPart, C.payload.sha_finite, C.payload.refined⟩

def MATERIAL_ENDPOINT_INHABITANT_PROMOTED_BY_MATERIAL : Prop :=
  Nonempty BSDMaterialPromotionCertificate

theorem lowRankPromotion_of_material
    {E : EllipticCurveQ}
    {A : AnalyticRankData E}
    (hLe : A.analyticOrderAtOne ≤ 1)
    (h0 : A.analyticOrderAtOne = 0 →
      genuineMordellWeilRank E = 0)
    (h1 : A.analyticOrderAtOne = 1 →
      genuineMordellWeilRank E = 1) :
    BSDOpenCore (toBSDDatum E A) := by
  exact material_apriori_bound_BSD_lowRank {
    analyticOrder_le_one := hLe
    rank_zero := h0
    rank_one := h1
  }

end MCore.BSDMaterialPromotion
