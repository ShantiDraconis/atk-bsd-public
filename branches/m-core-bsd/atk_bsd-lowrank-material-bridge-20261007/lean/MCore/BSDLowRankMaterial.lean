import MCore.K13

namespace MCore

/--
Material certificate for the analytically low-rank BSD domain.

This structure does not contain the desired equality as a field.  It contains
the two arithmetic conclusions needed to derive it in the cases
analytic order 0 and 1.
-/
structure BSDLowRankMaterialCertificate
    (d : BSDArithmeticAnalyticData) : Prop where
  rank_zero :
    d.analyticOrderAtOne = 0 → d.mordellWeilRank = 0
  rank_one :
    d.analyticOrderAtOne = 1 → d.mordellWeilRank = 1

/--
A genuine low-rank inhabitant consists of the domain condition together with
the material arithmetic certificate.  The BSD equality is not assumed here.
-/
structure BSDLowRankInhabitant
    (d : BSDArithmeticAnalyticData) : Prop where
  analyticOrder_le_one : d.analyticOrderAtOne ≤ 1
  material : BSDLowRankMaterialCertificate d

/--
The material certificate discharges the exact K12 rank target on the
analytic-order <= 1 domain.
-/
theorem bsdLowRank_material_to_rankPart
    (d : BSDArithmeticAnalyticData)
    (hAnalytic : d.analyticOrderAtOne ≤ 1)
    (hMaterial : BSDLowRankMaterialCertificate d) :
    BSDRankPart d := by
  unfold BSDRankPart
  have hCases :
      d.analyticOrderAtOne = 0 ∨ d.analyticOrderAtOne = 1 := by
    omega
  rcases hCases with h0 | h1
  · calc
      d.analyticOrderAtOne = 0 := h0
      _ = d.mordellWeilRank := (hMaterial.rank_zero h0).symm
  · calc
      d.analyticOrderAtOne = 1 := h1
      _ = d.mordellWeilRank := (hMaterial.rank_one h1).symm

/--
Direct bridge into the existing K13 terminal theorem.

This is the requested connection:
BSDLowRankMaterialCertificate -> BSDRankPart -> BSDOpenCore.
-/
theorem bsdLowRank_material_to_openCore
    (d : BSDArithmeticAnalyticData)
    (hAnalytic : d.analyticOrderAtOne ≤ 1)
    (hMaterial : BSDLowRankMaterialCertificate d) :
    BSDOpenCore d := by
  exact k13_consume_open_core d
    (bsdLowRank_material_to_rankPart d hAnalytic hMaterial)

/--
Inhabitant form used downstream: once a concrete arithmetic layer constructs
this object, the existing terminal BSD proposition follows without any
additional hypothesis wrapper.
-/
theorem BSDLowRankInhabitant.rankPart
    {d : BSDArithmeticAnalyticData}
    (h : BSDLowRankInhabitant d) :
    BSDRankPart d :=
  bsdLowRank_material_to_rankPart
    d h.analyticOrder_le_one h.material

theorem BSDLowRankInhabitant.openCore
    {d : BSDArithmeticAnalyticData}
    (h : BSDLowRankInhabitant d) :
    BSDOpenCore d :=
  bsdLowRank_material_to_openCore
    d h.analyticOrder_le_one h.material

/--
Adapter to the earlier K8 rank representation.
-/
theorem BSDLowRankInhabitant.rankEquality
    {d : BSDArithmeticAnalyticData}
    (h : BSDLowRankInhabitant d) :
    BSDRankEquality d.toRankData := by
  exact (k12_rank_part_iff_k8_target d).mp h.rankPart

/--
The universal K11/K12/K13 nodes intentionally remain OPEN: this file proves
the endpoint only for an explicitly inhabited analytic-order <= 1 object.
No claim is made for analytic order >= 2.
-/
theorem bsdLowRank_bridge_preserves_universal_open_frontier :
    k11_rank_core_node.status = .openBridge ∧
    k12_rank_part_node.status = .openBridge ∧
    k13_open_core_node.status = .openBridge := by
  exact ⟨k11_rank_core_open, k12_rank_part_open, k13_open_core_status⟩

end MCore
