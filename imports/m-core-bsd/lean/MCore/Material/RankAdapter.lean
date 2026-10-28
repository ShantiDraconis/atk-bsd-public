import MCore.Material.Closure
import MCore.K12
namespace MCore.Material
def BSDCanonicalRankMaterial (d : MCore.BSDArithmeticAnalyticData) : Prop := MCore.BSDRankPart d
theorem bsd_rank_material_iff_existing_target (d : MCore.BSDArithmeticAnalyticData) : BSDCanonicalRankMaterial d ↔ MCore.BSDRankEquality d.toRankData := MCore.k12_rank_part_iff_k8_target d
end MCore.Material
