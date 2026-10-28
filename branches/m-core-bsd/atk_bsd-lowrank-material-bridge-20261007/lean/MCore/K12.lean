import MCore.K11
namespace MCore

/-- Minimal typed interface for the arithmetic and analytic quantities compared
by the rank part of BSD.  These fields are data; no existence theorem is
asserted here. -/
structure BSDArithmeticAnalyticData where
  mordellWeilRank : Nat
  analyticOrderAtOne : Nat

/-- Rank-part target of BSD at the abstract interface level. -/
def BSDRankPart (d : BSDArithmeticAnalyticData) : Prop :=
  d.analyticOrderAtOne = d.mordellWeilRank

/-- Conversion to the earlier abstract rank data is definitional. -/
def BSDArithmeticAnalyticData.toRankData (d : BSDArithmeticAnalyticData) : BSDRankData :=
  { mordellWeilRank := d.mordellWeilRank,
    analyticRank := d.analyticOrderAtOne }

theorem k12_rank_part_iff_k8_target (d : BSDArithmeticAnalyticData) :
    BSDRankPart d ↔ BSDRankEquality d.toRankData := by
  rfl

/-- The substantive rank-part statement remains fail-closed. -/
def k12_rank_part_node : CertNode :=
  { status := .openBridge,
    statement := k11_rank_core_node.status = .openBridge }

theorem k12_rank_part_open : k12_rank_part_node.status = .openBridge := rfl

theorem k12_rank_part_not_proved :
    k12_rank_part_node.status ≠ .provedProperty := by decide

theorem k12_rank_part_not_certified :
    ¬ Nonempty (ProofCertificate k12_rank_part_node) := by
  intro h
  rcases h with ⟨c⟩
  exact k12_rank_part_not_proved c.status_proved

end MCore
