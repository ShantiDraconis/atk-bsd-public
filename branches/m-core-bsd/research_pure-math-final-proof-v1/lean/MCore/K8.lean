import MCore.K7
namespace MCore

/-- Minimal arithmetic/analytic data needed to state the rank part of BSD.
    The natural numbers stand for the two independently defined ranks. -/
structure BSDRankData where
  mordellWeilRank : Nat
  analyticRank : Nat

/-- The rank equality formulation of the BSD target. -/
def BSDRankEquality (d : BSDRankData) : Prop :=
  d.analyticRank = d.mordellWeilRank

/-- K8 does not assume or manufacture the equality. It records the exact
    proposition whose proof would discharge the rank-equality bridge. -/
structure BSDRankBridgeInterface where
  data : BSDRankData
  target : Prop := BSDRankEquality data

/-- The inherited K7/K6 target proposition, represented as an open node.
    The statement is the proposition itself, not a proof of it. -/
def k8_rank_bridge_node : CertNode :=
  { status := .openBridge,
    statement := k6_dependency.target.status = .openBridge }

theorem k8_rank_bridge_open :
    k8_rank_bridge_node.status = .openBridge := rfl

theorem k8_rank_bridge_not_proved :
    k8_rank_bridge_node.status ≠ .provedProperty := by decide

theorem k8_rank_bridge_not_certified :
    ¬ Nonempty (ProofCertificate k8_rank_bridge_node) := by
  intro h
  rcases h with ⟨c⟩
  exact k8_rank_bridge_not_proved c.status_proved

/-- A supplied equality can be consumed by the interface; K8 contains no
    theorem constructing such an equality from BSD data. -/
theorem k8_consume_rank_equality (d : BSDRankData)
    (h : d.analyticRank = d.mordellWeilRank) : BSDRankEquality d := h

end MCore
