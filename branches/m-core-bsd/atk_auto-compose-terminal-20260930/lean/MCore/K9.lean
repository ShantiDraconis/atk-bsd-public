import MCore.K8
namespace MCore

/-- K9 separates the two logical directions of the BSD rank equality. -/
def BSDAnalyticToArithmetic (d : BSDRankData) : Prop :=
  d.analyticRank ≤ d.mordellWeilRank

def BSDArithmeticToAnalytic (d : BSDRankData) : Prop :=
  d.mordellWeilRank ≤ d.analyticRank

/-- Equality genuinely yields both inequalities; this is elementary logic,
    not an assertion that BSD rank equality has been established. -/
theorem k9_equality_implies_analytic_to_arithmetic (d : BSDRankData)
    (h : BSDRankEquality d) : BSDAnalyticToArithmetic d := by
  unfold BSDRankEquality BSDAnalyticToArithmetic at *
  omega

theorem k9_equality_implies_arithmetic_to_analytic (d : BSDRankData)
    (h : BSDRankEquality d) : BSDArithmeticToAnalytic d := by
  unfold BSDRankEquality BSDArithmeticToAnalytic at *
  omega

/-- Conversely, the two inequalities reconstruct exactly the equality target. -/
theorem k9_two_directions_imply_equality (d : BSDRankData)
    (h₁ : BSDAnalyticToArithmetic d) (h₂ : BSDArithmeticToAnalytic d) :
    BSDRankEquality d := by
  unfold BSDRankEquality BSDAnalyticToArithmetic BSDArithmeticToAnalytic at *
  omega

/-- Neither direction is promoted by K9; both remain behind the K8 firewall. -/
def k9_analytic_to_arithmetic_node : CertNode :=
  { status := .openBridge, statement := k8_rank_bridge_node.status = .openBridge }

def k9_arithmetic_to_analytic_node : CertNode :=
  { status := .openBridge, statement := k8_rank_bridge_node.status = .openBridge }

theorem k9_analytic_to_arithmetic_open :
    k9_analytic_to_arithmetic_node.status = .openBridge := rfl

theorem k9_arithmetic_to_analytic_open :
    k9_arithmetic_to_analytic_node.status = .openBridge := rfl

theorem k9_analytic_to_arithmetic_not_certified :
    ¬ Nonempty (ProofCertificate k9_analytic_to_arithmetic_node) := by
  intro h
  rcases h with ⟨c⟩
  have hne : k9_analytic_to_arithmetic_node.status ≠ .provedProperty := by decide
  exact hne c.status_proved

theorem k9_arithmetic_to_analytic_not_certified :
    ¬ Nonempty (ProofCertificate k9_arithmetic_to_analytic_node) := by
  intro h
  rcases h with ⟨c⟩
  have hne : k9_arithmetic_to_analytic_node.status ≠ .provedProperty := by decide
  exact hne c.status_proved


/-- Producer-first specification audit: the universal closure over raw
BSDRankData is false because the structure permits arbitrary unrelated ranks. -/
def k9_counterexample_analytic_to_arithmetic : BSDRankData :=
  { mordellWeilRank := 0, analyticRank := 1 }

theorem k9_not_universal_analytic_to_arithmetic :
    ¬ (∀ d : BSDRankData, BSDAnalyticToArithmetic d) := by
  classical
  intro h
  have hbad : ¬ BSDAnalyticToArithmetic k9_counterexample_analytic_to_arithmetic := by
    simp [BSDAnalyticToArithmetic, k9_counterexample_analytic_to_arithmetic]
  exact hbad (h k9_counterexample_analytic_to_arithmetic)

def k9_counterexample_arithmetic_to_analytic : BSDRankData :=
  { mordellWeilRank := 1, analyticRank := 0 }

theorem k9_not_universal_arithmetic_to_analytic :
    ¬ (∀ d : BSDRankData, BSDArithmeticToAnalytic d) := by
  classical
  intro h
  have hbad : ¬ BSDArithmeticToAnalytic k9_counterexample_arithmetic_to_analytic := by
    simp [BSDArithmeticToAnalytic, k9_counterexample_arithmetic_to_analytic]
  exact hbad (h k9_counterexample_arithmetic_to_analytic)

end MCore
