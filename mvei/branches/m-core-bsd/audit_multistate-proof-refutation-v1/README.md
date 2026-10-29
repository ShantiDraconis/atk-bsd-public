# m-core-bsd — branch `audit/multistate-proof-refutation-v1`

Lean sources from the branch `audit/multistate-proof-refutation-v1` of the private repository `ShantiDraconis/m-core-bsd`, commit `20f96533d64d04e3db4df0f186f255529a2d6750` (2026-09-19T10:39:49+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 30 — closed 23, conditional 0, open 0, proof error 0, not reached 7, no result 0.
* History: 59 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `48bd92fa34cb52da8d9f1617bf7d601b87529b80f84c723bc692f0f9b8fb9260`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/audit_multistate-proof-refutation-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Audit8x5.A_pending` | `lean/MCore/Audit8x5.lean`:44 | fechado |
| `MCore.Audit8x5.HC_blocking` | `lean/MCore/Audit8x5.lean`:39 | fechado |
| `MCore.Audit8x5.K_pending` | `lean/MCore/Audit8x5.lean`:43 | fechado |
| `MCore.Audit8x5.Q_pending` | `lean/MCore/Audit8x5.lean`:41 | fechado |
| `MCore.Audit8x5.S_pending` | `lean/MCore/Audit8x5.lean`:42 | fechado |
| `MCore.Audit8x5.final_audit_not_certified` | `lean/MCore/Audit8x5.lean`:26 | fechado |
| `MCore.Audit8x5.rank_core_not_certified` | `lean/MCore/Audit8x5.lean`:21 | fechado |
| `MCore.Audit8x5.rank_part_reduction` | `lean/MCore/Audit8x5.lean`:16 | fechado |
| `MCore.BackwardAudit.P_on_1933a1` | `lean/MCore/BackwardAudit/BSD1933A1ExactPoints.lean`:9 | nao_alcancado |
| `MCore.BackwardAudit.PplusQ_on_curve` | `lean/MCore/BackwardAudit/BSD1933A1ExactPoints.lean`:18 | nao_alcancado |
| `MCore.BackwardAudit.Q_on_1933a1` | `lean/MCore/BackwardAudit/BSD1933A1ExactPoints.lean`:11 | nao_alcancado |
| `MCore.BackwardAudit.adapted_control_rejected` | `lean/MCore/BackwardAudit/BSDBridgeLabCertificate.lean`:63 | fechado |
| `MCore.BackwardAudit.audited_set_leaves_operator_open` | `lean/MCore/BackwardAudit/NumberFieldComplexSecondDerivativeHeightOperator.lean`:45 | fechado |
| `MCore.BackwardAudit.banwait_not_exact` | `lean/MCore/BackwardAudit/NumberFieldComplexSecondDerivativeHeightOperator.lean`:40 | fechado |
| `MCore.BackwardAudit.circular_control_rejected` | `lean/MCore/BackwardAudit/BSDBridgeLabCertificate.lean`:52 | fechado |
| `MCore.BackwardAudit.closedModel_ne_provedClosed` | `lean/MCore/BackwardAudit/HypotheticalClosureOracle.lean`:10 | fechado |
| `MCore.BackwardAudit.current_bridge_lab_fail_closed` | `lean/MCore/BackwardAudit/BSDBridgeLabCertificate.lean`:30 | fechado |
| `MCore.BackwardAudit.exact_point_layer_closed` | `lean/MCore/BackwardAudit/BSD1933A1ExactPoints.lean`:20 | nao_alcancado |
| `MCore.BackwardAudit.false_witness_refutes_rank_part` | `lean/MCore/BackwardAudit/HypotheticalClosureOracle.lean`:40 | fechado |
| `MCore.BackwardAudit.g3_false_has_no_certified_independent_witness` | `lean/MCore/BackwardAudit/HypotheticalClosureOracle.lean`:58 | fechado |
| `MCore.BackwardAudit.g3_true_first_recorded_collision_is_operator` | `lean/MCore/BackwardAudit/HypotheticalClosureOracle.lean`:51 | fechado |
| `MCore.BackwardAudit.generalized_negation_check` | `lean/MCore/BackwardAudit/BSD1933A1ExactPoints.lean`:19 | nao_alcancado |
| `MCore.BackwardAudit.gross_zagier_not_exact` | `lean/MCore/BackwardAudit/NumberFieldComplexSecondDerivativeHeightOperator.lean`:37 | fechado |
| `MCore.BackwardAudit.line_through_PQ` | `lean/MCore/BackwardAudit/BSD1933A1ExactPoints.lean`:12 | nao_alcancado |
| `MCore.BackwardAudit.positive_true_control_promotes` | `lean/MCore/BackwardAudit/BSDBridgeLabCertificate.lean`:41 | fechado |
| `MCore.BackwardAudit.testVector1933a1_constants` | `lean/MCore/BackwardAudit/BSDTestVector1933A1.lean`:27 | fechado |
| `MCore.BackwardAudit.testVector1933a1_fail_closed` | `lean/MCore/BackwardAudit/BSDTestVector1933A1.lean`:36 | fechado |
| `MCore.BackwardAudit.testVector1933a1_rank2` | `lean/MCore/BackwardAudit/BSDTestVector1933A1.lean`:23 | fechado |
| `MCore.BackwardAudit.third_intersection_on_curve` | `lean/MCore/BackwardAudit/BSD1933A1ExactPoints.lean`:17 | nao_alcancado |
| `MCore.BackwardAudit.yun_zhang_not_exact` | `lean/MCore/BackwardAudit/NumberFieldComplexSecondDerivativeHeightOperator.lean`:39 | fechado |
