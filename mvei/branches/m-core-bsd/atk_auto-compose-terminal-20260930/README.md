# m-core-bsd — branch `atk/auto-compose-terminal-20260930`

Lean sources from the branch `atk/auto-compose-terminal-20260930` of the private repository `ShantiDraconis/m-core-bsd`, commit `753a962bd18909a8a4e682856951e1189507b811` (2026-10-01T01:45:55+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 21 — closed 10, conditional 0, open 0, proof error 0, not reached 0, no result 11.
* History: 62 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `24eb5918f94e8322de4633d21c29dd005cf5e8675d5309b2266b22430993005f`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/atk_auto-compose-terminal-20260930/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.AutoCompose.extract` | `lean/MCore/AutoCompose.lean`:24 | nao_checado |
| `MCore.BSDFinal.finalExternal_leading` | `lean/MCore/BSDExactConsequences.lean`:22 | nao_checado |
| `MCore.BSDFinal.finalExternal_rank` | `lean/MCore/BSDExactConsequences.lean`:5 | nao_checado |
| `MCore.BSDFinal.finalExternal_sha` | `lean/MCore/BSDExactConsequences.lean`:14 | nao_checado |
| `MCore.BSDFinal.residual_closes_final` | `lean/MCore/FinalOpenMath.lean`:10 | nao_checado |
| `MCore.BSDRigorous.rigorous_to_legacy_FINAL_ROOT` | `lean/MCore/BSDRigorousFrontier.lean`:67 | nao_checado |
| `MCore.BSDRigorous.shaOrder_pos` | `lean/MCore/BSDRigorousFrontier.lean`:29 | nao_checado |
| `MCore.bsd_habitant_node_open` | `lean/MCore/BSDConstructionFrontier.lean`:29 | fechado |
| `MCore.bsd_habitant_not_false_certified` | `lean/MCore/BSDConstructionFrontier.lean`:35 | fechado |
| `MCore.bsd_resolution_mechanism_node_open` | `lean/MCore/BSDResolutionMechanism.lean`:134 | nao_checado |
| `MCore.bsd_resolution_mechanism_not_false_certified` | `lean/MCore/BSDResolutionMechanism.lean`:137 | nao_checado |
| `MCore.bsd_universal_certificate_node_open` | `lean/MCore/BSDConstructionFrontier.lean`:32 | fechado |
| `MCore.bsd_universal_not_false_certified` | `lean/MCore/BSDConstructionFrontier.lean`:41 | fechado |
| `MCore.groundedHabitant_closes_rank_interface` | `lean/MCore/GroundedBSDHabitant.lean`:88 | fechado |
| `MCore.groundedHabitant_exposes_leading_identity` | `lean/MCore/GroundedBSDHabitant.lean`:97 | fechado |
| `MCore.grounded_rank_views_equal` | `lean/MCore/BSDOperatorSemantics.lean`:39 | fechado |
| `MCore.k9_not_universal_analytic_to_arithmetic` | `lean/MCore/K9.lean`:62 | fechado |
| `MCore.k9_not_universal_arithmetic_to_analytic` | `lean/MCore/K9.lean`:73 | fechado |
| `MCore.resolutionMechanism_closes_leading` | `lean/MCore/BSDResolutionMechanism.lean`:114 | nao_checado |
| `MCore.resolutionMechanism_closes_rank` | `lean/MCore/BSDResolutionMechanism.lean`:105 | nao_checado |
| `MCore.universalCertificate_closes_old_rank_core` | `lean/MCore/BSDCompositeCertificate.lean`:31 | fechado |
