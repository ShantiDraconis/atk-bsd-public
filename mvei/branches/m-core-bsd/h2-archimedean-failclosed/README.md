# m-core-bsd — branch `h2-archimedean-failclosed`

Lean sources from the branch `h2-archimedean-failclosed` of the private repository `ShantiDraconis/m-core-bsd`, commit `46a604e4bcc253098a381da006b451d821e22ee5` (2026-09-18T06:08:32+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 14 — closed 11, conditional 0, open 0, proof error 0, not reached 3, no result 0.
* History: 47 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `31aa5e4b8218f0061eb8b302a840c5b423c35f530d5c55701b48a1dce6ee8f87`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/h2-archimedean-failclosed/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.B6.analyticLeading_def` | `lean/MCore/B6/Normalization.lean`:8 | fechado |
| `MCore.B6.b63_remains_open_math` | `lean/MCore/B6/Status.lean`:29 | fechado |
| `MCore.B6.b64_remains_open_math` | `lean/MCore/B6/Status.lean`:31 | fechado |
| `MCore.B6.b65_is_only_conditional` | `lean/MCore/B6/Status.lean`:33 | fechado |
| `MCore.B6.b6_remains_open` | `lean/MCore/B6/Status.lean`:26 | fechado |
| `MCore.B6.bridgeComposition_is_conditional` | `lean/MCore/B6/Normalization.lean`:22 | fechado |
| `MCore.B6.conditionalAssembly` | `lean/MCore/B6/Decomposition.lean`:42 | fechado |
| `MCore.B6.rankTwo_typed` | `lean/MCore/B6/Normalization.lean`:4 | fechado |
| `MCore.Heights.h2_certified_of_certificate` | `lean/MCore/Heights/H2_Certificate.lean`:16 | nao_alcancado |
| `MCore.Heights.independent_of_positive_gram` | `lean/MCore/Heights/H3_Regulator.lean`:8 | nao_alcancado |
| `MCore.Heights.term_bound_available` | `lean/MCore/Heights/ArchimedeanSeries.lean`:33 | nao_alcancado |
| `MCore.S2.b6_3_conditional` | `lean/MCore/S2/B6Conditional.lean`:12 | fechado |
| `MCore.S2.b6_4_conditional` | `lean/MCore/S2/B6Conditional.lean`:18 | fechado |
| `MCore.S2.b6_5_conditional` | `lean/MCore/S2/B6Conditional.lean`:23 | fechado |
