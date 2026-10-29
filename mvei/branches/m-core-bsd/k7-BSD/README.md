# m-core-bsd — branch `k7-BSD`

Lean sources from the branch `k7-BSD` of the private repository `ShantiDraconis/m-core-bsd`, commit `ae8680cec3ee8c37f9e9da44ea7ceec313b0488a` (2026-09-15T22:07:28+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 3 — closed 3, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 2 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `91eda8a74ef71b383072dae5c1cd19fabfd1bef49b50091bac14135a9e739ad9`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/k7-BSD/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.k7_dependency_reachable` | `lean/MCore/K7.lean`:9 | fechado |
| `MCore.k7_source_open` | `lean/MCore/K7.lean`:11 | fechado |
| `MCore.k7_target_open` | `lean/MCore/K7.lean`:13 | fechado |
