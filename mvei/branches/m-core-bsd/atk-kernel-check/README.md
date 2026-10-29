# m-core-bsd — branch `atk-kernel-check`

Lean sources from the branch `atk-kernel-check` of the private repository `ShantiDraconis/m-core-bsd`, commit `fe8ffaccfdc84a3fce785aefde1d29040fd9804a` (2026-10-13T01:45:17+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: em andamento (not in the default branch).
* Theorems only on branches, in this branch: 2 — closed 2, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 10 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `b27644c251f227b9d7ba9281f8798c29de04519b18feba62ac76376d55716e30`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/atk-kernel-check/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `ATK.BSD.torsion_card_pos` | `atk-kernel/ATK/BSD.lean`:47 | fechado |
| `ATK.BSD.torsion_contains_zero` | `atk-kernel/ATK/BSD.lean`:43 | fechado |
