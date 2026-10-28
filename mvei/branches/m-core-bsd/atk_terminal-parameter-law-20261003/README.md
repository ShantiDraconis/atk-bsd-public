# m-core-bsd — branch `atk/terminal-parameter-law-20261003`

Lean sources from the branch `atk/terminal-parameter-law-20261003` of the private repository `ShantiDraconis/m-core-bsd`, commit `9dcaf945382b8d497f697d95d3f694f8a8a1b3ba` (2026-10-04T17:52:18+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 4 — closed 4, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 23 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `1c7224f802966190961a2b6ca14f5d4a5b97b939383006bfc704a2c275afe9a1`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/atk_terminal-parameter-law-20261003/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.bsd_terminal_cert_refute_disjoint` | `lean/MCore/BSDTerminalLaw.lean`:16 | fechado |
| `MCore.not_bsdTerminalCertifies_iff_refutes` | `lean/MCore/BSDTerminalLaw.lean`:22 | fechado |
| `MCore.terminalCertificate_exposes_rank` | `lean/MCore/BSDTerminalLaw.lean`:34 | fechado |
| `MCore.universalCertificate_certifies_terminal` | `lean/MCore/BSDTerminalLaw.lean`:28 | fechado |
