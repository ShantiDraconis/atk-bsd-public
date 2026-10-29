# m-core-bsd — branch `a0-preaudit`

Lean sources from the branch `a0-preaudit` of the private repository `ShantiDraconis/m-core-bsd`, commit `0ee0a245a4f6d8ba6b798aa6e4b73b593df9597d` (2026-09-17T12:27:06+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 1 — closed 1, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 56 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `17eba406b1f7d09db66caae47c1b907f1c6a8a4473b7396d01ddeccc23a6ac49`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/a0-preaudit/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCoreBSD.Plectic.ConstructionGate.constructionConditional_proved` | `a0/Plectic/ConstructionGate.lean`:84 | fechado |
