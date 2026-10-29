# m-core-bsd — branch `research/pure-math-final-proof-v1`

Lean sources from the branch `research/pure-math-final-proof-v1` of the private repository `ShantiDraconis/m-core-bsd`, commit `0ef6b929df77326a90533b56e53dc4987f8855e6` (2026-09-20T09:04:24+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 6 — closed 1, conditional 0, open 0, proof error 0, not reached 5, no result 0.
* History: 11 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `7610c9c7c1d0ef82c2b5a9396bd6dd89ade588260d7daf239b59d849d6a2bebf`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/research_pure-math-final-proof-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.BackwardAudit.bsd_constructor_closes_rank_part` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:25 | nao_alcancado |
| `MCore.BackwardAudit.bsd_constructor_iff_rank_contract` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:21 | nao_alcancado |
| `MCore.BackwardAudit.bsd_witness_constructor_still_open` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:32 | nao_alcancado |
| `MCore.BackwardAudit.constructor_to_rank_contract` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:11 | nao_alcancado |
| `MCore.BackwardAudit.rank_contract_to_constructor` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:16 | nao_alcancado |
| `MCore.Research.return_to_primary` | `lean/MCore/Research/ParallelClosure.lean`:10 | fechado |
