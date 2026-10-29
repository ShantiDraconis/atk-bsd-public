# m-core-bsd — branch `atk/next-bsd-concrete-realizable-domain-20260928`

Lean sources from the branch `atk/next-bsd-concrete-realizable-domain-20260928` of the private repository `ShantiDraconis/m-core-bsd`, commit `9be97dca5ea6a3ac44af521f835fddf208682187` (2026-09-28T18:39:02+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 9 — closed 6, conditional 0, open 0, proof error 3, not reached 0, no result 0.
* History: 16 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `25b913d5ec99c88297aca768c0898bef79f1797943123c7084da45173f4938bf`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/atk_next-bsd-concrete-realizable-domain-20260928/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.StableHoleExtraction.bsd_pass_a` | `lean/Extraction/BSDPassA.lean`:6 | erro |
| `MCore.StableHoleExtraction.bsd_pass_b` | `lean/Extraction/BSDPassB.lean`:6 | erro |
| `MCore.StableHoleExtraction.bsd_pass_c` | `lean/Extraction/BSDPassC.lean`:6 | erro |
| `MCore.StableHoleExtraction.current_realizable_family_does_not_exclude_mismatch` | `lean/Extraction/BSDFenceAudit.lean`:17 | fechado |
| `MCore.StableHoleExtraction.expanded_normalizes` | `lean/Extraction/BSDStableHoleNormalization.lean`:16 | fechado |
| `MCore.StableHoleExtraction.mismatch_is_in_current_family_image` | `lean/Extraction/BSDFenceAudit.lean`:12 | fechado |
| `MCore.StableHoleExtraction.passA_normalizes` | `lean/Extraction/BSDStableHoleNormalization.lean`:11 | fechado |
| `MCore.StableHoleExtraction.unrestricted_fence` | `lean/Extraction/BSDStableHoleNormalization.lean`:23 | fechado |
| `MCore.bsd_rank_part_on_family_apply` | `lean/MCore/BackwardAudit/D01RealizableDomain.lean`:15 | fechado |
