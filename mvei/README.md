# MVEI kernel check — m-core-bsd

This folder records what the Lean 4 kernel said about the Lean sources of the private repository `ShantiDraconis/m-core-bsd`. The sources are published in [`imports/m-core-bsd/`](../imports/m-core-bsd/).

## What is published

* Source: `ShantiDraconis/m-core-bsd`, commit `a9e1292d13a0fba7da0bde8e082f34c2d5acd0d0` (2026-10-11T23:07:37Z).
* 33 files: 28 `.lean` files and the Lake files (`lakefile.*`, `lean-toolchain`, `lake-manifest.json`). Paths are the same as in the source repository.
* Nothing else from the private repository is published (documents, commercial license, prompts, storefront material).
* `SOURCES.sha256` lists every published file with its SHA-256. From the repository root: `sha256sum -c mvei/SOURCES.sha256`.

## What the kernel said

MVEI verification of 2026-10-29T01:49:57+00:00, on commit `a9e1292d13a0fba7da0bde8e082f34c2d5acd0d0`. Each theorem was read with `Lean.collectAxioms`, the function behind `#print axioms`.

| Lean project | Lean version | Build | Closed | Conditional | Open (`sorry`) | Checked file by file: closed / conditional / open / proof error / not reached |
|---|---|---|---:|---:|---:|---|
| `.` | v4.19.0 | OK | 156 | 0 | 0 | 3 / 0 / 1 / 1 / 1 |
| `atk-kernel` | v4.34.1 | OK | 3 | 0 | 0 | — |

| Closed theorems in this repository | |
|---|---:|
| Counting each project | 162 |
| Unique (name + statement) | 162 |
| Unique, without the lemmas Lean generates itself (`eq_1`, `mk.inj`, `sizeOf_spec`, `deriving`) | 74 |

*Closed* means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`. It says that the statement as written in the file is proved; it does not say that an open problem is solved. Every statement is in `VERIFICACAO.json`. *Conditional* means the proof also uses axioms declared in the repository; *open* means it uses `sorry`. *Checked file by file* covers the files that no build reached: each one went through Lean whole, with a `#print axioms` for each theorem.

| Theorem | Project | State | Axioms beyond the standard three |
|---|---|---|---|
| `MCore.no_universal_rank_part_over_arbitrary_data` | `. (file by file)` | open | `sorryAx` |

### Declared theorems

The `.lean` files of the verified commit declare 69 `theorem`/`lemma` (counting copies). The kernel checked 66 of them (66 closed, 0 conditional, 0 open). The closed count in the table above is larger: it also counts the theorems Lean generates by itself (equation lemmas, structure fields, `deriving`), which are not written in the text. For 3 the kernel has no result:

| Reason | Theorems |
|---|---:|
| the project built, but the file is not part of the lakefile target | 2 |
| checked file by file: Lean did not reach the theorem (missing import, syntax error or timeout) | 1 |

## Files in this folder

* `VERIFICACAO.json` — each Lean project of this repository, each theorem the kernel read, its statement, its axioms and its state (`fechado` closed, `condicional` conditional, `aberto-sorry` open)
* `TEOREMAS.csv` — each declared `theorem`/`lemma`: file, line, state in the kernel (`nao_checado` = not checked) and, if not checked, why (in Portuguese)
* `BUILD_LOG.txt` — one block per project: Lean version, result, errors
* `SOURCE.json` — source commit, verified commit and dates, machine-readable
* `SOURCES.sha256` — SHA-256 of every published file

## Reproduce

```
cd imports/m-core-bsd/<project>   # a project folder from the table above ('.' is imports/m-core-bsd)
lake exe cache get           # only for projects that require Mathlib
lake build
```

Each project uses the Lean version in its own `lean-toolchain`, which elan installs. The MVEI pipeline that produced these results is in the author's repository and is not public.
