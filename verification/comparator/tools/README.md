# Tool revisions

The comparator records in [`../results/`](../results/) used builds of comparator and lean4export made from upstream
tags plus the patches in this directory. All three builds below used the official Lean 4.33.1 release (commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`).

| tool | upstream base | change | binary sha256 |
|---|---|---|---|
| comparator | [leanprover/comparator](https://github.com/leanprover/comparator) tag `v4.33.0`, commit `3927ad383f208ae977c340a91c48ac9b497d2097`; its lean4export dependency at `15f6055e299ad5b89345e533cc2192f4cc00f659` (`lake-manifest.json`) | [`comparator-v4.33.0-parallel-replay-v4331.patch`](comparator-v4.33.0-parallel-replay-v4331.patch): `Main.lean` and `lean-toolchain` | `3bc16bba07de7a953e408342bf56a11ade76c09eda166010b665422c71040433` (121,011,920 bytes) |
| lean4export, fast build | [leanprover/lean4export](https://github.com/leanprover/lean4export) tag `v4.33.0`, commit `15f6055e299ad5b89345e533cc2192f4cc00f659` (export format 3.1.0) | [`lean4export-v4.33.0-fast-v4331.patch`](lean4export-v4.33.0-fast-v4331.patch): `Export.lean` and `lean-toolchain` | `6b1bdccb43a2437b628c13c361270e00fb50f70a569d906d524bba1745dc3a34` |
| lean4export, stock build | the same commit `15f6055e…` | `lean-toolchain` only | `805ab4cc6a88dcef109644d201c3142261f524aecaf58b04913a9f029e21e9b5` |

Each patch is a `git diff` against the upstream commit; apply it with `git apply` in a clone at that commit. The
`lean-toolchain` change is `leanprover/lean4:v4.33.0` → `leanprover/lean4:v4.33.1` in all three builds, as in the FLT
repository's `verification/comparator/run.sh`. Build with `lake build comparator` and `lake build lean4export`.

## comparator patch

Only `Main.lean` changes. `Comparator/Compare.lean`, `Comparator/Axioms.lean`, `Comparator/Util.lean`,
`Comparator.lean` and lean4export's `Export/Parse.lean` are upstream's.

1. **Export files.** Two optional fields in the config, `challenge_export_file` and `solution_export_file`. When set,
   comparator reads the export from that file instead of building the module and running lean4export itself. When
   unset, it builds and exports as upstream does.
2. **`compareAt` and `checkAxioms`** are called as upstream calls them, with the same arguments. The patch only prints a
   line before and after each call.
3. **Kernel replay.** `COMPARATOR_REPLAY_MODE=parallel`, the default in this build, uses the parallel replay proposed in
   [leanprover/comparator#95](https://github.com/leanprover/comparator/issues/95), not yet reviewed upstream:
   - Each theorem is checked by the same kernel call in its own task, against the environment just before that
     theorem.
   - `sequential` uses Lean's `Environment.replay`, as upstream does.
   - Both modes print replay statistics at the end.
4. **nanoda** can read the solution export from the file. nanoda was off in these runs.

## lean4export patch

Only `Export.lean` changes. The patch computes a structural hash for each expression once, bottom-up, while removing
metadata. This hash includes the full value of natural-number literals. The expression deduplication table is then
keyed on that hash instead of on `Expr`'s built-in hash.

Equality in the table is still `Expr` equality, so the same expressions get the same indices. The patch is meant to
change only the speed, not the output. Two checks on Lean 4.33.1 exports of release v1.2, commit `c3599c05`:

- **`CKChallenge.Challenge`.** The stock and the fast builds wrote the same file: 66,938,973 bytes, sha256
  `83593ce170233f5dc43c2506ec495d33751522193772fa51a917fabf1def3a21`.
- **`CKChallenge.Solution`.** The export is written in 49 chunks of 2 GiB. The stock build re-exported the first 9
  chunks (19,327,352,832 bytes, 18% of the file), and they were byte-identical to the fast build's. The other 40 chunks
  were not compared.

## What depends on the exporter

comparator treats the solution export as untrusted input:

- `compareAt` checks the theorem's statement, and every constant the statement depends on, against the challenge
  export.
- `checkAxioms` checks the axioms.
- A kernel checks every declaration of the solution export.

The trusted side is the challenge export, and the stock exporter writes it byte for byte. So the checks on the file
with sha256 `f7e39d1a…` hold whichever exporter wrote it. What does rely on the fast build and the partial byte check
is that this file is the export of commit `c3599c05`.
