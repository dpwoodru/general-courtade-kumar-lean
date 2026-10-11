# comparator on the Lean 4.33.1 exports: `compareAt` and `checkAxioms` passed 2026-10-08, full run accepted 2026-10-11

On the Lean 4.33.1 exports of release v1.2 (commit `c3599c05`), comparator's statement comparison and axiom check
passed ([`compare_and_axioms_output.txt`](compare_and_axioms_output.txt)):

```
Parsed challenge export (16336 constants). Parsing solution export stream...
Parsed solution export (22109794 constants). Running Comparator.compareAt...
Comparator.compareAt passed. Running Comparator.checkAxioms...
Comparator.checkAxioms passed.
```

- `compareAt`: in the solution export, `CourtadeKumar.courtade_kumar` has the challenge's statement, and every constant
  that the statement depends on is identical to the challenge's. The permitted axioms and the kernel's primitive
  constants are compared too.
- `checkAxioms`: the theorem depends only on `propext`, `Quot.sound` and `Classical.choice`.

The solution export is the file that unmodified con-leche accepted in full on 2026-10-10
([`../../../con-leche/results/2026-10-10/`](../../../con-leche/results/2026-10-10/)): sha256 `f7e39d1a…`. So the statement
and axiom checks here and con-leche's proof check are on the same file.

| | |
|---|---|
| config | [`../../config.json`](../../config.json): challenge `CKChallenge.Challenge`, solution `CKChallenge.Solution`, theorem `CourtadeKumar.courtade_kumar`, permitted axioms `propext`, `Quot.sound`, `Classical.choice`, nanoda off. The run added `challenge_export_file` and `solution_export_file`, pointing at the two exports below |
| challenge export | `CKChallenge.Challenge`: 66,938,973 bytes, sha256 `83593ce170233f5dc43c2506ec495d33751522193772fa51a917fabf1def3a21`. The stock and the fast lean4export builds wrote this same file |
| solution export | `CKChallenge.Solution`: 104,726,218,136 bytes, sha256 `f7e39d1adcb52ecd1b8dfdd96237e374a23b167f0cd8afeecca97b14c68fd3f6`. Written by the fast lean4export build; the first 9 of its 49 2-GiB chunks are byte-identical to the stock build's |
| exports made from | the Lean 4.33.1 build of commit `c3599c05181ad357331b701edf8fd8ec75c88305` with Mathlib v4.33.1, after checking `SHA256SUMS.txt` and `SOURCES_MANIFEST.tsv`. The build job exported the solution twice, by 2026-10-04 and again on 2026-10-08 after a restart, with the same sha256 |
| comparator | binary sha256 `3bc16bba07de7a953e408342bf56a11ade76c09eda166010b665422c71040433`: tag `v4.33.0` plus [`../../tools/comparator-v4.33.0-parallel-replay-v4331.patch`](../../tools/comparator-v4.33.0-parallel-replay-v4331.patch), built with Lean 4.33.1. The code of `compareAt` and `checkAxioms` is upstream's |
| lean4export | tag `v4.33.0` (commit `15f6055e…`): stock build, and fast build with [`../../tools/lean4export-v4.33.0-fast-v4331.patch`](../../tools/lean4export-v4.33.0-fast-v4331.patch) |
| Lean | 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, official release binaries (`lean` sha256 `e8baaa71…`) |
| run | Google compute cluster, 2026-10-08 UTC. The inputs were re-hashed at 02:18:59, and comparator started at 02:19:14. `compareAt` had passed by 05:45:59 and `checkAxioms` by 06:41:46. These times come from the run's once-a-minute monitor ([`run_log_excerpt.txt`](run_log_excerpt.txt)) |

[`../../tools/`](../../tools/) has the exact upstream revisions, the two patches, the binary hashes and the byte-identity
checks. [`result.json`](result.json) has the hashes and times in machine-readable form. In the text files, the run's
working directory is shortened to `<work>/`, and the host name and task number are replaced by `<host>` and `<task>`.

## Kernel replay: accepted, 2026-10-11

After `checkAxioms`, the same process replayed the whole solution export through the Lean 4.33.1 kernel, with the
parallel replay of [leanprover/comparator#95](https://github.com/leanprover/comparator/issues/95) (not yet reviewed
upstream). It accepted. The last lines of [`comparator_output.txt`](comparator_output.txt), the complete output:

```
[ReplayStats] mode=parallel replay_ms=271211118 checked_env_consts=22109794 replayed_decls=22109791 thm_tasks=9654755 postponed_ctor_rec=2579 env_digest=12720708470609912041 decl_counts=(axiom=3,defn=12451223,thm=9654755,opaque=42,quot=4,induct=1188,ctor=1389,rec=1190)
Lean default kernel accepts the solution
Your solution is okay!
```

- **Run:** one uninterrupted process, 2026-10-08 02:19 UTC to 2026-10-11 10:35 UTC: 80.3 h, 342 threads,
  15,023 CPU-hours, peak memory 897 GiB. Exit code 0, empty stderr. The original output was 4,985 bytes, sha256
  `2e7b8c917e1dbb08e8b428d8933d42f0dfcf2070c6795349e7d3890f2f899e6f`.
- **Second check of the proofs.** This replay is a second proof check of this file, with Lean's own kernel, next to
  con-leche's. The declaration counts are those of the 2026-10-04 run on the Lean 4.33.0 exports.
- **Environment digest.** The digest differs from that run's, as expected: the two solution exports are different files.
