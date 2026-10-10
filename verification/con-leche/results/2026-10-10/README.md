# con-leche check, 2026-10-10: accepted, unmodified con-leche

[con-leche](https://github.com/leanprover/con-leche) is the Lean FRO's external checker with a formal consistency
proof. Unmodified con-leche accepted the whole export of the solution, made with Lean 4.33.1:

```
con-leche: accepted 22107215 declarations (--verified)
```

| | |
|---|---|
| input | the `lean4export` export (format 3.1.0) of `CKChallenge.Solution`, made with Lean 4.33.1 from commit `c3599c05`: 104,726,218,136 bytes, sha256 `f7e39d1adcb52ecd1b8dfdd96237e374a23b167f0cd8afeecca97b14c68fd3f6`. It is the export of the end-to-end comparator run on Lean 4.33.1, and the input of the [2026-10-08 run](../2026-10-08/) |
| checker | con-leche at commit `65e74db49e89ad2bbd1e90aa4f784954db41fa3a` (`master` on 2026-10-09), unmodified, built with Lean v4.35.0-rc3 (binary sha256 `058e8b0cd946813056ab43de1f246d1c24ee17a9ed46276b48bd709119bdf3b9`). Run in its default `--verified` mode, the mode its consistency theorem is about |
| run | one process with 150 worker threads, 2026-10-09 19:41 to 2026-10-10 01:48 UTC: 6.1 h, of which parse 1,013 s, install 850 s and check 19,590 s. 572 CPU-hours, peak memory 967 GiB. Exit code 0 |

**What con-leche checks.** It checks every declaration of the export. The input may contain only the three standard
axioms, and any use of `sorryAx` is refused.

It does not compare the solution's statement with the Formal Conjectures statement. Comparator's `compareAt` does
that, and it passed on this same export on 2026-10-08, in the end-to-end comparator run on Lean 4.33.1.

**No patch.** The [2026-10-08 run](../2026-10-08/) needed a local patch that raised con-leche's loop step budgets,
because the con-leche of that time stopped on a step limit at `CKLaneD.Structural.structural_paths._proof_1_1`.
Upstream then raised the three budgets to 2^62 in
[`b0a170c`](https://github.com/leanprover/con-leche/commit/b0a170c9693137a802237f23b619649b388f141e), after
[leanprover/con-leche#10](https://github.com/leanprover/con-leche/issues/10), so this run uses con-leche as published.
At this commit all 630 of con-leche's build targets build, and its main theorems `ConLeche.no_False_declaration` and
`ConLeche.model_exists` depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Files

- [`result.json`](result.json): verdict, hashes and timings.
- [`con-leche.stderr`](con-leche.stderr): con-leche's progress log.
- [`con-leche.stdout`](con-leche.stdout): its verdict line.

## Reproducing

1. Build con-leche at the commit above (`lake build con-leche`).
2. Export `CKChallenge.Solution` with `lean4export`, the exporter comparator uses (see `HOW_TO_VERIFY.md`, Step 3).
3. Run `con-leche --verified --jobs=<n> --progress=200000 <export>`.

The run above, with 150 workers, peaked at 967 GiB of memory.
