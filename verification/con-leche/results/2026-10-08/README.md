# con-leche check, 2026-10-08: accepted

[con-leche](https://github.com/leanprover/con-leche) is the Lean FRO's external checker with a formal consistency
proof. It accepted the whole export of the solution, made with Lean 4.33.1:

```
con-leche: accepted 22107215 declarations (--verified)
```

| | |
|---|---|
| input | the `lean4export` export (format 3.1.0) of `CKChallenge.Solution`, made with Lean 4.33.1 from commit `c3599c05`: 104,726,218,136 bytes, sha256 `f7e39d1adcb52ecd1b8dfdd96237e374a23b167f0cd8afeecca97b14c68fd3f6`. It is the export of the end-to-end comparator run on Lean 4.33.1 |
| checker | con-leche at commit `67f04630d88718e81aa4d07ab64501f68f105398`, built with Lean v4.35.0-rc3, with the patch below (binary sha256 `a0a6705813cf4114b63385be4f3b844b9496f0595c51829b018af92eea41b000`). Run in its default `--verified` mode, the mode its consistency theorem is about |
| patch | [`con-leche-fuel.patch`](con-leche-fuel.patch) (sha256 `4ebb8a47f2a82754…`). See "The patch" below |
| run | one process with 150 worker threads, 2026-10-08 12:18 to 18:02 UTC: 5.7 h, of which parse 855 s, install 1,085 s and check 18,403 s. 636 CPU-hours, peak memory 954 GiB. Exit code 0 |

**What con-leche checks.** It checks every declaration of the export. The input may contain only the three standard
axioms, and any use of `sorryAx` is refused.

It does not compare the solution's statement with the Formal Conjectures statement. Comparator's `compareAt` does
that, and it passed on this same export on 2026-10-08, in the end-to-end comparator run on Lean 4.33.1.

## The patch

The patch raises three loop step budgets 1000x:

| budget | official | patched |
|---|---|---|
| `whnfLoopFuel` | 10^5 | 10^8 |
| `whnfCoreLoopFuel` | 10^6 | 10^9 |
| `defeqLoopFuel` | 10^5 | 10^8 |

It also updates the one proof that uses the value of `whnfLoopFuel`, a positivity witness in
`ConLeche/Verify/Knot.lean`.

- **Why it is needed.** Without the patch, con-leche stops with the internal error `fuel exhausted: whnf loop` at
  `CKLaneD.Structural.structural_paths._proof_1_1`. That proof is a `decide +kernel` over the leaves of a large tree.
- **Why it can't weaken the check.** Running out of fuel is an internal error (exit 3), never an accept.
- **con-leche's own proofs still hold.** With the patch, all 629 of con-leche's build targets build. Its main theorems
  `ConLeche.no_False_declaration` and `ConLeche.model_exists` depend only on `propext`, `Classical.choice` and
  `Quot.sound`.

## Files

- [`result.json`](result.json): verdict, hashes and timings.
- [`con-leche.stderr`](con-leche.stderr): con-leche's progress log.
- [`con-leche.stdout`](con-leche.stdout): its verdict line.
- [`con-leche-fuel.patch`](con-leche-fuel.patch): the patch.

## Reproducing

1. Build con-leche at the commit above with the patch applied (`lake build con-leche`).
2. Export `CKChallenge.Solution` with `lean4export`, the exporter comparator uses (see `HOW_TO_VERIFY.md`, Step 3).
3. Run `con-leche --verified --jobs=<n> --progress=200000 <export>`.

Memory grows with the number of workers. The run above, with 150 workers, peaked at 954 GiB.
