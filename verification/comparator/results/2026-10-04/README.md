# Full comparator run, 2026-10-04: accepted

comparator accepted [`verification/comparator/config.json`](../../config.json) in full:

- `CKChallenge.Solution` proves the challenge statement `CourtadeKumar.courtade_kumar`, which is the Formal Conjectures statement.
- The proof uses only `propext`, `Quot.sound` and `Classical.choice`.
- The Lean kernel replayed the solution's whole exported environment.

The last lines of [`comparator_output.txt`](comparator_output.txt):

```
[ReplayStats] mode=parallel replay_ms=283239264 checked_env_consts=22109794 replayed_decls=22109791 thm_tasks=9654755 postponed_ctor_rec=2579 env_digest=12041597716954051677 decl_counts=(axiom=3,defn=12451223,thm=9654755,opaque=42,quot=4,induct=1188,ctor=1389,rec=1190)
Lean default kernel accepts the solution
Your solution is okay!
```

| | |
|---|---|
| checks | `compareAt`: the solution's theorem has the challenge's statement, and every constant the statement depends on is identical to the challenge's. `checkAxioms`: only the three permitted axioms. Kernel replay: all 22,109,794 constants of the solution's export, 9,654,755 of them theorems |
| inputs | `lean4export` exports of `CKChallenge.Challenge` (66,938,973 bytes, sha256 `f6afc184…`) and `CKChallenge.Solution` (104,726,244,087 bytes, sha256 `b46814de…`). They were made on 2026-09-30/10-01 with Lean 4.33.0 and Mathlib v4.33.0, from this repository's sources: the 45,500 proof modules (the v1.0 `sources_v3` set, byte-identical to the `.lean` files here) and the `CKChallenge` modules |
| kernel | Lean 4.33.1 (commit `819816b2…`), which re-checks every declaration of the exports from scratch |
| comparator | comparator with the opt-in parallel kernel replay proposed in [leanprover/comparator#95](https://github.com/leanprover/comparator/issues/95), built with Lean 4.33.1 (binary sha256 `3bc16bba…`) |
| run | one uninterrupted process on one machine, 2026-10-01 07:42 UTC to 2026-10-04 19:05 UTC (83.4 h, 342 threads, peak memory 940 GiB). Exit code 0, empty stderr |

[`result.json`](result.json) has the full hashes and figures. `comparator_output.txt` is the complete output, except that the two input file paths are shortened to `<work>/`. The original output was 4,985 bytes, sha256 `6e8b891b…`.

## Caveats

- **Parallel replay.** Stock comparator replays the environment on one core. For this ~100 GB export that was projected to take one to two weeks.
  - The parallel replay of comparator#95 checks each theorem's proof in a separate task, against the environment just before that theorem, with the same kernel call. Only the order of the theorem checks changes.
  - It has not been reviewed upstream yet.
- **Lean 4.33.0 exports.** The exports were made with Lean 4.33.0 and re-checked by the Lean 4.33.1 kernel. A second, end-to-end run, on exports made with Lean 4.33.1 from commit `c3599c05`, started on 2026-10-04 at 19:16 UTC. Its result will be added here.
- **Cross-check.** A separate run used a different build of the parallel replay, split into 20 processes. Each process rebuilt the full environment and kernel-checked one twentieth of the theorems, definitions and opaque constants. It also accepted the same exports, with identical declaration counts.
