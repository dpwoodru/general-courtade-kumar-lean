# replay/ — layered-shard kernel replay

| file | role |
|---|---|
| `ReplayShard.lean` | the frozen replay harness (sha256 `d117c305e2eeaf2aac41665970cfed3d796ea6b812a3a2a8d4510fe9f81e8970`, unmodified since the campaign) |
| `plan.tsv` | the replay plan: 1,225 layered shards covering all 45,500 modules (`plan_meta.json`: limits and counts) |
| `replay_bundle.py` | the driver: runs every shard and checks coverage and axiom lines |
| `replay_cache.py` | computes the final verdict (`verdict` subcommand); its other subcommands served the campaign's incremental replay and are not used here |

Run it with `BUILD/replay_fresh.sh --out out --packages trusted/packages --lean $LEAN --workers N` after a full build.

## What a sharded replay proves

* **Target and trusted modules.** Target modules are every module of the closure outside the trusted packages. The
  trusted packages are Init, Lean, Std, Lake, Mathlib, Batteries, Aesop, Qq, ProofWidgets, Plausible, ImportGraph and
  LeanSearchClient.
* **Height.** A module has height 0 if it imports only trusted modules. Otherwise its height is 1 + the maximum height
  of its target imports.
* **Plan.** The plan cuts every height layer into shards, each bounded by a maximum number of constants and modules.
  The output is one `id<TAB>height<TAB>m1,m2,...` line per shard.
* **Shard run.** `lean --run ReplayShard.lean --shard PLAN K` does the following:
  * imports the union of the shard's direct imports at trust level 0;
  * refuses to run if any shard module is already in that base environment, or imports another module of the same
    shard;
  * sends every constant of every shard module through the kernel (`Lean.Environment.replay`: definitions and
    theorems re-typechecked, constructors and recursors compared);
  * prints `MOD <m> consts=<n>` per module and finally `SHARD_REPLAY_OK K`.
* **Soundness.** With a fixed LEAN_PATH, every module of the plan is replayed exactly once, against the constants of
  its imports as stored in the same olean files. By induction on height, every constant of the closure is
  kernel-checked relative to kernel-checked dependencies.
* **Driver check.** The driver requires `SHARD_REPLAY_OK` from every shard, every plan module replayed exactly once
  with no duplicate, and the axiom lines of the `--axioms` declarations, printed by the shard that replays them. It
  then writes `summary.json` with the result `SHARDED_REPLAY_OK`.
* **Custom axioms.** Declared axioms are not listed per shard. Any custom axiom a claimed declaration depends on
  appears in that declaration's axiom line.

## Controls and validation (campaign records)

* **Negative and positive controls** with the unmodified harness:
  * an ill-typed constant (inserted via `debug.skipKernelTC`) gives REPLAY_FAIL, driver rc 1;
  * a consumer replayed over the wrong dependency bytes: the dependency shard is OK, the consumer shard REPLAY_FAILs,
    driver rc 1;
  * a consumer over its own dependency gives SHARDED_REPLAY_OK, rc 0.
* **Independent re-run.** An independent verifier re-ran the same controls with identical results.
* **Sharded versus monolithic.** A sharded replay of `CKRoute.Bindings` (85/85 shards OK, 323 modules each exactly
  once, 7,275 constants) agrees with a single-process replay of the same closure (REPLAY_OK, 323 modules, 7,275
  constants).
