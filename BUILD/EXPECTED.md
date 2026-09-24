# EXPECTED results of the build, audit and replay

## 1. Build (`BUILD/build_plain.sh`)

- Every module must compile with rc 0 and no error message. `out/.build/summary.json` must show `n_failed: 0`.
- With the default recipes, each output `.olean` should equal `CLEAN_BUILD_HASHES.tsv` (`match` column IDENTICAL),
  except for the 2 `abs` modules (`GeneralCK.Certificates.E8TAxisReparamJet5`, `GeneralCK.Certificates.E8TAxisStableScalar`),
  which are compiled plainly here. Byte equality is a convenience, not a requirement: the acceptance criterion is
  compile + gate + kernel replay.
- `results.tsv` and `summary.json` in `out/.build/` describe only the modules compiled by the last invocation. After a
  restart, compare every `out/<Module/Path>.olean` with `CLEAN_BUILD_HASHES.tsv` for a complete byte comparison.
- Measured by the clean build (2026-09-23; `CLEAN_BUILD_HASHES.tsv` columns lean_wall_s / maxrss_kb):

| quantity | value |
|---|---|
| modules built | 45500 of 45500 |
| sum of per-module lean wall time (≈ core-hours; most compiles are single-threaded) | 721 h (the 45,477 modules with a recorded time; 23 locally built modules have `lean_wall_s = None`) |
| max RSS of one compile | 71.2 GB (`CKRoute.Final`) |
| RSS percentiles p50 / p90 / p99 | 1.8 / 4.2 / 6.9 GB |
| where the modules were compiled | a Google compute cluster 42,579, the build workstation 2,921 |
| `CKRoute.Final` | olean sha256 `43de2287ab0259c0ab294803f81e7cbf7f5ddec9902797071e396d56ce6840be`, 320.0 s, 71.2 GB |

Largest RSS:

| module | max RSS | lean wall |
|---|---|---|
| `CKRoute.Final` | 71.2 GB | 320 s |
| `CKLaneA5.Correction` | 49.4 GB | 118 s |
| `CKLaneA5.Bands` | 45.2 GB | 186 s |
| `GeneralCK.Certificates.LaneRB2WaveV2.Coverage` | 36.2 GB | 776 s |
| `GeneralCK.LaneRB2OwnerActual` | 31.0 GB | 201 s |
| `CKLaneN6.Sub3` | 26.0 GB | 229 s |
| `CKLaneA3X.Step026` | 25.9 GB | 3479 s |
| `CKRoute.Remaining3` | 24.8 GB | 35 s |
| `CKRoute.Remaining3T71` | 24.2 GB | 117 s |
| `CKLaneA3X.Step027` | 22.4 GB | 3223 s |

Longest compiles:

| module | lean wall | max RSS |
|---|---|---|
| `CKLaneA3X.Step026` | 3479 s | 25.9 GB |
| `CKLaneA3X.Step027` | 3223 s | 22.4 GB |
| `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation` | 2196 s | 12.6 GB |
| `GeneralCK.Certificates.E8TAxisProd0611EndpointWitnesses` | 2071 s | 4.4 GB |
| `GeneralCK.Certificates.E8TAxisProd0106EndpointWitnesses` | 2068 s | 4.4 GB |
| `GeneralCK.Certificates.E8TAxisProd0610EndpointWitnesses` | 2063 s | 4.4 GB |
| `GeneralCK.Certificates.E8TAxisProd0050EndpointWitnesses` | 2061 s | 4.3 GB |
| `GeneralCK.Certificates.E8TAxisProd0644EndpointWitnesses` | 2056 s | 4.4 GB |
| `GeneralCK.Certificates.E8TAxisProd0137EndpointWitnesses` | 2056 s | 4.3 GB |
| `GeneralCK.Certificates.E8TAxisProd0587EndpointWitnesses` | 2051 s | 4.3 GB |

- **RAM.** RSS is mostly file-backed: the imported oleans are memory-mapped. The top of the graph imports most of the
  closure: `CKRoute.Final` maps about 77k files (it imports 55,997 modules, and package modules have up to three olean
  parts each), and 69–71 GB were measured for it on the build workstation. Give each near-top job that much free page
  cache. With less, the compile re-reads oleans from disk and slows down sharply.
- **Disk.** The sources take 4.9 GB, and the output root 138.4 GB (121.9 GB `.olean` + 16.5 GB `.ilean`). Plan for
  about 160 GB free in total.
- **Open files.** Each near-top import maps ≈ 77k files. Many of them in parallel can exhaust the system-wide file
  table (`fs.file-max`).
- **Memory maps.** ≈ 77k mappings per near-top process exceed the Linux default `vm.max_map_count` (65,530). Our runs
  used 4,194,304. Lean 4.33.0 reads a file instead when its mapping fails: with 0, 17,634 or 18,634 of the 18,634
  olean mappings of `GeneralCK.Statement` made to fail (an LD_PRELOAD test shim), it compiled with rc 0, no messages
  and a byte-identical olean (RSS 2.73 → 3.25 GB, wall 3.0 → 6.3 s). A real exhaustion of the limit also refuses other
  new mappings, which that test cannot simulate, so a full run at the default limit is untested. Raise the limit
  where possible (`sudo sysctl -w vm.max_map_count=262144`).

## 2. Audit (`BUILD/audit_final.sh`)

It compiles `final/AuditFinal.lean` (`import CKRoute.Final`, `#check`, `#print axioms`) against the freshly built tree
and ends by printing a JSON summary:

```
{"rc": 0, "errors": 0, "type_printed": true, "axioms": ["Classical.choice", "Quot.sound", "propext"], "sorryAx": false, "ok": true}
```

Acceptance is `"ok": true`, which requires rc 0, no error, the type line
`GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar`, and an axiom set of
exactly {propext, Classical.choice, Quot.sound}. The raw Lean messages are in `audit_work/AuditFinal.jsonl`, where
the axiom list may be wrapped over several lines. The three axioms are Lean's standard ones: propositional
extensionality, the axiom of choice, and quotient soundness. There is no `sorryAx`, and no `Lean.ofReduceBool` /
`Lean.trustCompiler`, so nothing relied on `native_decide` or compiled code.

## 3. Gate criteria (applied by the campaign to `CKRoute.Final`)

- compile rc 0, with no error and no `sorry` warning;
- no `sorry`, `admit` or `native_decide`, and no custom `axiom`, in the source;
- `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.

The clean build's gate record for `CKRoute.Final` is `final/clean_final_gate.json` (all_pass).

## 4. Kernel replay (`BUILD/replay_fresh.sh`)

- All 1,225 shards of `replay/plan.tsv` must print `SHARD_REPLAY_OK`, and `summary.json` must show
  `SHARDED_REPLAY_OK` with 45,500 modules replayed exactly once.
- The verdict must be `INCREMENTAL_REPLAY_OK` (0 cached, 45,500 replayed) for a run in a new, empty work directory.
  In a reused directory, shards that already succeeded are not replayed again (see `SOURCE_COMMENT_NOTES.md` §5).
- The top shard (id 1224) must print the axiom line above.
- Cost: ≈ 236 Lean core-hours over the recorded shard runs of the original build; top shard 1:08:47 at 68.5 GB, all
  other shards ≤ 26.3 GB. The replay of the clean rebuild (a finer 4,990-shard plan) needed up to 82.9 GB for its top
  shard (`CKRoute.Final` alone, 59:41). Plan for up to about 83 GB for the top shard.
