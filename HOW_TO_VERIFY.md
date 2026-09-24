# How to verify the Lean proof of the General Courtade–Kumar theorem

```lean
theorem GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar
-- #print axioms: [propext, Classical.choice, Quot.sound]
```

- **Axioms.** The only axioms are Lean's three standard ones. There is no `sorry`, no `native_decide` and no custom
  axiom. Every numerical certificate is checked by Lean's kernel.
- **Size.** 45,500 Lean files, 50.4 million lines. Almost all of it is generated certificate data; the proof code is
  roughly 0.2 million lines.
- **Versions.** Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
- **Our checks (2026-09-23).**
  - Clean rebuild: every one of the 45,500 modules was recompiled from these sources, with no prebuilt compiled files.
  - The final theorem compiled and passed the gate: no sorry, no errors, only the standard axioms.
  - Its compiled file is byte-identical to the original build's.
  - Full kernel replay of the clean rebuild: 4,990/4,990 shards, 45,500 modules, 22,668,080 declarations re-checked,
    0 failures.
  - The verification kit was acceptance-tested by following these steps on Linux.
  - An independent end-to-end run of this kit (full rebuild, audit and replay) is in progress; results will be added.

## What you need

| item | where |
|---|---|
| this repository | `git clone https://github.com/dpwoodru/general-courtade-kumar-lean.git` |
| the release assets of `v1.0` | the GitHub Release page: `sources_v3.tar.zst` (all 45,500 sources), the two trusted package shards `packages-*.tar.zst` (prebuilt Mathlib `db584cd6` and its dependencies; file hashes in `LOCKS/TRUSTED_HASHES.tsv`), `v3_replay_addendum.tar.gz` (our kernel-replay verdict), `SHA256SUMS.txt` |
| Lean 4.33.0 | the official release, e.g. via `elan` (below) |

You may instead fetch and build Mathlib yourself: `LOCKS/REBUILD_TRUSTED_BASE.md`.

## Step 1: read what is claimed (everyone, about 30 minutes)

1. Read `REVIEW_GUIDE.md` §1: the 63-line statement (`GeneralCK/Statement.lean`; a copy is in `browse/`) and the
   Mathlib definitions it uses. Check that it says exactly what the conjecture says. This is the only part a human must
   check; Lean's kernel checks everything else.
2. Optionally continue with §2–4: the final theorem's 18 inputs, the proof skeleton that follows the manuscript, and
   the certificate families (checker, soundness theorem, kernel evaluation).
3. Read `MANUSCRIPT_DEVIATIONS.md`.

## Step 2: machine check (Linux x86-64)

**Requirements.**

| resource | need |
|---|---|
| total compute | about 720 CPU-hours (roughly a day on a 64-core machine); the optional replay adds about 240 CPU-hours |
| RAM | at least 128 GB (256 GB is comfortable). The largest single compile needs about 70 GB; the optional replay's largest shard up to about 83 GB |
| disk | about 160 GB free: the build output alone is 138 GB (121.9 GB `.olean` + 16.5 GB `.ilean`), plus about 15 GB of unpacked inputs and the toolchain |
| software | `git`, `python3` (≥ 3.7), `zstd`, GNU `tar` (≥ 1.31), `sha256sum`, and `curl` or the GitHub CLI `gh` |

- **Platform.** The scripts were run and tested on Linux only. On Windows or macOS, use a Linux machine or WSL2.
- **Open files.** Each Lean process near the top of the dependency graph maps up to about 77,000 files. With many
  parallel jobs, check that the system file limit (`/proc/sys/fs/file-max`) is large; most kernels allow many
  millions.
- **Memory maps.** Lean also maps every imported `.olean`: near the top this is about 77,000 files, more than the Linux
  default `vm.max_map_count` (65,530). We ran with a much higher limit. Lean reads a file instead when a mapping fails
  (we tested this on a small module), but a full run at the default limit was not tested. Where possible, raise it:
  `sudo sysctl -w vm.max_map_count=262144` (check with `cat /proc/sys/vm/max_map_count`).

```bash
git clone https://github.com/dpwoodru/general-courtade-kumar-lean.git
cd general-courtade-kumar-lean
sha256sum -c SHA256SUMS.txt                        # the repository files

# release assets -> ./release/  (either with the GitHub CLI ...)
gh release download v1.0 -R github.com/dpwoodru/general-courtade-kumar-lean -D release
# (... or with curl)
# mkdir -p release && cd release
# for a in SHA256SUMS.txt sources_v3.tar.zst v3_replay_addendum.tar.gz \
#          packages-olean-00-63d3bf7e0d7d49c25608e9bc5aa9ac34ceed871255511e6e80cd16ca93bf0af9.tar.zst \
#          packages-server-private-ir-00-f790c782b21af6394bcbd89e59ac4f9c01881f7372cb001ce161a251b06eb59d.tar.zst; do
#   curl -fLO https://github.com/dpwoodru/general-courtade-kumar-lean/releases/download/v1.0/$a; done
# cd ..
(cd release && sha256sum -c SHA256SUMS.txt)

# Lean 4.33.0, the official release (the build script checks the version and commit d8b18978...)
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.33.0
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean

# trusted base: Mathlib db584cd6 and its dependencies
mkdir -p trusted
for f in release/packages-*.tar.zst; do tar --zstd -xf "$f" -C trusted; done   # -> trusted/packages/<pkg>/

# sources
tar --zstd -xf release/sources_v3.tar.zst                                    # -> sources/ (45,500 files, 4.9 GB)

# quick test (seconds): builds only the statement file
BUILD/build_plain.sh --packages trusted/packages --out out_test --lean $LEAN --target GeneralCK.Statement

# full build (hours), then the audit of the final theorem
BUILD/build_plain.sh --packages trusted/packages --out out --lean $LEAN --jobs 32 --mem-gb 200
BUILD/audit_final.sh  --out out --packages trusted/packages --lean $LEAN

# optional: an independent kernel replay of your own build (about 240 CPU-hours)
BUILD/replay_fresh.sh --out out --packages trusted/packages --lean $LEAN --workers 32
```

Adjust `--jobs` and `--mem-gb` to your machine. The script starts a job only when the measured memory of the running
jobs fits in the budget. It is restart-safe: a module is marked done only after it compiled with rc 0, and re-running
the same command skips done modules. (`out/.build/results.tsv` and `summary.json` describe only the modules compiled
by the last invocation; after a restart, compare every `out/<Module/Path>.olean` with `CLEAN_BUILD_HASHES.tsv` for a
complete byte comparison.) To stop a build, send SIGTERM to its process group.

**What you should see** (full details in `BUILD/EXPECTED.md`):

- **Quick test:** `OK   GeneralCK.Statement rc=0 errors=0 … IDENTICAL`.
- **Build:** every module compiles, and `out/.build/summary.json` shows `n_failed: 0`. The script also compares each
  output with `CLEAN_BUILD_HASHES.tsv`. Byte equality is a convenience, not the acceptance criterion; the 2 modules
  with the `abs` recipe are expected to differ.
- **Audit:** `audit_final.sh` ends by printing this summary:

  ```
  {"rc": 0, "errors": 0, "type_printed": true, "axioms": ["Classical.choice", "Quot.sound", "propext"], "sorryAx": false, "ok": true}
  ```

  It summarizes the two messages Lean printed, which are saved in `audit_work/AuditFinal.jsonl`. Lean may wrap the
  axiom list over several lines:

  ```
  GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar
  'GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

- **Replay (optional):** every shard prints `SHARD_REPLAY_OK`; `replay_work/t2/summary.json` shows
  `SHARDED_REPLAY_OK` with 45,500 modules, `replay_work/t2/verdict.json` shows `INCREMENTAL_REPLAY_OK`, and the top
  shard prints the axiom line above.

**Our replay verdict.** `v3_replay_addendum.tar.gz` contains our kernel replay of the clean rebuild (4,990 shards: 4,954
run on a Google compute cluster and 36 on the build workstation), an independent recount from the shard outputs, the
per-shard index and the top shard's output. Check it with
`tar -xzf release/v3_replay_addendum.tar.gz && (cd v3_replay_addendum && sha256sum -c SHA256SUMS.txt)`.

**The trust base.** You trust:
- the Lean 4.33.0 kernel;
- Mathlib `db584cd6` (you can fetch it yourself instead of using the prebuilt packages);
- the 63-line statement.

The 45,500 campaign modules are not trusted: they are rebuilt and checked by the kernel.
