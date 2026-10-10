# How to verify the Lean proof of the General Courtade–Kumar theorem

```lean
theorem GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar
-- #print axioms: [propext, Classical.choice, Quot.sound]
```

- **Axioms.** The only axioms are Lean's three standard ones. There is no `sorry`, no `native_decide` and no custom
  axiom. Every numerical certificate is checked by Lean's kernel.
- **Size.** 45,500 Lean files, 50.4 million lines. Almost all of it is generated certificate data; the proof code is
  roughly 0.2 million lines (`READABLE_FILES.md`).
- **Versions.** Lean 4.33.1 and Mathlib `v4.33.1` (`0df444a360eaa60ab8c11dca51a86af692955474`, which is Mathlib v4.33.0
  `db584cd6` plus the toolchain bump), pinned in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. Lean
  4.33.1 fixes kernel soundness bugs in 4.33.0.

## Step 1: read what is claimed (everyone, about 30 minutes)

1. Read `REVIEW_GUIDE.md` §1: the 63-line statement (`GeneralCK/Statement.lean`) and the Mathlib definitions it uses.
   Check that it says exactly what the conjecture says. This is the only part a human must check; Lean's kernel checks
   everything else.
2. Optionally continue with §2–4: the final theorem's 18 inputs, the proof skeleton that follows the manuscript, and
   the certificate families (checker, soundness theorem, kernel evaluation).
3. Read `MANUSCRIPT_DEVIATIONS.md`.

## Step 2: build with Lake (Linux x86-64)

**Requirements.**

| resource | need |
|---|---|
| software | `git`, [elan](https://github.com/leanprover/elan) (installs Lean 4.33.1 from `lean-toolchain`), a network connection (GitHub and the Mathlib cache) |
| compute | about 1,200 CPU-hours; our Lean 4.33.1 run took 5.0 hours with 342 parallel jobs on a 380-core machine |
| memory | most modules need a few GiB, the largest about 42 GiB; Lake has no memory budget, so set `LEAN_NUM_THREADS` (the number of parallel jobs) to fit your machine. Our run averaged about 4.1 GiB of resident memory per job at its peak |
| disk | about 300 GB for `.lake/` (289 GB in our run) |

- **Platform.** We tested on Linux only. On Windows or macOS, use a Linux machine or WSL2.
- **Memory maps.** Lean maps every imported `.olean`: near the top of the import graph this is about 77,000 files, more
  than the Linux default `vm.max_map_count` (65,530). Our runs used a much higher limit. Lean reads a file instead when a
  mapping fails (we tested this on a small module), but a full run at the default limit was not tested. Where possible,
  raise it: `sudo sysctl -w vm.max_map_count=262144` (check with `cat /proc/sys/vm/max_map_count`).
- **Open files.** With many parallel jobs, check that the system file limit (`/proc/sys/fs/file-max`) is large; most
  kernels allow many millions.

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"

git clone https://github.com/dpwoodru/general-courtade-kumar-lean.git
cd general-courtade-kumar-lean
sha256sum -c --quiet SHA256SUMS.txt     # optional: every repository file except README.md

lake exe cache get                      # prebuilt Mathlib v4.33.1 and its dependencies, from the Mathlib cache
lake build GeneralCK.Statement          # quick test (seconds): the statement file and its Mathlib imports
LEAN_NUM_THREADS=32 lake build          # the whole proof: 45,500 modules, then FinalCheck
lake env lean final/AuditFinal.lean     # optional: print the type and the axioms of the final theorem again
```

`lake build` is restart-safe: if it is interrupted, run it again and it continues where it stopped.

**What you should see.**

- **Quick test:** `Build completed successfully`.
- **Build:** several thousand linter and deprecation warnings (unused `simp` arguments, deprecated lemma names and the
  like), which do not affect the result, and no errors. The default target `FinalCheck.lean` checks the type and the
  axioms of the final theorem with `#guard_msgs`, so the build fails unless both are as expected. It ends with

  ```
  info: FinalCheck.lean:…: 'GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  Build completed successfully (… jobs).
  ```

  (Lean breaks the axiom list over several lines.) A second `lake build` rebuilds nothing.
- **Audit (optional):**

  ```
  GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar
  'GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

## Step 3 (optional): comparator

[comparator](https://github.com/leanprover/comparator) checks that a solution module proves exactly the statement of a
trusted challenge module, using only permitted axioms, and replays the solution's whole environment (Mathlib
included) through the Lean kernel. `verification/comparator/` contains:

| file | what |
|---|---|
| `CKChallenge/Defs.lean` | the definitions of the Formal Conjectures statement ([google-deepmind/formal-conjectures#6688](https://github.com/google-deepmind/formal-conjectures/pull/6688)): `Cube`, `binEntropyBits`, `bsc`, `jointProb`, `entropy`, `mutualInfo`, with sanity tests (the dictator attains the bound). It imports only Mathlib |
| `CKChallenge/Challenge.lean` | the trusted challenge: `CourtadeKumar.courtade_kumar`, stated with `sorry` |
| `CKChallenge/Bridge.lean` | `CourtadeKumar.of_general`: `GeneralCK.GeneralCourtadeKumar` implies the challenge statement (the two sets of definitions have identical bodies) |
| `CKChallenge/Solution.lean` | the same theorem, proved by `of_general` applied to the final theorem |
| `config.json` | challenge `CKChallenge.Challenge`, solution `CKChallenge.Solution`, theorem `CourtadeKumar.courtade_kumar`, axioms `propext`, `Quot.sound`, `Classical.choice` |

They form the library `CKChallenge` of the root Lake project (`srcDir = "verification/comparator"`), which is not
part of the default target. After Step 2, build comparator and lean4export at tag `v4.33.0` with this repository's
toolchain (Lean 4.33.1, as in the FLT repository's `verification/comparator/run.sh`), put `lean4export` and `landrun` on `PATH` (see comparator's README; its `scripts/fake-landrun.sh` runs
without a sandbox), and run from the repository root:

```bash
lake build CKChallenge.Challenge CKChallenge.Solution
lake env /path/to/comparator/.lake/build/bin/comparator verification/comparator/config.json
```

Expect a long run: the exported environment of the solution is about 100 GB, and stock comparator replays it through
the kernel on one core (projected at one to two weeks). Status: the full run on `config.json` was accepted on
2026-10-04 (`Your solution is okay!`), after 83 hours on one machine with the opt-in parallel kernel replay proposed in
[leanprover/comparator#95](https://github.com/leanprover/comparator/issues/95), which is not yet reviewed upstream. Its
exports were made with Lean 4.33.0 and replayed by the Lean 4.33.1 kernel; the record is in
[`verification/comparator/results/2026-10-04/`](verification/comparator/results/2026-10-04/). An end-to-end run on
exports made with Lean 4.33.1 is in progress. Earlier, stock comparator accepted the bridge `CourtadeKumar.of_general`
and the tests of the definitions, on Lean 4.33.1 and on Lean 4.33.0 (there with both the Lean kernel and nanoda).

Independently, the Lean FRO's external checker [con-leche](https://github.com/leanprover/con-leche), which has a formal
consistency proof, accepted the whole Lean 4.33.1 export of `CKChallenge.Solution` on 2026-10-10, unmodified, at
commit `65e74db`. The record and how to reproduce it are in
[`verification/con-leche/results/2026-10-10/`](verification/con-leche/results/2026-10-10/). An earlier run on
2026-10-08, with its loop step budgets raised 1000x by a local patch before upstream raised them, gave the same verdict;
its record and the patch are in [`verification/con-leche/results/2026-10-08/`](verification/con-leche/results/2026-10-08/).

## Step 4 (optional): reproduce the published hashes with plain `lean`

The v1.0 verification kit compiles every module with plain `lean` (no Lake) in topological order, with a memory
budget, and compares each output with `CLEAN_BUILD_HASHES.tsv` byte for byte. It reproduces the v1.0 build exactly,
so it uses Lean 4.33.0, whose kernel has soundness bugs that 4.33.1 fixes: use it to reproduce the published hashes,
not as the main check. It needs the v1.0 release assets for the
prebuilt trusted base (or see `LOCKS/REBUILD_TRUSTED_BASE.md`), about 720 CPU-hours, at least 128 GB RAM and about
160 GB of disk. The sources are now in the repository, so pass `--sources .`:

```bash
# release assets of v1.0 -> ./release/
gh release download v1.0 -R github.com/dpwoodru/general-courtade-kumar-lean -D release
(cd release && sha256sum -c SHA256SUMS.txt)
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean   # the build script checks version and commit d8b18978...
mkdir -p trusted && for f in release/packages-*.tar.zst; do tar --zstd -xf "$f" -C trusted; done   # -> trusted/packages/<pkg>/

BUILD/build_plain.sh --sources . --packages trusted/packages --out out_test --lean $LEAN --target GeneralCK.Statement
BUILD/build_plain.sh --sources . --packages trusted/packages --out out --lean $LEAN --jobs 32 --mem-gb 200
BUILD/audit_final.sh  --out out --packages trusted/packages --lean $LEAN

# optional: an independent kernel replay of your own build (about 240 CPU-hours), in a NEW, empty work directory
# (default ./replay_work, or --work DIR; see SOURCE_COMMENT_NOTES.md §5)
BUILD/replay_fresh.sh --out out --packages trusted/packages --lean $LEAN --workers 32
```

`BUILD/EXPECTED.md` describes the expected output. In short: the quick test prints
`OK   GeneralCK.Statement rc=0 errors=0 … IDENTICAL`; the build ends with `n_failed: 0` in `out/.build/summary.json`, and
every output except the 2 modules with the `abs` recipe is byte-identical to `CLEAN_BUILD_HASHES.tsv`; the audit
prints `{"rc": 0, "errors": 0, "type_printed": true, "axioms": ["Classical.choice", "Quot.sound", "propext"],
"sorryAx": false, "ok": true}`; every replay shard prints `SHARD_REPLAY_OK` and `replay_work/t2/verdict.json` shows
`INCREMENTAL_REPLAY_OK`. The script is restart-safe; after a restart, compare every `out/<Module/Path>.olean` with
`CLEAN_BUILD_HASHES.tsv` for a complete byte comparison. `v3_replay_addendum.tar.gz` (a v1.0 release asset) contains
our own kernel replay of the clean rebuild.

## The trust base

You trust:
- the Lean 4.33.1 kernel;
- Mathlib `v4.33.1` and its dependencies, as fetched by Lake;
- the 63-line statement.

The 45,500 modules of this repository are not trusted: they are rebuilt and checked by the kernel.
