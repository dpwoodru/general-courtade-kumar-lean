# Changelog and errata

## Release v1.1 (2026-10-01): sources in the repository, standard Lake build

The proof is unchanged. The 45,500 Lean sources are byte-identical to `sources_v3.tar.zst` of v1.0 (sha256
`3f09b23672e3a29cd6533a4004b8fd0d92e5edd17845478d327ac1aeb0a45589`), and each matches its sha256 in
`SOURCES_MANIFEST.tsv`.

- **Sources in the repository.** All 45,500 `.lean` files are now in the repository at the root (`GeneralCK/`,
  `CKRoute/`, `CKLane*/`, `E8*.lean`), so no download or archive is part of the chain of trust. `browse/` (copies of
  1,359 of them) is removed; its list of readable files is now `READABLE_FILES.md`.
- **Lake project at the root.** `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` moved from `BUILD/lake/` to
  the root, so `git clone`, `lake exe cache get` and `lake build` build the whole proof. An independent agent ran the
  standard Lake build of these sources with the v1.0 Lake files (`lake build CKRoute.Final`, completed 2026-10-01):
  all 45,500 modules, no errors, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound`. `lean-toolchain` and
  `lake-manifest.json` are unchanged. Changes to `lakefile.toml` (header comment aside):
  - the default target is the new `FinalCheck` instead of `CKRoute`. `FinalCheck.lean` imports `CKRoute.Final` and
    checks the type and the axioms of the final theorem with `#guard_msgs`, so `lake build` fails unless both are as
    expected. We compiled it against the clean rebuild's compiled files: rc 0, while a copy expecting a different axiom
    list fails;
  - the 37 libraries without a root file `<Name>.lean` now have `globs = ["<Name>.+"]` instead of
    `["<Name>", "<Name>.+"]`. The bare `"<Name>"` glob named a module without a source file, so `lake build <Name>`,
    or a bare `lake build` with the old default target `CKRoute`, would have ended with "some modules have bad
    imports". `lake build CKRoute.Final`, as tested, is not affected: its modules are found through the `.+` globs,
    which are kept;
  - a new library `CKChallenge`, with sources in `verification/comparator/`, which is not built by default.
  The Mathlib `[[require]]` and the library names are unchanged, so compile options and module resolution are those
  of the tested build.
- **comparator.** New `verification/comparator/`: the Formal Conjectures statement as a comparator challenge, a
  solution derived from the final theorem, and `config.json`.
- **formalization.yaml.** New, in the mathlib-initiative v0.4 format; it validates against that format's JSON schema.
- **Documentation.** `README.md` and `HOW_TO_VERIFY.md` now lead with the Lake build. The plain-`lean` kit in `BUILD/`,
  which reproduces the published per-module hashes, is now optional and takes `--sources .`. Paths are updated in
  `REVIEW_GUIDE.md`, `SOURCE_COMMENT_NOTES.md`, `MANUSCRIPT_DEVIATIONS.md`, `provenance/` and
  `LOCKS/REBUILD_TRUSTED_BASE.md`.
- `SHA256SUMS.txt` now also lists the sources (still every file except `README.md`). `.gitignore` ignores `/.lake/`
  and `/.verify-work/`, and no longer `/sources/`.
- No `.lean` source, table or release asset of v1.0 changed; the v1.0 release assets remain available.

## Source-comment errata (2026-09-24, after release v1.0)

- New `SOURCE_COMMENT_NOTES.md`: corrections, with links, for six out-of-date or imprecise comments and notes raised in a
  coauthor review of commit `95f208b`.
- No `.lean` file was edited, so every source and compiled checksum and every verification record stays valid;
  `SOURCE_COMMENT_NOTES.md` explains why.
- `HOW_TO_VERIFY.md`, `BUILD/EXPECTED.md`: a fully fresh kernel replay needs a new, empty work directory.
- `provenance/E8TAxisZero0082Root/README.md`: tactic name corrected (`norm_num`, not `simp only`).
- New `provenance/PsiCornerBoundaryRefutation/`: the historical file that a source comment cites. It is outside the
  source set and is not imported by the final theorem; it was compile-checked against this release.
- No proof file, table or release asset changed.

## Documentation update (2026-09-24, after release v1.0)

- `README.md`, `MANUSCRIPT_DEVIATIONS.md`: reference and citation for the paper, arXiv:2609.24931.
- `SHA256SUMS.txt` no longer lists `README.md`, so that README updates (for example new verification results) do not
  invalidate the repository checksums.
- No proof file, table or release asset changed.

## GitHub release 1 (2026-09-24)

The proof content is unchanged from the v3 release: `sources_v3.tar.zst` (sha256
`3f09b23672e3a29cd6533a4004b8fd0d92e5edd17845478d327ac1aeb0a45589`) and the two trusted package shards are
byte-identical to what was compiled and kernel-checked.

This release repackages the verification kit for GitHub:
- **Repository.** The kit: build scripts, locks, manifests, the final theorem, the replay harness, the review guide,
  and `browse/` with read-only copies of the readable proof code.
- **Release assets.** The complete sources, the trusted packages and the replay verdict.
- **Instructions.** `HOW_TO_VERIFY.md` now downloads from the GitHub Release instead of a zip archive, and has all the
  errata below applied.
- **Paths.** Machine-specific paths in records and tables were replaced by neutral descriptions; the numbers and
  verdicts are unchanged. For example:
  - the `backend` column of `CLEAN_BUILD_HASHES.tsv` now reads `cluster` / `workstation`;
  - the label of the 2 `abs` recipes now reads `abs:historical-absolute-path`, and the build compiles those 2 modules
    plainly exactly as before.

## Earlier releases

| release | what it is |
|---|---|
| v1 | the campaign archive: the historical build of the closure |
| v2 | the historical compiled files (a 35.7 GB bundle) with a kit that checks them without rebuilding (T1: compile the final theorem against the bundle; T2: kernel replay) |
| v3 | the canonical clean-build release: the exact source set from which all 45,500 modules were recompiled with plain `lean` into an empty output root; per-module output hashes; the tested build driver; the review guide |
| v3 replay addendum | the kernel replay of the clean rebuild: `SHARDED_REPLAY_OK`, 4,990 / 4,990 shards, 45,500 modules, 22,668,080 declarations (here: `v3_replay_addendum.tar.gz`) |
| share archive r1, r2 | v3 + the addendum + the trusted packages as one zip for coauthors. r2 fixed read-only permissions after unzipping and clarified the instructions |

**Clean build versus the original build.** Of the 45,500 compiled files:
- 39,447 are byte-identical to the original build;
- 759 differ only by relocation (base address);
- 5,294 differ in bytes only through module names or embedded source paths (canonical names instead of historical
  staging names), or through one historical source variant.

Every one of them compiles from the published source, and the whole clean tree kernel-replays. `CKRoute.Final` is
byte-identical in both builds.

**The source variant.** The original build had compiled one module, `GeneralCK.Certificates.E8TAxisZero0082Root`, from
a slightly different revision of its source. The two revisions differ only in the last two lines of the proof of
`positiveAt`; the statement is identical at kernel level. The published source is the one the clean build compiled;
the variant is kept in `provenance/`.

## Errata to the share archive r2 and the v3 documents

All are corrected in this repository.

| # | where | correction |
|---|---|---|
| E1 | disk requirement (`HOW_TO_VERIFY.md`, `BUILD/EXPECTED.md`, v3 changelog) | A full run needs about **160 GB** free, not 130 GB. The build output alone is 138.4 GB (121.9 GB `.olean` + 16.5 GB `.ilean`); the earlier "≈ 114 GB" was the `.olean` total in GiB, without the `.ilean` files |
| E2 | memory maps (`HOW_TO_VERIFY.md`, `BUILD/EXPECTED.md`) | Near-top Lean processes map about 77,000 `.olean` files, more than the Linux default `vm.max_map_count` (65,530). Lean falls back to reading a file when its mapping fails (tested on a small module, byte-identical output), but a full run at the default limit was not tested; raise the limit where possible |
| E3 | replay addendum, shard counts | The 4,990 shard outputs were produced 4,954 on a Google compute cluster and 36 on the build workstation, not "4,955 / 35". The top shard (4989) ran on the workstation. The verdict is unchanged |
| E4 | `BUILD/EXPECTED.md` §2 | The audit prints a JSON summary (acceptance: `"ok": true`), not the two raw Lean lines; the raw axiom list may be wrapped over several lines |
| E5 | `BUILD/EXPECTED.md` §4 | The top replay shard can need up to about 83 GB (82.9 GB measured on the clean rebuild), not only the 68.5 GB measured on the original build |
| E6 | build restarts | `out/.build/results.tsv` and `summary.json` describe only the modules compiled by the last invocation; after a restart, compare every output with `CLEAN_BUILD_HASHES.tsv` for a complete byte comparison |
| E7 | `CLEAN_BUILD_HASHES.tsv` | 23 locally built modules have `lean_wall_s = None` (not recorded); the "721 h" total is over the other 45,477 modules |
| E8 | `CHANGES_r2.md` | "The literal steps are being re-run on r2 itself": that re-run is done and passed |
