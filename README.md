# The General Courtade–Kumar theorem in Lean 4

This repository contains a complete, machine-checked Lean 4 proof of the general Courtade–Kumar inequality: for
every n, every Boolean function f on {0,1}ⁿ and every crossover probability p ∈ [0, 1], the mutual information between
f(X) and the output Y of a binary symmetric channel with crossover p satisfies I(f(X); Y) ≤ 1 − H(p).

It formalizes the main theorem of Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair and D. P. Woodruff,
[*A Proof of the Most Informative Boolean Function Conjecture*](https://arxiv.org/abs/2609.24931), arXiv:2609.24931
(2026).

```lean
theorem GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar
-- #print axioms: [propext, Classical.choice, Quot.sound]
```

The proposition `GeneralCK.GeneralCourtadeKumar` is defined in the 63-line file
[`GeneralCK/Statement.lean`](browse/GeneralCK/Statement.lean):

```lean
def GeneralCourtadeKumar : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ),
    0 ≤ p → p ≤ 1 → mutualInformation f p ≤ 1 - H p
```

Here `Cube n := Fin n → Bool`, `H p := Real.binEntropy p / Real.log 2` (binary entropy in bits), and
`mutualInformation` is computed from the finite joint and marginal masses of (f(X), Y), with X uniform and independent
bit flips of probability p. The definitions use only Mathlib's `Real.binEntropy`, `Real.log`, `Real.negMulLog` and
finite sums. [`REVIEW_GUIDE.md`](REVIEW_GUIDE.md) §1 walks through them.

- **Axioms.** Only Lean's three standard axioms: propositional extensionality, choice, and quotient soundness.
  There is no `sorry`, no `native_decide` (no `Lean.ofReduceBool`) and no custom axiom. Every numerical certificate is
  checked by Lean's kernel.
- **Versions.** Lean 4.33.0 (official release, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`) and Mathlib
  `db584cd6d46c92f209a44c0f1c829460d327499d`.
- **Size.** 45,500 Lean modules, 50.4 million lines (4.90 GB). Almost all of it is generated certificate data that the
  kernel checks. The readable proof code (statement, proof skeleton, checkers and their soundness theorems,
  adapters) is roughly 0.2 million lines; a copy is in [`browse/`](browse/).

## Verification status

| check | result |
|---|---|
| Campaign kernel replay of the original build | `INCREMENTAL_REPLAY_OK`: all 45,500 modules, 22,668,080 declarations re-checked by the kernel |
| Clean rebuild from these sources | every one of the 45,500 modules recompiled with plain `lean` into an empty output root, with no prebuilt campaign files. The final theorem passed the gate (compile rc 0, no errors, no `sorry`, only the 3 standard axioms), and its compiled file `CKRoute/Final.olean` (sha256 `43de2287…`) is byte-identical to the original build's |
| Kernel replay of the clean rebuild | `SHARDED_REPLAY_OK`: 4,990 / 4,990 shards (4,954 run on a Google compute cluster, 36 on the build workstation), 45,500 modules each replayed exactly once, 22,668,080 declarations, 0 failures. The top shard prints the axiom line `[Classical.choice, Quot.sound, propext]` |
| Acceptance tests of the verification kit | following [`HOW_TO_VERIFY.md`](HOW_TO_VERIFY.md) literally: checksums, unpacking, quick test (byte-identical), a 488-module partial rebuild (486 byte-identical + the 2 expected differences), the audit of the final theorem, and sample replay shards all pass |
| Independent end-to-end run of the shipped kit (full rebuild, audit and replay on a Google compute cluster) | **in progress — results will be added** |

## How to verify

Full instructions, requirements and expected output: [`HOW_TO_VERIFY.md`](HOW_TO_VERIFY.md). In short (Linux
x86-64, about 720 CPU-hours, at least 128 GB RAM, about 160 GB free disk):

```bash
git clone https://github.com/dpwoodru/general-courtade-kumar-lean.git && cd general-courtade-kumar-lean
# download the release assets of v1.0 into ./release/ (see HOW_TO_VERIFY.md), then:
(cd release && sha256sum -c SHA256SUMS.txt)
mkdir -p trusted && for f in release/packages-*.tar.zst; do tar --zstd -xf "$f" -C trusted; done
tar --zstd -xf release/sources_v3.tar.zst            # -> sources/ (45,500 files)
BUILD/build_plain.sh --packages trusted/packages --out out_test --lean $LEAN --target GeneralCK.Statement   # seconds
BUILD/build_plain.sh --packages trusted/packages --out out --lean $LEAN --jobs 32 --mem-gb 200            # hours
BUILD/audit_final.sh  --out out --packages trusted/packages --lean $LEAN
BUILD/replay_fresh.sh --out out --packages trusted/packages --lean $LEAN --workers 32                     # optional
```

What a human must check is only the statement (`GeneralCK/Statement.lean`, 63 lines) and the Mathlib definitions it
uses; Lean's kernel checks everything else. [`REVIEW_GUIDE.md`](REVIEW_GUIDE.md) explains the statement, the proof
skeleton that follows the manuscript, and the certificate families.
[`MANUSCRIPT_DEVIATIONS.md`](MANUSCRIPT_DEVIATIONS.md) lists the few computer-assisted steps where the Lean proof checks
the paper's claim with its own certificates or a different argument.

## Repository layout

| path | what |
|---|---|
| `HOW_TO_VERIFY.md` | step-by-step machine check: requirements, commands, expected output |
| `REVIEW_GUIDE.md` | for human readers: statement, proof skeleton, the 18 inputs of the final theorem, certificate families, trust base |
| `MANUSCRIPT_DEVIATIONS.md` | where the Lean proof verifies a step differently from the paper's archived computations |
| `SOURCE_COMMENT_NOTES.md` | errata for out-of-date or imprecise comments in the sources, kept outside the `.lean` files to preserve their checksums |
| `CHANGELOG.md` | release history and errata |
| `BUILD/` | `build_plain.sh` / `build_plain.py` (the tested build: plain `lean`, topological order, parallel jobs under a memory budget), `audit_final.sh`, `replay_fresh.sh`, `EXPECTED.md`; `lake/` is a Lake project skeleton (**untested**, a convenience only) |
| `LOCKS/` | `lean-toolchain`, `lake-manifest.json` (Mathlib `db584cd6…` and its dependencies), the toolchain commit, per-file hashes of the trusted packages, and how to rebuild the trusted base yourself |
| `final/` | `Final.lean` (the final theorem), `AuditFinal.lean` (`#check` + `#print axioms`), and the clean build's gate record for `CKRoute.Final` |
| `replay/` | the frozen kernel-replay harness `ReplayShard.lean`, the 1,225-shard plan `plan.tsv`, and its drivers |
| `SOURCES_MANIFEST.tsv` | per module: height, source path, source sha256, size, build recipe, closure imports |
| `CLEAN_BUILD_HASHES.tsv` | per module: the clean build's `.olean` / `.ilean` sha256 and sizes, the comparison with the original build, wall time and max RSS |
| `FAMILIES.tsv` | the certificate families (checker, soundness theorem, kernel evaluation) |
| `provenance/` | the one historical source variant that is not part of the source set (`E8TAxisZero0082Root`: same statement, different proof) |
| `browse/` | **read-only copies** of the readable proof code, for browsing on GitHub (see below) |
| `THIRD_PARTY_NOTICES.md`, `LICENSES/` | licenses of the third-party packages whose compiled files are release assets (Apache License 2.0) |
| `SHA256SUMS.txt` | sha256 of every file of this repository except `README.md` (which may be updated after the release) |

**Release assets** (GitHub Release `v1.0`):

| asset | what |
|---|---|
| `sources_v3.tar.zst` | the complete source tree: all 45,500 modules, exactly as compiled and kernel-checked (388 MB; extracts to `sources/`, 4.9 GB) |
| `packages-olean-00-…tar.zst`, `packages-server-private-ir-00-…tar.zst` | the trusted base, prebuilt: Mathlib `db584cd6…` and its 7 dependency packages (a convenience; you can build it yourself, see `LOCKS/REBUILD_TRUSTED_BASE.md`) |
| `v3_replay_addendum.tar.gz` | the clean-tree kernel-replay verdict, an independent recount, the per-shard index and the top shard's output |
| `SHA256SUMS.txt` | sha256 of the assets |

The two `packages-*` assets are unmodified compiled files of Mathlib and its 7 dependency packages, redistributed under their own license (Apache License 2.0); see [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).

### About `browse/`

`browse/` holds byte-identical copies of 1,359 of the 45,500 source files (238,690 lines): the statement, the
`CKRoute` proof skeleton, the checkers, their soundness theorems and the adapters. Generated certificate data is left
out: modules whose last name component contains a number with two or more digits, modules whose name contains
`Generated`, `Data` or `Coverage`, and files over 3,000 lines. **The build does not use `browse/`**: it compiles the
complete tree from `sources_v3.tar.zst`. The list and the rule are in [`browse/README.md`](browse/README.md).

## Trust base

You trust:
- the Lean 4.33.0 kernel;
- Mathlib `db584cd6…` and its dependencies (you can fetch and build them yourself instead of using the prebuilt
  packages; their licenses and pinned revisions are in [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md));
- the 63-line statement and the Mathlib definitions it uses.

The 45,500 campaign modules are not trusted: they are rebuilt from source and re-checked by the kernel.

## Notes on provenance

- **Source comments.** The Lean sources are published exactly as they were compiled and kernel-checked. Twenty-two of
  them contain, inside comments only, historical references to the development workspace: directory names such as
  `~/…`, `coord/…` or `A/asmroot5`, with no user or host names. They are left unchanged so that every published file
  matches its recorded hash:
  `CKLaneA1/JnConvex.lean`, `CKLaneA5/Bands.lean`, `CKLaneA5/ChartOwnersAsm.lean`, `CKLaneA5/Correction.lean`,
  `CKLaneC/TM3/Core.lean`, `CKLaneC2R/ReflectionBridge.lean`, `CKLaneC3/LargeFields.lean`, `CKLaneD/OCompact.lean`,
  `CKLaneM06/CapSubrow.lean`, `CKLaneM1/MLRoute.lean`, `CKLaneM2/SLPlane.lean`, `CKLaneN1/SubRows.lean`,
  `CKLaneN1b/Moderate.lean`, `CKLaneN1c/FiveGain.lean`, `CKLaneN23/OpBoundaryStrip.lean`, `CKLaneN23/OpCorner.lean`,
  `CKLaneN23/RSDefs.lean`, `CKLaneN23/SameSideHalf.lean`, `CKLaneN4/CentralSubrows.lean`,
  `CKLaneP/RightLowerFinal.lean`, `CKLaneR2/TM3/Core.lean`, `GeneralCK/LanePHMC/Reduce.lean`.
- **Build recipes.** 39 modules were compiled by the clean build from a staging directory whose relative name
  becomes part of the module name recorded in the compiled file. The recipe column of `SOURCES_MANIFEST.tsv` keeps
  those two historical directory names so that `build_plain.sh` reproduces the published hashes exactly; they carry
  no meaning for the proof. Two further modules had an absolute source path that cannot be reproduced elsewhere; they
  are compiled plainly and are expected to differ from the published hashes by that path only.
- **Out-of-date comments.** Some comments in the sources describe an intermediate development status, for example
  "remains UNPROVED" or "still open", for statements that the release proves elsewhere. They are corrected, with links,
  in [`SOURCE_COMMENT_NOTES.md`](SOURCE_COMMENT_NOTES.md) rather than in the `.lean` files, to preserve the published
  source and compiled checksums. Lean's kernel does not read comments, so they do not affect the proof.
- Module namespaces such as `CKLaneE` or `CKLaneM07` are names of the work streams that produced them.

## License

This repository is licensed under the Apache License, Version 2.0 (SPDX: `Apache-2.0`); see [`LICENSE`](LICENSE).

The release asset `sources_v3.tar.zst` and its copies in `browse/` are covered by the same license. The trusted-package release assets (`packages-*.tar.zst`) contain unmodified compiled files of Mathlib and its dependencies, which remain under their own license (Apache License 2.0); see [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) and [`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt).

## Citation

Please cite the paper:

Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair and D. P. Woodruff. *A Proof of the Most Informative
Boolean Function Conjecture.* arXiv:2609.24931, 2026. https://arxiv.org/abs/2609.24931

```bibtex
@misc{chen2026mostinformative,
  title         = {A Proof of the Most Informative Boolean Function Conjecture},
  author        = {Chen, Zijie and Gohari, Amin and Javanmard, Adel and Lin, Honghao and Mirrokni, Vahab and Nair, Chandra and Woodruff, David P.},
  year          = {2026},
  eprint        = {2609.24931},
  archivePrefix = {arXiv},
  primaryClass  = {cs.DS},
  url           = {https://arxiv.org/abs/2609.24931}
}
```
