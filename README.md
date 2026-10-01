# The General Courtade–Kumar theorem in Lean 4

This repository contains a complete, machine-checked Lean 4 proof of the general Courtade–Kumar inequality: for
every n, every Boolean function f on {0,1}ⁿ and every crossover probability p ∈ [0, 1], the mutual information between
f(X) and the output Y of a binary symmetric channel with crossover p satisfies I(f(X); Y) ≤ 1 − H(p).

It formalizes the main theorem of Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair and D. P. Woodruff,
[*A Proof of the Most Informative Boolean Function Conjecture*](https://arxiv.org/abs/2609.24931), arXiv:2609.24931
(2026).

The repository is a standard Lake project: Lean 4.33.1 (official release, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Mathlib `v4.33.1` (`0df444a360eaa60ab8c11dca51a86af692955474`), with all 45,500 Lean source
files in the repository. [`formalization.yaml`](formalization.yaml) describes the project in the
[mathlib-initiative format](https://github.com/mathlib-initiative/formalization.yaml).

## The statement

[`GeneralCK/Statement.lean`](GeneralCK/Statement.lean) (63 lines) defines

```lean
def GeneralCourtadeKumar : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ),
    0 ≤ p → p ≤ 1 → mutualInformation f p ≤ 1 - H p
```

Here `Cube n := Fin n → Bool`, `H p := Real.binEntropy p / Real.log 2` (binary entropy in bits), and
`mutualInformation` is computed from the finite joint and marginal masses of (f(X), Y), with X uniform and independent
bit flips of probability p. The definitions use only Mathlib's `Real.binEntropy`, `Real.log`, `Real.negMulLog` and
finite sums. [`REVIEW_GUIDE.md`](REVIEW_GUIDE.md) §1 walks through them.

[`CKRoute/Final.lean`](CKRoute/Final.lean) proves it:

```lean
theorem GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar
```

The default build target [`FinalCheck.lean`](FinalCheck.lean) contains

```lean
/-- info: 'GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed
```

and a similar check of the theorem's type, so `lake build` fails unless the proof rests on exactly Lean's three
standard axioms: no `sorry`, no `native_decide` (`Lean.ofReduceBool`) and no added `axiom`. Every numerical
certificate is checked by Lean's kernel.

The statement has also been written in the style of [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures),
as `CourtadeKumar.courtade_kumar` (submitted in
[google-deepmind/formal-conjectures#6688](https://github.com/google-deepmind/formal-conjectures/pull/6688)).
[`verification/comparator/`](verification/comparator/) holds it as a [comparator](https://github.com/leanprover/comparator)
challenge, with a solution that derives it from the final theorem.

## Check it yourself

You need Linux x86-64 (the only platform we tested), [elan](https://github.com/leanprover/elan) (it installs Lean
4.33.1 from `lean-toolchain`) and a network connection for Mathlib.

```sh
git clone https://github.com/dpwoodru/general-courtade-kumar-lean.git && cd general-courtade-kumar-lean
lake exe cache get              # prebuilt Mathlib v4.33.1 from the Mathlib cache
lake build GeneralCK.Statement  # quick test: the statement file only (seconds)
LEAN_NUM_THREADS=32 lake build  # the whole proof, 45,500 modules; LEAN_NUM_THREADS = number of parallel jobs
```

- **Compute.** About 1,200 CPU-hours. Our Lean 4.33.1 run took 5.0 hours with 342 parallel jobs on a 380-core
  machine.
- **Memory.** Most modules need a few GiB and the largest needs about 42 GiB. Lake has no memory budget, so choose
  `LEAN_NUM_THREADS` to fit your machine; in our run the summed resident memory peaked at about 1,392 GiB with 342
  jobs, about 4.1 GiB per job.
- **Disk.** Allow about 300 GB for `.lake/` (289 GB in our run).
- **Memory maps.** Near the top of the import graph a Lean process maps about 77,000 `.olean` files, more than the
  Linux default `vm.max_map_count` (65,530). Raise it if you can: `sudo sysctl -w vm.max_map_count=262144`.

Lean prints several thousand linter and deprecation warnings (unused `simp` arguments and the like) while building;
they do not affect the result. The build has succeeded when it ends with the axioms of the final theorem
(`propext`, `Classical.choice`, `Quot.sound`) and `Build completed successfully`. To print the type and the axioms
again: `lake env lean final/AuditFinal.lean`.

[`HOW_TO_VERIFY.md`](HOW_TO_VERIFY.md) has the details, the comparator check, and the optional plain-`lean` rebuild
that reproduces the published per-module hashes.

## How it was verified

Release v1.2 moved from Lean 4.33.0 to Lean 4.33.1, which fixes kernel soundness bugs in 4.33.0
([release notes](https://lean-lang.org/doc/reference/stable/releases/v4.33.1/)). The first row ran on Lean 4.33.1, as
did part of the comparator row; the other rows ran on Lean 4.33.0, on the same sources.

| check | result |
|---|---|
| Standard Lake build on Lean 4.33.1 (release v1.2, 2026-10-01, by an independent agent on a Google compute cluster) | a clone of v1.2 (Lean 4.33.1, Mathlib v4.33.1 from `lake exe cache get`): a bare `lake build` from scratch built all 45,500 modules and `FinalCheck`, whose type and axiom checks passed, with no errors and no `sorry` (5.0 h with 342 parallel jobs, 1,171 CPU-hours); a second `lake build` rebuilt nothing; `lake env lean final/AuditFinal.lean` printed the expected type and the three standard axioms; `lake build CKChallenge.Solution` succeeded, and stock comparator accepted the two small checks below |
| Standard Lake build on Lean 4.33.0 (2026-10-01, same agent) | the 45,500 sources of this repository with the v1.0 Lake files, official Lean 4.33.0 and Mathlib from `lake exe cache get`: `lake build CKRoute.Final` built all 45,500 modules with no errors and no `sorry`; a second `lake build` rebuilt nothing; `lake env lean final/AuditFinal.lean` printed the expected type and the three standard axioms. In that built tree, a bare `lake build` with the v1.1 Lake configuration rebuilt only `FinalCheck`, which passed |
| Clean rebuild from these sources (2026-09-23) | every module recompiled with plain `lean` into an empty output root, with no prebuilt campaign files; the final theorem passed the gate (no errors, no `sorry`, only the 3 standard axioms), and `CKRoute/Final.olean` (sha256 `43de2287…`) is byte-identical to the original build's |
| Kernel replay of the clean rebuild | `SHARDED_REPLAY_OK`: 4,990 / 4,990 shards, 45,500 modules each replayed exactly once, 22,668,080 declarations, 0 failures; the top shard prints the 3 standard axioms |
| Independent end-to-end run of the v1.0 verification kit (2026-09-24) | `HOW_TO_VERIFY.md` of v1.0 followed literally on a fresh machine: all 45,500 modules rebuilt, 0 failures, 45,498 byte-identical to `CLEAN_BUILD_HASHES.tsv` plus the 2 expected `abs` modules; `CKRoute/Final.olean` `43de2287…`; audit: only the 3 standard axioms; kernel replay of this rebuild: all 45,500 modules, 0 failures |
| comparator | stock comparator accepted the bridge from `GeneralCK.GeneralCourtadeKumar` to the Formal Conjectures statement and the tests of its definitions, on Lean 4.33.1 and earlier on Lean 4.33.0 (there with both the Lean kernel and nanoda). A full run on the challenge/solution pair in `verification/comparator/` is in progress |

What a human must check is only the statement (`GeneralCK/Statement.lean`, 63 lines) and the Mathlib definitions it
uses; Lean's kernel checks everything else.

## Reading the proof

- [`REVIEW_GUIDE.md`](REVIEW_GUIDE.md): the statement, the proof skeleton that follows the manuscript, the 18 inputs of
  the final theorem, the certificate families and the trust base.
- [`MANUSCRIPT_DEVIATIONS.md`](MANUSCRIPT_DEVIATIONS.md): the few computer-assisted steps where the Lean proof checks the
  paper's claim with its own certificates or a different argument.
- [`READABLE_FILES.md`](READABLE_FILES.md): the 1,359 files (238,690 lines) that are readable proof code. The other
  44,141 files (4.88 GB) are generated certificate data: Lean definitions checked in the same file, mostly by `decide`
  and `norm_num`, written to be checked rather than read.
- [`SOURCE_COMMENT_NOTES.md`](SOURCE_COMMENT_NOTES.md): corrections to out-of-date comments, kept outside the `.lean`
  files so that every source keeps its recorded checksum.

## Repository layout

| path | what |
|---|---|
| `GeneralCK/`, `CKRoute/`, `CKLane*/`, `E8*.lean` | the 45,500 Lean sources; `GeneralCK/Statement.lean` is the statement and `CKRoute/Final.lean` the final theorem |
| `FinalCheck.lean` | the default build target: the type and axiom checks above |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | the Lake project (Lean 4.33.1; Mathlib `v4.33.1` and its dependencies pinned) |
| `formalization.yaml` | project metadata in the mathlib-initiative format |
| `verification/comparator/` | the comparator challenge (the Formal Conjectures statement), the solution and `config.json` |
| `HOW_TO_VERIFY.md` | step-by-step machine check: requirements, commands, expected output |
| `REVIEW_GUIDE.md`, `READABLE_FILES.md`, `MANUSCRIPT_DEVIATIONS.md`, `SOURCE_COMMENT_NOTES.md` | for human readers (see above) |
| `CHANGELOG.md` | release history and errata |
| `SOURCES_MANIFEST.tsv` | per module: height, source path, source sha256, size, build recipe, closure imports |
| `CLEAN_BUILD_HASHES.tsv` | per module: the clean build's `.olean` / `.ilean` sha256 and sizes, the comparison with the original build, wall time and max RSS |
| `FAMILIES.tsv` | the certificate families (checker, soundness theorem, kernel evaluation) |
| `BUILD/` | the optional plain-`lean` rebuild of v1.0 with Lean 4.33.0 (`build_plain.sh`, `audit_final.sh`, `replay_fresh.sh`, `EXPECTED.md`) |
| `LOCKS/` | the v1.0 toolchain commit (Lean 4.33.0), per-file hashes of the prebuilt trusted packages of v1.0, and how to rebuild the trusted base yourself |
| `final/` | `AuditFinal.lean` (`#check` + `#print axioms`), a copy of `Final.lean`, and the clean build's gate record for `CKRoute.Final` |
| `replay/` | the frozen kernel-replay harness `ReplayShard.lean`, the 1,225-shard plan `plan.tsv`, and its drivers |
| `provenance/` | the historical source variant that is not part of the source set, and a historical file that a source comment cites |
| `THIRD_PARTY_NOTICES.md`, `LICENSES/` | licenses of the third-party packages whose compiled files are v1.0 release assets (Apache License 2.0) |
| `SHA256SUMS.txt` | sha256 of every file of this repository except `README.md` (which may be updated after the release) |

The GitHub Release `v1.0` still holds the v1.0 assets: `sources_v3.tar.zst` (the same 45,500 sources, byte for byte),
the prebuilt trusted packages for the plain-`lean` rebuild, and our kernel-replay verdict. The Lake build does not need
them.

## Trust base

You trust:
- the Lean 4.33.1 kernel;
- Mathlib `v4.33.1` and its dependencies, as fetched by Lake (their licenses and pinned revisions are in
  [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md));
- the 63-line statement and the Mathlib definitions it uses.

The 45,500 modules of this repository are not trusted: they are rebuilt from source and checked by the kernel.

## Notes on provenance

- **Sources.** The Lean sources are published exactly as they were compiled and kernel-checked; every file matches its
  sha256 in `SOURCES_MANIFEST.tsv`, and they are byte-identical to the v1.0 release asset `sources_v3.tar.zst`
  (sha256 `3f09b23672e3a29cd6533a4004b8fd0d92e5edd17845478d327ac1aeb0a45589`).
- **Source comments.** Twenty-two sources contain, inside comments only, historical references to the development
  workspace: directory names such as `~/…`, `coord/…` or `A/asmroot5`, with no user or host names. They are left
  unchanged so that every published file matches its recorded hash:
  `CKLaneA1/JnConvex.lean`, `CKLaneA5/Bands.lean`, `CKLaneA5/ChartOwnersAsm.lean`, `CKLaneA5/Correction.lean`,
  `CKLaneC/TM3/Core.lean`, `CKLaneC2R/ReflectionBridge.lean`, `CKLaneC3/LargeFields.lean`, `CKLaneD/OCompact.lean`,
  `CKLaneM06/CapSubrow.lean`, `CKLaneM1/MLRoute.lean`, `CKLaneM2/SLPlane.lean`, `CKLaneN1/SubRows.lean`,
  `CKLaneN1b/Moderate.lean`, `CKLaneN1c/FiveGain.lean`, `CKLaneN23/OpBoundaryStrip.lean`, `CKLaneN23/OpCorner.lean`,
  `CKLaneN23/RSDefs.lean`, `CKLaneN23/SameSideHalf.lean`, `CKLaneN4/CentralSubrows.lean`,
  `CKLaneP/RightLowerFinal.lean`, `CKLaneR2/TM3/Core.lean`, `GeneralCK/LanePHMC/Reduce.lean`.
- **Out-of-date comments.** Some comments in the sources describe an intermediate development status, for example
  "remains UNPROVED" or "still open", for statements that the release proves elsewhere. They are corrected, with links,
  in [`SOURCE_COMMENT_NOTES.md`](SOURCE_COMMENT_NOTES.md) rather than in the `.lean` files. Lean's kernel does not read
  comments, so they do not affect the proof.
- **Build recipes.** 39 modules were compiled by the clean build from a staging directory whose relative name
  becomes part of the module name recorded in the compiled file. The recipe column of `SOURCES_MANIFEST.tsv` keeps
  those two historical directory names so that `BUILD/build_plain.sh` reproduces the published hashes exactly; they
  carry no meaning for the proof. Two further modules had an absolute source path that cannot be reproduced elsewhere;
  they are compiled plainly and are expected to differ from the published hashes by that path only. A Lake build
  records its package name (`general-ck`) in the compiled files, so its `.olean` files are in general not
  byte-identical to `CLEAN_BUILD_HASHES.tsv`.
- Module namespaces such as `CKLaneE` or `CKLaneM07` are names of the work streams that produced them.

## License

This repository is licensed under the Apache License, Version 2.0 (SPDX: `Apache-2.0`); see [`LICENSE`](LICENSE).

The files under `verification/comparator/CKChallenge/` follow the Formal Conjectures statement and carry its Apache-2.0
header. The trusted-package release assets of v1.0 (`packages-*.tar.zst`) contain unmodified compiled files of Mathlib
and its dependencies, which remain under their own license (Apache License 2.0); see
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) and [`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt).

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
