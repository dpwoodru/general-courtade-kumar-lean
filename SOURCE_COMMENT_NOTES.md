# Notes on source comments (errata)

**Why the corrections are here and not in the `.lean` files.** The Lean sources of this release are published
byte-for-byte as they were compiled and kernel-checked, and their checksums are part of the verification record:
- `SOURCES_MANIFEST.tsv` lists the sha256 of every source, and the release asset `sources_v3.tar.zst` contains exactly
  those files;
- `CLEAN_BUILD_HASHES.tsv` lists the sha256 of every compiled file;
- the clean rebuild, the kernel replays and the independent end-to-end run all use exactly these files.

Editing a source, even only a comment, would change its sha256 and the release tarball. Lean also stores doc comments
and declaration positions inside the compiled `.olean`, so the compiled checksums would change as well. Every
published hash, and every verification record that refers to them, would then no longer match the release. To
preserve the checksums, out-of-date or imprecise comments are corrected in this file instead.

Lean's kernel does not read comments, so none of the points below affects the proof of the final theorem. Line
numbers refer to release `v1.0`; the files under `browse/` are byte-identical copies of the sources. The points were
raised in a review of commit `95f208b` by a coauthor (2026-09-24).

## 1. M05 certificate trees: the correspondence with the archived subdivision is overstated

- **Where:** [`CKLaneM05/FE8/Skel.lean`, lines 6–10](browse/CKLaneM05/FE8/Skel.lean#L6-L10) (module docstring). Some
  M05 shard modules use the same wording.
- **The comment says:** the certificate trees "follow the archived splits and refine inside archived leaves".
- **Correction:** the 266 certificate roots are archived FULL_ENTROPY nodes. Below them, the certificate trees are
  M05's own, independently certified subdivisions covering the required region: some boxes are coarser than the
  archived leaves, and some cut across them. The theorem proved is exactly the row proposition over the full region.
  This deviation is recorded in [`MANUSCRIPT_DEVIATIONS.md`](MANUSCRIPT_DEVIATIONS.md) (FULL_ENTROPY Theorem (8) /
  CentralSquare row 8).

## 2. "`HalfMeanSlopeGapOnCompact` remains UNPROVED" is a historical status

- **Where:** [`GeneralCK/LanePHMC/Reduce.lean`, lines 23–28](browse/GeneralCK/LanePHMC/Reduce.lean#L23-L28) and
  [`GeneralCK/LanePHMC/Chain.lean`, lines 12–15](browse/GeneralCK/LanePHMC/Chain.lean#L12-L15).
- **The comments say:** "THIS IS NOT CLOSURE … `HalfMeanSlopeGapOnCompact` remains UNPROVED" and "STILL NOT CLOSURE".
- **Correction:** these modules do not prove the statement themselves, and they were written before it was proved.
  It is proved in this release as `CKLaneC2.halfMeanSlopeGapOnCompact_certified`, in
  [`CKLaneC2/Final.lean`, lines 97–103](browse/CKLaneC2/Final.lean#L97-L103). That file then gives field 6
  (`halfMeanCurvature`) of the final theorem unconditionally, and the final assembly uses it in
  [`CKRoute/Remaining3T71.lean`, line 92](browse/CKRoute/Remaining3T71.lean#L92).

## 3. The "still-open" label families in `Bindings2.lean` are inputs of an intermediate theorem

- **Where:** [`CKRoute/Bindings2.lean`, lines 11–23](browse/CKRoute/Bindings2.lean#L11-L23).
- **The comments say:** labels 0, 1 and 3 of the (O) row are "open" and the "three still-open label families".
- **Correction:** at that step they are the remaining inputs (hypotheses) of the intermediate theorem
  `opCompact_of_labels013`, not open problems of the project. All three are supplied:
  - label 3 by `oLabel3_of_M10` in [`CKRoute/Remaining3Rows.lean`, lines 39–43](browse/CKRoute/Remaining3Rows.lean#L39-L43);
  - labels 0 and 1 in the final assembly, [`final/Final.lean`, lines 47–48](final/Final.lean#L47-L48), by
    `CKLaneD.Leaves.endpoint_oLeafOK` and `CKLaneM2.Leaves.shifted_logsum_oLeafOK`.

## 4. A cited refutation file is not in the source set

- **Where:** [`GeneralCK/PsiBoundaryAnalyticBridge.lean`, lines 36–47](browse/GeneralCK/PsiBoundaryAnalyticBridge.lean#L36-L47).
- **The comment says:** the hypothesis of `residualPsiScalarBound_le_interiorCost_of_oppositeCorner` is false, as
  shown in `GeneralCK/PsiCornerBoundaryRefutation.lean`.
- **Clarification:** the warning is correct, but the cited file is historical development material. The final
  theorem does not import it, so it is not in `sources_v3.tar.zst`. It is now included, unmodified, in
  [`provenance/PsiCornerBoundaryRefutation/`](provenance/PsiCornerBoundaryRefutation/README.md), with a compile check
  against this release. To apply a theorem whose hypothesis is false, one would have to prove that hypothesis, so
  such a theorem cannot contribute to the kernel-checked final theorem.

## 5. `replay_fresh.sh`: "0 cached, all replayed" assumes a new work directory

- **Where:** [`BUILD/replay_fresh.sh`, lines 9–11](BUILD/replay_fresh.sh#L9-L11); the reuse happens in
  [`replay/replay_bundle.py`, lines 59–63](replay/replay_bundle.py#L59-L63).
- **The comment says:** the result is `INCREMENTAL_REPLAY_OK` with "0 cached, all replayed". `BUILD/EXPECTED.md`
  said the same.
- **Correction:** this holds for a run in a new, empty work directory (`./replay_work` by default, or `--work DIR`).
  If the work directory of an earlier run is reused, `replay_bundle.py` skips every shard whose earlier output
  already contains `SHARD_REPLAY_OK`, and those shards are not replayed again. For a fully fresh replay, use a new
  directory; `HOW_TO_VERIFY.md` and `BUILD/EXPECTED.md` now say so. The script itself is unchanged, because it is
  exactly the script the independent end-to-end run uses, in a new directory on a fresh machine.

## 6. Provenance note: wrong tactic name

- **Where:** [`provenance/E8TAxisZero0082Root/README.md`](provenance/E8TAxisZero0082Root/README.md). This is a
  documentation file, not a Lean source.
- **Correction:** the two historical revisions differ after `norm_num […]`, not after `simp only […]`. The README is
  corrected; the rest of its description was already accurate.
