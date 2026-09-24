# GeneralCK/PsiCornerBoundaryRefutation.lean: historical development file

A status note in [`GeneralCK/PsiBoundaryAnalyticBridge.lean`](../../browse/GeneralCK/PsiBoundaryAnalyticBridge.lean#L36-L47)
cites this file. It is **not part of the source set**: the final theorem does not import it, so it is not in
`sources_v3.tar.zst`, and it is not built by `BUILD/build_plain.sh`. It is included here only so that the reference
can be followed.

| file | bytes | sha256 |
|---|---:|---|
| `PsiCornerBoundaryRefutation.lean` (this folder, unmodified historical copy of 2026-09-14) | 29,644 | `fe09ad97f33b4a5777690d6989f1bd268d84be3aa81764fbda7aedf34596d502` |

- **What it shows.** Its theorems `not_residualPsiScalarOwner_oppositeCorner` and
  `not_residualPsiScalarOwner_oppositeBoundary` prove that the hypotheses `ResidualPsiScalarOwner
  oppositeCornerResidualRegion` and `ResidualPsiScalarOwner oppositeBoundaryResidualRegion` are false. The theorem
  `residualPsiScalarBound_le_interiorCost_of_oppositeCorner` in `PsiBoundaryAnalyticBridge` assumes the first of them,
  so it is vacuous and cannot be applied. That is what the status note warns about.
- **No effect on the final theorem.** To use a theorem with a false hypothesis, one would have to prove that
  hypothesis. The final theorem was checked by Lean's kernel with only the three standard axioms, so no such proof
  occurs in it.
- **Check (2026-09-24).** The file compiles with rc 0, with the official Lean 4.33.0, against the compiled sources of
  this release (the clean build, whose compiled files match `CLEAN_BUILD_HASHES.tsv`). It imports only
  `GeneralCK.PsiNormalizedLowEntropy`, which is in the source set. Both refutation theorems depend only on
  `[propext, Classical.choice, Quot.sound]`. To repeat the check after a full build, compile the file with `lean` and
  the `LEAN_PATH` that `BUILD/audit_final.sh` uses (your `out/` plus the trusted packages).
