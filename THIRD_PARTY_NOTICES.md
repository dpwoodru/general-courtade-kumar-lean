# Third-party notices

The release assets `packages-olean-00-….tar.zst` and `packages-server-private-ir-00-….tar.zst` contain **unmodified
compiled build outputs** of the eight Lean packages below: `.olean`, `.olean.server`, `.olean.private`, `.ir` and
`.ir.sig` files. They are taken at the pinned revisions of `LOCKS/lake-manifest.json` and were built with Lean 4.33.0
(commit `d8b18978322de05a8f3dba51ef03cf5461676c17`). Their per-file sha256 values are in `LOCKS/TRUSTED_HASHES.tsv`.

These packages are not part of this project's own work. They remain under their own license, the **Apache License
2.0**. A full copy of that license is in [`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt). The compiled files are
redistributed unmodified, as permitted by §4 of that license. The copyright belongs to each package's authors; see the
upstream repositories.

| package (root in `trusted/packages/`) | upstream | pinned revision | license |
|---|---|---|---|
| Mathlib (`mathlib`) | https://github.com/leanprover-community/mathlib4 | `db584cd6d46c92f209a44c0f1c829460d327499d` | Apache License 2.0 |
| Batteries (`batteries`) | https://github.com/leanprover-community/batteries | `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d` | Apache License 2.0 |
| Aesop (`aesop`) | https://github.com/leanprover-community/aesop | `3448c0bcc5ce01b2d1546e483ec3620e32df3d0e` | Apache License 2.0 |
| Qq (`Qq`) | https://github.com/leanprover-community/quote4 | `92c15be17b7caf78c2ad767ec40f89052d908d81` | Apache License 2.0 |
| ProofWidgets (`proofwidgets`) | https://github.com/leanprover-community/ProofWidgets4 | `4be2e3d5087eeb272cf5a8853b8f9dd025ef5957` | Apache License 2.0 |
| import-graph (`importGraph`) | https://github.com/leanprover-community/import-graph | `16f02aa7642864af59f1ff0e384a015994db9118` | Apache License 2.0 |
| Plausible (`plausible`) | https://github.com/leanprover-community/plausible | `b7eb3304aeae834b12dda98993a37f6a41f6f0bb` | Apache License 2.0 |
| LeanSearchClient (`LeanSearchClient`) | https://github.com/leanprover-community/LeanSearchClient | `5f4d51b81cbd3f6b32b156bfad9056621a040404` | Apache License 2.0 |

`LOCKS/lake-manifest.json` also lists `Cli` (https://github.com/leanprover/lean4-cli, `v4.33.0`), a build-tool
dependency of import-graph. No file of it is included in the release assets.

The Lean toolchain itself (Lean 4.33.0) is not redistributed here; readers install the official release.
