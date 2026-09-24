#!/usr/bin/env bash
# build_plain.sh — PRIMARY rebuild path of the v3 package: plain `lean` (no Lake), topological order, fresh root.
#
#   BUILD/build_plain.sh --packages PKGDIR --out OUT [--lean LEAN] [--jobs N] [--mem-gb M] [--target M1,M2]
#                        [--canonical] [--sources SRC]
#
#   SRC      the extracted sources_v3.tar.zst (default: ./sources next to this kit, i.e. KIT/sources)
#   PKGDIR   the 8 trusted package roots at Mathlib db584cd6… (aesop batteries importGraph LeanSearchClient mathlib
#            plausible proofwidgets Qq). Either the packages/ directory of the v2 bundle (shards packages-olean-00 +
#            packages-server-private-ir-00, verified against LOCKS/TRUSTED_HASHES.tsv) or a Lake checkout of
#            Mathlib at the pinned rev after `lake exe cache get` (give the roots colon-separated).
#   OUT      a fresh, empty output root; oleans/ileans land at OUT/<Mod/Path>.olean
#   LEAN     Lean 4.33.0 (commit d8b18978…), e.g. the official lean-4.33.0-linux/bin/lean
#   --jobs / --mem-gb   parallel lean processes and a memory budget. Per-module RSS estimates come from
#            CLEAN_BUILD_HASHES.tsv (the clean build's measured max RSS); a job starts only if the estimates of the
#            running jobs plus its own fit into --mem-gb (one job always runs). The top of the graph needs ≈ 70 GB
#            (importing CKRoute.Final maps the whole closure; mostly file-backed page cache).
#   --target builds only the import closure of the given modules (e.g. a quick test: --target GeneralCK.Statement)
#   --canonical compiles every module `plain` (then bytes differ from CLEAN_BUILD_HASHES.tsv for the 152 modules
#            with a non-plain recipe, by module name / package name / embedded path only)
# Then: BUILD/audit_final.sh --out OUT --packages PKGDIR   (type + axioms of the final theorem)
#       BUILD/replay_fresh.sh --out OUT --packages PKGDIR  (T2 kernel replay of the fresh tree)
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KIT="$(cd "$HERE/.." && pwd)"
SRC="$KIT/sources"; PKG=""; OUT=""; LEAN="lean"; JOBS=4; MEM=64; TARGET=""; CANON=""
while [ $# -gt 0 ]; do
  case "$1" in
    --sources) SRC="$2"; shift 2;; --packages) PKG="$2"; shift 2;; --out) OUT="$2"; shift 2;;
    --lean) LEAN="$2"; shift 2;; --jobs) JOBS="$2"; shift 2;; --mem-gb) MEM="$2"; shift 2;;
    --target) TARGET="$2"; shift 2;; --canonical) CANON="--canonical"; shift;;
    -h|--help) sed -n '2,/^set -euo/p' "$0" | grep '^#'; exit 0;;
    *) echo "unknown option $1"; exit 2;;
  esac
done
[ -n "$PKG" ] && [ -n "$OUT" ] || { echo "--packages and --out are required (see --help)"; exit 2; }
[ -d "$SRC/CKRoute" ] || { echo "sources not found at $SRC (extract sources_v3.tar.zst next to the kit)"; exit 2; }
VER="$("$LEAN" --version | tail -1)"
case "$VER" in *"version 4.33.0"*"d8b18978322de05a8f3dba51ef03cf5461676c17"*) ;; *) echo "wrong Lean: $VER"; exit 1;; esac
mkdir -p "$OUT"
exec python3 "$HERE/build_plain.py" --src "$SRC" --manifest "$KIT/SOURCES_MANIFEST.tsv" --packages "$PKG" \
  --out "$OUT" --lean "$LEAN" --jobs "$JOBS" --mem-gb "$MEM" --expect "$KIT/CLEAN_BUILD_HASHES.tsv" \
  ${TARGET:+--target "$TARGET"} $CANON
