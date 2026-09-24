#!/usr/bin/env bash
# replay_fresh.sh — T2 kernel replay (layered shards) of a FRESHLY BUILT tree.
# Wraps the v2 kit's driver (replay/replay_bundle.py; Lane I's frozen ReplayShard.lean and replay_cache.py) by
# presenting OUT and the packages as a bundle layout (symlinks only):  WORK/bundle/closure -> OUT,
# WORK/bundle/packages/<pkg> -> PKGDIR/<pkg>.  The plan (replay/plan.tsv, 1,225 shards, 45,500 modules) is the same
# module set as the v3 sources.
# usage: replay_fresh.sh --out OUT --packages PKGDIR [--lean LEAN] [--workers N] [--replay-only K1,K2] [--plan P]
#                        [--work DIR]
# Result: WORK/t2/summary.json (SHARDED_REPLAY_OK for a complete run) and WORK/t2/verdict.json
# (INCREMENTAL_REPLAY_OK: 0 cached, all replayed), and the kernel-replayed axiom line of the final theorem
# (printed by the top shard, id 1224) must be exactly [propext, Classical.choice, Quot.sound].
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KIT="$(cd "$HERE/.." && pwd)"
OUT=""; PKG=""; LEAN="lean"; WORKERS=2; ONLY=""; PLAN="$KIT/replay/plan.tsv"; WORK="$PWD/replay_work"
while [ $# -gt 0 ]; do
  case "$1" in
    --out) OUT="$2"; shift 2;; --packages) PKG="$2"; shift 2;; --lean) LEAN="$2"; shift 2;;
    --workers) WORKERS="$2"; shift 2;; --replay-only) ONLY="$2"; shift 2;; --plan) PLAN="$2"; shift 2;;
    --work) WORK="$2"; shift 2;; *) echo "unknown option $1"; exit 2;;
  esac
done
[ -n "$OUT" ] && [ -d "$PKG/mathlib" ] || { echo "usage: replay_fresh.sh --out OUT --packages PKGDIR (with PKGDIR/mathlib ...)"; exit 2; }
mkdir -p "$WORK/bundle/packages" "$WORK/t2"
ln -sfn "$(cd "$OUT" && pwd)" "$WORK/bundle/closure"
for p in aesop batteries importGraph LeanSearchClient mathlib plausible proofwidgets Qq; do
  ln -sfn "$(cd "$PKG/$p" && pwd)" "$WORK/bundle/packages/$p"
done
SYSROOT="$($LEAN --print-prefix | tail -1)"
DECL=GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed
set +e
python3 "$KIT/replay/replay_bundle.py" --bundle "$WORK/bundle" --plan "$PLAN" --out "$WORK/t2" --workers "$WORKERS" \
  --axioms "$DECL" --lean-cmd "$LEAN" --sysroot "$SYSROOT" --replay-shard "$KIT/replay/ReplayShard.lean" \
  ${ONLY:+--only "$ONLY"}
rc=$?
set -e
if [ -z "$ONLY" ] && [ "$rc" = 0 ]; then
  echo '{"covered": {}, "entries_used": []}' > "$WORK/t2/covered_none.json"
  echo '{"keys": {}}' > "$WORK/t2/keys_none.json"
  python3 "$KIT/replay/replay_cache.py" verdict --plan "$PLAN" --covered "$WORK/t2/covered_none.json" \
    --reduced "$PLAN" --rshards "$WORK/t2" --keys "$WORK/t2/keys_none.json" --out "$WORK/t2/verdict.json"
  rc=$?
fi
exit $rc
