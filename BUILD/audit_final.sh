#!/usr/bin/env bash
# audit_final.sh — check the final theorem in a FRESHLY BUILT tree (after build_plain.sh / build_plain.py).
#   compiles final/AuditFinal.lean  (import CKRoute.Final; #check; #print axioms)  against LEAN_PATH = OUT : packages
#   and requires: rc 0, no error messages, the type line
#     GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar
#   and the axiom set exactly {propext, Classical.choice, Quot.sound}.
# usage: audit_final.sh --out OUT --packages PKGDIR [--lean LEAN] [--work DIR]
#   PKGDIR: directory with the 8 package roots (aesop batteries importGraph LeanSearchClient mathlib plausible
#           proofwidgets Qq), e.g. the packages/ directory of the v2 bundle, or a colon-separated list of roots.
# RAM: importing CKRoute.Final maps the whole closure (≈ 70 GB, mostly file-backed page cache).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KIT="$(cd "$HERE/.." && pwd)"
OUT=""; PKG=""; LEAN="lean"; WORK="$PWD/audit_work"
while [ $# -gt 0 ]; do
  case "$1" in
    --out) OUT="$2"; shift 2;; --packages) PKG="$2"; shift 2;; --lean) LEAN="$2"; shift 2;;
    --work) WORK="$2"; shift 2;; *) echo "unknown option $1"; exit 2;;
  esac
done
[ -n "$OUT" ] && [ -n "$PKG" ] || { echo "usage: audit_final.sh --out OUT --packages PKGDIR [--lean LEAN]"; exit 2; }
OUT="$(cd "$OUT" && pwd)"
LP="$OUT"
if [ -d "$PKG/mathlib" ]; then
  for p in aesop batteries importGraph LeanSearchClient mathlib plausible proofwidgets Qq; do LP="$LP:$(cd "$PKG/$p" && pwd)"; done
else
  LP="$LP:$PKG"
fi
mkdir -p "$WORK"; cp "$KIT/final/AuditFinal.lean" "$WORK/AuditFinal.lean"
DECL=GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed
set +e
( cd "$WORK" && LEAN_PATH="$LP" "$LEAN" -j 1 -M 0 --json AuditFinal.lean > AuditFinal.jsonl 2> AuditFinal.err )
rc=$?; set -e
python3 - "$WORK/AuditFinal.jsonl" "$rc" "$DECL" <<'EOF' | tee "$WORK/audit_check.json"
import json, re, sys
p, rc, decl = sys.argv[1], int(sys.argv[2]), sys.argv[3]
msgs = [json.loads(l) for l in open(p) if l.strip()]
errs = [m for m in msgs if m.get('severity') == 'error']
typ = any(m.get('data', '').strip() == decl + ' : GeneralCK.GeneralCourtadeKumar' for m in msgs)
ax = [m['data'] for m in msgs if 'depends on axioms' in m.get('data', '')]
axset = set(re.findall(r'[A-Za-z_.]+', ax[0].split(':', 1)[1])) if ax else None
ok = rc == 0 and not errs and typ and axset == {'propext', 'Classical.choice', 'Quot.sound'}
print(json.dumps({'rc': rc, 'errors': len(errs), 'type_printed': typ, 'axioms': sorted(axset) if axset else None,
                  'sorryAx': any('sorryAx' in a for a in ax), 'ok': ok}))
sys.exit(0 if ok else 1)
EOF
