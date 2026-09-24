# Rebuilding the trusted base (toolchain + packages) with the official tools

The release ships the trusted package files as two prebuilt shards (`packages-*.tar.zst`), and the toolchain is the
official Lean release. This page describes the alternative: obtain both from upstream and check them against
`LOCKS/TRUSTED_HASHES.tsv`. We never ran `lake` on the build host; the Lake steps below are for the reader and were not
executed by us.

## Pins

| item | value |
|---|---|
| toolchain | `leanprover/lean4:v4.33.0` (`LOCKS/lean-toolchain`), commit `d8b18978322de05a8f3dba51ef03cf5461676c17` (`LOCKS/TOOLCHAIN_COMMIT`) |
| official toolchain archive | `https://github.com/leanprover/lean4/releases/download/v4.33.0/lean-4.33.0-linux.tar.zst`, 574,882,764 bytes, sha256 `4b3fb03c29a1e0a253fb1d11f9bae3725f19a0dc6fc09b3ea16d2c9df3349e2c` |
| Mathlib | rev `db584cd6d46c92f209a44c0f1c829460d327499d` (`BUILD/lake/lakefile.toml`, `LOCKS/lake-manifest.json`) |
| other packages | plausible `b7eb3304…`, LeanSearchClient `5f4d51b8…`, importGraph `16f02aa7…`, proofwidgets `4be2e3d5…`, aesop `3448c0bc…`, Qq `92c15be1…`, batteries `4488d40d…` (full revs in `lake-manifest.json`) |

**Verified.** On 2026-09-23 we downloaded the official toolchain archive above (sha256 as listed). All 17,493 of its
files are byte-identical to the toolchain that built and checked the closure.

## Toolchain

```bash
curl -LO https://github.com/leanprover/lean4/releases/download/v4.33.0/lean-4.33.0-linux.tar.zst
echo "4b3fb03c29a1e0a253fb1d11f9bae3725f19a0dc6fc09b3ea16d2c9df3349e2c  lean-4.33.0-linux.tar.zst" | sha256sum -c
tar --zstd -xf lean-4.33.0-linux.tar.zst          # -> lean-4.33.0-linux/bin/lean
# or: elan toolchain install leanprover/lean4:v4.33.0   (~/.elan/toolchains/leanprover--lean4---v4.33.0)
```

## Packages via Lake (alternative to the `packages-*` shards)

```bash
mkdir lakebase && cd lakebase
cp ../BUILD/lake/lakefile.toml ../LOCKS/lake-manifest.json ../LOCKS/lean-toolchain .
mkdir -p GeneralCK && echo "" > GeneralCK.lean      # the project's own library can stay empty
lake exe cache get                                  # downloads Mathlib's prebuilt oleans for rev db584cd6…
cd ..
```

Then build the `trusted/packages/` layout from the Lake tree. There is one root per package, holding that package's
`.lake/build/lib/lean` contents:

```bash
for p in aesop batteries importGraph LeanSearchClient mathlib plausible proofwidgets Qq; do
  mkdir -p trusted/packages/$p
  cp -a lakebase/.lake/packages/$p/.lake/build/lib/lean/. trusted/packages/$p/   # (lake package dir names may differ in case)
done
```

Check the files against `LOCKS/TRUSTED_HASHES.tsv` (columns: module, role, status, relative path, size, sha256; the
`packages/…` rows are the package files, the `toolchain:…` rows the toolchain's):

```bash
python3 - <<'EOF'
import hashlib, os
n = bad = 0
for line in open('LOCKS/TRUSTED_HASHES.tsv'):
    if line.startswith('#'):
        continue
    mod, role, status, rel, size, sha = line.rstrip('\n').split('\t')
    if status != 'present' or not rel.startswith('packages/') or role == '.ilean':
        continue
    p = os.path.join('trusted', rel)
    n += 1
    if not os.path.exists(p) or hashlib.sha256(open(p, 'rb').read()).hexdigest() != sha:
        bad += 1
print(n, 'package files checked,', bad, 'mismatches')
EOF
```

If there are mismatches, use the shipped `packages-*` shards instead. Olean bytes of the closure modules do not depend
on the bytes of their imports, but kernel replay and elaboration do need the same declarations.

**Not verified by us.** We did not check whether `lake exe cache get` delivers files byte-identical to
`TRUSTED_HASHES.tsv`. What we did verify: the package oleans used on the build host are byte-identical across five
independent copies on that host. For example, `Mathlib/Tactic/Ring.olean` has sha `592377cb…` in each of them.

## Minimal file roles (measured on 2026-09-23)

| use | closure modules | trusted modules (toolchain + packages) |
|---|---|---|
| compile / import (`lean` elaboration) | `.olean` only | `.olean`, `.olean.server`, `.olean.private`, `.ir`, `.ir.sig` (`.ilean` not needed) |
| kernel replay (`lean --run ReplayShard.lean`) | `.olean` only | the same as for import |

These roles were measured on the build host:
- Importing `Mathlib` with only `.olean` fails (`failed to open … Init.olean.server`).
- Without `.ir` or `.ir.sig`, loading Aesop and Lean fails with `(interpreter) unknown declaration '…initFn…'`.
- Without `.ilean` it works.
- The campaign's check of its original compiled files (compiling the final theorem against them) was run with exactly
  the minimal set.
