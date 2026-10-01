# provenance/ — historical material outside the source set

The 45,500 Lean sources of this repository (identical to `sources_v3.tar.zst` of v1.0) are exactly the sources the canonical clean build compiled. This folder holds historical
material that is not part of that source set:

- [`E8TAxisZero0082Root/`](E8TAxisZero0082Root/README.md): the single known case where the original campaign build had
  compiled a module from a different revision of its source.
- [`PsiCornerBoundaryRefutation/`](PsiCornerBoundaryRefutation/README.md): a historical file that a source comment cites
  (see [`SOURCE_COMMENT_NOTES.md`](../SOURCE_COMMENT_NOTES.md) §4). The final theorem does not import it.
