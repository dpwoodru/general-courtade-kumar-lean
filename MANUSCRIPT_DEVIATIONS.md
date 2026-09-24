# Where the Lean proof verifies a step differently from the paper's archived computations

The paper's computer-assisted steps rest on numerical computations archived with the manuscript: interval-arithmetic
ledgers and leaf lists, not Lean. The Lean proof re-proves every such step inside Lean, and for most steps it follows
the archived computation. The entries below are the steps where it instead uses its own certificate (a different
subdivision or cover) or a different argument. In every case the Lean statement is exactly the paper's lemma: the
field type of the manuscript route.

The entries are copied verbatim from the campaign's deviation log (2026-09-23). Lane names
(E, G3b, N23, C, R2, M05, ...) are internal work streams; namespaces such as CKLaneE.* are the corresponding Lean
modules in `sources/` (from `sources_v3.tar.zst`).

- (S) label 0 normalized_logsum (Lane E): lsk checks use the Lean-proved cost floor 1/(b(1−a)(2−a)) (CKLaneE.KappaFloor.cost_floor_sameSide) instead of the archive's κ-based β = min(κ(a),κ(b))/(2b(1−a)) (κ is a retained manuscript input absent from the corpus). The certified leaf inequality is the same proposition and at least as strong; no archive input assumed.
- (S) label 0 is bound twice: G3b CKLaneG3.S.Label0.label0 (from E's NLSB batches via SAdapt) and E's own CKLaneE.NLSFamily.nls_family; either discharges sLabel0.
- RA-stat (capFibers.rightStationary): proved by ray convexity (N23 rightStationary_of_gamma: φ''=rayGamma ≥ 0 along degenerate-edge rays) + Taylor-model covers (C bulk/small-b, R2 u-tail, N23b corner), not by re-executing the archived 29.4M-node ledger (which the manuscript itself reports as not independently re-executed, App. S.2). The proved proposition is the exact field type.
- CE-stat row 4 (M07): 280 TM cells replace the 5,487,944 archived A3 leaves; same row Prop (CKLaneN1.CEStat.A3LeafUnion).
- Reflection compact (C2): 5,079 BSP cells replace the historical 138,000; same field type.
- leftUpper (N4b) / leftLower (N1): new cell covers (1,131 / 3,006 cells) for SC+ clauses (v)/(ii); exact field types.
- FULL_ENTROPY Theorem (8) / CentralSquare row 8 (M05): the 266 certificate unit roots are archived FULL_ENTROPY nodes covering all 33,572 archived leaves (each under exactly one root), but below the roots the certificate trees are M05's own subdivision (box-level vs archived leaves: 12,692 equal, 18,715 inside a coarser certificate box, 859 refined, 1,306 cut across; per-box comparison by an independent verifier). The theorem is exactly the row proposition over the full archived region; M05's shard docstrings overstate ("archived splits + refinement inside archived leaves"). Ruled acceptable (certificate-level deviation, same as C2/M07), recorded by the independent verifier as PASS with flag.
- Other certificate-level re-subdivisions (same propositions): A2 diagonal3/4 covers (smaller non-dyadic), M06 quantitative_subrectangle leaves certified directly at 3/40, N4b/N1 new covers, M07 row 3/4 TM covers, C/R2 RA-stat covers.
