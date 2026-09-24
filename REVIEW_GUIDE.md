# REVIEW GUIDE (v3) — what is proved, where, and how it is checked

This guide is for human readers. It needs no Lean installation, only the extracted `sources_v3.tar.zst` (`sources/<Module/Path>.lean`: 45,500 files, 50,371,955 lines, 4.90 GB).

Line counts are `\n`-terminated lines of the v3 files (`SOURCES_MANIFEST.tsv`, column `lines`).

Some source comments describe an intermediate development status (for example "remains UNPROVED" or "still open") for
statements that the release proves elsewhere. `SOURCE_COMMENT_NOTES.md` corrects them with links. The corrections are
kept there rather than in the `.lean` files to preserve the published checksums.

## 1. The statement

`sources/GeneralCK/Statement.lean` (module `GeneralCK.Statement`, 63 lines) defines:

```lean
abbrev Cube (n : ℕ) := Fin n → Bool
noncomputable def H (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2          -- binary entropy in bits
noncomputable def noiseKernel {n : ℕ} (p : ℝ) (x y : Cube n) : ℝ := ∏ i, if x i = y i then 1 - p else p
noncomputable def jointMass {n : ℕ} (f : Cube n → Bool) (p : ℝ) (b : Bool) (y : Cube n) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x, if f x = b then noiseKernel p x y else 0
noncomputable def entropy {α : Type*} [Fintype α] (q : α → ℝ) : ℝ := (∑ a, Real.negMulLog (q a)) / Real.log 2
noncomputable def mutualInformation {n : ℕ} (f : Cube n → Bool) (p : ℝ) : ℝ :=
  entropy (fun b => ∑ y, jointMass f p b y) + entropy (fun y => ∑ b, jointMass f p b y) -
  entropy (fun byPair : Bool × Cube n => jointMass f p byPair.1 byPair.2)
def GeneralCourtadeKumar : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ), 0 ≤ p → p ≤ 1 → mutualInformation f p ≤ 1 - H p
```

- `mutualInformation f p` is I(f(X); Y). Here X is uniform on {0,1}ⁿ and Y is X sent through a binary symmetric channel with crossover probability p. The target is the Courtade–Kumar inequality I(f(X); Y) ≤ 1 − H(p).
- The statement covers every dimension (including n = 0), every Boolean function and every p ∈ [0, 1], endpoints included.
- Check these definitions against the conjecture you care about; this is the one file whose *meaning* must be trusted.

### Mathlib definitions the statement relies on (also to be checked by a human)

The statement uses these Mathlib definitions at the pinned revision `db584cd6…`. They are quoted verbatim from Mathlib at that revision (file:line):

| name | definition at `db584cd6…` | file |
|---|---|---|
| `Real.binEntropy` | `noncomputable def binEntropy (p : ℝ) : ℝ := p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹` (docstring: `= - p * log p - (1-p) * log (1 - p)`, the Shannon entropy of a Bernoulli(p) variable, in nats) | `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:63` |
| `Real.negMulLog` | `noncomputable def negMulLog (x : ℝ) : ℝ := - x * log x` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:164` |
| `Real.log` | `noncomputable def log (x : ℝ) : ℝ := if hx : x = 0 then 0 else expOrderIso.symm ⟨\|x\|, abs_pos.2 hx⟩`, the natural logarithm of `\|x\|` with `log 0 = 0` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:44` |
| `∑ x, …`, `∏ i, …` | `Finset.sum` / `Finset.prod` over `Finset.univ` of a `Fintype` (here `Cube n = Fin n → Bool`, `Bool`, `Bool × Cube n`) | `Mathlib/Algebra/BigOperators/…`, `Mathlib/Data/Fintype/…` |
| `(2 : ℝ) ^ (-(n : ℤ))` | integer power (`zpow`) on ℝ, i.e. 2⁻ⁿ | Mathlib core algebra |

The conventions that matter:

- `H p = binEntropy p / log 2` is the binary entropy in bits. Since `log 0 = 0`, it is 0 at p = 0 and p = 1.
- `entropy q = (∑ a, negMulLog (q a)) / log 2` is the Shannon entropy in bits, with 0·log 0 = 0.
- `jointMass f p b y` is the probability of (f(X) = b, Y = y).
- `mutualInformation f p` is H(f(X)) + H(Y) − H(f(X), Y).

## 2. The final theorem and its 18 inputs

`sources/CKRoute/Final.lean` (48 lines):

```lean
theorem GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar :=
  CKRoute.generalCourtadeKumar_of_remaining3 { correctionLeft := …, …, oLabel1 := … }   -- 18 fields
```

Each field of `CKRoute.Remaining3` is bound to one lane theorem. The closure column counts the campaign modules that the binding module imports, directly or indirectly.

| field | meaning (docstring in `Remaining3.lean`) | bound to | module | closure modules | closure lines |
|---|---|---|---|---|---|
| `correctionLeft` | Theorem 7.1 `correctionLeft` | `CKLaneA5.Assembly.correctionLeft` | `CKLaneA5.Correction` | 18,264 | 35,816,984 |
| `correctionDet` | Theorem 7.1 `correctionDet` | `CKLaneA5.Assembly.correctionDet` | `CKLaneA5.Correction` | 18,264 | 35,816,984 |
| `seam` | Theorem 7.1 `seam` | `CKLaneP.seam_field_certified` | `CKLaneP.SeamFieldFinal` | 2,393 | 1,286,766 |
| `capLeftLower` | Theorem 7.1 `capFibers.leftLower` | `CKLaneN1.Edge.leftLower_certified` | `CKLaneN1.LeftLowerFinal` | 2,300 | 1,232,380 |
| `capLeftUpper` | Theorem 7.1 `capFibers.leftUpper` | `CKLaneN4.LU.leftUpper_certified` | `CKLaneN4.LU.Final` | 2,303 | 1,238,473 |
| `ceStatRow3` | CE-stat row 3 of `capFibers.leftStationary` | `CKLaneM07.CE.R3Final.transverseCurvatureOwner` | `CKLaneM07.CE.R3Final` | 349 | 54,301 |
| `ceStatRow4` | CE-stat row 4 of `capFibers.leftStationary` | `CKLaneM07.CE.Row4.a3LeafUnion` | `CKLaneM07.CE.Row4` | 502 | 71,133 |
| `ceStatRow5` | CE-stat row 5 of `capFibers.leftStationary` | `CKLaneA1.R5.highTCExclusion` | `CKLaneA1.R5Final` | 259 | 55,982 |
| `gammaCorner` | RA-stat corner certificate of `capFibers.rightStationary` | `CKLaneN23.RS.gammaCorner_one_twentieth` | `CKLaneN23.CornerClosure` | 359 | 48,142 |
| `gammaNonCorner` | RA-stat non-corner certificate of `capFibers.rightStationary` | `CKLaneC.RSC2.Final.gammaNonCorner_retained` | `CKLaneC.RSC2.Final` | 3,207 | 299,909 |
| `e8Compact` | Theorem 7.1 `e8Strict`, the `compact` owner | `CKLaneC3.Compact.compact` | `CKLaneC3.Compact` | 1,136 | 320,971 |
| `fullEntropySSCoverRest` | CentralSquare: FULL_ENTROPY cover rest | `CKLaneM05.FE8.fullEntropySSCoverRest` | `CKLaneM05.FE8.Final` | 435 | 61,216 |
| `srModerate` | CentralSquare: moderate-entropy row | `CKLaneN1b.sr_moderate` | `CKLaneN1b.Moderate` | 241 | 68,499 |
| `sLabel0` | SS_Compact (S) label 0, normalized_logsum | `CKLaneG3.S.Label0.label0` | `CKLaneG3.S.Label0` | 586 | 148,877 |
| `sLabel1` | SS_Compact (S) label 1, mean_logsum | `CKLaneG3.S.Label1.label1` | `CKLaneG3.S.Label1` | 667 | 202,765 |
| `sLabel2` | SS_Compact (S) label 2, endpoint | `CKLaneG3.S.Label2.label2` | `CKLaneG3.S.Label2` | 562 | 242,925 |
| `oLabel0` | OP_Compact (O) label 0, endpoint_plane_taylor | `CKLaneD.Leaves.endpoint_oLeafOK` | `CKLaneD.Leaves` | 451 | 465,021 |
| `oLabel1` | OP_Compact (O) label 1, shifted_logsum | `CKLaneM2.Leaves.shifted_logsum_oLeafOK` | `CKLaneM2.Leaves` | 265 | 265,489 |

## 3. The manuscript-route skeleton

The chain of theorems is:

```
Final → generalCourtadeKumar_of_remaining3 (Remaining3: 18 fields)
      → Remaining3.toRemainingRows2 → generalCourtadeKumar_of_remainingRows2 (Bindings2)
      → RemainingRows2.toRoute : ManuscriptRoute → generalCourtadeKumar_of_manuscriptRoute (Manuscript)
      → ArchiveRegionalBoundary.Inputs → GeneralCourtadeKumar
```

The 18 fields group as follows:

- 11 Theorem 7.1 components (`Remaining3.theorem71`);
- 2 CentralSquare rows;
- 3 SS_Compact (S)-labels;
- 2 OP_Compact (O)-labels.

`Manuscript.lean` fixes the regional statements of the historical manuscript route. Its module docstring summarises the argument:

- Target (G): ζ ≥ R_B, with B = max φ ψ.
- Symmetries: label exchange and simultaneous complement give the canonical orientation a ≤ b, a + b ≤ 1.
- Branch transfer: a φ-active parent is owned by Theorem 7.1. A strictly ψ-active parent is owned by the tables.
- Same-side table (b ≤ 1/2): a + b ≤ 1/16 | a/b ≤ 2⁻³² | root (S).
- Opposite-side table (b ≥ 1/2): a ≥ 1/10 (central square) | a ≤ 2⁻²⁸ | a + 1 − b ≤ 2⁻¹³ | E ≤ 10⁻⁶ | root (O).
- The coordinate maps of the two finite covers (S) and (O) are also defined there.

| file | lines | role |
|---|---|---|
| `sources/GeneralCK/Statement.lean` | 63 | the statement: `GeneralCourtadeKumar` and its ingredients (entropy in bits, BSC noise kernel, mutual information) |
| `sources/CKRoute/Manuscript.lean` | 286 | the manuscript route as Lean propositions: rows `SS_SmallMean`, `SS_RatioTail`, `SS_Compact`, `CentralSquare`, `OP_BoundaryStrip`, `OP_Corner`, `OP_LowEntropy`, `OP_Compact`, the Theorem 7.1 branch `PhiBranch`, structure `ManuscriptRoute`, and `generalCourtadeKumar_of_manuscriptRoute` (via `ArchiveRegionalBoundary.Inputs`); rows SS_SmallMean, SS_RatioTail, OP_LowEntropy discharged unconditionally |
| `sources/CKRoute/OCompactBind.lean` | 26 | binds Lane D's (O)-tree aggregation to the row `OP_Compact` |
| `sources/CKRoute/Bindings.lean` | 59 | `OP_Corner`, `OP_BoundaryStrip` bound to lane theorems; `RemainingRows → ManuscriptRoute` |
| `sources/CKRoute/Bindings2.lean` | 74 | (O) row: closed per-label families; `RemainingRows2 → ManuscriptRoute` |
| `sources/CKRoute/Remaining3T71.lean` | 95 | Theorem 7.1 components with every closed owner bound (`theorem71_of_open`, `capFibers_of_open`, `e8Strict_of_compactOwner`) |
| `sources/CKRoute/Remaining3Rows.lean` | 71 | CentralSquare, SS_Compact, OP_Compact rows with the closed families bound (`centralSquare_of_open`, `ssCompact_of_open`, `oLabel3_of_M10`) |
| `sources/CKRoute/Remaining3.lean` | 86 | `structure Remaining3` (18 fields = the leaf obligations) and `generalCourtadeKumar_of_remaining3` |
| `sources/CKRoute/Final.lean` | 48 | the final theorem: one application of `generalCourtadeKumar_of_remaining3` to 18 gated lane theorems |

- `CKRoute.Final` imports 45,500 campaign modules in total.
- 18,245 of them lie under no field. They are imported through the route files themselves (the closed components bound in `Remaining3T71`, `Remaining3Rows`, `Bindings*`).
  - The largest are `CKLaneC3.TAxis` (E8 T-axis, 12,699-module closure) and `CKLaneC2R.ReflectionBridge` (reflection, 5,621).

## 4. Certificate families: checker, soundness, kernel evaluation

Almost all of the 50 M lines are generated certificate data. Every family follows the same pattern:

1. A *Boolean checker*, a computable `def … : Bool`, is written once in a small support module.
2. It comes with a *soundness theorem* proved in Lean: `check … = true → mathematical statement`.
3. Each generated data module contains concrete numbers (dyadic or rational intervals, witnesses, trees).
4. It proves `check data = true` by **kernel evaluation**: `decide`, `decide +kernel` or `rfl`. In the interval families it uses `norm_num [checker, …]` instead, which also yields an ordinary kernel-checked proof term.
5. It applies the soundness theorem. A `Coverage` / `All` / `Final` module assembles the per-cell statements, usually by a case split over the cover.

`native_decide` is used nowhere: its only 2 textual occurrences are in doc comments. `native_decide` would add the axiom `Lean.ofReduceBool`, and the final `#print axioms` lists only propext, Classical.choice and Quot.sound. So every check was performed by the kernel, not by compiled code.

Textual counts over all 45,500 sources, from `FAMILIES.tsv`:

- `decide +kernel`: 281,243
- `decide`: 15,294,001
- `norm_num`: 1,340,606
- `rfl`: 119,897
- `native_decide`: 2

The largest families follow. Checker and soundness names are verified against the v3 sources (file:line given). `FAMILIES.tsv` lists all 662 families, with automatically extracted checker heads and proof mechanisms.

| family | modules | lines | what a data module proves | checker / soundness | feeds |
|---|---|---|---|---|---|
| R-B2 correction band 2: 11,784 cells + `Coverage` (`GeneralCK.Certificates.LaneRB2WaveV2.*`) | 11,785 | 23,824,612 | each cell: `actual_minors_positive` — `0 < Mleft ∧ 0 < Mdet` (correction-Hessian minors) on a (u, ρ) box; `Coverage` assembles the cells by a case-split tree | `GeneralCK.Certificates.DyadicFastLog.check` (DyadicFastLog.lean:31) / `check_sound` (:36); verified jet program `CorrectionFactorizedProgramKernel`, `BivariateProvedProgram` | correctionLeft, correctionDet (via `CKLaneA5.Correction`) |
| R-B1 correction band 1: 5,891 cells + `Coverage` (`GeneralCK.Certificates.RB1Band1.*`) | 5,892 | 11,908,163 | same statement shape as R-B2 on band-1 boxes | as R-B2 | correctionLeft, correctionDet |
| E8 certificates (T-axis products `E8TAxisProd####*` in 13 parts each, zero sets, graph / witness data, adaptive and origin owners) (`GeneralCK.Certificates.E#*`) | 11,239 | 3,283,317 | positivity of the E8 quantity on boxes of the (s, t) region (`GeneralCK.E8PositiveOn`) and the T-axis bridge | `logBoxCheck` / `logBoxCheck_sound`, `expBoxCheck` / `expBoxCheck_sound` (E8TAxisStableInterval.lean:135/140, 187/192); `DyadicInterval.positiveCheck` (DyadicInterval.lean:145) | e8Compact (via `CKLaneC3.Compact`) and Theorem 7.1 `e8Strict` (via `CKLaneC3.TAxis` in `Remaining3T71`) |
| RA-stat cover batches (S / BA / BB / BD) + `CKLaneC.RST2` tree shards (`CKLaneC.RSC2.*`) | 2,428 | 234,265 | for each cell: `stageB … = true`, `stageC0…C3 … = true`, … accepted, giving the region positivity `RegionPosI` on the cell | `stageB`, `stageC0`–`stageC3`, `stageE`, `stageF` / `staged_check` (CKLaneC/RSCell/Staged.lean:43–86); `RegionPosI.of_check` (RegionI.lean:46) | gammaNonCorner (via `CKLaneC.RSC2.Final`) |
| low-ratio family: cells + `Logs####` log tables (`GeneralCK.Certificates.Generated.LowRatioFamily.*`) | 1,455 | 1,565,906 | interval (`Bounds`) proofs of the leaf inequalities; the log enclosures `reflection_log_k` are certified by `checkLog` | `GeneralCK.Certificates.LogBounds.checkLog` / `checkLog_sound` (LogBounds.lean:19/23), evaluated inside `norm_num [checkLog, …]` | the reflection component `CKLaneC2R.ReflectionBridge` (bound in `Remaining3T71`) |
| double-cap families (Middle, LowMiddle, HighMiddleDerivative) (`GeneralCK.Certificates.Generated.DoubleCapMiddle.*`) | 960 | 566,162 | each cell: an `acceptedCertificate : DoubleCapBiasCellCertificate …` from `Bounds` interval proofs | `LogBounds.checkLog` / `checkLog_sound` inside `norm_num` | seam, capLeftLower, capLeftUpper (Lanes P, N1, N4) and `CKLaneP.RightLowerFinal` (bound in `Remaining3T71`) |
| midpoint families (Midpoint, MidpointNext, MidpointExtension, MidpointNextBand, MidpointPostNextBand) (`GeneralCK.Certificates.Generated.MidpointFamily.*`) | 914 | 1,506,264 | leaf inequalities on midpoint boxes | `DyadicFastLog.check` / `check_sound` | the reflection component `CKLaneC2R.ReflectionBridge` (bound in `Remaining3T71`) |
| Lane M1 (S)-leaf population (`CKLaneM1.Pop.*`) | 423 | 160,593 | `check : (leaves.all fun x => checkLeaf x.1 x.2) = true`, then `SemSS` for every leaf | `checkLeaf` / `checkLeaves_sound` (`CKLaneM1.MLChecker`) | sLabel1 |
| Lane M03 endpoint leaves (`CKLaneM03.Leaves.*`) | 335 | 203,677 | `Sem (ssBox …)` per leaf via `epLeaf_sound (…) (by decide +kernel)` | `epLeaf_sound` (`CKLaneM03.Split` / kernel) | sLabel2 |
| Lane D (O)-tree fleet (`CKLaneD.Fleet.*`) | 330 | 434,838 | `ok : (leaves.all fun x => checkLeaf x.1 x.2) = true`, then `SemUVT` per leaf | `checkLeaf` / `checkLeaves_sound` (`CKLaneD.FleetBase`) | oLabel0 |
| Lane M07 CE-stat cells (`CKLaneM07.CE.Cells.*`) | 280 | 24,932 | per cell `chk0`/`chkA`/`chkC`/`chkU … = true` | `chk0`, `chkA`, `chkC`, `chkU` (CKLaneM07/CE/ChainV2.lean:150–159) / `CellThm.cell_mode0`–`cell_mode2` | ceStatRow4 |
| Lane M2 shifted-logsum fleet (`CKLaneM2.Fleet.*`) | 142 | 235,465 | `ok : (leaves.all fun x => checkLeafSL x.1 x.2) = true` | `checkLeafSL` / `checkLeavesSL_sound` (`CKLaneM2.SLChecker`) | oLabel1 |
| Lane P seam cells (`CKLaneP.Cells.S3.*`) | 148 | 50,742 | `STree.check … = true` | `STree.check` (`CKLaneP.SeamTree`) | seam |
| Lane N23 corner positivity cells (`CKLaneN23.PosCell.*`) | 128 | 1,152 | `boxCell … = true` | `boxCell` / `posRow_of_cells` (CKLaneN23/CPosSplit.lean:33/46) | gammaCorner |
| Lane N1b moderate-entropy fleet (`CKLaneN1b.Fleet.*`) | 105 | 36,050 | `Sem (boxOf …)` via `checkCert_sound _ (…) (by decide +kernel)` | `checkCert_sound` (`CKLaneN1b.FleetBase`) | srModerate |
| Lane N4 left-upper tree shards (`CKLaneN4.LU.Shards.*`) | 69 | 8,304 | `cellCheck`/`treeCheck … = true` | `treeCheck` / `treeCheck_sound` (CKLaneN4/LU/Tree.lean:23/60) | capLeftUpper |
| Lane M08 fleet (`CKLaneM08.Fleet.*`) | 154 | 10,429 | `checkAll … = true` | `checkAll` / `checkAll_sound` (CKLaneM08/Checker.lean:614/616) | SS_Compact (S) label 3 (`CKLaneG3.S.Label3`, bound in `Remaining3Rows`) |
| Lane C2R reflection cells (S00, S01, …) (`CKLaneC2R.Cells.S00.*`) | 76 | 59,422 | `cellOk … = true` per cell | `cellOk` / `cellOk_sound` (CKLaneC2/Cells.lean:94/184), `CompactCheck` | reflection (via `CKLaneC2R.ReflectionBridge` in `Remaining3T71`) |

## 5. Red flags searched in the 45,500 sources

The v3 set is byte-identical to the SOURCES_v2 chosen set, so the v2 scan applies unchanged:

- `sorry`: 2 files, both in doc comments (`CKLaneN23/OpCorner.lean:17`, `CKLaneN23/OpBoundaryStrip.lean:23`);
- `native_decide`: 2 files, both in doc comments (`CKLaneA1/Interval.lean:9`, `CKLaneN23/CornerClosure.lean:10`);
- `axiom` declarations: 0;
- `@[implemented_by]` / `@[extern]`: 0;
- `debug.skipKernelTC`: 0.

The authoritative checks are the kernel-level ones: `#print axioms` after compiling, and the kernel replay (T2) of every constant.

## 5b. One historical source variant (not a correctness issue)

For `GeneralCK.Certificates.E8TAxisZero0082Root`, the campaign's historical olean was compiled from another revision of the source. v3 ships the source the clean build compiled.

- The two revisions differ only in the proof of the theorem `positiveAt`. The type (statement) is identical at kernel level; see `provenance/E8TAxisZero0082Root/README.md`.
- Every downstream module sees the same theorem, and `CKRoute.Final` is byte-identical either way.

## 6. The trust base

- **Trusted.**
  - The Lean 4.33.0 kernel and toolchain: official `lean-4.33.0-linux`, commit `d8b18978…`.
  - Mathlib `db584cd6…` with its dependency packages (Batteries, Aesop, Qq, ProofWidgets, Plausible, ImportGraph, LeanSearchClient): 10,498 modules, pinned by `LOCKS/lake-manifest.json`, with file hashes in `LOCKS/TRUSTED_HASHES.tsv`.
- **Not trusted: all 45,500 campaign modules.**
  - They are rebuilt from these sources by plain `lean` (`BUILD/build_plain.sh`).
  - They are checked by the gate (compile, no sorry, axioms).
  - Every constant is re-typechecked by the kernel in the layered replay (`BUILD/replay_fresh.sh`, T2).
- The mathematical content that must be read and trusted is the statement (§1). Everything else is machine-checked relative to the trust base.

## 7. The three axioms

`#print axioms GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed` gives `[propext, Classical.choice, Quot.sound]`. These are exactly Lean's standard axioms:

- propositional extensionality;
- the axiom of choice (the basis of classical logic in Lean and Mathlib);
- soundness of quotient types.

Every Mathlib theorem about real numbers depends on the same three. There are no custom axioms, no `sorryAx`, and no `Lean.ofReduceBool` / `Lean.trustCompiler`.

