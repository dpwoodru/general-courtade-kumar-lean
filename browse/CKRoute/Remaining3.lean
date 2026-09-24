import CKRoute.Remaining3T71
import CKRoute.Remaining3Rows

/-!
# Remaining3: the scope-locked route with every CLOSED component bound (CONDITIONAL)

`Remaining3` lists ONLY the genuinely open leaf-level obligations (owners in `I/REMAINING3.md`);
`generalCourtadeKumar_of_remaining3` is CONDITIONAL on them. Parts: `CKRoute.Remaining3T71`
(Theorem 7.1 components) and `CKRoute.Remaining3Rows` (CentralSquare, SS_Compact, OP_Compact).
-/

set_option autoImplicit false

namespace CKRoute

open GeneralCK GeneralCK.SmallMeanPhiCutoff

/-- The open leaf-level obligations of the manuscript route after binding every closed component. -/
structure Remaining3 : Prop where
  /-- Theorem 7.1 `correctionLeft` (A5). -/
  correctionLeft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2
  /-- Theorem 7.1 `correctionDet` (A5). -/
  correctionDet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2
  /-- Theorem 7.1 `seam` (P). -/
  seam : StrictSeamMinimizerExclusion retainedCutoff
  /-- Theorem 7.1 `capFibers.leftLower` (N1). -/
  capLeftLower : ∀ e f, 0 < e → e < f → f ≤ 1 →
    capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
    0 ≤ canonicalPureGap (entropyInverse e) (capFiberLower retainedCutoff f (entropyInverse e)) e f
  /-- Theorem 7.1 `capFibers.leftUpper` (N4). -/
  capLeftUpper : ∀ e f, 0 < e → e < f → f ≤ 1 →
    capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
    0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f
  /-- CE-stat row 3 of `capFibers.leftStationary` (M07). -/
  ceStatRow3 : CKLaneN1.CEStat.TransverseCurvatureOwner
  /-- CE-stat row 4 of `capFibers.leftStationary` (M07). -/
  ceStatRow4 : CKLaneN1.CEStat.A3LeafUnion
  /-- CE-stat row 5 of `capFibers.leftStationary` (A1). -/
  ceStatRow5 : CKLaneN1.CEStat.HighTCExclusion
  /-- RA-stat corner certificate of `capFibers.rightStationary` (N23). -/
  gammaCorner : CKLaneN23.RS.GammaCorner (1 / 20)
  /-- RA-stat non-corner certificate of `capFibers.rightStationary` (R1). -/
  gammaNonCorner : CKLaneN23.RS.GammaNonCorner retainedCutoff (1 / 20)
  /-- Theorem 7.1 `e8Strict`, the `compact` owner (C3). -/
  e8Compact : GeneralCK.E8PositiveOn fun s t =>
    (1 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧ (1 / 50 : ℝ) ≤ t ∧ t ≤ 12
  /-- CentralSquare: FULL_ENTROPY cover rest (M05). -/
  fullEntropySSCoverRest : CKLaneN23.FullEntropySSCoverRest
  /-- CentralSquare: moderate-entropy row (N1b). -/
  srModerate : CKLaneN1.SR_Moderate
  /-- SS_Compact: (S) label 0, normalized_logsum (E). -/
  sLabel0 : ∀ q ∈ CKLaneG3.S.sTree.leaves, q.2 = 0 → CKLaneG3.SLeafOK (CKLaneG3.sBox q.1)
  /-- SS_Compact: (S) label 1, mean_logsum (M1). -/
  sLabel1 : ∀ q ∈ CKLaneG3.S.sTree.leaves, q.2 = 1 → CKLaneG3.SLeafOK (CKLaneG3.sBox q.1)
  /-- SS_Compact: (S) label 2, endpoint (M03). -/
  sLabel2 : ∀ q ∈ CKLaneG3.S.sTree.leaves, q.2 = 2 → CKLaneG3.SLeafOK (CKLaneG3.sBox q.1)
  /-- OP_Compact: (O) label 0, endpoint_plane_taylor (D). -/
  oLabel0 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 0 →
    CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)
  /-- OP_Compact: (O) label 1, shifted_logsum (M2b). -/
  oLabel1 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 1 →
    CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)

/-- CONDITIONAL: Theorem 7.1 components from `Remaining3`. -/
theorem Remaining3.theorem71 (h : Remaining3) : Theorem71Components :=
  theorem71_of_open h.correctionLeft h.correctionDet h.seam h.capLeftLower
    h.capLeftUpper h.ceStatRow3 h.ceStatRow4 h.ceStatRow5 h.gammaCorner h.gammaNonCorner h.e8Compact

/-- CONDITIONAL: the central square from `Remaining3`. -/
theorem Remaining3.centralSquare (h : Remaining3) : CentralSquare :=
  centralSquare_of_open h.fullEntropySSCoverRest h.srModerate

/-- CONDITIONAL: every row `RemainingRows2` still needs, from `Remaining3`. -/
theorem Remaining3.toRemainingRows2 (h : Remaining3) : RemainingRows2 where
  theorem71 := h.theorem71
  centralSquare := h.centralSquare
  ssCompact := ssCompact_of_open h.centralSquare h.sLabel0 h.sLabel1 h.sLabel2
  oLabel0 := h.oLabel0
  oLabel1 := h.oLabel1
  oLabel3 := oLabel3_of_M10

/-- CONDITIONAL: General CK from the open leaf-level obligations `Remaining3`. -/
theorem generalCourtadeKumar_of_remaining3 (h : Remaining3) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_remainingRows2 h.toRemainingRows2

end CKRoute
