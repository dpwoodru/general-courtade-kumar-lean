import CKRoute.Bindings
import CKLaneG3.OUnion.U_none
import CKLaneN4.OLeaves
import CKLaneM09.Leaves
import CKLaneG3.M11.Top
import CKLaneG3.M04.Top

/-!
# (O) row: closed per-label families of the archived outer-opposite partition

Labels of `CKLaneD.ArchTree.archTree` (29,495 leaves):
0 endpoint_plane_taylor (open, Lane D fleet), 1 shifted_logsum (open, Lane M2b fleet),
2 global_cap_slope (Lane M09), 3 global_feasible_split (open, Lane M10 fleet),
4 global_eight_ratio, 7 global_parent8, 8 global_low_entropy_025, 9 global_parent16,
10 global_parent_direct (Lane N4), 5 outside, 12 global_corner (Lane D),
6 global_parent_envelope (Lane M11, aggregated by G3), 11 logsum_direct (Lane M04, aggregated by G3).
-/

namespace CKRoute

open GeneralCK

/-- The (O) row from the three still-open label families (0, 1, 3). -/
theorem opCompact_of_labels013
    (h0 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 0 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1))
    (h1 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 1 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1))
    (h3 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 3 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)) :
    OP_Compact :=
  opCompact_iff_laneD.mpr
    (CKLaneG3.OUnion.U_none.opCompact_of_remaining_labels h0 h1
      (fun q hq hl => CKLaneD.OCompact.oLeafOK_of_semUVT _
        (CKLaneM09.Leaves.cap_slope_leaves q hq hl))
      h3
      CKLaneN4.OLeaves.family_label4
      CKLaneD.Structural.outside_oLeafOK
      CKLaneG3.M11.Top.label_oleaf
      CKLaneN4.OLeaves.family_label7
      CKLaneN4.OLeaves.family_label8
      CKLaneN4.OLeaves.family_label9
      CKLaneN4.OLeaves.family_label10
      CKLaneG3.M04.Top.label_oleaf
      CKLaneD.Structural.corner_oLeafOK)

/-- Everything the route still needs, after the closed (O) labels. -/
structure RemainingRows2 : Prop where
  theorem71 : Theorem71Components
  centralSquare : CentralSquare
  ssCompact : SS_Compact
  oLabel0 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 0 →
    CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)
  oLabel1 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 1 →
    CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)
  oLabel3 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 3 →
    CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)

theorem RemainingRows2.toRoute (h : RemainingRows2) : ManuscriptRoute where
  phiBranch := h.theorem71.phiBranch
  centralSquare := h.centralSquare
  ssSmallMean := row_ssSmallMean
  ssRatioTail := row_ssRatioTail
  ssCompact := h.ssCompact
  opBoundaryStrip := route_opBoundaryStrip
  opCorner := route_opCorner
  opLowEntropy := row_opLowEntropy
  opCompact := opCompact_of_labels013 h.oLabel0 h.oLabel1 h.oLabel3

/-- Conditional: General CK from the remaining rows. -/
theorem generalCourtadeKumar_of_remainingRows2 (h : RemainingRows2) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_manuscriptRoute h.toRoute

end CKRoute
