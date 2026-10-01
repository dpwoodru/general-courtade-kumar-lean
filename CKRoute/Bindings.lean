import CKRoute.OCompactBind
import CKLaneD.Structural
import CKLaneN23.OpBoundaryStrip

/-!
# Rows of the manuscript route bound to closed lane theorems

* `OP_Corner` and `OP_BoundaryStrip`: Lane N23 (verbatim row copies, definitional).
* (O) labels 5 (`outside`, 449 leaves) and 12 (`global_corner`, 1 leaf): Lane D
  (`CKLaneD.Structural`), in the `OLeafOK` form consumed by `opCompact_of_archLeaves`.

`RemainingRows` lists exactly what the route still needs.
-/

namespace CKRoute

open GeneralCK

theorem route_opCorner : OP_Corner := CKLaneN23.row_opCorner

theorem route_opBoundaryStrip : OP_BoundaryStrip := CKLaneN23.row_opBoundaryStrip

/-- (O) leaves: labels 5 and 12 are discharged; the rest is the remaining hypothesis. -/
theorem archLeaves_of_rest
    (h : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 ≠ 5 → q.2 ≠ 12 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)) :
    ∀ q ∈ CKLaneD.ArchTree.archTree.leaves,
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1) := by
  intro q hq
  by_cases h5 : q.2 = 5
  · exact CKLaneD.Structural.outside_oLeafOK q hq h5
  by_cases h12 : q.2 = 12
  · exact CKLaneD.Structural.corner_oLeafOK q hq h12
  exact h q hq h5 h12

/-- Everything the scope-locked route still needs. -/
structure RemainingRows : Prop where
  theorem71 : Theorem71Components
  centralSquare : CentralSquare
  ssCompact : SS_Compact
  opCompactLeaves : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 ≠ 5 → q.2 ≠ 12 →
    CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)

theorem RemainingRows.toRoute (h : RemainingRows) : ManuscriptRoute where
  phiBranch := h.theorem71.phiBranch
  centralSquare := h.centralSquare
  ssSmallMean := row_ssSmallMean
  ssRatioTail := row_ssRatioTail
  ssCompact := h.ssCompact
  opBoundaryStrip := route_opBoundaryStrip
  opCorner := route_opCorner
  opLowEntropy := row_opLowEntropy
  opCompact := opCompact_of_archLeaves (archLeaves_of_rest h.opCompactLeaves)

/-- Conditional: General CK from the remaining rows of the manuscript route. -/
theorem generalCourtadeKumar_of_remainingRows (h : RemainingRows) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_manuscriptRoute h.toRoute

end CKRoute
