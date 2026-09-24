import CKRoute.Bindings2
import CKLaneM10.Leaves
import CKLaneN1.Assembly
import CKLaneN6.AllLeaves
import CKLaneN1c.TransitionLiteral
import CKLaneM06.CapFinal
import CKLaneG3.S.Compact
import CKLaneG3.S.Label3
import CKLaneG3.S.Label4
import CKLaneG3.S.Label5
import CKLaneG3.S.Label6
import CKLaneG3.S.Label7
import CKLaneG3.S.Label8

/-!
# Remaining3, parts (b)-(d): table rows with every closed family bound (CONDITIONAL)

* (b) `OP_Compact` via `opCompact_of_labels013` (`CKRoute.Bindings2`: labels 2, 4-12 closed), label 3 :=
  `CKLaneD.OCompact.oLeafOK_of_semUVT` ∘ `CKLaneM10.Leaves.feasibleSplit_leaves_sem` (M10, 1,872 leaves);
  labels 0 (D) and 1 (M2b) stay open.
* (c) `CentralSquare` via `CKLaneN1.centralSquare_of_five_open_rows_central` (N1 rows 1, 2, 4, N23 rows 5, 6,
  N4 parent8 and `sr_eightRatio_central` bound inside), with `CentralCap` := `CKLaneM06.Cap.CapFinal.centralCap`
  (M06), `SmallRatioT3NearRest` := `CKLaneN6.smallRatioT3NearRest` (N6), `SR_Transition` :=
  `CKLaneN1c.row_SR_Transition_literal` (N1c); `FullEntropySSCoverRest` (M05) and `SR_Moderate` (N1b)
  stay open.
* (d) `SS_Compact` via `CKLaneG3.S.ssCompact_of_labels` with labels 3-8 := `CKLaneG3.S.Label3.label3`, ...,
  `CKLaneG3.S.Label8.label8` (label 5 consumes the central square of (c)); labels 0 (E), 1 (M1), 2 (M03)
  stay open.

Every theorem below is CONDITIONAL on the hypotheses in its type. Nothing here closes a route row.
-/

set_option autoImplicit false

namespace CKRoute

open GeneralCK

/-- (O) label 3 (`global_feasible_split`, Lane M10) in the `OLeafOK` form consumed by
`opCompact_of_labels013`. Unconditional. -/
theorem oLabel3_of_M10 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 3 →
    CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1) :=
  fun q hq hl => CKLaneD.OCompact.oLeafOK_of_semUVT _ (CKLaneM10.Leaves.feasibleSplit_leaves_sem q hq hl)

/-- CONDITIONAL: the (O) row from the two open label families 0 and 1. -/
theorem opCompact_of_labels01
    (h0 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 0 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1))
    (h1 : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 = 1 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)) :
    OP_Compact :=
  opCompact_of_labels013 h0 h1 oLabel3_of_M10

/-- CONDITIONAL: the central square from its two open rows. -/
theorem centralSquare_of_open
    (hFE : CKLaneN23.FullEntropySSCoverRest) (hMod : CKLaneN1.SR_Moderate) :
    CentralSquare :=
  CKLaneN1.centralSquare_of_five_open_rows_central CKLaneM06.Cap.CapFinal.centralCap
    CKLaneN6.smallRatioT3NearRest hFE hMod CKLaneN1c.row_SR_Transition_literal

/-- CONDITIONAL: the (S) row from the central square and the three open label families 0, 1, 2. -/
theorem ssCompact_of_open (hcs : CentralSquare)
    (h0 : ∀ q ∈ CKLaneG3.S.sTree.leaves, q.2 = 0 → CKLaneG3.SLeafOK (CKLaneG3.sBox q.1))
    (h1 : ∀ q ∈ CKLaneG3.S.sTree.leaves, q.2 = 1 → CKLaneG3.SLeafOK (CKLaneG3.sBox q.1))
    (h2 : ∀ q ∈ CKLaneG3.S.sTree.leaves, q.2 = 2 → CKLaneG3.SLeafOK (CKLaneG3.sBox q.1)) :
    SS_Compact :=
  CKLaneG3.S.ssCompact_of_labels h0 h1 h2 CKLaneG3.S.Label3.label3 CKLaneG3.S.Label4.label4
    (CKLaneG3.S.Label5.label5 hcs) CKLaneG3.S.Label6.label6 CKLaneG3.S.Label7.label7
    CKLaneG3.S.Label8.label8

end CKRoute
