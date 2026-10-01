import GeneralCK.CorrectionComplementCharts
import CKLaneA1.BSFinal
import CKLaneA1.FEFinal
import CKLaneA5.SlotDiagonal1
import CKLaneA4.D2Slot
import CKLaneA2.SlotDiagonal3
import CKLaneA2.SlotDiagonal4
import CKLaneA2.SlotDiagonal5
import CKLaneA2.SlotDiagonal6
import CKLaneA3W.Owners
import CKLaneA3X.Owners
import CKLaneA3V.Owners

/-!
# Lane A5: the `ChartOwners` inhabitant, every field taken from the lane that closed it

| field | owner declaration | lane |
|---|---|---|
| bothSmall | `CKLaneA1.bothSmall_field` | A1 |
| fixedEdge | `CKLaneA1.fixedEdge_field` | A1 |
| diagonal1 | `CKLaneA5.Slots.diagonal1_signs` | A5 |
| diagonal2 | `CKLaneA4.D2.diagonal2_signs` | A4 |
| diagonal3..6 | `CKLaneA2.Slots.diagonal{3,4,5,6}_signs` | A2 |
| diagonal7..9, corner0..5, directC5, directC6 | `CKLaneA3W.*` (u ≥ 9/25 high-u owner) | A3 |
| directC3 | `CKLaneA3X.directC3` | A3 |
| directC4 | `CKLaneA3V.directC4` | A3 |

All modules compiled over the F-C provider (`~/gck_lanes/F-C/work/root`); the single `CKLaneA` checker root is
`A2/checkerFC` (byte-identical to `A4/deproot`).
-/

namespace CKLaneA5.Assembly

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement

/-- The complete chart-owner record. -/
theorem chartOwners : ChartOwners where
  bothSmall := CKLaneA1.bothSmall_field
  fixedEdge := CKLaneA1.fixedEdge_field
  diagonal1 := CKLaneA5.Slots.diagonal1_signs
  diagonal2 := CKLaneA4.D2.diagonal2_signs
  diagonal3 := CKLaneA2.Slots.diagonal3_signs
  diagonal4 := CKLaneA2.Slots.diagonal4_signs
  diagonal5 := CKLaneA2.Slots.diagonal5_signs
  diagonal6 := CKLaneA2.Slots.diagonal6_signs
  diagonal7 := CKLaneA3W.diagonal7
  diagonal8 := CKLaneA3W.diagonal8
  diagonal9 := CKLaneA3W.diagonal9
  directC3 := CKLaneA3X.directC3
  directC4 := CKLaneA3V.directC4
  directC5 := CKLaneA3W.directC5
  directC6 := CKLaneA3W.directC6
  corner0 := CKLaneA3W.corner0
  corner1 := CKLaneA3W.corner1
  corner2 := CKLaneA3W.corner2
  corner3 := CKLaneA3W.corner3
  corner4 := CKLaneA3W.corner4
  corner5 := CKLaneA3W.corner5

end CKLaneA5.Assembly
