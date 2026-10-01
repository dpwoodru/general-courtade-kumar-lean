import CKLaneC.RSC2.Pieces
import CKLaneC.RST2.U_Top

/-!
# Lane C, RA-stat: `GammaNonCorner retainedCutoff (1/20)` (unconditional)

Union of the three gated pieces: Lane C's bulk and small-b covers (`CKLaneC.RSC2.Pieces`) and the u-tail cover
(`CKLaneC.RST2.U_Top.uTail`: R2's tail checker and leaf lemmas `CKLaneR2.Tail.leafS/leafL`, Lane C's emission).
-/

namespace CKLaneC.RSC2.Final

theorem uTail_retained :
    CKLaneC.RSCell.GammaUTail GeneralCK.SmallMeanPhiCutoff.retainedCutoff (1 / 20) (1 / 8) :=
  CKLaneC.RST2.U_Top.uTail (by norm_num [GeneralCK.SmallMeanPhiCutoff.retainedCutoff])

theorem gammaNonCorner_retained :
    CKLaneN23.RS.GammaNonCorner GeneralCK.SmallMeanPhiCutoff.retainedCutoff (1 / 20) :=
  CKLaneC.RSC2.Pieces.gammaNonCorner_of_uTail uTail_retained

end CKLaneC.RSC2.Final
