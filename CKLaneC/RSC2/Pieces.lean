import CKLaneC.RSC2.Bulk2
import CKLaneC.RSC2.SmallB2
import GeneralCK.SmallMeanPhiRetainedCutoff

/-!
# Lane C, RA-stat: the two Lane C pieces of `GammaNonCorner retainedCutoff (1/20)` and the union with R2

* `bulk_retained`   : `GammaBulk retainedCutoff (1/20) (1/8) (1/8)`   (compact cover, b ∈ [1/8, 1/2], σ ≥ 1/8);
* `smallB_retained` : `GammaSmallB retainedCutoff (1/20) (1/8) (1/8)` (compact cover, b ∈ [3/65536, 1/8], σ ≥ 1/8;
  `retainedCutoff = 1/10000 ≥ 2 · 3/65536`, so every admissible `b > retainedCutoff/2` is covered).
* `gammaNonCorner_of_uTail` is CONDITIONAL on Lane R2's u-tail piece `GammaUTail retainedCutoff (1/20) (1/8)`.
-/

namespace CKLaneC.RSC2.Pieces

open CKLaneC.RSCell

theorem bulk_retained :
    GammaBulk GeneralCK.SmallMeanPhiCutoff.retainedCutoff (1 / 20) (1 / 8) (1 / 8) :=
  CKLaneC.RSC2.Bulk2.bulk _

theorem smallB_retained :
    GammaSmallB GeneralCK.SmallMeanPhiCutoff.retainedCutoff (1 / 20) (1 / 8) (1 / 8) :=
  CKLaneC.RSC2.SmallB2.smallB (by norm_num [GeneralCK.SmallMeanPhiCutoff.retainedCutoff])

/-- CONDITIONAL on R2's u-tail piece. -/
theorem gammaNonCorner_of_uTail
    (hU : GammaUTail GeneralCK.SmallMeanPhiCutoff.retainedCutoff (1 / 20) (1 / 8)) :
    CKLaneN23.RS.GammaNonCorner GeneralCK.SmallMeanPhiCutoff.retainedCutoff (1 / 20) :=
  gammaNonCorner_of_pieces hU smallB_retained bulk_retained

end CKLaneC.RSC2.Pieces
