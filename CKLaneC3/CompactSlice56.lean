import CKLaneC3.CompactBatch56
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch56 = slice 56 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice56
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch56.tags.map tagRect = CompactTreeA.rects56 := by
  decide +kernel

end CKLaneC3.CompactSlice56
