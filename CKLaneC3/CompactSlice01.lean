import CKLaneC3.CompactBatch01
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch01 = slice 01 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice01
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch01.tags.map tagRect = CompactTreeA.rects01 := by
  decide +kernel

end CKLaneC3.CompactSlice01
