import CKLaneC3.CompactBatch06
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch06 = slice 06 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice06
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch06.tags.map tagRect = CompactTreeA.rects06 := by
  decide +kernel

end CKLaneC3.CompactSlice06
