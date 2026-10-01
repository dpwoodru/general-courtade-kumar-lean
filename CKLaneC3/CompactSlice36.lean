import CKLaneC3.CompactBatch36
import CKLaneC3.CompactTreeA

/-! Lane C3: leaf rectangles of CompactBatch36 = slice 36 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice36
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch36.tags.map tagRect = CompactTreeA.rects36 := by
  decide +kernel

end CKLaneC3.CompactSlice36
